/* Saves in iCloud: the same save on the Mac and on iPhone / iPad.

   The game's save folder (<profile>/save/<uid>, runtime/fs_host.c) stays the working copy. A copy of it lives in iCloud
   Drive as <cloud>/Saves/current, with current/sync.plist naming its generation, the device that wrote it, when and the
   SHA-256 of its files:
   - at start, before the game reads a save (fs_host.c init), the iCloud copy replaces the local folder when another
     device saved since this one last synced;
   - after the game commits a save (fs_host.c commit), the folder is copied to iCloud a few seconds later.
   When the two differ at start, the one saved last wins (sync.plist's time against the newest local file, which keeps its
   time when copied); the other is kept in <profile>/cloud-backups (the last 10). Nothing is merged inside a save.

   Where <cloud> is: the app's iCloud container on iPhone / iPad (ios/tools/install_device.py --icloud signs it in, the
   container's Documents folder); on the Mac the folder that container appears as in iCloud Drive,
   ~/Library/Mobile Documents/iCloud~org~macnativegames~totk~<team>/Documents, which app/launcher.m passes in
   TOTK_CLOUD_SAVE_DIR (the Mac app needs no iCloud entitlement for a folder iCloud Drive syncs). TOTK_CLOUD_SAVE_DIR=0
   turns it off. */
#import <Foundation/Foundation.h>
#include <CommonCrypto/CommonDigest.h>
#include <TargetConditionals.h>
#include <dispatch/dispatch.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "runtime.h"


static NSString *g_local, *g_state, *g_backups, *g_cloud;   // save folder, <profile>/cloud-sync.plist, backups, <cloud>/Saves
static dispatch_queue_t g_queue;
static int g_push_pending;

#define LOG(...) fprintf(stderr, "[cloud-save] " __VA_ARGS__)

static NSString *cloud_root(void) {
    const char *e = getenv("TOTK_CLOUD_SAVE_DIR");
    if (e) return *e && strcmp(e, "0") ? @(e) : nil;
#if TARGET_OS_IPHONE
    NSURL *u = [NSFileManager.defaultManager URLForUbiquityContainerIdentifier:nil];   // nil: no iCloud account or entitlement
    return u ? [u URLByAppendingPathComponent:@"Documents"].path : nil;
#else
    return nil;
#endif
}

/* The files of a save folder, sorted, without Finder / iCloud bookkeeping and sync.plist. */
static NSArray<NSString *> *save_files(NSString *dir) {
    NSMutableArray *out = [NSMutableArray array];
    NSDirectoryEnumerator *en = [NSFileManager.defaultManager enumeratorAtPath:dir];
    for (NSString *rel in en) {
        NSString *name = rel.lastPathComponent;
        if ([name isEqualToString:@".DS_Store"] || [rel isEqualToString:@"sync.plist"] || ([name hasPrefix:@"."] && [name hasSuffix:@".icloud"])) continue;
        if ([en.fileAttributes.fileType isEqualToString:NSFileTypeRegular]) [out addObject:rel];
    }
    [out sortUsingSelector:@selector(compare:)];
    return out;
}
static NSString *save_hash(NSString *dir) {
    CC_SHA256_CTX c; CC_SHA256_Init(&c);
    for (NSString *rel in save_files(dir)) {
        NSData *d = [NSData dataWithContentsOfFile:[dir stringByAppendingPathComponent:rel] options:NSDataReadingMappedIfSafe error:nil];
        if (!d) return nil;   // unreadable (not downloaded yet): no hash rather than a wrong one
        const char *r = rel.UTF8String; uint64_t n = d.length;
        CC_SHA256_Update(&c, r, (CC_LONG)strlen(r) + 1); CC_SHA256_Update(&c, &n, sizeof n); CC_SHA256_Update(&c, d.bytes, (CC_LONG)d.length);
    }
    unsigned char h[CC_SHA256_DIGEST_LENGTH]; CC_SHA256_Final(h, &c);
    NSMutableString *s = [NSMutableString string]; for (int i = 0; i < CC_SHA256_DIGEST_LENGTH; i++) [s appendFormat:@"%02x", h[i]];
    return s;
}
static double newest_mtime(NSString *dir) {
    double t = 0;
    for (NSString *rel in save_files(dir)) {
        NSDate *m = [NSFileManager.defaultManager attributesOfItemAtPath:[dir stringByAppendingPathComponent:rel] error:nil].fileModificationDate;
        if (m.timeIntervalSince1970 > t) t = m.timeIntervalSince1970;
    }
    return t;
}

/* iPhone / iPad: iCloud keeps files in the container as placeholders until asked; wait for them (at most `wait` s). On
   the Mac a read of a not yet downloaded file waits for it by itself. */
static BOOL ensure_downloaded(NSString *dir, double wait) {
#if TARGET_OS_IPHONE
    NSFileManager *fm = NSFileManager.defaultManager;
    NSURL *url = [NSURL fileURLWithPath:dir];
    [fm startDownloadingUbiquitousItemAtURL:url error:nil];
    for (double waited = 0;; waited += 0.25) {
        BOOL all = YES;
        for (NSURL *u in [fm enumeratorAtURL:url includingPropertiesForKeys:@[NSURLUbiquitousItemDownloadingStatusKey] options:0 errorHandler:nil]) {
            NSString *st = nil; [u getResourceValue:&st forKey:NSURLUbiquitousItemDownloadingStatusKey error:nil];
            if (st && ![st isEqualToString:NSURLUbiquitousItemDownloadingStatusCurrent]) { all = NO; [fm startDownloadingUbiquitousItemAtURL:u error:nil]; }
        }
        if (all) return YES;
        if (waited >= wait) return NO;
        usleep(250000);
    }
#else
    (void)dir; (void)wait; return YES;
#endif
}

static NSDictionary *read_plist(NSString *path) { NSDictionary *d = [NSDictionary dictionaryWithContentsOfFile:path]; return [d isKindOfClass:NSDictionary.class] ? d : nil; }
static void write_state(NSNumber *gen, NSString *hash) {
    [@{@"gen": gen ?: @0, @"hash": hash ?: @""} writeToFile:g_state atomically:YES];
}

/* Replace the contents of `dst` with those of `src`, through a sibling folder so a failure leaves `dst` as it was. */
static BOOL replace_folder(NSString *src, NSString *dst) {
    NSFileManager *fm = NSFileManager.defaultManager;
    NSString *tmp = [dst stringByAppendingFormat:@".incoming-%d", getpid()], *old = [dst stringByAppendingFormat:@".old-%d", getpid()];
    [fm removeItemAtPath:tmp error:nil]; [fm removeItemAtPath:old error:nil];
    NSError *err = nil;
    if (![fm copyItemAtPath:src toPath:tmp error:&err]) { LOG("copy failed: %s\n", err.localizedDescription.UTF8String); [fm removeItemAtPath:tmp error:nil]; return NO; }
    [fm removeItemAtPath:[tmp stringByAppendingPathComponent:@"sync.plist"] error:nil];
    BOOL had = [fm fileExistsAtPath:dst];
    if (had && ![fm moveItemAtPath:dst toPath:old error:&err]) { LOG("move failed: %s\n", err.localizedDescription.UTF8String); [fm removeItemAtPath:tmp error:nil]; return NO; }
    if (![fm moveItemAtPath:tmp toPath:dst error:&err]) { LOG("move failed: %s\n", err.localizedDescription.UTF8String); if (had) [fm moveItemAtPath:old toPath:dst error:nil]; return NO; }
    [fm removeItemAtPath:old error:nil];
    return YES;
}
static void backup(NSString *src, NSString *what) {
    NSFileManager *fm = NSFileManager.defaultManager;
    [fm createDirectoryAtPath:g_backups withIntermediateDirectories:YES attributes:nil error:nil];
    NSDateFormatter *f = [NSDateFormatter new]; f.dateFormat = @"yyyyMMdd-HHmmss";
    NSString *to = [g_backups stringByAppendingPathComponent:[NSString stringWithFormat:@"%@-%@", [f stringFromDate:NSDate.date], what]];
    if ([fm copyItemAtPath:src toPath:to error:nil]) LOG("kept the %s save in %s\n", what.UTF8String, to.UTF8String);
    NSArray *all = [[fm contentsOfDirectoryAtPath:g_backups error:nil] sortedArrayUsingSelector:@selector(compare:)];
    for (NSUInteger i = 0; i + 10 < all.count; i++) [fm removeItemAtPath:[g_backups stringByAppendingPathComponent:all[i]] error:nil];
}

/* Write the local save to iCloud as the next generation. */
static void push(void) {
    NSString *cur = [g_cloud stringByAppendingPathComponent:@"current"], *hash = save_hash(g_local);
    NSDictionary *state = read_plist(g_state), *meta = read_plist([cur stringByAppendingPathComponent:@"sync.plist"]);
    if (!hash || !save_files(g_local).count) return;
    if ([hash isEqualToString:state[@"hash"]] && [meta[@"gen"] isEqual:state[@"gen"]]) return;   // nothing new on either side
    long long gen = MAX([meta[@"gen"] longLongValue], [state[@"gen"] longLongValue]) + 1;
    if (meta && ![meta[@"gen"] isEqual:state[@"gen"]] && ensure_downloaded(cur, 10)) backup(cur, @"icloud");   // another device saved meanwhile
    [NSFileManager.defaultManager createDirectoryAtPath:g_cloud withIntermediateDirectories:YES attributes:nil error:nil];
    __block BOOL ok = NO;
    NSError *cerr = nil;
    [[[NSFileCoordinator alloc] initWithFilePresenter:nil] coordinateWritingItemAtURL:[NSURL fileURLWithPath:cur] options:NSFileCoordinatorWritingForReplacing error:&cerr byAccessor:^(NSURL *u) {
        if (!replace_folder(g_local, u.path)) return;
        ok = [@{@"gen": @(gen), @"device": NSProcessInfo.processInfo.hostName ?: @"?", @"time": @(NSDate.date.timeIntervalSince1970), @"hash": hash}
                 writeToFile:[u.path stringByAppendingPathComponent:@"sync.plist"] atomically:YES];
    }];
    if (!ok) { LOG("upload failed%s%s\n", cerr ? ": " : "", cerr ? cerr.localizedDescription.UTF8String : ""); return; }
    write_state(@(gen), hash);
    LOG("saved to iCloud (generation %lld)\n", gen);
}

/* fs_host.c init: before the game reads a save. */
void runtime_cloud_save_start(const char *save_dir, const char *profile_dir) {
    @autoreleasepool {
        NSString *root = cloud_root();
        if (!root) { LOG("off (no iCloud folder)\n"); return; }
        g_local = @(save_dir); g_cloud = [root stringByAppendingPathComponent:@"Saves"];
        g_state = [@(profile_dir) stringByAppendingPathComponent:@"cloud-sync.plist"];
        g_backups = [@(profile_dir) stringByAppendingPathComponent:@"cloud-backups"];
        g_queue = dispatch_queue_create("totk.cloud-save", DISPATCH_QUEUE_SERIAL);
        runtime_boot_status("iCloud", "Syncing saves");
        NSString *cur = [g_cloud stringByAppendingPathComponent:@"current"];
        NSDictionary *state = read_plist(g_state);
        ensure_downloaded(g_cloud, 30);
        NSDictionary *meta = read_plist([cur stringByAppendingPathComponent:@"sync.plist"]);
        NSString *local = save_hash(g_local);
        BOOL localSaves = save_files(g_local).count > 0;
        if (!meta) {
            /* A device that synced before but sees nothing has not learned of iCloud's files yet: it uploads on its
               next save, after the files have arrived, instead of now. */
            if (state) { LOG("no iCloud save visible yet; this device's save is used\n"); return; }
            LOG("iCloud has no save yet\n"); if (localSaves) push(); return;
        }
        if ([meta[@"hash"] isEqualToString:local]) { write_state(meta[@"gen"], local); LOG("in sync (generation %lld)\n", [meta[@"gen"] longLongValue]); return; }
        double cloudTime = [meta[@"time"] doubleValue], localTime = localSaves ? newest_mtime(g_local) : 0;
        if (localTime > cloudTime) { LOG("this device's save is newer than iCloud's\n"); push(); return; }
        if (!ensure_downloaded(cur, 60)) { LOG("the iCloud save did not download in time; this device's save is used\n"); return; }
        if (![save_hash(cur) isEqualToString:meta[@"hash"]]) { LOG("the iCloud save is incomplete (still syncing); this device's save is used\n"); return; }
        if (localSaves) backup(g_local, @"local");
        if (replace_folder(cur, g_local)) { write_state(meta[@"gen"], meta[@"hash"]); LOG("loaded the save from %s (generation %lld)\n", [meta[@"device"] UTF8String], [meta[@"gen"] longLongValue]); }
    }
}

/* fs_host.c commit: the game finished writing a save. Upload once it has been quiet for a moment. */
static void push_when_quiet(void) {
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 3 * NSEC_PER_SEC), g_queue, ^{
        if (runtime_fs_save_busy()) { push_when_quiet(); return; }
        __atomic_store_n(&g_push_pending, 0, __ATOMIC_SEQ_CST);
        @autoreleasepool { push(); }
    });
}
void runtime_cloud_save_changed(void) {
    if (!g_queue || __atomic_exchange_n(&g_push_pending, 1, __ATOMIC_SEQ_CST)) return;
    push_when_quiet();
}
