/* A stand-in for libuv, for the WASI build of the Lean runtime.
 *
 * libuv has no WASI port, and the Lean runtime's own libuv code is already
 * behind `LEAN_EMSCRIPTEN` (runtime/libuv.cpp) -- the event loop, timers, TCP,
 * UDP, DNS and signals all compile out. `runtime/io.cpp` is the exception: it
 * reaches for libuv's *synchronous filesystem* calls, which are thin wrappers
 * over POSIX and which WASI does provide. So this header is not a set of
 * stubs; it is those wrappers, over the real thing.
 *
 * Scope is exactly what `io.cpp` names -- stat, lstat, link, unlink, mkstemp,
 * mkdtemp, tmpdir, strerror -- and the libuv error convention it decodes
 * against: a failure is the *negated* errno, returned rather than set.
 */
#pragma once
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/stat.h>
#include <stdint.h>
#include <sys/types.h>

#define UV_VERSION_HEX 0

/* libuv reports errors as negative errno values. */
#define UV__E(name) (-(name))
#define UV_E2BIG UV__E(E2BIG)
#define UV_EACCES UV__E(EACCES)
#define UV_EADDRINUSE UV__E(EADDRINUSE)
#define UV_EADDRNOTAVAIL UV__E(EADDRNOTAVAIL)
#define UV_EAFNOSUPPORT UV__E(EAFNOSUPPORT)
#define UV_EAGAIN UV__E(EAGAIN)
#define UV_EBADF UV__E(EBADF)
#define UV_EBUSY UV__E(EBUSY)
#define UV_ECONNABORTED UV__E(ECONNABORTED)
#define UV_ECONNREFUSED UV__E(ECONNREFUSED)
#define UV_ECONNRESET UV__E(ECONNRESET)
#define UV_EDESTADDRREQ UV__E(EDESTADDRREQ)
#define UV_EEXIST UV__E(EEXIST)
#define UV_EFAULT UV__E(EFAULT)
#define UV_EFBIG UV__E(EFBIG)
#define UV_EHOSTUNREACH UV__E(EHOSTUNREACH)
#define UV_EILSEQ UV__E(EILSEQ)
#define UV_EINTR UV__E(EINTR)
#define UV_EINVAL UV__E(EINVAL)
#define UV_EIO UV__E(EIO)
#define UV_EISCONN UV__E(EISCONN)
#define UV_EISDIR UV__E(EISDIR)
#define UV_ELOOP UV__E(ELOOP)
#define UV_EMFILE UV__E(EMFILE)
#define UV_EMLINK UV__E(EMLINK)
#define UV_EMSGSIZE UV__E(EMSGSIZE)
#define UV_ENAMETOOLONG UV__E(ENAMETOOLONG)
#define UV_ENETDOWN UV__E(ENETDOWN)
#define UV_ENETUNREACH UV__E(ENETUNREACH)
#define UV_ENFILE UV__E(ENFILE)
#define UV_ENOBUFS UV__E(ENOBUFS)
#define UV_ENODATA UV__E(ENODATA)
#define UV_ENODEV UV__E(ENODEV)
#define UV_ENOENT UV__E(ENOENT)
#define UV_ENOMEM UV__E(ENOMEM)
#define UV_ENOPROTOOPT UV__E(ENOPROTOOPT)
#define UV_ENOSPC UV__E(ENOSPC)
#define UV_ENOSYS UV__E(ENOSYS)
#define UV_ENOTCONN UV__E(ENOTCONN)
#define UV_ENOTDIR UV__E(ENOTDIR)
#define UV_ENOTEMPTY UV__E(ENOTEMPTY)
#define UV_ENOTSOCK UV__E(ENOTSOCK)
#define UV_ENOTSUP UV__E(ENOTSUP)
#define UV_ENOTTY UV__E(ENOTTY)
#define UV_ENXIO UV__E(ENXIO)
#define UV_EPERM UV__E(EPERM)
#define UV_EPIPE UV__E(EPIPE)
#define UV_EPROTO UV__E(EPROTO)
#define UV_EPROTONOSUPPORT UV__E(EPROTONOSUPPORT)
#define UV_EPROTOTYPE UV__E(EPROTOTYPE)
#define UV_ERANGE UV__E(ERANGE)
#define UV_EROFS UV__E(EROFS)
#define UV_ESPIPE UV__E(ESPIPE)
#define UV_ESRCH UV__E(ESRCH)
#define UV_ETIMEDOUT UV__E(ETIMEDOUT)
#define UV_ETXTBSY UV__E(ETXTBSY)
#define UV_EXDEV UV__E(EXDEV)

typedef struct { int64_t tv_sec; int32_t tv_nsec; } uv_timespec_t;

typedef struct {
    uint64_t st_mode;
    uint64_t st_nlink;
    uint64_t st_size;
    uv_timespec_t st_atim;
    uv_timespec_t st_mtim;
} uv_stat_t;

/* `io.cpp` reads `statbuf` after stat/lstat and `result` + `path` after
   mkstemp/mkdtemp; nothing else in the struct is touched. */
typedef struct { uv_stat_t statbuf; ssize_t result; const char * path; } uv_fs_t;
typedef void uv_loop_t;
typedef void (*uv_fs_cb)(uv_fs_t *);

#ifdef __cplusplus
extern "C" {
#endif

static inline const char * uv_strerror(int err) { return strerror(err < 0 ? -err : err); }

static inline void uv_fs_req_cleanup(uv_fs_t * req) { (void) req; }

static inline void uv__fill(uv_stat_t * out, struct stat const * st) {
    out->st_mode  = (uint64_t) st->st_mode;
    out->st_nlink = (uint64_t) st->st_nlink;
    out->st_size  = (uint64_t) st->st_size;
    out->st_atim.tv_sec  = (int64_t) st->st_atim.tv_sec;
    out->st_atim.tv_nsec = (int32_t) st->st_atim.tv_nsec;
    out->st_mtim.tv_sec  = (int64_t) st->st_mtim.tv_sec;
    out->st_mtim.tv_nsec = (int32_t) st->st_mtim.tv_nsec;
}

static inline int uv_fs_stat(uv_loop_t * l, uv_fs_t * req, const char * path, uv_fs_cb cb) {
    (void) l; (void) cb;
    struct stat st;
    if (stat(path, &st) != 0) return -errno;
    uv__fill(&req->statbuf, &st);
    return 0;
}

static inline int uv_fs_lstat(uv_loop_t * l, uv_fs_t * req, const char * path, uv_fs_cb cb) {
    (void) l; (void) cb;
    struct stat st;
    if (lstat(path, &st) != 0) return -errno;
    uv__fill(&req->statbuf, &st);
    return 0;
}

static inline int uv_fs_link(uv_loop_t * l, uv_fs_t * req, const char * a, const char * b, uv_fs_cb cb) {
    (void) l; (void) req; (void) cb;
    return link(a, b) != 0 ? -errno : 0;
}

static inline int uv_fs_unlink(uv_loop_t * l, uv_fs_t * req, const char * path, uv_fs_cb cb) {
    (void) l; (void) req; (void) cb;
    return unlink(path) != 0 ? -errno : 0;
}

/* libuv rewrites the template in place and reports the fd (mkstemp) or success
   (mkdtemp) -- so do we. WASI's libc has neither, so they are spelled out. */
int uv_fs_mkstemp(uv_loop_t * l, uv_fs_t * req, const char * tmpl, uv_fs_cb cb);
int uv_fs_mkdtemp(uv_loop_t * l, uv_fs_t * req, const char * tmpl, uv_fs_cb cb);

static inline int uv_os_tmpdir(char * buf, size_t * size) {
    const char * t = "/tmp";
    size_t n = strlen(t);
    if (*size <= n) { *size = n + 1; return -ENOBUFS; }
    memcpy(buf, t, n + 1);
    *size = n;
    return 0;
}

#ifdef __cplusplus
}
#endif
