/* The two libuv filesystem calls that WASI's libc does not provide. See uv.h.
   Both follow libuv's contract: the template is rewritten in place, `req->path`
   points at it, `req->result` carries the fd for mkstemp, and a failure is the
   negated errno. */
#include <uv.h>
#include <fcntl.h>
#include <time.h>

static int uv__template_fill(char * tmpl) {
    size_t n = strlen(tmpl);
    if (n < 6 || strcmp(tmpl + n - 6, "XXXXXX") != 0) { errno = EINVAL; return -1; }
    return 0;
}

static void uv__scramble(char * suffix, unsigned seed) {
    static const char tbl[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
    for (int i = 0; i < 6; i++) { seed = seed * 1103515245u + 12345u; suffix[i] = tbl[(seed >> 16) % 62]; }
}

int uv_fs_mkstemp(uv_loop_t * l, uv_fs_t * req, const char * tmpl, uv_fs_cb cb) {
    (void) l; (void) cb;
    char * path = (char *) tmpl;             /* libuv rewrites in place */
    if (uv__template_fill(path) != 0) return -errno;
    unsigned seed = (unsigned) time(NULL);
    for (int attempt = 0; attempt < 128; attempt++) {
        uv__scramble(path + strlen(path) - 6, seed + attempt * 7919u);
        int fd = open(path, O_RDWR | O_CREAT | O_EXCL, 0600);
        if (fd >= 0) { req->result = fd; req->path = path; return 0; }
        if (errno != EEXIST) return -errno;
    }
    return -EEXIST;
}

int uv_fs_mkdtemp(uv_loop_t * l, uv_fs_t * req, const char * tmpl, uv_fs_cb cb) {
    (void) l; (void) cb;
    char * path = (char *) tmpl;
    if (uv__template_fill(path) != 0) return -errno;
    unsigned seed = (unsigned) time(NULL) ^ 0x5bf03635u;
    for (int attempt = 0; attempt < 128; attempt++) {
        uv__scramble(path + strlen(path) - 6, seed + attempt * 7919u);
        if (mkdir(path, 0700) == 0) { req->result = 0; req->path = path; return 0; }
        if (errno != EEXIST) return -errno;
    }
    return -EEXIST;
}
