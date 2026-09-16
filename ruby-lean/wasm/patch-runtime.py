#!/usr/bin/env python3
"""The seven edits the Lean runtime needs to compile for `wasm32-wasip1`.

Applied in place to an unpacked Lean source tree, and idempotent: each one
asserts on the text it expects and is a no-op once made, so `build.sh` can call
it on every run.

There is less here than the prior art suggests. The Lean runtime is *already*
written for a target with no libuv, no OpenSSL, no threads and no process
spawning -- that is what `LEAN_EMSCRIPTEN` selects, and defining it under
wasi-sdk gets almost all the way. These seven are what is left: places
where a platform header or device is reached for outside any guard, and places
where the guard exists but does not cover WASI.

None of them changes behaviour on any supported platform; every edit is inside
a `__wasi__` branch or adds an include.
"""
from __future__ import annotations

import sys
from pathlib import Path


def edit(path: Path, old: str, new: str, what: str) -> str:
    t = path.read_text()
    if new in t:
        return f"  = {path.name}: {what} (already applied)"
    if old not in t:
        sys.exit(f"FATAL: {path}: cannot find the text to patch for: {what}\n"
                 f"The Lean source tree is probably not v4.32.2.")
    path.write_text(t.replace(old, new, 1))
    return f"  + {path.name}: {what}"


def main(src: Path) -> None:
    rt = src / "runtime"
    out = []

    # 1. thread.h. The single-threaded fallback declares a `unique_lock`
    #    constructor taking `std::adopt_lock_t`, but only the LEAN_MULTI_THREAD
    #    branch includes <mutex>, which is where that tag is declared. Every
    #    platform upstream supports builds multi-threaded, so this path is never
    #    compiled there.
    anchor = "namespace lean {\nnamespace chrono = std::chrono;\n};\n"
    out.append(edit(rt / "thread.h", anchor, anchor + """
// [wasi] The single-threaded fallback below takes `std::adopt_lock_t`, which is
// declared in <mutex> -- included only by the LEAN_MULTI_THREAD branch.
#include <mutex>
""", "include <mutex> for the single-threaded fallback"))

    # 2 & 3. compact.cpp enumerates loaded shared objects to relocate closure
    #    code pointers when writing a .olean. WASI has no dynamic loading: there
    #    is one module and the list is correctly empty.
    out.append(edit(rt / "compact.cpp",
                    "#elif !defined(LEAN_WINDOWS)\n#include <link.h>\n#endif",
                    "#elif !defined(LEAN_WINDOWS) && !defined(__wasi__)\n#include <link.h>\n#endif",
                    "do not include <link.h> under WASI"))
    out.append(edit(rt / "compact.cpp",
                    "#else\n    // Linux: use dl_iterate_phdr\n    dl_iterate_phdr(",
                    "#elif defined(__wasi__)\n"
                    "    // [wasi] No dynamic loading: one module, no shared objects to enumerate.\n"
                    "#else\n    // Linux: use dl_iterate_phdr\n    dl_iterate_phdr(",
                    "skip dl_iterate_phdr under WASI"))

    # 4. stack_overflow.h. The guard keeps an alternate signal stack so a
    #    SIGSEGV handler can report an overflow. WASI has no signals; an
    #    overflow traps in the engine instead, which is the same outcome.
    out.append(edit(rt / "stack_overflow.h",
                    "#ifndef LEAN_WINDOWS\n"
                    "    // We need a separate signal stack since we can't use the overflowed stack\n"
                    "    stack_t m_signal_stack;\n#endif",
                    "#if !defined(LEAN_WINDOWS) && !defined(__wasi__)\n"
                    "    // We need a separate signal stack since we can't use the overflowed stack\n"
                    "    stack_t m_signal_stack;\n#endif",
                    "no alternate signal stack under WASI"))

    # 5. memory.cpp. WASI's <sys/resource.h> declares `rusage` without
    #    `ru_maxrss`, and a wasm module cannot observe its own resident set.
    out.append(edit(rt / "memory.cpp",
                    "#if defined(__APPLE__)\n"
                    "    return static_cast<size_t>(rusage.ru_maxrss);\n#else\n"
                    "    return static_cast<size_t>(rusage.ru_maxrss) * static_cast<size_t>(1024);\n#endif",
                    "#if defined(__wasi__)\n"
                    "    // [wasi] No `ru_maxrss`, and no resident set to report. Unknown.\n"
                    "    (void) rusage;\n    return 0;\n"
                    "#elif defined(__APPLE__)\n"
                    "    return static_cast<size_t>(rusage.ru_maxrss);\n#else\n"
                    "    return static_cast<size_t>(rusage.ru_maxrss) * static_cast<size_t>(1024);\n#endif",
                    "get_peak_rss reports unknown under WASI"))

    # 6. io.cpp. `lean_io_get_random_bytes` reads /dev/urandom, which WASI has no
    #    device tree for -- and every executable hits it at startup, so this is
    #    not an edge case. WASI's libc does expose `getentropy`, which is the
    #    same syscall (`random_get`) the browser shim backs with
    #    `crypto.getRandomValues`.
    out.append(edit(rt / "io.cpp",
                    """    if (nbytes == 0) return io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
""",
                    """    if (nbytes == 0) return io_result_mk_ok(lean_alloc_sarray(1, 0, 0));

#if defined(__wasi__)
    // [wasi] No /dev/urandom. `getentropy` is WASI's `random_get`, which a
    // browser shim backs with `crypto.getRandomValues`. POSIX caps one call at
    // 256 bytes.
    if (lean_alloc_sarray_would_overflow(1, nbytes)) {
        return io_result_mk_error(decode_io_error(ENOMEM, NULL));
    }
    {
        obj_res res = lean_alloc_sarray(1, 0, nbytes);
        uint8_t * dst = lean_sarray_cptr(res);
        size_t remain = nbytes;
        while (remain > 0) {
            size_t chunk = remain < 256 ? remain : 256;
            if (getentropy(dst, chunk) != 0) {
                dec_ref(res);
                return io_result_mk_error(decode_io_error(errno, nullptr));
            }
            dst += chunk; remain -= chunk;
        }
        lean_sarray_set_size(res, nbytes);
        return io_result_mk_ok(res);
    }
#endif
""",
                    "getRandomBytes via getentropy under WASI"))

    # 7. object.cpp -- an upstream 32-bit bug, and the only one of these seven
    #    that is a *defect* rather than a porting accommodation.
    #
    #    `string_to_list_core` builds the `List Char` behind `String.toList`.
    #    It seeds the list with `lean_box_uint32(0)` as the `nil`. On 64-bit
    #    that is `lean_box(0)`, which is `List.nil`, so it is correct by
    #    coincidence. On 32-bit `lean_box_uint32` does not tag a pointer -- it
    #    heap-allocates a constructor with a `uint32` scalar field and *zero*
    #    object fields (see `lean_box_uint32` in `include/lean/lean.h`). So the
    #    terminator is not a scalar, and every consumer that walks the list with
    #    `while (!lean_is_scalar(o))` -- `lean_string_mk` above all -- runs off
    #    the end, reading `lean_ctor_get(o, 0)` and `(o, 1)` from an object with
    #    neither.
    #
    #    Symptom before this fix: `"x-1".split("-")` returned `["x", "1\0\0\0"]`,
    #    and without `-DNDEBUG` it tripped `assert(i < lean_ctor_num_objs(o))`.
    #    The `nil` of a list is a list, not a boxed `UInt32`.
    out.append(edit(rt / "object.cpp",
                    "    obj_res  r = lean_box_uint32(0);",
                    "    // [wasi] `nil`, not a boxed UInt32 -- see patch 7 in patch-runtime.py.\n"
                    "    obj_res  r = lean_box(0);",
                    "string_to_list_core terminates its list with lean_box(0)"))

    print("\n".join(out))


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: patch-runtime.py <lean-source-tree>/src")
    main(Path(sys.argv[1]))
