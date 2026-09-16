/* Shim. The Lean runtime's WASI-shaped code paths are all behind
   `LEAN_EMSCRIPTEN`, which is what we want under wasi-sdk too -- no libuv, no
   OpenSSL, no threads, no process spawn. The only thing that guard also brings
   in is this header, for three uses:

     EM_ASM(debugger;)                 runtime/debug.cpp   -- drop it
     EM_ASM_INT({ ...js... }, $0)      runtime/io.cpp x2   -- IO.getEnv and
                                       appPath; returning 0 is the header's own
                                       "not available" answer on both paths.

   There is no JS engine to ask under WASI, so 0 is the honest reply. */
#pragma once
#define EM_ASM(...)     ((void) 0)
#define EM_ASM_INT(...) 0
