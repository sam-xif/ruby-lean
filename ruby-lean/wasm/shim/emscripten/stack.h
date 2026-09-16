/* Shim; see ../emscripten.h. `runtime/stackinfo.cpp` asks for the main stack's
   extent to size its overflow guard. wasi-sdk's default main stack is 64 KiB
   and the linker can be told otherwise (-z stack-size), so report what we
   actually link with rather than probing. */
#pragma once
#include <stddef.h>
#ifndef LEAN_WASI_STACK_SIZE
#define LEAN_WASI_STACK_SIZE (8u * 1024u * 1024u)
#endif
static inline size_t emscripten_stack_get_base(void) { return 0; }
static inline size_t emscripten_stack_get_end(void)  { return LEAN_WASI_STACK_SIZE; }
