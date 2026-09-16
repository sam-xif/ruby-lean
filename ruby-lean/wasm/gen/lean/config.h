#pragma once
#include <lean/version.h>
/* Upstream's cmake substitutes four `#define`s here. This is a plain,
   single-threaded, non-stage0 runtime: no mimalloc, no small allocator, no lazy
   RC. Only LEAN_IS_STAGE0 is tested with `#if` rather than `#ifdef`, so it is
   the only one that has to be present. */
#define LEAN_IS_STAGE0 0
