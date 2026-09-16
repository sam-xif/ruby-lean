/* The two runtime translation units that cannot be built for WASI, reduced to
 * the symbols `init_module.cpp` calls.
 *
 *   runtime/process.cpp        -- fork/exec/waitpid. A wasm module has no child
 *                                 processes; `sys/wait.h` does not exist.
 *   runtime/stack_overflow.cpp -- a SIGSEGV handler on an alternate signal
 *                                 stack, to turn a stack overflow into a
 *                                 diagnostic. WASI has no signals; an overflow
 *                                 traps in the engine instead, which is the
 *                                 same outcome by a different route.
 *
 * Only the initializers are referenced. The `lean_io_process_*` entry points
 * are not: nothing in the closure of these executables spawns a process, so
 * the linker never asks for them -- and if that ever changes, it will say so
 * rather than silently producing a binary that cannot spawn.
 */
namespace lean {
void initialize_process() {}
void finalize_process() {}
void initialize_stack_overflow() {}
void finalize_stack_overflow() {}
}
