// A WASI preview1 shim, sized to exactly what this page runs.
//
// The five jobs are all the same shape -- argv in, stdin in, stdout/stderr out,
// exit status -- so this implements that shape and refuses everything else with
// an honest errno rather than pretending. Nothing here is a general-purpose
// WASI: there is no filesystem, because none of the modules needs one.
//
//   ruby.wasm carries its own files. `wasi-vfs` links a shim *inside* the
//   module that answers `path_open` and friends for packed paths before they
//   reach these imports, which is why a 44 MB interpreter with a full stdlib
//   runs against a host that returns ENOSYS for every path call.
//
// Kept dependency-free on purpose: the site has to work from a `file://` URL
// and off GitHub Pages with no CDN, and a shim we understand is worth more than
// one we import when the failure mode is "the checker silently did nothing".

const ERRNO_SUCCESS = 0;
const ERRNO_BADF = 8;
const ERRNO_NOSYS = 52;

// `proc_exit` is not an error; it is how a WASI command returns. Unwinding with
// a sentinel is the only way out of the module's stack.
export class WasiExit extends Error {
  constructor(code) {
    super(`exit ${code}`);
    this.code = code;
  }
}

export class Wasi {
  /** @param {string[]} args argv, argv[0] included. @param {Uint8Array} stdin */
  constructor(args, stdin) {
    this.args = args;
    this.stdinBytes = stdin;
    this.stdinPos = 0;
    this.stdout = [];
    this.stderr = [];
    this.memory = null;
    this.exitCode = null;
  }

  /** Called once the instance exists; the shim reads guest memory through it. */
  bind(instance) {
    this.memory = instance.exports.memory;
  }

  get view() {
    return new DataView(this.memory.buffer);
  }

  get bytes() {
    return new Uint8Array(this.memory.buffer);
  }

  /** Gather an iovec array into one Uint8Array (for writes). */
  #gather(iovs, count) {
    const v = this.view;
    const out = [];
    let total = 0;
    for (let i = 0; i < count; i++) {
      const ptr = v.getUint32(iovs + i * 8, true);
      const len = v.getUint32(iovs + i * 8 + 4, true);
      out.push(this.bytes.subarray(ptr, ptr + len));
      total += len;
    }
    const buf = new Uint8Array(total);
    let at = 0;
    for (const chunk of out) {
      buf.set(chunk, at);
      at += chunk.length;
    }
    return buf;
  }

  /** Scatter bytes into an iovec array (for reads); returns bytes written. */
  #scatter(iovs, count, src, from) {
    const v = this.view;
    let wrote = 0;
    for (let i = 0; i < count && from + wrote < src.length; i++) {
      const ptr = v.getUint32(iovs + i * 8, true);
      const len = v.getUint32(iovs + i * 8 + 4, true);
      const n = Math.min(len, src.length - from - wrote);
      if (n <= 0) break;
      this.bytes.set(src.subarray(from + wrote, from + wrote + n), ptr);
      wrote += n;
    }
    return wrote;
  }

  get imports() {
    const enc = new TextEncoder();
    const ok = () => ERRNO_SUCCESS;
    const nosys = () => ERRNO_NOSYS;
    const badf = () => ERRNO_BADF;

    const self = this;
    const wasi = {
      // -- process ---------------------------------------------------------
      proc_exit(code) {
        self.exitCode = code;
        throw new WasiExit(code);
      },

      args_sizes_get(countPtr, sizePtr) {
        const v = self.view;
        v.setUint32(countPtr, self.args.length, true);
        v.setUint32(sizePtr, self.args.reduce((n, a) => n + enc.encode(a).length + 1, 0), true);
        return ERRNO_SUCCESS;
      },
      args_get(argvPtr, bufPtr) {
        const v = self.view;
        let at = bufPtr;
        self.args.forEach((a, i) => {
          v.setUint32(argvPtr + i * 4, at, true);
          const b = enc.encode(a);
          self.bytes.set(b, at);
          self.bytes[at + b.length] = 0;
          at += b.length + 1;
        });
        return ERRNO_SUCCESS;
      },

      // No environment. Ruby reads RUBYOPT and friends; an empty environment is
      // the right answer rather than a guessed one.
      environ_sizes_get(countPtr, sizePtr) {
        const v = self.view;
        v.setUint32(countPtr, 0, true);
        v.setUint32(sizePtr, 0, true);
        return ERRNO_SUCCESS;
      },
      environ_get: ok,

      // -- the three standard streams --------------------------------------
      fd_read(fd, iovs, count, nreadPtr) {
        if (fd !== 0) return ERRNO_BADF;
        const n = self.#scatter(iovs, count, self.stdinBytes, self.stdinPos);
        self.stdinPos += n;
        self.view.setUint32(nreadPtr, n, true);
        return ERRNO_SUCCESS;
      },
      fd_write(fd, iovs, count, nwrittenPtr) {
        const buf = self.#gather(iovs, count);
        if (fd === 1) self.stdout.push(buf);
        else if (fd === 2) self.stderr.push(buf);
        else return ERRNO_BADF;
        self.view.setUint32(nwrittenPtr, buf.length, true);
        return ERRNO_SUCCESS;
      },
      fd_close(fd) {
        return fd <= 2 ? ERRNO_SUCCESS : ERRNO_BADF;
      },
      fd_fdstat_get(fd, ptr) {
        if (fd > 2) return ERRNO_BADF;
        const v = self.view;
        v.setUint8(ptr, 2);            // filetype: character device
        v.setUint16(ptr + 2, 0, true); // flags
        v.setBigUint64(ptr + 8, 0n, true);  // rights base
        v.setBigUint64(ptr + 16, 0n, true); // rights inheriting
        return ERRNO_SUCCESS;
      },
      // A pipe is not seekable, and Ruby asks. Saying so is what makes it treat
      // stdin as a stream rather than trying to rewind it.
      fd_seek: () => 29 /* ESPIPE */,
      fd_tell: () => 29,

      // No preopened directories: this host exposes no filesystem at all.
      fd_prestat_get: badf,
      fd_prestat_dir_name: badf,

      // -- clocks and entropy ----------------------------------------------
      clock_time_get(_id, _precision, ptr) {
        self.view.setBigUint64(ptr, BigInt(Date.now()) * 1000000n, true);
        return ERRNO_SUCCESS;
      },
      clock_res_get(_id, ptr) {
        self.view.setBigUint64(ptr, 1000000n, true);
        return ERRNO_SUCCESS;
      },
      // Every Lean executable hits this at startup (`lean_io_get_random_bytes`
      // -> `getentropy` -> `random_get`), so it is not optional.
      random_get(ptr, len) {
        crypto.getRandomValues(self.bytes.subarray(ptr, ptr + len));
        return ERRNO_SUCCESS;
      },

      // -- everything else -------------------------------------------------
      // Nothing the page runs reaches these: ruby.wasm's files are answered by
      // the wasi-vfs shim inside the module, and the Lean executables are pure
      // stdin -> stdout. If one ever is reached, ENOSYS surfaces as a real Ruby
      // or Lean error rather than as silence.
      sched_yield: ok,
      poll_oneoff: nosys,
      fd_advise: ok,
      fd_datasync: ok,
      fd_sync: ok,
      fd_renumber: nosys,
      fd_filestat_get: badf,
      fd_filestat_set_size: badf,
      fd_fdstat_set_flags: ok,
      fd_pread: badf,
      fd_pwrite: badf,
      fd_readdir: badf,
      path_open: nosys,
      path_filestat_get: nosys,
      path_filestat_set_times: nosys,
      path_create_directory: nosys,
      path_remove_directory: nosys,
      path_unlink_file: nosys,
      path_readlink: nosys,
      path_rename: nosys,
      path_link: nosys,
      path_symlink: nosys,
    };
    return { wasi_snapshot_preview1: wasi };
  }

  /** stdout as text. */
  text(which = "stdout") {
    const parts = which === "stdout" ? this.stdout : this.stderr;
    let n = 0;
    for (const p of parts) n += p.length;
    const buf = new Uint8Array(n);
    let at = 0;
    for (const p of parts) {
      buf.set(p, at);
      at += p.length;
    }
    return new TextDecoder().decode(buf);
  }
}

/**
 * Run a compiled module to completion as a WASI command.
 * @param {WebAssembly.Module} mod
 * @param {{args?: string[], stdin?: string}} opts
 * @returns {{stdout: string, stderr: string, exitCode: number}}
 */
export async function run(mod, { args = [], stdin = "" } = {}) {
  const wasi = new Wasi(["main", ...args], new TextEncoder().encode(stdin));
  const instance = await WebAssembly.instantiate(mod, wasi.imports);
  wasi.bind(instance);
  let exitCode = 0;
  try {
    instance.exports._start();
  } catch (e) {
    if (e instanceof WasiExit) exitCode = e.code;
    // A Lean `panic!` or a wasm trap arrives here. Report it as stderr and a
    // non-zero status, which is what the caller would have seen from a process.
    else {
      return {
        stdout: wasi.text("stdout"),
        stderr: wasi.text("stderr") + `\n[wasm trap] ${e && e.message ? e.message : e}`,
        exitCode: 134,
      };
    }
  }
  return { stdout: wasi.text("stdout"), stderr: wasi.text("stderr"), exitCode };
}
