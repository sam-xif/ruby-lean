#!/usr/bin/env bash
# Build `ruby.wasm` — CRuby, the desugar harness, the strip chain and
# sorbet-runtime, packed into one self-contained WebAssembly module.
#
#   wasm/ruby/build.sh        # -> wasm/out/ruby.wasm
#
# This is the *other half* of the playground's pipeline. `wasm/build.sh` gets
# the Lean side into the browser; this gets the Ruby side, which is five
# distinct jobs the page needs, all of them the same interpreter:
#
#   harness/desugar-dt/bin/export-json   Ruby source -> RubyCore JSON
#   difftest/ruby/*_strip.rb             the six-stage strip chain
#   the program itself                   the CRuby oracle, "Run in CRuby"
#
# The oracle is the reason this is worth doing rather than faking: it is real
# CRuby, the same 4.0 series the difftest gate runs against, so the page can
# keep comparing the model to an oracle rather than to a story about one.
#
# Nothing in `harness/` or `difftest/ruby/` is modified or vendored-with-edits.
# The files are copied in as they are; if they work here they work there.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PKG="$(dirname "$(dirname "$HERE")")"          # ruby-lean/
ROOT="$(dirname "$PKG")"                       # the workspace root
OUT="$(dirname "$HERE")/out"
CACHE="${RUBYLEAN_WASM_CACHE:-$HOME/.cache/ruby-lean-wasm}/ruby"

# The ruby.wasm nightly to pin. `wasip1` (not the `-js` variant) because the
# page runs this module through the same WASI shim as rubycore.wasm — one
# runner, three modules, all of them stdin -> stdout.
RUBY_WASM_RELEASE="${RUBY_WASM_RELEASE:-2026-09-15-a}"
RUBY_WASM_BUILD="${RUBY_WASM_BUILD:-ruby-4.0-wasm32-unknown-wasip1-full}"
WASI_VFS_VERSION="${WASI_VFS_VERSION:-v0.6.3}"

STRIP_CHAIN=(sig_strip visibility_strip freeze_strip require_strip
             const_inline class_sugar_strip)

say() { printf '\033[1m==>\033[0m %s\n' "$*"; }

mkdir -p "$CACHE" "$OUT"

# ── 1. the interpreter ───────────────────────────────────────────────────────
DIST="$CACHE/$RUBY_WASM_BUILD"
if [ ! -x "$DIST/usr/local/bin/ruby" ]; then
  say "fetching $RUBY_WASM_BUILD ($RUBY_WASM_RELEASE)"
  curl -fsSL -o "$CACHE/ruby.tar.gz" \
    "https://github.com/ruby/ruby.wasm/releases/download/$RUBY_WASM_RELEASE/$RUBY_WASM_BUILD.tar.gz"
  tar xzf "$CACHE/ruby.tar.gz" -C "$CACHE"
fi

# ── 2. the packer ────────────────────────────────────────────────────────────
VFS="$CACHE/wasi-vfs/wasi-vfs"
if [ ! -x "$VFS" ]; then
  say "fetching wasi-vfs $WASI_VFS_VERSION"
  case "$(uname -s)-$(uname -m)" in
    Darwin-arm64) VFS_ASSET=wasi-vfs-cli-aarch64-apple-darwin.zip ;;
    Darwin-x86_64) VFS_ASSET=wasi-vfs-cli-x86_64-apple-darwin.zip ;;
    Linux-aarch64) VFS_ASSET=wasi-vfs-cli-aarch64-unknown-linux-gnu.zip ;;
    Linux-x86_64) VFS_ASSET=wasi-vfs-cli-x86_64-unknown-linux-gnu.zip ;;
    *) echo "no wasi-vfs build for $(uname -s)-$(uname -m)"; exit 1 ;;
  esac
  curl -fsSL -o "$CACHE/wasi-vfs.zip" \
    "https://github.com/kateinoigakukun/wasi-vfs/releases/download/$WASI_VFS_VERSION/$VFS_ASSET"
  unzip -oq "$CACHE/wasi-vfs.zip" -d "$CACHE/wasi-vfs"
  chmod +x "$VFS"
fi

# ── 3. stage the guest filesystem ────────────────────────────────────────────
# Rebuilt from scratch each run, so a stale file cannot survive into the image.
STAGE="$CACHE/stage"
rm -rf "$STAGE"
mkdir -p "$STAGE/usr/local/lib" "$STAGE/opt/desugar" "$STAGE/opt/strip" "$STAGE/opt/deriv"

say "staging the guest filesystem"
# Only `lib/ruby` is runtime. The distribution also ships `libruby-static.a`
# (24 MB) and the C headers, for building extensions, and `bin/ruby` itself —
# packing that would put the interpreter inside its own filesystem.
cp -R "$DIST/usr/local/lib/ruby" "$STAGE/usr/local/lib/"

cp -R "$ROOT/harness/desugar-dt/lib" "$ROOT/harness/desugar-dt/bin" "$STAGE/opt/desugar/"
for s in "${STRIP_CHAIN[@]}"; do
  cp "$ROOT/difftest/ruby/$s.rb" "$STAGE/opt/strip/"
done

# The typed ladder's untrusted stages, ported to Ruby so the page can re-derive
# for a program the user has *edited* rather than only replay a stored rung.
# `read_sigs.rb` replaces `srb_sigs.py`: Sorbet is C++ with no wasm port, and
# shipping each rung's stored sigs.json would go stale the moment the buffer
# changes. Reading signatures off the source is sound rather than a shortcut --
# `Ratchet/Deriv.lean` re-derives every declared type, so a weaker reader costs
# blocks and rejects, never a wrong accept. Sorbet's *verdict* is a different
# thing and is not faked; `read_sigs.rb` reports `"verdict": "not-checked"`.
cp "$PKG/scripts/emit_deriv.rb" "$PKG/scripts/read_sigs.rb" "$STAGE/opt/deriv/"

# sorbet-runtime is pure Ruby and not a default gem, so it is not in the
# distribution — but eleven corpus programs `require` it, and without it the
# oracle cannot run them. Dropped into `site_ruby` rather than installed as a
# gem: that is on the default load path, so `require` finds it with no
# RubyGems activation and no gemspec to keep in sync.
SR_LIB="$(gem which sorbet-runtime 2>/dev/null | xargs -r dirname || true)"
STDLIB_VER="$(basename "$(ls -d "$STAGE"/usr/local/lib/ruby/[0-9]*.[0-9]*.[0-9]* | head -1)")"
if [ -n "$SR_LIB" ] && [ -d "$SR_LIB" ]; then
  mkdir -p "$STAGE/usr/local/lib/ruby/site_ruby/$STDLIB_VER"
  cp -R "$SR_LIB"/* "$STAGE/usr/local/lib/ruby/site_ruby/$STDLIB_VER/"
  say "vendored sorbet-runtime from $SR_LIB"
else
  echo "  WARNING: sorbet-runtime not found on the host; the 11 corpus programs"
  echo "           that require it will fail in the oracle. \`gem install sorbet-runtime\`"
fi

python3 "$HERE/prune.py" "$STAGE"

# ── 4. pack ──────────────────────────────────────────────────────────────────
say "packing"
"$VFS" pack "$DIST/usr/local/bin/ruby" \
  --dir "$STAGE/usr::/usr" --dir "$STAGE/opt::/opt" \
  -o "$OUT/ruby.wasm"

sz=$(stat -f%z "$OUT/ruby.wasm" 2>/dev/null || stat -c%s "$OUT/ruby.wasm")
gz=$(gzip -9 -c "$OUT/ruby.wasm" | wc -c | tr -d ' ')
printf '    %s  %.1f MB (%.1f MB gzipped)\n' "$OUT/ruby.wasm" \
  "$(echo "$sz/1048576" | bc -l)" "$(echo "$gz/1048576" | bc -l)"

# ── 5. smoke test ────────────────────────────────────────────────────────────
# Self-contained: no --dir, because the filesystem is inside the module now.
say "smoke test"
printf 'a = 1\nputs a + 2\n' \
  | wasmtime "$OUT/ruby.wasm" /opt/desugar/bin/export-json \
  | head -c 70
echo
printf 'sig { returns(Integer) }\ndef f\n  1\nend\nf\n' \
  | wasmtime "$OUT/ruby.wasm" /opt/deriv/read_sigs.rb | head -c 110
echo
say "done -- run wasm/ruby/verify.sh for the full differential"
