#!/usr/bin/env bash
# Package the playground as a static site, for GitHub Pages or a `file://` URL.
#
#   playground/build.sh              # -> playground/dist/ and playground/dist.tar.gz
#   playground/build.sh --serve      # ... then serve it on :8080 to look at it
#
# Output is self-contained: no CDN, no server, no network at run time. Drop
# `dist/` on any static host, or hand someone `dist.tar.gz`.
#
# The same `index.html` runs both ways. `config.js` -- written here and absent
# from the source tree -- is the only difference: it sets the backend to `wasm`.
# A checkout served by `server.py` has no `config.js`, so it defaults to the
# server, and `?backend=wasm` / `?backend=server` overrides either. That is why
# the fallback stays honest rather than rotting: it is the same page.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PKG="$HERE/../ruby-lean"
WASM="$PKG/wasm/out"
DIST="$HERE/dist"

say() { printf '\033[1m==>\033[0m %s\n' "$*"; }

MODULES=(ruby rubycore validate-one)
for m in "${MODULES[@]}"; do
  [ -f "$WASM/$m.wasm" ] || {
    echo "missing $WASM/$m.wasm"
    echo "  build the Lean side with:  (cd $PKG && wasm/build.sh)"
    echo "  and the Ruby side with:    (cd $PKG && wasm/ruby/build.sh)"
    exit 1
  }
done

say "assembling $DIST"
rm -rf "$DIST"
mkdir -p "$DIST/js" "$DIST/wasm"

cp "$HERE/index.html" "$DIST/"
cp "$HERE/js/"*.js "$DIST/js/"
for m in "${MODULES[@]}"; do cp "$WASM/$m.wasm" "$DIST/wasm/"; done

cat > "$DIST/config.js" <<'EOF'
// Written by playground/build.sh. Its presence is what makes this a static
// build: with no server to talk to, every stage runs in this tab.
window.PLAYGROUND_BACKEND = "wasm";
window.PLAYGROUND_WASM_BASE = "wasm/";
EOF
# `config.js` is a plain script, loaded before the module so the module sees it.
python3 - "$DIST/index.html" <<'EOF'
import sys, pathlib
p = pathlib.Path(sys.argv[1]); t = p.read_text()
t = t.replace('<script type="module">', '<script src="config.js"></script>\n<script type="module">', 1)
p.write_text(t)
EOF

say "baking the corpus"
python3 "$HERE/mkcorpus.py" "$DIST/corpus.json"

# GitHub Pages runs Jekyll by default, which ignores files and directories
# beginning with an underscore and can rewrite things it thinks are templates.
touch "$DIST/.nojekyll"

say "archiving"
tar czf "$HERE/dist.tar.gz" -C "$HERE" dist

printf '\n'
say "sizes"
( cd "$DIST" && find . -type f ! -name '.*' -exec ls -l {} \; \
  | awk '{printf "    %-28s %8.1f MB\n", $NF, $5/1048576}' | sort )
raw=$(du -sk "$DIST" | cut -f1)
arc=$(du -k "$HERE/dist.tar.gz" | cut -f1)
printf '    %-28s %8.1f MB\n' "(total on disk)" "$(echo "$raw/1024" | bc -l)"
printf '    %-28s %8.1f MB\n' "dist.tar.gz" "$(echo "$arc/1024" | bc -l)"

cat <<EOF

  GitHub Pages: the per-file limit is 100 MB and ruby.wasm is the big one.
  Pages gzips on the wire, so the transfer is roughly the gzipped size, not the
  figure above. Nothing here is fetched from a third party.

  Local check:  python3 -m http.server -d $DIST 8080
  Fallback:     python3 $HERE/server.py     (the same page, native binaries)
EOF

if [ "${1:-}" = "--serve" ]; then
  say "serving $DIST on http://localhost:8080"
  exec python3 -m http.server -d "$DIST" 8080
fi
