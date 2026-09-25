#!/usr/bin/env bash
# Differential: every Ruby job the playground runs, packed module vs the host's
# own CRuby, over the whole corpus.
#
#   wasm/ruby/verify.sh              # all three jobs, all 259 programs
#   wasm/ruby/verify.sh desugar      # one job
#
# Three jobs, because the page needs three and they fail in different ways:
#
#   desugar   `export-json`: Ruby source -> RubyCore JSON. Compared byte for
#             byte, because the Lean side parses the result.
#   strip     the six-stage strip chain, run as a pipeline the way
#             `certify-file.sh` runs it. Compared byte for byte.
#   oracle    the program itself, under CRuby. Compared on stdout, exit status
#             *and* stderr.
#   deriv     `read_sigs.rb` then `emit_deriv.rb`: the typed ladder's two
#             untrusted stages. Compared byte for byte on the emitted Deriv.
#
# `deriv` checks the *port* -- the same Ruby, host versus wasm. Whether reading
# signatures with Prism agrees with reading them out of Sorbet is a different
# axis, and `scripts/cmp_sig_readers.py` is where that is measured.
#
# Everything is fed on **stdin**, which is how the page will do it -- there is
# no writable filesystem in the packed module, and none in a browser tab. It
# also makes the comparison stricter than the server does: with no script file
# to read back, `error_highlight` adds no source snippet on either side, so
# stderr matches exactly rather than approximately.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PKG="$(dirname "$(dirname "$HERE")")"
ROOT="$(dirname "$PKG")"
RUBY_WASM="$(dirname "$HERE")/out/ruby.wasm"
CORPUS="$PKG/corpus"
JOBS="$(sysctl -n hw.ncpu 2>/dev/null || nproc)"
ONLY="${1:-all}"

[ -f "$RUBY_WASM" ] || { echo "no $RUBY_WASM -- run wasm/ruby/build.sh"; exit 1; }

export RUBY_WASM ROOT HERE ONLY
cat > "${TMPDIR:-/tmp}/rl-verify-one.sh" <<'EOF'
#!/usr/bin/env bash
# One program, all selected jobs. Prints one `<job> OK|DIFF <name>` per job.
f="$1"; name="$(basename "$f" .rb)"
w() { wasmtime "$RUBY_WASM" "$@"; }
CHAIN="sig_strip visibility_strip freeze_strip require_strip const_inline class_sugar_strip"

if [ "$ONLY" = all ] || [ "$ONLY" = desugar ]; then
  a=$(ruby "$ROOT/desugar/bin/export-json" < "$f" 2>&1; echo "rc=$?")
  b=$(w /opt/desugar/bin/export-json < "$f" 2>&1; echo "rc=$?")
  [ "$a" = "$b" ] && echo "desugar OK" || echo "desugar DIFF $name"
fi

if [ "$ONLY" = all ] || [ "$ONLY" = strip ]; then
  a=$(cat "$f"); b=$a
  for s in $CHAIN; do a=$(printf '%s' "$a" | ruby "$ROOT/difftest/ruby/$s.rb" 2>&1); done
  for s in $CHAIN; do b=$(printf '%s' "$b" | w "/opt/strip/$s.rb" 2>&1); done
  [ "$a" = "$b" ] && echo "strip OK" || echo "strip DIFF $name"
fi

if [ "$ONLY" = all ] || [ "$ONLY" = deriv ]; then
  a=$(ruby "$ROOT/ruby-lean/scripts/read_sigs.rb" < "$f" 2>&1)
  b=$(w /opt/deriv/read_sigs.rb < "$f" 2>&1)
  if [ "$a" = "$b" ]; then
    ast="$ROOT/ruby-lean/build/$name.ast.json"
    if [ -f "$ast" ]; then
      payload=$(python3 -c 'import json,sys; print(json.dumps({"ast": json.load(open(sys.argv[1])), "sigs": json.loads(sys.argv[2])}))' "$ast" "$a")
      da=$(printf '%s' "$payload" | ruby "$ROOT/ruby-lean/scripts/emit_deriv.rb" 2>&1)
      db=$(printf '%s' "$payload" | w /opt/deriv/emit_deriv.rb 2>&1)
      [ "$da" = "$db" ] && echo "deriv OK" || echo "deriv DIFF $name"
    else
      echo "deriv OK"
    fi
  else
    echo "deriv DIFF $name"
  fi
fi

if [ "$ONLY" = all ] || [ "$ONLY" = oracle ]; then
  # `error_highlight` annotates some exceptions with extra lines -- for an arity
  # mismatch, `caller:`/`callee:` locations. It is active on the host and not in
  # the ruby.wasm build, which has no `RubyVM::AbstractSyntaxTree`. The exception
  # class, message, backtrace and exit status are unaffected, so both sides are
  # stripped of it rather than the difference being called a disagreement.
  eh() { sed -e '/^[[:space:]]*caller: /d' -e '/^[[:space:]]*callee: /d' -e '/^$/d'; }
  src=$(cat "$f")
  ao=$(printf '%s' "$src" | ruby 2>/dev/null); arc=$?
  ae=$(printf '%s' "$src" | ruby 2>&1 >/dev/null | eh)
  bo=$(printf '%s' "$src" | w 2>/dev/null); brc=$?
  be=$(printf '%s' "$src" | w 2>&1 >/dev/null | eh)
  if [ "$ao" = "$bo" ] && [ "$arc" = "$brc" ] && [ "$ae" = "$be" ]; then
    echo "oracle OK"
  else
    echo "oracle DIFF $name"
    [ "$ao" = "$bo" ] || printf '    stdout host=%s wasm=%s\n' "${ao:0:70}" "${bo:0:70}"
    [ "$arc" = "$brc" ] || printf '    exit   host=%s wasm=%s\n' "$arc" "$brc"
    [ "$ae" = "$be" ] || printf '    stderr host=%s wasm=%s\n' "${ae:0:70}" "${be:0:70}"
  fi
fi
EOF
chmod +x "${TMPDIR:-/tmp}/rl-verify-one.sh"

n=$(ls "$CORPUS"/*.rb | wc -l | tr -d ' ')
echo "corpus: $n programs · jobs: $ONLY · $JOBS-way parallel"
res="${TMPDIR:-/tmp}/rl-verify-results.txt"
ls "$CORPUS"/*.rb | xargs -P "$JOBS" -n 1 "${TMPDIR:-/tmp}/rl-verify-one.sh" > "$res" 2>&1

rc=0
for job in desugar strip deriv oracle; do
  ok=$(grep -c "^$job OK"   "$res" || true)
  bad=$(grep -c "^$job DIFF" "$res" || true)
  [ "$ok" = 0 ] && [ "$bad" = 0 ] && continue
  printf '  %-8s %3d agree, %d disagree\n' "$job" "$ok" "$bad"
  [ "$bad" = 0 ] || rc=1
done
grep -A3 'DIFF' "$res" | head -40
exit $rc
