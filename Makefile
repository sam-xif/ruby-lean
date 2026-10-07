# ruby-lean — top-level build.
#
# Each piece keeps its own build tool: Lake for the two Lean packages (ruby-lean/
# for the model and the checker, books/ for the proofs about them), uv for difftest/, Bundler for the Ruby gems, and the shell scripts under
# ruby-lean/wasm/ and playground/ for the browser build. This file only names
# the targets and wires the edges *between* those tools, which nothing else
# tracks:
#
#   desugar/ ──gen_prelude.rb──▶ RubyCore/PreludeJson.lean ──genprelude──▶ RubyCore/Prelude.lean ──lake──▶ rubycore
#   rubycore, validate-one ──wasm/build.sh──▶ *.wasm ──▶ playground/dist
#   desugar/, strip chain ──wasm/ruby/build.sh──▶ ruby.wasm ──▶ playground/dist
#
# `make help` lists the targets. Written for GNU Make 3.81 (what macOS ships).

SHELL := /bin/bash
.DEFAULT_GOAL := help

RUBY  ?= ruby
LAKE  ?= lake
UV    ?= uv

PKG       := ruby-lean
LEAN_BIN  := $(PKG)/.lake/build/bin
WASM_OUT  := $(PKG)/wasm/out
STAMP     := .make
CACHE     ?= $(HOME)/.cache/ruby-lean
WASM_CACHE ?= $(HOME)/.cache/ruby-lean-wasm

# MRI's bootstraptest, harvested into desugar/corpus/ for `make bootstraptest`.
# Pinned to the CRuby release the model is checked against.
RUBY_REF  ?= v4.0.5
RUBY_SRC  ?= $(CACHE)/ruby-src-$(RUBY_REF)
BOOTSTRAP := desugar/corpus/bootstraptest

.PHONY: help all prereqs deps lean lean-exes desugar difftest run proofs books comparator gate check \
        gen gen-check desugar-test difftest-test bootstraptest \
        wasm playground playground-serve docs docs-serve clean distclean

help: ## List the targets
	@awk 'BEGIN {FS = ":.*## "} /^[a-z-]+:.*## / {printf "  \033[1m%-17s\033[0m %s\n", $$1, $$2}' $(MAKEFILE_LIST)

all: lean desugar difftest run ## Lean package, desugarer, difftest and bin/ruby-lean (not proofs or wasm)

prereqs: ## Check the external tools (elan, ruby, sorbet, uv)
	@scripts/check-prereqs.sh

$(STAMP):
	@mkdir -p $@

# ── Ruby gems ────────────────────────────────────────────────────────────────

deps: $(STAMP)/bundle ## Install the pinned Ruby gems (Gemfile.lock)

$(STAMP)/bundle: Gemfile Gemfile.lock | $(STAMP)
	bundle check >/dev/null 2>&1 || bundle install
	@touch $@

# ── Generated Lean sources ───────────────────────────────────────────────────
# Committed, so a checkout builds without Ruby; regenerated here so they cannot
# drift from their inputs. Only Prelude.lean is a make dependency of the Lean
# build: it is the one whose input (the desugarer) changes in ordinary work. The
# CRuby name and Unicode tables follow the oracle's version, so they regenerate
# only on an explicit `make gen`; `make gen-check` catches all four.

PRELUDE_LEAN := $(PKG)/RubyCore/Prelude.lean
PRELUDE_JSON := $(PKG)/RubyCore/PreludeJson.lean
PRELUDE_SRC  := $(PKG)/scripts/gen_prelude.rb $(PKG)/prelude/prelude.rb \
                $(wildcard $(PKG)/prelude/features/*.rb) $(wildcard desugar/lib/*.rb)

# Two steps. Ruby desugars the prelude to JSON (PreludeJson.lean); then a Lean
# program decodes that with the model's own decoder and prints the result as
# terms (Prelude.lean), which is what the model boots from and what the kernel
# can evaluate. `genprelude` does not import Prelude.lean, so it can always
# rebuild it.
$(PRELUDE_JSON): $(PRELUDE_SRC)
	cd $(PKG) && $(RUBY) scripts/gen_prelude.rb > RubyCore/PreludeJson.lean.tmp
	@if cmp -s $@.tmp $@; then rm $@.tmp; touch $@; else mv $@.tmp $@; echo "  regenerated $@"; fi

$(PRELUDE_LEAN): $(PRELUDE_JSON) $(PKG)/GenPrelude.lean $(PKG)/RubyCore/Syntax.lean
	cd $(PKG) && $(LAKE) -q exe genprelude > RubyCore/Prelude.lean.tmp
	@if cmp -s $@.tmp $@; then rm $@.tmp; touch $@; else mv $@.tmp $@; echo "  regenerated $@"; fi

gen: ## Regenerate every generated Lean source
	cd $(PKG) && $(RUBY) scripts/gen_prelude.rb      > RubyCore/PreludeJson.lean
	cd $(PKG) && $(LAKE) -q exe genprelude > RubyCore/Prelude.lean.tmp && mv RubyCore/Prelude.lean.tmp RubyCore/Prelude.lean
	cd $(PKG) && $(RUBY) scripts/gen_cruby_names.rb  > RubyCore/CRubyNames.lean
	cd $(PKG) && $(RUBY) scripts/gen_unicode.rb --verify > RubyCore/Unicode.lean
	cd $(PKG) && python3 scripts/generate_audited_checker.py

gen-check: | $(STAMP) ## Fail if a generated Lean source is stale
	@set -e; fail=0; \
	for g in prelude:PreludeJson cruby_names:CRubyNames unicode:Unicode; do \
	  s=$${g%%:*}; f=$${g##*:}; \
	  (cd $(PKG) && $(RUBY) scripts/gen_$$s.rb) > $(STAMP)/$$f.lean; \
	  if cmp -s $(STAMP)/$$f.lean $(PKG)/RubyCore/$$f.lean; then echo "  fresh  RubyCore/$$f.lean"; \
	  else echo "  STALE  RubyCore/$$f.lean  (run: make gen)"; fail=1; fi; \
	done; \
	(cd $(PKG) && $(LAKE) -q exe genprelude) > $(STAMP)/Prelude.lean; \
	if cmp -s $(STAMP)/Prelude.lean $(PKG)/RubyCore/Prelude.lean; then echo "  fresh  RubyCore/Prelude.lean"; \
	else echo "  STALE  RubyCore/Prelude.lean  (run: make gen)"; fail=1; fi; \
	(cd $(PKG) && python3 scripts/generate_audited_checker.py --check) || fail=1; \
	exit $$fail

# ── Lean ─────────────────────────────────────────────────────────────────────
# Lake owns Lean incrementality, so these always run it (a no-op build takes
# well under a second). `lean-exes` is the narrow one: the model and the
# validator executables, which is all that `run`, `difftest` and `wasm` need,
# so a broken proof elsewhere in the package does not block them. The binaries
# are file targets on top so that the wasm rules rebuild only when Lake actually
# relinked one. `lean` waits for `lean-exes` so two Lakes never share .lake/.

lean-exes: $(PRELUDE_LEAN) ## Just the rubycore and validate-one executables
	cd $(PKG) && $(LAKE) build --log-level=error rubycore validate-one

lean: lean-exes ## Build the Lean package: the model and the checker (the proofs are `make books`)
	cd $(PKG) && $(LAKE) build

$(LEAN_BIN)/rubycore $(LEAN_BIN)/validate-one: lean-exes ;

# ── The proof books ──────────────────────────────────────────────────────────
# books/ is a second Lake package that uses ruby-lean/ as a library, so these
# wait for `lean-exes`: two Lakes never build ruby-lean/.lake at once.

books: lean-exes ## Every proof book: every file under books/Books/ (soundness theorem, metatheory, program proofs)
	cd books && $(LAKE) build

proofs: lean-exes ## Build the metatheory (books/Books/Metatheory/) and check every theorem's axioms
	cd books && ./scripts/check-proofs.sh

comparator: lean-exes ## Check the soundness theorem with leanprover/comparator (fetches and builds it)
	cd books && ./scripts/run-comparator.sh

gate: $(PRELUDE_LEAN) ## The typed ratchet gate — must be GREEN before a commit
	cd books && ./scripts/run_typed_ratchet.sh

# ── Desugarer and bin/ruby-lean ──────────────────────────────────────────────

desugar: deps ## Ruby → RubyCore JSON (desugar/bin/export-json); smoke-tests it
	@echo 'puts 1 + 2' | $(RUBY) desugar/bin/export-json > /dev/null && echo "  desugar/bin/export-json ok"

# Run from a scratch directory: the corpus programs execute under CRuby, and
# some of them (bootstraptest's autoload tests) write files into the cwd.
desugar-test: deps | $(STAMP) ## The desugar round-trip over desugar/corpus/
	@mkdir -p $(STAMP)/desugar-cwd
	cd $(STAMP)/desugar-cwd && $(RUBY) $(CURDIR)/desugar/bin/run

run: lean-exes desugar ## Build what bin/ruby-lean needs; with FILE=prog.rb, also run it
	@if [ -n "$(FILE)" ]; then bin/ruby-lean $(FILE); \
	else echo "  ready: bin/ruby-lean prog.rb   (or: make run FILE=prog.rb)"; fi

# ── Differential testing ─────────────────────────────────────────────────────

difftest: $(STAMP)/uv lean-exes desugar ## The difftest environment; then: (cd difftest && uv run difftest --help)

$(STAMP)/uv: difftest/pyproject.toml difftest/uv.lock | $(STAMP)
	cd difftest && $(UV) sync --quiet
	@touch $@

difftest-test: $(STAMP)/uv deps ## difftest's own unit tests
	cd difftest && $(UV) run pytest -q

$(BOOTSTRAP):
	@if [ ! -d "$(RUBY_SRC)/bootstraptest" ]; then \
	  echo "  cloning ruby/ruby $(RUBY_REF) (sparse) into $(RUBY_SRC)"; \
	  git clone --depth 1 --branch $(RUBY_REF) --filter=blob:none --sparse \
	    https://github.com/ruby/ruby "$(RUBY_SRC)" && \
	  (cd "$(RUBY_SRC)" && git sparse-checkout set bootstraptest); \
	fi
	$(RUBY) desugar/bin/harvest_bootstraptest "$(RUBY_SRC)/bootstraptest"

bootstraptest: difftest $(BOOTSTRAP) ## Differential run: the model vs CRuby over MRI's bootstraptest
	cd difftest && $(UV) run difftest run --tier 0 --sut lean

# ── WebAssembly and the playground ───────────────────────────────────────────
# One stamp for both Lean modules: wasm/build.sh compiles the shared objects
# once and links each target, and two concurrent runs would race on them.

WASM_LEAN_SRC := $(PKG)/wasm/build.sh $(PKG)/wasm/patch-runtime.py \
                 $(wildcard $(PKG)/wasm/shim/*) $(wildcard $(PKG)/wasm/gen/*)
WASM_RUBY_SRC := $(PKG)/wasm/ruby/build.sh $(PKG)/wasm/ruby/prune.py \
                 $(wildcard desugar/lib/*.rb) $(wildcard desugar/bin/*) \
                 $(wildcard difftest/ruby/*.rb) \
                 $(PKG)/scripts/emit_deriv.rb $(PKG)/scripts/read_sigs.rb

$(STAMP)/wasm-lean: $(LEAN_BIN)/rubycore $(LEAN_BIN)/validate-one $(WASM_LEAN_SRC) | $(STAMP)
	cd $(PKG) && RUBYLEAN_WASM_CACHE=$(WASM_CACHE) wasm/build.sh rubycore validate-one
	@touch $@

$(WASM_OUT)/rubycore.wasm $(WASM_OUT)/validate-one.wasm: $(STAMP)/wasm-lean ;

$(WASM_OUT)/ruby.wasm: $(WASM_RUBY_SRC) $(STAMP)/bundle
	cd $(PKG) && RUBYLEAN_WASM_CACHE=$(WASM_CACHE) wasm/ruby/build.sh

wasm: $(WASM_OUT)/rubycore.wasm $(WASM_OUT)/validate-one.wasm $(WASM_OUT)/ruby.wasm ## The three .wasm modules (Lean model, validator, CRuby + desugarer)

PLAYGROUND_SRC := playground/index.html playground/build.sh playground/mkcorpus.py \
                  $(wildcard playground/js/*.js) $(wildcard books/corpus/*)

playground/dist/index.html: $(WASM_OUT)/rubycore.wasm $(WASM_OUT)/validate-one.wasm \
                            $(WASM_OUT)/ruby.wasm $(PLAYGROUND_SRC)
	playground/build.sh

playground: playground/dist/index.html ## The static playground site (playground/dist, dist.tar.gz)

playground-serve: playground ## Build the playground and serve it on :8080
	python3 -m http.server -d playground/dist 8080

# ── Docs ─────────────────────────────────────────────────────────────────────

MKDOCS := uvx --from 'mkdocs<2' --with mkdocs-material mkdocs

docs: ## The MkDocs site (site/)
	$(MKDOCS) build

docs-serve: ## Serve the docs with live reload on :8000
	$(MKDOCS) serve

# ── Aggregates and cleanup ───────────────────────────────────────────────────

check: gen-check desugar-test difftest-test gate ## Everything that should pass before a commit (proofs separately)

clean: ## Remove build outputs in the tree (keeps .lake, venvs and caches)
	rm -rf $(STAMP) site playground/dist playground/dist.tar.gz $(WASM_OUT)/*.wasm books/build

distclean: clean ## Also remove .lake, the difftest venv, harvested corpora and download caches
	rm -rf $(PKG)/.lake books/.lake difftest/.venv $(BOOTSTRAP) $(CACHE) $(WASM_CACHE)

