# ruby-lean — top-level build.
#
# `make check` is the one command that says whether the repository is sound:
# it builds the model, the type checker and every proof, audits their axioms,
# and runs the model against CRuby. `make help` lists every target.
#
# Each part keeps its own build tool: Lake for the two Lean packages (ruby-lean/
# is the model, books/ is the proofs about it and the type checker), uv for
# difftest/, Bundler for the Ruby gems, and shell scripts for the browser build.
# This file names the targets and tracks the edges between those tools:
#
#   prelude/*.rb ──gen_prelude.rb──▶ PreludeJson.lean ──genprelude──▶ Prelude.lean ──lake──▶ rubycore
#   rubycore, validate-one ──wasm/build.sh──▶ *.wasm ──▶ playground/dist
#
# Written for GNU Make 3.81, which is what macOS ships.

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

# MRI's bootstraptest, harvested into desugar/corpus/ for `make conformance`.
# Pinned to the CRuby release the model is checked against.
RUBY_REF  ?= v4.0.5
RUBY_SRC  ?= $(CACHE)/ruby-src-$(RUBY_REF)
BOOTSTRAP := desugar/corpus/bootstraptest

.PHONY: help all check prereqs ci-sync deps lean lean-exes desugar difftest run \
        books metatheory soundness comparator \
        gen gen-check desugar-test desugar-coverage difftest-test conformance feature-loading \
        book-checks \
        wasm playground playground-serve docs docs-serve clean distclean

help: ## List the targets
	@awk 'BEGIN {FS = ":.*## "} /^[a-z-]+:.*## / {printf "  \033[1m%-17s\033[0m %s\n", $$1, $$2}' $(MAKEFILE_LIST)

all: lean desugar difftest run ## Build the model, the checker, the desugarer and bin/ruby-lean (no proofs)

# ── The one check ────────────────────────────────────────────────────────────
# Everything that has to hold, in dependency order, stopping at the first
# failure. CI runs exactly these targets, so a local `make check` and a CI run
# mean the same thing. Nothing here is optional and nothing is skipped.

CHECKS := prereqs ci-sync gen-check lean books metatheory soundness comparator \
          desugar-test desugar-coverage difftest-test conformance feature-loading \
          book-checks docs

check: $(CHECKS) ## Everything: build, every proof, the model against CRuby, the docs
	@echo
	@echo "make check: ALL CHECKS PASSED"

prereqs: ## Check the external tools (elan, ruby, sorbet, uv)
	@scripts/check-prereqs.sh

ci-sync: ## Fail if CI does not run every target of `make check`
	@scripts/check-ci-matches-make.sh

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

GENERATED    := $(PKG)/RubyCore/Generated
PRELUDE_LEAN := $(GENERATED)/Prelude.lean
PRELUDE_JSON := $(GENERATED)/PreludeJson.lean
PRELUDE_SRC  := $(PKG)/scripts/gen_prelude.rb $(PKG)/prelude/prelude.rb \
                $(wildcard $(PKG)/prelude/features/*.rb) $(wildcard desugar/lib/*.rb)

# Two steps. Ruby desugars the prelude to JSON (PreludeJson.lean); then a Lean
# program decodes that with the model's own decoder and prints the result as
# terms (Prelude.lean), which is what the model boots from and what the kernel
# can evaluate. `genprelude` does not import Prelude.lean, so it can always
# rebuild it.
$(PRELUDE_JSON): $(PRELUDE_SRC)
	cd $(PKG) && $(RUBY) scripts/gen_prelude.rb > RubyCore/Generated/PreludeJson.lean.tmp
	@if cmp -s $@.tmp $@; then rm $@.tmp; touch $@; else mv $@.tmp $@; echo "  regenerated $@"; fi

# Build the generator first and run the binary, so that nothing Lake prints
# while building can end up in the generated file.
GENPRELUDE := $(LAKE) build --log-level=error genprelude >&2 && .lake/build/bin/genprelude

$(PRELUDE_LEAN): $(PRELUDE_JSON) $(PKG)/GenPrelude.lean $(PKG)/RubyCore/Syntax.lean
	cd $(PKG) && $(GENPRELUDE) > RubyCore/Generated/Prelude.lean.tmp
	@if cmp -s $@.tmp $@; then rm $@.tmp; touch $@; else mv $@.tmp $@; echo "  regenerated $@"; fi

gen: ## Regenerate every generated Lean source
	cd $(PKG) && $(RUBY) scripts/gen_prelude.rb      > RubyCore/Generated/PreludeJson.lean
	cd $(PKG) && $(GENPRELUDE) > RubyCore/Generated/Prelude.lean.tmp && mv RubyCore/Generated/Prelude.lean.tmp RubyCore/Generated/Prelude.lean
	cd $(PKG) && $(RUBY) scripts/gen_cruby_names.rb  > RubyCore/Generated/CRubyNames.lean
	cd $(PKG) && $(RUBY) scripts/gen_unicode.rb --verify > RubyCore/Generated/Unicode.lean
	python3 books/Books/TypeSoundness/scripts/generate_audited_checker.py

gen-check: | $(STAMP) ## Fail if a generated Lean source is stale
	@set -e; fail=0; \
	for g in prelude:PreludeJson cruby_names:CRubyNames unicode:Unicode; do \
	  s=$${g%%:*}; f=$${g##*:}; \
	  (cd $(PKG) && $(RUBY) scripts/gen_$$s.rb) > $(STAMP)/$$f.lean; \
	  if cmp -s $(STAMP)/$$f.lean $(GENERATED)/$$f.lean; then echo "  fresh  RubyCore/Generated/$$f.lean"; \
	  else echo "  STALE  RubyCore/Generated/$$f.lean  (run: make gen)"; \
	    diff $(GENERATED)/$$f.lean $(STAMP)/$$f.lean | head -40 | cut -c1-600; fail=1; fi; \
	done; \
	(cd $(PKG) && $(GENPRELUDE)) > $(STAMP)/Prelude.lean; \
	if cmp -s $(STAMP)/Prelude.lean $(PRELUDE_LEAN); then echo "  fresh  RubyCore/Generated/Prelude.lean"; \
	else echo "  STALE  RubyCore/Generated/Prelude.lean  (run: make gen)"; \
	  diff $(PRELUDE_LEAN) $(STAMP)/Prelude.lean | head -40 | cut -c1-600; fail=1; fi; \
	python3 books/Books/TypeSoundness/scripts/generate_audited_checker.py --check || fail=1; \
	exit $$fail

# ── Lean ─────────────────────────────────────────────────────────────────────
# Lake owns Lean incrementality, so these always run it (a no-op build takes
# well under a second). `lean-exes` is the narrow one: the model's executable
# and the checker's, which is all that `run`, `difftest` and `wasm` need. The
# checker lives in books/, which uses ruby-lean/ as a library, so the two Lakes
# run one after the other and never share ruby-lean/.lake. The binaries are file
# targets on top so that the wasm rules rebuild only when Lake relinked one.

CHECKER_BIN := books/.lake/build/bin

lean-exes: $(PRELUDE_LEAN) ## Just the rubycore and validate-one executables
	cd $(PKG) && $(LAKE) build --log-level=error rubycore
	cd books && $(LAKE) build --log-level=error validate-one

lean: lean-exes ## Build the model's package (the checker and the proofs are `make books`)
	cd $(PKG) && $(LAKE) build

$(LEAN_BIN)/rubycore $(CHECKER_BIN)/validate-one: lean-exes ;

# ── The proof books ──────────────────────────────────────────────────────────
# books/ is a second Lake package that uses ruby-lean/ as a library, so these
# wait for `lean-exes`: two Lakes never build ruby-lean/.lake at once.

books: lean-exes ## Build every proof book: every file under books/Books/
	cd books && $(LAKE) build

metatheory: lean-exes ## The model's metatheory: build it, audit its axioms, check the booted heap's assumptions
	books/Books/Metatheory/scripts/check-metatheory.sh

soundness: $(PRELUDE_LEAN) $(STAMP)/uv deps ## The checker's soundness theorem, its controls, and the checker on the corpus
	books/Books/TypeSoundness/scripts/check-soundness.sh

comparator: lean-exes ## Re-check the soundness theorem with leanprover/comparator (fetches and builds it)
	books/Books/TypeSoundness/scripts/run-comparator.sh

# ── Desugarer and bin/ruby-lean ──────────────────────────────────────────────

desugar: deps ## Ruby → RubyCore JSON (desugar/bin/export-json); smoke-tests it
	@echo 'puts 1 + 2' | $(RUBY) desugar/bin/export-json > /dev/null && echo "  desugar/bin/export-json ok"

# Run from a scratch directory: the corpus programs execute under CRuby, and
# some of them (bootstraptest's autoload tests) write files into the cwd.
desugar-test: deps $(BOOTSTRAP) | $(STAMP) ## Round-trip every program in desugar/corpus/ through the desugarer, against CRuby
	@mkdir -p $(STAMP)/desugar-cwd
	cd $(STAMP)/desugar-cwd && $(RUBY) $(CURDIR)/desugar/bin/run

desugar-coverage: deps $(BOOTSTRAP) ## How much of bootstraptest the desugarer supports; fails below desugar/coverage-baseline.json
	$(RUBY) desugar/bin/coverage

run: lean-exes desugar ## Build what bin/ruby-lean and bin/ruby-lean-check need; with FILE=prog.rb, also run it
	@if [ -n "$(FILE)" ]; then bin/ruby-lean $(FILE); \
	else echo "  ready: bin/ruby-lean prog.rb, bin/ruby-lean-check prog.rb"; fi

# ── Differential testing ─────────────────────────────────────────────────────

difftest: $(STAMP)/uv lean-exes desugar ## The difftest environment; then: (cd difftest && uv run difftest --help)

$(STAMP)/uv: difftest/pyproject.toml difftest/uv.lock | $(STAMP)
	cd difftest && $(UV) sync --quiet
	@touch $@

# Some of these tests need Sorbet and the model's executable and are marked to
# skip without them. Under make both are present, so a skip is a failure.
difftest-test: $(STAMP)/uv deps lean-exes ## difftest's own unit tests
	cd difftest && DIFFTEST_NO_SKIPS=1 $(UV) run pytest -q

$(BOOTSTRAP):
	@if [ ! -d "$(RUBY_SRC)/bootstraptest" ]; then \
	  echo "  cloning ruby/ruby $(RUBY_REF) (sparse) into $(RUBY_SRC)"; \
	  git clone --depth 1 --branch $(RUBY_REF) --filter=blob:none --sparse \
	    https://github.com/ruby/ruby "$(RUBY_SRC)" && \
	  (cd "$(RUBY_SRC)" && git sparse-checkout set bootstraptest); \
	fi
	$(RUBY) desugar/bin/harvest_bootstraptest "$(RUBY_SRC)/bootstraptest"

# The model against CRuby, over three sets of programs:
#   * every program of MRI's bootstraptest. The run fails on any disagreement;
#     check-conformance.sh then fails if fewer programs agree, or more are
#     declined as unsupported, than difftest/coverage-baseline.json records;
#   * every minimized reproducer of a disagreement found in the past
#     (difftest/corpus/regressions/);
#   * the hand-written adversarial programs (difftest/corpus/tier3/).
CONFORMANCE_OUT := $(CURDIR)/$(STAMP)/conformance
DIFFTEST_RUN    := cd difftest && $(UV) run difftest

conformance: difftest $(BOOTSTRAP) ## The model against CRuby: bootstraptest, past regressions, adversarial programs
	@rm -rf $(CONFORMANCE_OUT)
	$(DIFFTEST_RUN) run --tier 0 --sut lean --out $(CONFORMANCE_OUT)
	scripts/check-conformance.sh $(CONFORMANCE_OUT)
	@for t in "run --tier regressions" "replay corpus/tier3"; do \
	  name=$${t##* }; name=$${name##*/}; \
	  if ($(DIFFTEST_RUN) $$t --sut lean --out $(CONFORMANCE_OUT)-$$name) > $(STAMP)/conformance-$$name.log 2>&1; \
	  then echo "  $$name: the model and CRuby agree"; \
	  else tail -40 $(STAMP)/conformance-$$name.log; echo "  $$name: DISAGREEMENT (report in $(CONFORMANCE_OUT)-$$name)"; exit 1; fi; \
	done

# A program book proves a theorem about the model. Its check.rb runs the same
# program under CRuby and under the model on a grid of inputs and compares both
# with what the theorem says.
book-checks: run ## Each program book's theorem against CRuby and the model (books/Books/*/check.rb)
	@set -e; for c in books/Books/*/check.rb; do echo "  $$c"; $(RUBY) $$c; done

feature-loading: lean-exes ## `require` in the model against CRuby: scope, caching, re-entry, failed loads
	python3 $(PKG)/scripts/check-feature-loading.py

# ── WebAssembly and the playground ───────────────────────────────────────────
# One stamp for both Lean modules: wasm/build.sh compiles the shared objects
# once and links each target, and two concurrent runs would race on them.

WASM_LEAN_SRC := $(PKG)/wasm/build.sh $(PKG)/wasm/patch-runtime.py \
                 $(wildcard $(PKG)/wasm/shim/*) $(wildcard $(PKG)/wasm/gen/*)
WASM_RUBY_SRC := $(PKG)/wasm/ruby/build.sh $(PKG)/wasm/ruby/prune.py \
                 $(wildcard desugar/lib/*.rb) $(wildcard desugar/bin/*) \
                 $(wildcard difftest/ruby/*.rb) \
                 books/Books/TypeSoundness/scripts/emit_deriv.rb books/Books/TypeSoundness/scripts/read_sigs.rb

$(STAMP)/wasm-lean: $(LEAN_BIN)/rubycore $(CHECKER_BIN)/validate-one $(WASM_LEAN_SRC) | $(STAMP)
	cd $(PKG) && RUBYLEAN_WASM_CACHE=$(WASM_CACHE) wasm/build.sh rubycore validate-one
	@touch $@

$(WASM_OUT)/rubycore.wasm $(WASM_OUT)/validate-one.wasm: $(STAMP)/wasm-lean ;

$(WASM_OUT)/ruby.wasm: $(WASM_RUBY_SRC) $(STAMP)/bundle
	cd $(PKG) && RUBYLEAN_WASM_CACHE=$(WASM_CACHE) wasm/ruby/build.sh

wasm: $(WASM_OUT)/rubycore.wasm $(WASM_OUT)/validate-one.wasm $(WASM_OUT)/ruby.wasm ## The three .wasm modules (Lean model, validator, CRuby + desugarer)

PLAYGROUND_SRC := playground/index.html playground/build.sh playground/mkcorpus.py \
                  $(wildcard playground/js/*.js) $(wildcard books/Books/TypeSoundness/corpus/*)

playground/dist/index.html: $(WASM_OUT)/rubycore.wasm $(WASM_OUT)/validate-one.wasm \
                            $(WASM_OUT)/ruby.wasm $(PLAYGROUND_SRC)
	playground/build.sh

playground: playground/dist/index.html ## The static playground site (playground/dist, dist.tar.gz)

playground-serve: playground ## Build the playground and serve it on :8080
	python3 -m http.server -d playground/dist 8080

# ── Docs ─────────────────────────────────────────────────────────────────────

MKDOCS := uvx --from 'mkdocs<2' --with mkdocs-material mkdocs

docs: ## Build the documentation site into site/; a broken link fails
	$(MKDOCS) build --strict

docs-serve: ## Serve the docs with live reload on :8000
	$(MKDOCS) serve

# ── Cleanup ─────────────────────────────────────────────────────────────────

clean: ## Remove build outputs in the tree (keeps .lake, venvs and caches)
	rm -rf $(STAMP) site playground/dist playground/dist.tar.gz $(WASM_OUT)/*.wasm books/Books/TypeSoundness/build

distclean: clean ## Also remove .lake, the difftest venv, harvested corpora and download caches
	rm -rf $(PKG)/.lake books/.lake difftest/.venv $(BOOTSTRAP) $(CACHE) $(WASM_CACHE)

