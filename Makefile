# Makefile for Mugda (Constructive Lean 4 Edition)

LAKE ?= lake
MUGDA := .lake/build/bin/mugda

POS_EXAMPLES := \
	examples/acc.ma \
	examples/addWith.ma \
	examples/fib.ma \
	examples/goodterm.ma \
	examples/ho.ma \
	examples/infbranch.ma \
	examples/inverse.ma \
	examples/k.ma \
	examples/nat.ma \
	examples/ord.ma \
	examples/pair.ma \
	examples/procs.ma \
	examples/sigma.ma \
	examples/simple.ma \
	examples/slist.ma \
	examples/sord.ma \
	examples/sort.ma \
	examples/sp.ma \
	examples/sqsort.ma \
	examples/str.ma \
	examples/stree.ma \
	examples/vec.ma

NEG_EXAMPLES := \
	examples/counterexamples/cody_nowraps.ma \
	examples/counterexamples/cody_simplified.ma \
	examples/counterexamples/llet_bug.ma \
	examples/counterexamples/loop_wrapped.ma \
	examples/counterexamples/overlap_bug.ma \
	examples/counterexamples/snat_mat_bug.ma \
	examples/counterexamples/stree_mat_bug.ma \
	examples/loop.ma \
	examples/loop2.ma \
	examples/loop3.ma \
	examples/rose.ma \
	examples/badterm.ma \
	examples/badterm2.ma \
	examples/badterm3.ma \
	examples/badterm4.ma \
	examples/badadm.ma \
	examples/badco.ma \
	examples/badlist.ma

.PHONY: all build test check-axioms golden golden-update test-js showcase check-showcase clean

all: build

build:
	$(LAKE) build

check-axioms:
	@echo "--- Checking for sorry / partial / unsafe in Lean sources ---"
	@! grep -En '(^|[^`a-zA-Z0-9_])(sorry|partial[[:space:]]+def|unsafe[[:space:]]+def)([^`a-zA-Z0-9_]|$$)' Mugda.lean Main.lean Mugda/*.lean
	@echo "Zero sorry, zero partial, zero unsafe verified."

test: build check-axioms
	@echo "=== Running 22 Positive Benchmarks (must succeed) ==="
	@for f in $(POS_EXAMPLES); do \
		echo "[PASS-CHECK] $$f"; \
		$(MUGDA) "$$f" > /dev/null || exit 1; \
	done
	@echo "=== Running 18 Negative Counterexamples (must be rejected) ==="
	@for f in $(NEG_EXAMPLES); do \
		echo "[REJECT-CHECK] $$f"; \
		if [ ! -f "$$f" ]; then echo "ERROR: $$f does not exist!"; exit 1; fi; \
		if $(MUGDA) "$$f" > /dev/null 2>&1; then \
			echo "ERROR: $$f was unexpectedly accepted!"; \
			exit 1; \
		fi; \
	done
	@echo "All 22 positive benchmarks and 18 negative counterexamples verified."
	@$(MAKE) --no-print-directory check-showcase
	@echo "=== Golden output snapshots (every examples/**/*.ma) ==="
	@tests/golden.sh

# Golden-output regression: compare stdout/stderr/exit code of every example
# against tests/expected/. After an intended change, run `make golden-update`
# and review the diff.
golden: build
	@tests/golden.sh

golden-update: build
	@tests/golden.sh --update

# Differential test: browser playground engine (docs/mugda-engine.js) vs Lean checker.
test-js: build
	@node tests/js-vs-lean.mjs

# The showcase project is written as several parts (Mugda has no imports) and
# concatenated into one checkable program.
SHOWCASE_DIR := examples/showcase/sizedlib
showcase:
	@if [ -d $(SHOWCASE_DIR)/src ]; then \
		cat $(SHOWCASE_DIR)/src/*.ma > $(SHOWCASE_DIR)/sizedlib.ma; \
		echo "wrote $(SHOWCASE_DIR)/sizedlib.ma"; \
	fi

check-showcase:
	@if [ -d $(SHOWCASE_DIR)/src ]; then \
		cat $(SHOWCASE_DIR)/src/*.ma | cmp -s - $(SHOWCASE_DIR)/sizedlib.ma || \
		{ echo "ERROR: $(SHOWCASE_DIR)/sizedlib.ma is out of date; run 'make showcase'"; exit 1; }; \
		echo "Showcase sizedlib.ma is up to date with src/."; \
	fi

clean:
	$(LAKE) clean
