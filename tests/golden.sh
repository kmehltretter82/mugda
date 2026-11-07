#!/usr/bin/env bash
# Golden-output regression suite for Mugda.
#
# Runs the Lean 4 checker on every `.ma` file under examples/ and compares its
# complete observable behaviour (stdout, stderr, exit code) against the
# committed snapshot in tests/expected/<path>.out.
#
#   tests/golden.sh            check all examples (fails on any difference)
#   tests/golden.sh --update   regenerate snapshots (review the git diff!)
#
# Additionally, any file whose header contains a line
#   -- Expect: accept          must exit 0
#   -- Expect: reject (...)    must exit non-zero
# is checked against that declaration, so a blind `--update` cannot silently
# turn an intended rejection into an acceptance (or vice versa).
#
# Files under any `src/` directory are fragments of a larger program (they are
# concatenated by `make showcase`) and are skipped.

set -u
cd "$(dirname "$0")/.."

MUGDA=${MUGDA:-.lake/build/bin/mugda}
EXPECTED_DIR=tests/expected
UPDATE=0
[ "${1:-}" = "--update" ] && UPDATE=1

if [ ! -x "$MUGDA" ]; then
  echo "golden: $MUGDA not found; run 'lake build' first" >&2
  exit 2
fi

render() {
  # $1 = .ma file; prints the canonical snapshot to stdout
  local f=$1 out err rc
  err=$(mktemp)
  out=$("$MUGDA" "$f" 2>"$err")
  rc=$?
  printf '%s\n' "$out"
  printf -- '--- stderr ---\n'
  cat "$err"
  printf -- '--- exit: %d ---\n' "$rc"
  rm -f "$err"
}

pass=0; fail=0; updated=0; expect_errors=0
failed_files=()

while IFS= read -r f; do
  snap="$EXPECTED_DIR/$f.out"
  actual=$(render "$f")
  rc=$(printf '%s\n' "$actual" | tail -n 1 | sed -E 's/^--- exit: ([0-9]+) ---$/\1/')

  # 1. Header declaration check (independent of snapshots).
  expect=$(grep -m1 -E '^--[[:space:]]*Expect:' "$f" | sed -E 's/^--[[:space:]]*Expect:[[:space:]]*([a-z]+).*/\1/')
  if [ "$expect" = "accept" ] && [ "$rc" != "0" ]; then
    echo "EXPECT-FAIL  $f declares 'Expect: accept' but exited $rc"
    expect_errors=$((expect_errors + 1)); failed_files+=("$f")
  elif [ "$expect" = "reject" ] && [ "$rc" = "0" ]; then
    echo "EXPECT-FAIL  $f declares 'Expect: reject' but was accepted"
    expect_errors=$((expect_errors + 1)); failed_files+=("$f")
  fi

  # 2. Snapshot comparison.
  if [ "$UPDATE" = 1 ]; then
    mkdir -p "$(dirname "$snap")"
    if [ ! -f "$snap" ] || [ "$(cat "$snap")" != "$actual" ]; then
      printf '%s\n' "$actual" > "$snap"
      echo "updated      $snap"
      updated=$((updated + 1))
    fi
    pass=$((pass + 1))
  elif [ ! -f "$snap" ]; then
    echo "MISSING      $snap  (run: tests/golden.sh --update)"
    fail=$((fail + 1)); failed_files+=("$f")
  elif [ "$(cat "$snap")" != "$actual" ]; then
    echo "DIFF         $f"
    diff -u "$snap" <(printf '%s\n' "$actual") | sed 's/^/    /' | head -40
    fail=$((fail + 1)); failed_files+=("$f")
  else
    pass=$((pass + 1))
  fi
done < <(find examples -name '*.ma' -not -path '*/src/*' | LC_ALL=C sort)

# Stale snapshots (example deleted or renamed).
stale=0
while IFS= read -r s; do
  src=${s#"$EXPECTED_DIR/"}; src=${src%.out}
  if [ ! -f "$src" ]; then
    if [ "$UPDATE" = 1 ]; then rm -f "$s"; echo "removed      $s"
    else echo "STALE        $s (no such example: $src)"; stale=$((stale + 1)); fi
  fi
done < <(find "$EXPECTED_DIR" -name '*.ma.out' 2>/dev/null | LC_ALL=C sort)

echo "golden: $pass ok, $fail differing/missing, $stale stale, $expect_errors header violations"
[ "$UPDATE" = 1 ] && echo "golden: $updated snapshot(s) written"
[ $fail -eq 0 ] && [ $stale -eq 0 ] && [ $expect_errors -eq 0 ]
