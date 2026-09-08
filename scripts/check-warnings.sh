#!/usr/bin/env bash
# Fail if `lake build` emits any warning.
#
# Run this after lean-action has already built: Lake replays diagnostics from
# its cache, so this second build is close to free and still reports every
# warning in the library, not just the modules that happened to rebuild.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 1

log=$(mktemp)
trap 'rm -f "$log"' EXIT

lake build >"$log" 2>&1
build_status=$?

if [ "$build_status" -ne 0 ]; then
  echo "error: lake build failed" >&2
  grep -E '^error' "$log" >&2 | head -50
  exit "$build_status"
fi

count=$(grep -c '^warning:' "$log")

if [ "$count" -ne 0 ]; then
  echo "FAIL: lake build emitted $count warning(s)" >&2
  echo >&2
  grep -A3 '^warning:' "$log" >&2 | head -120
  cat >&2 <<'MSG'

The build is expected to be warning-free. Lean's linters print the exact
correction for most of these -- apply that rather than inventing a fix, and
note that removing one unused simp argument can expose the next, so re-run
until the count stops changing.

Please do not silence a warning with `set_option linter.… false`. If a fix
needs a judgement call that isn't yours to make -- a signature change, or
dropping a hypothesis that callers pass by name -- say so on the PR instead.
MSG
  exit 1
fi

echo "lake build: 0 warnings"
