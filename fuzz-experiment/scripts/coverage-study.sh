#!/usr/bin/env bash
# Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
# Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
#
# Coverage head-to-head: for a property, measure how many DISTINCT code-under-test edges each backend
# reaches at an equal execution budget. One metric for all three backends (covmeter.c, trace-pc-guard):
#   fuzz      — run libFuzzer for `-runs=BUDGET` growing a corpus, then replay that corpus through
#               strata-cov (its corpus is the coverage frontier it discovered).
#   io        — strata-cov --backend=io       -runs=BUDGET
#   plausible — strata-cov --backend=plausible -runs=BUDGET
#
# Requires both binaries built first:
#     fuzz-experiment/scripts/build.sh              # strata-fuzz  (libFuzzer)
#     BUILD_MODE=cov fuzz-experiment/scripts/build.sh   # strata-cov  (coverage meter)
#
# Usage:  coverage-study.sh <property> [budget1 budget2 ...]      (default budgets: 20000 100000)
set -euo pipefail
cd "$(dirname "$0")/../.."
ROOT=$(pwd)
FE="$ROOT/fuzz-experiment"
FUZZ="$FE/strata-fuzz"; COV="$FE/strata-cov"
PROP="${1:?usage: coverage-study.sh <property> [budgets...]}"; shift || true
BUDGETS=( "${@:-}" ); [ -n "${BUDGETS[*]}" ] || BUDGETS=( 20000 100000 )
# libFuzzer byte-buffer cap. A deeper generator needs more bytes to express a term, so set MAXLEN
# larger for deep-regime properties (else the fuzzer is handicapped: it cannot form deep inputs).
MAXLEN="${MAXLEN:-64}"

[ -x "$FUZZ" ] || { echo "missing $FUZZ (run build.sh)" >&2; exit 1; }
[ -x "$COV" ]  || { echo "missing $COV (run BUILD_MODE=cov build.sh)" >&2; exit 1; }

# Run a backend, capturing its coverage even if it exits 77 (counterexample found) — a failing campaign
# still prints its COVERAGE line at exit, and that coverage-at-failure is a legitimate data point. A `!`
# after the value marks that a counterexample stopped the campaign early. `|| true` keeps set -e/pipefail
# from aborting the study on that 77.
run() {  # run <logfile> <cmd...>  -> echoes "<edges>[!]"
  local log="$1"; shift
  "$@" >"$log" 2>&1 || true
  local e; e=$(grep -oE 'edges_covered=[0-9]+' "$log" | head -1 | cut -d= -f2)
  if grep -q 'PROPERTY FAILED' "$log"; then echo "${e:-?}!"; else echo "${e:-?}"; fi
}

echo "# coverage study: property=$PROP  metric=distinct code-under-test edges  (trailing ! = counterexample stopped it early)"
printf '%-10s %12s %12s %12s\n' "budget" "fuzz" "io" "plausible"
for B in "${BUDGETS[@]}"; do
  CORP=$(mktemp -d "$FE/corpus.$PROP.$B.XXXX"); LOG=$(mktemp)
  # fuzz: grow a corpus for BUDGET executions (-max_len keeps the byte buffer in the same size regime as
  # the fixed-depth generator draws). A crash saves an artifact and stops early; the corpus so far stands.
  "$FUZZ" "$PROP" "$CORP" -runs="$B" -max_len="$MAXLEN" -artifact_prefix="$CORP/" >/dev/null 2>&1 || true
  fcov=$(run "$LOG" "$COV" replay-dir "$PROP" "$CORP")
  icov=$(run "$LOG" "$COV" "$PROP" --backend=io       -runs="$B")
  pcov=$(run "$LOG" "$COV" "$PROP" --backend=plausible -runs="$B")
  printf '%-10s %12s %12s %12s\n' "$B" "$fcov" "$icov" "$pcov"
  ncorp=$(find "$CORP" -type f | wc -l | tr -d ' ')
  echo "  (fuzz corpus: $ncorp inputs)"
  rm -rf "$CORP" "$LOG"
done
