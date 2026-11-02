#!/usr/bin/env bash
# Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
# Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).
#
# Build the opt-in `strata-fuzz` executable: elaborate the Mathlib-free property/generator closure
# with Lake, SanitizerCoverage-instrument the first-party (generator + property) C, and link it
# against libFuzzer with Lean owning `main`. The Strata analogue of basalt's fuzz-run/build.sh; see
# fuzz-experiment/README.md and basalt's fuzz-run/README.md.
#
# Unlike basalt's tiny hand-listed closure, the Strata closure spans four packages
# (strata-generators, basalt, Strata, plausible), so this script DISCOVERS the exact module closure
# by BFS over the `initialize_<pkg>_<mod>(builtin)` calls each emitted .c makes. That naturally
# excludes runtime modules (libleanshared: Init/Std/Lean) and — crucially — the Mathlib-importing
# proof modules, which StrataFuzzMain never imports.
#
# Instrumentation scope: the strata-generators and basalt packages (generators + combinators +
# property). Strata (the language/AST + evaluator) and plausible (the --backend=plausible PRNG) are
# linked uninstrumented, matching DESIGN's "property + generators" coverage scope.
#
# NOT part of `lake build`. Usage:  fuzz-experiment/scripts/build.sh   then
#   ./fuzz-experiment/strata-fuzz <property> [--backend=fuzz|io|plausible] [-runs=N]
set -euo pipefail
cd "$(dirname "$0")/../.."
ROOT=$(pwd)
BASALT="$ROOT/.lake/packages/basalt"   # basalt dependency (git: hgoldstein95/basalt @ lean-4.29 — Basalt.PBT + Fuzz)

[ -f fuzz-experiment/scripts/env.sh ] && . fuzz-experiment/scripts/env.sh

# Two builds from the same closure:
#   BUILD_MODE=fuzz (default) — libFuzzer-driven `strata-fuzz`; instrument generators + code-under-test
#     with `-fsanitize=fuzzer-no-link`. This is the campaign binary.
#   BUILD_MODE=cov            — `strata-cov`; instrument ONLY the code-under-test (INSTR_MODULES) with
#     `-fsanitize-coverage=trace-pc-guard`, link the covmeter (no libFuzzer). Used by the coverage study
#     to count distinct code-under-test edges reached under io/plausible/replay-dir on one metric.
BUILD_MODE="${BUILD_MODE:-fuzz}"
if [ "$BUILD_MODE" = "cov" ]; then
  OUT="$ROOT/fuzz-experiment/obj-cov"; BIN="$ROOT/fuzz-experiment/strata-cov"
  INSTR_FLAG="-fsanitize-coverage=trace-pc-guard"
else
  OUT="$ROOT/fuzz-experiment/obj"; BIN="$ROOT/fuzz-experiment/strata-fuzz"
  INSTR_FLAG="-fsanitize=fuzzer-no-link"
fi
mkdir -p "$OUT"

# IR roots. Modules under an *instrumented* root get -fsanitize=fuzzer-no-link; others are plain.
ROOTS_INSTR=( "$ROOT/.lake/build/ir" "$BASALT/.lake/build/ir" )
ROOTS_PLAIN=(
  "$ROOT/.lake/packages/Strata/.lake/build/ir"
  "$ROOT/.lake/packages/StrataDDM/.lake/build/ir"
  "$ROOT/.lake/packages/plausible/.lake/build/ir"
  "$ROOT/.lake/packages/batteries/.lake/build/ir"
)

# ---------------------------------------------------------------------------------------------
# Platform detection (copied from basalt/fuzz-run/build.sh; same Amazon Linux 2023 environment).
# ---------------------------------------------------------------------------------------------
: "${CC:=leanc}"
TC=$(lean --print-prefix)
UNAME=$(uname -s)

if [ -z "${BRIDGE_INCLUDES+x}" ]; then
  if [ "$UNAME" = "Darwin" ]; then
    BRIDGE_INCLUDES="-isystem $(xcrun --show-sdk-path)/usr/include"
  else
    BRIDGE_INCLUDES="-isystem /usr/include"
    ma=$(gcc -print-multiarch 2>/dev/null || true)
    [ -n "$ma" ] && [ -d "/usr/include/$ma" ] && BRIDGE_INCLUDES="$BRIDGE_INCLUDES -isystem /usr/include/$ma"
  fi
fi
: "${BRIDGE_INCLUDES:=}"

# libFuzzer runtime: a version-matched toolchain archive, else basalt's from-source build, else a
# mismatched system archive with a warning. (On this box: instrumenting clang 19 vs system clang 22;
# the mismatched clang-22 archive is used and the chain-n canary confirms coverage still reaches it.)
if [ -z "${FUZZER_LIB_FLAGS+x}" ]; then
  arch=$(uname -m)
  instr_major=$(echo | $CC -dM -E - 2>/dev/null | sed -n 's/^#define __clang_major__ \([0-9][0-9]*\).*/\1/p')
  matched=""; any_host=""
  for d in ${FUZZER_LIB_SEARCH:-} \
           "$TC"/lib/clang/*/lib/linux "$TC"/lib/clang/*/lib/* \
           /usr/lib64/clang/*/lib/linux /usr/lib/clang/*/lib/linux \
           /usr/lib64/clang/*/lib/* /usr/lib/clang/*/lib/* \
           /usr/lib/llvm-*/lib/clang/*/lib/linux /usr/lib/llvm-*/lib/clang/*/lib/*; do
    [ -d "$d" ] || continue
    for a in "$d/libclang_rt.fuzzer_no_main.a" "$d/libclang_rt.fuzzer_no_main-$arch.a"; do
      [ -f "$a" ] || continue
      [ -n "$any_host" ] || any_host="$a"
      amaj=$(printf '%s' "$a" | sed -n 's#.*/clang/\([0-9][0-9]*\).*#\1#p')
      if [ -n "$instr_major" ] && [ "$amaj" = "$instr_major" ]; then matched="$a"; break 2; fi
    done
  done
  if [ -n "$matched" ]; then
    FUZZER_LIB_FLAGS="$matched"
  elif [ -f "$BASALT/fuzz-run/vendor/libFuzzerNoMain.a" ] || FUZZ_LLVM_MAJOR="$instr_major" "$BASALT/fuzz-run/get-libfuzzer.sh"; then
    FUZZER_LIB_FLAGS="$BASALT/fuzz-run/vendor/libFuzzerNoMain.a"
  elif [ -n "$any_host" ]; then
    echo "== WARNING: no libFuzzer runtime matches the instrumenting clang ${instr_major:-?} and none"
    echo "==          could be built from source; falling back to $any_host. If chain-n coverage is"
    echo "==          degraded, this skew is why (BasaltFuzz/DESIGN.md Appendix A). =="
    FUZZER_LIB_FLAGS="$any_host"
  else
    echo "no libFuzzer runtime found and none could be built" >&2; exit 1
  fi
fi

if [ -z "${CXXLIB_FLAGS+x}" ]; then
  if [ "$UNAME" = "Darwin" ]; then
    CXXLIB_FLAGS="-lc++"
  else
    newest_libstdcxx=$(ls /usr/lib/gcc/*/*/libstdc++.so 2>/dev/null | grep -v '/32/' | sort -V | tail -1)
    CXXLIB_FLAGS="${newest_libstdcxx:--lstdc++}"
  fi
fi

if [ -z "${DRIVER_DEFINE+x}" ]; then
  DRIVER_DEFINE=""
  probe=$(printf '%s\n' $FUZZER_LIB_FLAGS | grep -E '\.a$' | head -1 || true)
  if [ -n "$probe" ] && [ -f "$probe" ]; then
    hits=$(nm "$probe" 2>/dev/null | grep -c 'LLVMFuzzerRunDriver' || true)
    if [ "${hits:-0}" -eq 0 ]; then DRIVER_DEFINE="-DBASALT_FUZZ_LEGACY_DRIVER"; fi
  fi
fi

echo "== platform: $UNAME; cc: $CC; runtime: $FUZZER_LIB_FLAGS ${DRIVER_DEFINE:+(legacy driver)} =="

# ---------------------------------------------------------------------------------------------
echo "== elaborate + emit C via Lake =="
# Build the first-party closure explicitly so their .c (ir) are emitted (a lean_lib build does not
# emit .c for modules owned by another lib). For the expression fragment this is Core + PrimitiveGens.
lake build StrataFuzzMain StrataGenerators.HasTypeAGen.Core StrataGenerators.PrimitiveGens \
  ${EXTRA_LAKE_TARGETS:-} >/dev/null

echo "== scan IR roots =="
declare -A SYM2FILE SYM2INSTR
scan_root() {
  local root="$1" instr="$2" c sym
  [ -d "$root" ] || return 0
  while IFS= read -r c; do
    # The module's own init is the sole `LEAN_EXPORT lean_object* initialize_<self>(` definition;
    # earlier `initialize_X(uint8_t builtin);` lines are forward declarations of imports, not it.
    sym=$(grep -m1 "LEAN_EXPORT lean_object\* initialize_" "$c" | grep -o "initialize_[A-Za-z0-9_]*")
    [ -n "$sym" ] || continue
    SYM2FILE["$sym"]="$c"; SYM2INSTR["$sym"]="$instr"
  done < <(find "$root" -name '*.c')
}
for r in "${ROOTS_INSTR[@]}"; do scan_root "$r" 1; done
for r in "${ROOTS_PLAIN[@]}"; do scan_root "$r" 0; done

# Force-instrument the *code under test* — modules from an otherwise-plain package (Strata) whose
# behaviour the property exercises, so libFuzzer's coverage covers what is being tested and not just
# the generator. A POSIX-ERE matched against each module's init symbol; the default is Strata's
# expression evaluator + type checker (what expr-preservation / expr-progress test). Extend it as you
# add properties about a pass (e.g. add the ANF / monomorphization / PrecondElim modules). Override or
# clear via env.sh (`INSTR_MODULES=`).
: "${INSTR_MODULES:=_(LExprEval|LExprT|StatementType|LiftInternalFuncDecls|ProgramType)$}"
n_forced=0
if [ -n "$INSTR_MODULES" ]; then
  for sym in "${!SYM2INSTR[@]}"; do
    if [ "${SYM2INSTR[$sym]}" != "1" ] && printf '%s' "$sym" | grep -qE "$INSTR_MODULES"; then
      SYM2INSTR["$sym"]=1; n_forced=$((n_forced+1))
    fi
  done
fi
echo "== code-under-test instrumentation: INSTR_MODULES='$INSTR_MODULES' ($n_forced module(s) forced) =="

# In cov mode the metric is code-under-test coverage *only*, so drop the generator/property
# instrumentation the ROOTS_INSTR scan added — leave instrumented exactly the INSTR_MODULES-matched
# code-under-test modules forced just above.
if [ "$BUILD_MODE" = "cov" ]; then
  for sym in "${!SYM2INSTR[@]}"; do
    if printf '%s' "$sym" | grep -qE "$INSTR_MODULES"; then SYM2INSTR["$sym"]=1; else SYM2INSTR["$sym"]=0; fi
  done
fi

echo "== discover closure (BFS over initialize_* calls) + compile =="
declare -A VISITED
QUEUE=( "initialize_strata_x2dgenerators_StrataFuzzMain" )
OBJS=(); n_instr=0; n_plain=0
while [ ${#QUEUE[@]} -gt 0 ]; do
  sym="${QUEUE[0]}"; QUEUE=("${QUEUE[@]:1}")
  [ -n "${VISITED[$sym]:-}" ] && continue
  VISITED[$sym]=1
  file="${SYM2FILE[$sym]:-}"
  [ -z "$file" ] && continue                 # runtime module (libleanshared) — skip
  o="$OUT/${sym#initialize_}.o"
  if [ "${SYM2INSTR[$sym]}" = "1" ]; then
    $CC -O1 $INSTR_FLAG -c "$file" -o "$o"; n_instr=$((n_instr+1))
  else
    $CC -O1 -c "$file" -o "$o"; n_plain=$((n_plain+1))
  fi
  OBJS+=("$o")
  for dep in $(grep -o "res = initialize_[A-Za-z0-9_]*" "$file" | sed 's/res = //' | sort -u); do
    [ -n "${VISITED[$dep]:-}" ] || QUEUE+=("$dep")
  done
done
echo "== closure: $((n_instr+n_plain)) modules ($n_instr instrumented, $n_plain plain) =="

echo "== compile C bridge =="
if [ "$BUILD_MODE" = "cov" ]; then
  # No libFuzzer: the coverage meter provides the trace-pc-guard callbacks and stubs `basalt_fuzz_go`.
  $CC -O1 $BRIDGE_INCLUDES -c "$ROOT/fuzz-experiment/scripts/covmeter.c" -o "$OUT/covmeter.o"
  OBJS+=("$OUT/covmeter.o")
  LINK_RUNTIME=""
else
  $CC -O1 $BRIDGE_INCLUDES $DRIVER_DEFINE -c "$BASALT/Basalt/Fuzz/native.c" -o "$OUT/native.o"
  OBJS+=("$OUT/native.o")
  if [ "$UNAME" != "Darwin" ]; then
    $CC -O1 -c "$BASALT/fuzz-run/isoc23_compat.c" -o "$OUT/isoc23_compat.o"
    OBJS+=("$OUT/isoc23_compat.o")
  fi
  LINK_RUNTIME="$FUZZER_LIB_FLAGS"
fi

echo "== link =="
rm -f "$BIN"
if ! $CC "${OBJS[@]}" -o "$BIN" $LINK_RUNTIME $CXXLIB_FLAGS > "$OUT/link.log" 2>&1; then
  grep -viE 'unused|-Wl' "$OUT/link.log" >&2 || true
  echo "== link FAILED (runtime: $LINK_RUNTIME; cxxlib: $CXXLIB_FLAGS) ==" >&2
  exit 1
fi
grep -viE 'unused|-Wl' "$OUT/link.log" || true
[ -x "$BIN" ] || { echo "== link reported success but produced no binary ==" >&2; exit 1; }
echo "== built: $BIN =="
