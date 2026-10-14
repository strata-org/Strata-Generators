/* Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
   Released under the Apache-2.0 or MIT license (see LICENSE-APACHE / LICENSE-MIT).

   Coverage meter for the `strata-cov` build (BUILD_MODE=cov in build.sh).

   The code-under-test modules are compiled with `-fsanitize-coverage=trace-pc-guard`, which makes the
   compiler emit a call to `__sanitizer_cov_trace_pc_guard` at every edge and one
   `__sanitizer_cov_trace_pc_guard_init` per section. We provide those callbacks ourselves (instead of
   libFuzzer) and simply count the number of *distinct* edges hit over the life of the process, printing
   it at exit. Running an `io`/`plausible` campaign or a `replay-dir` over a libFuzzer corpus in one
   process therefore yields "distinct code-under-test edges reached" on one metric, comparable across
   all three backends — with no external llvm-cov/llvm-profdata (none are installed for leanc's clang). */

#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint8_t *g_seen = NULL;   /* per-edge hit flag, indexed by the guard id we assign */
static size_t   g_total = 0;     /* number of instrumented edges */
static size_t   g_covered = 0;   /* number distinct edges hit so far */

/* Called once per merged guard section. `start`/`stop` bound the guard table; we number the guards
   1..N (0 stays "unassigned") and allocate the seen-table. The `if (*start)` check makes re-entry a
   no-op, matching the canonical SanitizerCoverage example. */
void __sanitizer_cov_trace_pc_guard_init(uint32_t *start, uint32_t *stop) {
  if (start == stop || *start) return;
  size_t n = (size_t)(stop - start);
  uint32_t id = 1;
  for (uint32_t *p = start; p < stop; ++p) *p = id++;
  g_total = n;
  g_seen = (uint8_t *)calloc(n + 1, 1);
}

/* Called at every edge. First hit of an edge bumps the distinct-edge count. */
void __sanitizer_cov_trace_pc_guard(uint32_t *guard) {
  uint32_t id = *guard;
  if (!id || !g_seen) return;
  if (!g_seen[id]) { g_seen[id] = 1; g_covered++; }
}

static void basalt_cov_report(void) {
  fprintf(stderr, "COVERAGE edges_covered=%zu edges_total=%zu\n", g_covered, g_total);
  fflush(stderr);
}
__attribute__((constructor)) static void basalt_cov_register(void) { atexit(basalt_cov_report); }

/* The Lean closure references `basalt_fuzz_go` (the `--backend=fuzz` path). This build does not link
   libFuzzer, so we stub it: it must never run here (use `replay-dir` to measure the fuzzer's corpus).
   Signature mirrors basalt/Basalt/Fuzz/native.c. */
LEAN_EXPORT lean_object *basalt_fuzz_go(lean_object *run, lean_object *argv, lean_object *w) {
  (void)w;
  lean_dec(run);
  lean_dec(argv);
  fprintf(stderr, "strata-cov: '--backend=fuzz' is unavailable (no libFuzzer); use replay-dir\n");
  return lean_io_result_mk_ok(lean_box(0));
}
