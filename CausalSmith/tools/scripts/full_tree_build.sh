#!/usr/bin/env bash
# Build EVERY CausalSmith module, not just the root import graph.
#
# `lake -d CausalSmith build` verifies only what `CausalSmith.lean` transitively
# imports. Research-run modules (CausalSmith/<Area>/<RUN>_Research/**) are mostly
# not reachable from it, so a library-wide signature change can break them while
# the default build stays green — on 2026-08-04 fourteen such modules across six
# runs and the substrate were broken at a "green" HEAD. This sweep derives the
# target list from the filesystem so nothing can be silently out of scope.
#
# EXCLUSION: `**/tmp/**` is skipped. Research runs leave scratch probes under
# `CausalSmith/<Area>/<RUN>_Research/tmp/` (49 such files as of 2026-08-16, all
# untracked). They are throwaway elaboration experiments, not library modules,
# so building them turns a real regression signal into noise. This is the ONLY
# exclusion — everything else stays find-derived on purpose, because the whole
# point of this sweep is that nothing escapes scope by being forgotten.
#
# Usage: full_tree_build.sh  (from anywhere inside the workspace)
# Exit: 0 iff every module builds; failing targets are listed on stderr.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WS_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
cd "$WS_ROOT"

# Bound walks on the shared mount, but never silently omit a deeper module tree.
if [ -n "$(find CausalSmith/CausalSmith -mindepth 31 -maxdepth 31 -type d -print -quit)" ]; then
  echo "full_tree_build: directory depth exceeds the bounded sweep; raise the limit explicitly" >&2
  exit 1
fi

ALLMODS=$(cd CausalSmith && find CausalSmith -maxdepth 32 -name '*.lean' -not -path '*/tmp/*' \
  | sed 's/\.lean$//; s|/|.|g')
N=$(echo "$ALLMODS" | wc -l)
SKIPPED=$(cd CausalSmith && find CausalSmith -maxdepth 32 -name '*.lean' -path '*/tmp/*' | wc -l)
echo "full_tree_build: $N CausalSmith modules (find-derived, root graph + orphans)"
# Report what was dropped: a silent exclusion would read as "covered everything".
[ "$SKIPPED" -gt 0 ] && echo "full_tree_build: skipped $SKIPPED scratch module(s) under **/tmp/**"

# Bound parallelism by MEMORY, not cores. Some research runs carry certified interval-arithmetic
# modules that peak at several GB each; unbounded `lake` starts one job per core (and more), and
# under a Slurm cgroup cap that means SIGKILL -- a 2026-09-20 sweep lost 27 modules to exit 137
# because the 128G allocation, not the node's 755G, is the real budget. Override with LAKE_JOBS.
# Lake 5 has no `-j`; its build jobs run on Lean's task pool, sized by LEAN_NUM_THREADS.
JOBS=${LAKE_JOBS:-8}
echo "full_tree_build: LEAN_NUM_THREADS=$JOBS (memory-bounded; export LAKE_JOBS to change)"
OUT=$(LEAN_NUM_THREADS="$JOBS" lake -d CausalSmith build $ALLMODS 2>&1)
STATUS=$?
if [ $STATUS -ne 0 ]; then
  # The gate redirects stderr to its per-step log.  Keep every Lake diagnostic
  # there: the old summary-only slice hid the first actionable type error.
  printf '%s\n' "$OUT" >&2
  echo "full_tree_build: FAILED (lake exit $STATUS; full diagnostics above)" >&2
  exit 1
fi
echo "full_tree_build: OK ($N modules green)"
