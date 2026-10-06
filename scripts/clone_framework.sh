#!/usr/bin/env bash
# Clone only the framework: the Causalean library, the pipeline tools, the docs and one worked
# example paper, without the other papers' bundles and Lean. File contents are downloaded only
# for the folders checked out, so the clone is a fraction of a full one.
#
#   curl -fsSL https://raw.githubusercontent.com/Jiyuan-Tan/CausalSmith/main/scripts/clone_framework.sh | bash
#   scripts/clone_framework.sh [DIR]            # DIR defaults to CausalSmith
#
# Needs git 2.25 or newer. Runs on Linux, macOS and Windows (Git Bash).
#
# Later, inside the clone:
#   git sparse-checkout disable        # check out everything: every paper bundle and its Lean
set -euo pipefail
URL="${CAUSALSMITH_REPO_URL:-https://github.com/Jiyuan-Tan/CausalSmith.git}"
DIR="${1:-CausalSmith}"
EXAMPLE_BUNDLE="stat_discrete_ate_minimax_loggap_polynomial_upper_match"
EXAMPLE_LEAN="Stat/STAT_DiscreteAteMinimaxLoggap_Research"
# The run whose helper modules the example imports.
EXAMPLE_HELPER="Experimentation/EXP_RolloutChebyshevMinimax_Research/"
# The banked entry the tools' integration tests load, with its Lean.
FIXTURE_ENTRY="eid_crl_coverratio_mmd_genericity_v1"
FIXTURE_LEAN="ExactID/EID_CrlCoverratioMmdGenericity_Research"
[ ! -e "$DIR" ] || { echo "clone_framework: $DIR already exists" >&2; exit 1; }
# core.longpaths: harmless elsewhere, needed on Windows for the deeper paths.
git clone -c core.longpaths=true --filter=blob:none --sparse "$URL" "$DIR"
cd "$DIR"
# Non-cone patterns (gitignore syntax): everything, minus the paper bundles, the paper Lean
# (each run is a `<Run>_Research/` folder plus a `<Run>_Research.lean` module file) and the
# shelved-run summaries (so the site's Shelved runs page is empty in this checkout), plus the one
# example paper.
patterns=(
  '/*'
  '!/CausalSmith/doc/presentation/*/'
  '!/CausalSmith/doc/research/_bank/'
  '!/CausalSmith/CausalSmith/*/*_Research/' '!/CausalSmith/CausalSmith/*/*_Research.lean'
  "/CausalSmith/doc/presentation/$EXAMPLE_BUNDLE/"
  "/CausalSmith/CausalSmith/$EXAMPLE_LEAN/" "/CausalSmith/CausalSmith/$EXAMPLE_LEAN.lean"
  "/CausalSmith/CausalSmith/$EXAMPLE_HELPER"
  '/CausalSmith/doc/research/_bank/README.md'
  "/CausalSmith/doc/research/_bank/accepted/$FIXTURE_ENTRY/"
  "/CausalSmith/CausalSmith/$FIXTURE_LEAN/" "/CausalSmith/CausalSmith/$FIXTURE_LEAN.lean"
)
# git 2.35 and newer take --no-cone; older ones have pattern mode as their only `set` behaviour.
git sparse-checkout set --no-cone "${patterns[@]}" 2>/dev/null || git sparse-checkout set "${patterns[@]}"
echo "clone_framework: framework checked out in $DIR."
echo "  every paper bundle and its Lean:  git sparse-checkout disable"
