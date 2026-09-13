---
qid: exp_spatial_dr_fpt_design
spec: v1
topic: "Exact fixed-parameter optimization of Zhu et al.'s second-order spatial cluster-design risk. For a finite connected graph G, fixed K>=2, closed one-hop exposure neighborhoods, and rational symmetric PSD entrywise-nonnegative pilot covariance Sigma with positive trace, minimize the exact p=1/2 oracle residual criterion V(C;Sigma)=N^-1 sum_{i,i'} 2^{m_ii'(C)+1} Sigma_ii' 1{m_ii'>0} over nonempty G-connected K-partitions. Define the interaction graph F by adding G's edges and clique-completing every scope N[i] union N[i'] with nonzero Sigma_ii'. Prove an exact general MILP and, given a width-w nice tree decomposition of F, a sound-complete DP with bag labels, processed-edge connectivity partitions, and completed-label flags; give a conservative explicit FPT runtime, reconstruct the optimum, and output a rational table/backpointer certificate. Verify the C4 surrogate reversal with exact risks 33.04 versus 38.72, and prove the ordered-entry l1 pilot perturbation and true-design regret bounds. Position against Zhu et al. arXiv:2505.20130 and use Holtz et al.'s Airbnb pricing meta-experiment as consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A processed component of an unfinished label must meet the current bag; forgetting its sole remaining block closes the label, which then cannot restart. At joins, active connectivity partitions merge by transitive closure and an absent label completed in both children is rejected. Label-refining partitions are bounded by Bell(w+1), so K^(w+1) Bell(w+1) 2^K safely bounds states. Every nonzero-covariance scope is a clique of F, hence occurs in a bag and can be charged once at its highest bag. The exact MILP, C4 values, perturbation constants, dense-covariance loss of practical width, and generic connected-partition DP prior art were checked without finding a collision. UNRESOLVED BOTTLENECK: Complete the node-by-node soundness and completeness induction, especially the join compatibility rule for absent completed labels and the matching backpointer reconstruction certificate. EARLY KILL TEST: On G=a-c-b, K=2, Sigma=diag(1,0,1), use a width-one nice decomposition joining the leaf branches at bag {c}. With a,b labeled 1 and c labeled 2, reject the state where both children close absent label 1, but accept the separator-active analogue; stop if the DP table does otherwise."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  - "ass:nice-node-forms does not require each introduce-edge node to contain both endpoints, so the transition can be undefined and the locality proof uses an unavailable premise."
  - "CandoganChenNiazadeh2023, Zhang2023GraphCut, and PougetAbadieEtAl2019 lack theorem-level closest-result contrasts."
  - "interaction-graph width may be linear even for simple geographic graphs, the MILP and perturbation bound are routine support, and the only delivered design consequence is C4."
  - "Covariance truncation yields only the existing l1 regret bound; covariance decay alone does not control interaction-graph treewidth. A width theorem needs new geometric/separator and quantitative tail assumptions, a materially new regime."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_lem_join_kill_test.json
  - discovery/solve_thm_exact_milp.json
  - discovery/solve_thm_c4_reversal.json
  - discovery/solve_thm_pilot_regret.json
  - reviews/stage_0.5.G_attempt1.json
seeds_burned: []
proof_attempt_summary: |
  The run derived an exact connected-partition MILP, a quotient-state tree-decomposition DP with rank compression and replayable backpointers, the C4 surrogate reversal, and an ordered-entry l1 pilot-regret bound. The field-tier claim collapsed because the covariance-scope interaction graph need not have practically controlled treewidth under the stated spatial assumptions; obtaining such control requires a materially new geometric and quantitative-decay regime. The banked note is not a verified theorem package: its nice-decomposition assumptions omit the introduce-edge endpoint condition, and three closest-result contrasts remain incomplete.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 17470366
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 17470366
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# exp_spatial_dr_fpt_design / v1 — Downgraded

**Topic.** Exact fixed-parameter optimization of Zhu et al.'s second-order spatial cluster-design risk. For a finite connected graph G, fixed K>=2, closed one-hop exposure neighborhoods, and rational symmetric PSD entrywise-nonnegative pilot covariance Sigma with positive trace, minimize the exact p=1/2 oracle residual criterion V(C;Sigma)=N^-1 sum_{i,i'} 2^{m_ii'(C)+1} Sigma_ii' 1{m_ii'>0} over nonempty G-connected K-partitions. Define the interaction graph F by adding G's edges and clique-completing every scope N[i] union N[i'] with nonzero Sigma_ii'. Prove an exact general MILP and, given a width-w nice tree decomposition of F, a sound-complete DP with bag labels, processed-edge connectivity partitions, and completed-label flags; give a conservative explicit FPT runtime, reconstruct the optimum, and output a rational table/backpointer certificate. Verify the C4 surrogate reversal with exact risks 33.04 versus 38.72, and prove the ordered-entry l1 pilot perturbation and true-design regret bounds. Position against Zhu et al. arXiv:2505.20130 and use Holtz et al.'s Airbnb pricing meta-experiment as consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A processed component of an unfinished label must meet the current bag; forgetting its sole remaining block closes the label, which then cannot restart. At joins, active connectivity partitions merge by transitive closure and an absent label completed in both children is rejected. Label-refining partitions are bounded by Bell(w+1), so K^(w+1) Bell(w+1) 2^K safely bounds states. Every nonzero-covariance scope is a clique of F, hence occurs in a bag and can be charged once at its highest bag. The exact MILP, C4 values, perturbation constants, dense-covariance loss of practical width, and generic connected-partition DP prior art were checked without finding a collision. UNRESOLVED BOTTLENECK: Complete the node-by-node soundness and completeness induction, especially the join compatibility rule for absent completed labels and the matching backpointer reconstruction certificate. EARLY KILL TEST: On G=a-c-b, K=2, Sigma=diag(1,0,1), use a width-one nice decomposition joining the leaf branches at bag {c}. With a,b labeled 1 and c labeled 2, reject the state where both children close absent label 1, but accept the separator-active analogue; stop if the DP table does otherwise.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G graded achieved tier incremental with paper_score_ceiling 5.8 < 7.2, below the field floor; no bounded in-scope repair lifts the tier, and the DP note retains an unrepaired introduce-edge endpoint premise.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
