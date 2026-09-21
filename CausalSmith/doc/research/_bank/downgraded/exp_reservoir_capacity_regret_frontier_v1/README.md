---
qid: exp_reservoir_capacity_regret_frontier
spec: v1
topic: "Reservoir-capacity frontier for online paired randomized experiments. For even T and B>=1, observe iid covariates X on [0,1]^d with a density bounded above and below and bounded potential outcomes whose prognostic score g(x)=E[Y(1)+Y(0)|X=x] lies in a fixed beta-Holder ball, 0<beta<=1. A covariate-only nonanticipating policy must assign immediately, maintain at most B already-assigned unmatched units, form opposite-treatment pairs with independent fair orientations, and empty the reservoir at T. Define R_T(B)=T^{-1} inf_pi sup_P E[C_g(M_pi)-min_M C_g(M)], where C_g(M)=sum_(i,j in M)(g(X_i)-g(X_j))^2; by the exact conditional-IPW identity this is T times the expected variance excess over the full-information offline pairing oracle. Prove a matched all-policy capacity/deadline frontier, an implementable capped coarsening/forced-clearing policy, and the iff growth regime for offline first-order precision. Consumer: Kapelner-Krieger Biometrics 2023 and CRAN SeqExpMatch. PRESOLVE EVIDENCE REQUIRING VERIFICATION: With a=2beta/d and b=min(B,T/2), a weighted-suffix argument plus a bounded random Holder-function prior gives R_T(B)>=c[b^-a+T^-1 sum_{r=1}^b r^-a]. A legal grid-parity policy gives R_T(B)<=C inf_{m<=b}(m^-a+m/T), matching when b^(1+a)<=T and proving offline first-order attainment iff B_T diverges. Exact small-state dynamic programs and feasible-path checks survived; current general-arrivals matching work does not supply this hard-cap causal frontier. UNRESOLVED BOTTLENECK: Prove the endpoint-safe clearance bound for the fixed-branching coarsening-grid policy, uniformly over the density class, to obtain the matching upper bound in the deadline-dominated regime. EARLY KILL TEST: Stress-test emergency-clearing start sizes and geometric costs at d=1,beta=1/2 and d=2,beta=1; stop this policy spine if clearance probability/cost exceeds the critical logarithmic order. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_reservoir_capacity_regret_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "The result is nevertheless restricted to additive expected conditional design-variance regret under a uniform covariate-to-score modulus; it does not establish relative efficiency, feasible inference, or an upper guarantee over Bai's broader class."
  - "The hard-cap and forced-empty model is specialized, and the package contains no implementation study or quantitative comparison showing how much the frontier changes trial design in realistic regimes."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_all_policy_lower_frontier.tex
  - discovery/solve_thm_minimax_frontier.tex
  - discovery/solve_prop_frontier_regimes.tex
  - orchestrator/decision_log.jsonl
seeds_burned:
  - index: 0
    one_liner: "seed-capacity-deadline-frontier"
    reason: "The original field-tier angle was mathematically completed and maximized, but its additive conditional-variance scope has a genuine subfield ceiling."
proof_attempt_summary: |
  D0 proved the advertised two-sided minimax capacity--deadline frontier, including the
  all-policy lower bound, an endpoint-safe fixed-branching coarsening construction, the
  alpha-dependent elbows, and the qualified memory iff. Both correctness reviews passed
  without findings; only the field-tier novelty claim collapsed. Reaching field tier would
  require a separate inference, broader-class, relative-efficiency, or empirical program.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 16925154
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 16925154
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# exp_reservoir_capacity_regret_frontier / v1 — Downgraded

**Topic.** Reservoir-capacity frontier for online paired randomized experiments. For even T and B>=1, observe iid covariates X on [0,1]^d with a density bounded above and below and bounded potential outcomes whose prognostic score g(x)=E[Y(1)+Y(0)|X=x] lies in a fixed beta-Holder ball, 0<beta<=1. A covariate-only nonanticipating policy must assign immediately, maintain at most B already-assigned unmatched units, form opposite-treatment pairs with independent fair orientations, and empty the reservoir at T. Define R_T(B)=T^{-1} inf_pi sup_P E[C_g(M_pi)-min_M C_g(M)], where C_g(M)=sum_(i,j in M)(g(X_i)-g(X_j))^2; by the exact conditional-IPW identity this is T times the expected variance excess over the full-information offline pairing oracle. Prove a matched all-policy capacity/deadline frontier, an implementable capped coarsening/forced-clearing policy, and the iff growth regime for offline first-order precision. Consumer: Kapelner-Krieger Biometrics 2023 and CRAN SeqExpMatch. PRESOLVE EVIDENCE REQUIRING VERIFICATION: With a=2beta/d and b=min(B,T/2), a weighted-suffix argument plus a bounded random Holder-function prior gives R_T(B)>=c[b^-a+T^-1 sum_{r=1}^b r^-a]. A legal grid-parity policy gives R_T(B)<=C inf_{m<=b}(m^-a+m/T), matching when b^(1+a)<=T and proving offline first-order attainment iff B_T diverges. Exact small-state dynamic programs and feasible-path checks survived; current general-arrivals matching work does not supply this hard-cap causal frontier. UNRESOLVED BOTTLENECK: Prove the endpoint-safe clearance bound for the fixed-branching coarsening-grid policy, uniformly over the density class, to obtain the matching upper bound in the deadline-dominated regime. EARLY KILL TEST: Stress-test emergency-clearing start sizes and geometric costs at d=1,beta=1/2 and d=2,beta=1; stop this policy spine if clearance probability/cost exceeds the critical logarithmic order. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_reservoir_capacity_regret_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G achieved subfield with projected paper-score ceiling 7.3 below the field gate 7.4; not salvageable within scope.

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
