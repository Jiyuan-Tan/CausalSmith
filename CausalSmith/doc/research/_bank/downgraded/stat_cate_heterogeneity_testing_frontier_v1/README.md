---
qid: stat_cate_heterogeneity_testing_frontier
spec: v1
topic: "The minimax bracket and exact no-penalty phase for testing treatment-effect heterogeneity with rough confounding. For fixed d>=1, alpha,beta,gamma>0, Holder radius L>=2, and overlap epsilon in (0,1/4), observe n iid O=(X,A,Y), with X uniform on [0,1]^d, A binary, Y in [0,1], propensity e in H^alpha(L) satisfying epsilon<=e<=1-epsilon, baseline mu0=E[Y|A=0,X] in H^beta(L), and CATE tau=mu1-mu0 in H^gamma(L). Consistency and conditional exchangeability identify tau; the experiment is the observed-data image of the corresponding full causal-law class. No interior arm-mean restriction, conditional-variance floor, or fitted-nuisance rate is assumed. Let V(P)=integral (tau-integral tau)^2 and rho_star(n) be the constant-CATE minimax separation radius at size 0.05 and type-II error 0.20 over this same observed-law class. Prove the full-class two-sided bracket c*r_or(n)<=rho_star(n)<=C*max(r_or(n),r_nu(n)), with explicit powers r_or=n^(-2gamma/(4gamma+d)) and r_nu=n^(-4gamma(alpha+beta)/(4gamma(alpha+beta)+d(alpha+beta)+2dgamma)). Prove the exact no-penalty phase rho_star(n) asymptotic to r_or(n) when alpha+beta>=2dgamma/(4gamma+d), including equality without logarithmic loss. Supply an explicitly computable, terminating, uniformly calibrated higher-order corrected-energy test attaining the upper endpoint, with deterministic tuning from the declared class constants and stated arithmetic complexity. Treat only the complementary rough regime alpha+beta<2dgamma/(4gamma+d) as open: whether r_nu is sharp, whether alpha and beta enter separately through further elbows, and whether logarithms occur there. Compare this continuous-design CATE-variance testing problem locally with the discrete arbitrary-cell-mass scalar-ATE bracket stat_discrete_ate_heterogeneity_frontier/v1 and with the additional learner/direction/variance conditions of Yu (2026) and Dhawan--Guo--Shah (2026), without claiming those procedures give a uniform full-class minimax converse."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The note proves the advertised full-class bracket and a matched oracle-rate result only in the no-penalty region; throughout the strict rough-confounding regime it supplies an upper rate but no nuisance-scale converse, so it does not establish the complete minimax frontier suggested by the title."
  - "The claim that the attaining test is explicitly computable is under-documented because the projectors, basis normalization, grid-rounding rules, and numerical constructions of C_B and C_0 are described generically rather than specified sufficiently for direct independent implementation."
  - "The missing rough-regime characterization, impractical worst-case arithmetic cost, and absence of computational evidence for the proposed calibration keep the projected paper below the matched-frontier calibration anchors."
reusable_artifacts:
  - "discovery/core.json — discharged graph for the full-class bracket, exact no-penalty region, and localized rough-regime OEQs"
  - "discovery/solve_thm_computable_upper_bound.json — explicit corrected-energy upper-bound construction and covariance analysis"
  - "discovery/solve_thm_observational_rate_bracket.json — oracle comparison and exact no-penalty phase proof"
  - "discovery/solve_oeq_nuisance_phase_characterization.json — failed-mixture obstruction and requirements for a legal rough-regime converse"
  - "discovery/writeup.tex — consolidated derivation and source-attested comparator account"
seeds_burned:
  - index: 0
    one_liner: "sharp-full-observational-frontier"
    reason: "Angle 0 was repaired through an honest bracket/no-penalty recast; the remaining strict rough-regime converse requires a new unvetted construction, and the attempted mixture failed legal transition-region and baseline-smoothness control."
proof_attempt_summary: |
  The run proved a same-class two-sided observational minimax bracket, constructed a total higher-order
  corrected-energy test for its upper endpoint, and matched the oracle rate throughout the no-penalty
  region, including the equality boundary without a logarithmic loss. The attempted correlated
  propensity–baseline lower-bound mixture did not control all observed transition regions and could
  transfer impermissible CATE roughness into the baseline when beta exceeds gamma. A field-level revival
  therefore needs a new legal composite-null mixture establishing the strict rough-regime converse,
  together with fully executable projector/calibration constants and computational evidence.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 38794107
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 38794107
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# stat_cate_heterogeneity_testing_frontier / v1 — Downgraded

**Topic.** The minimax bracket and exact no-penalty phase for testing treatment-effect heterogeneity with rough confounding. For fixed d>=1, alpha,beta,gamma>0, Holder radius L>=2, and overlap epsilon in (0,1/4), observe n iid O=(X,A,Y), with X uniform on [0,1]^d, A binary, Y in [0,1], propensity e in H^alpha(L) satisfying epsilon<=e<=1-epsilon, baseline mu0=E[Y|A=0,X] in H^beta(L), and CATE tau=mu1-mu0 in H^gamma(L). Consistency and conditional exchangeability identify tau; the experiment is the observed-data image of the corresponding full causal-law class. No interior arm-mean restriction, conditional-variance floor, or fitted-nuisance rate is assumed. Let V(P)=integral (tau-integral tau)^2 and rho_star(n) be the constant-CATE minimax separation radius at size 0.05 and type-II error 0.20 over this same observed-law class. Prove the full-class two-sided bracket c*r_or(n)<=rho_star(n)<=C*max(r_or(n),r_nu(n)), with explicit powers r_or=n^(-2gamma/(4gamma+d)) and r_nu=n^(-4gamma(alpha+beta)/(4gamma(alpha+beta)+d(alpha+beta)+2dgamma)). Prove the exact no-penalty phase rho_star(n) asymptotic to r_or(n) when alpha+beta>=2dgamma/(4gamma+d), including equality without logarithmic loss. Supply an explicitly computable, terminating, uniformly calibrated higher-order corrected-energy test attaining the upper endpoint, with deterministic tuning from the declared class constants and stated arithmetic complexity. Treat only the complementary rough regime alpha+beta<2dgamma/(4gamma+d) as open: whether r_nu is sharp, whether alpha and beta enter separately through further elbows, and whether logarithms occur there. Compare this continuous-design CATE-variance testing problem locally with the discrete arbitrary-cell-mass scalar-ATE bracket stat_discrete_ate_heterogeneity_frontier/v1 and with the additional learner/direction/variance conditions of Yu (2026) and Dhawan--Guo--Shah (2026), without claiming those procedures give a uniform full-class minimax converse.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Stage 0.5 (typed) BELOW NOVELTY FLOOR: D0.5.G tier=subfield < floor=field; paper_score_ceiling 6.6 < 7.2; not salvageable within scope.

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
