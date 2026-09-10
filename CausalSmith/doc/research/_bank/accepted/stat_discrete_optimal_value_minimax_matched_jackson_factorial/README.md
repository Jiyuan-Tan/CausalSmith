---
qid: stat_discrete_optimal_value_minimax_matched
spec: jackson_factorial
topic: "Matched minimax frontier for unrestricted optimal-policy value with a high-dimensional discrete confounder. Observe n iid draws of X in [d] and binary A,Y under consistency, conditional exchangeability, and fixed overlap eps. Target Vstar=sum_x p_x max(mu_0x,mu_1x), equivalently the degree-one homogeneous Lambda-plus-Gamma cell functional on the overlap cone. Prove for every n>=1,d>=2 that R_n,d,eps is comparable up to eps-only constants to min{1,d/[n log(ed)]}. Construct an explicit all-data estimator using a globally Lipschitz extension of the cell oracle functional, pilot-local tensor Jackson polynomials, centered factorial moments, clipping, and de-Poissonization; allow unknown unequal propensities, arbitrary cell masses, null cells, outcome-boundary means, and exact treatment-effect ties. Prove the matching all-measurable-estimator lower bound in every regime, plus uniform consistency iff d=o(n log(en)) and parametric MSE iff d=O(1). This upgrades the banked nonmatching lower-versus-d/n bracket and must independently verify the GPT-6 derivation rather than import it as theorem. Consumer: implementations of individualized optimal-treatment value estimation such as the tmle3mopttx workflow, where high-dimensional categorical adjustment and data-adaptive treatment maximization make the nonsmooth cell-value risk directly operational. PRESOLVE EVIDENCE REQUIRING VERIFICATION: GPT-6 derived the explicit extension g_a(u)=s(u)u_a1/max{s_a(u),eps s(u)}, agreeing with the oracle functional on the overlap cone and globally Lipschitz. A tensor Jackson convolution supplies, for the same pilot-local polynomial, vertex-adaptive pointwise error and an exponential centered-monomial coefficient envelope. Centered Poisson factorial identities, local clipping, integrated pilot tails, and Poisson coupling then give the d/[n log(ed)] upper contribution without cross-cell covariance; an exact Poisson moment-matching splice gives the matching dense converse. Null cells, overlap boundaries, unequal masses, exact ties, saturation, and superpolynomial n relative to d were stress-checked. UNRESOLVED BOTTLENECK: No hard lemma was left open, but D0 must independently verify the combined Jackson coefficient bookkeeping, local pilot scale, clipping variance, de-Poissonization, and all-regime lower splice. EARLY KILL TEST: Verify Sections 2-6 together; stop or pivot if one Jackson polynomial cannot satisfy both displayed approximation and coefficient bounds, or if pilot failures lose their local sqrt(p_x L/m)+L/m scale. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_discrete_optimal_value_minimax_gpt6.md."
novelty_target: field
banked_novelty_tier: field
supersedes:
  parent_qid: "stat_discrete_optimal_value_minimax_diagonal_adaptive_ratio"
  parent_spec: "tv"
  parent_tier: "downgraded"
  upgrade_axis: "estimation"
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: true
reraise_status: none
gap_reasons: []
reusable_artifacts:
  - `Causalean/Mathlib/Analysis/JacksonApproximation/{Kernel,Tensor,TensorExtraction,TrigExtraction,CoefficientEnvelopeFour,AffineFour}.lean`
  - `Causalean/Stat/FiniteRaoBlackwell/PairedPoissonHistogram.lean` and `Causalean/Stat/FiniteRaoBlackwell/PairedPoissonHistogram/{Basic,FixedRisk,PairingLaw,Risk}.lean`
  - `Causalean/Stat/Minimax/MomentMatchedMixture.lean` and `Causalean/Stat/Minimax/MomentMatchedMixture/{Analytic,ExponentialEnergy,Product,SupportLocalized}.lean`
  - `Causalean/Stat/Minimax/FuzzyHypotheses.lean`
  - capped-Poisson and Rao--Blackwell transport declarations in `Causalean/Stat/Minimax/MarkovKernelTransport.lean`
seeds_burned: []
proof_attempt_summary: |
  The run proved the matched upper and lower minimax rates, the causal reduction,
  and the consistency and parametric boundaries with no remaining proof holes or
  added assumptions. Reusable Jackson, Rao--Blackwell, and minimax-mixture
  infrastructure was validated and promoted into Causalean during F7.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 864993059
  pipeline_claude_tokens: 38346853
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# stat_discrete_optimal_value_minimax_matched / jackson_factorial — Accepted

**Topic.** Matched minimax frontier for unrestricted optimal-policy value with a high-dimensional discrete confounder. Observe n iid draws of X in [d] and binary A,Y under consistency, conditional exchangeability, and fixed overlap eps. Target Vstar=sum_x p_x max(mu_0x,mu_1x), equivalently the degree-one homogeneous Lambda-plus-Gamma cell functional on the overlap cone. Prove for every n>=1,d>=2 that R_n,d,eps is comparable up to eps-only constants to min{1,d/[n log(ed)]}. Construct an explicit all-data estimator using a globally Lipschitz extension of the cell oracle functional, pilot-local tensor Jackson polynomials, centered factorial moments, clipping, and de-Poissonization; allow unknown unequal propensities, arbitrary cell masses, null cells, outcome-boundary means, and exact treatment-effect ties. Prove the matching all-measurable-estimator lower bound in every regime, plus uniform consistency iff d=o(n log(en)) and parametric MSE iff d=O(1). This upgrades the banked nonmatching lower-versus-d/n bracket and must independently verify the GPT-6 derivation rather than import it as theorem. Consumer: implementations of individualized optimal-treatment value estimation such as the tmle3mopttx workflow, where high-dimensional categorical adjustment and data-adaptive treatment maximization make the nonsmooth cell-value risk directly operational. PRESOLVE EVIDENCE REQUIRING VERIFICATION: GPT-6 derived the explicit extension g_a(u)=s(u)u_a1/max{s_a(u),eps s(u)}, agreeing with the oracle functional on the overlap cone and globally Lipschitz. A tensor Jackson convolution supplies, for the same pilot-local polynomial, vertex-adaptive pointwise error and an exponential centered-monomial coefficient envelope. Centered Poisson factorial identities, local clipping, integrated pilot tails, and Poisson coupling then give the d/[n log(ed)] upper contribution without cross-cell covariance; an exact Poisson moment-matching splice gives the matching dense converse. Null cells, overlap boundaries, unequal masses, exact ties, saturation, and superpolynomial n relative to d were stress-checked. UNRESOLVED BOTTLENECK: No hard lemma was left open, but D0 must independently verify the combined Jackson coefficient bookkeeping, local pilot scale, clipping variance, de-Poissonization, and all-regime lower splice. EARLY KILL TEST: Verify Sections 2-6 together; stop or pivot if one Jackson polynomial cannot satisfy both displayed approximation and coefficient bounds, or if pilot failures lose their local sqrt(p_x L/m)+L/m scale. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_discrete_optimal_value_minimax_gpt6.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Accepted at CKPT 2: matched finite-sample minimax frontier formally verified with explicit Cai-Low and JHW cited premises, zero added assumptions, and dual-model F4 convergence.

**Supersedes.** stat_discrete_optimal_value_minimax_diagonal_adaptive_ratio_tv (tier=downgraded, upgrade_axis=estimation). The parent remains in _bank/downgraded/ as an independent reference; this entry is its `estimation`-axis upgrade, banked at field. An upgrade target may equal the parent's novelty tier — the delta is the declared axis, not a tier bump.

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
