---
qid: scm_shapley_sharedcoupling_bounds
spec: v1
topic: "Sharp shared-SCM bounds for trajectory-conditioned Shapley credit. In a finite-horizon finite-state/action Markov SCM with known bounded rewards, a positive-probability factual trajectory, factual and baseline policies, independent disturbances across time, and arbitrary within-time coupling of potential next states across action rows subject to observed transition marginals, characterize the attained sharp interval of each Li–Lee–Bareinboim trajectory Shapley coordinate without counterfactual independence. Optimize one posterior transition-row coupling shared across all coalition worlds; compress the 2^H Shapley sum to a polynomial-size exact representation and prove an endpoint compiler exponential only in a formally valid constrained elimination width, returning compatible endpoint SCMs. Prove an open-family strict gap versus independently optimizing coalition counterfactuals. Add simultaneous multinomial confidence-fiber inversion, whole-set coverage, and endpoint consistency controlled by factual transition probabilities. Consumer: φ-PPO's Shapley reward/critic updates; do not claim a sharp bound for PTR's RMS priority. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived compact attained posterior-row programs, polynomial coalition evaluation, confidence-fiber projection, and endpoint sensitivity at most 4DHδ/κ. Exact enumeration gives a two-step open family with shared interval [−ε,ε/2] versus independent outer interval [−(1+ε)/2,1/2]; 1,536 rational quadrature comparisons and 300 projection-LP checks passed. Generic row gluing is already in Lally et al., so novelty is confined to shared sequential optimization and compression. UNRESOLVED BOTTLENECK: Prove the optimization-preserving mixed-elimination invariant and O(H²Nd^(w+1)) complexity while retaining one shared optimizing row assignment across every coalition and state realization. EARLY KILL TEST: Implement the rational compiler for H≤4 and binary states/actions, compare every endpoint and confidence fiber with exhaustive shared-row enumeration, and stop on any mismatch or if constrained widths show no sequential gain beyond generic marginal-MAP solving. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_shapley_sharedcoupling_bounds.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The D0.5 ceiling is 7.3, which caps the assignable tier at subfield (field needs 7.5), so acceptance is arithmetically impossible."
  - "Generic row gluing is already in Lally et al., so novelty is confined to shared sequential optimization and compression."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_local_positivity_modulus.json
  - discovery/solve_tex/solve_thm_local_positivity_modulus.tex
  - discovery/proof_archive/
  - reviews/
seeds_burned: []
proof_attempt_summary: |
  The final atomic D0 repair made factual and coalition policy coins jointly
  independent, synchronized mutual transition-row CI, narrowed the published
  comparison to transition components, restored ambient metadata, and repaired
  malformed TeX; fresh review accepted all 63 changes and replay passed. Ten
  reviewed proof bodies persist, but dependency invalidation leaves the compiler,
  confidence-fiber, sparse-width, active-chain, and two supporting results marked
  partial/to-prove. The topic is banked below the field floor because its assessed
  ceiling is 7.3 rather than the required 7.5, not because the repaired model is unsound.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 91193272
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# scm_shapley_sharedcoupling_bounds / v1 — Downgraded

**Topic.** Sharp shared-SCM bounds for trajectory-conditioned Shapley credit. In a finite-horizon finite-state/action Markov SCM with known bounded rewards, a positive-probability factual trajectory, factual and baseline policies, independent disturbances across time, and arbitrary within-time coupling of potential next states across action rows subject to observed transition marginals, characterize the attained sharp interval of each Li–Lee–Bareinboim trajectory Shapley coordinate without counterfactual independence. Optimize one posterior transition-row coupling shared across all coalition worlds; compress the 2^H Shapley sum to a polynomial-size exact representation and prove an endpoint compiler exponential only in a formally valid constrained elimination width, returning compatible endpoint SCMs. Prove an open-family strict gap versus independently optimizing coalition counterfactuals. Add simultaneous multinomial confidence-fiber inversion, whole-set coverage, and endpoint consistency controlled by factual transition probabilities. Consumer: φ-PPO's Shapley reward/critic updates; do not claim a sharp bound for PTR's RMS priority. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived compact attained posterior-row programs, polynomial coalition evaluation, confidence-fiber projection, and endpoint sensitivity at most 4DHδ/κ. Exact enumeration gives a two-step open family with shared interval [−ε,ε/2] versus independent outer interval [−(1+ε)/2,1/2]; 1,536 rational quadrature comparisons and 300 projection-LP checks passed. Generic row gluing is already in Lally et al., so novelty is confined to shared sequential optimization and compression. UNRESOLVED BOTTLENECK: Prove the optimization-preserving mixed-elimination invariant and O(H²Nd^(w+1)) complexity while retaining one shared optimizing row assignment across every coalition and state realization. EARLY KILL TEST: Implement the rational compiler for H≤4 and binary states/actions, compare every endpoint and confidence fiber with exhaustive shared-row enumeration, and stop on any mismatch or if constrained widths show no sequential gain beyond generic marginal-MAP solving. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_shapley_sharedcoupling_bounds.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Fresh full-packet review accepted the sound repaired shared-SCM construction, but the D0.5 score ceiling is 7.3, below the 7.5 field threshold.

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
