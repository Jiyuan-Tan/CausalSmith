---
qid: eid_proximal_trialnetwork_nullity
spec: v1
topic: "Causal nullity and attainable-rank design in finite proximal treatment multigraphs. For binary outcomes, finite observed proxies, bounded finite latent support, eta-positive observed cells, and strictly positive full-data completions with common W-given-U kernels and shared treatment-node contrast bridges, prove target-population root contrasts are identified exactly when ker(A_P) is contained in ker(R_0). For every violating null direction, construct an explicit nonzero interval of positive full-data perturbations preserving all observed trial and target laws, proxy restrictions, and latent node contrasts while changing the target. In the rank-one trial submodel with common proxy kernel C of rank q, prove generic rank q(|V|-1) exactly when the treatment multigraph contains q edge-disjoint spanning trees; full W-bridge recovery also requires q=|W|. Give matroid-union certificates, separated-rank GLS/Wald inference, and finite-sample Bonferroni Clopper–Pearson cell-region projection covering every compatible contrast without rank selection. Consumer: the NETMOTION neonatal-oxygen IPD network, where added trials cannot overcome the proxy-rank ceiling. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Signed-cell causal lifts were derived and stress-tested on eight heterogeneous two-stratum/four-treatment rational models, preserving 5,120 observed cells and 2,304 latent-CATE equalities. Nonempty attainable-row sets have affine dimension q−1; 258 rectangular-kernel graph cases matched the q-tree rank formula. Rank-two/rank-three parallel-edge designs and exact binomial-tail inversion were checked, including 3,528 multinomial configurations. Boundaries involving q=1, redundant C rows, insufficient trees, zero Z-kernel entries, dependent outcomes, deficient rank, and denominator clearing were tested; no exact literature collision was found. UNRESOLVED BOTTLENECK: Independently prove the universal signed-cell lifting lemma for arbitrary finite supports, preserving every observed cell and shared latent node contrast simultaneously. EARLY KILL TEST: Reconstruct the supplied two-X/four-treatment rational model with dependent outcomes, a zero in a nonconstant Z kernel, and a nonreference left endpoint; apply both perturbation signs at half the explicit radius and verify every equality and positivity condition exactly. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_proximal_trialnetwork_nullity.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The exact nullity converse remains tangent-rich, attainable-rank design remains rank-one, and the promised nonconstant-Z early-kill witness was not reproduced."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The exact null-space identification equivalence is proved only for the deliberately tangent-rich active-carrier class: when a carrier is empty or its outcome-support tangent map is deficient, the global secant characterization remains open in oeq:support-face-frontier."
  - "The exact graphic-matroid-union rank and augmentation results are confined to the rank-one observed-proxy-row submodel; outside it, the paper proves only a proxy-rank ceiling rather than an attainable-rank characterization."
  - "The NETMOTION discussion is only a conditional consumer interpretation, with no instantiated network calculation demonstrating that the proxy ceiling or proposed augmentation changes conclusions in that application."
  - "The required zero-in-a-nonconstant-Z-kernel stress witness is not reproduced: this example gives every Z_e singleton support, so it cannot verify the lift on that required case."
reusable_artifacts:
  - "discovery/core.json — exact nullity criterion, active-carrier signed-cell lift, generic graphic-matroid-union rank, and q_max augmentation construction"
  - "discovery/solve_thm_exact_nullity.json — solver artifact for the causal nullity equivalence"
  - "discovery/solve_thm_proxy_rank_ceiling.json — solver artifact for the proxy-rank ceiling"
  - "discovery/solve_thm_exact_cell_projection.json — solver artifact for finite-sample rank-free projection"
  - "discovery/writeup.tex — integrated derivation and disclosed scope limitations"
seeds_burned: []
proof_attempt_summary: |
  Discovery proved a sound exact null-space identification criterion on a tangent-rich active-carrier class, an explicit signed-cell causal lift, exact generic graphic-matroid-union rank and q_max augmentation results in the rank-one row model, plus separated-rank and rank-free inference constructions. The package fell below the field floor because the necessity theorem remains restricted, general attainable rank outside the rank-one design is unresolved, and the motivating application was not instantiated; the promised nonconstant-Z stress witness was also not reproduced. An independent validity audit found no counterexample to the delivered theorems, so the result was banked at subfield rather than failed.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 27066159
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 27066159
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# eid_proximal_trialnetwork_nullity / v1 — Downgraded

**Topic.** Causal nullity and attainable-rank design in finite proximal treatment multigraphs. For binary outcomes, finite observed proxies, bounded finite latent support, eta-positive observed cells, and strictly positive full-data completions with common W-given-U kernels and shared treatment-node contrast bridges, prove target-population root contrasts are identified exactly when ker(A_P) is contained in ker(R_0). For every violating null direction, construct an explicit nonzero interval of positive full-data perturbations preserving all observed trial and target laws, proxy restrictions, and latent node contrasts while changing the target. In the rank-one trial submodel with common proxy kernel C of rank q, prove generic rank q(|V|-1) exactly when the treatment multigraph contains q edge-disjoint spanning trees; full W-bridge recovery also requires q=|W|. Give matroid-union certificates, separated-rank GLS/Wald inference, and finite-sample Bonferroni Clopper–Pearson cell-region projection covering every compatible contrast without rank selection. Consumer: the NETMOTION neonatal-oxygen IPD network, where added trials cannot overcome the proxy-rank ceiling. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Signed-cell causal lifts were derived and stress-tested on eight heterogeneous two-stratum/four-treatment rational models, preserving 5,120 observed cells and 2,304 latent-CATE equalities. Nonempty attainable-row sets have affine dimension q−1; 258 rectangular-kernel graph cases matched the q-tree rank formula. Rank-two/rank-three parallel-edge designs and exact binomial-tail inversion were checked, including 3,528 multinomial configurations. Boundaries involving q=1, redundant C rows, insufficient trees, zero Z-kernel entries, dependent outcomes, deficient rank, and denominator clearing were tested; no exact literature collision was found. UNRESOLVED BOTTLENECK: Independently prove the universal signed-cell lifting lemma for arbitrary finite supports, preserving every observed cell and shared latent node contrast simultaneously. EARLY KILL TEST: Reconstruct the supplied two-X/four-treatment rational model with dependent outcomes, a zero in a nonconstant Z kernel, and a nonreference left endpoint; apply both perturbation signs at half the explicit radius and verify every equality and positivity condition exactly. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_proximal_trialnetwork_nullity.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5 delivered subfield below the field floor: paper_score_ceiling 7.1 < 7.4 and salvageable=false; independent validity gate found the mathematics sound.

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
