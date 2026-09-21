---
qid: pid_sharedassay_benefit_envelope
spec: v1
topic: "Shared-assay sharp probability-of-benefit envelope. In a blinded binary-outcome RCT, let one nondifferential assay channel with sensitivity s and specificity c be shared across arms, with (s,c) in a fixed rectangle and s+c-1>=kappa>0. Let the closed four-type potential-outcome law satisfy finite cross-product odds-band inequalities. Derive the unique compatible quadratic root and prove every sharp endpoint of P(Y(0)=0,Y(1)=1) is computed from at most ten explicit channel candidates (hence at most fourteen): feasible polygon vertices, stationary-line/edge contacts, and one possible kappa-edge point. Construct attaining laws; for the strictly positive finite-log-odds model prove equality of infimum/supremum and an exact endpoint-attainment criterion. With independent trial arm binomials and a blinded gold-standard assay-validation sample, invert exact primitive confidence sets and project the finite candidate map to cover the full sharp interval uniformly through contacts and tied optimizers, with excess width O(1/(kappa sqrt(Nmin))). Consumer: a prospective validation-enabled replication or reanalysis of the Polack et al. BNT162b2 endpoint workflow. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent algebra derived the compatible p11 root, marginal derivative bounds, factored stationary resultants, a conservative ten-candidate endpoint classification, strict-attainment criterion, explicit witness endpoints (sqrt(193)-5)/48 and 4/15, four-piece exact confidence projection, and uniform Clopper-Pearson/Hoeffding excess-width control. Two hundred twenty population optimizations agreed within 4.435e-11; one generic optimizer missed a legal boundary minimum that the explicit enumeration recovered, reinforcing the need for certified edge handling. No exact primary-source collision was found; assay transport remains an explicit prospective assumption. UNRESOLVED BOTTLENECK: Mechanize the finite-candidate completeness lemma across theta=1, marginal contacts, and strict-compatible representatives, then implement outward-rounded certified feasibility and projection arithmetic. EARLY KILL TEST: Reproduce the recorded kappa-edge confidence-projection instance whose legal vertex gives benefit about 0.1320580555; any implementation returning the failed generic optimizer's 0.1443566356 must stop and repair its edge enumeration. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_sharedassay_benefit_envelope.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "field framing outran a sound subfield sharp-identification and inference result"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The proved headline is a complete upper cap of ten candidate evaluations, not a minimal ten-point complexity result; the note correctly leaves minimality of M* open."
  - "The confidence theorem covers K*, the odds-band interval at the true transported assay channel, rather than the rectangle-robust population envelope [L,U], so references to covering the ‘full sharp interval’ must retain that distinction."
  - "The projected procedure has no outward-rounded certified implementation or substantive trial reanalysis, and the single numerical kill-test witness is insufficient reproducible evidence for the proposed clinical workflow."
reusable_artifacts:
  - path: discovery/core.json
    kind: other
    one_line: Complete theorem graph for the shared-channel sharp envelope, strict-model attainment criterion, and exact confidence projection.
  - path: discovery/writeup.tex
    kind: other
    one_line: Discharged derivation note with the finite candidate classification and contact-uniform inference argument.
  - path: discovery/solve_thm_exact_confidence_projection.tex
    kind: other
    one_line: Standalone exact primitive-set projection proof using attested Clopper–Pearson coverage.
seeds_burned: []
proof_attempt_summary: |
  The run proved the closed-model sharp envelope, constructive endpoint attainment, the strict-model
  endpoint criterion, a complete at-most-ten candidate evaluator, and exact projected coverage with
  a uniform width rate. The null-stratum channel formulation was repaired and every affected proof
  closure re-solved; both final technical referees passed. The field-tier framing nevertheless failed
  because minimum candidate complexity remains open and the inference/application layer is narrower
  and less operationally developed than promised, leaving a sound subfield result for re-anchoring.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 14467645
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 14467645
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# pid_sharedassay_benefit_envelope / v1 — Downgraded

**Topic.** Shared-assay sharp probability-of-benefit envelope. In a blinded binary-outcome RCT, let one nondifferential assay channel with sensitivity s and specificity c be shared across arms, with (s,c) in a fixed rectangle and s+c-1>=kappa>0. Let the closed four-type potential-outcome law satisfy finite cross-product odds-band inequalities. Derive the unique compatible quadratic root and prove every sharp endpoint of P(Y(0)=0,Y(1)=1) is computed from at most ten explicit channel candidates (hence at most fourteen): feasible polygon vertices, stationary-line/edge contacts, and one possible kappa-edge point. Construct attaining laws; for the strictly positive finite-log-odds model prove equality of infimum/supremum and an exact endpoint-attainment criterion. With independent trial arm binomials and a blinded gold-standard assay-validation sample, invert exact primitive confidence sets and project the finite candidate map to cover the full sharp interval uniformly through contacts and tied optimizers, with excess width O(1/(kappa sqrt(Nmin))). Consumer: a prospective validation-enabled replication or reanalysis of the Polack et al. BNT162b2 endpoint workflow. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent algebra derived the compatible p11 root, marginal derivative bounds, factored stationary resultants, a conservative ten-candidate endpoint classification, strict-attainment criterion, explicit witness endpoints (sqrt(193)-5)/48 and 4/15, four-piece exact confidence projection, and uniform Clopper-Pearson/Hoeffding excess-width control. Two hundred twenty population optimizations agreed within 4.435e-11; one generic optimizer missed a legal boundary minimum that the explicit enumeration recovered, reinforcing the need for certified edge handling. No exact primary-source collision was found; assay transport remains an explicit prospective assumption. UNRESOLVED BOTTLENECK: Mechanize the finite-candidate completeness lemma across theta=1, marginal contacts, and strict-compatible representatives, then implement outward-rounded certified feasibility and projection arithmetic. EARLY KILL TEST: Reproduce the recorded kappa-edge confidence-projection instance whose legal vertex gives benefit about 0.1320580555; any implementation returning the failed generic optimizer's 0.1443566356 must stop and repair its edge enumeration. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_sharedassay_benefit_envelope.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Stage 0.5 BELOW NOVELTY FLOOR: the complete ten-candidate upper cap is not a minimal complexity result, the exact confidence theorem covers the true-channel interval K* rather than the rectangle-wide envelope [L,U], and the projected workflow lacks certified implementation or substantive reanalysis; score 7.1 is below the 7.4 field floor.

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
