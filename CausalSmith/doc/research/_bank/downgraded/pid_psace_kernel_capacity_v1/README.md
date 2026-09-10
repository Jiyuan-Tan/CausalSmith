---
qid: pid_psace_kernel_capacity
spec: v1
topic: "Primitive Shared-Center Rowwise-TV PSACE Frontier and Sign Radius across ACCT trials. For m≥4 randomized trials and q=4 states x,z=(S,Y), observe arm marginals μ_g^0 and ν_g and maintain the observable first-stage floor Δ_g^S≥κ>0. Define primitive stochastic center rows k_x and primitive trial rows k_gx for every state, interpreting k_gx as a conditional transition law only when μ_g^0(x)>0. Impose TV(k_gx,k_x)≤d for d∈[0,1] and exact marginal reproduction, with no latent entry floor. Prove compatibility iff Σ_g⟨h_g,ν_g⟩≤H_d^*(h) for every h, where H_d^* is the direct finite rowwise LP support; prove finite normalized facet sufficiency, polynomial-size LP separation, and rational feasible or Farkas certificates. Derive attained sharp PSACE intervals, the compatibility radius ρ*, and trialwise/all-trial sign-reversal radii with an attaining adversarial kernel, finite dual cut or rational infeasibility ray, including +∞. On the explicit nondegenerate m=4 observable neighborhood W_{ε_w}, prove {θ_1^WM}=Θ_1^pr(0)⊊Θ_1^pr(d)⊊Θ_1^ST for every 0<d≤10^-2, with Wu–Mao as the d=0 comparator. Prove simultaneous multinomial-region coverage by set inclusion, including ties, incompatibility, d∈{0,1}, and +∞. For rational numerical inputs, give finite exact CAD profiling of the bilinear projections; practical complexity, implementation, coverage-preserving rational outer approximation for generally irrational concentration radii, and the numerical ACCT reanalysis are not claimed."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "The finite set is defined to contain only facet-normal rays, but at d=0 (and other lower-dimensional images) compatibility also requires affine-hull equalities; treating each equality as two supporting half-spaces in the proof does not put their non-facet normals in R*, so its advertised finite facet test can accept nu outside P_{mu,d}."
  - "The supplied attested sentence only says that a problem with 'X regular' reduces to two LPs; it does not state the core claim's arbitrary-polyhedron/strict-denominator hypotheses or optimizer-recovery conclusion."
  - "Cold tier verdict: review_general tier=subfield, meets_floor=false, novelty_target=field, floor=field, paper_score_ceiling=7.2, salvageable=true."
  - "Tier-lifting characterization is not bounded: it requires new endpoint-reaching radius definitions, a replacement flagship theorem, and a new proof absent from durable state."
reusable_artifacts:
  - "discovery/core.json — primitive shared-center rowwise-TV model, sharp PSACE endpoint programs, positive-radius sandwich construction, sign-radius LP/dual setup, and exact CAD profiling claim."
  - "discovery/writeup.tex — full derivation, including the explicit m=4 observable neighborhood and rational witness."
  - "discovery/proof_archive/ — proof receipts retained across the D0 maximization and repair rounds."
  - "reviews/ and orchestrator/decision_log.jsonl — comparator audit, Wu–Mao positioning, source attestations, decisive tier review, and terminal validity receipts."
seeds_burned:
  - index: 0
    one_liner: "Interior shared-center cut theorem with constructive residual gluing"
    reason: "Angle 0 exhausted seven versions and the one authorized root-changing retry; the final cold review remained below field with non-PASS defects."
proof_attempt_summary: |
  Seven proposal versions replaced the original interior-floor formula with primitive stochastic kernels, positioned Wu–Mao as the d=0 baseline, and derived positive-radius PSACE, sign-radius, and CAD-profiling results. The final cold review judged the contribution subfield rather than field and found that the finite facet-normal test omits affine-hull equality normals; the Charnes–Cooper cited leaf was also broader than its attestation, although the needed compact endpoint case was proved directly. A future reuse should first repair those two local defects, then supply a genuinely new saturation-radius or similarly anchor-free flagship theorem before seeking field status.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 54065492
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-04"
---

# pid_psace_kernel_capacity / v1 — Downgraded

**Topic.** Primitive Shared-Center Rowwise-TV PSACE Frontier and Sign Radius across ACCT trials. For m≥4 randomized trials and q=4 states x,z=(S,Y), observe arm marginals μ_g^0 and ν_g and maintain the observable first-stage floor Δ_g^S≥κ>0. Define primitive stochastic center rows k_x and primitive trial rows k_gx for every state, interpreting k_gx as a conditional transition law only when μ_g^0(x)>0. Impose TV(k_gx,k_x)≤d for d∈[0,1] and exact marginal reproduction, with no latent entry floor. Prove compatibility iff Σ_g⟨h_g,ν_g⟩≤H_d^*(h) for every h, where H_d^* is the direct finite rowwise LP support; prove finite normalized facet sufficiency, polynomial-size LP separation, and rational feasible or Farkas certificates. Derive attained sharp PSACE intervals, the compatibility radius ρ*, and trialwise/all-trial sign-reversal radii with an attaining adversarial kernel, finite dual cut or rational infeasibility ray, including +∞. On the explicit nondegenerate m=4 observable neighborhood W_{ε_w}, prove {θ_1^WM}=Θ_1^pr(0)⊊Θ_1^pr(d)⊊Θ_1^ST for every 0<d≤10^-2, with Wu–Mao as the d=0 comparator. Prove simultaneous multinomial-region coverage by set inclusion, including ties, incompatibility, d∈{0,1}, and +∞. For rational numerical inputs, give finite exact CAD profiling of the bilinear projections; practical complexity, implementation, coverage-preserving rational outer approximation for generally irrational concentration radii, and the numerical ACCT reanalysis are not claimed.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Cold D0.5 review: subfield tier, below the fixed field floor; sound positive-radius core, but the finite determining-ray clause and Charnes-Cooper cited leaf require local repair and the field lift requires new theorem architecture.

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

The positive-radius shared-kernel construction remains the reusable mathematical core. Do not reuse the finite `R*` facet-only sufficiency clause without adding both orientations of a basis for the affine-hull equalities, and do not cite the broad Charnes–Cooper leaf in place of the run's direct compact, uniformly positive-denominator argument.
