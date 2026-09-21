---
qid: eid_blind_replicate_adrf_honest_supband
spec: blind_cfzero_adrf_band
topic: "Blind replicated continuous-treatment ADRF over a fixed quantitative class. Observe finite-stratum X, bounded Y, and S_r=A+U_r; the centered independent nonidentical asymmetric errors have a uniform q>=8 moment radius and fixed near-origin characteristic-function lower modulus but may have open spectral zeros. Compact A support supplies the analytic source radius; latent densities f_x and outcome-weighted measures q_x have fixed H^beta radii with beta>3/2 and f_x is bounded below near the target interval. Prove analytic-cocycle identification of f_x, q_x, and mu(a)=sum_x P(X=x)q_x(a)/f_x(a), then construct a uniformly honest simultaneous band with width r_n=(log log n/log n)^(beta-1/2) and prove a matching all-honest-band expected-width converse. Use empirical-CF confidence-set inversion and constrained analytic sieves. Consumer: Melaku-Shi 2026 NHANES two-recall diet-mortality mvGPS. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact identities give F_x(s,t)=fhat_x(s+t)phi_1(s)phi_2(t) and G_x(s,t)=qhat_x(s+t)phi_1(s)phi_2(t); their ratios and cocycle recover the centered latent and outcome-weighted transforms near zero, with analyticity extending globally. At the EJS cutoff T_n of order log n/log log n, Fourier Cauchy-Schwarz yields the candidate sup-norm scale T_n^(1/2-beta), transferred through f_x>=kappa. The sinc^12 asymmetric witness, denominator, contamination, signed-measure, and prior-art checks all survived independently. UNRESOLVED BOTTLENECK: Establish the matching outcome-channel modulus by constructing contiguous Bernoulli-outcome alternatives with fixed positive f and compact-spectrum errors whose dose-response curves differ by cT_n^(1/2-beta), and match it with a uniformly honest band of width CT_n^(1/2-beta). EARLY KILL TEST: In one X cell with known smooth positive f, fixed sinc^12 errors, and Bernoulli mean 1/2+g(a), compute the singular-value modulus over an H^beta ball at degree log n/log log n; pivot if the H^beta-to-L-infinity separation differs from m^(1/2-beta) or outcomes permit a faster honest-band rate."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "The field-tier kernel remained sound with clear novelty axes, but proposal review never accepted its assumption sourcing and tagging."
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The cited CapitaoMiniconiGassiatLehericy2025 identification theorem assumes coordinate independence, not the proposal's uniform local characteristic-function lower modulus; the quantitative class restriction must be retagged novel with applicability justification or supported by another citation."
  - "HuangZhang2023 supports consistency, unconfoundedness, positivity, and observed-response moment regularity, but not the proposal's almost-sure uniform bound on every potential outcome; the restriction needs a supporting source or transparent retagging and justification."
  - "Angle 0 v9 exhausted the expressly authorized revision cap; the operator directed banking if any flag remained."
reusable_artifacts:
  - "discovery/proto_core.json — the final field-tier proposal kernel, including analytic-cocycle identification, the stratum-homogeneous hard family, and the matched honest-band target."
  - "reviews/angle0_v9.json — the final reviewer receipt, with clear novelty axes and the remaining potential-outcome-range attribution defect."
  - "orchestrator/decision_log.jsonl — the complete nine-version repair history and validity-gate terminal classification."
seeds_burned:
  - index: 0
    one_liner: "seed:joint-id-sharp-band"
    reason: "Angle 0 exhausted nine revisions and the operator-directed final repair still returned an assumption-attribution flag."
proof_attempt_summary: |
  Nine proposal revisions repaired empirical-definition conventions, nuisance uncertainty, Sobolev representatives, pointwise causal identification, comparator coverage, and the finite-stratum hard family. The final review still assessed the kernel at field tier with no novelty or structure flags, but found that Huang--Zhang did not support the claimed uniform bound on all potential outcomes. The validity gate classified this as sound-but-unaccepted rather than refuted; nevertheless, the operator's final-repair cap required D-0.5 NO-PASS banking before D0.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 48169140
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 48169140
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# eid_blind_replicate_adrf_honest_supband / blind_cfzero_adrf_band — Failed

**Topic.** Blind replicated continuous-treatment ADRF over a fixed quantitative class. Observe finite-stratum X, bounded Y, and S_r=A+U_r; the centered independent nonidentical asymmetric errors have a uniform q>=8 moment radius and fixed near-origin characteristic-function lower modulus but may have open spectral zeros. Compact A support supplies the analytic source radius; latent densities f_x and outcome-weighted measures q_x have fixed H^beta radii with beta>3/2 and f_x is bounded below near the target interval. Prove analytic-cocycle identification of f_x, q_x, and mu(a)=sum_x P(X=x)q_x(a)/f_x(a), then construct a uniformly honest simultaneous band with width r_n=(log log n/log n)^(beta-1/2) and prove a matching all-honest-band expected-width converse. Use empirical-CF confidence-set inversion and constrained analytic sieves. Consumer: Melaku-Shi 2026 NHANES two-recall diet-mortality mvGPS. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact identities give F_x(s,t)=fhat_x(s+t)phi_1(s)phi_2(t) and G_x(s,t)=qhat_x(s+t)phi_1(s)phi_2(t); their ratios and cocycle recover the centered latent and outcome-weighted transforms near zero, with analyticity extending globally. At the EJS cutoff T_n of order log n/log log n, Fourier Cauchy-Schwarz yields the candidate sup-norm scale T_n^(1/2-beta), transferred through f_x>=kappa. The sinc^12 asymmetric witness, denominator, contamination, signed-measure, and prior-art checks all survived independently. UNRESOLVED BOTTLENECK: Establish the matching outcome-channel modulus by constructing contiguous Bernoulli-outcome alternatives with fixed positive f and compact-spectrum errors whose dose-response curves differ by cT_n^(1/2-beta), and match it with a uniformly honest band of width CT_n^(1/2-beta). EARLY KILL TEST: In one X cell with known smooth positive f, fixed sinc^12 errors, and Bernoulli mean 1/2+g(a), compute the singular-value modulus over an H^beta ball at degree log n/log log n; pivot if the H^beta-to-L-infinity separation differs from m^(1/2-beta) or outcomes permit a faster honest-band rate.

**Novelty target.** field

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** D-0.5 NO-PASS after the operator-authorized final v9: HuangZhang2023 supports observed-response moment regularity, not the proposed almost-sure uniform bound on every potential outcome.

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
