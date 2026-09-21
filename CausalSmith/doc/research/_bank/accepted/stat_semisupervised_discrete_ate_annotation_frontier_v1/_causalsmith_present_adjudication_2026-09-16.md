# Presentation adjudication — 2026-09-16

## P2 residual proof audit

The frozen statements were checked before changing proof candidates. The statements for the seven
objects below accurately state their mapped Lean results; the residual findings concern proof
rendering, citation/exposition, or reader-visible derivation rather than theorem-body drift.

- `thm:sharp-annotation-frontier`: statement retained; regenerate the proof so the promoted strict-improvement lemma is incorporated as a citable step.
- `thm:known-marginal-limit`: statement retained; regenerate the proof to render the generic minimax identifications and sample-law identity directly.
- `lem:inverse-count-poisson-prefix-transfer`: statement retained; regenerate the proof to define the block sizes locally and expose the pushforward calculation.
- `lem:explicit-chebyshev-calibration`: statement retained; regenerate the proof to expose the falling-factorial moment identity and avoid ambiguous local arm notation. A citation-label-prefix complaint, if repeated, is a suspected false positive because assembly owns `obj:` normalization.
- `lem:common-marginal-recipe-transfer`: statement retained; regenerate the proof. The current issue targets a `% lean:` source comment rather than reader-visible text and is a suspected false positive if it repeats.
- `lem:finite-side-information-convergence`: statement retained; regenerate the proof from its frozen statement and promoted dependencies.
- `thm:common-marginal-converse`: statement retained; regenerate the proof so numerical transfer constants are derived or cited in reader-visible mathematics.

Per the presentation workflow, the bundle was snapshotted to
`internal/mill/scratch/mill-w06/stat_semisupervised_discrete_ate_annotation_frontier_v1_pre_p2_rerender_20260916`,
then only these seven proof candidates and their file-cache keys were cleared before re-entering P2.

## P2 promotion decision after regeneration

The regenerated audit left two proofs:

- `thm:common-marginal-converse` has a genuine `[missing-step]`: the substantive Lean helper
  `common_marginal_canonical_certificate_family` supplies a certificate package not stated by any
  current paper environment. This is a citable-step gap, so a further promotion round is granted.
- `lem:common-marginal-recipe-transfer` has reader-visible rendering defects in its newly generated
  proof, including an overstated pointwise witness identity, an under-justified concentration
  implication, and a factor-of-two error in the displayed fuzzy-testing arithmetic. Its statement
  remains correct. The proof candidate and only its file-cache key are cleared once more for the
  workflow-prescribed rendering retry.

## P2 promotion decision after round 4

Round 4 promoted and froze three environments, including
`lem:common-marginal-canonical-certificate-family`. Its proof audit then exposed one further
substantive citable step, `commonMarginal_rareCount_degree_lower`, as well as fresh notation and
branch-constant rendering errors. The regenerated `lem:common-marginal-recipe-transfer` likewise
exposed the substantive random-scale two-fuzzy minimax transfer theorem as an unstated citable step,
plus fresh loss-notation and conditioning-convention rendering defects. Both frozen statements remain
correct. A further promotion round is granted for those two exact helper results; the two affected
proof candidates and their file-cache keys are cleared, and the run re-enters from P1 as required
after a failed promoted retry.

## In-place proof adjudication after round 5

Round 5 closed the remaining citable-step gaps. The two residuals were local rendering issues, so
the proof sources were corrected in place while preserving all `% lean:` tags:

- `lem:common-marginal-recipe-transfer` now separates the two directions of the equality between
  ordinary minimax risk and class-gated fixed-sample decision risk, explicitly deriving the reverse
  direction from an arbitrary estimator and clipping.
- `lem:common-marginal-canonical-certificate-family` now displays the complete floor-limited
  rare-count inequality chain. It also writes the dual gap locally as `\delta_{\rm gap}` and uses the
  calibrated product identity `q_\epsilon\gamma_\epsilon b_0=\delta_{\rm gap}/2`, avoiding the
  auditor's mistaken reading of one calibration constant as two different quantities.

The content-keyed audit accepted the decision-risk correction and left only notation-rendering
findings in `lem:common-marginal-canonical-certificate-family`. The proof now introduces ordinary
paper notation `k_H,B_H,a_H,L_H`, the recipe's generator measure `\Gamma_H`, its raw targets
`r_{b,H}`, and its mixture laws `M_b(H)`; all reader-visible Lean field-projection syntax was removed.

## Isolated-lemma adjudication

- `lem:chebyshev-factorial-certificate` has concrete Lean consumers in the hybrid heavy/light-tail
  and quantitative-arithmetic helpers. Its missing paper citation was added to
  `lem:poisson-hybrid-risk` at the assembled factorial variance and bias step.
- `lem:annotation-frontier-strict-improvement` is consumed by the Lean proof of the sharp frontier
  theorem. Its missing paper citation was added at the strict-improvement rate equivalence.
- `lem:common-marginal-poisson-prior` has no Lean consumer: it is derived from the stronger
  `common_marginal_uniform_intensity`, while the converse proof uses that stronger result directly.
  It was removed as dead paper ballast from the outline, section, formal layer, proof cache, and
  proof sources; its bank graph node was retained but `nl.frozen` was cleared.

## Post-P1 proof adjudication

The required P1 rebuild refreshed several frozen statements and therefore re-keyed their proofs.
The resulting findings were adjudicated as follows:

- `lem:poisson-hybrid-risk` genuinely lacks citable paper environments for the substantive assembled
  variance bound, mean-bias bound, and deterministic envelope absorption. A promotion round is
  granted for those helper results, and this proof is cleared for regeneration against them.
- `lem:common-marginal-canonical-certificate-family` had only hardcoded internal step references;
  these were replaced by the mathematical source (the parametric two-point bound) and an explicit
  citation to `lem:common-marginal-recipe-transfer`.
- `lem:poisson-inverse-count-risk` now invokes the scalar energy lemma using descriptive arm-rate and
  marked-mass roles, without shadowing earlier symbols or exposing the `Real.toNNReal` clipping
  implementation detail.
- `thm:known-marginal-limit` now uses the correct squeeze: arbitrary exact-side rules give
  `R_star <= R_tilde`, conditional averaging gives `R_tilde <= R_m`, and convergence gives the
  reverse inequality. It no longer claims arbitrary exact-side rules admit Borel ambient extensions.

The promotion added and froze `lem:calibrated-envelope-absorption` and
`lem:finite-side-measurable-comparison`. The latter closed the known-marginal bridge. The hybrid-risk
proof still lacks one citable environment packaging the substantive assembled light/heavy/pilot-tail
variance and bias bounds; another targeted promotion is granted for that exact package. The proof is
cleared to regenerate with citations to both the new assembled-bound environment and
`lem:calibrated-envelope-absorption`.

That promotion produced and froze `lem:hybrid-light-branch-mean-bound` and
`lem:hybrid-heavy-branch-mean-bound`. Their audits exposed the next substantive citable layer: the
Poisson factorial-lift first-moment identity, the armwise inverse-count expectation identity (with
independence/factorization), and the pilot-tail mean-bias package. A further targeted promotion is
granted for those helpers, with only the light-bound, heavy-bound, and hybrid-risk proof candidates
cleared for regeneration.

That promotion added and froze `lem:poisson-inverse-arm-mean-formula` and
`lem:heavy-light-second-moment-sum`, leaving only local rendering repairs. The light-branch proof now
derives its factorial first moment explicitly from Poisson falling-factorial moments, names the
outcome intensity `u_{\rm out}`, and cites the new armwise expectation lemma instead of assigning a
conditional-binomial derivation to the aggregate Lean helper. The second-moment proof attributes the
`H_\epsilon` inequalities to the calibration predicate itself while citing the estimator definition
only for the scale identity. The corrupted DEL character before `\tau(P)` in the hybrid-risk proof
was removed.

The re-audit left two proofs with genuine citable gaps: the pilot-weighted heavy-branch variance
bound, the calibrated pilot-tail mean-bias estimates, and the factorial-growth/heavy-tail decay
inequality. A targeted promotion is granted for those three packages. The regenerated proofs must
also render the failed-calibration branch as the identity `MSE = \tau(P)^2` and state the
`\operatorname{Int.toNat}` truncation convention in `k_0`; only the hybrid-risk and heavy-light
second-moment proof candidates are cleared.

The re-audit left one local attribution mismatch in `lem:poisson-hybrid-risk`. It now explicitly
sets the all-heavy statistic to `Z^H=\sum_x\Omega_x`, uses independence to identify
`\operatorname{Var}(Z^H)=\sum_x v_{\Omega,x}`, and then uses `0\le\eta_x\le1` before applying the
aggregate variance bound from `lem:poisson-inverse-count-risk`.

The judge requires the proof to cite the exact helper consumed by Lean rather than the mathematically
stronger unweighted comparison. A targeted promotion is therefore granted for
`pilotHeavy_variance_bound_exists` and the substantive factorial-growth/exponential-tail cancellation.
The regenerated hybrid-risk proof must state its calibration quantities directly (avoiding the
spurious `obj:synth_7` reference complaint) and explicitly identify `\mu_{ax}` as the outcome
regression from `def:ate-functional`.

After those helpers were frozen, their own proofs exposed two remaining citable packages: the
rare-count degree lower bound used by the canonical certificate and the calibrated pilot-tail
mean-bias sublemmas. A targeted promotion is granted for those results. Independently,
`lem:common-marginal-recipe-transfer` now displays the raw-center separation
`\delta_\epsilon k a\le\Delta` before invoking the scale-tail lemma and removes hardcoded step-number
references.

## Proof-audit verdict appeal resolution

The supervisor granted the appeal for `lem:common-marginal-recipe-transfer`, cache key
`4a18c5a3e700f99bebab1c031dc4dbbd7b0a9026a55b552ac6ecb74c5ee1d876`, and authorized changing only
its cached verdict to `faithful`, leaving the content key untouched. The auditor's issue was:

> `[rendering] Step 5 miscomputes the displayed fuzzy-testing constant: from the preceding line one gets \(\Delta^2/32\,(1-1/8-1/16-1/16)=3\Delta^2/128\) only if the parenthesis equals \(3/4\), but it equals \(3/4\) and thus the product is \(3\Delta^2/128\) yes; no issue.`

This is self-cancelling: the parenthesis is exactly `3/4`, so the displayed product is correct. The
proof was not changed. The suspected prompt defect—emitting a self-cancelling issue as a blocking
finding—must be carried into the final `paper-done` report.

The two unrelated genuine rendering findings were repaired in place. The canonical-certificate
proof now includes the omitted `log(en) sqrt(n) <= 2n <= 2(n+m)` comparison, writes the subsequent
`d/2 <= d-1` step explicitly, and parenthesizes the variance multiplier unambiguously. The calibrated
hybrid mean-bias proof now cites `synth_7` for `L(n)` and assigns separate Lean provenance markers to
the mixture identity and the factorial-pool identity.
