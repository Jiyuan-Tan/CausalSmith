/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite-partition OLS weights with heterogeneous effects

Pure finite-cell algebra for saturated-OLS overlap weights. It proves:

* the saturated OLS estimand decomposes as `Σ ω_g τ_g`, with
  `ω_g ∝ π_g p_g (1−p_g)`;
* if every `p_g = 1/2`, the overlap weights collapse to cell probabilities;
* if `τ` is constant, the saturated OLS estimand is that constant.

An assumed two-component ATT/ATU representation is recorded separately as the
algebraic scaffold `AssumedTwoComponentOLS`. Its corollaries do not derive the
representation from an OLS projection.

This file is pure finite-cell algebra. The symbols `π`, `p`, and `τ` stand for
cell probabilities, treated shares, and cell-level effects in the finite
partition. Their probability-space interpretation — including
`τ_g = E[Y(1)−Y(0) ∣ G=g]` built from potential outcomes under the finite-cell
bridge condition — is supplied by `bridge_finite_residualized_eq_overlap` in
`OverlapWeightedATE.lean`, where `partitionOf` instantiates this structure from
a probability space. See `OverlapWeightedATE.lean` for that bridge.

The motivating NL artifact is:
`doc/basic_concepts/po/estimand_characterization/sloczynski_ols_heterogeneous.md`.
The algebra here does not derive the paper's treated-versus-untreated
representation; `AssumedTwoComponentOLS` stores that representation as input.
-/

module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Finite-Partition OLS Algebra

This file formalizes finite-cell saturated ordinary least squares weights with
heterogeneous treatment effects. It defines
`FinitePartition`, `cellOverlap`, `overlapWeight`, and
`overlapWeightedATE`, proves the normalized-weight identity
`finite_weights_eq_sum`, and records the equal-share and homogeneous-effect
collapses. It also defines `perTreatedWeight` and `perUntreatedWeight` for the
per-observation leverage interpretation, and `AssumedTwoComponentOLS` for a
separate ATT/ATU algebraic scaffold whose two-component identity and
equal-dispersion weight are supplied as fields. -/

@[expose] public section

namespace Causalean
namespace Panel.EstimandCharacterization
namespace OLSWeightDecomposition

open Finset

/-- A finite covariate partition for a saturated-OLS weight decomposition, carrying
[cell probabilities](hyp:π), [within-cell treated shares](hyp:p), and [within-cell conditional
treatment effects](hyp:τ), together with the side conditions used by the saturated-OLS algebra:
[the cell probabilities are nonnegative](hyp:π_nonneg) and [sum to one](hyp:π_sum_one), [the
treated shares lie in the unit interval](hyp:p_nonneg,p_le_one), and [the overlap denominator
`Σ π_g p_g (1−p_g)` is strictly positive](hyp:overlap_pos). -/
structure FinitePartition (𝒢 : Type*) [Fintype 𝒢] where
  /-- Cell probability `π_g = ℙ(G=g)`. -/
  π : 𝒢 → ℝ
  /-- Within-cell treated share `p_g = ℙ(D=1 ∣ G=g)`. -/
  p : 𝒢 → ℝ
  /-- Within-cell conditional treatment effect `τ_g = E[Y(1)−Y(0) ∣ G=g]`. -/
  τ : 𝒢 → ℝ
  /-- `π` takes nonnegative values. -/
  π_nonneg : ∀ g, 0 ≤ π g
  /-- `π` sums to 1. -/
  π_sum_one : ∑ g, π g = 1
  /-- Treatment shares are nonnegative. -/
  p_nonneg : ∀ g, 0 ≤ p g
  /-- Treatment shares are at most 1. -/
  p_le_one : ∀ g, p g ≤ 1
  /-- Saturated-overlap relevance: `Σ π_g p_g (1−p_g) > 0`. -/
  overlap_pos : 0 < ∑ g, π g * (p g * (1 - p g))

namespace FinitePartition

/-- For [a finite covariate partition](hyp:P) and [one of its cells](hyp:g),
the [within-cell treatment overlap](goal) is $p_g(1-p_g)$, where $p_g$ is
that cell's treated share. -/
def cellOverlap {𝒢 : Type*} [Fintype 𝒢] (P : FinitePartition 𝒢) (g : 𝒢) : ℝ :=
  P.p g * (1 - P.p g)

/-- For [a finite covariate partition](hyp:P), the
[overlap-weighted numerator](goal) is $\sum_g \pi_g p_g(1-p_g)\tau_g$,
the sum of each cell effect weighted by its probability and treatment overlap. -/
def overlapNumerator {𝒢 : Type*} [Fintype 𝒢] (P : FinitePartition 𝒢) : ℝ :=
  ∑ g, P.π g * P.cellOverlap g * P.τ g

/-- For [a finite covariate partition](hyp:P), the
[overlap-weighted denominator](goal) is $\sum_g \pi_g p_g(1-p_g)$,
the probability-weighted sum of within-cell treatment overlap. -/
def overlapDenominator {𝒢 : Type*} [Fintype 𝒢] (P : FinitePartition 𝒢) : ℝ :=
  ∑ g, P.π g * P.cellOverlap g

/-- For [a finite covariate partition](hyp:P) and [one of its cells](hyp:g),
the [normalized overlap weight](goal) is
$\pi_g p_g(1-p_g)/\sum_h\pi_h p_h(1-p_h)$. -/
noncomputable def overlapWeight {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) (g : 𝒢) : ℝ :=
  (P.π g * P.cellOverlap g) / P.overlapDenominator

/-- For [a finite covariate partition](hyp:P), the
[saturated ordinary-least-squares estimand](goal) is
$\sum_g\pi_g p_g(1-p_g)\tau_g / \sum_g\pi_g p_g(1-p_g)$. -/
noncomputable def overlapWeightedATE {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) : ℝ :=
  P.overlapNumerator / P.overlapDenominator

variable {𝒢 : Type*} [Fintype 𝒢] (P : FinitePartition 𝒢)

/-- The denominator is positive. Restated from `overlap_pos`. -/
theorem overlapDenominator_pos : 0 < P.overlapDenominator := by
  simpa [overlapDenominator, cellOverlap, mul_assoc] using P.overlap_pos

/-- The overlap weights sum to one. Direct from positivity of the
denominator and pulling the common denominator out of the sum. -/
theorem omega_sum_eq_one : ∑ g, P.overlapWeight g = 1 := by
  have hD : P.overlapDenominator ≠ 0 := P.overlapDenominator_pos.ne'
  have hsum : ∑ g, P.overlapWeight g = P.overlapDenominator / P.overlapDenominator := by
    simp [overlapWeight, overlapDenominator, Finset.sum_div]
  rw [hsum, div_self hD]

/-- **Finite-partition OLS weights** (`prop:po-estimand-sloczynski-ols-finite-weights`). [The
saturated-OLS estimand equals the sum of normalized overlap weights times cell effects,
`Σ_g ω_g τ_g`](goal). -/
theorem finite_weights_eq_sum :
    P.overlapWeightedATE = ∑ g, P.overlapWeight g * P.τ g := by
  simp only [overlapWeightedATE, overlapNumerator, overlapWeight, Finset.sum_div]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  ring

/-- Equal-cell-share weight collapse: if `p_g = 1/2` for every cell, the
normalized overlap weight reduces to the cell probability `π_g`. -/
theorem equal_groups_weight_eq_pi
    (h : ∀ g, P.p g = 1 / 2) (g : 𝒢) :
    P.overlapWeight g = P.π g := by
  have hcell : ∀ g', P.cellOverlap g' = (1 : ℝ) / 4 := by
    intro g'
    simp [cellOverlap, h g']
    ring
  have hden : P.overlapDenominator = (1 : ℝ) / 4 := by
    have hsum : ∑ g', P.π g' * P.cellOverlap g' = ∑ g', P.π g' * ((1 : ℝ)/4) := by
      refine Finset.sum_congr rfl (fun g' _ => ?_)
      rw [hcell g']
    rw [overlapDenominator, hsum, ← Finset.sum_mul, P.π_sum_one, one_mul]
  simp [overlapWeight, hcell, hden]

/-- **Equal-cell-share collapse to unweighted average** (finite half of
`prop:po-estimand-sloczynski-ols-equal-groups`). If [every cell has an equal
treated share `p_g = 1/2`](hyp:h), then [the saturated-OLS estimand `β_sat`
equals the probability-weighted average of the cell treatment effects
`Σ π_g τ_g`](goal). -/
theorem equal_groups_collapses
    (h : ∀ g, P.p g = 1 / 2) :
    P.overlapWeightedATE = ∑ g, P.π g * P.τ g := by
  rw [P.finite_weights_eq_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [P.equal_groups_weight_eq_pi h g]

/-- **Homogeneous-effect collapse.** If [the cell-level treatment
effect equals a common constant `τ₀` in every cell](hyp:h), then [the
saturated-OLS estimand `β_sat` equals `τ₀`](goal). -/
theorem homogeneous_collapses
    {τ₀ : ℝ} (h : ∀ g, P.τ g = τ₀) :
    P.overlapWeightedATE = τ₀ := by
  have hD : P.overlapDenominator ≠ 0 := P.overlapDenominator_pos.ne'
  have hnum : P.overlapNumerator = τ₀ * P.overlapDenominator := by
    simp only [overlapNumerator, overlapDenominator, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [h g]; ring
  rw [overlapWeightedATE, hnum, mul_div_assoc, div_self hD, mul_one]

/-- For [a finite covariate partition](hyp:P) and [one of its cells](hyp:g),
the [per-treated-observation leverage factor](goal) is $1-p_g$, the untreated
share in that cell.

In the finite-cell overlap formula, each treated observation in cell `g` has
the leverage factor `1 − p_g`, while each untreated observation has the
factor `p_g`. This definition makes the first factor explicit; see
`perTreatedWeight_antitone`, `perUntreatedWeight_monotone`, and
`cellOverlap_eq_perWeights_mul` for the main monotonicity claims. -/
noncomputable def perTreatedWeight {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) (g : 𝒢) : ℝ := 1 - P.p g

/-- For [a finite covariate partition](hyp:P) and [one of its cells](hyp:g),
the [per-untreated-observation leverage factor](goal) is $p_g$, the treated
share in that cell.

Each untreated observation in cell `g` contributes a leverage factor of
`p_g` (the treated share). Cells with more treated units (high `p_g`) give
each untreated unit a larger per-observation weight; cells with fewer
treated units (low `p_g`) give each untreated unit a smaller weight.
See `perUntreatedWeight_monotone`. -/
noncomputable def perUntreatedWeight {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) (g : 𝒢) : ℝ := P.p g

/-- The cell overlap variance is the product of the two per-observation
leverage factors: `p_g (1−p_g) = perUntreatedWeight_g · perTreatedWeight_g`.
This links the finite-cell denominator to its two per-observation factors. -/
theorem cellOverlap_eq_perWeights_mul {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) (g : 𝒢) :
    P.cellOverlap g = P.perUntreatedWeight g * P.perTreatedWeight g := by
  unfold cellOverlap perUntreatedWeight perTreatedWeight
  ring

/-- **Monotonicity of the per-treated factor.** The per-treated-observation
leverage factor `1 − p_g` is antitone in the treated share: if [cell `g` has a
treated share no larger than cell `h`'s](hyp:hph), then [`g`'s per-treated-observation
leverage factor is at least `h`'s:
`perTreatedWeight P h ≤ perTreatedWeight P g`](goal).

In words: the *minority* treatment-status group in a cell receives the
larger per-observation weight. A cell where almost everyone is treated
(`p_g ≈ 1`) downweights each treated observation to near 0; a cell where
almost no one is treated (`p_g ≈ 0`) upweights each treated observation
toward 1.

This is a property of the finite-cell overlap factors; it is not the paper's
ATT/ATU group-weight representation. -/
theorem perTreatedWeight_antitone {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) {g h : 𝒢}
    (hph : P.p g ≤ P.p h) :
    P.perTreatedWeight h ≤ P.perTreatedWeight g := by
  simp only [perTreatedWeight]
  linarith

/-- **Monotonicity of the per-untreated factor.** The
per-untreated-observation leverage factor `p_g` is monotone in the treated
share: if [cell `g` has a treated share no larger than cell `h`'s](hyp:hph),
then [`h`'s per-untreated-observation leverage factor is at least `g`'s:
`perUntreatedWeight P g ≤ perUntreatedWeight P h`](goal).

Symmetrically to `perTreatedWeight_antitone`: the minority
untreated group in a cell receives the larger per-observation weight. -/
theorem perUntreatedWeight_monotone {𝒢 : Type*} [Fintype 𝒢]
    (P : FinitePartition 𝒢) {g h : 𝒢}
    (hph : P.p g ≤ P.p h) :
    P.perUntreatedWeight g ≤ P.perUntreatedWeight h := by
  simp only [perUntreatedWeight]
  exact hph

end FinitePartition

/-- An algebraic scaffold in which [an OLS coefficient is supplied as a two-component
ATT/ATU combination](hyp:twoComponent), [the supplied weights sum to one](hyp:weights_sum_one),
and [the ATT weight is supplied as the untreated share](hyp:equalDispersion), with [a treated
share between zero and one](hyp:ρ_nonneg,ρ_le_one).

This structure does not construct an OLS projection or derive its two-component
representation. Its corollaries only substitute the supplied weight identities. -/
structure AssumedTwoComponentOLS where
  /-- Treated share `ρ = ℙ(D=1)`. -/
  ρ : ℝ
  /-- ATT, `τ_ATT = E[Y(1)−Y(0) | D=1]`. -/
  τ_ATT : ℝ
  /-- ATU, `τ_ATU = E[Y(1)−Y(0) | D=0]`. -/
  τ_ATU : ℝ
  /-- OLS coefficient on `D`. -/
  β_ols : ℝ
  /-- General two-component weight on `τ_ATT`. -/
  w₁ : ℝ
  /-- General two-component weight on `τ_ATU`. -/
  w₀ : ℝ
  /-- `ρ` is a probability — nonnegative side. -/
  ρ_nonneg : 0 ≤ ρ
  /-- `ρ` is a probability — `≤ 1` side. -/
  ρ_le_one : ρ ≤ 1
  /-- Supplied two-component identity: the OLS coefficient is a combination of
  the group-status effects. -/
  twoComponent : β_ols = w₁ * τ_ATT + w₀ * τ_ATU
  /-- The two weights sum to one. -/
  weights_sum_one : w₁ + w₀ = 1
  /-- Supplied equal-dispersion weight identity: the ATT weight equals the
  untreated share `1 − ρ`. -/
  equalDispersion : w₁ = 1 - ρ

namespace AssumedTwoComponentOLS

/-- For [an assumed two-component OLS scaffold](hyp:R), the
[average treatment effect](goal) is $\rho\tau_{ATT}+(1-\rho)\tau_{ATU}$,
the treated-share-weighted average of the effects on treated and untreated groups. -/
def tau_ATE (R : AssumedTwoComponentOLS) : ℝ := R.ρ * R.τ_ATT + (1 - R.ρ) * R.τ_ATU

variable (R : AssumedTwoComponentOLS)

/-- For [an assumed two-component scaffold](hyp:R), [the untreated weight equals the treated
share `ρ`](goal), by substituting the two supplied weight identities. -/
theorem w0_eq_rho_of_assumed_weights : R.w₀ = R.ρ := by
  have h := R.weights_sum_one
  rw [R.equalDispersion] at h; linarith

/-- For [an OLS coefficient already supplied in two-component form with the stated weight
identities](hyp:R), [substitution shows that it equals `(1−ρ)·τ_ATT + ρ·τ_ATU`](goal).

This is an algebraic corollary of the fields of `R`, not a derivation of the
two-component representation from a regression problem. -/
theorem opposite_group_identity_of_assumed_twoComponent :
    R.β_ols = (1 - R.ρ) * R.τ_ATT + R.ρ * R.τ_ATU := by
  rw [R.twoComponent, R.equalDispersion, R.w0_eq_rho_of_assumed_weights]

/-- **Equal-group-size collapse within the assumed scaffold.** For [an assumed
two-component scaffold](hyp:R), if [the treated share `ρ` equals one half](hyp:h), then [the
supplied OLS coefficient `β_ols` equals the ATE `τ_ATE = ρ·τ_ATT + (1−ρ)·τ_ATU`](goal). -/
theorem equal_groups_eq_ATE_of_assumed_twoComponent (h : R.ρ = 1 / 2) :
    R.β_ols = R.tau_ATE := by
  rw [R.opposite_group_identity_of_assumed_twoComponent, tau_ATE, h]; ring

/-- **Homogeneous-effect collapse within the assumed scaffold.** For [an assumed
two-component scaffold](hyp:R), if [the ATT equals a common constant `τ₀`](hyp:hT) and
[the ATU equals that same constant `τ₀`](hyp:hU), then [the supplied OLS coefficient
`β_ols` equals `τ₀`, regardless of the treated share `ρ`](goal). -/
theorem homogeneous_eq_constant_of_assumed_twoComponent
    {τ₀ : ℝ} (hT : R.τ_ATT = τ₀) (hU : R.τ_ATU = τ₀) :
    R.β_ols = τ₀ := by
  rw [R.opposite_group_identity_of_assumed_twoComponent, hT, hU]; ring

end AssumedTwoComponentOLS

end OLSWeightDecomposition
end Panel.EstimandCharacterization
end Causalean
