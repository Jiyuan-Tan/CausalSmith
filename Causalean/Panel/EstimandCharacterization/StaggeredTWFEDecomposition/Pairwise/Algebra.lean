/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon pairwise algebra layer

**Role in the folder.** *Finite-algebra support (not a headline).* Reduction
machinery feeding the algebraic headline `AlgebraicDecomposition.lean`. See
`StaggeredTWFEDecomposition.lean` for the folder layer-map.

This file sits between the paper-agnostic finite weighted identities in
`Causalean/Stat/Weighted/NormalizedWeights.lean` and the headline
Goodman-Bacon decomposition in `AlgebraicDecomposition.lean`.

It exposes the pairwise centered-treatment contributions that the denominator
and numerator identities should first reduce to before the adoption-window
case split into TN / EL / LE comparisons.
-/

module
public import Causalean.Stat.Weighted.NormalizedWeights
public import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.FinitePanel
public import Mathlib.Tactic.Ring

/-! # Goodman-Bacon Pairwise Algebra

This file reduces Goodman-Bacon denominator and numerator terms to ordered-pair
centered-treatment contributions. It is the algebraic bridge between generic
finite weighted covariance identities and the adoption-window case analysis that
produces the three comparison types in the decomposition. -/

@[expose] public section

namespace Causalean
namespace Panel.EstimandCharacterization
namespace StaggeredTWFEDecomposition

open Finset

variable {𝒢 : Type*} [Fintype 𝒢] [DecidableEq 𝒢] {T : ℕ}

/-- For a finite collection with weights summing to one, the weighted sum of deviations of one
quantity from its weighted mean times another quantity equals one half of the weighted sum of
pairwise differences in the two quantities. -/
lemma weighted_center_cov_uncentered_right {ι : Type*} [Fintype ι]
    (p x y : ι → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, p i * (x i - ∑ j, p j * x j) * y i =
      (1 / 2) * ∑ i, ∑ j, p i * p j * (x i - x j) * (y i - y j) := by
  classical
  let mx := ∑ j, p j * x j
  let my := ∑ j, p j * y j
  have hzero : ∑ i, p i * (x i - mx) = 0 := by
    calc
      ∑ i, p i * (x i - mx) = (∑ i, p i * x i) - ∑ i, p i * mx := by
        simp [mul_sub, Finset.sum_sub_distrib]
      _ = mx - (∑ i, p i) * mx := by
        simp [Finset.sum_mul, mx]
      _ = 0 := by
        rw [hp]
        ring
  have hmy : ∑ i, p i * (x i - mx) * my = 0 := by
    calc
      ∑ i, p i * (x i - mx) * my = (∑ i, p i * (x i - mx)) * my := by
        rw [Finset.sum_mul]
      _ = 0 := by
        rw [hzero]
        ring
  have hcenter : ∑ i, p i * (x i - mx) * y i =
      ∑ i, p i * (x i - mx) * (y i - my) := by
    calc
      ∑ i, p i * (x i - mx) * y i =
          ∑ i, (p i * (x i - mx) * (y i - my) + p i * (x i - mx) * my) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
      _ = ∑ i, p i * (x i - mx) * (y i - my) + ∑ i, p i * (x i - mx) * my := by
            rw [Finset.sum_add_distrib]
      _ = ∑ i, p i * (x i - mx) * (y i - my) := by
            rw [hmy]
            ring
  calc
    ∑ i, p i * (x i - ∑ j, p j * x j) * y i =
        ∑ i, p i * (x i - mx) * y i := by rfl
    _ = ∑ i, p i * (x i - mx) * (y i - my) := hcenter
    _ = ∑ i, p i * (x i - ∑ j, p j * x j) * (y i - ∑ j, p j * y j) := by rfl
    _ = (1 / 2) * ∑ i, ∑ j, p i * p j * (x i - x j) * (y i - y j) :=
      Causalean.Stat.Weighted.NormalizedWeights.weighted_center_cov p x y hp (by norm_num)

omit [DecidableEq 𝒢] in
/-- In a finite cohort panel, a cohort-weighted sum over cohorts and periods with equal period
weight equals the average over periods of the corresponding cohort-weighted sums. -/
lemma sum_weight_over_T_commute
    (P : CohortPanel 𝒢 T) (f : 𝒢 → Fin T → ℝ) :
    (∑ g, ∑ t, (P.p g / (T : ℝ)) * f g t) =
      (T : ℝ)⁻¹ * ∑ t, ∑ g, P.p g * f g t := by
  classical
  rw [Finset.sum_comm]
  simp [div_eq_mul_inv, Finset.mul_sum, mul_left_comm, mul_comm]

omit [DecidableEq 𝒢] in
/-- In a finite cohort panel, averaging half the ordered-pair weighted total at each period equals
the ordered-pair weighted total of the time sums with the same normalization. -/
lemma pairwise_sum_normalize
    (P : CohortPanel 𝒢 T) (f : 𝒢 → 𝒢 → Fin T → ℝ) :
    (T : ℝ)⁻¹ * ∑ t, ((1 / 2) * ∑ g, ∑ u, P.p g * P.p u * f g u t) =
      ∑ g, ∑ u, (P.p g * P.p u / (2 * (T : ℝ))) * ∑ t, f g u t := by
  classical
  calc
    (T : ℝ)⁻¹ * ∑ t, ((1 / 2) * ∑ g, ∑ u, P.p g * P.p u * f g u t)
        = (T : ℝ)⁻¹ * ∑ t, ∑ g, ∑ u, (1 / 2) * (P.p g * P.p u * f g u t) := by
          simp [Finset.mul_sum]
    _ = (T : ℝ)⁻¹ * ∑ g, ∑ u, ∑ t, (1 / 2) * (P.p g * P.p u * f g u t) := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro g _hg
          rw [Finset.sum_comm]
    _ = ∑ g, ∑ u, (P.p g * P.p u / (2 * (T : ℝ))) * ∑ t, f g u t := by
          simp [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

/-- For [a cohort panel](hyp:P), [a cohort](hyp:g), and [a period](hyp:t), [the cohort-demeaned treatment path](goal) is that cohort's treatment indicator in the period minus its average treatment indicator across all periods. -/
noncomputable def centeredD (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) : ℝ :=
  D P g t - barD P g

/-- For [a cohort panel](hyp:P) and [two cohorts](hyp:g,u), [the ordered-pair contribution to residualized-treatment variance](goal) is one half of their share product divided by the number of periods, multiplied by the sum of squared differences between their cohort-demeaned treatment paths.

The factor `1/2` is deliberate: the generic finite weighted variance identity
sums over ordered pairs. The Goodman-Bacon denominator later combines the two
orders `(g,u)` and `(u,g)` into one unordered comparison weight.
-/
noncomputable def vdPairContribution (P : CohortPanel 𝒢 T) (g u : 𝒢) : ℝ :=
  (P.p g * P.p u / (2 * (T : ℝ))) *
    ∑ t, (centeredD P g t - centeredD P u t)^2

/-- For [a cohort panel](hyp:P) and [two cohorts](hyp:g,u), [the ordered-pair contribution to the two-way-fixed-effects numerator](goal) is one half of their share product divided by the number of periods, multiplied by the sum of the product of their demeaned-treatment difference and factual-outcome difference.

As for `vdPairContribution`, the two orders of each cohort pair are
combined by the Goodman-Bacon-specific window lemmas below. -/
noncomputable def numPairContribution (P : CohortPanel 𝒢 T) (g u : 𝒢) : ℝ :=
  (P.p g * P.p u / (2 * (T : ℝ))) *
    ∑ t, (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t)

omit [DecidableEq 𝒢] in
/-- In a cohort panel, a cohort that is never treated has a zero treatment indicator in every
period. -/
lemma D_eq_zero_of_isInf (P : CohortPanel 𝒢 T) {u : 𝒢}
    (hu : AdoptionPath.isInfinite (P.A u)) (t : Fin T) :
    D P u t = 0 := by
  classical
  unfold D
  rw [show P.A u = ⊤ from hu]
  simp

omit [DecidableEq 𝒢] in
/-- In a cohort panel, the binary treatment indicator for any cohort and time period equals its
own square. -/
lemma D_sq_eq_D (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) :
    D P g t ^ 2 = D P g t := by
  unfold D
  by_cases h : P.A g ≤ (t : WithTop (Fin T)) <;> simp [h]

omit [DecidableEq 𝒢] in
/-- For a binary quantity observed over the panel's time periods, its average
    squared deviation from its time mean equals that mean times one minus that mean. -/
lemma binary_time_variance (hT_pos : 0 < T)
    (x : Fin T → ℝ) (hx : ∀ t, x t ^ 2 = x t) :
    (T : ℝ)⁻¹ * ∑ t, (x t - ((T : ℝ)⁻¹ * ∑ t, x t)) ^ 2 =
      ((T : ℝ)⁻¹ * ∑ t, x t) * (1 - ((T : ℝ)⁻¹ * ∑ t, x t)) := by
  classical
  let m : ℝ := (T : ℝ)⁻¹ * ∑ t, x t
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hT_pos)
  have hsum_sq : ∑ t, x t ^ 2 = ∑ t, x t := by
    exact Finset.sum_congr rfl (by intro t _ht; exact hx t)
  have hsum_expand :
      ∑ t, (x t ^ 2 - 2 * m * x t + m ^ 2) =
        ∑ t, x t - 2 * m * ∑ t, x t + (T : ℝ) * m ^ 2 := by
    calc
      ∑ t, (x t ^ 2 - 2 * m * x t + m ^ 2) =
          ∑ t, x t ^ 2 - ∑ t, 2 * m * x t + ∑ _t : Fin T, m ^ 2 := by
        simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = ∑ t, x t - 2 * m * ∑ t, x t + (T : ℝ) * m ^ 2 := by
        rw [hsum_sq]
        simp [Finset.mul_sum, Fintype.card_fin]
  calc
    (T : ℝ)⁻¹ * ∑ t, (x t - ((T : ℝ)⁻¹ * ∑ t, x t)) ^ 2 =
        (T : ℝ)⁻¹ * ∑ t, (x t ^ 2 - 2 * m * x t + m ^ 2) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      simp [m]
      ring
    _ = ((T : ℝ)⁻¹ * ∑ t, x t) * (1 - ((T : ℝ)⁻¹ * ∑ t, x t)) := by
      rw [hsum_expand]
      simp [m]
      field_simp [hTne]
      ring

omit [DecidableEq 𝒢] in
set_option linter.flexible false in
/-- For an indicator of a nonempty set of periods, the time-average product of
    its centered value and another quantity equals its variance times the difference
    between the selected-period and unselected-period averages of that quantity. -/
lemma binary_time_cov_filter_mean
    (hT_pos : 0 < T) (p : Fin T → Prop) [DecidablePred p] (z : Fin T → ℝ)
    (hcard1 : ((Finset.univ.filter p).card : ℝ) ≠ 0) :
    (T : ℝ)⁻¹ * ∑ t, ((if p t then (1 : ℝ) else 0) -
        ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) * z t =
      ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0)) *
        (1 - ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) *
          (((Finset.univ.filter p).card : ℝ)⁻¹ *
              (∑ t ∈ (Finset.univ.filter p), z t) -
            ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ)⁻¹ *
              (∑ t ∈ (Finset.univ.filter (fun t => ¬ p t)), z t)) := by
  classical
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hT_pos)
  let A : ℝ := ((Finset.univ.filter p).card : ℝ)
  let B : ℝ := ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ)
  let Z1 : ℝ := ∑ t ∈ (Finset.univ.filter p), z t
  let Z0 : ℝ := ∑ t ∈ (Finset.univ.filter (fun t => ¬ p t)), z t
  have hA : A ≠ 0 := by
    simpa [A] using hcard1
  have hsum_if : (∑ t, (if p t then (1 : ℝ) else 0)) = A := by
    simp [A]
  have hsum_if_z : (∑ t, (if p t then (1 : ℝ) else 0) * z t) = Z1 := by
    simp [Z1, Finset.sum_filter]
  have hsum_z : (∑ t, z t) = Z1 + Z0 := by
    simp [Z1, Z0, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro t _
    by_cases ht : p t <;> simp [ht]
  have hcard_total : A + B = (T : ℝ) := by
    have hnat :
        (Finset.univ.filter p).card +
            (Finset.univ.filter (fun t => ¬ p t)).card = T := by
      calc
        (Finset.univ.filter p).card +
            (Finset.univ.filter (fun t => ¬ p t)).card =
            ((Finset.univ.filter p) ∪
              (Finset.univ.filter (fun t => ¬ p t))).card := by
          rw [Finset.card_union_of_disjoint]
          simp [Finset.disjoint_left]
        _ = T := by
          have hunion :
              (Finset.univ.filter p) ∪ (Finset.univ.filter (fun t => ¬ p t)) =
                (Finset.univ : Finset (Fin T)) := by
            ext t
            simp [em]
          simp [hunion]
    simpa [A, B] using
      (show (((Finset.univ.filter p).card : ℝ) +
              ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ) = (T : ℝ)) by
        exact_mod_cast hnat)
  have hmain :
      (T : ℝ)⁻¹ * (Z1 - ((T : ℝ)⁻¹ * A) * (Z1 + Z0)) =
        ((T : ℝ)⁻¹ * A) * (1 - ((T : ℝ)⁻¹ * A)) *
          (A⁻¹ * Z1 - B⁻¹ * Z0) := by
    by_cases hB : B = 0
    · have hZT0 : Z0 = 0 := by
        have hempty : Finset.univ.filter (fun t => ¬ p t) = ∅ := by
          apply Finset.card_eq_zero.mp
          have hB' : ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ) = 0 := by
            simpa [B] using hB
          exact_mod_cast hB'
        simp [Z0, hempty]
      have hAeq : A = (T : ℝ) := by
        linarith
      rw [hZT0, hAeq]
      field_simp [hTne]
      ring
    · have hABne : A + B ≠ 0 := by
        rw [hcard_total]
        exact hTne
      rw [← hcard_total]
      field_simp [hA, hB, hABne]
      ring
  calc
    (T : ℝ)⁻¹ * ∑ t, ((if p t then (1 : ℝ) else 0) -
        ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) * z t =
        (T : ℝ)⁻¹ * (Z1 - ((T : ℝ)⁻¹ * A) * (Z1 + Z0)) := by
      rw [hsum_if]
      calc
        (T : ℝ)⁻¹ *
            ∑ t, ((if p t then (1 : ℝ) else 0) - (T : ℝ)⁻¹ * A) * z t =
            (T : ℝ)⁻¹ * (∑ t, (if p t then (1 : ℝ) else 0) * z t -
              ∑ t, ((T : ℝ)⁻¹ * A) * z t) := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro t _
          ring
        _ = (T : ℝ)⁻¹ * (Z1 - ((T : ℝ)⁻¹ * A) * (Z1 + Z0)) := by
          rw [hsum_if_z, ← Finset.mul_sum, hsum_z]
    _ = ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0)) *
        (1 - ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) *
          (((Finset.univ.filter p).card : ℝ)⁻¹ *
              (∑ t ∈ (Finset.univ.filter p), z t) -
            ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ)⁻¹ *
              (∑ t ∈ (Finset.univ.filter (fun t => ¬ p t)), z t)) := by
      rw [hmain, hsum_if]

omit [DecidableEq 𝒢] in
open Classical in
/-- Given [a finite-cohort panel and a cohort](hyp:𝒢,T,P,g), if [the cohort has a finite
adoption date](hyp:hg), then [the real-valued cardinality of its treated-period window is nonzero](goal). -/
lemma TN_treated_window_card_ne_zero
    (P : CohortPanel 𝒢 T) {g : 𝒢} (hg : AdoptionPath.isFinite (P.A g)) :
    ((Finset.univ.filter (fun t => AdoptionPath.le (P.A g) t)).card : ℝ) ≠ 0 := by
  cases hA : P.A g with
  | top =>
      exact False.elim (hg hA)
  | coe a =>
      have hmem : a ∈ Finset.univ.filter (fun t => AdoptionPath.le (P.A g) t) := by
        simp [AdoptionPath.le, hA]
      have hpos : 0 < (Finset.univ.filter
          (fun t => AdoptionPath.le (P.A g) t)).card :=
        Finset.card_pos.mpr ⟨a, hmem⟩
      have hne :
          ((Finset.univ.filter (fun t => AdoptionPath.le (P.A g) t)).card : ℝ) ≠
            0 := by
        exact_mod_cast (ne_of_gt hpos)
      simpa [hA] using hne

open Classical in
/-- Given [a finite-cohort panel and two cohorts](hyp:𝒢,T,P,e,ℓ), if [the first adopts
before the second](hyp:hord), then [the real-valued cardinality of the periods between their
adoption dates is nonzero](goal). This includes the case where the second cohort never adopts. -/
lemma TT_middle_window_card_ne_zero
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) :
    ((Finset.univ.filter
        (fun t => AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t)).card :
      ℝ) ≠ 0 := by
  cases he : P.A e with
  | top =>
      have hbad := hord
      simp [he] at hbad
  | coe a =>
      cases hℓA : P.A ℓ with
      | top =>
          have hmem : a ∈ Finset.univ.filter
              (fun t => AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t) := by
            simp [AdoptionPath.le, AdoptionPath.lt, he, hℓA]
          have hpos : 0 < (Finset.univ.filter
              (fun t => AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t)).card :=
            Finset.card_pos.mpr ⟨a, hmem⟩
          have hne :
              ((Finset.univ.filter
                (fun t => AdoptionPath.le (P.A e) t ∧
                  AdoptionPath.lt (P.A ℓ) t)).card : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt hpos)
          simpa [he, hℓA] using hne
      | coe b =>
          have hab : (a : WithTop (Fin T)) < (b : WithTop (Fin T)) := by
            simpa [he, hℓA] using hord
          have habFin : a < b := by
            exact (WithTop.coe_lt_coe (a := b) (b := a)).mp hab
          have hmem : a ∈ Finset.univ.filter
              (fun t => AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t) := by
            simp [AdoptionPath.le, AdoptionPath.lt, he, hℓA, habFin]
          have hpos : 0 < (Finset.univ.filter
              (fun t => AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t)).card :=
            Finset.card_pos.mpr ⟨a, hmem⟩
          have hne :
              ((Finset.univ.filter
                (fun t => AdoptionPath.le (P.A e) t ∧
                  AdoptionPath.lt (P.A ℓ) t)).card : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt hpos)
          simpa [he, hℓA] using hne

private lemma weighted_centeredD_mean (P : CohortPanel 𝒢 T) (t : Fin T) :
    (∑ h, P.p h * centeredD P h t) = (∑ h, P.p h * D P h t) - pCohort P := by
  unfold centeredD pCohort
  calc
    (∑ h, P.p h * (D P h t - barD P h)) =
        ∑ h, (P.p h * D P h t - P.p h * barD P h) := by
          refine Finset.sum_congr rfl ?_
          intro h _hh
          ring
    _ = (∑ h, P.p h * D P h t) - ∑ h, P.p h * barD P h := by
          simp only [Finset.sum_sub_distrib]

/-- The explicit double-demeaning formula for `Dtilde` is the weighted
centering, across cohorts, of the cohort-demeaned treatment path. -/
lemma Dtilde_eq_centeredD_sub_weighted_mean
    (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) :
    Dtilde P g t = centeredD P g t - ∑ h, P.p h * centeredD P h t := by
  rw [weighted_centeredD_mean P t]
  rw [Dtilde_eq]
  unfold centeredD
  ring

/-- For [a cohort panel](hyp:P), [the residualized-treatment variance `VD P` equals the sum,
over all ordered pairs of cohorts, of their pairwise centered-treatment contribution
`vdPairContribution P g u`](goal).

Proof route: rewrite `Dtilde` using
`Dtilde_eq_centeredD_sub_weighted_mean`, swap the `g`/`t` finite sums, and
apply `Causalean.Stat.Weighted.NormalizedWeights.weighted_center_var` at each period `t`. -/
lemma VD_eq_pairwise_centeredD (P : CohortPanel 𝒢 T) :
    VD P = ∑ g, ∑ u, vdPairContribution P g u := by
  classical
  calc
    VD P = (T : ℝ)⁻¹ * ∑ t, ∑ g, P.p g * (Dtilde P g t)^2 := by
      unfold VD
      exact sum_weight_over_T_commute P (fun g t => (Dtilde P g t)^2)
    _ = (T : ℝ)⁻¹ * ∑ t, ∑ g, P.p g *
        (centeredD P g t - ∑ h, P.p h * centeredD P h t)^2 := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      refine Finset.sum_congr rfl ?_
      intro g _hg
      rw [Dtilde_eq_centeredD_sub_weighted_mean]
    _ = (T : ℝ)⁻¹ * ∑ t,
        ((1 / 2) * ∑ g, ∑ u, P.p g * P.p u *
          (centeredD P g t - centeredD P u t)^2) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      exact Causalean.Stat.Weighted.NormalizedWeights.weighted_center_var (fun g => P.p g)
        (fun g => centeredD P g t) P.p_sum_one (by norm_num)
    _ = ∑ g, ∑ u, vdPairContribution P g u := by
      unfold vdPairContribution
      exact pairwise_sum_normalize P
        (fun g u t => (centeredD P g t - centeredD P u t)^2)

/-- Pairwise representation of the TWFE numerator.

Proof route: rewrite `Dtilde` using
`Dtilde_eq_centeredD_sub_weighted_mean`, use that the weighted centered
`D` term has zero cohort mean at each period, and apply
`Causalean.Stat.Weighted.NormalizedWeights.weighted_center_cov` to the cohort dimension. -/
lemma twfe_numerator_eq_pairwise_centeredD_Y (P : CohortPanel 𝒢 T) :
    (∑ g, ∑ t, (P.p g / (T : ℝ)) * Dtilde P g t * P.Y g t) =
      ∑ g, ∑ u, numPairContribution P g u := by
  classical
  calc
    (∑ g, ∑ t, (P.p g / (T : ℝ)) * Dtilde P g t * P.Y g t) =
        ∑ g, ∑ t, (P.p g / (T : ℝ)) * (Dtilde P g t * P.Y g t) := by
      refine Finset.sum_congr rfl ?_
      intro g _hg
      refine Finset.sum_congr rfl ?_
      intro t _ht
      ring
    _ = (T : ℝ)⁻¹ * ∑ t, ∑ g, P.p g * (Dtilde P g t * P.Y g t) := by
      exact sum_weight_over_T_commute P (fun g t => Dtilde P g t * P.Y g t)
    _ = (T : ℝ)⁻¹ * ∑ t, ∑ g, P.p g *
        (centeredD P g t - ∑ h, P.p h * centeredD P h t) * P.Y g t := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      refine Finset.sum_congr rfl ?_
      intro g _hg
      rw [Dtilde_eq_centeredD_sub_weighted_mean]
      ring
    _ = (T : ℝ)⁻¹ * ∑ t,
        ((1 / 2) * ∑ g, ∑ u, P.p g * P.p u *
          (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t)) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      exact weighted_center_cov_uncentered_right (fun g => P.p g)
        (fun g => centeredD P g t) (fun g => P.Y g t) P.p_sum_one
    _ = ∑ g, ∑ u, numPairContribution P g u := by
      unfold numPairContribution
      simpa [mul_assoc] using pairwise_sum_normalize P
        (fun g u t => (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t))


end StaggeredTWFEDecomposition
end Panel.EstimandCharacterization
end Causalean
