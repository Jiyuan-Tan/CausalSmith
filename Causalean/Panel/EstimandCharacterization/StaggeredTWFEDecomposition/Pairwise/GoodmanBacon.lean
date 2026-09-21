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
public import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.Pairwise.Algebra

/-! # Goodman-Bacon Pairwise Contribution Formulas

This part proves the treated-never-treated and treated-treated pairwise denominator
and numerator contribution formulas used by the staggered-TWFE decomposition. -/

public section

namespace Causalean
namespace Panel.EstimandCharacterization
namespace StaggeredTWFEDecomposition

open Finset

variable {𝒢 : Type*} [Fintype 𝒢] [DecidableEq 𝒢] {T : ℕ}

omit [DecidableEq 𝒢] in
private lemma barD_eq_zero_of_isInf (P : CohortPanel 𝒢 T) {u : 𝒢}
    (hu : AdoptionPath.isInfinite (P.A u)) :
    barD P u = 0 := by
  unfold barD
  simp [D_eq_zero_of_isInf P hu]

/-! ### Pairwise Goodman-Bacon helper layer -/

/-- Symmetric denominator helper for `TN_pair_vd_contribution_eq_gap` and
`TT_pair_vd_contribution_eq_gap`: after adding the two ordered pair
contributions, only the raw time variance of the centered treatment gap
remains. -/
private lemma vdPairContribution_add_swap
    (P : CohortPanel 𝒢 T) (g u : 𝒢) :
    vdPairContribution P g u + vdPairContribution P u g =
      (P.p g * P.p u / (T : ℝ)) *
        ∑ t, (centeredD P g t - centeredD P u t)^2 := by
  classical
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hsum :
      (∑ t, (centeredD P u t - centeredD P g t)^2) =
        ∑ t, (centeredD P g t - centeredD P u t)^2 := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    ring
  unfold vdPairContribution
  rw [hsum]
  field_simp [hTne]
  ring

/-- Symmetric numerator helper for `TN_pair_contribution_eq_lambda_delta` and
`TT_pair_contribution_eq_lambda_delta_sum`: after adding the two ordered pair
contributions, the two sign reversals in the swapped covariance term cancel. -/
private lemma numPairContribution_add_swap
    (P : CohortPanel 𝒢 T) (g u : 𝒢) :
    numPairContribution P g u + numPairContribution P u g =
      (P.p g * P.p u / (T : ℝ)) *
        ∑ t, (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t) := by
  classical
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hsum :
      (∑ t, (centeredD P u t - centeredD P g t) * (P.Y u t - P.Y g t)) =
        ∑ t, (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t) := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    ring
  unfold numPairContribution
  rw [hsum]
  field_simp [hTne]
  ring

/-- TN denominator/numerator bridge used by the TN pair lemmas: the
never-treated cohort contributes zero to both `D` and `barD`, so the centered
gap is exactly the finite cohort's demeaned treatment path. -/
private lemma TN_centeredD_gap_eq
    (P : CohortPanel 𝒢 T) {g u : 𝒢} (hu : AdoptionPath.isInfinite (P.A u)) (t : Fin T) :
    centeredD P g t - centeredD P u t = D P g t - barD P g := by
  unfold centeredD
  rw [D_eq_zero_of_isInf P hu t, barD_eq_zero_of_isInf P hu]
  ring

open Classical in
private lemma TN_filter_not_treated_eq_S0
    (P : CohortPanel 𝒢 T) (g : 𝒢) :
    Finset.univ.filter (fun t => ¬ AdoptionPath.le (P.A g) t) = S0_TN P g := by
  rw [S0_TN]
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [AdoptionPath.le, AdoptionPath.lt]
  exact not_le

open Classical in
private lemma TT_D_gap_eq_middle_indicator
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) (t : Fin T) :
    D P e t - D P ℓ t =
      if AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t then 1 else 0 := by
  unfold D
  by_cases hℓt : P.A ℓ ≤ (t : WithTop (Fin T))
  · have het : P.A e ≤ (t : WithTop (Fin T)) := le_trans (le_of_lt hord) hℓt
    have hnlt : ¬(t : WithTop (Fin T)) < P.A ℓ := by
      exact fun h => not_lt_of_ge hℓt h
    simp [hℓt, het, hnlt]
  · have hlt : (t : WithTop (Fin T)) < P.A ℓ := by
      exact not_le.mp hℓt
    by_cases het : P.A e ≤ (t : WithTop (Fin T)) <;> simp [hℓt, hlt, het]

/-- TN denominator bridge for `TN_pair_vd_contribution_eq_gap`: rewrites the
time variance of the centered treated-vs-never gap as the Bernoulli variance of
the finite cohort's treatment path. -/
private lemma TN_time_variance_eq_gap
    (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hu : AdoptionPath.isInfinite (P.A u)) :
    (T : ℝ)⁻¹ * ∑ t, (centeredD P g t - centeredD P u t)^2 =
      q P g u * (1 - q P g u) := by
  calc
    (T : ℝ)⁻¹ * ∑ t, (centeredD P g t - centeredD P u t)^2 =
        (T : ℝ)⁻¹ * ∑ t, (D P g t - barD P g)^2 := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      rw [TN_centeredD_gap_eq P hu t]
    _ = barD P g * (1 - barD P g) := by
      simpa [barD] using binary_time_variance P.T_pos (fun t => D P g t) (D_sq_eq_D P g)
    _ = q P g u * (1 - q P g u) := by
      rw [q, barD_eq_zero_of_isInf P hu]
      ring

/-- TT denominator bridge for `TT_pair_vd_contribution_eq_gap`: under
`A_e < A_ℓ < ⊤`, the centered early-late gap has variance
`q P e ℓ * (1 - q P e ℓ)`. -/
private lemma TT_time_variance_eq_gap
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) :
    (T : ℝ)⁻¹ * ∑ t, (centeredD P e t - centeredD P ℓ t)^2 =
      q P e ℓ * (1 - q P e ℓ) := by
  let x : Fin T → ℝ := fun t => D P e t - D P ℓ t
  have hx : ∀ t, x t ^ 2 = x t := by
    intro t
    unfold x D
    by_cases hℓt : P.A ℓ ≤ (t : WithTop (Fin T))
    · by_cases het : P.A e ≤ (t : WithTop (Fin T))
      · simp [hℓt, het]
      · have : P.A e ≤ (t : WithTop (Fin T)) := le_trans (le_of_lt hord) hℓt
        exact False.elim (het this)
    · by_cases het : P.A e ≤ (t : WithTop (Fin T)) <;> simp [hℓt, het]
  have hmean : (T : ℝ)⁻¹ * ∑ t, x t = q P e ℓ := by
    unfold x q barD
    rw [Finset.sum_sub_distrib]
    ring
  calc
    (T : ℝ)⁻¹ * ∑ t, (centeredD P e t - centeredD P ℓ t)^2 =
        (T : ℝ)⁻¹ * ∑ t, (x t - ((T : ℝ)⁻¹ * ∑ t, x t))^2 := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      unfold x centeredD
      rw [hmean]
      unfold q
      ring
    _ = q P e ℓ * (1 - q P e ℓ) := by
      rw [binary_time_variance P.T_pos x hx, hmean]

/-- When two finite sets are disjoint and the second is nonempty, the mean of a quantity over
their union is the cardinality-weighted combination of its means over the two sets. -/
lemma disjoint_union_mean_eq_card_weighted_mean {α : Type*} [DecidableEq α]
    (A B : Finset α) (z : α → ℝ) (hdisj : Disjoint A B)
    (hB : ((B.card : ℝ) ≠ 0)) :
    (((A ∪ B).card : ℝ)⁻¹ * ∑ t ∈ A ∪ B, z t) =
      ((A.card : ℝ) / ((A ∪ B).card : ℝ)) *
          ((A.card : ℝ)⁻¹ * ∑ t ∈ A, z t) +
        (1 - ((A.card : ℝ) / ((A ∪ B).card : ℝ))) *
          ((B.card : ℝ)⁻¹ * ∑ t ∈ B, z t) := by
  classical
  let a : ℝ := A.card
  let b : ℝ := B.card
  let ZA : ℝ := ∑ t ∈ A, z t
  let ZB : ℝ := ∑ t ∈ B, z t
  have hsum : ∑ t ∈ A ∪ B, z t = ZA + ZB := by
    simp [ZA, ZB, Finset.sum_union hdisj]
  have hcard : ((A ∪ B).card : ℝ) = a + b := by
    have hnat : (A ∪ B).card = A.card + B.card :=
      Finset.card_union_of_disjoint hdisj
    simp [a, b, hnat]
  have hb : b ≠ 0 := by simpa [b] using hB
  have hbpos : 0 < b := by
    have hBnat : B.card ≠ 0 := by
      exact_mod_cast hB
    dsimp [b]
    exact_mod_cast (Nat.pos_of_ne_zero hBnat)
  have hab : a + b ≠ 0 := by
    intro h
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact_mod_cast (Nat.zero_le A.card)
    linarith
  by_cases ha : a = 0
  · have hAempty : A = ∅ := by
      apply Finset.card_eq_zero.mp
      have : (A.card : ℝ) = 0 := by simpa [a] using ha
      exact Nat.cast_eq_zero.mp this
    have hZA : ZA = 0 := by simp [ZA, hAempty]
    rw [hsum, hcard, hZA, ha]
    simp [hAempty]
    field_simp [hb]
    ring
  · have haA : ((A.card : ℝ) ≠ 0) := by
      simpa [a] using ha
    have hAB : ((A.card : ℝ) + (B.card : ℝ)) ≠ 0 := by
      simpa [a, b] using hab
    rw [hsum, hcard]
    field_simp [haA, hB, hAB]
    simp [a, b, ZA, ZB]
    ring_nf

open Classical in
private lemma TT_middle_filter_eq_S1_EL
    (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) :
    Finset.univ.filter
        (fun t => AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t) =
      S1_EL P e ℓ := by
  ext t
  rfl

open Classical in
private lemma TT_middle_filter_eq_S0_LE
    (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) :
    Finset.univ.filter
        (fun t => AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t) =
      S0_LE P e ℓ := by
  ext t
  simp [S0_LE, S1_EL]

set_option linter.flexible false in
open Classical in
private lemma TT_middle_complement_eq_pre_union_post
    (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) :
    Finset.univ.filter
        (fun t => ¬ (AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t)) =
      S0_EL P e ∪ S1_LE P ℓ := by
  ext t
  simp only [Finset.mem_union, S0_EL, S1_LE, Finset.mem_filter, Finset.mem_univ, true_and]
  simp
  constructor
  · intro h
    by_cases hpre : (t : WithTop (Fin T)) < P.A e
    · exact Or.inl hpre
    · have he : P.A e ≤ (t : WithTop (Fin T)) := le_of_not_gt hpre
      exact Or.inr (h he)
  · intro h hmid
    rcases h with hpre | hpost
    · exact False.elim ((not_lt_of_ge hmid) hpre)
    · exact hpost

set_option linter.flexible false in
private lemma TT_disjoint_pre_mid
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢} :
    Disjoint (S0_EL P e) (S1_EL P e ℓ) := by
  rw [Finset.disjoint_left]
  intro t ht0 ht1
  simp only [S0_EL, S1_EL, Finset.mem_filter, Finset.mem_univ, true_and] at ht0 ht1
  simp only [AdoptionPath.le, AdoptionPath.lt] at ht0 ht1
  exact not_lt_of_ge ht1.1 ht0

set_option linter.flexible false in
private lemma TT_disjoint_mid_post
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢} :
    Disjoint (S1_EL P e ℓ) (S1_LE P ℓ) := by
  rw [Finset.disjoint_left]
  intro t htm htp
  simp only [S1_EL, S1_LE, Finset.mem_filter, Finset.mem_univ, true_and] at htm htp
  simp only [AdoptionPath.le, AdoptionPath.lt] at htm htp
  exact not_lt_of_ge htp htm.2

set_option linter.flexible false in
private lemma TT_disjoint_pre_post
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢} (hord : P.A e < P.A ℓ) :
    Disjoint (S0_EL P e) (S1_LE P ℓ) := by
  rw [Finset.disjoint_left]
  intro t ht0 ht1
  simp only [S0_EL, S1_LE, Finset.mem_filter, Finset.mem_univ, true_and] at ht0 ht1
  simp only [AdoptionPath.le, AdoptionPath.lt] at ht0 ht1
  exact not_lt_of_ge ht1 (lt_trans ht0 hord)

private lemma TT_pre_mid_post_union
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢} :
    S0_EL P e ∪ S1_EL P e ℓ ∪ S1_LE P ℓ =
      (Finset.univ : Finset (Fin T)) := by
  ext t
  simp only [Finset.mem_union, S0_EL, S1_EL, S1_LE, Finset.mem_filter, Finset.mem_univ,
    true_and]
  simp [AdoptionPath.le, AdoptionPath.lt]
  by_cases hpre : (t : WithTop (Fin T)) < P.A e
  · simp [hpre]
  · have he : P.A e ≤ (t : WithTop (Fin T)) := le_of_not_gt hpre
    by_cases hmid : (t : WithTop (Fin T)) < P.A ℓ
    · simp [hpre, he, hmid]
    · have hpost : P.A ℓ ≤ (t : WithTop (Fin T)) := le_of_not_gt hmid
      simp [hpre, he, hmid, hpost]

open Classical in
private lemma TT_post_window_card_ne_zero
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢} (hℓ : AdoptionPath.isFinite (P.A ℓ)) :
    (((S1_LE P ℓ).card : ℝ) ≠ 0) := by
  cases hA : P.A ℓ with
  | top =>
      exact False.elim (hℓ hA)
  | coe a =>
      have hmem : a ∈ S1_LE P ℓ := by
        simp [S1_LE, hA]
      have hpos : 0 < (S1_LE P ℓ).card :=
        Finset.card_pos.mpr ⟨a, hmem⟩
      exact_mod_cast (ne_of_gt hpos)

set_option linter.flexible false in
private lemma TT_mu_eq_pre_complement_share
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) (hℓ : AdoptionPath.isFinite (P.A ℓ)) :
    mu P e ℓ =
      ((S0_EL P e).card : ℝ) /
        (((S0_EL P e ∪ S1_LE P ℓ).card : ℝ)) := by
  classical
  let A := S0_EL P e
  let M := S1_EL P e ℓ
  let B := S1_LE P ℓ
  have hpre_mid : Disjoint A M := by
    simpa [A, M] using TT_disjoint_pre_mid P (e := e) (ℓ := ℓ)
  have hmid_post : Disjoint M B := by
    simpa [M, B] using TT_disjoint_mid_post P (e := e) (ℓ := ℓ)
  have hpre_post : Disjoint A B := by
    simpa [A, B] using TT_disjoint_pre_post P hord
  have huniv : A ∪ M ∪ B = (Finset.univ : Finset (Fin T)) := by
    simpa [A, M, B] using TT_pre_mid_post_union P
  have hAM_B : Disjoint (A ∪ M) B := by
    rw [Finset.disjoint_left]
    intro t ht hb
    rw [Finset.mem_union] at ht
    rcases ht with ht | ht
    · exact (Finset.disjoint_left.mp hpre_post) ht hb
    · exact (Finset.disjoint_left.mp hmid_post) ht hb
  have htreated_e :
      Finset.univ.filter (fun t => AdoptionPath.le (P.A e) t) = M ∪ B := by
    ext t
    simp only [M, B, Finset.mem_union, S1_EL, S1_LE, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simp [AdoptionPath.le]
    constructor
    · intro he
      by_cases hlt : (t : WithTop (Fin T)) < P.A ℓ
      · exact Or.inl ⟨he, hlt⟩
      · exact Or.inr (le_of_not_gt hlt)
    · intro h
      rcases h with h | h
      · exact h.1
      · exact le_trans (le_of_lt hord) h
  have hbar_e : barD P e = (T : ℝ)⁻¹ * ((M ∪ B).card : ℝ) := by
    unfold barD D
    rw [← htreated_e]
    apply congrArg (fun x : ℝ => (T : ℝ)⁻¹ * x)
    exact Finset.sum_boole (R := ℝ)
      (fun t : Fin T => AdoptionPath.le (P.A e) t) Finset.univ
  have hbar_l : barD P ℓ = (T : ℝ)⁻¹ * (B.card : ℝ) := by
    unfold barD D
    change (T : ℝ)⁻¹ * (∑ t, if AdoptionPath.le (P.A ℓ) t then 1 else 0) =
      (T : ℝ)⁻¹ * ((Finset.univ.filter
        (fun t => AdoptionPath.le (P.A ℓ) t)).card : ℝ)
    apply congrArg (fun x : ℝ => (T : ℝ)⁻¹ * x)
    exact Finset.sum_boole (R := ℝ)
      (fun t : Fin T => AdoptionPath.le (P.A ℓ) t) Finset.univ
  have hMBcard : ((M ∪ B).card : ℝ) = (M.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_union_of_disjoint hmid_post)
  have hABcard : ((A ∪ B).card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_union_of_disjoint hpre_post)
  have hTcard : (T : ℝ) = (A.card : ℝ) + (M.card : ℝ) + (B.card : ℝ) := by
    have hnat : A.card + M.card + B.card = T := by
      calc
        A.card + M.card + B.card = (A ∪ M).card + B.card := by
          rw [Finset.card_union_of_disjoint hpre_mid]
        _ = ((A ∪ M) ∪ B).card := by
          rw [Finset.card_union_of_disjoint hAM_B]
        _ = T := by
          rw [huniv]
          simp
    exact_mod_cast hnat.symm
  have hqM : q P e ℓ = (T : ℝ)⁻¹ * (M.card : ℝ) := by
    unfold q
    rw [hbar_e, hbar_l, hMBcard]
    ring
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hBne : ((B.card : ℝ) ≠ 0) := by
    simpa [B] using TT_post_window_card_ne_zero P (e := e) hℓ
  have hABne : ((A.card : ℝ) + (B.card : ℝ)) ≠ 0 := by
    intro h
    have hb0 : (B.card : ℝ) = 0 := by
      nlinarith [show (0 : ℝ) ≤ (A.card : ℝ) by exact_mod_cast (Nat.zero_le A.card)]
    exact hBne hb0
  unfold mu
  rw [hbar_e, hqM, hMBcard, hABcard, hTcard]
  field_simp [hTne, hABne]
  ring_nf
  simp [A]
  field_simp [hABne]
  ring

/-- TN numerator bridge for `TN_pair_contribution_eq_lambda_delta`: rewrites
the centered treated-vs-never time covariance as the raw TN weight factor times
the two-window DID contrast. -/
private lemma TN_time_cov_eq_lambda_delta_core
    (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hg : AdoptionPath.isFinite (P.A g)) (hu : AdoptionPath.isInfinite (P.A u)) :
    (T : ℝ)⁻¹ * ∑ t,
      (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t) =
      barD P g * (1 - barD P g) * Δ_TN P g u := by
  classical
  let p : Fin T → Prop := fun t => AdoptionPath.le (P.A g) t
  let z : Fin T → ℝ := fun t => P.Y g t - P.Y u t
  have hcov := binary_time_cov_filter_mean P.T_pos p z
    (by simpa [p] using TN_treated_window_card_ne_zero P hg)
  have hbar :
      ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0)) = barD P g := by
    unfold p barD D
    rfl
  have hS1 : Finset.univ.filter p = S1_TN P g := by
    ext t
    simp [p, S1_TN]
  have hS0 : Finset.univ.filter (fun t => ¬ p t) = S0_TN P g := by
    simpa [p] using TN_filter_not_treated_eq_S0 P g
  have hdelta :
      (((Finset.univ.filter p).card : ℝ)⁻¹ *
            (∑ t ∈ (Finset.univ.filter p), z t) -
          ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ)⁻¹ *
            (∑ t ∈ (Finset.univ.filter (fun t => ¬ p t)), z t)) =
        Δ_TN P g u := by
    rw [hS1, hS0]
    unfold z Δ_TN Ybar
    simp only [Finset.sum_sub_distrib]
    ring
  calc
    (T : ℝ)⁻¹ * ∑ t,
        (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t) =
        (T : ℝ)⁻¹ * ∑ t, ((if p t then (1 : ℝ) else 0) -
          ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) * z t := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      rw [TN_centeredD_gap_eq P hu t]
      unfold p z barD D
      ring
    _ = barD P g * (1 - barD P g) * Δ_TN P g u := by
      rw [hcov, hbar, hdelta]

/-- TT numerator bridge for `TT_pair_contribution_eq_lambda_delta_sum`: rewrites
the centered early-late time covariance as the `mu`-weighted EL and LE DID
contrast combination. -/
private lemma TT_time_cov_eq_lambda_delta_core
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) (hℓ : AdoptionPath.isFinite (P.A ℓ)) :
    (T : ℝ)⁻¹ * ∑ t,
      (centeredD P e t - centeredD P ℓ t) * (P.Y e t - P.Y ℓ t) =
      q P e ℓ * (1 - q P e ℓ) *
        (mu P e ℓ * Δ_EL P e ℓ + (1 - mu P e ℓ) * Δ_LE P e ℓ) := by
  classical
  let p : Fin T → Prop := fun t =>
    AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t
  let z : Fin T → ℝ := fun t => P.Y e t - P.Y ℓ t
  have hcov := binary_time_cov_filter_mean P.T_pos p z
    (by simpa [p] using TT_middle_window_card_ne_zero P hord)
  have hq :
      ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0)) = q P e ℓ := by
    calc
      (T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0) =
          (T : ℝ)⁻¹ * ∑ t, (D P e t - D P ℓ t) := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro t _ht
        rw [TT_D_gap_eq_middle_indicator P hord t]
      _ = q P e ℓ := by
        unfold q barD
        rw [Finset.sum_sub_distrib]
        ring
  have hqbar :
      barD P e - barD P ℓ =
        ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0)) := by
    rw [hq]
    rfl
  have hdid :
      (((Finset.univ.filter p).card : ℝ)⁻¹ *
            (∑ t ∈ (Finset.univ.filter p), z t) -
          ((Finset.univ.filter (fun t => ¬ p t)).card : ℝ)⁻¹ *
            (∑ t ∈ (Finset.univ.filter (fun t => ¬ p t)), z t)) =
        mu P e ℓ * Δ_EL P e ℓ + (1 - mu P e ℓ) * Δ_LE P e ℓ := by
    have hmid1 : Finset.univ.filter p = S1_EL P e ℓ := by
      simpa [p] using TT_middle_filter_eq_S1_EL P e ℓ
    have hmid0 : Finset.univ.filter p = S0_LE P e ℓ := by
      simpa [p] using TT_middle_filter_eq_S0_LE P e ℓ
    have hcomp :
        Finset.univ.filter (fun t => ¬ p t) = S0_EL P e ∪ S1_LE P ℓ := by
      simpa [p] using TT_middle_complement_eq_pre_union_post P e ℓ
    have hcomp_mean :=
      disjoint_union_mean_eq_card_weighted_mean (S0_EL P e) (S1_LE P ℓ) z
        (TT_disjoint_pre_post P hord) (TT_post_window_card_ne_zero P (e := e) hℓ)
    have hmu := TT_mu_eq_pre_complement_share P hord hℓ
    rw [hmid1, hcomp, hcomp_mean, hmu]
    unfold z Δ_EL Δ_LE Ybar
    rw [← hmid1, ← hmid0]
    simp only [Finset.sum_sub_distrib]
    ring
  calc
    (T : ℝ)⁻¹ * ∑ t,
        (centeredD P e t - centeredD P ℓ t) * (P.Y e t - P.Y ℓ t) =
        (T : ℝ)⁻¹ * ∑ t, ((if p t then (1 : ℝ) else 0) -
          ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) * z t := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t _ht
      have hdgap : D P e t - D P ℓ t = if p t then (1 : ℝ) else 0 := by
        rw [TT_D_gap_eq_middle_indicator P hord t]
      calc
        (centeredD P e t - centeredD P ℓ t) * (P.Y e t - P.Y ℓ t) =
            ((D P e t - D P ℓ t) - (barD P e - barD P ℓ)) *
              (P.Y e t - P.Y ℓ t) := by
          unfold centeredD
          ring
        _ = ((if p t then (1 : ℝ) else 0) -
            ((T : ℝ)⁻¹ * ∑ t, (if p t then (1 : ℝ) else 0))) * z t := by
          rw [hdgap, hqbar]
    _ = q P e ℓ * (1 - q P e ℓ) *
        (mu P e ℓ * Δ_EL P e ℓ + (1 - mu P e ℓ) * Δ_LE P e ℓ) := by
      rw [hcov, hq, hdid]

/-- TN denominator pair: combining the two ordered pairwise-variance
contributions gives the treated-vs-never raw denominator factor. -/
lemma TN_pair_vd_contribution_eq_gap
    (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hu : AdoptionPath.isInfinite (P.A u)) :
    vdPairContribution P g u + vdPairContribution P u g =
      P.p g * P.p u * q P g u * (1 - q P g u) := by
  rw [vdPairContribution_add_swap]
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hvar := TN_time_variance_eq_gap P (g := g) hu
  calc
    (P.p g * P.p u / (T : ℝ)) *
        ∑ t, (centeredD P g t - centeredD P u t)^2 =
        P.p g * P.p u *
          ((T : ℝ)⁻¹ * ∑ t, (centeredD P g t - centeredD P u t)^2) := by
      field_simp [hTne]
    _ = P.p g * P.p u * q P g u * (1 - q P g u) := by
      rw [hvar]
      ring

/-- Treated-treated denominator pair: combining the two ordered
pairwise-variance contributions gives the timing-pair raw denominator factor. -/
lemma TT_pair_vd_contribution_eq_gap
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) :
    vdPairContribution P e ℓ + vdPairContribution P ℓ e =
      P.p e * P.p ℓ * q P e ℓ * (1 - q P e ℓ) := by
  rw [vdPairContribution_add_swap]
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hvar := TT_time_variance_eq_gap P hord
  calc
    (P.p e * P.p ℓ / (T : ℝ)) *
        ∑ t, (centeredD P e t - centeredD P ℓ t)^2 =
        P.p e * P.p ℓ *
          ((T : ℝ)⁻¹ * ∑ t, (centeredD P e t - centeredD P ℓ t)^2) := by
      field_simp [hTne]
    _ = P.p e * P.p ℓ * q P e ℓ * (1 - q P e ℓ) := by
      rw [hvar]
      ring

/-- **TN numerator pair.** For [a treated cohort `g` with finite adoption date](hyp:hg) and
[a never-treated cohort `u` with infinite adoption date](hyp:hu), the sum of the two ordered
pairwise-covariance contributions between `g` and `u` in the finite cohort panel `P` [equals the
product of the TN comparison weight and the treated-versus-never contrast,
`λ_TN P g u · Δ_TN P g u`](goal). -/
lemma TN_pair_contribution_eq_lambda_delta
    (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hg : AdoptionPath.isFinite (P.A g)) (hu : AdoptionPath.isInfinite (P.A u)) :
    numPairContribution P g u + numPairContribution P u g =
      lambdaTN P g u * Δ_TN P g u := by
  rw [numPairContribution_add_swap]
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hcov := TN_time_cov_eq_lambda_delta_core P hg hu
  calc
    (P.p g * P.p u / (T : ℝ)) *
        ∑ t, (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t) =
        P.p g * P.p u *
          ((T : ℝ)⁻¹ * ∑ t,
            (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t)) := by
      field_simp [hTne]
    _ = lambdaTN P g u * Δ_TN P g u := by
      rw [hcov]
      unfold lambdaTN
      ring

/-- Treated-treated numerator pair: combining the two ordered
pairwise-covariance contributions splits into the EL and LE comparison
windows. -/
lemma TT_pair_contribution_eq_lambda_delta_sum
    (P : CohortPanel 𝒢 T) {e ℓ : 𝒢}
    (hord : P.A e < P.A ℓ) (hℓ : AdoptionPath.isFinite (P.A ℓ)) :
    numPairContribution P e ℓ + numPairContribution P ℓ e =
      lambdaEL P e ℓ * Δ_EL P e ℓ + lambdaLE P e ℓ * Δ_LE P e ℓ := by
  rw [numPairContribution_add_swap]
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.T_pos)
  have hcov := TT_time_cov_eq_lambda_delta_core P hord hℓ
  calc
    (P.p e * P.p ℓ / (T : ℝ)) *
        ∑ t, (centeredD P e t - centeredD P ℓ t) * (P.Y e t - P.Y ℓ t) =
        P.p e * P.p ℓ *
          ((T : ℝ)⁻¹ * ∑ t,
            (centeredD P e t - centeredD P ℓ t) * (P.Y e t - P.Y ℓ t)) := by
      field_simp [hTne]
    _ = lambdaEL P e ℓ * Δ_EL P e ℓ + lambdaLE P e ℓ * Δ_LE P e ℓ := by
      rw [hcov]
      unfold lambdaEL lambdaLE
      ring

end StaggeredTWFEDecomposition
end Panel.EstimandCharacterization
end Causalean
