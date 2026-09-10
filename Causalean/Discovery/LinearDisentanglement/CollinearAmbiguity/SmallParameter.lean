/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity.Algebra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

/-!
# Selecting a simultaneous small deformation parameter

This module proves the openness step for the transformed invariant and packages all
algebraic, normalization, invertibility, cycle-product, and nonnegativity constraints
into one arbitrarily-small nonzero parameter choice.
-/

noncomputable section

open scoped Matrix Topology

open Filter Set Metric

namespace Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity

open Causalean.Discovery.LinearDisentanglement.Quantitative

private theorem posDef_eventually_of_continuousAt {d : ℕ}
    (f : ℝ → SqMatrix d) (hf : ContinuousAt f 0) (h0 : (f 0).PosDef)
    (hherm : ∀ t, (f t).IsHermitian) :
    ∀ᶠ t in nhds 0, (f t).PosDef := by
  let S : Set (Fin d → ℝ) := Metric.sphere 0 1
  let q : ℝ → (Fin d → ℝ) → ℝ := fun t x ↦
    dotProduct x (f t *ᵥ x)
  have hcompact : IsCompact S := isCompact_sphere _ _
  have hlocal : ∀ x ∈ S, ∀ᶠ z : ℝ × (Fin d → ℝ) in nhds (0, x),
      0 < q z.1 z.2 := by
    intro x hx
    have hfcomp : ContinuousAt (fun z : ℝ × (Fin d → ℝ) ↦ f z.1) (0, x) := by
      simpa [Function.comp_def] using hf.comp_of_eq continuousAt_fst rfl
    have hpair : ContinuousAt
        (fun z : ℝ × (Fin d → ℝ) ↦ (f z.1, z.2)) (0, x) :=
      hfcomp.prodMk continuousAt_snd
    have hop : Continuous
        (fun p : SqMatrix d × (Fin d → ℝ) ↦
          dotProduct p.2 (p.1 *ᵥ p.2)) :=
      continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
    have hq : ContinuousAt
        (fun z : ℝ × (Fin d → ℝ) ↦ q z.1 z.2) (0, x) := by
      simpa [q, Function.comp_def] using hop.continuousAt.comp hpair
    have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      norm_num at hxnorm
    have hpos : 0 < q 0 x := by
      simp only [q]
      simpa using h0.dotProduct_mulVec_pos hx0
    exact hq.eventually_const_lt hpos
  have hall := hcompact.eventually_forall_of_forall_eventually
    (P := fun t x ↦ 0 < q t x) hlocal
  filter_upwards [hall] with t ht
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hherm t)
  intro x hx
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let y : Fin d → ℝ := ‖x‖⁻¹ • x
  have hynorm : ‖y‖ = 1 := by
    simp [y, norm_smul, hxnorm]
  have hypos : 0 < q t y := ht y (mem_sphere_zero_iff_norm.mpr hynorm)
  have hscale : q t y = ‖x‖⁻¹ ^ 2 * q t x := by
    simp only [q, y, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    ring
  rw [hscale] at hypos
  have hscale_pos : 0 < ‖x‖⁻¹ ^ 2 := sq_pos_of_ne_zero (inv_ne_zero hxnorm)
  have hqx : 0 < q t x := by nlinarith
  simpa [q] using hqx

private theorem continuousAt_deformedInvariant {d : ℕ} (B Ω : SqMatrix d)
    (i j : Fin d) (u v c : ℝ) :
    ContinuousAt (fun t ↦ deformedInvariant B Ω i j u v c t) 0 := by
  classical
  have hR : ContinuousAt (fun t ↦ pairRowNormalizer B i j u v t) 0 := by
    apply continuousAt_pi.mpr
    intro k
    apply continuousAt_pi.mpr
    intro l
    by_cases hkl : k = l
    · subst l
      simp only [pairRowNormalizer, Matrix.diagonal_apply, if_pos]
      by_cases hki : k = i
      · simp [hki, firstNormalizationDenom]
        fun_prop (disch := norm_num)
      · by_cases hkj : k = j
        · have hji : j ≠ i := by
            intro h
            exact hki (hkj.trans h)
          simp [hkj, hji, secondNormalizationDenom]
          fun_prop (disch := norm_num)
        · simpa [hki, hkj] using
            (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (1 : ℝ)) 0)
    · simpa [pairRowNormalizer, hkl] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) 0)
  have hS : ContinuousAt (fun t ↦ pairShear i j u v t) 0 := by
    apply continuousAt_pi.mpr
    intro k
    apply continuousAt_pi.mpr
    intro l
    simp only [pairShear, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  have hT : ContinuousAt
      (fun t ↦ normalizedPairDeformation B i j u v t) 0 := by
    unfold normalizedPairDeformation
    exact hR.mul hS
  have hC : ContinuousAt
      (fun t ↦ commonShiftCrossTerm B i j u v c t) 0 := by
    unfold commonShiftCrossTerm firstNormalizationDenom secondNormalizationDenom
    fun_prop (disch := norm_num)
  have hE : ContinuousAt
      (fun t ↦ pairSymmetricOffDiagonal i j
        (commonShiftCrossTerm B i j u v c t)) 0 := by
    apply continuousAt_pi.mpr
    intro k
    apply continuousAt_pi.mpr
    intro l
    simp only [pairSymmetricOffDiagonal, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  have hTT : ContinuousAt
      (fun t ↦ (normalizedPairDeformation B i j u v t).transpose) 0 :=
    (continuous_id.matrix_transpose.continuousAt).comp hT
  unfold deformedInvariant
  exact ((hT.mul continuousAt_const).mul hTT).add hE

private theorem deformedInvariant_isHermitian {d : ℕ} (B Ω : SqMatrix d)
    (i j : Fin d) (hΩ : Ω.PosDef) (u v c t : ℝ) :
    (deformedInvariant B Ω i j u v c t).IsHermitian := by
  classical
  unfold deformedInvariant
  apply Matrix.IsHermitian.add
  · rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Matrix.isHermitian_mul_mul_conjTranspose
      (normalizedPairDeformation B i j u v t) hΩ.isHermitian
  · rw [Matrix.isHermitian_iff_isSymm]
    unfold pairSymmetricOffDiagonal Matrix.IsSymm
    simp [add_comm]

/- Proof guide: `deformedInvariant` is continuous at zero because all matrix operations
are coordinatewise continuous and both scalar inverses have value one at zero.  Combine
that with openness of finite-dimensional positive definiteness (or prove a uniform
quadratic-form margin on the compact unit sphere).  Intersect this radius with elementary
nonvanishing radii for the three polynomial denominators, then choose half of the minimum
with the caller's positive bound. -/

/-- When [the selected coordinates are distinct](hyp:hij) and [the original invariant
is positive definite](hyp:hΩ), [some positive radius keeps every transformed invariant
positive definite](goal). -/
theorem exists_deformedInvariant_posDef_radius {d : ℕ} (B Ω : SqMatrix d)
    {i j : Fin d} (hij : i ≠ j) (hΩ : Ω.PosDef) (u v c : ℝ) :
    ∃ ρ > 0, ∀ t : ℝ, |t| < ρ →
      (deformedInvariant B Ω i j u v c t).PosDef := by
  have heventually : ∀ᶠ t in nhds 0,
      (deformedInvariant B Ω i j u v c t).PosDef :=
    posDef_eventually_of_continuousAt
      (fun t ↦ deformedInvariant B Ω i j u v c t)
      (continuousAt_deformedInvariant B Ω i j u v c) (by simpa using hΩ)
      (deformedInvariant_isHermitian B Ω i j hΩ u v c)
  rcases Metric.mem_nhds_iff.mp heventually with ⟨ρ, hρ, hball⟩
  refine ⟨ρ, hρ, fun t ht ↦ hball ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using ht

/-- [Some positive radius makes both row-normalization denominators and the selected
shear determinant nonzero](goal). -/
theorem exists_algebraic_admissibility_radius {d : ℕ} (B : SqMatrix d)
    (i j : Fin d) (u v : ℝ) :
    ∃ ρ > 0, ∀ t : ℝ, |t| < ρ →
      firstNormalizationDenom B i j v t ≠ 0 ∧
      secondNormalizationDenom B i j u t ≠ 0 ∧
      1 - t ^ 2 * u * v ≠ 0 := by
  have hfirst : ∀ᶠ t in nhds 0, firstNormalizationDenom B i j v t ≠ 0 := by
    apply ContinuousAt.eventually_ne
    · unfold firstNormalizationDenom
      fun_prop
    · simp [firstNormalizationDenom]
  have hsecond : ∀ᶠ t in nhds 0, secondNormalizationDenom B i j u t ≠ 0 := by
    apply ContinuousAt.eventually_ne
    · unfold secondNormalizationDenom
      fun_prop
    · simp [secondNormalizationDenom]
  have hdet : ∀ᶠ t in nhds 0, 1 - t ^ 2 * u * v ≠ 0 := by
    apply ContinuousAt.eventually_ne
    · fun_prop
    · norm_num
  have hall : ∀ᶠ t in nhds 0,
      firstNormalizationDenom B i j v t ≠ 0 ∧
      secondNormalizationDenom B i j u t ≠ 0 ∧
      1 - t ^ 2 * u * v ≠ 0 := by
    filter_upwards [hfirst, hsecond, hdet] with t ht1 ht2 ht3
    exact ⟨ht1, ht2, ht3⟩
  rcases Metric.mem_nhds_iff.mp hall with ⟨ρ, hρ, hball⟩
  refine ⟨ρ, hρ, fun t ht ↦ hball ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using ht

/-- Given [two distinct selected coordinates](hyp:hij), [a unit-diagonal reference
matrix](hyp:hBdiag), [an invertible reference matrix](hyp:hBunit), [an admissible selected
two-cycle](hyp:hcycle), [a positive-definite invariant](hyp:hΩ), [coordinatewise
nonnegative shifts](hyp:hs), and [a positive requested bound](hyp:hr), [there is a
nonzero deformation parameter below that bound preserving all stated admissibility,
positivity, and nonnegativity properties](goal). -/
theorem exists_small_admissible_parameter {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E] (B Ω : SqMatrix d) {i j : Fin d}
    (hij : i ≠ j) (hBdiag : UnitDiagonal B) (hBunit : IsUnit B.det)
    (hcycle : PairCycleAdmissible B i j) (hΩ : Ω.PosDef)
    (s : E → Fin d → ℝ) (cert : AffineLineCertificate s i j)
    (hs : ∀ e k, 0 ≤ s e k) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ,
      0 < |t| ∧ |t| < r ∧
      firstNormalizationDenom B i j cert.v t ≠ 0 ∧
      secondNormalizationDenom B i j cert.u t ≠ 0 ∧
      1 - t ^ 2 * cert.u * cert.v ≠ 0 ∧
      IsUnit (normalizedPairDeformation B i j cert.u cert.v t).det ∧
      IsUnit (deformedDiagonalizer B i j cert.u cert.v t).det ∧
      UnitDiagonal (deformedDiagonalizer B i j cert.u cert.v t) ∧
      PairCycleAdmissible (deformedDiagonalizer B i j cert.u cert.v t) i j ∧
      deformedDiagonalizer B i j cert.u cert.v t ≠ B ∧
      (deformedInvariant B Ω i j cert.u cert.v cert.c t).PosDef ∧
      ∀ e k, 0 ≤ deformedShift B i j cert.u cert.v t (s e) k := by
  rcases exists_deformedInvariant_posDef_radius B Ω hij hΩ
      cert.u cert.v cert.c with ⟨ρp, hρp, hp⟩
  rcases exists_algebraic_admissibility_radius B i j cert.u cert.v with
    ⟨ρa, hρa, ha⟩
  let δ := min r (min ρp ρa)
  let t := δ / 2
  have hδ : 0 < δ := by
    exact lt_min hr (lt_min hρp hρa)
  have ht_abs : |t| = δ / 2 := by
    rw [abs_of_pos]
    exact div_pos hδ (by norm_num)
  have ht0 : 0 < |t| := by rw [ht_abs]; positivity
  have htr : |t| < r := by
    rw [ht_abs]
    have hδr : δ ≤ r := min_le_left _ _
    linarith
  have htp : |t| < ρp := by
    rw [ht_abs]
    have hδp : δ ≤ ρp := (min_le_right r _).trans (min_le_left _ _)
    linarith
  have hta : |t| < ρa := by
    rw [ht_abs]
    have hδa : δ ≤ ρa := (min_le_right r _).trans (min_le_right _ _)
    linarith
  rcases ha t hta with ⟨hfirst, hsecond, hdet⟩
  have hTunit : IsUnit (normalizedPairDeformation B i j cert.u cert.v t).det :=
    normalizedPairDeformation_isUnit_det B hij hfirst hsecond hdet
  have hB'unit : IsUnit (deformedDiagonalizer B i j cert.u cert.v t).det := by
    rw [deformedDiagonalizer, Matrix.det_mul]
    exact hTunit.mul hBunit
  have hdiag : UnitDiagonal (deformedDiagonalizer B i j cert.u cert.v t) :=
    deformedDiagonalizer_unitDiagonal B hij hBdiag hfirst hsecond
  have hcycle' : PairCycleAdmissible
      (deformedDiagonalizer B i j cert.u cert.v t) i j :=
    deformedDiagonalizer_pairCycleAdmissible B hij hBdiag hcycle
      hfirst hsecond hdet
  have htne : t ≠ 0 := abs_pos.mp ht0
  have hne : deformedDiagonalizer B i j cert.u cert.v t ≠ B :=
    deformedDiagonalizer_ne B hij hBunit cert.normal_ne htne hfirst hsecond
  have hpos : (deformedInvariant B Ω i j cert.u cert.v cert.c t).PosDef :=
    hp t htp
  have hshift : ∀ e k, 0 ≤ deformedShift B i j cert.u cert.v t (s e) k := by
    intro e
    exact deformedShift_nonnegative B hij cert.u cert.v t (s e) (hs e)
  exact ⟨t, ht0, htr, hfirst, hsecond, hdet, hTunit, hB'unit,
    hdiag, hcycle', hne, hpos, hshift⟩

end Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity
