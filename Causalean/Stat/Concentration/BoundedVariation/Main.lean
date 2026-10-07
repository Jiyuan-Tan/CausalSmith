module
public import Causalean.Stat.Concentration.BoundedVariation.CopySigns
public import Causalean.Stat.Concentration.BoundedVariation.EnvelopeAlgebra
public import Causalean.Stat.Concentration.BoundedVariation.Rademacher
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The bounded-variation process maximal inequality

Independent continuous bounded-variation random paths admit a universal
second-moment bound for the supremum of their centered sum. The theorem uses
the full time continuum and has no dimension or grid-size factor.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.Concentration.BoundedVariation

/-- For finitely many random continuous paths on the unit interval that
are [measurable](hyp:hWmeas), [Bochner-integrable](hyp:hWint), [almost
surely of bounded variation](hyp:hBV), [with integrable squared
supremum-plus-variation size](hyp:hMom), and [mutually
independent](hyp:hind), [the expected squared supremum norm of their
centered sum is at most 16384 times the sum of their expected squared
sizes](goal).

The supremum ranges over the full time continuum; the bound has no
dimension or grid-size factor.
-/
theorem centered_path_sum_maximal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (W : Fin n → Ω → Path)
    (hWmeas : ∀ j, Measurable (W j))
    (hWint : ∀ j, Integrable (W j) μ)
    (hBV : ∀ j, ∀ᵐ ω ∂μ, eVariationOn (W j ω) Set.univ < ⊤)
    (hMom : ∀ j, Integrable (fun ω => (pathSize (W j ω)) ^ 2) μ)
    (hind : iIndepFun W μ) :
    (∫ ω, ‖∑ j, (W j ω - ∫ x, W j x ∂μ)‖ ^ 2 ∂μ) ≤
      16384 * ∑ j, (∫ ω, (pathSize (W j ω)) ^ 2 ∂μ) := by
  classical
  let : BorelSpace Path := ⟨rfl⟩
  let A (j : Fin n) (ω : Ω) : ℝ := (pathSize (W j ω)) ^ 2
  let B (ω ω' : Ω) : ℝ := ∑ j, (A j ω + A j ω')
  have hAmeas (j : Fin n) : Measurable (A j) := by
    unfold A pathSize
    exact (((continuous_norm.measurable.comp (hWmeas j)).add
      (measurable_pathTV.comp (hWmeas j))).pow_const 2)
  have hAint (j : Fin n) : Integrable (A j) μ :=
    ⟨(hAmeas j).aestronglyMeasurable, (hMom j).hasFiniteIntegral⟩
  have hWsq (j : Fin n) : Integrable (fun ω => ‖W j ω‖ ^ 2) μ := by
    apply Integrable.mono' (hMom j) (by fun_prop)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖W j ω‖ ^ 2 ≤ A j ω
    have hle : ‖W j ω‖ ≤ pathSize (W j ω) := by
      simp only [pathSize]
      exact le_add_of_nonneg_right (pathTV_nonneg _)
    exact (sq_le_sq₀ (norm_nonneg _) (pathSize_nonneg _)).mpr hle
  have hBVall : ∀ᵐ ω ∂μ, ∀ j, eVariationOn (W j ω) Set.univ < ⊤ :=
    ae_all_iff.mpr hBV
  have hBint (ω : Ω) : Integrable (B ω) μ := by
    unfold B
    exact integrable_finsetSum (Finset.univ : Finset (Fin n))
      (fun j _ => (integrable_const (A j ω)).add (hAint j))
  have hBouter : Integrable (fun ω => ∫ ω', B ω ω' ∂μ) μ := by
    have hBprod : Integrable (fun p : Ω × Ω => B p.1 p.2) (μ.prod μ) := by
      unfold B
      exact integrable_finsetSum (Finset.univ : Finset (Fin n))
        (fun j _ => (Integrable.comp_fst (hAint j) μ).add
          (Integrable.comp_snd (hAint j) μ))
    exact hBprod.integral_prod_left
  have hpoint (ω ω' : Ω)
      (hω : ∀ j, eVariationOn (W j ω) Set.univ < ⊤)
      (hω' : ∀ j, eVariationOn (W j ω') Set.univ < ⊤) :
      rademacherEnergy (fun j => W j ω - W j ω') ≤ 8192 * B ω ω' := by
    have hdiff : ∀ j, eVariationOn (W j ω - W j ω') Set.univ < ⊤ := by
      intro j
      exact lt_of_le_of_lt (eVariationOn_path_sub_le _ _)
        (ENNReal.add_lt_top.mpr ⟨hω j, hω' j⟩)
    calc
      rademacherEnergy (fun j => W j ω - W j ω') ≤
          4096 * ∑ j, (pathSize (W j ω - W j ω')) ^ 2 :=
        rademacherEnergy_le_pathSize_sq _ hdiff
      _ ≤ 8192 * B ω ω' := by
        unfold B
        have hsum : (∑ j, (pathSize (W j ω - W j ω')) ^ 2) ≤
            2 * ∑ j, (A j ω + A j ω') := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro j _
          have hsub := pathSize_sub_le (W j ω) (W j ω') (hω j) (hω' j)
          have hnonneg := pathSize_nonneg (W j ω - W j ω')
          have ha := pathSize_nonneg (W j ω)
          have hb := pathSize_nonneg (W j ω')
          dsimp [A]
          nlinarith [sq_nonneg (pathSize (W j ω) - pathSize (W j ω'))]
        nlinarith
  have hsign_nonneg (ω ω' : Ω) :
      0 ≤ rademacherEnergy (fun j => W j ω - W j ω') := by
    unfold rademacherEnergy
    exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  have hinner (ω : Ω) (hω : ∀ j, eVariationOn (W j ω) Set.univ < ⊤) :
      (∫ ω', rademacherEnergy (fun j => W j ω - W j ω') ∂μ) ≤
        8192 * ∫ ω', B ω ω' ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (hsign_nonneg ω)
    · exact (hBint ω).const_mul _
    · filter_upwards [hBVall] with ω' hω'
      exact hpoint ω ω' hω hω'
  have houter :
      (∫ ω, ∫ ω', rademacherEnergy (fun j => W j ω - W j ω') ∂μ ∂μ) ≤
        8192 * ∫ ω, ∫ ω', B ω ω' ∂μ ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun ω => integral_nonneg fun ω' => hsign_nonneg ω ω'
    · exact hBouter.const_mul _
    · filter_upwards [hBVall] with ω hω
      exact hinner ω hω
  have hBvalue : (∫ ω, ∫ ω', B ω ω' ∂μ ∂μ) =
      2 * ∑ j, (∫ ω, A j ω ∂μ) := by
    have hinnerB (ω : Ω) : (∫ ω', B ω ω' ∂μ) =
        ∑ j, (A j ω + ∫ ω', A j ω' ∂μ) := by
      change (∫ ω', ∑ j, (A j ω + A j ω') ∂μ) = _
      rw [integral_finsetSum (Finset.univ : Finset (Fin n))]
      · congr 1
        ext j
        rw [integral_add (integrable_const _) (hAint j)]
        simp [A]
      · intro j _
        exact (integrable_const _).add (hAint j)
    simp_rw [hinnerB]
    rw [integral_finsetSum (Finset.univ : Finset (Fin n))]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_add (hAint j) (integrable_const _)]
      simp [A]
      ring
    · intro j _
      exact (hAint j).add (integrable_const _)
  calc
    (∫ ω, ‖∑ j, (W j ω - ∫ x, W j x ∂μ)‖ ^ 2 ∂μ) ≤
        ∫ ω, ∫ ω', ‖∑ j, (W j ω - W j ω')‖ ^ 2 ∂μ ∂μ :=
      centered_path_sum_energy_le_copy μ W hWint hWsq
    _ = ∫ ω, ∫ ω', rademacherEnergy (fun j => W j ω - W j ω') ∂μ ∂μ :=
      independent_copy_difference_energy_eq_sign_energy μ W hWmeas hWsq hind
    _ ≤ 8192 * ∫ ω, ∫ ω', B ω ω' ∂μ ∂μ := houter
    _ = 16384 * ∑ j, (∫ ω, (pathSize (W j ω)) ^ 2 ∂μ) := by
      rw [hBvalue]
      dsimp [A]
      ring

end Causalean.Stat.Concentration.BoundedVariation
