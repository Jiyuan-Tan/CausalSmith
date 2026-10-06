module
public import Causalean.Stat.Concentration.BoundedVariation.CopyJensen
public import Causalean.Stat.Concentration.BoundedVariation.CopySwap
public import Causalean.Stat.Concentration.BoundedVariation.SignedChaining
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Sign symmetry of independent path differences

The differences between an independent finite family of paths and a product
copy have the same joint law after any fixed coordinatewise sign reversal.
Consequently their squared sum energy equals their averaged signed energy.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.Concentration.BoundedVariation

/-- For finitely many random continuous paths that are
[measurable](hyp:hWmeas), [have integrable squared supremum
norm](hyp:hWsq), and [are mutually independent](hyp:hind), [the expected
squared supremum norm of the summed differences between two independent
draws equals the expected Rademacher energy (sign-averaged squared supremum
norm) of those differences](goal).
-/
theorem independent_copy_difference_energy_eq_sign_energy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (W : Fin n → Ω → Path)
    (hWmeas : ∀ j, Measurable (W j))
    (hWsq : ∀ j, Integrable (fun ω => ‖W j ω‖ ^ 2) μ)
    (hind : iIndepFun W μ) :
    (∫ ω, ∫ ω', ‖∑ j, (W j ω - W j ω')‖ ^ 2 ∂μ ∂μ) =
      ∫ ω, ∫ ω', rademacherEnergy (fun j => W j ω - W j ω') ∂μ ∂μ := by
  /- Under the product-copy law, the pairs `(W_j,W'_j)` are independent
  across j. Swapping the two entries in any subset of pairs preserves the
  law, and reverses exactly those difference signs. Average the resulting
  equalities over all Boolean sign vectors. Apply
  `independent_copy_difference_map_sign_invariant` to the measurable
  squared-norm-of-sum function, convert product integrals to iterated
  integrals, then commute the finite sign sum with the integral. The
  second-moment assumptions justify the integrals and finite averaging. -/
  classical
  let : BorelSpace Path := ⟨rfl⟩
  let D : Ω × Ω → Fin n → Path := fun p j => W j p.1 - W j p.2
  let F : (Fin n → Path) → ℝ := fun w => ‖∑ j, w j‖ ^ 2
  let G : (Fin n → Bool) → Ω × Ω → ℝ := fun σ p =>
    ‖∑ j, (if σ j then (1 : ℝ) else -1) • D p j‖ ^ 2
  have hDm : Measurable D := by
    apply measurable_pi_iff.mpr
    intro j
    exact ((hWmeas j).comp measurable_fst).sub ((hWmeas j).comp measurable_snd)
  have hFm : Measurable F := by
    unfold F
    fun_prop
  have hGm (σ : Fin n → Bool) : Measurable (G σ) := by
    unfold G
    fun_prop
  have hDLp (j : Fin n) : MemLp (fun p : Ω × Ω => D p j) 2 (μ.prod μ) := by
    have h1 : MemLp (fun p : Ω × Ω => W j p.1) 2 (μ.prod μ) :=
      (memLp_two_iff_integrable_sq_norm
        (AEStronglyMeasurable.comp_fst (hWmeas j).aestronglyMeasurable)).mpr
        (Integrable.comp_fst (hWsq j) μ)
    have h2 : MemLp (fun p : Ω × Ω => W j p.2) 2 (μ.prod μ) :=
      (memLp_two_iff_integrable_sq_norm
        (AEStronglyMeasurable.comp_snd (hWmeas j).aestronglyMeasurable)).mpr
        (Integrable.comp_snd (hWsq j) μ)
    exact h1.sub h2
  have hDj (j : Fin n) : Measurable (fun p : Ω × Ω => D p j) :=
    (measurable_pi_apply j).comp hDm
  have hDsq (j : Fin n) : Integrable (fun p : Ω × Ω => ‖D p j‖ ^ 2)
      (μ.prod μ) :=
    (memLp_two_iff_integrable_sq_norm (hDj j).aestronglyMeasurable).mp (hDLp j)
  have hnegm (j : Fin n) : Measurable (fun p : Ω × Ω => -D p j) := by
    convert (hDj j).neg using 1
    funext p
    rfl
  have hnegLp (j : Fin n) : MemLp (fun p : Ω × Ω => -D p j) 2 (μ.prod μ) := by
    apply (memLp_two_iff_integrable_sq_norm (hnegm j).aestronglyMeasurable).mpr
    simpa only [norm_neg] using hDsq j
  have hGLp (σ : Fin n → Bool) :
      MemLp (fun p => ∑ j, (if σ j then (1 : ℝ) else -1) • D p j)
        2 (μ.prod μ) := by
    apply memLp_finsetSum (Finset.univ : Finset (Fin n))
    intro j hj
    by_cases hs : σ j
    · simpa [hs] using hDLp j
    · simpa [hs] using hnegLp j
  have hGi (σ : Fin n → Bool) : Integrable (G σ) (μ.prod μ) := by
    exact (memLp_two_iff_integrable_sq_norm
      (show AEStronglyMeasurable
        (fun p => ∑ j, (if σ j then (1 : ℝ) else -1) • D p j) (μ.prod μ) by
          fun_prop)).mp (hGLp σ)
  have hFi : Integrable (F ∘ D) (μ.prod μ) := by
    convert hGi (fun _ => true) using 1
    funext p
    simp only [F, G, Function.comp_apply, if_true, one_smul]
  have hsign (σ : Fin n → Bool) :
      (∫ p, F (D p) ∂(μ.prod μ)) = ∫ p, G σ p ∂(μ.prod μ) := by
    have hlaw := independent_copy_difference_map_sign_invariant μ W hWmeas hind σ
    have hmap : (μ.prod μ).map D =
        (μ.prod μ).map (fun p : Ω × Ω => fun j : Fin n =>
          if σ j then D p j else -D p j) := by
      convert hlaw using 1
      congr 1
      funext p j
      by_cases hs : σ j <;> simp [D, hs, sub_eq_add_neg]
    have hm : Measurable (fun p : Ω × Ω => fun j : Fin n =>
        if σ j then D p j else -D p j) := by
      apply measurable_pi_iff.mpr
      intro j
      by_cases hs : σ j
      · simpa [hs] using hDj j
      · simpa [hs] using hnegm j
    calc
      (∫ p, F (D p) ∂(μ.prod μ)) = ∫ w, F w ∂((μ.prod μ).map D) :=
        (integral_map hDm.aemeasurable hFm.aestronglyMeasurable).symm
      _ = ∫ w, F w ∂((μ.prod μ).map (fun p : Ω × Ω => fun j : Fin n =>
          if σ j then D p j else -D p j)) := by rw [hmap]
      _ = ∫ p, G σ p ∂(μ.prod μ) := by
        rw [integral_map hm.aemeasurable hFm.aestronglyMeasurable]
        congr 1
        funext p
        simp only [F, G]
        have heq : (∑ j, if σ j then D p j else -D p j) =
            ∑ j, (if σ j then (1 : ℝ) else -1) • D p j := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hs : σ j <;> simp [hs]
        rw [heq]
  have hEi : Integrable (fun p : Ω × Ω => rademacherEnergy (D p)) (μ.prod μ) := by
    unfold rademacherEnergy
    exact (integrable_finsetSum (Finset.univ : Finset (Fin n → Bool))
      (fun σ _ => hGi σ)).div_const _
  have hprod : (∫ p, F (D p) ∂(μ.prod μ)) =
      ∫ p, rademacherEnergy (D p) ∂(μ.prod μ) := by
    rw [show (∫ p, rademacherEnergy (D p) ∂(μ.prod μ)) =
        (∑ σ : Fin n → Bool, ∫ p, G σ p ∂(μ.prod μ)) / (2 ^ n : ℝ) by
      change (∫ p, (∑ σ : Fin n → Bool, G σ p) / (2 ^ n : ℝ) ∂(μ.prod μ)) = _
      rw [integral_div, integral_finsetSum (Finset.univ : Finset (Fin n → Bool))
        (fun σ _ => hGi σ)]]
    simp only [← hsign]
    simp [Fintype.card_bool]
  calc
    (∫ ω, ∫ ω', ‖∑ j, (W j ω - W j ω')‖ ^ 2 ∂μ ∂μ) =
        ∫ p, F (D p) ∂(μ.prod μ) := by
          change (∫ ω, ∫ ω', (F ∘ D) (ω, ω') ∂μ ∂μ) =
            ∫ p, (F ∘ D) p ∂(μ.prod μ)
          exact (integral_prod _ hFi).symm
    _ = ∫ p, rademacherEnergy (D p) ∂(μ.prod μ) := hprod
    _ = ∫ ω, ∫ ω', rademacherEnergy (fun j => W j ω - W j ω') ∂μ ∂μ := by
          simpa only [D] using (integral_prod _ hEi)

end Causalean.Stat.Concentration.BoundedVariation
