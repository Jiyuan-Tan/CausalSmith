module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic

/-!
# A fixed prefix of a finite Poisson sample

The finite Poisson experiment can be read as a fixed-length array by using a
common fallback observation when its random count is too small. This module
isolates the exact pushforward law needed for fixed-sample comparisons.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory ProbabilityTheory
open Set
open scoped ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Read the first `n` observations of a finite sample, returning the
constant `x₀` array when its count is less than `n`. -/
def finitePoissonPrefix {X : Type*} [MeasurableSpace X]
    (x₀ : X) (n : ℕ) (s : FiniteSample X) : Fin n → X :=
  if h : n ≤ s.count then fun i => s.points (Fin.castLE h i)
  else fun _ => x₀

/-- The padded fixed prefix is a measurable function of the finite sample. -/
@[fun_prop] theorem measurable_finitePoissonPrefix {X : Type*} [MeasurableSpace X]
    (x₀ : X) (n : ℕ) :
    Measurable (finitePoissonPrefix x₀ n : FiniteSample X → Fin n → X) := by
  intro t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet ((fun x : Fin m → X =>
    if h : n ≤ m then fun i : Fin n => x (Fin.castLE h i)
    else fun _ => x₀) ⁻¹' t)
  by_cases h : n ≤ m
  · simp only [dif_pos h]
    exact ht.preimage (by fun_prop)
  · simp only [dif_neg h]
    exact measurable_const ht

private lemma map_prefixCoordinates_pi {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    {n m : ℕ} (h : n ≤ m) :
    Measure.map (fun x : Fin m → X => fun i : Fin n => x (Fin.castLE h i))
      (Measure.pi (fun _ : Fin m => P)) = Measure.pi (fun _ : Fin n => P) := by
  classical
  let p : Fin m → Prop := fun i => i.val < n
  let e : Subtype p ≃ Fin n :=
    { toFun := fun i => ⟨i.1.val, i.2⟩
      invFun := fun i => ⟨Fin.castLE h i, i.isLt⟩
      left_inv := by intro i; apply Subtype.ext; apply Fin.ext; rfl
      right_inv := by intro i; apply Fin.ext; rfl }
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin m => P) p
  have hfst :
      MeasurePreserving
        (fun x : Fin m → X =>
          ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => X) p) x).1)
        (Measure.pi (fun _ : Fin m => P))
        (Measure.pi (fun _ : Subtype p => P)) :=
    measurePreserving_fst.comp hsplit
  have hreindex :
      MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n => X) e)
        (Measure.pi (fun _ : Subtype p => P))
        (Measure.pi (fun _ : Fin n => P)) :=
    measurePreserving_piCongrLeft (fun _ : Fin n => P) e
  have hc := hreindex.comp hfst
  rw [← hc.map_eq]
  congr 1

/-- Given [a measurable outcome space](hyp:X), [a probability law](hyp:P), [a Poisson mean](hyp:lam), [a fallback outcome](hyp:x₀), and [a prefix length](hyp:n), [the padded Poisson prefix law splits into the fixed iid law and the fallback law according to the count tail](goal). -/
theorem finitePoissonSampleLaw_map_prefix {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (x₀ : X) (n : ℕ) :
    Measure.map (finitePoissonPrefix x₀ n) (finitePoissonSampleLaw P lam) =
      (poissonMeasure lam) (Set.Ici n) •
          Measure.pi (fun _ : Fin n => P) +
        (poissonMeasure lam) (Set.Iio n) •
          Measure.dirac (fun _ : Fin n => x₀) := by
  let μ := finitePoissonSampleLaw P lam
  let good : Set (FiniteSample X) := FiniteSample.count ⁻¹' Set.Ici n
  let bad : Set (FiniteSample X) := FiniteSample.count ⁻¹' Set.Iio n
  have hgood_meas : MeasurableSet good :=
    (by measurability : MeasurableSet (Set.Ici n)).preimage measurable_finiteSample_count
  have hbad_meas : MeasurableSet bad :=
    (by measurability : MeasurableSet (Set.Iio n)).preimage measurable_finiteSample_count
  have hgood : Measure.map (finitePoissonPrefix x₀ n) (μ.restrict good) =
      (poissonMeasure lam) (Set.Ici n) • Measure.pi (fun _ : Fin n => P) := by
    have hdecomp :
        μ.restrict good =
          Measure.sum (fun m : (Set.Ici n : Set ℕ) =>
            μ.restrict (FiniteSample.count ⁻¹' ({m.1} : Set ℕ))) := by
      dsimp [good]
      rw [← Set.biUnion_preimage_singleton]
      exact Measure.restrict_biUnion (Set.to_countable (Set.Ici n))
        (pairwiseDisjoint_fiber FiniteSample.count (Set.Ici n))
        (fun m => measurable_finiteSample_count (measurableSet_singleton m))
    rw [hdecomp, Measure.map_sum (measurable_finitePoissonPrefix x₀ n).aemeasurable]
    simp_rw [show ∀ m : (Set.Ici n : Set ℕ),
        Measure.map (finitePoissonPrefix x₀ n)
            (μ.restrict (FiniteSample.count ⁻¹' ({m.1} : Set ℕ))) =
          (poissonMeasure lam) ({m.1} : Set ℕ) •
            Measure.pi (fun _ : Fin n => P) by
      intro m
      rw [show μ = finitePoissonSampleLaw P lam by rfl,
        finitePoissonSampleLaw_restrict_count_eq, Measure.map_smul,
        Measure.map_map (measurable_finitePoissonPrefix x₀ n)
          (measurable_fixedSizeEmbed m.1)]
      have hfun : finitePoissonPrefix x₀ n ∘ fixedSizeEmbed m.1 =
          fun x : Fin m.1 → X => fun i : Fin n => x (Fin.castLE m.2 i) := by
        have hm : n ≤ m.1 := m.2
        funext x
        funext i
        simp [Function.comp_apply, finitePoissonPrefix, fixedSizeEmbed,
          FiniteSample.count, FiniteSample.points, hm]
      rw [hfun, map_prefixCoordinates_pi P m.2]]
    ext A hA
    simp only [Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.tsum_mul_right]
    congr 1
    simpa using (tsum_measure_preimage_singleton
      (μ := poissonMeasure lam) (s := Set.Ici n) (f := id)
      (Set.to_countable (Set.Ici n))
      (fun m _ => measurableSet_singleton m))
  have hbad : Measure.map (finitePoissonPrefix x₀ n) (μ.restrict bad) =
      (poissonMeasure lam) (Set.Iio n) •
        Measure.dirac (fun _ : Fin n => x₀) := by
    have heq : finitePoissonPrefix x₀ n =ᵐ[μ.restrict bad]
        fun _ => (fun _ : Fin n => x₀) := by
      apply ae_restrict_of_forall_mem hbad_meas
      intro s hs
      have hlt : s.count < n := hs
      simp [finitePoissonPrefix, not_le.mpr hlt]
    rw [Measure.map_congr heq, Measure.map_const]
    congr 1
    rw [Measure.restrict_apply_univ]
    change μ (FiniteSample.count ⁻¹' Set.Iio n) = _
    rw [show μ = finitePoissonSampleLaw P lam by rfl,
      ← finitePoissonSampleLaw_map_count P lam,
      Measure.map_apply measurable_finiteSample_count (by measurability)]
  have hcompl : bad = goodᶜ := by
    ext s
    simp [good, bad]
  change Measure.map (finitePoissonPrefix x₀ n) μ = _
  rw [← (Measure.restrict_add_restrict_compl hgood_meas :
    μ.restrict good + μ.restrict goodᶜ = μ), ← hcompl,
    Measure.map_add _ _ (measurable_finitePoissonPrefix x₀ n),
    hgood, hbad]

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
