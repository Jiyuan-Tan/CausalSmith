module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.RelaxedSplitReconstruction
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization
-- private import
import all CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.FixedPoissonBridge

/-!
# Marked and unmarked prefix reconstruction

This module proves that ordering independent atomless marks and then reading a
fixed prefix gives exactly the same observation law as reading the prefix of
the uniformly ordered unmarked Poisson sample reconstructed from split counts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

variable {X : Type*} [MeasurableSpace X]

/-- For [the specified inputs and assumptions](hyp:X,x₀,n,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def unmarkedPrefixObservations (x₀ : X) (n : ℕ)
    (s : FiniteSample X) : Fin n → X :=
  if h : n ≤ s.count then fun k => s.points (Fin.castLE h k) else fun _ => x₀

/-- Given [the specified inputs and assumptions](hyp:x₀,n), [the stated mathematical conclusion holds](goal). -/
@[fun_prop] lemma measurable_unmarkedPrefixObservations (x₀ : X) (n : ℕ) :
    Measurable (unmarkedPrefixObservations x₀ n : FiniteSample X → Fin n → X) := by
  unfold unmarkedPrefixObservations
  apply measurable_pi_lambda
  intro k t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet ((fun x : Fin m → X =>
    (if h : n ≤ m then fun k => x (Fin.castLE h k) else fun _ => x₀) k) ⁻¹' t)
  by_cases h : n ≤ m
  · simp only [dif_pos h]
    exact ht.preimage (measurable_pi_apply (Fin.castLE h k))
  · simp only [dif_neg h]
    exact measurable_const ht

private lemma map_finPrefix_pi_unmarked (P : Measure X) [IsProbabilityMeasure P]
    {n m : ℕ} (h : n ≤ m) :
    Measure.map (fun x : Fin m → X => fun k : Fin n => x (Fin.castLE h k))
        (Measure.pi (fun _ : Fin m => P)) =
      Measure.pi (fun _ : Fin n => P) := by
  let p : Fin m → Prop := fun i => i.val < n
  let e : Subtype p ≃ Fin n :=
    { toFun := fun i => ⟨i.1.val, i.2⟩
      invFun := fun k => ⟨Fin.castLE h k, k.isLt⟩
      left_inv := by intro i; apply Subtype.ext; apply Fin.ext; rfl
      right_inv := by intro k; apply Fin.ext; rfl }
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin m => P) p
  have hfst : MeasurePreserving
      (fun x : Fin m → X =>
        ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => X) p) x).1)
      (Measure.pi (fun _ : Fin m => P))
      (Measure.pi (fun _ : Subtype p => P)) :=
    measurePreserving_fst.comp hsplit
  have hreindex : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => X) e)
      (Measure.pi (fun _ : Subtype p => P))
      (Measure.pi (fun _ : Fin n => P)) :=
    measurePreserving_piCongrLeft (fun _ : Fin n => P) e
  have hc := hreindex.comp hfst
  rw [← hc.map_eq]
  congr 1

private lemma map_unmarkedPrefix_fixedSizeEmbed_pi
    (P : Measure X) [IsProbabilityMeasure P]
    (x₀ : X) {n m : ℕ} (h : n ≤ m) :
    Measure.map (unmarkedPrefixObservations x₀ n)
        (Measure.map (fixedSizeEmbed m) (Measure.pi (fun _ : Fin m => P))) =
      Measure.pi (fun _ : Fin n => P) := by
  rw [Measure.map_map (measurable_unmarkedPrefixObservations x₀ n)
    (measurable_fixedSizeEmbed m)]
  have hfun : unmarkedPrefixObservations x₀ n ∘ fixedSizeEmbed m =
      fun x : Fin m → X => fun k : Fin n => x (Fin.castLE h k) := by
    funext x k
    simp only [Function.comp_apply]
    unfold unmarkedPrefixObservations
    rw [dif_pos (show n ≤ (fixedSizeEmbed m x).count from h)]
    rfl
  rw [hfun, map_finPrefix_pi_unmarked P h]

private lemma map_prefix_restrict_count_lt_unmarked
    (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (x₀ : X) (n : ℕ) :
    Measure.map (unmarkedPrefixObservations x₀ n)
      ((finitePoissonSampleLaw P lam).restrict
        (FiniteSample.count ⁻¹' Ici n)ᶜ) =
      (poissonMeasure lam) (Ici n)ᶜ • Measure.dirac (fun _ : Fin n => x₀) := by
  let μ := finitePoissonSampleLaw P lam
  let S : Set (FiniteSample X) := FiniteSample.count ⁻¹' Ici n
  have hS : MeasurableSet S := measurable_finiteSample_count measurableSet_Ici
  calc
    Measure.map (unmarkedPrefixObservations x₀ n) (μ.restrict Sᶜ) =
        Measure.map (fun _ : FiniteSample X => fun _ : Fin n => x₀) (μ.restrict Sᶜ) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hS.compl] with s hs
      unfold unmarkedPrefixObservations
      simp only [S, Set.mem_compl_iff, Set.mem_preimage, Set.mem_Ici] at hs
      simp [not_le.mp hs]
    _ = μ Sᶜ • Measure.dirac (fun _ : Fin n => x₀) := by
      rw [Measure.map_const, Measure.restrict_apply_univ]
    _ = (poissonMeasure lam) (Ici n)ᶜ • Measure.dirac (fun _ : Fin n => x₀) := by
      congr 1
      have hc := finitePoissonSampleLaw_map_count P lam
      rw [← hc, Measure.map_apply measurable_finiteSample_count measurableSet_Ici.compl]
      rfl

private lemma map_prefix_restrict_count_lt_marked
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    (lam : ℝ≥0) (x₀ : X) (n : ℕ) :
    Measure.map (canonicalPrefixObservations x₀ n)
      ((canonicalMarkedPoissonSampleLaw P R lam).restrict
        (FiniteSample.count ⁻¹' Ici n)ᶜ) =
      (poissonMeasure lam) (Ici n)ᶜ • Measure.dirac (fun _ : Fin n => x₀) := by
  let μ := canonicalMarkedPoissonSampleLaw P R lam
  let S : Set (FiniteSample (X × ℝ)) := FiniteSample.count ⁻¹' Ici n
  have hS : MeasurableSet S := measurable_finiteSample_count measurableSet_Ici
  calc
    Measure.map (canonicalPrefixObservations x₀ n) (μ.restrict Sᶜ) =
        Measure.map (fun _ : FiniteSample (X × ℝ) => fun _ : Fin n => x₀) (μ.restrict Sᶜ) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hS.compl] with s hs
      unfold canonicalPrefixObservations
      simp only [S, Set.mem_compl_iff, Set.mem_preimage, Set.mem_Ici] at hs
      simp [not_le.mp hs]
    _ = μ Sᶜ • Measure.dirac (fun _ : Fin n => x₀) := by
      rw [Measure.map_const, Measure.restrict_apply_univ]
    _ = (poissonMeasure lam) (Ici n)ᶜ • Measure.dirac (fun _ : Fin n => x₀) := by
      congr 1
      have hc := canonicalMarkedPoissonSampleLaw_map_count P R lam
      rw [← hc, Measure.map_apply measurable_finiteSample_count measurableSet_Ici.compl]
      rfl

/-- For [the specified inputs and assumptions](hyp:t), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def relaxedZengClip (t : ℝ) : ℝ := max (-1) (min 1 t)

/-- [the stated mathematical conclusion holds](goal). -/
@[fun_prop] lemma measurable_relaxedZengClip : Measurable relaxedZengClip := by
  unfold relaxedZengClip
  fun_prop

/-- For [the specified inputs and assumptions](hyp:n,d,T,x₀), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def unmarkedPrefixDecisionKernel {n d : ℕ}
    (T : ZengEstimator n (d + 1)) (x₀ : RelaxedZengRecord d) :
    Kernel (FiniteSample (RelaxedZengRecord d)) ℝ :=
  T.1 ∘ₖ Kernel.deterministic (unmarkedPrefixObservations x₀ n)
    (measurable_unmarkedPrefixObservations x₀ n)

/-- For [the specified inputs and assumptions](hyp:n,d,T,x₀), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
instance unmarkedPrefixDecisionKernel_isMarkov {n d : ℕ}
    (T : ZengEstimator n (d + 1)) (x₀ : RelaxedZengRecord d) :
    IsMarkovKernel (unmarkedPrefixDecisionKernel T x₀) := by
  letI : IsMarkovKernel T.1 := T.2.1
  unfold unmarkedPrefixDecisionKernel
  infer_instance

/-- For [the specified inputs and assumptions](hyp:n,d,T,x₀), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def relaxedCountPrefixEstimator {n d : ℕ}
    (T : ZengEstimator n (d + 1)) (x₀ : RelaxedZengRecord d) :
    (((ℕ × ℕ) × ℕ) × (Fin d → ((ℕ × ℕ) × ℕ))) → ℝ :=
  Causalean.Stat.kernelMean
    (unmarkedPrefixDecisionKernel T x₀ ∘ₖ relaxedSplitReconstructionKernel d)
    relaxedZengClip

/-- Given [the specified inputs and assumptions](hyp:n,d,T,x₀), [the stated mathematical conclusion holds](goal). -/
@[fun_prop] theorem measurable_relaxedCountPrefixEstimator {n d : ℕ}
    (T : ZengEstimator n (d + 1)) (x₀ : RelaxedZengRecord d) :
    Measurable (relaxedCountPrefixEstimator T x₀) := by
  exact Causalean.Stat.measurable_kernelMean _ measurable_relaxedZengClip

end CausalSmith.Stat.MarRareqLogfrontier
