module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.RelaxedPoissonBridge

/-! Product-prior factorization for the current marked-Poisson experiment. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open Causalean.Stat.Minimax.MomentMatchedMixture

namespace CausalSmith.Stat.MarRareqLogfrontier

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

end CausalSmith.Stat.MarRareqLogfrontier

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:Θ,X,K,d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def coordinatewiseFiniteKernel
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (K : Kernel Θ X) : (d : ℕ) → Kernel (Fin d → Θ) (Fin d → X)
  | 0 => Kernel.const (Fin 0 → Θ) (Measure.dirac (fun i : Fin 0 => Fin.elim0 i))
  | d + 1 =>
      let lastK := K.comap (fun z : Fin (d + 1) → Θ => z (Fin.last d))
        (measurable_pi_apply _)
      let initK := (coordinatewiseFiniteKernel K d).comap
        (fun z : Fin (d + 1) → Θ => Fin.init z) (by
          exact measurable_pi_iff.2 fun i => measurable_pi_apply i.castSucc)
      (lastK.prod initK).map
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (d + 1) => X) (Fin.last d)).symm

/-- For [the specified inputs and assumptions](hyp:X,K,d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable instance coordinatewiseFiniteKernel_isMarkov
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (K : Kernel Θ X) [IsMarkovKernel K] (d : ℕ) :
    IsMarkovKernel (coordinatewiseFiniteKernel K d) := by
  induction d with
  | zero =>
      unfold coordinatewiseFiniteKernel
      infer_instance
  | succ d ih =>
      letI : IsMarkovKernel (coordinatewiseFiniteKernel K d) := ih
      unfold coordinatewiseFiniteKernel
      exact Kernel.IsMarkovKernel.map _
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (d + 1) => X) (Fin.last d)).symm.measurable

end CausalSmith.Stat.MarRareqLogfrontier

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/-- [the stated mathematical conclusion holds](goal). -/
lemma measurable_poissonMeasure_rate_local :
    Measurable (fun r : NNReal => poissonMeasure r) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [poissonMeasure, Measure.sum_apply _ hs]
  apply Measurable.tsum
  intro k
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  fun_prop

/-- Given [the specified inputs and assumptions](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma measurable_markedPoissonLaw_local (n : ℝ) :
    Measurable (markedPoissonLaw n) := by
  have h₁ : Measurable (fun t : MarkedParam =>
      (⟨poissonMeasure (nnRate (n * t.1 * t.2.1 * t.2.2)), inferInstance⟩ :
        ProbabilityMeasure ℕ)) :=
    Measurable.subtype_mk (measurable_poissonMeasure_rate_local.comp (by
      unfold nnRate
      fun_prop))
  have h₂ : Measurable (fun t : MarkedParam =>
      (⟨poissonMeasure (nnRate (n * t.1 * t.2.1 * (1 - t.2.2))), inferInstance⟩ :
        ProbabilityMeasure ℕ)) :=
    Measurable.subtype_mk (measurable_poissonMeasure_rate_local.comp (by
      unfold nnRate
      fun_prop))
  have h₃ : Measurable (fun t : MarkedParam =>
      (⟨poissonMeasure (nnRate (n * t.1 * (1 - t.2.1))), inferInstance⟩ :
        ProbabilityMeasure ℕ)) :=
    Measurable.subtype_mk (measurable_poissonMeasure_rate_local.comp (by
      unfold nnRate
      fun_prop))
  have h₁₂ : Measurable (fun t : MarkedParam =>
      (⟨(poissonMeasure (nnRate (n * t.1 * t.2.1 * t.2.2))).prod
        (poissonMeasure (nnRate (n * t.1 * t.2.1 * (1 - t.2.2)))), inferInstance⟩ :
          ProbabilityMeasure (ℕ × ℕ))) :=
    Measurable.subtype_mk
      (ProbabilityMeasure.measurable_fun_prod.comp (h₁.prodMk h₂))
  exact ProbabilityMeasure.measurable_fun_prod.comp (h₁₂.prodMk h₃)

/-- For [the specified inputs and assumptions](hyp:n), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def markedPoissonKernel (n : ℝ) :
    Kernel MarkedParam ((ℕ × ℕ) × ℕ) where
  toFun := markedPoissonLaw n
  measurable' := measurable_markedPoissonLaw_local n

/-- For [the specified inputs and assumptions](hyp:n), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable instance markedPoissonKernel_isMarkov (n : ℝ) :
    IsMarkovKernel (markedPoissonKernel n) where
  isProbabilityMeasure t := by
    change IsProbabilityMeasure (markedPoissonLaw n t)
    unfold markedPoissonLaw
    infer_instance

/-- For [the specified inputs and assumptions](hyp:d,a0,lam), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable instance relaxedDummyCountLaw_isProbability
    (d : ℕ) (a0 : ℝ) (lam : ℝ≥0) :
    IsProbabilityMeasure (relaxedDummyCountLaw d a0 lam) := by
  unfold relaxedDummyCountLaw
  infer_instance

end CausalSmith.Stat.MarRareqLogfrontier
