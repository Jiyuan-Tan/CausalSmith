import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmSmoothModel
import Causalean.Experimentation.DesignBased.FiniteDesignMeasure
import Causalean.Stat.Minimax.FiniteKernelBayes

/-!
The measurable Markov-kernel form of the smooth scalar-to-effect-count design.
This is the continuous-mixture input used by the finite posterior Bayes-risk bridge.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Causalean.Experimentation.DesignBased

/-- The smooth kernel effect triple space carries the discrete measurable structure. -/
noncomputable local instance smoothKernelEffectTripleMeasurableSpace (n : ℕ) :
    MeasurableSpace (EffectTriple n) := ⊤
/-- [the smooth kernel effect triple measurable singleton property holds](goal). -/
noncomputable local instance smoothKernelEffectTripleMeasurableSingleton (n : ℕ) :
    MeasurableSingletonClass (EffectTriple n) :=
  ⟨fun _ => MeasurableSet.of_discrete⟩

-- @node: effectTriple_nonempty
/-- [The zero/zero/`n` effect-count triple witnesses nonemptiness.](goal) -/
noncomputable local instance effectTriple_nonempty (n : ℕ) : Nonempty (EffectTriple n) :=
  ⟨⟨⟨⟨0, Nat.zero_lt_succ n⟩,
      ⟨⟨0, Nat.zero_lt_succ n⟩, ⟨n, Nat.lt_succ_self n⟩⟩⟩, by simp⟩⟩

-- @node: twoArmSmoothEffectDesign_p_measurable
/-- [the first arm count satisfies its stated condition](hyp:ha0), [the second arm count satisfies its stated condition](hyp:ha1), [Every effect-count atom of the clamped smooth response design depends measurably on the scalar parameter.](goal) -/
lemma twoArmSmoothEffectDesign_p_measurable {n : ℕ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (e : EffectTriple n) :
    Measurable (fun θ : ℝ => (twoArmSmoothEffectDesign n a θ ha0 ha1).p e) := by
  unfold twoArmSmoothEffectDesign
  simp only [FiniteDesign.map_p, prodDesign_p, twoArmSmoothResponseTypeDesign,
    twoArmClampedParameter]
  apply Finset.measurable_sum
  intro r _hr
  by_cases h : responseVectorEffectTriple r = e
  · simp only [h, if_true]
    apply Finset.measurable_prod
    intro i _hi
    cases h0 : (r i).1 <;> cases h1 : (r i).2 <;> simp [h0, h1] <;> fun_prop
  · simp [h]

-- @node: twoArmSmoothEffectKernel
/-- The smooth scalar response model as a measurable Markov kernel into finite
effect-class counts.  Clamping makes it a probability kernel for every real parameter. -/
noncomputable def twoArmSmoothEffectKernel (n : ℕ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : Kernel ℝ (EffectTriple n) where
  toFun θ := (twoArmSmoothEffectDesign n a θ ha0 ha1).toMeasure
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s _hs
    simp only [FiniteDesign.toMeasure_apply]
    apply Finset.measurable_sum
    intro e _he
    apply Measurable.mul_const
    exact ENNReal.measurable_ofReal.comp
      (twoArmSmoothEffectDesign_p_measurable ha0 ha1 e)

/-- The two arm smooth effect kernel construction is a Markov kernel. -/
noncomputable instance twoArmSmoothEffectKernel_isMarkovKernel
    (n : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IsMarkovKernel (twoArmSmoothEffectKernel n a ha0 ha1) := by
  refine ⟨?_⟩
  intro θ
  change IsProbabilityMeasure (twoArmSmoothEffectDesign n a θ ha0 ha1).toMeasure
  infer_instance

-- @node: twoArmSmoothEffectKernel_apply
/-- [the first arm count satisfies its stated condition](hyp:ha0), [the second arm count satisfies its stated condition](hyp:ha1), [At a fixed scalar parameter, the smooth effect kernel is exactly the measure induced by the paper-local finite effect-count design.](goal) -/
lemma twoArmSmoothEffectKernel_apply (n : ℕ) (a θ : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    twoArmSmoothEffectKernel n a ha0 ha1 θ =
      (twoArmSmoothEffectDesign n a θ ha0 ha1).toMeasure := rfl

-- @node: twoArmSmoothEffectKernel_singletonReal
/-- [the first arm count satisfies its stated condition](hyp:ha0), [the second arm count satisfies its stated condition](hyp:ha1), [Singleton masses of the smooth effect kernel are the corresponding finite-design masses.](goal) -/
lemma twoArmSmoothEffectKernel_singletonReal (n : ℕ) (a θ : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (e : EffectTriple n) :
    (twoArmSmoothEffectKernel n a ha0 ha1 θ).real {e} =
      (twoArmSmoothEffectDesign n a θ ha0 ha1).p e := by
  classical
  change (twoArmSmoothEffectDesign n a θ ha0 ha1).toMeasure.real {e} = _
  rw [show ({e} : Set (EffectTriple n)) = {x | x = e} by ext; simp]
  rw [FiniteDesign.toMeasure_real_setOf]
  unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
  simp

-- @node: inducedFiniteDesign_twoArmSmoothEffect_p
/-- [the first arm count satisfies its stated condition](hyp:ha0), [the second arm count satisfies its stated condition](hyp:ha1), [The prior-induced finite effect-count design has the expected atomwise mixture formula.](goal) -/
lemma inducedFiniteDesign_twoArmSmoothEffect_p (n : ℕ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (π : Measure ℝ) [IsProbabilityMeasure π]
    (e : EffectTriple n) :
    (Causalean.Stat.inducedFiniteDesign π
      (twoArmSmoothEffectKernel n a ha0 ha1)).p e =
      ∫ θ, (twoArmSmoothEffectDesign n a θ ha0 ha1).p e ∂π := by
  unfold Causalean.Stat.inducedFiniteDesign
  simp_rw [twoArmSmoothEffectKernel_singletonReal]

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
