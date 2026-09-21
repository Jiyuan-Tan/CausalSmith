module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepthObservedChain
public import Causalean.Mathlib.InformationTheory.KLBind

set_option linter.style.longLine false

/-! # Conditional signed-depth KL factorization -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- A two-point law parameterized by its signed mean. -/
noncomputable def signedMeanPMF (m : ℝ) : PMF Bool :=
  pmfOfRealWeight fun r ↦ (1 + signedValue r * m) / 2

/-- The common-behavior conditional observed-symbol law. -/
noncomputable def signedDepthConditionalEpochPMF (zeta m : ℝ) :
    PMF (Fin 1 × Bool × Fin 2) :=
  pmfOfRealWeight fun x ↦ signedDepthBehaviourWeight zeta x.2.1 *
    (1 + signedValue (finTwoEquiv x.2.2) * m) / 2

/-- Assuming [the hm condition](hyp:hm), [the signed Mean PMF to Real assertion holds](goal). -/
lemma signedMeanPMF_toReal {m : ℝ} (hm : |m| < 1) (r : Bool) :
    (signedMeanPMF m r).toReal = (1 + signedValue r * m) / 2 := by
  have hn : ∀ r : Bool, 0 ≤ (1 + signedValue r * m) / 2 := by
    intro r
    cases r <;> simp [signedValue] <;> linarith [abs_lt.mp hm |>.1, abs_lt.mp hm |>.2]
  have hs : ∑ r : Bool, (1 + signedValue r * m) / 2 = 1 := by
    simp [signedValue]
    ring
  rw [signedMeanPMF, pmfOfRealWeight_apply_of_nonneg_sum_one _ hn hs,
    ENNReal.toReal_ofReal (hn r)]

/-- Assuming [the hzeta condition](hyp:hzeta), [the hm condition](hyp:hm), [the signed Depth Conditional Epoch PMF to Real assertion holds](goal). -/
lemma signedDepthConditionalEpochPMF_toReal {zeta m : ℝ}
    (hzeta : 0 < zeta) (hm : |m| < 1) (x : Fin 1 × Bool × Fin 2) :
    (signedDepthConditionalEpochPMF zeta m x).toReal =
      signedDepthBehaviourWeight zeta x.2.1 *
        (1 + signedValue (finTwoEquiv x.2.2) * m) / 2 := by
  let q : Fin 1 × Bool × Fin 2 → ℝ := fun x ↦ signedDepthBehaviourWeight zeta x.2.1 *
    (1 + signedValue (finTwoEquiv x.2.2) * m) / 2
  have hq : ∀ x, 0 ≤ q x := by
    intro x
    dsimp [q]
    apply div_nonneg
    apply mul_nonneg (signedDepthBehaviourWeight_nonneg hzeta x.2.1)
    rcases x with ⟨x, a, r⟩
    fin_cases r <;> simp [finTwoEquiv, signedValue] <;>
      linarith [abs_lt.mp hm |>.1, abs_lt.mp hm |>.2]
    norm_num
  have hs : ∑ x, q x = 1 := by
    simp only [q, Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
    simp [finTwoEquiv, signedValue]
    calc
      _ = signedDepthBehaviourWeight zeta false +
          signedDepthBehaviourWeight zeta true := by ring
      _ = ∑ a : Bool, signedDepthBehaviourWeight zeta a := by
        rw [Fintype.sum_bool]
        ring
      _ = 1 := sum_signedDepthBehaviourWeight zeta
  change (pmfOfRealWeight q x).toReal = q x
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one q hq hs,
    ENNReal.toReal_ofReal (hq x)]

/-- Reorder reward and action bits into the observed triple. -/
def signedDepthEpochEquiv : Bool × Bool ≃ Fin 1 × Bool × Fin 2 where
  toFun z := (0, z.2, finTwoEquiv.symm z.1)
  invFun z := (finTwoEquiv z.2.2, z.2.1)
  left_inv z := by cases z with | mk r a => cases r <;> rfl
  right_inv z := by
    rcases z with ⟨x, a, r⟩
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · apply Prod.ext
      · rfl
      · exact finTwoEquiv.symm_apply_apply r

/-- The conditional epoch law is an equivalent presentation of a Rademacher reward followed
by the common behavior action. [the hzeta condition](hyp:hzeta); and [the hm condition](hyp:hm). [the stated conclusion](goal). -/
lemma signedDepthConditionalEpochPMF_eq_map {zeta m : ℝ}
    (hzeta : 0 < zeta) (hm : |m| < 1) :
    (signedDepthConditionalEpochPMF zeta m).toMeasure =
      Measure.map
        ({ toEquiv := signedDepthEpochEquiv
           measurable_toFun := measurable_of_finite _
           measurable_invFun := measurable_of_finite _ } :
          (Bool × Bool) ≃ᵐ (Fin 1 × Bool × Fin 2))
        ((signedMeanPMF m).toMeasure.prod
          (pmfOfRealWeight (signedDepthBehaviourWeight zeta)).toMeasure) := by
  let e : (Bool × Bool) ≃ᵐ (Fin 1 × Bool × Fin 2) :=
    { toEquiv := signedDepthEpochEquiv
      measurable_toFun := measurable_of_finite _
      measurable_invFun := measurable_of_finite _ }
  apply Measure.ext_of_singleton
  intro x
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x),
    Measure.map_apply e.measurable (measurableSet_singleton x)]
  have hpre : e ⁻¹' {x} = {e.symm x} := by
    ext z
    exact e.toEquiv.apply_eq_iff_eq_symm_apply
  rw [hpre]
  rw [show ({e.symm x} : Set (Bool × Bool)) =
      {(e.symm x).1} ×ˢ {(e.symm x).2} by simp, Measure.prod_prod]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))).mp
  rw [ENNReal.toReal_mul, signedDepthConditionalEpochPMF_toReal hzeta hm,
    signedMeanPMF_toReal hm]
  have hb : ((pmfOfRealWeight (signedDepthBehaviourWeight zeta)) (e.symm x).2).toReal =
      signedDepthBehaviourWeight zeta (e.symm x).2 := by
    rw [pmfOfRealWeight_apply_of_nonneg_sum_one _
      (signedDepthBehaviourWeight_nonneg hzeta) (sum_signedDepthBehaviourWeight zeta),
      ENNReal.toReal_ofReal (signedDepthBehaviourWeight_nonneg hzeta _)]
  rw [hb]
  rcases x with ⟨x, a, r⟩
  fin_cases x
  fin_cases r <;> simp [e, signedDepthEpochEquiv, finTwoEquiv] <;> ring

/-- Common behavior actions cancel exactly from conditional KL. [the hzeta condition](hyp:hzeta); and [the hm condition](hyp:hm); and [the hn condition](hyp:hn). [the stated conclusion](goal). -/
lemma signedDepthConditionalEpoch_klDiv_eq {zeta m n : ℝ}
    (hzeta : 0 < zeta) (hm : |m| < 1) (hn : |n| < 1) :
    InformationTheory.klDiv (signedDepthConditionalEpochPMF zeta m).toMeasure
        (signedDepthConditionalEpochPMF zeta n).toMeasure =
      InformationTheory.klDiv (signedMeanPMF m).toMeasure (signedMeanPMF n).toMeasure := by
  let e : (Bool × Bool) ≃ᵐ (Fin 1 × Bool × Fin 2) :=
    { toEquiv := signedDepthEpochEquiv
      measurable_toFun := measurable_of_finite _
      measurable_invFun := measurable_of_finite _ }
  rw [signedDepthConditionalEpochPMF_eq_map hzeta hm,
    signedDepthConditionalEpochPMF_eq_map hzeta hn]
  change InformationTheory.klDiv
      (Measure.map e ((signedMeanPMF m).toMeasure.prod
        (pmfOfRealWeight (signedDepthBehaviourWeight zeta)).toMeasure))
      (Measure.map e ((signedMeanPMF n).toMeasure.prod
        (pmfOfRealWeight (signedDepthBehaviourWeight zeta)).toMeasure)) = _
  rw [Causalean.Mathlib.Probability.klDiv_map_measurableEquiv]
  rw [← Measure.compProd_const, ← Measure.compProd_const]
  exact Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_left
    (signedMeanPMF m).toMeasure (signedMeanPMF n).toMeasure
    (Kernel.const Bool (pmfOfRealWeight (signedDepthBehaviourWeight zeta)).toMeasure)

/-- The model-specific next-symbol PMF is the generic conditional epoch PMF. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the hm condition](hyp:hm). [the stated conclusion](goal). -/
lemma signedDepth_observedNextPMF_eq_conditionalEpoch {k Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (w : FiniteObsView k 1 2)
    (hm : |conditionalRewardMean (1 + k) t0 zeta C Q v
      (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w)| < 1) :
    Causalean.Mathlib.InformationTheory.FiniteWordChainRule.nextSymbolPMF
      (signedDepthFinite (k + 1) t0 zeta C Q v).obsPMF w =
      signedDepthConditionalEpochPMF zeta
        (conditionalRewardMean (1 + k) t0 zeta C Q v
          (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w)) := by
  apply PMF.ext
  intro x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [signedDepth_observedNextPMF_toReal ht0 hzeta hC,
    signedDepthConditionalEpochPMF_toReal hzeta hm]
  rcases x with ⟨x, a, r⟩
  fin_cases r <;> simp [finTwoEquiv, signedValue]

end CausalSmith.Stat.PomdpLatentOverlapMinimax
