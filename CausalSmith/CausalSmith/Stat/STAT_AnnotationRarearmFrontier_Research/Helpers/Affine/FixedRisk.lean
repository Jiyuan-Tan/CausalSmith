module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.FixedExperiment

/-!
Real and extended squared-risk readback for clipped original-experiment rules,
and the affine prior's fixed-size minimax assembly.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open Causalean.Stat.Minimax.FuzzyHypotheses

/-- [Under the stated inputs and conditions](hyp:T,P,z,n,m,d), Clipping the action and target bounds squared loss by four.  This gives [the stated result](goal).-/
-- @node: affine_rule_loss_bound
lemma affine_rule_loss_bound {n m d : Nat} (T : Rule n m d) (P : DiscreteLaw d)
    (z : Sample n m d × Real) : (T.1 z - ateFunctional P) ^ 2 ≤ 4 := by
  have hT := T.2.2 z
  have hP := ateFunctional_mem_Icc P
  have hlo : -2 ≤ T.1 z - ateFunctional P := by linarith [hT.1, hP.2]
  have hhi : T.1 z - ateFunctional P ≤ 2 := by linarith [hT.2, hP.1]
  nlinarith [mul_nonneg (by linarith : 0 ≤ T.1 z - ateFunctional P + 2)
    (by linarith : 0 ≤ 2 - (T.1 z - ateFunctional P))]

/-- [Under the stated inputs and conditions](hyp:T,P,n,m,d), The bounded measurable squared loss is integrable under the original experiment.  This gives [the stated result](goal).-/
-- @node: affine_rule_loss_integrable
lemma affine_rule_loss_integrable {n m d : Nat} (T : Rule n m d) (P : DiscreteLaw d) :
    Integrable (fun z => (T.1 z - ateFunctional P) ^ 2)
      ((annotationLaw P n m).prod seedLaw) := by
  let : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw obsLaw
    infer_instance
  let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  have hT := T.2.1
  apply Integrable.of_bound (by fun_prop) 4
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact affine_rule_loss_bound T P z

/-- [Under the stated inputs and conditions](hyp:T,P,n,m,d), The original real risk agrees with the extended nonnegative loss integral.  This gives [the stated result](goal).-/
-- @node: affine_ruleRisk_ofReal
lemma affine_ruleRisk_ofReal {n m d : Nat} (T : Rule n m d) (P : DiscreteLaw d) :
    ENNReal.ofReal (ruleRisk T.1 P) =
      ∫⁻ z, ENNReal.ofReal ((T.1 z - ateFunctional P) ^ 2)
        ∂((annotationLaw P n m).prod seedLaw) := by
  exact ofReal_integral_eq_lintegral_ofReal (affine_rule_loss_integrable T P)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-- [Under the stated inputs and conditions](hyp:T,P,n,m,d), Every clipped original rule has nonnegative risk bounded by four.  This gives [the stated result](goal).-/
-- @node: affine_ruleRisk_bounds
lemma affine_ruleRisk_bounds {n m d : Nat} (T : Rule n m d) (P : DiscreteLaw d) :
    0 ≤ ruleRisk T.1 P ∧ ruleRisk T.1 P ≤ 4 := by
  let : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw obsLaw
    infer_instance
  let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  constructor
  · exact integral_nonneg fun _ => sq_nonneg _
  · calc
      _ ≤ ∫ _z, (4 : Real) ∂((annotationLaw P n m).prod seedLaw) :=
        integral_mono (affine_rule_loss_integrable T P) (integrable_const _)
          (affine_rule_loss_bound T P)
      _ = 4 := by simp

/-- [Under the stated inputs and conditions](hyp:T,eps,P,hP,n,m,d), A legal table's risk is dominated by the bounded real worst-case supremum.  This gives [the stated result](goal).-/
-- @node: affine_ruleRisk_le_worstRisk
lemma affine_ruleRisk_le_worstRisk {n m d : Nat} (T : Rule n m d)
    (eps : Real) (P : DiscreteLaw d) (hP : ModelClass d eps P) :
    ruleRisk T.1 P ≤ worstRisk T.1 eps := by
  apply le_ciSup (show BddAbove (Set.range (fun Q : ClassLaw d eps => ruleRisk T.1 Q.1)) from
    ⟨4, by rintro _ ⟨Q, rfl⟩; exact (affine_ruleRisk_bounds T Q.1).2⟩) ⟨P, hP⟩

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,sigma,T,fallbackX,fallbackY,hyp,m), Averaging the conditional transfer under either tagged prior preserves the
worst-case bound and the half-gap failure budget.  This gives [the stated result](goal).-/
-- @node: affineTransferredRule_bayes_le
lemma affineTransferredRule_bayes_le (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (T : Rule n m d) (fallbackX : Fin n → Obs d) (fallbackY : Fin m → AuxObs d)
    (hyp : Bool) :
    let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
    let gap := (∫ lat, affineRawTarget n m d eps sigma true lat ∂nu) -
      (∫ lat, affineRawTarget n m d eps sigma false lat ∂nu)
    bayesSquaredRisk (affineRawTaggedPrior n m d eps sigma hyp)
      (affineRawTaggedKernel n m d eps hd sigma)
      (fun theta => ateFunctional (normalizedLaw theta.1 n m d eps hd sigma theta.2))
      (affineTransferredRule n m d T.1 fallbackX fallbackY) ≤
      ENNReal.ofReal (worstRisk T.1 eps) + ENNReal.ofReal (gap ^ 2 / 128) := by
  intro nu gap
  unfold bayesSquaredRisk
  calc
    _ ≤ ∫⁻ _theta, ENNReal.ofReal (worstRisk T.1 eps) + ENNReal.ofReal (gap ^ 2 / 128)
        ∂affineRawTaggedPrior n m d eps sigma hyp := by
      apply lintegral_mono
      intro theta
      have ht := affineTransferredRule_conditional_risk_le n m d eps hd sigma
        hn heps heps' hS hx T fallbackX fallbackY theta
      apply ht.trans
      apply add_le_add ?_ (le_refl _)
      change (∫⁻ z, ENNReal.ofReal ((T.1 z -
        ateFunctional (normalizedLaw theta.1 n m d eps hd sigma theta.2)) ^ 2)
        ∂((annotationLaw (normalizedLaw theta.1 n m d eps hd sigma theta.2) n m).prod seedLaw)) ≤ _
      rw [← affine_ruleRisk_ofReal T]
      apply ENNReal.ofReal_le_ofReal
      exact affine_ruleRisk_le_worstRisk T eps _
        (((affine_support_and_normalizer n m d eps hn hd heps heps' sigma).2 theta.2).2.1 theta.1)
    _ = _ := by simp

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,sigma,T,m), The genuine raw Bayes bound and prefix transfer force each original clipped
Borel rule to pay at least one one-hundred-twenty-eighth of the squared gap.  This gives [the stated result](goal).-/
-- @node: affine_fixed_rule_gap_lower
lemma affine_fixed_rule_gap_lower (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : Real.exp 4096 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (T : Rule n m d) :
    let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
    let gap := (∫ lat, affineRawTarget n m d eps sigma true lat ∂nu) -
      (∫ lat, affineRawTarget n m d eps sigma false lat ∂nu)
    gap ^ 2 / 128 ≤ worstRisk T.1 eps := by
  intro nu gap
  have hS1 : 1 ≤ (n : Real) * eps := by linarith [Real.add_one_le_exp (4096 : Real)]
  let fallbackX : Fin n → Obs d := fun _ => (⟨0, by omega⟩, false, false)
  let fallbackY : Fin m → AuxObs d := fun _ => (⟨0, by omega⟩, false)
  have hlower := affineRawTaggedKernel_bayes_lower n m d eps hd sigma hn heps heps' hS hx
    (affineTransferredRule n m d T.1 fallbackX fallbackY)
    (affineTransferredRule_measurable n m d T.1 T.2.1 fallbackX fallbackY)
  have hupper (hyp : Bool) := affineTransferredRule_bayes_le n m d eps hn hd heps heps'
    hS1 hx sigma T fallbackX fallbackY hyp
  have hraw : ENNReal.ofReal (gap ^ 2 / 64) ≤
      ENNReal.ofReal (worstRisk T.1 eps) + ENNReal.ofReal (gap ^ 2 / 128) :=
    hlower.trans (max_le (hupper false) (hupper true))
  have hW : 0 ≤ worstRisk T.1 eps := by
    let lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L :=
      fun _ => none
    exact (affine_ruleRisk_bounds T (normalizedLaw false n m d eps hd sigma lat)).1.trans
      (affine_ruleRisk_le_worstRisk T eps _
        (((affine_support_and_normalizer n m d eps hn hd heps heps' sigma).2 lat).2.1 false))
  rw [← ENNReal.ofReal_add hW (by positivity)] at hraw
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤
    worstRisk T.1 eps + gap ^ 2 / 128)).mp hraw
  linarith

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,sigma,T,m), Squaring the quantitative target separation gives the displayed affine
rate, with the same numerical constant as the paper.  This gives [the stated result](goal).-/
-- @node: affine_fixed_rule_rate_lower
lemma affine_fixed_rule_rate_lower (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : Real.exp 4096 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (T : Rule n m d) :
    (10 ^ (-20 : Int) / 128 : Real) *
      min 1 (((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2) ≤
      worstRisk T.1 eps := by
  let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
  let gap := (∫ lat, affineRawTarget n m d eps sigma true lat ∂nu) -
    (∫ lat, affineRawTarget n m d eps sigma false lat ∂nu)
  let x := (d : Real) / (((n : Real) + m) * eps * logScale n eps)
  have hS1 : 1 ≤ (n : Real) * eps := by linarith [Real.add_one_le_exp (4096 : Real)]
  have hell := affine_logScale_one_le n eps heps.le
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hclip : 0 ≤ min x 1 := le_min hx0 (by norm_num)
  have hgap : min x 1 / 10000000000 ≤ gap :=
    affine_raw_target_mean_gap_uniform n m d eps hn hd heps heps' hS1 sigma
  have hsq := pow_le_pow_left₀ (div_nonneg hclip (by norm_num)) hgap 2
  have hmin : (min x 1) ^ 2 = min 1 (x ^ 2) := by
    by_cases hx1 : x ≤ 1
    · rw [min_eq_left hx1, min_eq_right (by nlinarith)]
    · rw [min_eq_right (le_of_not_ge hx1), min_eq_left (by nlinarith), one_pow]
  have hfixed : gap ^ 2 / 128 ≤ worstRisk T.1 eps :=
    affine_fixed_rule_gap_lower n m d eps hn hd heps heps' hS hx sigma T
  have hscaled : (10 ^ (-20 : Int) / 128 : Real) * min 1 (x ^ 2) ≤ gap ^ 2 / 128 := by
    rw [div_pow, hmin] at hsq
    norm_num at hsq ⊢
    linarith
  exact hscaled.trans hfixed

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,sigma,m), Taking the infimum over all original randomized Borel rules preserves the
fixed-size affine lower bound.  This gives [the stated result](goal).-/
-- @node: affine_fixed_minimax_rate_lower
lemma affine_fixed_minimax_rate_lower (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : Real.exp 4096 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    (10 ^ (-20 : Int) / 128 : Real) *
      min 1 (((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2) ≤
      minimaxRisk n m d eps := by
  haveI : Nonempty (Rule n m d) := ⟨⟨fun _ => 0, measurable_const,
    fun _ => by constructor <;> norm_num⟩⟩
  apply le_ciInf
  intro T
  exact affine_fixed_rule_rate_lower n m d eps hn hd heps heps' hS hx sigma T

end CausalSmith.Stat.AnnotationRarearmFrontier
