module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.ObservedConditionalKL
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepthMembership
public import Causalean.Mathlib.InformationTheory.KLBind
public import Causalean.Mathlib.Probability.BernoulliMeasure
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

set_option linter.style.longLine false

/-! # Observed-path KL bounds for the signed-depth alternatives -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- The observed law of a signed-depth alternative. -/
noncomputable def signedDepthObsLaw (T : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool) :=
  obsLaw (embed (signedDepthFinite T t0 zeta C Q v))
  -- @realizes \(\mathbb P_{Q,v}^{\mathrm{obs},T}\)(observed law of the signed-depth experiment)

/-- Rademacher KL is bounded by the corresponding chi-squared expression. [the hm condition](hyp:hm); and [the hn condition](hyp:hn). [the stated conclusion](goal). -/
lemma rademacher_kl_le_chiSq {m n : ℝ} (hm : |m| < 1) (hn : |n| < 1) :
    InformationTheory.klDiv
      (pmfOfRealWeight (fun b : Bool ↦ (1 + signedValue b * m) / 2)).toMeasure
      (pmfOfRealWeight (fun b : Bool ↦ (1 + signedValue b * n) / 2)).toMeasure ≤
      ENNReal.ofReal ((m - n) ^ 2 / (1 - n ^ 2)) := by
  let p : ℝ := (1 + m) / 2
  let q : ℝ := (1 + n) / 2
  have hp0 : 0 < p := by dsimp [p]; linarith [abs_lt.mp hm |>.1]
  have hp1 : p < 1 := by dsimp [p]; linarith [abs_lt.mp hm |>.2]
  have hq0 : 0 < q := by dsimp [q]; linarith [abs_lt.mp hn |>.1]
  have hq1 : q < 1 := by dsimp [q]; linarith [abs_lt.mp hn |>.2]
  letI : IsProbabilityMeasure (Causalean.Mathlib.Probability.bernoulliLaw p) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hp0.le hp1.le
  letI : IsProbabilityMeasure (Causalean.Mathlib.Probability.bernoulliLaw q) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hq0.le hq1.le
  have hlaw (u : ℝ) (hu : |u| < 1) :
      (pmfOfRealWeight (fun b : Bool ↦ (1 + signedValue b * u) / 2)).toMeasure =
        Causalean.Mathlib.Probability.bernoulliBool ((1 + u) / 2) := by
    apply Measure.ext_of_singleton
    intro b
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
    rcases abs_lt.mp hu with ⟨hulo, huhi⟩
    have huminus : 0 ≤ 1 - u := by linarith
    have huplus : 0 ≤ 1 + u := by linarith
    have hsum : ENNReal.ofReal ((1 - u) / 2) + ENNReal.ofReal ((1 + u) / 2) = 1 := by
      rw [← ENNReal.ofReal_add (div_nonneg huminus (by norm_num))
        (div_nonneg huplus (by norm_num))]
      norm_num
      ring_nf
    have hneg : (1 + -u) / 2 = (1 - u) / 2 := by ring
    have hweight :
        ∑' b : Bool, ENNReal.ofReal ((1 + signedValue b * u) / 2) = 1 := by
      rw [tsum_bool]
      simp only [signedValue, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul]
      rw [hneg]
      exact hsum
    have hweight_ne :
        ∑' b : Bool, ENNReal.ofReal ((1 + signedValue b * u) / 2) ≠ 0 := by
      rw [hweight]
      norm_num
    cases b
    · rw [pmfOfRealWeight, dif_neg hweight_ne, PMF.normalize_apply, hweight]
      simp only [signedValue, Bool.false_eq_true, ↓reduceIte, neg_one_mul, inv_one, mul_one]
      rw [hneg]
      simp [Causalean.Mathlib.Probability.bernoulliBool]
      congr 2
      ring
    · rw [pmfOfRealWeight, dif_neg hweight_ne, PMF.normalize_apply, hweight]
      simp only [signedValue, ↓reduceIte, one_mul, inv_one, mul_one]
      simp [Causalean.Mathlib.Probability.bernoulliBool]
  rw [hlaw m hm, hlaw n hn]
  have hmap (r : ℝ) : Measure.map (fun x : ℝ ↦ decide (x = 1))
      (Causalean.Mathlib.Probability.bernoulliLaw r) =
      Causalean.Mathlib.Probability.bernoulliBool r := by
    have hg : Measurable (fun x : ℝ ↦ decide (x = 1)) := by
      exact Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const
    rw [Causalean.Mathlib.Probability.bernoulliLaw,
      Causalean.Mathlib.Probability.bernoulliBool]
    rw [Measure.map_add _ _ hg, Measure.map_smul, Measure.map_smul]
    simp
  rw [← hmap p, ← hmap q]
  calc
    InformationTheory.klDiv
        (Measure.map (fun x : ℝ ↦ decide (x = 1))
          (Causalean.Mathlib.Probability.bernoulliLaw p))
        (Measure.map (fun x : ℝ ↦ decide (x = 1))
          (Causalean.Mathlib.Probability.bernoulliLaw q)) ≤
      InformationTheory.klDiv (Causalean.Mathlib.Probability.bernoulliLaw p)
        (Causalean.Mathlib.Probability.bernoulliLaw q) :=
      InformationTheory.klDiv_map_le _ _ (by
        exact Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const)
    _ ≤ ENNReal.ofReal ((m - n) ^ 2 / (1 - n ^ 2)) := by
      have hac := Causalean.Mathlib.Probability.bernoulliLaw_ac_of_reference_interior
        (p := p) (q := q) hq0 hq1
      have hint := Causalean.Mathlib.Probability.bernoulliLaw_llr_integrable (p := p) (q := q)
      have hfin := InformationTheory.klDiv_ne_top hac hint
      rw [← ENNReal.ofReal_toReal hfin]
      apply ENNReal.ofReal_le_ofReal
      rw [Causalean.Mathlib.Probability.bernoulliLaw_klDiv_toReal hp0.le hp1.le hq0 hq1]
      have hlogp := Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
      have hlogc := Real.log_le_sub_one_of_pos
        (div_pos (sub_pos.mpr hp1) (sub_pos.mpr hq1))
      have hp_mul := mul_le_mul_of_nonneg_left hlogp hp0.le
      have hc_mul := mul_le_mul_of_nonneg_left hlogc (sub_nonneg.mpr hp1.le)
      dsimp [p, q] at *
      calc
        (1 + m) / 2 * Real.log (((1 + m) / 2) / ((1 + n) / 2)) +
            (1 - (1 + m) / 2) *
              Real.log ((1 - (1 + m) / 2) / (1 - (1 + n) / 2)) ≤
            (1 + m) / 2 * ((((1 + m) / 2) / ((1 + n) / 2)) - 1) +
            (1 - (1 + m) / 2) *
              (((1 - (1 + m) / 2) / (1 - (1 + n) / 2)) - 1) :=
          add_le_add hp_mul hc_mul
        _ = (m - n) ^ 2 / (1 - n ^ 2) := by
          have hnlo := abs_lt.mp hn |>.1
          have hnhi := abs_lt.mp hn |>.2
          have hplus : 1 + n ≠ 0 := ne_of_gt (by linarith)
          have hminus : 1 - n ≠ 0 := ne_of_gt (by linarith)
          have hsq : 1 - n ^ 2 ≠ 0 := by nlinarith
          have htwo : 2 - (1 + n) ≠ 0 := by linarith
          field_simp [hplus, hminus]
          field_simp [htwo, hsq]
          ring

/-- Every signed-depth predictive reward mean lies strictly inside the Rademacher parameter
interval. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma abs_conditionalRewardMean_lt_one {T Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (t : Fin T) (o : ObsPrefix t.val) :
    |conditionalRewardMean T t0 zeta C Q v t o| < 1 := by
  rw [conditionalRewardMean_signedDepth_all ht0 hzeta hC]
  have hc0pos : 0 < c0 t0 := by
    unfold c0 mixingAlpha
    have he : Real.exp (-(1 / t0)) < 1 := by
      rw [Real.exp_lt_one_iff]
      exact neg_neg_of_pos (one_div_pos.mpr ht0)
    linarith
  have hc0lt : c0 t0 < 1 := by
    unfold c0
    have he : 0 < mixingAlpha t0 := by unfold mixingAlpha; positivity
    linarith
  have hea := abs_epsC_mul_signedDepthActionFactor_le_one hzeta hC Q o
  have hq := terminalPosterior_mem_Icc T t0 zeta C Q v t o
  have hqabs : |(filterQuantities T t0 zeta C Q v).terminalPosterior t o| ≤ 1 := by
    rw [abs_of_nonneg hq.1]
    exact hq.2
  have habsc : |signedValue v * c0 t0| = c0 t0 := by
    cases v <;> simp [signedValue, abs_of_pos hc0pos]
  rw [show signedValue v * c0 t0 * epsC C *
      (filterQuantities T t0 zeta C Q v).actionFactor t o *
      (filterQuantities T t0 zeta C Q v).terminalPosterior t o =
    (signedValue v * c0 t0) *
      (epsC C * (filterQuantities T t0 zeta C Q v).actionFactor t o) *
      (filterQuantities T t0 zeta C Q v).terminalPosterior t o by ring,
    abs_mul, abs_mul, habsc]
  calc
    c0 t0 * |epsC C *
        (filterQuantities T t0 zeta C Q v).actionFactor t o| *
        |(filterQuantities T t0 zeta C Q v).terminalPosterior t o| ≤
        c0 t0 * 1 * 1 := by
      have hea' : |epsC C *
          (filterQuantities T t0 zeta C Q v).actionFactor t o| ≤ 1 := by
        change |epsC C * signedDepthActionFactor zeta Q o| ≤ 1
        exact hea
      gcongr
    _ < 1 := by simpa using hc0lt

/-- Conditional observed-symbol KL is exactly controlled by the two predictive reward means. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepth_observedNext_klDiv_le {k Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C)
    (w : FiniteObsView k 1 2) :
    InformationTheory.klDiv
        (Causalean.Mathlib.InformationTheory.FiniteWordChainRule.nextSymbolPMF
          (signedDepthFinite (k + 1) t0 zeta C Q true).obsPMF w).toMeasure
        (Causalean.Mathlib.InformationTheory.FiniteWordChainRule.nextSymbolPMF
          (signedDepthFinite (k + 1) t0 zeta C Q false).obsPMF w).toMeasure ≤
      ENNReal.ofReal
        ((conditionalRewardMean (1 + k) t0 zeta C Q true
              (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w) -
            conditionalRewardMean (1 + k) t0 zeta C Q false
              (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w)) ^ 2 /
          (1 - conditionalRewardMean (1 + k) t0 zeta C Q false
              (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w) ^ 2)) := by
  let mt := conditionalRewardMean (1 + k) t0 zeta C Q true
    (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w)
  let mf := conditionalRewardMean (1 + k) t0 zeta C Q false
    (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w)
  have hmt : |mt| < 1 := abs_conditionalRewardMean_lt_one ht0 hzeta hC true _ _
  have hmf : |mf| < 1 := abs_conditionalRewardMean_lt_one ht0 hzeta hC false _ _
  rw [signedDepth_observedNextPMF_eq_conditionalEpoch ht0 hzeta hC true w hmt,
    signedDepth_observedNextPMF_eq_conditionalEpoch ht0 hzeta hC false w hmf,
    signedDepthConditionalEpoch_klDiv_eq hzeta hmt hmf]
  simpa [signedMeanPMF, mt, mf] using rademacher_kl_le_chiSq hmt hmf

/-- Scalar domination of the conditional chi-square term by the squared rare-action factor. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the h K0 condition](hyp:hK0); and [the hpost condition](hyp:hpost). [the stated conclusion](goal). -/
lemma signedDepth_conditional_chiSq_le {k Q : Nat} {t0 zeta C K0 : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (hK0 : 0 < K0)
    (w : FiniteObsView k 1 2)
    (hpost : ∀ v : Bool,
      (filterQuantities (1 + k) t0 zeta C Q v).terminalPosterior
          (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w) ≤
        K0 * mixingAlpha t0 ^ Q) :
    (conditionalRewardMean (1 + k) t0 zeta C Q true
          (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w) -
        conditionalRewardMean (1 + k) t0 zeta C Q false
          (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w)) ^ 2 /
      (1 - conditionalRewardMean (1 + k) t0 zeta C Q false
          (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w) ^ 2) ≤
      (4 * c0 t0 ^ 2 * K0 ^ 2 / (1 - c0 t0 ^ 2)) * epsC C ^ 2 *
        mixingAlpha t0 ^ (2 * Q) *
        signedDepthActionFactor zeta Q (signedDepthObservedActions w) ^ 2 := by
  let o := signedDepthObservedActions w
  let t : Fin (1 + k) := ⟨k, by omega⟩
  let qt := (filterQuantities (1 + k) t0 zeta C Q true).terminalPosterior t o
  let qf := (filterQuantities (1 + k) t0 zeta C Q false).terminalPosterior t o
  let A := signedDepthActionFactor zeta Q o
  let d := c0 t0 * epsC C * A
  have hmt : conditionalRewardMean (1 + k) t0 zeta C Q true t o = d * qt := by
    rw [conditionalRewardMean_signedDepth_all ht0 hzeta hC]
    change signedValue true * c0 t0 * epsC C * A * qt = d * qt
    simp [signedValue, d]
  have hmf : conditionalRewardMean (1 + k) t0 zeta C Q false t o = -(d * qf) := by
    rw [conditionalRewardMean_signedDepth_all ht0 hzeta hC]
    change signedValue false * c0 t0 * epsC C * A * qf = -(d * qf)
    simp [signedValue, d]
  change (conditionalRewardMean (1 + k) t0 zeta C Q true t o -
      conditionalRewardMean (1 + k) t0 zeta C Q false t o) ^ 2 /
      (1 - conditionalRewardMean (1 + k) t0 zeta C Q false t o ^ 2) ≤ _
  rw [hmt, hmf]
  have hc0pos : 0 < c0 t0 := by
    unfold c0 mixingAlpha
    have he : Real.exp (-(1 / t0)) < 1 := by
      rw [Real.exp_lt_one_iff]
      exact neg_neg_of_pos (one_div_pos.mpr ht0)
    linarith
  have hc0lt : c0 t0 < 1 := by
    unfold c0
    have he : 0 < mixingAlpha t0 := by unfold mixingAlpha; positivity
    linarith
  have heps0 : 0 ≤ epsC C := by unfold epsC; positivity
  have hA0 : 0 ≤ A := signedDepthActionFactor_nonneg hzeta Q o
  have hA1 : A ≤ 1 := signedDepthActionFactor_le_one hzeta Q o
  have hqtI := terminalPosterior_mem_Icc (1 + k) t0 zeta C Q true t o
  have hqfI := terminalPosterior_mem_Icc (1 + k) t0 zeta C Q false t o
  have halphaBase : 0 ≤ mixingAlpha t0 := by unfold mixingAlpha; positivity
  have halpha0 : 0 ≤ mixingAlpha t0 ^ Q := pow_nonneg halphaBase _
  have hqtK : qt ≤ K0 * mixingAlpha t0 ^ Q := hpost true
  have hqfK : qf ≤ K0 * mixingAlpha t0 ^ Q := hpost false
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact mul_nonneg (mul_nonneg hc0pos.le heps0) hA0
  have hfac : epsC C * A ≤ 1 := by
    have h := abs_epsC_mul_signedDepthActionFactor_le_one hzeta hC Q o
    rw [abs_of_nonneg (mul_nonneg heps0 hA0)] at h
    exact h
  have hdsq : d ^ 2 ≤ c0 t0 ^ 2 := by
    have hdle : d ≤ c0 t0 := by
      dsimp [d]
      nlinarith
    nlinarith [sq_nonneg (d - c0 t0)]
  have hden : 0 < 1 - c0 t0 ^ 2 := by nlinarith
  have hqsum : qt + qf ≤ 2 * (K0 * mixingAlpha t0 ^ Q) := by
    dsimp [qt, qf] at hqtK hqfK ⊢
    linarith
  have hnum : (d * qt - -(d * qf)) ^ 2 ≤
      4 * c0 t0 ^ 2 * K0 ^ 2 * epsC C ^ 2 * A ^ 2 *
        mixingAlpha t0 ^ (2 * Q) := by
    have hpow : (mixingAlpha t0 ^ Q) ^ 2 = mixingAlpha t0 ^ (2 * Q) := by
      rw [← pow_mul]
      congr 1
      omega
    have hqnonneg : 0 ≤ qt + qf := add_nonneg hqtI.1 hqfI.1
    have hbase : (qt + qf) ^ 2 ≤ (2 * (K0 * mixingAlpha t0 ^ Q)) ^ 2 := by
      nlinarith
    dsimp [d]
    rw [show (c0 t0 * epsC C * A * qt - -(c0 t0 * epsC C * A * qf)) ^ 2 =
      (c0 t0 * epsC C * A) ^ 2 * (qt + qf) ^ 2 by ring]
    calc
      _ ≤ (c0 t0 * epsC C * A) ^ 2 *
          (2 * (K0 * mixingAlpha t0 ^ Q)) ^ 2 := by
            gcongr
      _ = _ := by rw [← hpow]; ring
  have hnum0 : 0 ≤ 4 * c0 t0 ^ 2 * K0 ^ 2 * epsC C ^ 2 * A ^ 2 *
      mixingAlpha t0 ^ (2 * Q) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity : 0 ≤ 4 * c0 t0 ^ 2) (sq_nonneg K0))
          (sq_nonneg (epsC C)))
        (sq_nonneg A))
      (pow_nonneg halphaBase _)
  have hdenle : 1 - d ^ 2 * qf ^ 2 ≥ 1 - c0 t0 ^ 2 := by
    have hqf1 := hqfI.2
    have hqf0 := hqfI.1
    have hqfsq : qf ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hdsq (sq_nonneg qf),
      mul_le_mul_of_nonneg_left hqfsq (sq_nonneg d)]
  have hdiv := div_le_div₀ hnum0 hnum hden hdenle
  have hdrewrite : 1 - (-(d * qf)) ^ 2 = 1 - d ^ 2 * qf ^ 2 := by ring
  calc
    (d * qt - -(d * qf)) ^ 2 / (1 - (-(d * qf)) ^ 2) ≤
        (4 * c0 t0 ^ 2 * K0 ^ 2 * epsC C ^ 2 * A ^ 2 *
          mixingAlpha t0 ^ (2 * Q)) / (1 - c0 t0 ^ 2) := by
            rw [hdrewrite]
            exact hdiv
    _ = _ := by ring

/-- Iterating the conditional chain rule and the rare-action moment bound gives the finite
signed-depth observed-PMF KL estimate. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the h K0 condition](hyp:hK0); and [the hpost condition](hyp:hpost). [the stated conclusion](goal). -/
lemma signedDepth_finiteObs_klDiv_le {T Q : Nat} {t0 zeta C K0 : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (hK0 : 0 < K0)
    (hpost : ∀ (N : Nat) (v : Bool) (t : Fin N) (o : ObsPrefix t.val),
      (filterQuantities N t0 zeta C Q v).terminalPosterior t o ≤
        K0 * mixingAlpha t0 ^ Q) :
    InformationTheory.klDiv (signedDepthFinite T t0 zeta C Q true).obsPMF.toMeasure
        (signedDepthFinite T t0 zeta C Q false).obsPMF.toMeasure ≤
      ENNReal.ofReal ((4 * c0 t0 ^ 2 * K0 ^ 2 / (1 - c0 t0 ^ 2)) *
        T * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
        policyFactor zeta ^ (-(Q : ℤ))) := by
  let D := 4 * c0 t0 ^ 2 * K0 ^ 2 / (1 - c0 t0 ^ 2)
  have hc0pos : 0 < c0 t0 := by
    unfold c0 mixingAlpha
    have he : Real.exp (-(1 / t0)) < 1 := by
      rw [Real.exp_lt_one_iff]
      exact neg_neg_of_pos (one_div_pos.mpr ht0)
    linarith
  have hc0lt : c0 t0 < 1 := by
    unfold c0
    have he : 0 < mixingAlpha t0 := by unfold mixingAlpha; positivity
    linarith
  have hden0 : 0 ≤ 1 - c0 t0 ^ 2 := by nlinarith
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg (by positivity) hden0
  have heps0 : 0 ≤ epsC C ^ 2 := sq_nonneg _
  have halphaBase : 0 ≤ mixingAlpha t0 := by unfold mixingAlpha; positivity
  have halpha0 : 0 ≤ mixingAlpha t0 ^ (2 * Q) := pow_nonneg halphaBase _
  have hpolicyBase : 0 ≤ policyFactor zeta := by unfold policyFactor; positivity
  have hpolicy0 : 0 ≤ policyFactor zeta ^ (-(Q : ℤ)) := zpow_nonneg hpolicyBase _
  induction T with
  | zero =>
      rw [Causalean.Mathlib.InformationTheory.FiniteWordChainRule.klDiv_eq_chainKL]
      simp [Causalean.Mathlib.InformationTheory.FiniteWordChainRule.chainKL]
  | succ k ih =>
      rw [Causalean.Mathlib.InformationTheory.FiniteWordChainRule.klDiv_lastCoordinate_eq_add_sum_of_fullSupport
        (signedDepthFinite (k + 1) t0 zeta C Q true).obsPMF
        (signedDepthFinite (k + 1) t0 zeta C Q false).obsPMF
        (signedDepth_fullSupportObs ht0 hzeta hC)
        (signedDepth_fullSupportObs ht0 hzeta hC)]
      rw [signedDepth_observed_horizon_projective (k := k) (Q := Q),
        signedDepth_observed_horizon_projective (k := k) (Q := Q)]
      have hinc :
          (∑ w : FiniteObsView k 1 2,
            (signedDepthFinite k t0 zeta C Q true).obsPMF w *
              InformationTheory.klDiv
                (Causalean.Mathlib.InformationTheory.FiniteWordChainRule.nextSymbolPMF
                  (signedDepthFinite (k + 1) t0 zeta C Q true).obsPMF w).toMeasure
                (Causalean.Mathlib.InformationTheory.FiniteWordChainRule.nextSymbolPMF
                  (signedDepthFinite (k + 1) t0 zeta C Q false).obsPMF w).toMeasure) ≤
            ENNReal.ofReal (D * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
              policyFactor zeta ^ (-(Q : ℤ))) := by
        let f : FiniteObsView k 1 2 → ℝ := fun w ↦
          prefixMass (1 + k) t0 zeta C Q true (⟨k, by omega⟩ : Fin (1 + k))
              (signedDepthObservedActions w) *
            (D * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
              signedDepthActionFactor zeta Q (signedDepthObservedActions w) ^ 2)
        have hf0 (w : FiniteObsView k 1 2) : 0 ≤ f w := by
          dsimp [f]
          exact mul_nonneg
            (prefixMass_nonneg (1 + k) t0 zeta C Q true
              (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w))
            (mul_nonneg (mul_nonneg (mul_nonneg hD0 heps0) halpha0) (sq_nonneg _))
        calc
          _ ≤ ∑ w : FiniteObsView k 1 2, ENNReal.ofReal (f w) := by
            apply Finset.sum_le_sum
            intro w _
            have hchi := signedDepth_conditional_chiSq_le ht0 hzeta hC hK0 w
              (fun v ↦ hpost (1 + k) v (⟨k, by omega⟩ : Fin (1 + k))
                (signedDepthObservedActions w))
            have hnext := (signedDepth_observedNext_klDiv_le ht0 hzeta hC w).trans
              (ENNReal.ofReal_le_ofReal hchi)
            have hp : (signedDepthFinite k t0 zeta C Q true).obsPMF w =
                ENNReal.ofReal (prefixMass (1 + k) t0 zeta C Q true
                  (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w)) := by
              rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
                signedDepth_obsPMF_toReal_eq_prefixMass]
            rw [hp]
            calc
              _ ≤ ENNReal.ofReal (prefixMass (1 + k) t0 zeta C Q true
                    (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w)) *
                  ENNReal.ofReal (D * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
                    signedDepthActionFactor zeta Q (signedDepthObservedActions w) ^ 2) :=
                by gcongr
              _ = ENNReal.ofReal (f w) := by
                have hp0 := prefixMass_nonneg (1 + k) t0 zeta C Q true
                  (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w)
                simpa [f] using (ENNReal.ofReal_mul hp0).symm
          _ = ENNReal.ofReal (∑ w : FiniteObsView k 1 2, f w) := by
            symm
            exact ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hf0 i)
          _ ≤ ENNReal.ofReal (D * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
              policyFactor zeta ^ (-(Q : ℤ))) := by
            apply ENNReal.ofReal_le_ofReal
            have hrare := rareAction_secondMoment_le (k := k) (Q := Q)
              ht0 hzeta hC true
            dsimp [f]
            rw [show (∑ w : FiniteObsView k 1 2,
                prefixMass (1 + k) t0 zeta C Q true (⟨k, by omega⟩ : Fin (1 + k))
                    (signedDepthObservedActions w) *
                  (D * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
                    signedDepthActionFactor zeta Q (signedDepthObservedActions w) ^ 2)) =
                D * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
                  ∑ o : ObsPrefix k, prefixMass (1 + k) t0 zeta C Q true
                    (⟨k, by omega⟩ : Fin (1 + k)) o *
                    signedDepthActionFactor zeta Q o ^ 2 by
              rw [Fintype.sum_equiv
                { toFun := signedDepthObservedActions
                  invFun := fun o i ↦ (0, o i)
                  left_inv := by intro w; funext i; apply Prod.ext; exact (Fin.eq_zero _).symm; rfl
                  right_inv := by intro o; rfl }
                (fun w ↦ prefixMass (1 + k) t0 zeta C Q true
                    (⟨k, by omega⟩ : Fin (1 + k)) (signedDepthObservedActions w) *
                  (D * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
                    signedDepthActionFactor zeta Q (signedDepthObservedActions w) ^ 2))
                (fun o ↦ prefixMass (1 + k) t0 zeta C Q true
                    (⟨k, by omega⟩ : Fin (1 + k)) o *
                  (D * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
                    signedDepthActionFactor zeta Q o ^ 2))]
              · rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro o _
                ring
              · intro w
                rfl]
            gcongr
      have hconst0 : 0 ≤ D * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
          policyFactor zeta ^ (-(Q : ℤ)) := by positivity
      have hprev0 : 0 ≤ D * k * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
          policyFactor zeta ^ (-(Q : ℤ)) := by positivity
      calc
        _ ≤ ENNReal.ofReal (D * k * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
              policyFactor zeta ^ (-(Q : ℤ))) +
            ENNReal.ofReal (D * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
              policyFactor zeta ^ (-(Q : ℤ))) := add_le_add ih hinc
        _ = ENNReal.ofReal (D * (k + 1) * epsC C ^ 2 *
              mixingAlpha t0 ^ (2 * Q) * policyFactor zeta ^ (-(Q : ℤ))) := by
            rw [← ENNReal.ofReal_add hprev0 hconst0]
            congr 1
            ring
        _ = _ := by
          dsimp [D]
          congr 1
          push_cast
          ring

/-- A fixed analytic bootstrap factor controls every signed-depth posterior, uniformly in the
behavior parameter.  This is the quantified form needed when the constant is chosen before
`zeta` in the observed-path statement. [the ht0 condition](hyp:ht0); and [the hfactor condition](hyp:hfactor). [the stated conclusion](goal). -/
lemma terminalPosterior_le_of_bootstrap_factor {t0 K0 : ℝ} (ht0 : 0 < t0)
    (hfactor : ∀ Q : Nat,
      1 / (1 - c0 t0 * (mixingAlpha t0 / (1 - c0 t0)) ^ Q) ^ Q ≤ K0) :
    ∀ {zeta C : ℝ}, 0 < zeta → 1 < C → ∀ (T Q : Nat) (v : Bool)
      (t : Fin T) (o : ObsPrefix t.val),
      (filterQuantities T t0 zeta C Q v).terminalPosterior t o ≤
        K0 * mixingAlpha t0 ^ Q := by
  intro zeta C hzeta hC T Q v t o
  rcases t with ⟨k, hk⟩
  obtain ⟨U, hT⟩ : ∃ U : Nat, T = U + (k + 1) := ⟨T - (k + 1), by omega⟩
  subst T
  have hprefix :
      prefixMass (U + (k + 1)) t0 zeta C Q v
          (⟨k, by omega⟩ : Fin (U + (k + 1))) o =
        signedDepthTotalMass (U + (k + 1)) t0 zeta C Q v o := by
    have h := prefixMass_eq_sum_signedDepthFilterMass (U + 1) k (by omega)
      t0 zeta C Q v o
    convert h using 1
    · congr 1
      · omega
      · apply (Fin.heq_ext_iff (by omega)).2
        rfl
    · apply Finset.sum_congr rfl
      intro h _
      congr 1 <;> omega
  have hterminal :
      terminalPrefixMass (U + (k + 1)) t0 zeta C Q v
          (⟨k, by omega⟩ : Fin (U + (k + 1))) o =
        ∑ h : Fin (2 * (Q + 1)),
          if latentDepth Q h = Q then
            signedDepthFilterMass (U + (k + 1)) t0 zeta C Q v o h else 0 := by
    have h := terminalPrefixMass_eq_sum_signedDepthFilterMass (U + 1) k (by omega)
      t0 zeta C Q v o
    convert h using 1
    · congr 1
      · omega
      · apply (Fin.heq_ext_iff (by omega)).2
        rfl
    · apply Finset.sum_congr rfl
      intro h _
      by_cases hQ : latentDepth Q h = Q <;> simp [hQ]
      congr 1 <;> omega
  have hrefined := signedDepthRawPosterior_le_refined
    (N := U + (k + 1)) (Q := Q) ht0 hzeta hC v o
  have ha : 0 ≤ mixingAlpha t0 ^ Q := pow_nonneg (mixingAlpha_pos ht0).le _
  simp only [filterQuantities]
  rw [hterminal, hprefix]
  change signedDepthRawPosterior (U + (k + 1)) t0 zeta C Q v o ≤ _
  calc
    _ ≤ mixingAlpha t0 ^ Q /
        (1 - c0 t0 * (mixingAlpha t0 / (1 - c0 t0)) ^ Q) ^ Q := hrefined
    _ = mixingAlpha t0 ^ Q *
        (1 / (1 - c0 t0 * (mixingAlpha t0 / (1 - c0 t0)) ^ Q) ^ Q) := by ring
    _ ≤ mixingAlpha t0 ^ Q * K0 := mul_le_mul_of_nonneg_left (hfactor Q) ha
    _ = K0 * mixingAlpha t0 ^ Q := by ring

-- @node: lem:observed-path-kl
/-- A `Q,T`-uniform observed-divergence constant and terminal-posterior constant exist;
the same constants also give the exact finite-prefix conditional-mean identity. [the ht0 condition](hyp:ht0). [the stated conclusion](goal). -/
lemma observed_path_kl {t0 : ℝ} (ht0 : 0 < t0) :
    ∃ K0 : ℝ, 0 < K0 ∧ -- @realizes \(K_0\)(chosen from t0 alone)
      ∀ (zeta C : ℝ) (hzeta : 0 < zeta) (hC : 1 < C),
      (∀ (T Q : Nat) (hQ : 1 ≤ Q) (v : Bool),
        SequentialIgnorability (signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ)) →
      (∀ (T Q : Nat) (hQ : 1 ≤ Q) (v : Bool),
        StationaryStart (signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ)) →
      ∃ B0 : ℝ, 0 < B0 ∧ -- @realizes \(B_0\)(may depend on t0,zeta,C only)
        ∀ (T Q : Nat), 1 ≤ Q →
        InformationTheory.klDiv
            (signedDepthObsLaw T t0 zeta C Q true)
            (signedDepthObsLaw T t0 zeta C Q false) ≤
          ENNReal.ofReal (B0 * T * mixingAlpha t0 ^ (2 * Q) *
            policyFactor zeta ^ (-(Q : ℤ))) ∧
        (∀ (v : Bool) (t : Fin T) (o : ObsPrefix t.val),
          conditionalRewardMean T t0 zeta C Q v t o =
            signedValue v * c0 t0 * epsC C *
              (filterQuantities T t0 zeta C Q v).actionFactor t o *
              (filterQuantities T t0 zeta C Q v).terminalPosterior t o) ∧
        (∀ (v : Bool) (t : Fin T) (o : ObsPrefix t.val),
          (filterQuantities T t0 zeta C Q v).terminalPosterior t o ≤
            K0 * mixingAlpha t0 ^ Q) ∧
        InformationTheory.klDiv
            (signedDepthObsLaw T t0 zeta C Q true)
            (signedDepthObsLaw T t0 zeta C Q false) ≤
          ENNReal.ofReal ((4 * c0 t0 ^ 2 * K0 ^ 2 / (1 - c0 t0 ^ 2)) *
            T * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
            policyFactor zeta ^ (-(Q : ℤ))) := by
  rcases exists_uniform_signedDepth_bootstrap_factor ht0 with ⟨K0, hK0, hfactor⟩
  refine ⟨K0, hK0, ?_⟩
  intro zeta C hzeta hC _hseq _hstat
  let B0 := 4 * c0 t0 ^ 2 * K0 ^ 2 / (1 - c0 t0 ^ 2)
  have hc0pos : 0 < c0 t0 := by
    unfold c0 mixingAlpha
    have he : Real.exp (-(1 / t0)) < 1 := by
      rw [Real.exp_lt_one_iff]
      exact neg_neg_of_pos (one_div_pos.mpr ht0)
    linarith
  have hc0lt : c0 t0 < 1 := by
    unfold c0
    linarith [mixingAlpha_pos ht0]
  have hden : 0 < 1 - c0 t0 ^ 2 := by nlinarith
  have hB0 : 0 < B0 := by
    dsimp [B0]
    positivity
  refine ⟨B0, hB0, ?_⟩
  intro T Q hQ
  have hpost : ∀ (N : Nat) (v : Bool) (t : Fin N) (o : ObsPrefix t.val),
      (filterQuantities N t0 zeta C Q v).terminalPosterior t o ≤
        K0 * mixingAlpha t0 ^ Q := by
    intro N v t o
    exact terminalPosterior_le_of_bootstrap_factor ht0 hfactor hzeta hC N Q v t o
  have hpostQ : ∀ (v : Bool) (t : Fin T) (o : ObsPrefix t.val),
      (filterQuantities T t0 zeta C Q v).terminalPosterior t o ≤
        K0 * mixingAlpha t0 ^ Q := by
    intro v t o
    exact terminalPosterior_le_of_bootstrap_factor ht0 hfactor hzeta hC T Q v t o
  have hfinite := signedDepth_finiteObs_klDiv_le (T := T) (Q := Q)
    ht0 hzeta hC hK0 hpost
  have hdecode := embed_klDiv_le
    (F := signedDepthFinite T t0 zeta C Q true)
    (G := signedDepthFinite T t0 zeta C Q false) (by rfl)
  have hkl : InformationTheory.klDiv
      (signedDepthObsLaw T t0 zeta C Q true)
      (signedDepthObsLaw T t0 zeta C Q false) ≤
        ENNReal.ofReal (B0 * T * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
          policyFactor zeta ^ (-(Q : ℤ))) := by
    exact hdecode.trans (by simpa [B0] using hfinite)
  have heps0 : 0 ≤ epsC C := epsC_nonneg hC.le
  have heps1 : epsC C ≤ 1 := le_trans (epsC_le_half C) (by norm_num)
  have hpolicyBase : 0 ≤ policyFactor zeta := by unfold policyFactor; positivity
  have hpolicy0 : 0 ≤ policyFactor zeta ^ (-(Q : ℤ)) :=
    zpow_nonneg hpolicyBase _
  have htail0 : 0 ≤ mixingAlpha t0 ^ (2 * Q) *
      policyFactor zeta ^ (-(Q : ℤ)) :=
    mul_nonneg (pow_nonneg (mixingAlpha_pos ht0).le _) hpolicy0
  have hcoarseReal :
      B0 * T * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
          policyFactor zeta ^ (-(Q : ℤ)) ≤
        B0 * T * mixingAlpha t0 ^ (2 * Q) *
          policyFactor zeta ^ (-(Q : ℤ)) := by
    have hepssq : epsC C ^ 2 ≤ 1 := by nlinarith
    have hBT0 : 0 ≤ B0 * (T : ℝ) := mul_nonneg hB0.le (Nat.cast_nonneg T)
    calc
      _ = (B0 * T) * epsC C ^ 2 *
          (mixingAlpha t0 ^ (2 * Q) * policyFactor zeta ^ (-(Q : ℤ))) := by ring
      _ ≤ (B0 * T) * 1 *
          (mixingAlpha t0 ^ (2 * Q) * policyFactor zeta ^ (-(Q : ℤ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hepssq hBT0) htail0
      _ = _ := by ring
  refine ⟨hkl.trans (ENNReal.ofReal_le_ofReal hcoarseReal), ?_, hpostQ, ?_⟩
  · intro v t o
    exact conditionalRewardMean_signedDepth_all ht0 hzeta hC v t o
  · simpa [B0] using hkl

-- @node: lem:radius-explicit-observed-kl
/-- The signed-depth amplitude is comparable to `q_C`, and the KL coefficient can be
chosen independently of `C,Q,T` and of alphabet cardinalities. [the ht0 condition](hyp:ht0). [the stated conclusion](goal). -/
lemma radius_explicit_observed_kl {t0 : ℝ} (ht0 : 0 < t0) :
    ∃ K0 : ℝ, 0 < K0 ∧ -- @realizes \(K_0\)(coefficient chosen from t0 alone)
      ∀ (zeta : ℝ), 0 < zeta → ∀ (C : ℝ), 1 < C → ∀ (T Q : Nat), 1 ≤ Q →
      overlapRadius C / 2 ≤ epsC C ∧ epsC C ≤ overlapRadius C ∧
      InformationTheory.klDiv
          (signedDepthObsLaw T t0 zeta C Q true)
          (signedDepthObsLaw T t0 zeta C Q false) ≤
        ENNReal.ofReal ((4 * c0 t0 ^ 2 * K0 ^ 2 / (1 - c0 t0 ^ 2)) *
          T * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
          policyFactor zeta ^ (-(Q : ℤ))) := by
  obtain ⟨K0, hK0, hpath⟩ := observed_path_kl ht0
  refine ⟨K0, hK0, ?_⟩
  intro zeta hzeta C hC T Q hQ
  have hseq : ∀ (T' Q' : Nat) (hQ' : 1 ≤ Q') (v : Bool),
      SequentialIgnorability (signedDepthFamily T' t0 zeta C Q' v ht0 hzeta hC hQ') := by
    intro T' Q' hQ' v
    exact embed_sequentialIgnorability (signedDepthFinite T' t0 zeta C Q' v)
  have hstat : ∀ (T' Q' : Nat) (hQ' : 1 ≤ Q') (v : Bool),
      StationaryStart (signedDepthFamily T' t0 zeta C Q' v ht0 hzeta hC hQ') := by
    intro T' Q' hQ' v
    exact signedDepth_stationaryStart ht0 hzeta hC.le hQ'
  obtain ⟨B0, hB0, hall⟩ := hpath zeta C hzeta hC hseq hstat
  have hkl := (hall T Q hQ).2.2.2
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have hCsub : 0 ≤ C - 1 := sub_nonneg.mpr hC.le
  constructor
  · unfold overlapRadius epsC
    by_cases hC2 : C ≤ 2
    · rw [min_eq_left (by linarith)]
      have hbase : (C - 1) / C ≤ C - 1 := (div_le_iff₀ hCpos).2 (by
        nlinarith [mul_nonneg hCsub (sub_nonneg.mpr hC.le)])
      linarith
    · rw [min_eq_right (by linarith)]
      have hbase : (C - 1) / C ≤ 1 := (div_le_iff₀ hCpos).2 (by linarith)
      linarith
  constructor
  · unfold overlapRadius epsC
    by_cases hC2 : C ≤ 2
    · rw [min_eq_left (by linarith)]
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hCpos).2
      nlinarith [mul_nonneg hCsub (sub_nonneg.mpr hC2)]
    · rw [min_eq_right (by linarith)]
      apply (le_div_iff₀ hCpos).2
      nlinarith
  · exact hkl

end CausalSmith.Stat.PomdpLatentOverlapMinimax
