import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.ObservedKL
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwUpper
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.TwoPoint

set_option linter.style.longLine false

/-! # Fixed-radius minimax theorem -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory
open scoped ENNReal

-- @node: thm:fixed-c-minimax
/-- At every fixed `C > 1`, the minimax risk has exponent `2/(2+t0*zeta)` without
a logarithmic loss, and the balanced PHIW estimator attains the upper bound. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
theorem fixed_c_minimax {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) :
    ∃ cLower cUpper : ℝ, 0 < cLower ∧ cLower ≤ cUpper ∧
      ∃ TStar : Nat, ∃ hTStar : 1 ≤ TStar, ∀ T, ∀ hT : T ≥ TStar,
        cLower * (T : ℝ) ^ (-rateExponent t0 zeta) ≤ minimaxRisk T t0 zeta C ∧
        minimaxRisk T t0 zeta C ≤
          cUpper * (T : ℝ) ^ (-rateExponent t0 zeta) ∧
        Causalean.Stat.worstCaseRisk
          (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := C))
          (phiwObservable (T := T) (historyDepth T t0 zeta)) ≤
            cUpper * (T : ℝ) ^ (-rateExponent t0 zeta) ∧
        ∃ Q : Nat, ∃ hQ : 1 ≤ Q,
          ∀ est : RawEstimator T,
            (∀ nX b e, Measurable (est nX b e)) →
            MeasureTheory.Integrable
              (fun w ↦ (est 1
                (signedDepthFamily T t0 zeta C Q false ht0 hzeta hC hQ).b
                (signedDepthFamily T t0 zeta C Q false ht0 hzeta hC hQ).e w -
                  targetValue (signedDepthFamily T t0 zeta C Q false ht0 hzeta hC hQ)) ^ 2)
              (obsLaw (signedDepthFamily T t0 zeta C Q false ht0 hzeta hC hQ)) →
            MeasureTheory.Integrable
              (fun w ↦ (est 1
                (signedDepthFamily T t0 zeta C Q true ht0 hzeta hC hQ).b
                (signedDepthFamily T t0 zeta C Q true ht0 hzeta hC hQ).e w -
                  targetValue (signedDepthFamily T t0 zeta C Q true ht0 hzeta hC hQ)) ^ 2)
              (obsLaw (signedDepthFamily T t0 zeta C Q true ht0 hzeta hC hQ)) →
            cLower * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
              max (rawObservedRisk est
                (signedDepthModel T Q t0 zeta C false (hTStar.trans hT)
                  ht0 hzeta hC hQ))
                (rawObservedRisk est
                  (signedDepthModel T Q t0 zeta C true (hTStar.trans hT)
                    ht0 hzeta hC hQ)) := by
  have halpha0 : 0 < mixingAlpha t0 := by unfold mixingAlpha; positivity
  have halpha1 : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have hL0 : 0 < policyFactor zeta := by unfold policyFactor; positivity
  have hlogalpha : Real.log (mixingAlpha t0) = -(1 / t0) := by simp [mixingAlpha]
  have hlogL : Real.log (policyFactor zeta) = zeta := by simp [policyFactor]
  let D : ℝ := 2 / t0 + zeta
  have hD : 0 < D := by dsimp [D]; positivity
  have hbeta : rateExponent t0 zeta = (2 / t0) / D := by
    unfold rateExponent
    dsimp [D]
    field_simp
  obtain ⟨cUpper0, hcUpper0, TUpper, hUpper, _hCovarianceSum⟩ :=
    phiw_upper ht0 hzeta hC.le
  obtain ⟨K0, hK0, hpath⟩ := observed_path_kl ht0
  have hseq : ∀ (T' Q' : Nat) (hQ' : 1 ≤ Q') (v : Bool),
      SequentialIgnorability (signedDepthFamily T' t0 zeta C Q' v ht0 hzeta hC hQ') := by
    intro T Q hQ v
    exact embed_sequentialIgnorability (signedDepthFinite T t0 zeta C Q v)
  have hstat : ∀ (T' Q' : Nat) (hQ' : 1 ≤ Q') (v : Bool),
      StationaryStart (signedDepthFamily T' t0 zeta C Q' v ht0 hzeta hC hQ') := by
    intro T Q hQ v
    exact signedDepth_stationaryStart ht0 hzeta hC.le hQ
  obtain ⟨B0, hB0, hbudget⟩ := hpath zeta C hzeta hC hseq hstat
  let cLower : ℝ :=
    (c0 t0 * epsC C * (1 - mixingAlpha t0) * mixingAlpha t0) ^ 2 *
      (8 * B0) ^ (-rateExponent t0 zeta) * Real.exp (-(1 / 8 : ℝ)) / 4
  have heps0 : 0 < epsC C := by unfold epsC; positivity
  have hc00 : 0 < c0 t0 := by unfold c0; positivity
  have hcLower : 0 < cLower := by
    dsimp [cLower]
    positivity
  let cUpper : ℝ := max cUpper0 cLower
  have hcUpper : 0 < cUpper := lt_of_lt_of_le hcUpper0 (le_max_left _ _)
  let TPos : Nat := Nat.ceil (1 / (8 * B0)) + 1
  let TStar : Nat := max (max TUpper TPos) 1
  refine ⟨cLower, cUpper, hcLower, le_max_right _ _, TStar,
    le_max_right _ _, ?_⟩
  intro T hT
  have hTU : TUpper ≤ T := (le_max_left TUpper TPos).trans
    ((le_max_left (max TUpper TPos) 1).trans hT)
  have hTP : TPos ≤ T := (le_max_right TUpper TPos).trans
    ((le_max_left (max TUpper TPos) 1).trans hT)
  have hT1 : 1 ≤ T := (le_max_right (max TUpper TPos) 1).trans hT
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT1)
  have harg1 : 1 < 8 * B0 * (T : ℝ) := by
    have hceil : 1 / (8 * B0) ≤ (Nat.ceil (1 / (8 * B0)) : Nat) := Nat.le_ceil _
    have hceilT : (Nat.ceil (1 / (8 * B0)) : ℝ) < T := by
      exact_mod_cast (show Nat.ceil (1 / (8 * B0)) < T by simpa [TPos] using hTP)
    have hrecip : 1 / (8 * B0) < (T : ℝ) := lt_of_le_of_lt hceil hceilT
    have h8B : 0 < 8 * B0 := mul_pos (by norm_num) hB0
    calc
      1 = (8 * B0) * (1 / (8 * B0)) := by field_simp
      _ < (8 * B0) * (T : ℝ) := mul_lt_mul_of_pos_left hrecip h8B
      _ = 8 * B0 * (T : ℝ) := by ring
  let x : ℝ := Real.log (8 * B0 * (T : ℝ)) / D
  have hx0 : 0 ≤ x := div_nonneg (Real.log_nonneg harg1.le) hD.le
  let Q : Nat := Nat.ceil x
  have hQ : 1 ≤ Q := Nat.ceil_pos.mpr (div_pos (Real.log_pos harg1) hD)
  have hxQ : x ≤ (Q : ℝ) := Nat.le_ceil x
  have hQx : (Q : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hDQ : D * (Q : ℝ) ≥ Real.log (8 * B0 * (T : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hxQ hD.le
    calc
      Real.log (8 * B0 * (T : ℝ)) = D * x := by
        dsimp [x]
        field_simp
      _ ≤ D * (Q : ℝ) := this
  have hcombined :
      mixingAlpha t0 ^ (2 * Q) * policyFactor zeta ^ (-(Q : ℤ)) =
        Real.exp (-D * (Q : ℝ)) := by
    rw [zpow_neg]
    calc
      mixingAlpha t0 ^ (2 * Q) * (policyFactor zeta ^ Q)⁻¹ =
          Real.exp (Real.log (mixingAlpha t0) * (2 * Q : Nat)) /
            Real.exp (Real.log (policyFactor zeta) * (Q : Nat)) := by
        rw [show Real.log (mixingAlpha t0) * (2 * Q : Nat) =
            (2 * Q : Nat) * Real.log (mixingAlpha t0) by ring,
          show Real.log (policyFactor zeta) * (Q : Nat) =
            (Q : Nat) * Real.log (policyFactor zeta) by ring,
          Real.exp_nat_mul, Real.exp_log halpha0,
          Real.exp_nat_mul, Real.exp_log hL0]
        simp [div_eq_mul_inv]
      _ = Real.exp (Real.log (mixingAlpha t0) * (2 * Q : Nat) -
          Real.log (policyFactor zeta) * (Q : Nat)) := (Real.exp_sub _ _).symm
      _ = Real.exp (-D * (Q : ℝ)) := by
        congr 1
        rw [hlogalpha, hlogL]
        dsimp [D]
        push_cast
        ring
  have hKLreal : B0 * T * mixingAlpha t0 ^ (2 * Q) *
      policyFactor zeta ^ (-(Q : ℤ)) ≤ 1 / 8 := by
    rw [show B0 * (T : ℝ) * mixingAlpha t0 ^ (2 * Q) *
        policyFactor zeta ^ (-(Q : ℤ)) =
        (B0 * (T : ℝ)) *
          (mixingAlpha t0 ^ (2 * Q) * policyFactor zeta ^ (-(Q : ℤ))) by ring,
      hcombined]
    have hexp : Real.exp (-D * (Q : ℝ)) ≤
        (8 * B0 * (T : ℝ))⁻¹ := by
      calc
        Real.exp (-D * (Q : ℝ)) ≤
            Real.exp (-Real.log (8 * B0 * (T : ℝ))) :=
          Real.exp_le_exp.mpr (by nlinarith [neg_le_neg hDQ])
        _ = (8 * B0 * (T : ℝ))⁻¹ := by
          rw [Real.exp_neg, Real.exp_log
            (mul_pos (mul_pos (by norm_num) hB0) hTreal)]
    have hBT : 0 ≤ B0 * (T : ℝ) := mul_nonneg hB0.le hTreal.le
    calc
      B0 * (T : ℝ) * Real.exp (-D * (Q : ℝ)) ≤
          B0 * (T : ℝ) * (8 * B0 * (T : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hexp hBT
      _ = 1 / 8 := by field_simp [ne_of_gt hB0, ne_of_gt hTreal]
  have hKL : InformationTheory.klDiv
      (signedDepthObsLaw T t0 zeta C Q true)
      (signedDepthObsLaw T t0 zeta C Q false) ≤ ENNReal.ofReal (1 / 8 : ℝ) :=
    (hbudget T Q hQ).1.trans (ENNReal.ofReal_le_ofReal hKLreal)
  let M0 := signedDepthModel T Q t0 zeta C false hT1 ht0 hzeta hC hQ
  let M1 := signedDepthModel T Q t0 zeta C true hT1 ht0 hzeta hC hQ
  have hb : HEq M0.raw.b M1.raw.b := by
    simp [M0, M1, signedDepthModel, signedDepthFamily, signedDepthFinite, embed]
  have he : HEq M0.raw.e M1.raw.e := by
    simp [M0, M1, signedDepthModel, signedDepthFamily, signedDepthFinite, embed]
  have hac : obsLaw M1.raw ≪ castObsLaw (show M1.nX = M0.nX by rfl) M0.raw := by
    dsimp [M0, M1, signedDepthModel, castObsLaw]
    exact embed_absolutelyContinuous
      (absolutelyContinuous_of_fullSupport
        (signedDepth_fullSupportObs ht0 hzeta hC)
        (signedDepth_fullSupportObs ht0 hzeta hC)) rfl
  have hfin : InformationTheory.klDiv (obsLaw M1.raw)
      (castObsLaw (show M1.nX = M0.nX by rfl) M0.raw) ≠ ⊤ := by
    have hKL' : InformationTheory.klDiv (obsLaw M1.raw)
        (castObsLaw (show M1.nX = M0.nX by rfl) M0.raw) ≤
          ENNReal.ofReal (1 / 8 : ℝ) := by
      exact hKL
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL'
  let s : ℝ := c0 t0 * epsC C * depthMass t0 Q Q
  have hdepth0 : 0 ≤ depthMass t0 Q Q := depthMass_nonneg ht0 Q Q
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hsep : 2 * s ≤ |targetValue M1.raw - targetValue M0.raw| := by
    have hv1 := (signedDepth_membership (T := T) ht0 hzeta hC hQ true).2.2.2.2.2
    have hv0 := (signedDepth_membership (T := T) ht0 hzeta hC hQ false).2.2.2.2.2
    dsimp [M0, M1, signedDepthModel]
    rw [hv1, hv0]
    simp [signedValue, s]
    rw [abs_of_nonneg]
    · linarith
    · positivity
  have hKL' : InformationTheory.klDiv (obsLaw M1.raw)
      (castObsLaw (show M1.nX = M0.nX by rfl) M0.raw) ≤
        ENNReal.ofReal (1 / 8 : ℝ) := by exact hKL
  have hfloor := two_point_floor_explicit (s := s) (K := (1 / 8 : ℝ))
    M1 M0 rfl hb.symm he.symm hT1 hs0 (by norm_num) hKL' hac hfin hsep
  have hden0 : 0 < 1 - mixingAlpha t0 ^ (Q + 1) := by
    have hp := pow_lt_one₀ halpha0.le halpha1 (by omega : Q + 1 ≠ 0)
    linarith
  have hdepthLower : (1 - mixingAlpha t0) * mixingAlpha t0 ^ Q ≤
      depthMass t0 Q Q := by
    unfold depthMass
    apply (le_div_iff₀ hden0).2
    have hnum0 : 0 ≤ (1 - mixingAlpha t0) * mixingAlpha t0 ^ Q := by positivity
    nlinarith [pow_nonneg halpha0.le (Q + 1)]
  have halphaQ : mixingAlpha t0 ^ Q ≥
      mixingAlpha t0 * (8 * B0 * (T : ℝ)) ^ (-(1 / t0) / D) := by
    have hmul := mul_lt_mul_of_neg_left hQx (neg_lt_zero.mpr (one_div_pos.mpr ht0))
    have hexp := Real.exp_le_exp.mpr (le_of_lt hmul)
    calc
      mixingAlpha t0 * (8 * B0 * (T : ℝ)) ^ (-(1 / t0) / D) =
          Real.exp (-(1 / t0) * (x + 1)) := by
        rw [Real.rpow_def_of_pos (mul_pos (mul_pos (by norm_num) hB0) hTreal),
          ← Real.exp_log halpha0, ← Real.exp_add]
        congr 1
        rw [hlogalpha]
        dsimp [x]
        ring
      _ ≤ Real.exp (-(1 / t0) * (Q : ℝ)) := hexp
      _ = mixingAlpha t0 ^ Q := by
        rw [← Real.exp_log halpha0, ← Real.exp_nat_mul]
        congr 1
        rw [hlogalpha]
        push_cast
        ring
  have hsLower : c0 t0 * epsC C * (1 - mixingAlpha t0) * mixingAlpha t0 *
        (8 * B0 * (T : ℝ)) ^ (-(1 / t0) / D) ≤ s := by
    dsimp [s]
    have hscale : 0 ≤ c0 t0 * epsC C * (1 - mixingAlpha t0) := by positivity
    calc
      _ = (c0 t0 * epsC C * (1 - mixingAlpha t0)) *
          (mixingAlpha t0 *
            (8 * B0 * (T : ℝ)) ^ (-(1 / t0) / D)) := by ring
      _ ≤ (c0 t0 * epsC C * (1 - mixingAlpha t0)) *
          mixingAlpha t0 ^ Q := mul_le_mul_of_nonneg_left halphaQ hscale
      _ = (c0 t0 * epsC C) *
          ((1 - mixingAlpha t0) * mixingAlpha t0 ^ Q) := by ring
      _ ≤ (c0 t0 * epsC C) * depthMass t0 Q Q :=
        mul_le_mul_of_nonneg_left hdepthLower (mul_nonneg hc00.le heps0.le)
  have hpowSplit : (8 * B0 * (T : ℝ)) ^ (-rateExponent t0 zeta) =
      (8 * B0) ^ (-rateExponent t0 zeta) *
        (T : ℝ) ^ (-rateExponent t0 zeta) := by
    rw [Real.mul_rpow (mul_nonneg (by norm_num) hB0.le) hTreal.le]
  have hsSq : (c0 t0 * epsC C * (1 - mixingAlpha t0) * mixingAlpha t0) ^ 2 *
        (8 * B0) ^ (-rateExponent t0 zeta) *
        (T : ℝ) ^ (-rateExponent t0 zeta) ≤ s ^ 2 := by
    have harg0 : 0 ≤ 8 * B0 * (T : ℝ) := by positivity
    have hsLowerSq := (sq_le_sq₀ (show (0 : ℝ) ≤
      c0 t0 * epsC C * (1 - mixingAlpha t0) * mixingAlpha t0 *
        (8 * B0 * (T : ℝ)) ^ (-(1 / t0) / D) by positivity) hs0).2 hsLower
    have hrpowSq : ((8 * B0 * (T : ℝ)) ^ (-(1 / t0) / D)) ^ 2 =
        (8 * B0 * (T : ℝ)) ^ (-rateExponent t0 zeta) := by
      rw [← Real.rpow_mul_natCast harg0]
      congr 1
      rw [hbeta]
      push_cast
      ring
    calc
      _ = (c0 t0 * epsC C * (1 - mixingAlpha t0) * mixingAlpha t0) ^ 2 *
          (8 * B0 * (T : ℝ)) ^ (-rateExponent t0 zeta) := by
        rw [hpowSplit]
        ring
      _ = (c0 t0 * epsC C * (1 - mixingAlpha t0) * mixingAlpha t0 *
          (8 * B0 * (T : ℝ)) ^ (-(1 / t0) / D)) ^ 2 := by
        rw [← hrpowSq]
        ring
      _ ≤ s ^ 2 := hsLowerSq
  have hlower : cLower * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
      s ^ 2 * Real.exp (-(1 / 8 : ℝ)) / 4 := by
    dsimp [cLower]
    have hexp0 := (Real.exp_pos (-(1 / 8 : ℝ))).le
    nlinarith [mul_le_mul_of_nonneg_right hsSq hexp0]
  have hmini : minimaxRisk T t0 zeta C ≤
      Causalean.Stat.worstCaseRisk
        (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := C))
        (phiwObservable (T := T) (historyDepth T t0 zeta)) := by
    apply Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    intro est m
    exact observedRisk_nonneg est m
  refine ⟨hlower.trans hfloor.2, hmini.trans ?_, ?_, Q, hQ, ?_⟩
  · exact (hUpper T hTU).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.rpow_nonneg hTreal.le _))
  · exact (hUpper T hTU).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.rpow_nonneg hTreal.le _))
  · intro est hmeas hint0 hint1
    have hp := hfloor.1 est hmeas hint1 hint0
    rw [max_comm] at hp
    exact hlower.trans hp

end CausalSmith.Stat.PomdpLatentOverlapMinimax
