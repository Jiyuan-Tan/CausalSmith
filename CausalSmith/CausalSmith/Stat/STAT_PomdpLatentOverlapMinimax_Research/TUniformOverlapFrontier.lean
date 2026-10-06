module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.BiasVariance
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.ObservedKL
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.TwoPoint

set_option linter.style.longLine false

/-! # Uniform latent-overlap minimax frontier -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open Filter MeasureTheory
open scoped Topology ENNReal

/-- The all-radius target rate surface. -/
noncomputable def frontierRate (T : Nat) (t0 zeta C : ℝ) : ℝ :=
  (T : ℝ)⁻¹ + (T : ℝ) ^ (-rateExponent t0 zeta) *
    overlapRadius C ^ (2 * (1 - rateExponent t0 zeta))

set_option maxHeartbeats 800000 in
-- @node: thm:uniform-overlap-frontier
/-- Uniformly over every `C ≥ 1`, the minimax risk is comparable to the sum of the
parametric and hidden-state terms, with constants and threshold chosen before `C`;
the radius-adaptive PHIW estimator attains the common upper bound, while fixed
depth zero has parametric risk along every regime where `T * q_C^2` is bounded. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
theorem uniform_overlap_frontier {t0 zeta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ cLower cUpper : ℝ, 0 < cLower ∧ cLower ≤ cUpper ∧
      (∃ TStar : Nat, 1 ≤ TStar ∧ ∀ (C : ℝ), 1 ≤ C → ∀ T ≥ TStar,
          cLower * frontierRate T t0 zeta C ≤ minimaxRisk T t0 zeta C ∧
          minimaxRisk T t0 zeta C ≤ cUpper * frontierRate T t0 zeta C ∧
          Causalean.Stat.worstCaseRisk
            (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := C))
            (phiwObservable (T := T) (radiusAdaptiveDepth T t0 zeta C)) ≤
              cUpper * frontierRate T t0 zeta C) ∧
      ∀ (Cregime : Nat → ℝ), (∀ T, 1 ≤ Cregime T) →
        (∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ (T : Nat) in atTop,
          (T : ℝ) * overlapRadius (Cregime T) ^ 2 ≤ D) →
        ∃ cImmediate : ℝ, 0 < cImmediate ∧
          ∀ᶠ (T : Nat) in atTop,
            Causalean.Stat.worstCaseRisk
              (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := Cregime T))
              (phiwObservable (T := T) 0) ≤ cImmediate / T := by
  have halpha0 : 0 < mixingAlpha t0 := by unfold mixingAlpha; positivity
  have halpha1 : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have hL1 : 1 < policyFactor zeta := by
    rw [policyFactor, Real.one_lt_exp_iff]
    exact hzeta
  have hbeta0 : 0 < rateExponent t0 zeta := by unfold rateExponent; positivity
  have hbeta1 : rateExponent t0 zeta < 1 := by
    unfold rateExponent
    rw [div_lt_one (by positivity)]
    nlinarith [mul_pos ht0 hzeta]
  obtain ⟨cR, hcR, TR, hTR, hrate⟩ := radiusAdaptiveDepth_rate ht0 hzeta
  obtain ⟨K0, hK0, hKL⟩ := radius_explicit_observed_kl ht0
  let B : ℝ := 4 * c0 t0 ^ 2 * K0 ^ 2 / (1 - c0 t0 ^ 2)
  have hc00 : 0 < c0 t0 := by unfold c0; positivity
  have hc01 : c0 t0 < 1 := by unfold c0; linarith
  have hdenB : 0 < 1 - c0 t0 ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hc01) (by linarith : 0 < 1 + c0 t0)]
  have hB : 0 < B := by
    dsimp [B]
    exact div_pos (mul_pos (mul_pos (by positivity) (sq_pos_of_pos hc00))
      (sq_pos_of_pos hK0)) hdenB
  let x0 : ℝ := max 1 (1 / (4 * B))
  have hx00 : 0 < x0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h8Bx0 : 1 < 8 * B * x0 := by
    have hx := le_max_right (1 : ℝ) (1 / (4 * B))
    have h4B : 0 < 4 * B := mul_pos (by norm_num) hB
    have hm := mul_le_mul_of_nonneg_left hx h4B.le
    have : 1 ≤ 4 * B * x0 := by
      calc
        1 = 4 * B * (1 / (4 * B)) := by field_simp
        _ ≤ 4 * B * x0 := hm
    nlinarith
  let cP : ℝ := Real.exp (-(1 / 4 : ℝ)) / 64
  let cH : ℝ :=
    (c0 t0 * (1 - mixingAlpha t0) * mixingAlpha t0 / 2) ^ 2 *
      (8 * B) ^ (-rateExponent t0 zeta) * Real.exp (-(1 / 8 : ℝ)) / 4
  have hcP : 0 < cP := by dsimp [cP]; positivity
  have hcH : 0 < cH := by dsimp [cH]; positivity
  let smallFactor : ℝ := 1 + x0 ^ (1 - rateExponent t0 zeta)
  have hsmallFactor : 0 < smallFactor := by dsimp [smallFactor]; positivity
  let cLower : ℝ := min (cP / (2 * smallFactor)) (cH / 2)
  have hcLower : 0 < cLower := by
    dsimp [cLower]
    exact lt_min (div_pos hcP (mul_pos (by norm_num) hsmallFactor))
      (div_pos hcH (by norm_num))
  let A : ℝ := max 4 (max
    (2 * policyFactor zeta * (1 + 4 / (policyFactor zeta - 1)))
    (8 / (1 - mixingAlpha t0)))
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let cAttain : ℝ := A * (cR + 1)
  have hcAttain : 0 < cAttain := mul_pos hA (by linarith)
  let cUpper : ℝ := max cAttain cLower
  have hcUpper : 0 < cUpper := lt_of_lt_of_le hcAttain (le_max_left _ _)
  have hcLowerUpper : cLower ≤ cUpper := le_max_right _ _
  refine ⟨cLower, cUpper, hcLower, hcLowerUpper, ?_, ?_⟩
  · refine ⟨max TR 1, le_max_right _ _, ?_⟩
    intro C hC T hT
    have hTR' : TR ≤ T := (le_max_left TR 1).trans hT
    have hT1 : 1 ≤ T := (le_max_right TR 1).trans hT
    have hTpos : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT1)
    let q := overlapRadius C
    let k := radiusAdaptiveDepth T t0 zeta C
    have hq0 : 0 ≤ q := (overlapRadius_mem hC).1
    have hq1 : q < 1 := (overlapRadius_mem hC).2
    have hk : k ≤ T / 2 := by
      dsimp [k]
      unfold radiusAdaptiveDepth
      split_ifs
      · omega
      · exact min_le_left _ _
    have hkT : k < T := by omega
    have hrateT := hrate T hTR' C hC
    change q ^ 2 * mixingAlpha t0 ^ (2 * k) +
        policyFactor zeta ^ k / (T : ℝ) ≤ cR * frontierRate T t0 zeta C at hrateT
    let m0 := parametricModel T t0 zeta C false hT1 ht0 hzeta hC
    letI : Nonempty (ModelIndex T t0 zeta C) := ⟨m0⟩
    have hattain : Causalean.Stat.worstCaseRisk
        (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := C))
        (phiwObservable (T := T) k) ≤ cUpper * frontierRate T t0 zeta C := by
      simp [phiwObservable, hkT]
      apply Causalean.Stat.worstCaseRisk_le
      intro m
      have hrisk := radius_sensitive_phiw ht0 hzeta hC hT1 m.raw m.mem hk
      change Causalean.Stat.sqRisk (obsLaw m.raw)
        (phiwEstimator k hkT m.raw.b m.raw.e) (targetValue m.raw) ≤ _
      have hx : 0 ≤ q ^ 2 * mixingAlpha t0 ^ (2 * k) := by positivity
      have hy : 0 ≤ policyFactor zeta ^ k / (T : ℝ) := by positivity
      have hz : 0 ≤ (T : ℝ)⁻¹ := by positivity
      have hboundA :
          4 * q ^ 2 * mixingAlpha t0 ^ (2 * k) +
            (2 / (T : ℝ)) *
              (policyFactor zeta ^ (k + 1) *
                  (1 + 4 / (policyFactor zeta - 1)) +
                4 / (1 - mixingAlpha t0)) ≤
            A * (q ^ 2 * mixingAlpha t0 ^ (2 * k) +
              policyFactor zeta ^ k / (T : ℝ) + (T : ℝ)⁻¹) := by
        have hA4 : 4 ≤ A := le_max_left _ _
        have hAvar : 2 * policyFactor zeta *
            (1 + 4 / (policyFactor zeta - 1)) ≤ A :=
          (le_max_left _ _).trans (le_max_right _ _)
        have hAmix : 8 / (1 - mixingAlpha t0) ≤ A :=
          (le_max_right _ _).trans (le_max_right _ _)
        have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
        have heq :
            (2 / (T : ℝ)) *
                (policyFactor zeta ^ (k + 1) *
                    (1 + 4 / (policyFactor zeta - 1)) +
                  4 / (1 - mixingAlpha t0)) =
              (2 * policyFactor zeta * (1 + 4 / (policyFactor zeta - 1))) *
                  (policyFactor zeta ^ k / (T : ℝ)) +
                (8 / (1 - mixingAlpha t0)) * (T : ℝ)⁻¹ := by
          rw [pow_succ]
          field_simp
          ring
        rw [heq]
        nlinarith [mul_nonneg (sub_nonneg.mpr hA4) hx,
          mul_nonneg (sub_nonneg.mpr hAvar) hy,
          mul_nonneg (sub_nonneg.mpr hAmix) hz]
      have hfront0 : 0 ≤ frontierRate T t0 zeta C := by
        unfold frontierRate
        positivity
      have hsum : q ^ 2 * mixingAlpha t0 ^ (2 * k) +
            policyFactor zeta ^ k / (T : ℝ) + (T : ℝ)⁻¹ ≤
          (cR + 1) * frontierRate T t0 zeta C := by
        have hinv : (T : ℝ)⁻¹ ≤ frontierRate T t0 zeta C := by
          unfold frontierRate
          exact le_add_of_nonneg_right (by positivity)
        nlinarith [hrateT]
      calc
        Causalean.Stat.sqRisk (obsLaw m.raw)
            (phiwEstimator k hkT m.raw.b m.raw.e) (targetValue m.raw) ≤ _ := hrisk
        _ ≤ A * (q ^ 2 * mixingAlpha t0 ^ (2 * k) +
              policyFactor zeta ^ k / (T : ℝ) + (T : ℝ)⁻¹) := hboundA
        _ ≤ A * ((cR + 1) * frontierRate T t0 zeta C) := by gcongr
        _ = cAttain * frontierRate T t0 zeta C := by dsimp [cAttain]; ring
        _ ≤ cUpper * frontierRate T t0 zeta C := by
          gcongr
          exact le_max_left _ _
    have hminiUpper : minimaxRisk T t0 zeta C ≤
        Causalean.Stat.worstCaseRisk
          (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := C))
          (phiwObservable (T := T) k) := by
      apply Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
      intro est m
      exact observedRisk_nonneg est m
    have hparam : cP / (T : ℝ) ≤ minimaxRisk T t0 zeta C := by
      have hp := (uniform_parametric_floor ht0 hzeta T hT1 C hC).1
      dsimp [cP]
      convert hp using 1 <;> field_simp
    have hlower : cLower * frontierRate T t0 zeta C ≤ minimaxRisk T t0 zeta C := by
      let x : ℝ := (T : ℝ) * q ^ 2
      have hx0 : 0 ≤ x := by dsimp [x]; positivity
      have hcommon : (T : ℝ) ^ (-rateExponent t0 zeta) *
          q ^ (2 * (1 - rateExponent t0 zeta)) =
          (T : ℝ)⁻¹ * x ^ (1 - rateExponent t0 zeta) := by
        by_cases hqz : q = 0
        · have hp : 0 < 1 - rateExponent t0 zeta := by linarith
          have hp2 : 0 < 2 * (1 - rateExponent t0 zeta) := by positivity
          simp [x, hqz, ne_of_gt hp, ne_of_gt hp2]
        · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
          rw [show x = (T : ℝ) * q ^ 2 by rfl,
            Real.mul_rpow hTpos.le (sq_nonneg q),
            ← Real.rpow_natCast_mul hq0 2 (1 - rateExponent t0 zeta)]
          rw [← Real.rpow_neg_one]
          calc
            (T : ℝ) ^ (-rateExponent t0 zeta) *
                q ^ (2 * (1 - rateExponent t0 zeta)) =
                ((T : ℝ) ^ (-(1 : ℝ)) *
                  (T : ℝ) ^ (1 - rateExponent t0 zeta)) *
                    q ^ (2 * (1 - rateExponent t0 zeta)) := by
              rw [← Real.rpow_add hTpos]
              congr 2
              ring
            _ = (T : ℝ) ^ (-(1 : ℝ)) *
                ((T : ℝ) ^ (1 - rateExponent t0 zeta) *
                  q ^ (2 * (1 - rateExponent t0 zeta))) := by ring
      by_cases hxsmall : x < x0
      · have hxpow : x ^ (1 - rateExponent t0 zeta) ≤
            x0 ^ (1 - rateExponent t0 zeta) :=
          Real.rpow_le_rpow hx0 (le_of_lt hxsmall) (by linarith)
        have hfront : frontierRate T t0 zeta C ≤
            smallFactor / (T : ℝ) := by
          rw [frontierRate, hcommon]
          dsimp [smallFactor]
          rw [div_eq_mul_inv]
          nlinarith [mul_le_mul_of_nonneg_left hxpow (inv_nonneg.mpr hTpos.le)]
        calc
          cLower * frontierRate T t0 zeta C ≤
              cLower * (smallFactor / (T : ℝ)) := by gcongr
          _ ≤ cP / (T : ℝ) := by
            have hc : cLower ≤ cP / smallFactor :=
              (min_le_left _ _).trans (by
                apply (div_le_div_iff₀ (mul_pos (by norm_num) hsmallFactor)
                  hsmallFactor).2
                nlinarith [hcP])
            have := mul_le_mul_of_nonneg_right hc (div_nonneg hsmallFactor.le hTpos.le)
            field_simp at this ⊢
            nlinarith
          _ ≤ minimaxRisk T t0 zeta C := hparam
      · have hxlarge : x0 ≤ x := le_of_not_gt hxsmall
        have hCgt : 1 < C := by
          by_contra hn
          have hCeq : C = 1 := le_antisymm (le_of_not_gt hn) hC
          subst C
          simp [q, overlapRadius, x] at hxlarge
          linarith
        let D : ℝ := 2 / t0 + zeta
        have hD : 0 < D := by dsimp [D]; positivity
        have hlogalpha : Real.log (mixingAlpha t0) = -(1 / t0) := by simp [mixingAlpha]
        have hlogL : Real.log (policyFactor zeta) = zeta := by simp [policyFactor]
        have hbeta : rateExponent t0 zeta = (2 / t0) / D := by
          unfold rateExponent
          dsimp [D]
          field_simp
        have harg : 1 < 8 * B * x := h8Bx0.trans_le
          (mul_le_mul_of_nonneg_left hxlarge (mul_nonneg (by norm_num) hB.le))
        let y : ℝ := Real.log (8 * B * x) / D
        have hy0 : 0 ≤ y := div_nonneg (Real.log_nonneg harg.le) hD.le
        let Q : Nat := Nat.ceil y
        have hQ : 1 ≤ Q := Nat.ceil_pos.mpr (div_pos (Real.log_pos harg) hD)
        have hyQ : y ≤ (Q : ℝ) := Nat.le_ceil y
        have hQy : (Q : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
        have hDQ : Real.log (8 * B * x) ≤ D * (Q : ℝ) := by
          have hm := mul_le_mul_of_nonneg_left hyQ hD.le
          calc
            Real.log (8 * B * x) = D * y := by dsimp [y]; field_simp
            _ ≤ D * (Q : ℝ) := hm
        have hcombined : mixingAlpha t0 ^ (2 * Q) *
            policyFactor zeta ^ (-(Q : ℤ)) = Real.exp (-D * (Q : ℝ)) := by
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
                Real.exp_nat_mul, Real.exp_log (by positivity : 0 < policyFactor zeta)]
              simp [div_eq_mul_inv]
            _ = Real.exp (Real.log (mixingAlpha t0) * (2 * Q : Nat) -
                Real.log (policyFactor zeta) * (Q : Nat)) := (Real.exp_sub _ _).symm
            _ = Real.exp (-D * (Q : ℝ)) := by
              congr 1
              rw [hlogalpha, hlogL]
              dsimp [D]
              push_cast
              ring
        obtain ⟨hepsLower, hepsUpper, hbudget⟩ := hKL zeta hzeta C hCgt T Q hQ
        have hKLreal : B * (T : ℝ) * epsC C ^ 2 *
            mixingAlpha t0 ^ (2 * Q) * policyFactor zeta ^ (-(Q : ℤ)) ≤ 1 / 8 := by
          have hepsq : epsC C ^ 2 ≤ q ^ 2 :=
            (sq_le_sq₀ (epsC_nonneg hCgt.le) hq0).2 hepsUpper
          have hpre : B * (T : ℝ) * epsC C ^ 2 ≤ B * x := by
            dsimp [x]
            nlinarith [mul_nonneg hB.le (mul_nonneg hTpos.le (sub_nonneg.mpr hepsq))]
          rw [show B * (T : ℝ) * epsC C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
              policyFactor zeta ^ (-(Q : ℤ)) =
              (B * (T : ℝ) * epsC C ^ 2) *
                (mixingAlpha t0 ^ (2 * Q) * policyFactor zeta ^ (-(Q : ℤ))) by ring,
            hcombined]
          have hexp : Real.exp (-D * (Q : ℝ)) ≤ (8 * B * x)⁻¹ := by
            calc
              Real.exp (-D * (Q : ℝ)) ≤ Real.exp (-Real.log (8 * B * x)) :=
                Real.exp_le_exp.mpr (by linarith)
              _ = (8 * B * x)⁻¹ := by rw [Real.exp_neg, Real.exp_log (lt_trans zero_lt_one harg)]
          have hpre0 : 0 ≤ B * (T : ℝ) * epsC C ^ 2 := by positivity
          have hxpos : 0 < x := by
            exact lt_of_lt_of_le hx00 hxlarge
          calc
            B * (T : ℝ) * epsC C ^ 2 * Real.exp (-D * (Q : ℝ)) ≤
                (B * x) * (8 * B * x)⁻¹ :=
              (mul_le_mul hpre hexp (Real.exp_nonneg _) (by positivity))
            _ = 1 / 8 := by field_simp [ne_of_gt hB, ne_of_gt hxpos]
        have hbudget' : InformationTheory.klDiv
            (signedDepthObsLaw T t0 zeta C Q true)
            (signedDepthObsLaw T t0 zeta C Q false) ≤ ENNReal.ofReal (1 / 8 : ℝ) :=
          hbudget.trans (ENNReal.ofReal_le_ofReal hKLreal)
        let M0 := signedDepthModel T Q t0 zeta C false hT1 ht0 hzeta hCgt hQ
        let M1 := signedDepthModel T Q t0 zeta C true hT1 ht0 hzeta hCgt hQ
        have hb : HEq M1.raw.b M0.raw.b := by
          simp [M0, M1, signedDepthModel, signedDepthFamily, signedDepthFinite, embed]
        have he : HEq M1.raw.e M0.raw.e := by
          simp [M0, M1, signedDepthModel, signedDepthFamily, signedDepthFinite, embed]
        have hac : obsLaw M1.raw ≪ castObsLaw (show M1.nX = M0.nX by rfl) M0.raw := by
          dsimp [M0, M1, signedDepthModel, castObsLaw]
          exact embed_absolutelyContinuous
            (absolutelyContinuous_of_fullSupport
              (signedDepth_fullSupportObs ht0 hzeta hCgt)
              (signedDepth_fullSupportObs ht0 hzeta hCgt)) rfl
        have hfin : InformationTheory.klDiv (obsLaw M1.raw)
            (castObsLaw (show M1.nX = M0.nX by rfl) M0.raw) ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbudget'
        let s : ℝ := c0 t0 * epsC C * depthMass t0 Q Q
        have heps0 : 0 ≤ epsC C := epsC_nonneg hCgt.le
        have hs0 : 0 ≤ s := by
          dsimp [s]
          exact mul_nonneg (mul_nonneg hc00.le heps0) (depthMass_nonneg ht0 Q Q)
        have hsep : 2 * s ≤ |targetValue M1.raw - targetValue M0.raw| := by
          have hv1 := (signedDepth_membership (T := T) ht0 hzeta hCgt hQ true).2.2.2.2.2
          have hv0 := (signedDepth_membership (T := T) ht0 hzeta hCgt hQ false).2.2.2.2.2
          dsimp [M0, M1, signedDepthModel]
          rw [hv1, hv0]
          simp only [signedValue, ↓reduceIte, Bool.false_eq_true]
          rw [abs_of_nonneg]
          · have heq : 2 * s = 1 * c0 t0 * epsC C * depthMass t0 Q Q -
                -1 * c0 t0 * epsC C * depthMass t0 Q Q := by
              dsimp [s]
              ring
            exact heq.le
          · dsimp [s] at hs0 ⊢
            nlinarith
        have hfloor := (two_point_floor_explicit (s := s) (K := (1 / 8 : ℝ))
          M1 M0 rfl hb he hT1 hs0 (by norm_num) hbudget' hac hfin hsep).2
        have hden0 : 0 < 1 - mixingAlpha t0 ^ (Q + 1) := by
          exact sub_pos.mpr (pow_lt_one₀ halpha0.le halpha1 (by omega : Q + 1 ≠ 0))
        have hdepthLower : (1 - mixingAlpha t0) * mixingAlpha t0 ^ Q ≤
            depthMass t0 Q Q := by
          unfold depthMass
          apply (le_div_iff₀ hden0).2
          have hn : 0 ≤ (1 - mixingAlpha t0) * mixingAlpha t0 ^ Q := by positivity
          rw [mul_sub, mul_one]
          exact sub_le_self _ (mul_nonneg hn (pow_nonneg halpha0.le (Q + 1)))
        have halphaQ : mixingAlpha t0 ^ Q ≥
            mixingAlpha t0 * (8 * B * x) ^ (-(1 / t0) / D) := by
          have hm := mul_lt_mul_of_neg_left hQy (neg_lt_zero.mpr (one_div_pos.mpr ht0))
          have hexp := Real.exp_le_exp.mpr (le_of_lt hm)
          calc
            mixingAlpha t0 * (8 * B * x) ^ (-(1 / t0) / D) =
                Real.exp (-(1 / t0) * (y + 1)) := by
              rw [Real.rpow_def_of_pos (lt_trans zero_lt_one harg),
                ← Real.exp_log halpha0, ← Real.exp_add]
              congr 1
              rw [hlogalpha]
              dsimp [y]
              ring
            _ ≤ Real.exp (-(1 / t0) * (Q : ℝ)) := hexp
            _ = mixingAlpha t0 ^ Q := by
              rw [← Real.exp_log halpha0, ← Real.exp_nat_mul]
              congr 1
              rw [hlogalpha]
              push_cast
              ring
        have hsLower : c0 t0 * q * (1 - mixingAlpha t0) * mixingAlpha t0 / 2 *
              (8 * B * x) ^ (-(1 / t0) / D) ≤ s := by
          dsimp [s]
          have hscale : 0 ≤ c0 t0 * (1 - mixingAlpha t0) := by positivity
          have heps : q / 2 ≤ epsC C := by simpa [q] using hepsLower
          have hfac0 : 0 ≤ c0 t0 * (1 - mixingAlpha t0) * mixingAlpha t0 *
              (8 * B * x) ^ (-(1 / t0) / D) := by positivity
          calc
            _ = (q / 2) * (c0 t0 * (1 - mixingAlpha t0) * mixingAlpha t0 *
                (8 * B * x) ^ (-(1 / t0) / D)) := by ring
            _ ≤ epsC C * (c0 t0 * (1 - mixingAlpha t0) * mixingAlpha t0 *
                (8 * B * x) ^ (-(1 / t0) / D)) :=
              mul_le_mul_of_nonneg_right heps hfac0
            _ = c0 t0 * epsC C * (1 - mixingAlpha t0) * mixingAlpha t0 *
                (8 * B * x) ^ (-(1 / t0) / D) := by
              ring
            _ ≤ c0 t0 * epsC C * (1 - mixingAlpha t0) * mixingAlpha t0 ^ Q := by
              have hscl : 0 ≤ c0 t0 * epsC C * (1 - mixingAlpha t0) := by positivity
              calc
                _ = (c0 t0 * epsC C * (1 - mixingAlpha t0)) *
                    (mixingAlpha t0 * (8 * B * x) ^ (-(1 / t0) / D)) := by ring
                _ ≤ (c0 t0 * epsC C * (1 - mixingAlpha t0)) *
                    mixingAlpha t0 ^ Q := mul_le_mul_of_nonneg_left halphaQ hscl
                _ = _ := by ring
            _ ≤ c0 t0 * epsC C * depthMass t0 Q Q := by
              have hscl : 0 ≤ c0 t0 * epsC C := by positivity
              calc
                _ = (c0 t0 * epsC C) *
                    ((1 - mixingAlpha t0) * mixingAlpha t0 ^ Q) := by ring
                _ ≤ (c0 t0 * epsC C) * depthMass t0 Q Q :=
                  mul_le_mul_of_nonneg_left hdepthLower hscl
                _ = _ := by ring
        have hsSq : (c0 t0 * (1 - mixingAlpha t0) * mixingAlpha t0 / 2) ^ 2 *
              q ^ 2 * (8 * B * x) ^ (-rateExponent t0 zeta) ≤ s ^ 2 := by
          have hlhs0 : 0 ≤ c0 t0 * q * (1 - mixingAlpha t0) * mixingAlpha t0 / 2 *
              (8 * B * x) ^ (-(1 / t0) / D) := by positivity
          have hsLowerSq := (sq_le_sq₀ hlhs0 hs0).2 hsLower
          have hrpowSq : ((8 * B * x) ^ (-(1 / t0) / D)) ^ 2 =
              (8 * B * x) ^ (-rateExponent t0 zeta) := by
            rw [← Real.rpow_mul_natCast (le_of_lt (lt_trans zero_lt_one harg))]
            congr 1
            rw [hbeta]
            push_cast
            ring
          calc
            _ = (c0 t0 * q * (1 - mixingAlpha t0) * mixingAlpha t0 / 2 *
                (8 * B * x) ^ (-(1 / t0) / D)) ^ 2 := by
              rw [← hrpowSq]
              ring
            _ ≤ s ^ 2 := hsLowerSq
        have hpowSplit : (8 * B * x) ^ (-rateExponent t0 zeta) =
            (8 * B) ^ (-rateExponent t0 zeta) *
              x ^ (-rateExponent t0 zeta) := by
          rw [Real.mul_rpow (mul_nonneg (by norm_num) hB.le) hx0]
        have hhiddenFloor : cH *
              ((T : ℝ) ^ (-rateExponent t0 zeta) *
                q ^ (2 * (1 - rateExponent t0 zeta))) ≤
            minimaxRisk T t0 zeta C := by
          have hqx : q ^ 2 * x ^ (-rateExponent t0 zeta) =
              (T : ℝ) ^ (-rateExponent t0 zeta) *
                q ^ (2 * (1 - rateExponent t0 zeta)) := by
            have hqpos : 0 < q := by
              dsimp [q, overlapRadius]
              positivity
            rw [show x = (T : ℝ) * q ^ 2 by rfl,
              Real.mul_rpow hTpos.le (sq_nonneg q),
              ← Real.rpow_natCast_mul hq0 2 (-rateExponent t0 zeta)]
            calc
              q ^ 2 * ((T : ℝ) ^ (-rateExponent t0 zeta) *
                  q ^ ((2 : ℕ) * (-rateExponent t0 zeta))) =
                  (T : ℝ) ^ (-rateExponent t0 zeta) *
                    (q ^ 2 * q ^ ((2 : ℝ) * (-rateExponent t0 zeta))) := by ring_nf
              _ = (T : ℝ) ^ (-rateExponent t0 zeta) *
                    (q ^ (2 : ℝ) * q ^ ((2 : ℝ) * (-rateExponent t0 zeta))) := by
                congr 2
                exact (Real.rpow_natCast q 2).symm
              _ = (T : ℝ) ^ (-rateExponent t0 zeta) *
                    q ^ ((2 : ℝ) + 2 * (-rateExponent t0 zeta)) := by
                rw [Real.rpow_add hqpos]
              _ = (T : ℝ) ^ (-rateExponent t0 zeta) *
                    q ^ (2 * (1 - rateExponent t0 zeta)) := by ring_nf
          have hsSq' : (c0 t0 * (1 - mixingAlpha t0) * mixingAlpha t0 / 2) ^ 2 *
                (8 * B) ^ (-rateExponent t0 zeta) *
                (q ^ 2 * x ^ (-rateExponent t0 zeta)) ≤ s ^ 2 := by
            calc
              _ = (c0 t0 * (1 - mixingAlpha t0) * mixingAlpha t0 / 2) ^ 2 *
                    q ^ 2 * (8 * B * x) ^ (-rateExponent t0 zeta) := by
                rw [hpowSplit]
                ring
              _ ≤ s ^ 2 := hsSq
          dsimp [cH]
          rw [hqx] at hsSq'
          calc
            (c0 t0 * (1 - mixingAlpha t0) * mixingAlpha t0 / 2) ^ 2 *
                  (8 * B) ^ (-rateExponent t0 zeta) * Real.exp (-(1 / 8 : ℝ)) / 4 *
                  ((T : ℝ) ^ (-rateExponent t0 zeta) *
                    q ^ (2 * (1 - rateExponent t0 zeta))) =
                ((c0 t0 * (1 - mixingAlpha t0) * mixingAlpha t0 / 2) ^ 2 *
                  (8 * B) ^ (-rateExponent t0 zeta) *
                  ((T : ℝ) ^ (-rateExponent t0 zeta) *
                    q ^ (2 * (1 - rateExponent t0 zeta)))) *
                    Real.exp (-(1 / 8 : ℝ)) / 4 := by ring
            _ ≤ s ^ 2 * Real.exp (-(1 / 8 : ℝ)) / 4 := by gcongr
            _ ≤ minimaxRisk T t0 zeta C := hfloor
        have hinv : (T : ℝ)⁻¹ ≤ frontierRate T t0 zeta C := by
          unfold frontierRate
          exact le_add_of_nonneg_right (by positivity)
        have hhidden : (T : ℝ) ^ (-rateExponent t0 zeta) *
            q ^ (2 * (1 - rateExponent t0 zeta)) ≤ frontierRate T t0 zeta C := by
          unfold frontierRate
          exact le_add_of_nonneg_left (by positivity)
        have hsf1 : 1 ≤ smallFactor := by
          dsimp [smallFactor]
          exact le_add_of_nonneg_right (Real.rpow_nonneg hx00.le _)
        have hcLP : cLower ≤ cP / 2 :=
          (min_le_left _ _).trans (by
            have hden : (2 : ℝ) ≤ 2 * smallFactor :=
              by
                simpa only [mul_one] using
                  (mul_le_mul_of_nonneg_left hsf1 (by norm_num : (0 : ℝ) ≤ 2))
            have hcross : cP * 2 ≤ cP * (2 * smallFactor) :=
              mul_le_mul_of_nonneg_left hden hcP.le
            exact (div_le_div_iff₀ (by positivity : 0 < 2 * smallFactor)
              (by norm_num : (0 : ℝ) < 2)).2 hcross)
        have hcLH : cLower ≤ cH / 2 := min_le_right _ _
        unfold frontierRate
        have hpHalf : cLower * (T : ℝ)⁻¹ ≤ minimaxRisk T t0 zeta C / 2 := by
          have hm := mul_le_mul_of_nonneg_right hcLP (inv_nonneg.mpr hTpos.le)
          calc
            cLower * (T : ℝ)⁻¹ ≤ (cP / 2) * (T : ℝ)⁻¹ := hm
            _ = (cP * (T : ℝ)⁻¹) / 2 := by ring
            _ ≤ minimaxRisk T t0 zeta C / 2 := by
              gcongr
              simpa only [div_eq_mul_inv] using hparam
        have hhHalf : cLower * ((T : ℝ) ^ (-rateExponent t0 zeta) *
              q ^ (2 * (1 - rateExponent t0 zeta))) ≤ minimaxRisk T t0 zeta C / 2 := by
          have hm := mul_le_mul_of_nonneg_right hcLH (by positivity : 0 ≤
            (T : ℝ) ^ (-rateExponent t0 zeta) * q ^ (2 * (1 - rateExponent t0 zeta)))
          calc
            cLower * ((T : ℝ) ^ (-rateExponent t0 zeta) *
                q ^ (2 * (1 - rateExponent t0 zeta))) ≤
                (cH / 2) * ((T : ℝ) ^ (-rateExponent t0 zeta) *
                  q ^ (2 * (1 - rateExponent t0 zeta))) := hm
            _ = (cH * ((T : ℝ) ^ (-rateExponent t0 zeta) *
                  q ^ (2 * (1 - rateExponent t0 zeta)))) / 2 := by ring
            _ ≤ minimaxRisk T t0 zeta C / 2 := by gcongr
        calc
          cLower * ((T : ℝ)⁻¹ + (T : ℝ) ^ (-rateExponent t0 zeta) *
              q ^ (2 * (1 - rateExponent t0 zeta))) =
              cLower * (T : ℝ)⁻¹ + cLower * ((T : ℝ) ^ (-rateExponent t0 zeta) *
                q ^ (2 * (1 - rateExponent t0 zeta))) := by ring
          _ ≤ minimaxRisk T t0 zeta C / 2 + minimaxRisk T t0 zeta C / 2 :=
            add_le_add hpHalf hhHalf
          _ = minimaxRisk T t0 zeta C := by ring
    refine ⟨hlower, hminiUpper.trans hattain, ?_⟩
    simpa only [k] using hattain
  · intro Cregime hCregime hbounded
    obtain ⟨D0, hD0, hev⟩ := hbounded
    let V : ℝ := policyFactor zeta * (1 + 4 / (policyFactor zeta - 1)) +
      4 / (1 - mixingAlpha t0)
    let cImmediate : ℝ := 4 * D0 + 2 * V
    have hV : 0 < V := by dsimp [V]; positivity
    have hcI : 0 < cImmediate := by dsimp [cImmediate]; positivity
    refine ⟨cImmediate, hcI, ?_⟩
    filter_upwards [hev, eventually_ge_atTop (1 : Nat)] with T hx hT1
    have hkT : 0 < T := Nat.zero_lt_of_lt hT1
    let m0 := parametricModel T t0 zeta (Cregime T) false hT1 ht0 hzeta (hCregime T)
    letI : Nonempty (ModelIndex T t0 zeta (Cregime T)) := ⟨m0⟩
    simp [phiwObservable, hkT]
    apply Causalean.Stat.worstCaseRisk_le
    intro m
    have hrisk := radius_sensitive_phiw ht0 hzeta (hCregime T) hT1 m.raw m.mem
      (k := 0) (by omega)
    change Causalean.Stat.sqRisk (obsLaw m.raw)
      (phiwEstimator 0 hkT m.raw.b m.raw.e) (targetValue m.raw) ≤ cImmediate / T
    have hTpos : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT1)
    have hq : overlapRadius (Cregime T) ^ 2 ≤ D0 / (T : ℝ) := by
      apply (le_div_iff₀ hTpos).2
      nlinarith
    calc
      Causalean.Stat.sqRisk (obsLaw m.raw)
          (phiwEstimator 0 hkT m.raw.b m.raw.e) (targetValue m.raw) ≤ _ := hrisk
      _ ≤ 4 * (D0 / (T : ℝ)) + 2 / (T : ℝ) * V := by
        dsimp [V]
        nlinarith
      _ = cImmediate / T := by dsimp [cImmediate]; ring
  -- @realizes \(c_\star\)(C-uniform lower constant) @realizes \(c^\star\)(C-uniform upper constant) @realizes \(T_\star\)(C-uniform threshold)

end CausalSmith.Stat.PomdpLatentOverlapMinimax
