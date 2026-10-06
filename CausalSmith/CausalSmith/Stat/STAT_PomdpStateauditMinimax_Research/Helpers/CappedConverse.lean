module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.CappedRisk
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.SignedDepth
public import Causalean.Stat.Minimax.Pinsker

/-! # Quantitative signed-depth converse at the collision cap. -/

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory
open scoped ENNReal

-- @node: signedDepthHorizon_pos
/-- The signed-depth choice is always positive. -/
lemma signedDepthHorizon_pos (T : Nat) (t0 zeta B0 : ℝ) :
    1 ≤ signedDepthHorizon T t0 zeta B0 := by
  unfold signedDepthHorizon
  exact le_max_left _ _

-- @node: signedDepthHorizon_quantitative
/-- The prescribed signed depth makes the KL budget constant while retaining the
hidden-state separation rate. -/
lemma signedDepthHorizon_quantitative {t0 zeta B0 : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hB0 : 1 ≤ B0) :
    ∃ csep : ℝ, 0 < csep ∧ ∀ T : Nat, 1 ≤ T →
      let Q := signedDepthHorizon T t0 zeta B0
      1 ≤ Q ∧
      B0 * T * mixingAlpha t0 ^ (2 * Q) *
          policyFactor zeta ^ (-(Q : ℤ)) ≤ 1 / 16 ∧
      csep * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
        separationRadius t0 2 Q ht0 (by norm_num)
          (signedDepthHorizon_pos T t0 zeta B0) ^ 2 := by
  have halpha0 : 0 < mixingAlpha t0 := by unfold mixingAlpha; positivity
  have halpha1 : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have hL0 : 0 < policyFactor zeta := by unfold policyFactor; positivity
  have hlogalpha : Real.log (mixingAlpha t0) = -(1 / t0) := by simp [mixingAlpha]
  have hlogL : Real.log (policyFactor zeta) = zeta := by simp [policyFactor]
  have hlogInv : Real.log (1 / mixingAlpha t0) = 1 / t0 := by
    rw [Real.log_div (by norm_num) (ne_of_gt halpha0), Real.log_one, hlogalpha]
    ring
  let D : ℝ := 2 / t0 + zeta
  have hD : 0 < D := by dsimp [D]; positivity
  have hden : 2 * Real.log (1 / mixingAlpha t0) +
      Real.log (policyFactor zeta) = D := by
    rw [hlogInv, hlogL]
    dsimp [D]
    ring
  have hbeta : rateExponent t0 zeta = (2 / t0) / D := by
    unfold rateExponent
    dsimp [D]
    field_simp
  let csep : ℝ :=
    (rewardAmplitude t0 ht0 * signBias 2 (by norm_num) *
      (1 - mixingAlpha t0) * mixingAlpha t0) ^ 2 *
      (16 * B0) ^ (-rateExponent t0 zeta)
  have hcsep : 0 < csep := by
    dsimp [csep, rewardAmplitude, signBias]
    positivity
  refine ⟨csep, hcsep, ?_⟩
  intro T hT
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT)
  have harg1 : 1 < 16 * B0 * (T : ℝ) := by
    have : (1 : ℝ) ≤ B0 * T := by
      have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
      nlinarith [mul_nonneg (sub_nonneg.mpr hB0) (sub_nonneg.mpr hTr)]
    nlinarith
  let x : ℝ := Real.log (16 * B0 * (T : ℝ)) / D
  have hx0 : 0 ≤ x := div_nonneg (Real.log_nonneg harg1.le) hD.le
  have hxpos : 0 < x := div_pos (Real.log_pos harg1) hD
  let Q : Nat := signedDepthHorizon T t0 zeta B0
  have hQeq : Q = Nat.ceil x := by
    dsimp [Q]
    unfold signedDepthHorizon
    rw [hden, Int.ceil_toNat]
    change max 1 (Nat.ceil x) = Nat.ceil x
    apply max_eq_right
    exact Nat.ceil_pos.mpr (div_pos (Real.log_pos harg1) hD)
  have hQ : 1 ≤ Q := by rw [hQeq]; exact Nat.ceil_pos.mpr hxpos
  have hxQ : x ≤ (Q : ℝ) := by rw [hQeq]; exact Nat.le_ceil x
  have hQx : (Q : ℝ) < x + 1 := by rw [hQeq]; exact Nat.ceil_lt_add_one hx0
  have hDQ : D * (Q : ℝ) ≥ Real.log (16 * B0 * (T : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hxQ hD.le
    calc
      Real.log (16 * B0 * (T : ℝ)) = D * x := by dsimp [x]; field_simp
      _ ≤ D * (Q : ℝ) := hm
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
      policyFactor zeta ^ (-(Q : ℤ)) ≤ 1 / 16 := by
    rw [show B0 * (T : ℝ) * mixingAlpha t0 ^ (2 * Q) *
        policyFactor zeta ^ (-(Q : ℤ)) =
        (B0 * (T : ℝ)) *
          (mixingAlpha t0 ^ (2 * Q) * policyFactor zeta ^ (-(Q : ℤ))) by ring,
      hcombined]
    have hexp : Real.exp (-D * (Q : ℝ)) ≤
        (16 * B0 * (T : ℝ))⁻¹ := by
      calc
        Real.exp (-D * (Q : ℝ)) ≤
            Real.exp (-Real.log (16 * B0 * (T : ℝ))) :=
          Real.exp_le_exp.mpr (by nlinarith [neg_le_neg hDQ])
        _ = (16 * B0 * (T : ℝ))⁻¹ := by
          rw [Real.exp_neg, Real.exp_log
            (mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hB0)) hTreal)]
    calc
      B0 * (T : ℝ) * Real.exp (-D * (Q : ℝ)) ≤
          B0 * (T : ℝ) * (16 * B0 * (T : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (le_trans zero_le_one hB0) hTreal.le)
      _ = 1 / 16 := by field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hB0), ne_of_gt hTreal]
  have halphaQ : mixingAlpha t0 ^ Q ≥
      mixingAlpha t0 * (16 * B0 * (T : ℝ)) ^ (-(1 / t0) / D) := by
    have hmul := mul_lt_mul_of_neg_left hQx (neg_lt_zero.mpr (one_div_pos.mpr ht0))
    have hexp := Real.exp_le_exp.mpr (le_of_lt hmul)
    calc
      mixingAlpha t0 * (16 * B0 * (T : ℝ)) ^ (-(1 / t0) / D) =
          Real.exp (-(1 / t0) * (x + 1)) := by
        rw [Real.rpow_def_of_pos
          (mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hB0)) hTreal),
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
  have hden0 : 0 < 1 - mixingAlpha t0 ^ (Q + 1) := by
    nlinarith [pow_lt_one₀ halpha0.le halpha1 (by omega : Q + 1 ≠ 0)]
  have hmass : (1 - mixingAlpha t0) * mixingAlpha t0 ^ Q ≤
      terminalMass t0 Q ht0 hQ := by
    unfold terminalMass
    apply (le_div_iff₀ hden0).2
    have hn : 0 ≤ (1 - mixingAlpha t0) * mixingAlpha t0 ^ Q := by positivity
    nlinarith [pow_nonneg halpha0.le (Q + 1)]
  have hsep : rewardAmplitude t0 ht0 * signBias 2 (by norm_num) *
      (1 - mixingAlpha t0) * mixingAlpha t0 *
        (16 * B0 * (T : ℝ)) ^ (-(1 / t0) / D) ≤
      separationRadius t0 2 Q ht0 (by norm_num) hQ := by
    unfold separationRadius
    have hs : 0 ≤ rewardAmplitude t0 ht0 * signBias 2 (by norm_num) := by
      dsimp [rewardAmplitude, signBias]
      positivity
    calc
      _ = (rewardAmplitude t0 ht0 * signBias 2 (by norm_num)) *
          ((1 - mixingAlpha t0) * (mixingAlpha t0 *
            (16 * B0 * (T : ℝ)) ^ (-(1 / t0) / D))) := by ring
      _ ≤ (rewardAmplitude t0 ht0 * signBias 2 (by norm_num)) *
          ((1 - mixingAlpha t0) * mixingAlpha t0 ^ Q) := by
        gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass hs
  have hpowSplit : (16 * B0 * (T : ℝ)) ^ (-rateExponent t0 zeta) =
      (16 * B0) ^ (-rateExponent t0 zeta) *
        (T : ℝ) ^ (-rateExponent t0 zeta) := by
    rw [Real.mul_rpow
      (mul_nonneg (by norm_num) (le_trans zero_le_one hB0)) hTreal.le]
  have hsep0 : 0 ≤ separationRadius t0 2 Q ht0 (by norm_num) hQ := by
    unfold separationRadius
    have hr : 0 ≤ rewardAmplitude t0 ht0 := by
      unfold rewardAmplitude
      positivity
    have hs : 0 ≤ signBias 2 (by norm_num) := by norm_num [signBias]
    have hm : 0 ≤ terminalMass t0 Q ht0 hQ := by
      unfold terminalMass
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr halpha1.le) (pow_nonneg halpha0.le _))
        hden0.le
    positivity
  have hsepSq := (sq_le_sq₀ (show (0 : ℝ) ≤
      rewardAmplitude t0 ht0 * signBias 2 (by norm_num) *
        (1 - mixingAlpha t0) * mixingAlpha t0 *
          (16 * B0 * (T : ℝ)) ^ (-(1 / t0) / D) by
            have hB00 : 0 ≤ B0 := le_trans zero_le_one hB0
            have hrew : 0 ≤ rewardAmplitude t0 ht0 := by
              unfold rewardAmplitude
              positivity
            have hsign : 0 ≤ signBias 2 (by norm_num) := by norm_num [signBias]
            positivity) hsep0).2 hsep
  refine ⟨hQ, hKLreal, ?_⟩
  dsimp [csep]
  have hrpowSq : ((16 * B0 * (T : ℝ)) ^ (-(1 / t0) / D)) ^ 2 =
      (16 * B0 * (T : ℝ)) ^ (-rateExponent t0 zeta) := by
    rw [← Real.rpow_mul_natCast (by
      exact mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one hB0)) hTreal.le)]
    congr 1
    rw [hbeta]
    push_cast
    ring
  calc
    _ = (rewardAmplitude t0 ht0 * signBias 2 (by norm_num) *
        (1 - mixingAlpha t0) * mixingAlpha t0) ^ 2 *
          (16 * B0 * (T : ℝ)) ^ (-rateExponent t0 zeta) := by
      rw [hpowSplit]
      ring
    _ = (rewardAmplitude t0 ht0 * signBias 2 (by norm_num) *
        (1 - mixingAlpha t0) * mixingAlpha t0 *
          (16 * B0 * (T : ℝ)) ^ (-(1 / t0) / D)) ^ 2 := by
      rw [← hrpowSq]
      ring
    _ ≤ _ := hsepSq

-- @node: signedDepthModel_obsLaw_ac
/-- The two signed-depth observed laws are mutually supported. -/
lemma signedDepthModel_obsLaw_ac {T Q : Nat} {t0 zeta : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hQ : 1 ≤ Q) :
    obsLaw (signedDepthModel T Q t0 zeta 2 true ht0 hzeta (by norm_num) hQ) ≪
      obsLaw (signedDepthModel T Q t0 zeta 2 false ht0 hzeta (by norm_num) hQ) := by
  rw [signedDepthModel_obsLaw true ht0 hzeta (by norm_num) hQ,
    signedDepthModel_obsLaw false ht0 hzeta (by norm_num) hQ]
  apply Measure.AbsolutelyContinuous.map
  · exact CausalSmith.Stat.PomdpLatentOverlapMinimax.embed_absolutelyContinuous
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.absolutelyContinuous_of_fullSupport
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_fullSupportObs
          ht0 hzeta (by norm_num))
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_fullSupportObs
          ht0 hzeta (by norm_num))) rfl
  · fun_prop

-- @node: capped_signedDepth_converse
/-- A clone budget meeting the collision tolerance turns the signed-depth pair into
a lower bound for the cardinality-capped audited minimax risk. -/
lemma capped_signedDepth_converse {t0 zeta B0 : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hconst : SignedDepthConstantAtTwo t0 zeta B0) :
    ∀ delta0 : ℝ, delta0 ∈ Set.Ioo (0 : ℝ) (3 / 8) →
      ∃ c : ℝ, 0 < c ∧ ∀ (T N m : Nat) (eta : ℝ), 1 ≤ T →
        eta ∈ Set.Icc (0 : ℝ) 1 → 1 ≤ m →
        collisionEnvelope T eta m ≤ delta0 →
        signedDepthCardinality T t0 zeta B0 * m ≤ N →
        c * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
          cappedMinimaxRisk T N t0 zeta eta := by
  intro delta0 hdelta0
  rcases signedDepthConstantAtTwo_spec hconst with ⟨hB0, hwitness⟩
  obtain ⟨csep, hcsep, hquant⟩ :=
    signedDepthHorizon_quantitative ht0 hzeta hB0
  let gap : ℝ := 3 / 4 - 2 * delta0
  have hgap : 0 < gap := by dsimp [gap]; linarith [hdelta0.2]
  let c : ℝ := csep * gap / 2
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro T N m eta hT heta hm hcollision hcap
  let Q := signedDepthHorizon T t0 zeta B0
  have hq := hquant T hT
  have hQ : 1 ≤ Q := hq.1
  let Mp := signedDepthModel T Q t0 zeta 2 true ht0 hzeta (by norm_num) hQ
  let Mm := signedDepthModel T Q t0 zeta 2 false ht0 hzeta (by norm_num) hQ
  have hwit := hwitness T Q hQ ht0 hzeta
  have hMp : FixedOverlapClass t0 zeta 2 Mp := by simpa [Mp] using hwit.1
  have hMm : FixedOverlapClass t0 zeta 2 Mm := by simpa [Mm] using hwit.2.1
  let a := separationRadius t0 2 Q ht0 (by norm_num) hQ
  have ha : 0 ≤ a := by
    dsimp [a]
    unfold separationRadius rewardAmplitude signBias terminalMass
    have halpha0 : 0 < mixingAlpha t0 := by unfold mixingAlpha; positivity
    have halpha1 : mixingAlpha t0 < 1 := by
      rw [mixingAlpha, Real.exp_lt_one_iff]
      exact neg_neg_of_pos (one_div_pos.mpr ht0)
    have hden : 0 < 1 - mixingAlpha t0 ^ (Q + 1) := by
      nlinarith [pow_lt_one₀ halpha0.le halpha1 (by omega : Q + 1 ≠ 0)]
    positivity
  have hplus : targetValue Mp = a := by simpa [Mp, a] using hwit.2.2.1
  have hminus : targetValue Mm = -a := by simpa [Mm, a] using hwit.2.2.2.1
  have hKL : InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm) ≤
      ENNReal.ofReal (1 / 16 : ℝ) := by
    have hraw : InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm) ≤
        ENNReal.ofReal (B0 * T * mixingAlpha t0 ^ (2 * Q) *
          policyFactor zeta ^ (-(Q : ℤ))) := by
      simpa [Mp, Mm] using hwit.2.2.2.2.2.2
    exact hraw.trans (ENNReal.ofReal_le_ofReal hq.2.1)
  have hfin : InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  have hac : obsLaw Mp ≪ obsLaw Mm := by
    simpa [Mp, Mm] using signedDepthModel_obsLaw_ac ht0 hzeta hQ
  letI : IsProbabilityMeasure (obsLaw Mp) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map (by
      unfold obsProj currentState actionAt rewardAt
      fun_prop)
  letI : IsProbabilityMeasure (obsLaw Mm) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map (by
      unfold obsProj currentState actionAt rewardAt
      fun_prop)
  have hKLreal : (InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm)).toReal ≤ 1 / 16 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL
    simpa using this
  have htvObs : Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) ≤ 1 / 4 := by
    have hpinsker := Causalean.Stat.pinskerBound_of_ac_of_ne_top
      (obsLaw Mp) (obsLaw Mm) hac hfin
    unfold Causalean.Stat.PinskerBound at hpinsker
    have hsqrt : Real.sqrt
        ((InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm)).toReal / 2) ≤ 1 / 4 := by
      have hnonneg : 0 ≤
          (InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm)).toReal / 2 := by positivity
      have hsq := Real.sq_sqrt hnonneg
      have hs0 := Real.sqrt_nonneg
          ((InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm)).toReal / 2)
      nlinarith
    exact hpinsker.trans hsqrt
  unfold cappedMinimaxRisk
  let zeroEst : AuditedEstimator T := ⟨fun _ _ _ _ _ _ => 0, by
    constructor
    · intros
      fun_prop
    · intros
      norm_num⟩
  letI : Nonempty (AuditedEstimator T) := ⟨zeroEst⟩
  apply Causalean.Stat.le_minimaxValue
  intro est
  have hb : Mp.b = Mm.b := by
    dsimp [Mp, Mm, signedDepthModel, embedBinary]
    rw [show (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFamily
        T t0 zeta 2 Q true ht0 hzeta (by norm_num) hQ).b =
        CausalSmith.Stat.PomdpLatentOverlapMinimax.actionOnePolicy
          (1 / policyFactor zeta) by
      exact CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_behaviour_eq_actionOne
        ht0 hzeta (by norm_num) hQ,
      show (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFamily
        T t0 zeta 2 Q false ht0 hzeta (by norm_num) hQ).b =
        CausalSmith.Stat.PomdpLatentOverlapMinimax.actionOnePolicy
          (1 / policyFactor zeta) by
      exact CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_behaviour_eq_actionOne
        ht0 hzeta (by norm_num) hQ]
  have he : Mp.e = Mm.e := by
    dsimp [Mp, Mm, signedDepthModel, embedBinary]
    rw [show (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFamily
        T t0 zeta 2 Q true ht0 hzeta (by norm_num) hQ).e =
        CausalSmith.Stat.PomdpLatentOverlapMinimax.actionOnePolicy 1 by
      exact CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_target_eq_actionOne
        ht0 hzeta (by norm_num) hQ,
      show (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFamily
        T t0 zeta 2 Q false ht0 hzeta (by norm_num) hQ).e =
        CausalSmith.Stat.PomdpLatentOverlapMinimax.actionOnePolicy 1 by
      exact CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_target_eq_actionOne
        ht0 hzeta (by norm_num) hQ]
  have htransfer := overflow_safe_all_procedure_transfer Mp Mm (by omega) hm
    (by norm_num) hMp hMm ⟨hb, he⟩ eta a heta ha hplus hminus
  let est0 : AuditedRecord T 1 (2 * (Q + 1) * m) 2 → ℝ :=
    est.1 1 (2 * (Q + 1) * m) 2 Mp.b Mp.e
  have hest0 : Measurable est0 := est.2.1 _ _ _ _ _
  obtain ⟨v, π, hvclass, hvrisk⟩ := htransfer.2.2 est0 hest0
  let Mv := cloneModel (if v then Mp else Mm) hm π
  let iv : HWIndex T t0 zeta := {
    nX := 1
    nH := 2 * (Q + 1) * m
    k := 2
    nX_pos := by norm_num
    nH_pos := Nat.mul_pos (by omega) (Nat.zero_lt_of_lt hm)
    k_pos := by norm_num
    raw := Mv
    mem := by simpa [Mv] using hvclass.1 }
  have hivcap : iv.nX * iv.nH ≤ N := by
    dsimp [iv]
    simpa [signedDepthCardinality, Q, Nat.mul_assoc] using hcap
  let ivc : {i : HWIndex T t0 zeta // i.nX * i.nH ≤ N} := ⟨iv, hivcap⟩
  have htoWorst : auditedRisk eta est iv ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_est : AuditedEstimator T)
          (i : {i : HWIndex T t0 zeta // i.nX * i.nH ≤ N}) =>
            auditedRisk eta _est i.1) est := by
    exact Causalean.Stat.le_worstCaseRisk
      (risk := fun (_est : AuditedEstimator T)
        (i : {i : HWIndex T t0 zeta // i.nX * i.nH ≤ N}) =>
          auditedRisk eta _est i.1)
      (bddAbove_range_cappedAuditedRisk heta est) ivc
  have htvMix : Causalean.Stat.tvDist
      (permutationMixture Mp hm eta) (permutationMixture Mm hm eta) ≤
      1 / 4 + 2 * delta0 := by
    exact htransfer.1.trans (by linarith)
  have haff : gap ≤ 1 - Causalean.Stat.tvDist
      (permutationMixture Mp hm eta) (permutationMixture Mm hm eta) := by
    dsimp [gap]
    linarith
  have hrate : csep * (T : ℝ) ^ (-rateExponent t0 zeta) ≤ a ^ 2 := by
    simpa [Q, a] using hq.2.2
  have hreal : c * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
      (a ^ 2 / 2) * (1 - Causalean.Stat.tvDist
        (permutationMixture Mp hm eta) (permutationMixture Mm hm eta)) := by
    dsimp [c]
    have hpow : 0 ≤ (T : ℝ) ^ (-rateExponent t0 zeta) := Real.rpow_nonneg (by positivity) _
    nlinarith [mul_le_mul_of_nonneg_right hrate hgap.le,
      mul_le_mul_of_nonneg_left haff (sq_nonneg a)]
  have hriskLower : ENNReal.ofReal (c * (T : ℝ) ^ (-rateExponent t0 zeta)) ≤
      Causalean.Stat.sqRiskLIntegral (auditedLaw eta Mv) est0 (targetValue Mv) :=
    (ENNReal.ofReal_le_ofReal hreal).trans (by simpa [Mv] using hvrisk)
  have hbound : ∀ w, |est0 w - targetValue Mv| ≤ 2 := by
    intro w
    have he := est.2.2 1 (2 * (Q + 1) * m) 2 Mp.b Mp.e w
    have ht := targetValue_mem_unit_hw hvclass.1
    rw [abs_le]
    constructor <;> linarith [he.1, he.2, ht.1, ht.2]
  have hint : Integrable (fun w => (est0 w - targetValue Mv) ^ 2)
      (auditedLaw eta Mv) := by
    letI : IsProbabilityMeasure (auditedLaw eta Mv) := auditedLaw_prob Mv eta heta
    apply Integrable.of_bound
      ((hest0.sub measurable_const).pow_const 2).aestronglyMeasurable 4
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [← sq_abs]
    change |est0 w - targetValue Mv| ^ 2 ≤ 4
    have hp : 0 ≤ (2 - |est0 w - targetValue Mv|) *
        (2 + |est0 w - targetValue Mv|) :=
      mul_nonneg (by linarith [hbound w]) (by positivity)
    nlinarith
  rw [sqRiskLIntegral_eq_ofReal_sqRisk _ _ _ hint] at hriskLower
  have hriskReal : c * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
      Causalean.Stat.sqRisk (auditedLaw eta Mv) est0 (targetValue Mv) := by
    exact (ENNReal.ofReal_le_ofReal_iff
      (integral_nonneg fun _ => sq_nonneg _)).mp hriskLower
  have hMvb : Mv.b = Mp.b := by
    dsimp [Mv, cloneModel]
    split <;> simp_all
  have hMve : Mv.e = Mp.e := by
    dsimp [Mv, cloneModel]
    split <;> simp_all
  have hestEq : est.1 1 (2 * (Q + 1) * m) 2 Mv.b Mv.e = est0 := by
    rw [hMvb, hMve]
  have htoIv : c * (T : ℝ) ^ (-rateExponent t0 zeta) ≤ auditedRisk eta est iv := by
    change c * (T : ℝ) ^ (-rateExponent t0 zeta) ≤
      Causalean.Stat.sqRisk (auditedLaw eta Mv)
        (est.1 1 (2 * (Q + 1) * m) 2 Mv.b Mv.e) (targetValue Mv)
    rw [hestEq]
    exact hriskReal
  exact htoIv.trans htoWorst

end CausalSmith.Stat.PomdpStateauditMinimax
