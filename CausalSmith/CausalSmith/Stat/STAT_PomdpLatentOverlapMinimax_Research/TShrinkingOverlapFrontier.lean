module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.TUniformOverlapFrontier

set_option linter.style.longLine false
set_option maxHeartbeats 800000

/-! # Shrinking-overlap phase diagram -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open Filter
open scoped Topology

/-- The local-radius rate surface written in terms of the excess `delta_T`. -/
noncomputable def localFrontierRate (T : Nat) (t0 zeta : ℝ) (delta : Nat → ℝ) : ℝ :=
  (T : ℝ)⁻¹ + (T : ℝ) ^ (-rateExponent t0 zeta) *
    delta T ^ (2 * (1 - rateExponent t0 zeta))

/-- The local-depth formula stated in the shrinking-radius theorem. -/
noncomputable def shrinkingDepth (T : Nat) (t0 zeta : ℝ) (delta : Nat → ℝ) : Nat :=
  if (T : ℝ) * delta T ^ 2 ≤ 1 then 0
  else min (T / 2) (Int.toNat ⌊Real.log ((T : ℝ) * delta T ^ 2) /
    (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))⌋)

-- @node: thm:shrinking-overlap-frontier
/-- For every deterministic nonnegative radius excess tending to zero, the local
minimax risk has the stated two-term rate and is attained by the local-depth PHIW
estimator, with constants depending only on `t0,zeta`. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
theorem shrinking_overlap_frontier {t0 zeta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ cLower cUpper : ℝ, 0 < cLower ∧ cLower ≤ cUpper ∧
      ∀ (delta : Nat → ℝ), (∀ T, 0 ≤ delta T) →
        Tendsto delta atTop (nhds 0) →
        (∃ TStar : Nat, 1 ≤ TStar ∧ ∀ T ≥ TStar,
          cLower * localFrontierRate T t0 zeta delta ≤
            minimaxRisk T t0 zeta (1 + delta T) ∧
          minimaxRisk T t0 zeta (1 + delta T) ≤
            cUpper * localFrontierRate T t0 zeta delta ∧
          Causalean.Stat.worstCaseRisk
            (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := 1 + delta T))
            (phiwObservable (T := T) (shrinkingDepth T t0 zeta delta)) ≤
              cUpper * localFrontierRate T t0 zeta delta) ∧
        ((∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ (T : Nat) in atTop, (T : ℝ) * delta T ^ 2 ≤ D) →
          ∃ cImmediate : ℝ, 0 < cImmediate ∧
            ∀ᶠ (T : Nat) in atTop,
              Causalean.Stat.worstCaseRisk
                (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := 1 + delta T))
                (phiwObservable (T := T) 0) ≤ cImmediate / T) := by
  obtain ⟨cL, cU, hcL, hLcU, ⟨TU, hTU, hfront⟩, himmediate⟩ :=
    uniform_overlap_frontier ht0 hzeta
  obtain ⟨cR, hcR, TR, hTR, hrate⟩ := radiusAdaptiveDepth_rate ht0 hzeta
  let p : ℝ := 2 * (1 - rateExponent t0 zeta)
  have hbeta0 : 0 < rateExponent t0 zeta := by
    unfold rateExponent
    positivity
  have hbeta1 : rateExponent t0 zeta < 1 := by
    unfold rateExponent
    rw [div_lt_one (by positivity)]
    nlinarith [mul_pos ht0 hzeta]
  have hp : 0 < p := by dsimp [p]; linarith
  let a : ℝ := (1 / 2 : ℝ) ^ p
  have ha : 0 < a := by dsimp [a]; positivity
  let cLower := cL * a
  let A : ℝ := max 4 (max
    (2 * policyFactor zeta * (1 + 4 / (policyFactor zeta - 1)))
    (8 / (1 - mixingAlpha t0)))
  have halpha1 : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have hL1 : 1 < policyFactor zeta := by
    rw [policyFactor, Real.one_lt_exp_iff]
    exact hzeta
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let cAttain := A * (cR + 1)
  have hcAttain : 0 < cAttain := mul_pos hA (by linarith)
  let cUpper := max cU cAttain
  have hcLower : 0 < cLower := mul_pos hcL ha
  have hcLowerUpper : cLower ≤ cUpper := by
    have ha1 : a ≤ 1 := by
      dsimp [a]
      exact Real.rpow_le_one (by norm_num) (by norm_num) hp.le
    dsimp [cLower, cUpper]
    calc
      cL * a ≤ cL * 1 := by gcongr
      _ = cL := by ring
      _ ≤ cU := hLcU
      _ ≤ max cU cAttain := le_max_left _ _
  refine ⟨cLower, cUpper, hcLower, hcLowerUpper, ?_⟩
  intro delta hdelta hdelta0
  have hevDelta : ∀ᶠ T : Nat in atTop, delta T < 1 := by
    have hnhds : Set.Iio (1 : ℝ) ∈ nhds 0 := Iio_mem_nhds (by norm_num)
    exact hdelta0.eventually hnhds
  rw [eventually_atTop] at hevDelta
  obtain ⟨TD, hTD⟩ := hevDelta
  let TStar := max (max TU TR) TD
  have hmain : ∃ TStar : Nat, 1 ≤ TStar ∧ ∀ T ≥ TStar,
      cLower * localFrontierRate T t0 zeta delta ≤
        minimaxRisk T t0 zeta (1 + delta T) ∧
      minimaxRisk T t0 zeta (1 + delta T) ≤
        cUpper * localFrontierRate T t0 zeta delta ∧
      Causalean.Stat.worstCaseRisk
        (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := 1 + delta T))
        (phiwObservable (T := T) (shrinkingDepth T t0 zeta delta)) ≤
          cUpper * localFrontierRate T t0 zeta delta := by
    refine ⟨TStar, hTU.trans ((le_max_left TU TR).trans (le_max_left _ _)), ?_⟩
    intro T hT
    have hTU' : TU ≤ T := (le_max_left TU TR).trans (le_max_left (max TU TR) TD) |>.trans hT
    have hTR' : TR ≤ T := (le_max_right TU TR).trans (le_max_left (max TU TR) TD) |>.trans hT
    have hTD' : TD ≤ T := (le_max_right (max TU TR) TD).trans hT
    have hd0 := hdelta T
    have hd1 := hTD T hTD'
    have hC : 1 ≤ 1 + delta T := by linarith
    obtain ⟨hlower, hupper, hattain⟩ := hfront (1 + delta T) hC T hTU'
    have hq : overlapRadius (1 + delta T) = delta T / (1 + delta T) := by
      unfold overlapRadius
      congr 1
      ring
    have hq0 : 0 ≤ overlapRadius (1 + delta T) := by rw [hq]; positivity
    have hq_le : overlapRadius (1 + delta T) ≤ delta T := by
      rw [hq]
      exact (div_le_iff₀ (by linarith : 0 < 1 + delta T)).2 (by nlinarith)
    have hdhalf : delta T / 2 ≤ overlapRadius (1 + delta T) := by
      rw [hq]
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < 1 + delta T)).2
      nlinarith
    have hpow_upper : overlapRadius (1 + delta T) ^ p ≤ delta T ^ p :=
      Real.rpow_le_rpow hq0 hq_le hp.le
    have hpow_lower : a * delta T ^ p ≤ overlapRadius (1 + delta T) ^ p := by
      have hbase := Real.rpow_le_rpow (by positivity : 0 ≤ delta T / 2) hdhalf hp.le
      have heq : (delta T / 2) ^ p = a * delta T ^ p := by
        rw [Real.div_rpow hd0 (by norm_num : (0 : ℝ) ≤ 2)]
        dsimp [a]
        rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      rwa [heq] at hbase
    have hrateLower : a * localFrontierRate T t0 zeta delta ≤
        frontierRate T t0 zeta (1 + delta T) := by
      unfold localFrontierRate frontierRate
      change a * ((T : ℝ)⁻¹ + (T : ℝ) ^ (-rateExponent t0 zeta) * delta T ^ p) ≤
        (T : ℝ)⁻¹ + (T : ℝ) ^ (-rateExponent t0 zeta) * overlapRadius (1 + delta T) ^ p
      have ha0 : 0 ≤ a := ha.le
      have ha1 : a ≤ 1 := by
        dsimp [a]
        exact Real.rpow_le_one (by norm_num) (by norm_num) hp.le
      have hTinv : 0 ≤ (T : ℝ)⁻¹ := by positivity
      have hTpow : 0 ≤ (T : ℝ) ^ (-rateExponent t0 zeta) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hpow_lower hTpow]
    have hrateUpper : frontierRate T t0 zeta (1 + delta T) ≤
        localFrontierRate T t0 zeta delta := by
      unfold localFrontierRate frontierRate
      change (T : ℝ)⁻¹ + (T : ℝ) ^ (-rateExponent t0 zeta) * overlapRadius (1 + delta T) ^ p ≤
        (T : ℝ)⁻¹ + (T : ℝ) ^ (-rateExponent t0 zeta) * delta T ^ p
      gcongr
    constructor
    · calc
        cLower * localFrontierRate T t0 zeta delta =
            cL * (a * localFrontierRate T t0 zeta delta) := by
              dsimp [cLower]
              ring
        _ ≤ cL * frontierRate T t0 zeta (1 + delta T) := by gcongr
        _ ≤ minimaxRisk T t0 zeta (1 + delta T) := hlower
    constructor
    · exact (hupper.trans (mul_le_mul_of_nonneg_left hrateUpper
        (hcL.le.trans hLcU))).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by unfold localFrontierRate; positivity))
    · let Caux : ℝ := 1 / (1 - delta T)
      have hCaux : 1 ≤ Caux := by
        dsimp [Caux]
        rw [le_div_iff₀ (by linarith : 0 < 1 - delta T)]
        linarith
      have hqaux : overlapRadius Caux = delta T := by
        dsimp [Caux]
        unfold overlapRadius
        field_simp [ne_of_gt (by linarith : 0 < 1 - delta T)]
        ring
      have hdepth : radiusAdaptiveDepth T t0 zeta Caux =
          shrinkingDepth T t0 zeta delta := by
        unfold radiusAdaptiveDepth shrinkingDepth
        rw [hqaux]
      have hrateT := hrate T hTR' Caux hCaux
      rw [hqaux, hdepth] at hrateT
      let k := shrinkingDepth T t0 zeta delta
      change delta T ^ 2 * mixingAlpha t0 ^ (2 * k) +
          policyFactor zeta ^ k / (T : ℝ) ≤
        cR * localFrontierRate T t0 zeta delta at hrateT
      have hk : k ≤ T / 2 := by
        dsimp [k]
        unfold shrinkingDepth
        split_ifs
        · omega
        · exact min_le_left _ _
      have hT1 : 1 ≤ T := hTU.trans hTU'
      have hkT : k < T := by omega
      have hkDepth : shrinkingDepth T t0 zeta delta < T := by
        simpa only [k] using hkT
      let m0 := parametricModel T t0 zeta (1 + delta T) false hT1 ht0 hzeta hC
      letI : Nonempty (ModelIndex T t0 zeta (1 + delta T)) := ⟨m0⟩
      simp [phiwObservable, hkDepth]
      apply Causalean.Stat.worstCaseRisk_le
      intro m
      have hrisk := radius_sensitive_phiw ht0 hzeta hC hT1 m.raw m.mem hk
      change Causalean.Stat.sqRisk (obsLaw m.raw)
        (phiwEstimator k hkT m.raw.b m.raw.e) (targetValue m.raw) ≤
          cUpper * localFrontierRate T t0 zeta delta
      have hqSq : overlapRadius (1 + delta T) ^ 2 ≤ delta T ^ 2 :=
        (sq_le_sq₀ hq0 hd0).2 hq_le
      have hmix : 0 ≤ mixingAlpha t0 ^ (2 * k) :=
        pow_nonneg (Real.exp_pos _).le _
      have hx : 0 ≤ delta T ^ 2 * mixingAlpha t0 ^ (2 * k) :=
        mul_nonneg (sq_nonneg _) hmix
      have hy : 0 ≤ policyFactor zeta ^ k / (T : ℝ) :=
        div_nonneg (pow_nonneg (Real.exp_pos _).le _) (Nat.cast_nonneg T)
      have hz : 0 ≤ (T : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg T)
      have hboundA :
          4 * overlapRadius (1 + delta T) ^ 2 * mixingAlpha t0 ^ (2 * k) +
            (2 / (T : ℝ)) *
              (policyFactor zeta ^ (k + 1) *
                  (1 + 4 / (policyFactor zeta - 1)) +
                4 / (1 - mixingAlpha t0)) ≤
            A * (delta T ^ 2 * mixingAlpha t0 ^ (2 * k) +
              policyFactor zeta ^ k / (T : ℝ) + (T : ℝ)⁻¹) := by
        have hA4 : 4 ≤ A := le_max_left _ _
        have hAvar : 2 * policyFactor zeta *
            (1 + 4 / (policyFactor zeta - 1)) ≤ A :=
          (le_max_left _ _).trans (le_max_right _ _)
        have hAmix : 8 / (1 - mixingAlpha t0) ≤ A :=
          (le_max_right _ _).trans (le_max_right _ _)
        have hs : 0 ≤ 1 + 4 / (policyFactor zeta - 1) := by positivity
        have hm : 0 ≤ 8 / (1 - mixingAlpha t0) := by positivity
        have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hT1))
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
        have hbias := mul_le_mul_of_nonneg_right hqSq hmix
        nlinarith [mul_nonneg (sub_nonneg.mpr hA4) hx,
          mul_nonneg (sub_nonneg.mpr hAvar) hy,
          mul_nonneg (sub_nonneg.mpr hAmix) hz]
      have hlocal0 : 0 ≤ localFrontierRate T t0 zeta delta := by
        unfold localFrontierRate
        positivity
      have hsum : delta T ^ 2 * mixingAlpha t0 ^ (2 * k) +
            policyFactor zeta ^ k / (T : ℝ) + (T : ℝ)⁻¹ ≤
          (cR + 1) * localFrontierRate T t0 zeta delta := by
        have hinv : (T : ℝ)⁻¹ ≤ localFrontierRate T t0 zeta delta := by
          unfold localFrontierRate
          exact le_add_of_nonneg_right (by positivity)
        nlinarith [hrateT]
      calc
        Causalean.Stat.sqRisk (obsLaw m.raw)
            (phiwEstimator k hkT m.raw.b m.raw.e) (targetValue m.raw) ≤ _ := hrisk
        _ ≤ A * (delta T ^ 2 * mixingAlpha t0 ^ (2 * k) +
              policyFactor zeta ^ k / (T : ℝ) + (T : ℝ)⁻¹) := hboundA
        _ ≤ A * ((cR + 1) * localFrontierRate T t0 zeta delta) := by gcongr
        _ = cAttain * localFrontierRate T t0 zeta delta := by
          dsimp [cAttain]
          ring
        _ ≤ cUpper * localFrontierRate T t0 zeta delta := by
          gcongr
          exact le_max_right _ _
  refine ⟨hmain, ?_⟩
  intro hbounded
  apply himmediate (fun T ↦ 1 + delta T) (fun T ↦ by linarith [hdelta T])
  obtain ⟨D, hD, hev⟩ := hbounded
  refine ⟨D, hD, ?_⟩
  filter_upwards [hev] with T hT
  have hq0 : 0 ≤ overlapRadius (1 + delta T) := by
    unfold overlapRadius
    exact div_nonneg (by linarith [hdelta T]) (by linarith [hdelta T])
  have hqle : overlapRadius (1 + delta T) ≤ delta T := by
    unfold overlapRadius
    apply (div_le_iff₀ (by linarith [hdelta T] : 0 < 1 + delta T)).2
    nlinarith [hdelta T]
  have hsquare := (sq_le_sq₀ hq0 (hdelta T)).2 hqle
  nlinarith [mul_nonneg (Nat.cast_nonneg T) (sub_nonneg.mpr hsquare)]

end CausalSmith.Stat.PomdpLatentOverlapMinimax
