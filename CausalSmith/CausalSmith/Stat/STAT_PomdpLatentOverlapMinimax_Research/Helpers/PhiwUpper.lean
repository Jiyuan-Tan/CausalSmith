import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.BiasVariance

set_option linter.style.longLine false

/-! # Fixed-radius PHIW upper bound -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

-- @node: lem:phiw-upper
/-- At fixed positive mixing and policy-overlap scales and fixed latent-overlap radius,
the balanced PHIW estimator has worst-case squared risk of order `T^(-beta)`, uniformly
over both finite alphabet cardinalities and without a logarithmic loss. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma phiw_upper {t0 zeta C : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) :
    ∃ cStar : ℝ, 0 < cStar ∧
      ∃ TStar : Nat,
        (∀ T ≥ TStar,
          Causalean.Stat.worstCaseRisk
            (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := C))
            (phiwObservable (T := T) (historyDepth T t0 zeta)) ≤
          cStar * (T : ℝ) ^ (-rateExponent t0 zeta)) ∧
        ∀ T ≥ TStar, ∀ {nX nH : Nat} (M : RawPomdpExperiment T nX nH),
          LatentOverlapClass t0 zeta C M →
          variance (phiwRaw (historyDepth T t0 zeta) M.b M.e) (obsLaw M) ≤
            (2 / (T : ℝ)) *
              (policyFactor zeta ^ (historyDepth T t0 zeta + 1) *
                  (1 + 4 / (policyFactor zeta - 1)) +
                4 / (1 - mixingAlpha t0)) := by
  have halpha0 : 0 < mixingAlpha t0 := by
    unfold mixingAlpha
    positivity
  have halpha1 : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have hL1 : 1 < policyFactor zeta := by
    rw [policyFactor, Real.one_lt_exp_iff]
    exact hzeta
  have hbeta0 : 0 < rateExponent t0 zeta := by
    unfold rateExponent
    positivity
  have hbeta1 : rateExponent t0 zeta < 1 := by
    unfold rateExponent
    have hprod : 0 < t0 * zeta := mul_pos ht0 hzeta
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨c, hc, T0, hrate⟩ := historyDepth_rate ht0 hzeta
  let A : ℝ := 1 + 4 / (policyFactor zeta - 1)
  let B : ℝ := 4 / (1 - mixingAlpha t0)
  let D : ℝ := max 4 (2 * A)
  let cStar : ℝ := D * c + 2 * B
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left 4 (2 * A))
  have hcStar : 0 < cStar := by
    dsimp [cStar]
    positivity
  refine ⟨cStar, hcStar, max T0 1, ?_, ?_⟩
  intro T hT
  have hT0 : T0 ≤ T := (le_max_left T0 1).trans hT
  have hT1 : 1 ≤ T := (le_max_right T0 1).trans hT
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT1)
  have hk : historyDepth T t0 zeta ≤ T / 2 := by
    simp [historyDepth]
  have hkT : historyDepth T t0 zeta < T := by omega
  have hq : overlapRadius C ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · unfold overlapRadius
      exact div_nonneg (sub_nonneg.mpr hC) (by linarith)
    · unfold overlapRadius
      apply (div_le_one (by linarith)).2
      linarith
  have hq_sq : overlapRadius C ^ 2 ≤ 1 := by
    nlinarith [hq.1, hq.2]
  have hpowA : 0 ≤ mixingAlpha t0 ^ (2 * historyDepth T t0 zeta) := by positivity
  have hpowL : 0 ≤ policyFactor zeta ^ (historyDepth T t0 zeta + 1) := by positivity
  have hrateT := hrate T hT0
  have hTinvrate : (T : ℝ)⁻¹ ≤ (T : ℝ) ^ (-rateExponent t0 zeta) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num [hT1]) (by linarith)
  by_cases hclass : Nonempty (ModelIndex T t0 zeta C)
  · letI : Nonempty (ModelIndex T t0 zeta C) := hclass
    simp [phiwObservable, hkT]
    apply Causalean.Stat.worstCaseRisk_le
    intro m
    have hrisk := radius_sensitive_phiw ht0 hzeta hC hT1 m.raw m.mem hk
    change Causalean.Stat.sqRisk (obsLaw m.raw)
      (phiwEstimator (historyDepth T t0 zeta) hkT m.raw.b m.raw.e)
      (targetValue m.raw) ≤ cStar * (T : ℝ) ^ (-rateExponent t0 zeta)
    calc
      Causalean.Stat.sqRisk (obsLaw m.raw)
          (phiwEstimator (historyDepth T t0 zeta) hkT m.raw.b m.raw.e)
          (targetValue m.raw) ≤
          4 * overlapRadius C ^ 2 * mixingAlpha t0 ^
              (2 * historyDepth T t0 zeta) +
            (2 / (T : ℝ)) *
              (policyFactor zeta ^ (historyDepth T t0 zeta + 1) * A + B) := by
        simpa [A, B] using hrisk
      _ ≤ D * (mixingAlpha t0 ^ (2 * historyDepth T t0 zeta) +
            policyFactor zeta ^ (historyDepth T t0 zeta + 1) / (T : ℝ)) +
            2 * B * (T : ℝ)⁻¹ := by
        have hD4 : 4 ≤ D := le_max_left _ _
        have hD2A : 2 * A ≤ D := le_max_right _ _
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith [mul_le_mul_of_nonneg_right hq_sq hpowA,
          mul_le_mul_of_nonneg_right hD4 hpowA,
          mul_le_mul_of_nonneg_right hD2A
            (mul_nonneg hpowL (inv_nonneg.mpr hTpos.le))]
      _ ≤ D * (c * (T : ℝ) ^ (-rateExponent t0 zeta)) +
            2 * B * (T : ℝ) ^ (-rateExponent t0 zeta) := by
        gcongr
      _ = cStar * (T : ℝ) ^ (-rateExponent t0 zeta) := by
        dsimp [cStar]
        ring
  · letI : IsEmpty (ModelIndex T t0 zeta C) := not_nonempty_iff.mp hclass
    rw [Causalean.Stat.worstCaseRisk_of_isEmpty_class]
    exact mul_nonneg hcStar.le (Real.rpow_nonneg hTpos.le _)
  · intro T hT nX nH M hM
    have hT1 : 1 ≤ T := (le_max_right T0 1).trans hT
    have hk : historyDepth T t0 zeta ≤ T / 2 := by simp [historyDepth]
    exact variance_phiwRaw_le hT1 M hM hk
  -- @realizes \(c^\star\)(fixed-radius upper constant) @realizes \(T_\star\)(large-sample threshold)

end CausalSmith.Stat.PomdpLatentOverlapMinimax
