module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.InferenceMidpointBias
public import Causalean.Stat.Concentration.TailBounds.Hoeffding
public import Causalean.Stat.Sample.PiTransport

/-! Product-law concentration of the equal-width midpoint statistic. -/

public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

private lemma midpointWeightedRow_measurable' (ε : ℝ) (K : ℕ) :
    Measurable (midpointWeightedRow ε K) := by
  unfold midpointWeightedRow equalWidthMidpoint
  apply Measurable.ite
  · exact measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const
  · fun_prop
  · fun_prop

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,K,hK,z), this result [establishes the stated mathematical conclusion](goal). -/
lemma midpointWeightedRow_mem_Icc {ε : ℝ} (hOverlap : Overlap ε)
    (K : ℕ) (hK : 0 < K) (z : Observation K) :
    midpointWeightedRow ε K z ∈ Icc (-ε⁻¹) ε⁻¹ := by
  have hm := equalWidthMidpoint_mem_Icc hOverlap K hK z.1
  have hε : 0 < ε := hOverlap.1
  have hm0 : 0 < equalWidthMidpoint ε K z.1 := hε.trans_le hm.1
  have hm1 : 0 < 1 - equalWidthMidpoint ε K z.1 := by
    linarith [hm.2, hOverlap.1]
  by_cases ha : z.2.1 = true
  · simp only [midpointWeightedRow, ha, ↓reduceIte]
    constructor
    · exact (div_nonneg z.2.2.property.1 hm0.le).trans' (neg_nonpos.mpr (inv_nonneg.mpr hε.le))
    · have hinv := (inv_le_inv₀ hm0 hε).mpr hm.1
      calc
        (z.2.2 : ℝ) / equalWidthMidpoint ε K z.1 ≤
            1 / equalWidthMidpoint ε K z.1 :=
          div_le_div_of_nonneg_right z.2.2.property.2 hm0.le
        _ ≤ ε⁻¹ := by simpa [one_div] using hinv
  · have ha' : z.2.1 = false := Bool.eq_false_of_not_eq_true ha
    simp only [midpointWeightedRow, ha', Bool.false_eq_true, ↓reduceIte]
    have hmLower : ε ≤ 1 - equalWidthMidpoint ε K z.1 := by
      linarith [hm.2]
    have hinv := (inv_le_inv₀ hm1 hε).mpr hmLower
    have hy : (z.2.2 : ℝ) / (1 - equalWidthMidpoint ε K z.1) ≤ ε⁻¹ := by
      calc
        (z.2.2 : ℝ) / (1 - equalWidthMidpoint ε K z.1) ≤
            1 / (1 - equalWidthMidpoint ε K z.1) :=
          div_le_div_of_nonneg_right z.2.2.property.2 hm1.le
        _ ≤ ε⁻¹ := by simpa [one_div] using hinv
    rw [neg_div]
    constructor
    · exact neg_le_neg hy
    · exact (neg_nonpos.mpr (div_nonneg z.2.2.property.1 hm1.le)).trans
        (inv_nonneg.mpr hε.le)

private lemma midpointRadius_hoeffding_rhs_le {ε α : ℝ}
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (n : ℕ) (hn : 0 < n) :
    2 * Real.exp
      (-2 * n * ((4 / ε) * Real.sqrt (Real.log (4 / α) / n)) ^ 2 /
        (ε⁻¹ - -ε⁻¹) ^ 2) ≤ α := by
  have hε : 0 < ε := hOverlap.1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq : 1 < 4 / α := by
    rw [lt_div_iff₀ hα.1]
    linarith [hα.2]
  have hlog : 0 ≤ Real.log (4 / α) := (Real.log_pos hq).le
  have hexponent :
      -2 * (n : ℝ) * ((4 / ε) * Real.sqrt (Real.log (4 / α) / n)) ^ 2 /
          (ε⁻¹ - -ε⁻¹) ^ 2 =
        -8 * Real.log (4 / α) := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hlog hnR.le)]
    field_simp
    ring
  rw [hexponent]
  have hlogPow : Real.log ((4 / α) ^ 8) = 8 * Real.log (4 / α) := by
    rw [Real.log_pow]
    norm_num
  rw [show -8 * Real.log (4 / α) = -Real.log ((4 / α) ^ 8) by
      rw [hlogPow]
      ring]
  rw [Real.exp_neg, Real.exp_log (pow_pos (by positivity : 0 < 4 / α) 8)]
  have hα1 : α ≤ 1 := by linarith [hα.2]
  have hpow : α ^ 8 ≤ α := by
    calc
      α ^ 8 = α * α ^ 7 := by ring
      _ ≤ α * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα1) hα.1.le
      _ = α := mul_one _
  rw [← inv_pow, show (4 / α)⁻¹ = α / 4 by field_simp]
  rw [div_pow]
  calc
    2 * (α ^ 8 / 4 ^ 8) ≤ 2 * (α / 4 ^ 8) := by
      gcongr
    _ ≤ α := by norm_num; linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hOverlap,hα,K,n,hK,hn,P), this result [establishes the stated mathematical conclusion](goal). -/
lemma midpointWeightedCenter_deviation_probability_le
    {ε α : ℝ} (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (K n : ℕ) (hK : 0 < K) (hn : 0 < n)
    (P : Measure (Observation K)) [IsProbabilityMeasure P] :
    (Measure.pi (fun _ : Fin n => P)).real
      {x | (4 / ε) * Real.sqrt (Real.log (4 / α) / n) ≤
        |midpointWeightedCenter ε n K x -
          ∫ z, midpointWeightedRow ε K z ∂P|} ≤ α := by
  let S := Causalean.Stat.iidSample_infinitePi P
  let ψ : (ℕ → Observation K) → (Fin n → Observation K) :=
    fun ω k => S.Z k ω
  let t := (4 / ε) * Real.sqrt (Real.log (4 / α) / n)
  let A : Set (Fin n → Observation K) :=
    {x | t ≤ |midpointWeightedCenter ε n K x -
      ∫ z, midpointWeightedRow ε K z ∂P|}
  have hψ : Measurable ψ := Causalean.Stat.iidSample_finN_measurable S n
  have hA : MeasurableSet A := by
    dsimp [A, t]
    apply measurableSet_le measurable_const
    have hcenter : Measurable (midpointWeightedCenter ε n K) := by
      rw [show midpointWeightedCenter ε n K = fun x : TrialSample n K =>
          (n : ℝ)⁻¹ * ∑ i : Fin n, midpointWeightedRow ε K (x i) from
        funext (midpointWeightedCenter_eq_rowMean ε n K)]
      exact measurable_const.mul (Finset.measurable_fun_sum Finset.univ
        fun i _ => (midpointWeightedRow_measurable' ε K).comp
          (measurable_pi_apply i))
    exact (hcenter.sub measurable_const).abs
  have hpush : (Measure.infinitePi (fun _ : ℕ => P)).map ψ =
      Measure.pi (fun _ : Fin n => P) :=
    Causalean.Stat.iidSample_finN_pushforward S n
  have hmeasure : (Measure.infinitePi (fun _ : ℕ => P)).real (ψ ⁻¹' A) =
      (Measure.pi (fun _ : Fin n => P)).real A := by
    simp only [measureReal_def]
    rw [← hpush, Measure.map_apply hψ hA]
  have hevent : ψ ⁻¹' A =
      {ω | t ≤ |S.sampleMean (midpointWeightedRow ε K) n ω -
        ∫ z, midpointWeightedRow ε K z ∂P|} := by
    ext ω
    dsimp [A, ψ, t, Causalean.Stat.IIDSample.sampleMean]
    rw [midpointWeightedCenter_eq_rowMean]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => midpointWeightedRow ε K (S.Z i ω)) n]
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact mul_nonneg (div_nonneg (by norm_num) hOverlap.1.le)
      (Real.sqrt_nonneg _)
  have htail := Causalean.Stat.Concentration.hoeffding_abs_ge S
    (midpointWeightedRow_measurable' ε K)
    (a := -ε⁻¹) (b := ε⁻¹)
    (by have hi : 0 < ε⁻¹ := inv_pos.mpr hOverlap.1; linarith)
    (ae_of_all P (midpointWeightedRow_mem_Icc hOverlap K hK)) n hn ht0
  have hrhs := midpointRadius_hoeffding_rhs_le hOverlap hα n hn
  change (Measure.pi (fun _ : Fin n => P)).real A ≤ α
  rw [← hmeasure, hevent]
  exact htail.trans hrhs

end
end CausalSmith.PartialID.UnlinkedPropensityAte
