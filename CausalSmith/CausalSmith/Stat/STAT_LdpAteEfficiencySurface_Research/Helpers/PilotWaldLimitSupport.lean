module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAttainmentSupport
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotWeakLimitSupport
public import Causalean.Stat.Inference.Studentize

/-! # Varying-law support for pilot Wald limits

The standard studentization API uses one fixed sample space.  Pilot transcripts
change with the sample size, so this file supplies the corresponding CDF-level
converging-together and interval-probability adapters.
-/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory ProbabilityTheory Filter Set Causalean.Stat
open scoped Topology ENNReal

/-- CDF-level converging together for row-varying probability spaces. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:μ,S,T,hApprox,hT,hΦ), [the varying Law cdf converging together](goal).

Under the stated assumptions, the varying Law cdf converging together. -/
lemma varyingLaw_cdf_converging_together
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (S T : ∀ n, Ω n → ℝ) (Φ : ℝ → ℝ)
    (hApprox : ∀ η : ℝ, 0 < η →
      Tendsto (fun n => (μ n).real {z | η ≤ |S n z - T n z|})
        atTop (nhds 0))
    (hT : ∀ x : ℝ,
      Tendsto (fun n => (μ n).real {z | T n z ≤ x}) atTop (nhds (Φ x)))
    (hΦ : Continuous Φ) :
    ∀ x : ℝ,
      Tendsto (fun n => (μ n).real {z | S n z ≤ x}) atTop (nhds (Φ x)) := by
  intro x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨η, hηpos, hη⟩ :=
    (Metric.continuousAt_iff.mp hΦ.continuousAt) (ε / 4) hε4
  let γ : ℝ := η / 2
  have hγpos : 0 < γ := by dsimp [γ]; linarith
  have hγ_lt_η : γ < η := by dsimp [γ]; linarith
  have hΦplus : dist (Φ (x + γ)) (Φ x) < ε / 4 := by
    apply hη
    rw [Real.dist_eq]
    simpa [abs_of_pos hγpos] using hγ_lt_η
  have hΦminus : dist (Φ (x - γ)) (Φ x) < ε / 4 := by
    apply hη
    rw [Real.dist_eq]
    simpa [abs_of_pos hγpos] using hγ_lt_η
  rw [Real.dist_eq] at hΦplus hΦminus
  have hR := hApprox γ hγpos
  have hTplus := hT (x + γ)
  have hTminus := hT (x - γ)
  have hRev : ∀ᶠ n in atTop,
      (μ n).real {z | γ ≤ |S n z - T n z|} < ε / 4 := by
    have h := (Metric.tendsto_nhds.mp hR) (ε / 4) hε4
    filter_upwards [h] with n hn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg MeasureTheory.measureReal_nonneg] at hn
    exact hn
  have hTplusEv : ∀ᶠ n in atTop,
      (μ n).real {z | T n z ≤ x + γ} < Φ (x + γ) + ε / 4 := by
    have h := (Metric.tendsto_nhds.mp hTplus) (ε / 4) hε4
    filter_upwards [h] with n hn
    rw [Real.dist_eq] at hn
    linarith [(abs_lt.mp hn).2]
  have hTminusEv : ∀ᶠ n in atTop,
      Φ (x - γ) - ε / 4 < (μ n).real {z | T n z ≤ x - γ} := by
    have h := (Metric.tendsto_nhds.mp hTminus) (ε / 4) hε4
    filter_upwards [h] with n hn
    rw [Real.dist_eq] at hn
    linarith [(abs_lt.mp hn).1]
  refine Filter.eventually_atTop.1 ?_
  filter_upwards [hRev, hTplusEv, hTminusEv] with n hRn hTpn hTmn
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · have hmono :
        (μ n).real {z | S n z ≤ x} ≤
          (μ n).real ({z | T n z ≤ x + γ} ∪
            {z | γ ≤ |S n z - T n z|}) := by
      apply MeasureTheory.measureReal_mono (h₂ := measure_ne_top _ _)
      intro z hz
      change S n z ≤ x at hz
      by_cases hfar : γ ≤ |S n z - T n z|
      · exact Or.inr hfar
      · apply Or.inl
        rw [not_le, abs_sub_lt_iff] at hfar
        change T n z ≤ x + γ
        linarith
    have hunion := MeasureTheory.measureReal_union_le (μ := μ n)
      {z | T n z ≤ x + γ} {z | γ ≤ |S n z - T n z|}
    linarith [hmono.trans hunion, (abs_lt.mp hΦplus).2]
  · have hmono :
        (μ n).real {z | T n z ≤ x - γ} ≤
          (μ n).real ({z | S n z ≤ x} ∪
            {z | γ ≤ |S n z - T n z|}) := by
      apply MeasureTheory.measureReal_mono (h₂ := measure_ne_top _ _)
      intro z hz
      change T n z ≤ x - γ at hz
      by_cases hfar : γ ≤ |S n z - T n z|
      · exact Or.inr hfar
      · apply Or.inl
        rw [not_le, abs_sub_lt_iff] at hfar
        change S n z ≤ x
        linarith
    have hunion := MeasureTheory.measureReal_union_le (μ := μ n)
      {z | S n z ≤ x} {z | γ ≤ |S n z - T n z|}
    linarith [hmono.trans hunion, (abs_lt.mp hΦminus).1]

/-- A negligible row-varying perturbation of a statistic with continuous-limit CDF has the expected probability limit on every continuity interval. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:μ,S,T,hS,hApprox,hT,hQcdf,hboundary), [the varying Law Icc tendsto of cdf and approx](goal).

Under the stated assumptions, the varying Law Icc tendsto of cdf and approx. -/
lemma varyingLaw_Icc_tendsto_of_cdf_and_approx
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (S T : ∀ n, Ω n → ℝ) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hS : ∀ n, Measurable (S n))
    (hApprox : ∀ η : ℝ, 0 < η →
      Tendsto (fun n => (μ n).real {z | η ≤ |S n z - T n z|})
        atTop (nhds 0))
    (hT : ∀ x : ℝ,
      Tendsto (fun n => (μ n).real {z | T n z ≤ x})
        atTop (nhds (Q.real (Iic x))))
    (hQcdf : Continuous (cdf Q)) {a b : ℝ}
    (hboundary : Q (frontier (Icc a b)) = 0) :
    Tendsto (fun n => (μ n).real {z | S n z ∈ Icc a b})
      atTop (nhds (Q.real (Icc a b))) := by
  let νs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨Measure.map (S n) (μ n), Measure.isProbabilityMeasure_map (hS n).aemeasurable⟩
  let ν : ProbabilityMeasure ℝ := ⟨Q, inferInstance⟩
  have hScdf (x : ℝ) :
      Tendsto (fun n => (cdf (νs n : Measure ℝ) x : ℝ)) atTop
        (nhds (cdf (ν : Measure ℝ) x : ℝ)) := by
    have hraw := varyingLaw_cdf_converging_together μ S T
      (fun x => Q.real (Iic x)) hApprox hT (by
        simpa only [← ProbabilityTheory.cdf_eq_real] using hQcdf)
    have htarget : (cdf (ν : Measure ℝ) x : ℝ) = Q.real (Iic x) := by
      rw [ProbabilityTheory.cdf_eq_real]
      rfl
    rw [htarget]
    apply (hraw x).congr'
    filter_upwards with n
    rw [ProbabilityTheory.cdf_eq_real]
    change (μ n).real {z | S n z ≤ x} =
      (Measure.map (S n) (μ n)).real (Iic x)
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
      Measure.map_apply (hS n) measurableSet_Iic]
    rfl
  have hν : Tendsto νs atTop (nhds ν) :=
    probabilityMeasure_tendsto_of_cdf_tendsto νs ν hScdf
  have hprob := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    hν (E := Icc a b) (by
      change ENNReal.toNNReal (Q (frontier (Icc a b))) = 0
      simp [hboundary])
  have hreal := NNReal.continuous_coe.tendsto _ |>.comp hprob
  apply hreal.congr'
  filter_upwards with n
  change (((νs n) (Icc a b) : NNReal) : ℝ) =
    (μ n).real {z | S n z ∈ Icc a b}
  rw [show (((νs n) (Icc a b) : NNReal) : ℝ) =
      (Measure.map (S n) (μ n)).real (Icc a b) by
        change ((ENNReal.toNNReal
          ((Measure.map (S n) (μ n)) (Icc a b)) : NNReal) : ℝ) = _
        rw [ENNReal.coe_toNNReal_eq_toReal]
        rfl]
  rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
    Measure.map_apply (hS n) measurableSet_Icc]
  rfl

/-- Exact pilot Wald coverage once the standardized oracle CDF and the row-varying Slutsky approximation to the fallback pivot have been proved. The fallback is retained verbatim, so samples with zero estimated variance are handled by `pilot_wald_event_eq`. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hcutoff,hselect,hp,hθ,hε,hApprox,hstandardCDF), [the pilot wald coverage of standardized cdf and approx](goal).

Under the stated assumptions, the pilot wald coverage of standardized cdf and approx. -/
lemma pilot_wald_coverage_of_standardized_cdf_and_approx
    (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hApprox : ∀ η : ℝ, 0 < η →
      Tendsto (fun n =>
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n).real
          {z | η ≤ |pilotWaldPivot select cutoff θ p ε m hselect hp hε n z -
            scaledError (pilotEstimator p ε m select hselect hp hε) θ 0 n z /
              Real.sqrt (Vstar θ p ε)|}) atTop (nhds 0))
    (hstandardCDF : ∀ x : ℝ,
      Tendsto (fun n =>
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n).real
          {z | scaledError (pilotEstimator p ε m select hselect hp hε) θ 0 n z /
              Real.sqrt (Vstar θ p ε) ≤ x}) atTop
        (nhds ((gaussianMeasure 0 1).real (Iic x)))) :
    Tendsto (fun n =>
      ((transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {z | |(pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ| ≤
          cutoff * Real.sqrt
            (VhatStar p ε m (select) z / n)}).toReal)
      atTop (nhds ((gaussianMeasure 0 1).real (Icc (-cutoff) cutoff))) := by
  let μ : ∀ n, Measure (Transcript (pilotOutputFamily n)) := fun n =>
    transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
  let S : ∀ n, Transcript (pilotOutputFamily n) → ℝ := fun n =>
    pilotWaldPivot select cutoff θ p ε m hselect hp hε n
  let T : ∀ n, Transcript (pilotOutputFamily n) → ℝ := fun n z =>
    scaledError (pilotEstimator p ε m select hselect hp hε) θ 0 n z /
      Real.sqrt (Vstar θ p ε)
  let _ (n : ℕ) : IsProbabilityMeasure (μ n) :=
    transcriptLaw_isProbability _ θ p hp hθ n
  have hS (n : ℕ) : Measurable (S n) := measurable_of_finite _
  have hpivot : Tendsto (fun n =>
      (μ n).real {z | S n z ∈ Icc (-cutoff) cutoff}) atTop
      (nhds ((gaussianMeasure 0 1).real (Icc (-cutoff) cutoff))) := by
    apply varyingLaw_Icc_tendsto_of_cdf_and_approx μ S T
      (gaussianMeasure 0 1) hS hApprox hstandardCDF
    · simpa [gaussianMeasure] using
        (continuous_cdf_gaussianReal_zero (v := (1 : NNReal)) (by norm_num))
    · exact gaussianMeasure_zero_one_frontier_Icc hcutoff
  apply pilot_wald_coverage_of_pivot_Icc select cutoff hcutoff θ p ε m hselect hp hε
    ((gaussianMeasure 0 1).real (Icc (-cutoff) cutoff))
  simpa only [μ, S, MeasureTheory.measureReal_def] using hpivot

end CausalSmith.Stat.LdpAteEfficiencySurface
