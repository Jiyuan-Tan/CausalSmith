module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotWaldLimitSupport
public import Causalean.Stat.CLT.GaussianTail

/-! # Row-varying studentization for the private pilot

This file derives the Slutsky approximation required by the varying-law Wald
adapter from the genuine CDF and plug-in variance consistency premises.
-/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory ProbabilityTheory Filter Set Causalean.Stat
open scoped Topology ENNReal

/-- A row-varying statistic whose CDF converges to the standard normal is tight. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:μ,T,hTmeas,hcdf), [the varying Law tight of standard Normal cdf](goal).

Under the stated assumptions, the varying Law tight of standard Normal cdf. -/
lemma varyingLaw_tight_of_standardNormal_cdf
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (T : ∀ n, Ω n → ℝ) (hTmeas : ∀ n, Measurable (T n))
    (hcdf : ∀ x : ℝ,
      Tendsto (fun n => (μ n).real {z | T n z ≤ x}) atTop
        (nhds ((gaussianMeasure 0 1).real (Iic x)))) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n in atTop, (μ n).real {z | M ≤ |T n z|} < η := by
  intro η hη
  let η₀ : ℝ := min (η / 8) (1 / 8)
  have hη₀ : 0 < η₀ := lt_min (by linarith) (by norm_num)
  obtain ⟨R, hR, hleft, hright⟩ :=
    gaussian_tail_small_gaussian (m := 0) (v := 1) hη₀
  have hleftR : (gaussianMeasure 0 1).real (Iic (-R)) ≤ η₀ := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hleft
    simpa [MeasureTheory.measureReal_def, ENNReal.toReal_ofReal hη₀.le] using ht
  have hrightR : (gaussianMeasure 0 1).real (Ici R) ≤ η₀ := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hright
    simpa [MeasureTheory.measureReal_def, ENNReal.toReal_ofReal hη₀.le] using ht
  have hcomp : (gaussianMeasure 0 1).real (Icc (-R) R)ᶜ ≤ 2 * η₀ := by
    calc
      _ ≤ (gaussianMeasure 0 1).real (Iic (-R) ∪ Ici R) := by
        apply MeasureTheory.measureReal_mono (h₂ := measure_ne_top _ _)
        intro x hx
        simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
        exact hx.imp le_of_lt le_of_lt
      _ ≤ (gaussianMeasure 0 1).real (Iic (-R)) +
          (gaussianMeasure 0 1).real (Ici R) :=
        MeasureTheory.measureReal_union_le _ _
      _ ≤ 2 * η₀ := by linarith
  have hzeroApprox : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ n).real {z | δ ≤ |T n z - T n z|})
        atTop (nhds 0) := by
    intro δ hδ
    convert tendsto_const_nhds (x := (0 : ℝ)) using 1
    funext n
    simp [not_le_of_gt hδ]
  have hinter := varyingLaw_Icc_tendsto_of_cdf_and_approx μ T T
    (gaussianMeasure 0 1) hTmeas hzeroApprox hcdf
    (by simpa [gaussianMeasure] using
      (continuous_cdf_gaussianReal_zero (v := (1 : NNReal)) (by norm_num)))
    (gaussianMeasure_zero_one_frontier_Icc hR)
  have hcompl : Tendsto (fun n => (μ n).real {z | T n z ∉ Icc (-R) R})
      atTop (nhds ((gaussianMeasure 0 1).real (Icc (-R) R)ᶜ)) := by
    have hsub :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hinter
    have hq := MeasureTheory.measureReal_add_measureReal_compl
      (μ := gaussianMeasure 0 1)
      (show MeasurableSet (Icc (-R) R) from measurableSet_Icc)
    have hq' : (gaussianMeasure 0 1).real (Icc (-R) R) +
        (gaussianMeasure 0 1).real (Icc (-R) R)ᶜ = 1 := by
      simpa [MeasureTheory.measureReal_def] using hq
    rw [show (gaussianMeasure 0 1).real (Icc (-R) R)ᶜ =
        1 - (gaussianMeasure 0 1).real (Icc (-R) R) by linarith [hq']]
    apply hsub.congr'
    filter_upwards with n
    have hn := MeasureTheory.measureReal_add_measureReal_compl
      (μ := μ n) (hTmeas n
        (show MeasurableSet (Icc (-R) R) from measurableSet_Icc))
    have hn' : (μ n).real (T n ⁻¹' Icc (-R) R) +
        (μ n).real (T n ⁻¹' Icc (-R) R)ᶜ = 1 := by
      simpa [MeasureTheory.measureReal_def] using hn
    rw [show {z | T n z ∈ Icc (-R) R} = T n ⁻¹' Icc (-R) R by rfl,
      show {z | T n z ∉ Icc (-R) R} = (T n ⁻¹' Icc (-R) R)ᶜ by rfl]
    linarith [hn']
  refine ⟨R + 1, by linarith, ?_⟩
  have hev := hcompl.eventually_lt_const (by
    have h2η : 2 * η₀ < η := by
      dsimp [η₀]
      have hm := min_le_left (η / 8) (1 / 8)
      linarith
    exact lt_of_le_of_lt hcomp h2η)
  filter_upwards [hev] with n hn
  apply lt_of_le_of_lt (MeasureTheory.measureReal_mono (h₂ := measure_ne_top _ _) ?_) hn
  intro z hz
  simp only [mem_Icc, not_and_or, not_le]
  change R + 1 ≤ |T n z| at hz
  rcases (le_abs.mp hz) with hz | hz
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

/-- Plug-in variance consistency and the Gaussian CDF limit imply that the fallback-studentized pilot pivot is asymptotically indistinguishable from the oracle-standardized scaled error. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hstandardCDF,hvhat), [the pilot Wald Pivot approx standardized Scaled Error](goal).

Under the stated assumptions, the pilot Wald Pivot approx standardized Scaled Error. -/
lemma pilotWaldPivot_approx_standardizedScaledError
    (cutoff : ℝ) (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hstandardCDF : ∀ x : ℝ,
      Tendsto (fun n =>
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n).real
          {z | scaledError (pilotEstimator p ε m select hselect hp hε) θ 0 n z /
              Real.sqrt (Vstar θ p ε) ≤ x}) atTop
        (nhds ((gaussianMeasure 0 1).real (Iic x))))
    (hvhat : ∀ r : ℝ, 0 < r →
      Tendsto (fun n =>
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n).real
          {z | r ≤ |VhatStar p ε m (select) z -
            Vstar θ p ε|}) atTop (nhds 0)) :
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n =>
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n).real
          {z | δ ≤ |pilotWaldPivot select cutoff θ p ε m hselect hp hε n z -
            scaledError (pilotEstimator p ε m select hselect hp hε) θ 0 n z /
              Real.sqrt (Vstar θ p ε)|}) atTop (nhds 0) := by
  let μ : ∀ n, Measure (Transcript (pilotOutputFamily n)) := fun n =>
    transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
  let T : ∀ n, Transcript (pilotOutputFamily n) → ℝ := fun n z =>
    scaledError (pilotEstimator p ε m select hselect hp hε) θ 0 n z /
      Real.sqrt (Vstar θ p ε)
  let _ (n : ℕ) : IsProbabilityMeasure (μ n) :=
    transcriptLaw_isProbability _ θ p hp hθ n
  have hTmeas (n : ℕ) : Measurable (T n) := measurable_of_finite _
  have hV : 0 < Vstar θ p ε :=
    inv_pos.mpr (Jstar_pos_interior θ p ε hp hθ hε)
  let g : ℝ → ℝ := fun v => Real.sqrt (Vstar θ p ε) / Real.sqrt v
  have hg : ContinuousAt g (Vstar θ p ε) := by
    dsimp [g]
    exact continuousAt_const.div₀ Real.continuous_sqrt.continuousAt
      (ne_of_gt (Real.sqrt_pos.2 hV))
  have hgV : g (Vstar θ p ε) = 1 := by
    dsimp [g]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hV)]
  intro δ hδ
  rw [Metric.tendsto_atTop]
  intro ζ hζ
  obtain ⟨M, hM, hMtight⟩ :=
    varyingLaw_tight_of_standardNormal_cdf μ T hTmeas hstandardCDF
      (ζ / 2) (by linarith)
  obtain ⟨r₀, hr₀, hgr₀⟩ :=
    (Metric.continuousAt_iff.mp hg) (δ / M) (div_pos hδ hM)
  let r : ℝ := min (r₀ / 2) (Vstar θ p ε / 2)
  have hr : 0 < r := lt_min (half_pos hr₀) (half_pos hV)
  have hrV : r < Vstar θ p ε :=
    (min_le_right _ _).trans_lt (half_lt_self hV)
  have hvarEv := (hvhat r hr).eventually_lt_const (half_pos hζ)
  refine Filter.eventually_atTop.1 ?_
  filter_upwards [hMtight, hvarEv] with n htight hvar
  rw [Real.dist_eq, sub_zero, abs_of_nonneg MeasureTheory.measureReal_nonneg]
  have hsubset :
      {z | δ ≤ |pilotWaldPivot select cutoff θ p ε m hselect hp hε n z - T n z|} ⊆
        {z | r ≤ |VhatStar p ε m (select) z -
          Vstar θ p ε|} ∪ {z | M ≤ |T n z|} := by
    intro z hz
    by_contra hbad
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hbad
    have hVn : 0 < VhatStar p ε m (select) z := by
      linarith [abs_lt.mp hbad.1 |>.1]
    have hdist : dist
        (VhatStar p ε m (select) z)
        (Vstar θ p ε) < r₀ := by
      rw [Real.dist_eq]
      exact hbad.1.trans_le (min_le_left _ _ |>.trans (half_le_self hr₀.le))
    have hgclose := hgr₀ hdist
    rw [Real.dist_eq, hgV] at hgclose
    have hpivot : pilotWaldPivot select cutoff θ p ε m hselect hp hε n z =
        T n z * g (VhatStar p ε m (select) z) := by
      have hlocal : localAlternative θ 0 n = θ := by
        funext k
        simp [localAlternative]
      simp [pilotWaldPivot, waldFallbackPivot, ne_of_gt hVn, T, g,
        scaledError, hlocal]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hV),
        ne_of_gt (Real.sqrt_pos.2 hVn)]
    change δ ≤ |pilotWaldPivot select cutoff θ p ε m hselect hp hε n z - T n z| at hz
    rw [hpivot, show T n z * g
        (VhatStar p ε m (select) z) - T n z =
          T n z * (g (VhatStar p ε m
            (select) z) - 1) by ring,
      abs_mul] at hz
    have hprod : |T n z| *
        |g (VhatStar p ε m (select) z) - 1| < δ := by
      calc
        _ ≤ M * |g (VhatStar p ε m (select) z) - 1| :=
          mul_le_mul_of_nonneg_right hbad.2.le (abs_nonneg _)
        _ < M * (δ / M) := mul_lt_mul_of_pos_left hgclose hM
        _ = δ := by field_simp
    exact (not_lt_of_ge hz) hprod
  have hmono := MeasureTheory.measureReal_mono (μ := μ n)
    (h₂ := measure_ne_top _ _) hsubset
  have hunion := MeasureTheory.measureReal_union_le (μ := μ n)
    {z | r ≤ |VhatStar p ε m (select) z -
      Vstar θ p ε|} {z | M ≤ |T n z|}
  exact lt_of_le_of_lt (hmono.trans hunion) (by linarith)

/-- The actual standardized-error CDF limit and consistent `VhatStar` imply the private-pilot Wald coverage limit, with the zero-variance fallback handled inside the proved Slutsky approximation. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hcutoff,hselect,hp,hθ,hε,hstandardCDF,hvhat), [the pilot wald coverage of standardized cdf and Vhat Star consistent](goal).

Under the stated assumptions, the pilot wald coverage of standardized cdf and Vhat Star consistent. -/
lemma pilot_wald_coverage_of_standardized_cdf_and_VhatStar_consistent
    (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hstandardCDF : ∀ x : ℝ,
      Tendsto (fun n =>
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n).real
          {z | scaledError (pilotEstimator p ε m select hselect hp hε) θ 0 n z /
              Real.sqrt (Vstar θ p ε) ≤ x}) atTop
        (nhds ((gaussianMeasure 0 1).real (Iic x))))
    (hvhat : ∀ r : ℝ, 0 < r →
      Tendsto (fun n =>
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n).real
          {z | r ≤ |VhatStar p ε m (select) z -
            Vstar θ p ε|}) atTop (nhds 0)) :
    Tendsto (fun n =>
      ((transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {z | |(pilotEstimator p ε m select hselect hp hε).estimate n z - contrast θ| ≤
          cutoff * Real.sqrt
            (VhatStar p ε m (select) z / n)}).toReal)
      atTop (nhds ((gaussianMeasure 0 1).real (Icc (-cutoff) cutoff))) := by
  apply pilot_wald_coverage_of_standardized_cdf_and_approx
    select cutoff hcutoff θ p ε m hselect hp hθ hε
  · exact pilotWaldPivot_approx_standardizedScaledError
      select cutoff θ p ε m hselect hp hθ hε hstandardCDF hvhat
  · exact hstandardCDF

end CausalSmith.Stat.LdpAteEfficiencySurface
