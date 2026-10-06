module
public import Causalean.Stat.Bootstrap.AsymptoticLinear.LimitLemmas
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.Inference.Studentize
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Pilot
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotGaussianTransfer
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotLocalization
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotMoments
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotPrefix
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotRowGaussianLimit
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotStudentizationSupport
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotUniformTails
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotVhatConsistency
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotWeakLimitSupport

/-! # Attainment by the private-pilot estimator

The complete pilot procedure is private, conditionally unbiased, regular and
asymptotically Gaussian. Its main-sample variance gives Wald coverage at every
interior parameter, including channel-support boundaries. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Filter Causalean.Stat
open scoped BigOperators ENNReal

/-- For [the supplied quantities and conditions](hyp:x), the [standard normal cdf](goal) is the mathematical object specified below. -/
def standardNormalCDF (x : ℝ) : ℝ :=
  (gaussianMeasure 0 1 (Set.Iic x)).toReal
  -- @realizes \Phi(standard-normal CDF)

/-- the wald critical value is the mathematical object specified below. [The wald Critical Value](goal) is determined by [the displayed parameters](hyp:γ). -/
def waldCriticalValue (γ : ℝ) : ℝ :=
  sInf {z : ℝ | 1 - γ / 2 ≤ standardNormalCDF z}
  -- @realizes z_{1-\gamma/2}(normal quantile)

/-- Under [the supplied quantities and conditions](hyp:x), [the standard normal cdf eq std normal cdf assertion](goal) holds. -/
lemma standardNormalCDF_eq_stdNormalCDF (x : ℝ) :
    standardNormalCDF x = Causalean.Mathlib.stdNormalCDF x := by
  simp [standardNormalCDF, Causalean.Mathlib.stdNormalCDF_def,
    ProbabilityTheory.cdf_eq_real, MeasureTheory.measureReal_def, gaussianMeasure]

/-- [the wald critical value eq probit assertion](goal) holds. -/
lemma waldCriticalValue_eq_probit (γ : ℝ) :
    waldCriticalValue γ = Causalean.Mathlib.probit (1 - γ / 2) := by
  unfold waldCriticalValue Causalean.Mathlib.probit
  congr 1
  ext z
  simp only [Set.mem_setOf_eq]
  rw [standardNormalCDF_eq_stdNormalCDF]

/-- Under the supplied quantities and conditions, the wald critical value pos assertion holds. Under [the stated assumptions](hyp:hγ), [the wald Critical Value pos](goal).

Under the stated assumptions, the wald Critical Value pos. -/
lemma waldCriticalValue_pos {γ : ℝ} (hγ : 0 < γ ∧ γ < 1) :
    0 < waldCriticalValue γ := by
  have hq0 : 0 < 1 - γ / 2 := by linarith
  have hq1 : 1 - γ / 2 < 1 := by linarith
  have hzero : Causalean.Mathlib.stdNormalCDF 0 = 1 / 2 := by
    have hsym := Causalean.Mathlib.stdNormalCDF_neg 0
    norm_num at hsym ⊢
    linarith
  rw [waldCriticalValue_eq_probit]
  apply Causalean.Mathlib.stdNormalCDF_strictMono.lt_iff_lt.mp
  rw [Causalean.Mathlib.stdNormalCDF_probit hq0 hq1, hzero]
  linarith

/-- the gaussian measure wald critical value icc assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hγ), [the gaussian Measure wald Critical Value Icc](goal).

Under the stated assumptions, the gaussian Measure wald Critical Value Icc. -/
lemma gaussianMeasure_waldCriticalValue_Icc {γ : ℝ}
    (hγ : 0 < γ ∧ γ < 1) :
    (gaussianMeasure 0 1
      (Set.Icc (-waldCriticalValue γ) (waldCriticalValue γ))).toReal = 1 - γ := by
  have hp0 : 0 < γ / 2 := by linarith
  have hp1 : γ / 2 < 1 := by linarith
  have hq0 : 0 < 1 - γ / 2 := by linarith
  have hq1 : 1 - γ / 2 < 1 := by linarith
  have hsym : Causalean.Mathlib.probit (γ / 2) =
      -Causalean.Mathlib.probit (1 - γ / 2) := by
    apply Causalean.Mathlib.stdNormalCDF_strictMono.injective
    rw [Causalean.Mathlib.stdNormalCDF_probit hp0 hp1,
      Causalean.Mathlib.stdNormalCDF_neg,
      Causalean.Mathlib.stdNormalCDF_probit hq0 hq1]
    ring
  have h := gaussianReal_quantile_Icc_toReal
    (v := (1 : NNReal)) (by norm_num) hγ.1 hγ.2
  simpa [gaussianMeasure, waldCriticalValue_eq_probit, hsym,
    MeasureTheory.measureReal_def] using h

-- @node: thm:pilot-attainment
/-- Under the supplied quantities and conditions, the pilot attainment assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hassignment,hmeans,hfixed,hselect,hγ,hdiverges,hsublinear), [the pilot attainment](goal).

Under the stated assumptions, the pilot attainment. -/
theorem pilot_attainment
    (θ : TrialParameter) (p ε γ : ℝ)
    (hassignment : InteriorAssignment p)
    (hmeans : InteriorMeans θ)
    (epsSeq : ℕ → ℝ) (hfixed : FixedPrivacy epsSeq ε)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hγ : 0 < γ ∧ γ < 1) -- @realizes \gamma(Wald error in (0,1))
    (m : ℕ → ℕ) (hdiverges : PilotDiverges m)
    (hsublinear : PilotSublinear m) :
    let P := pilotEstimator p ε m select hselect hassignment hfixed.1
    (∀ n, SequentialLDP (Z := pilotOutputFamily n) ε (P.channel n)) ∧
    (∀ n ≥ 2, ∀ f : Transcript (pilotOutputFamily n) → ℝ,
      Measurable f →
      (∃ C : ℝ, ∀ z, |f z| ≤ C) →
      (∀ z z', (∀ i : Fin n, i.val < m n → z i = z' i) → f z = f z') →
      Integrable (fun z => (P.estimate n z - contrast θ) * f z)
        (transcriptLaw P θ p n) ∧
      (∫ z, (P.estimate n z - contrast θ) * f z
        ∂transcriptLaw P θ p n) = 0) ∧
    WeakLocalLimit P θ p (gaussianMeasure 0 (Vstar θ p ε)) ∧
    (∀ δ : ℝ, 0 < δ →
      Tendsto (fun n =>
        (transcriptLaw P θ p n)
          {z | δ < |VhatStar p ε m
            (select) z -
              Vstar θ p ε|}) atTop (nhds 0)) ∧
    RegularProcedure P θ p ∧
    Tendsto (fun n =>
      ((transcriptLaw P θ p n)
        {z | |P.estimate n z - contrast θ| ≤
          waldCriticalValue γ *
            Real.sqrt (VhatStar p ε m
              (select) z / n)}).toReal)
      atTop (nhds (1 - γ)) := by
  let P := pilotEstimator p ε m select hselect hassignment hfixed.1
  have hgaussianCDF : ∀ h : TrialParameter, ∀ x : ℝ,
      Tendsto (fun n =>
        (transcriptLaw P (localAlternative θ h n) p n).real
          {z | scaledError P θ h n z ≤ x}) atTop
        (nhds ((gaussianMeasure 0 (Vstar θ p ε)).real (Set.Iic x))) := by
    exact pilot_scaledError_cdf_tendsto_of_all_conditionalRows
      select θ p ε m hselect hassignment hmeans hfixed.1 hdiverges hsublinear
      (fun h x φ hφ η hη hηlim =>
        adaptivePilotRowScaledCDF_subsequence_tendsto_gaussian
          select θ h p ε m hselect hassignment hmeans hfixed.1 hsublinear
          x φ hφ η hη hηlim)
  have hweak : WeakLocalLimit P θ p
      (gaussianMeasure 0 (Vstar θ p ε)) :=
    weakLocalLimit_of_scaledError_cdf_tendsto
      select P θ p hselect hassignment hmeans hfixed.1 hgaussianCDF
  have hvhat : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n =>
        (transcriptLaw P θ p n)
          {z | δ < |VhatStar p ε m
            (select) z -
              Vstar θ p ε|}) atTop (nhds 0) := by
    exact pilot_VhatStar_consistent select θ p ε m hselect hassignment hmeans
      hfixed.1 hdiverges hsublinear
  have htails := pilot_scaledError_uniform_squared_tails
    select θ p ε m hselect hassignment hmeans hfixed.1 hsublinear
  have hregular : RegularProcedure P θ p :=
    regular_of_weakLocalLimit_and_uniformTails
      P θ p (Vstar θ p ε) hweak htails
  have hV : 0 < Vstar θ p ε :=
    inv_pos.mpr (Jstar_pos_interior θ p ε hassignment hmeans hfixed.1)
  have hsqrtV : 0 < Real.sqrt (Vstar θ p ε) := Real.sqrt_pos.2 hV
  have hstandardCDF : ∀ x : ℝ,
      Tendsto (fun n =>
        (transcriptLaw P θ p n).real
          {z | scaledError P θ 0 n z / Real.sqrt (Vstar θ p ε) ≤ x}) atTop
        (nhds ((gaussianMeasure 0 1).real (Set.Iic x))) := by
    intro x
    have hraw := hgaussianCDF 0 (x * Real.sqrt (Vstar θ p ε))
    have hevent (n : ℕ) :
        {z | scaledError P θ 0 n z / Real.sqrt (Vstar θ p ε) ≤ x} =
          {z | scaledError P θ 0 n z ≤ x * Real.sqrt (Vstar θ p ε)} := by
      ext z
      exact div_le_iff₀ hsqrtV
    have htarget :
        (gaussianMeasure 0 (Vstar θ p ε)).real
            (Set.Iic (x * Real.sqrt (Vstar θ p ε))) =
          (gaussianMeasure 0 1).real (Set.Iic x) := by
      rw [← ProbabilityTheory.cdf_eq_real, ← ProbabilityTheory.cdf_eq_real]
      simp only [gaussianMeasure]
      rw [Causalean.Stat.cdf_gaussianReal_zero
          (Real.toNNReal_pos.mpr hV),
        Causalean.Stat.cdf_gaussianReal_zero (v := Real.toNNReal 1)
          (by norm_num [Real.toNNReal_pos])]
      congr 1
      rw [Real.coe_toNNReal (Vstar θ p ε) hV.le,
        Real.coe_toNNReal 1 (by norm_num)]
      simp only [Real.sqrt_one, div_one]
      field_simp
    rw [← htarget]
    apply hraw.congr'
    filter_upwards with n
    rw [hevent n]
    have hlocal0 : localAlternative θ 0 n = θ := by
      funext k
      simp [localAlternative]
    rw [hlocal0]
  letI (n : ℕ) : IsProbabilityMeasure (transcriptLaw P θ p n) :=
    transcriptLaw_isProbability P θ p hassignment hmeans n
  have hvhat_ge : ∀ r : ℝ, 0 < r →
      Tendsto (fun n =>
        (transcriptLaw P θ p n).real
          {z | r ≤ |VhatStar p ε m
            (select) z - Vstar θ p ε|})
        atTop (nhds 0) := by
    intro r hr
    have hstrict := hvhat (r / 2) (half_pos hr)
    have hstrictReal : Tendsto (fun n =>
        (transcriptLaw P θ p n).real
          {z | r / 2 < |VhatStar p ε m
            (select) z - Vstar θ p ε|})
        atTop (nhds 0) := by
      change Tendsto (fun n => ENNReal.toReal
        ((transcriptLaw P θ p n)
          {z | r / 2 < |VhatStar p ε m
            (select) z - Vstar θ p ε|}))
        atTop (nhds (ENNReal.toReal 0))
      exact (ENNReal.tendsto_toReal (by simp)).comp hstrict
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hstrictReal
    · intro n
      exact MeasureTheory.measureReal_nonneg
    · intro n
      apply MeasureTheory.measureReal_mono (h₂ := measure_ne_top _ _)
      intro z hz
      exact lt_of_lt_of_le (half_lt_self hr) hz
  have hwald :=
    pilot_wald_coverage_of_standardized_cdf_and_VhatStar_consistent
      select (waldCriticalValue γ) (waldCriticalValue_pos hγ)
      θ p ε m hselect hassignment hmeans hfixed.1 hstandardCDF hvhat_ge
  refine ⟨?_, ?_, hweak, hvhat, hregular, ?_⟩
  · intro n
    exact pilotProtocol_private p ε m select hselect hassignment hfixed.1 n
  · intro n hn f hf hbound hpref
    exact pilot_conditional_unbiasedness select θ p ε m hselect hassignment hmeans
      hfixed.1 hsublinear n hn f hf hbound hpref
  · have hcoverage :
        (gaussianMeasure 0 1).real
            (Set.Icc (-waldCriticalValue γ) (waldCriticalValue γ)) = 1 - γ := by
      simpa only [MeasureTheory.measureReal_def] using
        gaussianMeasure_waldCriticalValue_Icc hγ
    rw [hcoverage] at hwald
    simpa only [P] using hwald

end CausalSmith.Stat.LdpAteEfficiencySurface
