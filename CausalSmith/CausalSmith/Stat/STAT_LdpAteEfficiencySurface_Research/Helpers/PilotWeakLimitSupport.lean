module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotRowInputs
public import Causalean.Stat.Quantile.CdfConvergence
public import Causalean.Stat.CLT.AsymptoticLinearity

/-!
# CDF support for the pilot weak limit

This file supplies the measure-theoretic bridge from convergence of real CDFs to
weak convergence.  The paper-specific theorem below deliberately leaves the CDF
convergence of the actual centered estimator as an explicit hypothesis.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory ProbabilityTheory Filter Set Causalean.Stat
open scoped Topology ENNReal

/-- Pointwise convergence of the CDFs of real probability measures implies weak convergence. This all-points form is convenient for triangular-array adapters. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hcdf), [the probability Measure tendsto of cdf tendsto](goal).

Under the stated assumptions, the probability Measure tendsto of cdf tendsto. -/
lemma probabilityMeasure_tendsto_of_cdf_tendsto
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hcdf : ∀ x : ℝ,
      Tendsto (fun n => (cdf (μs n : Measure ℝ) x : ℝ)) atTop
        (nhds (cdf (μ : Measure ℝ) x : ℝ))) :
    Tendsto μs atTop (nhds μ) := by
  let S : Set (Set ℝ) := {s | ∃ a b : ℝ, a < b ∧ Ioc a b = s}
  have hpi : IsPiSystem S := by
    simpa only [S, id_eq] using (isPiSystem_Ioc (id : ℝ → ℝ) id)
  apply hpi.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a, b, hab, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hxu
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hu x hxu
    refine ⟨Ioc (x - r / 2) (x + r / 2), ?_, ?_, ?_⟩
    · exact ⟨x - r / 2, x + r / 2, by linarith, rfl⟩
    · exact Ioc_mem_nhds (by linarith) (by linarith)
    · intro y hy
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_lt]
      constructor <;> linarith [hy.1, hy.2]
  · rintro s ⟨a, b, hab, rfl⟩
    rw [← NNReal.tendsto_coe]
    have hmass (ν : ProbabilityMeasure ℝ) :
        ((ν (Ioc a b) : NNReal) : ℝ) =
          (cdf (ν : Measure ℝ) b : ℝ) - (cdf (ν : Measure ℝ) a : ℝ) := by
      change (ν : Measure ℝ).real (Ioc a b) = _
      rw [show Ioc a b = Iic b \ Iic a by ext y; simp]
      rw [MeasureTheory.measureReal_sdiff (μ := (ν : Measure ℝ))
        (Iic_subset_Iic.mpr hab.le) measurableSet_Iic]
      rw [← ProbabilityTheory.cdf_eq_real, ← ProbabilityTheory.cdf_eq_real]
    simpa only [hmass] using (hcdf b).sub (hcdf a)

/-- CDF convergence of the actual centered, root-scaled estimator laws implies the bounded-continuous-test formulation of the local weak limit. The transcript spaces may vary with `n`; the hypothesis is stated directly using their induced laws. No pilot CLT or CDF convergence is hidden in this adapter. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hcdf), [the weak Local Limit of scaled Error cdf tendsto](goal).

Under the stated assumptions, the weak Local Limit of scaled Error cdf tendsto. -/
lemma weakLocalLimit_of_scaledError_cdf_tendsto
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hcdf : ∀ h : TrialParameter, ∀ x : ℝ,
      Tendsto (fun n =>
        (transcriptLaw P (localAlternative θ h n) p n).real
          {z | scaledError P θ h n z ≤ x}) atTop
        (nhds ((gaussianMeasure 0 (Vstar θ p ε)).real (Iic x)))) :
    WeakLocalLimit P θ p (gaussianMeasure 0 (Vstar θ p ε)) := by
  classical
  have hvpos : 0 < Vstar θ p ε := by
    exact_mod_cast adaptivePilotLimitVariance_pos select θ p ε hselect hp hθ hε
  let L : Measure ℝ := gaussianMeasure 0 (Vstar θ p ε)
  let _ : IsProbabilityMeasure L := by
    dsimp [L, gaussianMeasure]
    rw [Real.toNNReal_of_nonneg hvpos.le]
    infer_instance
  intro h f hf ⟨C, hC⟩
  have hscaled (n : ℕ) : Measurable (scaledError P θ h n) := by
    exact measurable_const.mul ((P.estimate_measurable n).sub measurable_const)
  let ν : ℕ → ProbabilityMeasure ℝ := fun n =>
    if hn : InteriorMeans (localAlternative θ h n) then
      letI : IsProbabilityMeasure
          (transcriptLaw P (localAlternative θ h n) p n) :=
        transcriptLaw_isProbability P _ p hp hn n
      ⟨Measure.map (scaledError P θ h n)
          (transcriptLaw P (localAlternative θ h n) p n),
        Measure.isProbabilityMeasure_map (hscaled n).aemeasurable⟩
    else ⟨L, inferInstance⟩
  let νlim : ProbabilityMeasure ℝ := ⟨L, inferInstance⟩
  have hνcdf (x : ℝ) :
      Tendsto (fun n => (cdf (ν n : Measure ℝ) x : ℝ)) atTop
        (nhds (cdf (νlim : Measure ℝ) x : ℝ)) := by
    have htarget : (cdf (νlim : Measure ℝ) x : ℝ) =
        (gaussianMeasure 0 (Vstar θ p ε)).real (Iic x) := by
      rw [ProbabilityTheory.cdf_eq_real]
      rfl
    rw [htarget]
    apply (hcdf h x).congr'
    filter_upwards [eventually_localAlternative_interior θ h hθ] with n hn
    have hmap : (ν n : Measure ℝ) =
        Measure.map (scaledError P θ h n)
          (transcriptLaw P (localAlternative θ h n) p n) := by
      simp only [ν, hn, ↓reduceDIte]
      rfl
    rw [ProbabilityTheory.cdf_eq_real, hmap]
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
    congr 1
    change (transcriptLaw P (localAlternative θ h n) p n)
      ((scaledError P θ h n) ⁻¹' Iic x) = _
    exact (Measure.map_apply (hscaled n) measurableSet_Iic).symm
  have hν : Tendsto ν atTop (nhds νlim) :=
    probabilityMeasure_tendsto_of_cdf_tendsto ν νlim hνcdf
  let fb : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup f hf C (by
      intro x
      simpa only [Real.norm_eq_abs] using hC x)
  have hint :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) fb
  apply hint.congr'
  filter_upwards [eventually_localAlternative_interior θ h hθ] with n hn
  have hmap : (ν n : Measure ℝ) =
      Measure.map (scaledError P θ h n)
        (transcriptLaw P (localAlternative θ h n) p n) := by
    simp only [ν, hn, ↓reduceDIte]
    rfl
  rw [hmap]
  change (∫ y, f y ∂Measure.map (scaledError P θ h n)
    (transcriptLaw P (localAlternative θ h n) p n)) = _
  rw [MeasureTheory.integral_map (hscaled n).aemeasurable
    hf.aestronglyMeasurable]

end CausalSmith.Stat.LdpAteEfficiencySurface
