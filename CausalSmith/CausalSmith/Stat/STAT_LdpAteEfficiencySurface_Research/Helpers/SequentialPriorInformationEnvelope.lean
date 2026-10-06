module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialBayesOrdering
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialInformationEnvelope
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialVanTreesRegularity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Compact-prior sequential information envelope

This file upgrades the local stationary-envelope limit to uniform convergence
over the compact scalar prior and integrates that envelope against the exact
normalized quartic prior used by the sequential van Trees argument.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open Filter MeasureTheory Set
open scoped Topology BigOperators
open Causalean.Stat.Minimax.ObservationDependentVanTrees

/-- The inverse-root-sample parameter path agrees with the local alternative
indexed by the corresponding scalar multiple of the direction. For [the displayed inputs and conditions](hyp:v,a,n), [the stated result](goal) follows. -/
lemma parameterPath_compactScaled_eq_localAlternative
    (θ v : TrialParameter) (a : ℝ) (n : ℕ) :
    parameterPath θ v (a / Real.sqrt n) =
      localAlternative θ (scaledDirection a v) n := by
  funext k
  simp [parameterPath, localAlternative, scaledDirection]
  ring

/-- A compact scalar family of inverse-root-sample paths is eventually contained in the interior parameter space. For the displayed inputs and conditions, the stated result follows. Under [the stated assumptions](hyp:hθ), [the eventually parameter Path compact Scaled interior](goal).

Under the stated assumptions, the eventually parameter Path compact Scaled interior. -/
lemma eventually_parameterPath_compactScaled_interior
    (θ v : TrialParameter) (R : ℝ) (hθ : InteriorMeans θ) :
    ∀ᶠ n : ℕ in atTop, ∀ a ∈ Icc (-R) R,
      InteriorMeans (parameterPath θ v (a / Real.sqrt n)) := by
  let H := R * Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2)
  have hev := eventually_localAlternative_interior_uniform θ H hθ
  refine hev.mono ?_
  intro n hn a ha
  rw [parameterPath_compactScaled_eq_localAlternative]
  exact hn (scaledDirection a v) (scaledDirection_mem_cover v ha)

/-- The selected stationary information envelope converges uniformly over a fixed compact scalar family of inverse-root-sample local paths. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the tendsto Uniformly On upper Envelope compact Scaled selected Direction](goal).

Under the stated assumptions, the tendsto Uniformly On upper Envelope compact Scaled selected Direction. -/
lemma tendstoUniformlyOn_upperEnvelope_compactScaled_selectedDirection
    (θ : TrialParameter) (p ε R : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    TendstoUniformlyOn
      (fun (n : ℕ) a => upperEnvelope
        (parameterPath θ
          (direction (selectedDirection θ p ε hp hθ hε))
          (a / Real.sqrt n)) p ε
        (selectedDirection θ p ε hp hθ hε))
      (fun _ => Jstar θ p ε) atTop (Icc (-R) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  let v := direction (selectedDirection θ p ε hp hθ hε)
  let Θ := {η : TrialParameter // InteriorMeans η}
  let θsub : Θ := ⟨θ, hθ⟩
  have hc := (continuous_upperEnvelope_interior p ε
    (selectedDirection θ p ε hp hθ hε) hp hε.le).continuousAt
      (x := θsub)
  obtain ⟨r, hr, hcontrol⟩ := (Metric.continuousAt_iff.mp hc) δ hδ
  let H := R * Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2)
  have hevDist := eventually_localAlternative_dist_lt_uniform θ H r hr
  have hevInterior := eventually_localAlternative_interior_uniform θ H hθ
  refine (hevDist.and hevInterior).mono ?_
  intro n hn a ha
  rcases hn with ⟨hdist, hinterior⟩
  have hcover : Real.sqrt (((scaledDirection a v) 0) ^ 2 +
      ((scaledDirection a v) 1) ^ 2) ≤ H :=
    scaledDirection_mem_cover v ha
  have heq : parameterPath θ v (a / Real.sqrt n) =
      localAlternative θ (scaledDirection a v) n :=
    parameterPath_compactScaled_eq_localAlternative θ v a n
  have hη : InteriorMeans (parameterPath θ v (a / Real.sqrt n)) := by
    rw [heq]
    exact hinterior (scaledDirection a v) hcover
  have hclose : dist (parameterPath θ v (a / Real.sqrt n)) θ < r := by
    rw [heq]
    exact hdist (scaledDirection a v) hcover
  have hsubclose : dist (⟨parameterPath θ v
      (a / Real.sqrt n), hη⟩ : Θ) θsub < r := by
    change dist (parameterPath θ v (a / Real.sqrt n)) θ < r
    exact hclose
  have hout := hcontrol (x := (⟨parameterPath θ v
    (a / Real.sqrt n), hη⟩ : Θ)) hsubclose
  simpa [v, θsub, upperEnvelope_selectedDirection θ p ε hp hθ hε,
    dist_comm] using hout

/-- The prior-averaged per-sample stationary information envelope. [The sequential Prior Information Envelope](goal) is determined by [the displayed parameters](hyp:θ,p,ε,R,hp,hθ,hε,n). -/
noncomputable def sequentialPriorInformationEnvelope
    (θ : TrialParameter) (p ε R : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (n : ℕ) : ℝ :=
  ∫ a, sequentialVTPrior R a *
    upperEnvelope
      (parameterPath θ
        (direction (selectedDirection θ p ε hp hθ hε))
        (a / Real.sqrt n)) p ε
      (selectedDirection θ p ε hp hθ hε)
    ∂parameterMeasure (-R) R

/-- Once the compact path lies in the interior, its selected envelope is continuous on the scalar interval and hence measurable for the prior measure. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hR,hinterior), [the aestrongly Measurable prior Weighted upper Envelope](goal).

Under the stated assumptions, the aestrongly Measurable prior Weighted upper Envelope. -/
lemma aestronglyMeasurable_priorWeighted_upperEnvelope
    (θ : TrialParameter) (p ε R : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hR : 0 < R)
    (n : ℕ)
    (hinterior : ∀ a ∈ Icc (-R) R, InteriorMeans
      (parameterPath θ
        (direction (selectedDirection θ p ε hp hθ hε))
        (a / Real.sqrt n))) :
    AEStronglyMeasurable (fun a => sequentialVTPrior R a *
      upperEnvelope
        (parameterPath θ
          (direction (selectedDirection θ p ε hp hθ hε))
          (a / Real.sqrt n)) p ε
        (selectedDirection θ p ε hp hθ hε))
      (parameterMeasure (-R) R) := by
  let v := direction (selectedDirection θ p ε hp hθ hε)
  let Θ := {η : TrialParameter // InteriorMeans η}
  let path : ℝ → TrialParameter := fun a =>
    parameterPath θ v (a / Real.sqrt n)
  let pathSub : ↥(Icc (-R) R) → Θ := fun a =>
    ⟨path a.1, hinterior a.1 a.2⟩
  have hpath : Continuous path := by
    apply continuous_pi
    intro k
    dsimp [path, parameterPath]
    exact continuous_const.add
      ((continuous_id.div_const _).mul continuous_const)
  have hpathSub : Continuous pathSub := by
    apply Continuous.subtype_mk
    exact hpath.comp continuous_subtype_val
  have henv : Continuous fun a : ↥(Icc (-R) R) =>
      upperEnvelope (pathSub a).1 p ε
        (selectedDirection θ p ε hp hθ hε) :=
    (continuous_upperEnvelope_interior p ε
      (selectedDirection θ p ε hp hθ hε) hp hε.le).comp hpathSub
  have henvOn : ContinuousOn (fun a => upperEnvelope (path a) p ε
      (selectedDirection θ p ε hp hθ hε)) (Icc (-R) R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun a : ↥(Icc (-R) R) =>
      upperEnvelope (path a.1) p ε
        (selectedDirection θ p ε hp hθ hε))
    simpa only [pathSub] using henv
  have hprior : Continuous (sequentialVTPrior R) := by
    unfold sequentialVTPrior
    exact (smoothPrior_contDiff (by linarith)).continuous
  unfold parameterMeasure
  exact (hprior.continuousOn.mul henvOn).aestronglyMeasurable measurableSet_Icc

/-- For all sufficiently large sample sizes, the prior-weighted stationary information envelope is integrable under the compact parameter measure. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hR), [the eventually integrable prior Weighted upper Envelope](goal).

Under the stated assumptions, the eventually integrable prior Weighted upper Envelope. -/
lemma eventually_integrable_priorWeighted_upperEnvelope
    (θ : TrialParameter) (p ε R : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hR : 0 < R) :
    ∀ᶠ n : ℕ in atTop, Integrable (fun a => sequentialVTPrior R a *
      upperEnvelope
        (parameterPath θ
          (direction (selectedDirection θ p ε hp hθ hε))
          (a / Real.sqrt n)) p ε
        (selectedDirection θ p ε hp hθ hε))
      (parameterMeasure (-R) R) := by
  let v := direction (selectedDirection θ p ε hp hθ hε)
  let F : ℕ → ℝ → ℝ := fun n a => sequentialVTPrior R a *
    upperEnvelope (parameterPath θ v (a / Real.sqrt n)) p ε
      (selectedDirection θ p ε hp hθ hε)
  let B : ℝ → ℝ := fun a =>
    (|Jstar θ p ε| + 1) * sequentialVTPrior R a
  have hpriorInt : Integrable (sequentialVTPrior R)
      (parameterMeasure (-R) R) := by
    unfold sequentialVTPrior
    exact smoothPrior_integrable_parameterMeasure (by linarith)
  have hBint : Integrable B (parameterMeasure (-R) R) := by
    exact hpriorInt.const_mul (|Jstar θ p ε| + 1)
  have hu := tendstoUniformlyOn_upperEnvelope_compactScaled_selectedDirection
    θ p ε R hp hθ hε
  rw [Metric.tendstoUniformlyOn_iff] at hu
  have hclose := hu 1 zero_lt_one
  have hinterior := eventually_parameterPath_compactScaled_interior
    θ v R hθ
  refine (hclose.and hinterior).mono ?_
  intro n hn
  rcases hn with ⟨hnclose, hninterior⟩
  have hmeas : AEStronglyMeasurable (F n)
      (parameterMeasure (-R) R) := by
    exact aestronglyMeasurable_priorWeighted_upperEnvelope
      θ p ε R hp hθ hε hR n hninterior
  apply hBint.mono' hmeas
  have hmem : ∀ᵐ a ∂parameterMeasure (-R) R, a ∈ Icc (-R) R := by
    unfold parameterMeasure
    exact ae_restrict_mem measurableSet_Icc
  filter_upwards [hmem] with a ha
  have henv : |upperEnvelope (parameterPath θ v
      (a / Real.sqrt n)) p ε
      (selectedDirection θ p ε hp hθ hε)| < |Jstar θ p ε| + 1 := by
    have hd := hnclose a ha
    rw [Real.dist_eq] at hd
    calc
      |upperEnvelope (parameterPath θ v (a / Real.sqrt n)) p ε
          (selectedDirection θ p ε hp hθ hε)| =
          |Jstar θ p ε +
            (upperEnvelope (parameterPath θ v (a / Real.sqrt n)) p ε
              (selectedDirection θ p ε hp hθ hε) - Jstar θ p ε)| := by
        congr 1
        ring
      _ ≤
          |Jstar θ p ε| +
            |upperEnvelope (parameterPath θ v (a / Real.sqrt n)) p ε
              (selectedDirection θ p ε hp hθ hε) - Jstar θ p ε| :=
        abs_add_le _ _
      _ < |Jstar θ p ε| + 1 := by
        rw [abs_sub_comm]
        linarith
  have hpriorNonneg := (sequentialVTPrior_facts hR).nonneg a
  dsimp [F, B]
  rw [abs_mul, abs_of_nonneg hpriorNonneg]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left henv.le hpriorNonneg)

/-- A pointwise compact-prior Fisher bound by `n` times the stationary envelope integrates to `n` times the per-sample prior information envelope. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hR,hfInt,henvInt,hle), [the integral prior Weighted le nat mul sequential Prior Information Envelope](goal).

Under the stated assumptions, the integral prior Weighted le nat mul sequential Prior Information Envelope. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma integral_priorWeighted_le_nat_mul_sequentialPriorInformationEnvelope
    (θ : TrialParameter) (p ε R : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hR : 0 < R) (n : ℕ) (f : ℝ → ℝ)
    (hfInt : Integrable (fun a => sequentialVTPrior R a * f a)
      (parameterMeasure (-R) R))
    (henvInt : Integrable (fun a => sequentialVTPrior R a *
      upperEnvelope
        (parameterPath θ
          (direction (selectedDirection θ p ε hp hθ hε))
          (a / Real.sqrt n)) p ε
        (selectedDirection θ p ε hp hθ hε))
      (parameterMeasure (-R) R))
    (hle : ∀ a ∈ Icc (-R) R, f a ≤ (n : ℝ) *
      upperEnvelope
        (parameterPath θ
          (direction (selectedDirection θ p ε hp hθ hε))
          (a / Real.sqrt n)) p ε
        (selectedDirection θ p ε hp hθ hε)) :
    (∫ a, sequentialVTPrior R a * f a
      ∂parameterMeasure (-R) R) ≤
      (n : ℝ) * sequentialPriorInformationEnvelope
        θ p ε R hp hθ hε n := by
  let env : ℝ → ℝ := fun a => upperEnvelope
    (parameterPath θ
      (direction (selectedDirection θ p ε hp hθ hε))
      (a / Real.sqrt n)) p ε
    (selectedDirection θ p ε hp hθ hε)
  have hrightInt : Integrable (fun a =>
      sequentialVTPrior R a * ((n : ℝ) * env a))
      (parameterMeasure (-R) R) := by
    convert henvInt.const_mul (n : ℝ) using 1
    funext a
    ring
  calc
    (∫ a, sequentialVTPrior R a * f a
        ∂parameterMeasure (-R) R) ≤
        ∫ a, sequentialVTPrior R a * ((n : ℝ) * env a)
          ∂parameterMeasure (-R) R := by
      apply integral_mono_ae hfInt hrightInt
      have hmem : ∀ᵐ a ∂parameterMeasure (-R) R,
          a ∈ Icc (-R) R := by
        unfold parameterMeasure
        exact ae_restrict_mem measurableSet_Icc
      filter_upwards [hmem] with a ha
      exact mul_le_mul_of_nonneg_left (hle a ha)
        ((sequentialVTPrior_facts hR).nonneg a)
    _ = (n : ℝ) * sequentialPriorInformationEnvelope
        θ p ε R hp hθ hε n := by
      rw [show (fun a => sequentialVTPrior R a * ((n : ℝ) * env a)) =
          fun a => (n : ℝ) * (sequentialVTPrior R a * env a) by
        funext a
        ring]
      rw [integral_const_mul]
      rfl

/-- The normalized compact-prior average of the selected per-sample envelope converges to the least-favorable stationary information `Jstar`. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hR), [the tendsto sequential Prior Information Envelope](goal).

Under the stated assumptions, the tendsto sequential Prior Information Envelope. -/
lemma tendsto_sequentialPriorInformationEnvelope
    (θ : TrialParameter) (p ε R : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hR : 0 < R) :
    Tendsto (sequentialPriorInformationEnvelope θ p ε R hp hθ hε)
      atTop (nhds (Jstar θ p ε)) := by
  let v := direction (selectedDirection θ p ε hp hθ hε)
  let F : ℕ → ℝ → ℝ := fun n a => sequentialVTPrior R a *
    upperEnvelope (parameterPath θ v (a / Real.sqrt n)) p ε
      (selectedDirection θ p ε hp hθ hε)
  let limit : ℝ → ℝ := fun a => sequentialVTPrior R a * Jstar θ p ε
  let B : ℝ → ℝ := fun a =>
    (|Jstar θ p ε| + 1) * sequentialVTPrior R a
  have hpriorInt : Integrable (sequentialVTPrior R)
      (parameterMeasure (-R) R) := by
    unfold sequentialVTPrior
    exact smoothPrior_integrable_parameterMeasure (by linarith)
  have hBint : Integrable B (parameterMeasure (-R) R) :=
    hpriorInt.const_mul (|Jstar θ p ε| + 1)
  have hu := tendstoUniformlyOn_upperEnvelope_compactScaled_selectedDirection
    θ p ε R hp hθ hε
  have huMetric := Metric.tendstoUniformlyOn_iff.mp hu
  have hclose := huMetric 1 zero_lt_one
  have hinterior := eventually_parameterPath_compactScaled_interior
    θ v R hθ
  have hmeas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable (F n) (parameterMeasure (-R) R) := by
    refine hinterior.mono ?_
    intro n hn
    exact aestronglyMeasurable_priorWeighted_upperEnvelope
      θ p ε R hp hθ hε hR n hn
  have hmem : ∀ᵐ a ∂parameterMeasure (-R) R, a ∈ Icc (-R) R := by
    unfold parameterMeasure
    exact ae_restrict_mem measurableSet_Icc
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ a ∂parameterMeasure (-R) R,
      ‖F n a‖ ≤ B a := by
    refine hclose.mono ?_
    intro n hn
    filter_upwards [hmem] with a ha
    have henv : |upperEnvelope (parameterPath θ v
        (a / Real.sqrt n)) p ε
        (selectedDirection θ p ε hp hθ hε)| ≤ |Jstar θ p ε| + 1 := by
      have hd := hn a ha
      rw [Real.dist_eq] at hd
      calc
        |upperEnvelope (parameterPath θ v (a / Real.sqrt n)) p ε
            (selectedDirection θ p ε hp hθ hε)| =
            |Jstar θ p ε +
              (upperEnvelope (parameterPath θ v (a / Real.sqrt n)) p ε
                (selectedDirection θ p ε hp hθ hε) - Jstar θ p ε)| := by
          congr 1
          ring
        _ ≤
            |Jstar θ p ε| +
              |upperEnvelope (parameterPath θ v (a / Real.sqrt n)) p ε
                (selectedDirection θ p ε hp hθ hε) - Jstar θ p ε| :=
          abs_add_le _ _
        _ ≤ |Jstar θ p ε| + 1 := by
          rw [abs_sub_comm]
          linarith
    have hpriorNonneg := (sequentialVTPrior_facts hR).nonneg a
    dsimp [F, B]
    rw [abs_mul, abs_of_nonneg hpriorNonneg]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left henv hpriorNonneg)
  have hlim : ∀ᵐ a ∂parameterMeasure (-R) R,
      Tendsto (fun n => F n a) atTop (nhds (limit a)) := by
    filter_upwards [hmem] with a ha
    exact (hu.tendsto_at ha).const_mul (sequentialVTPrior R a)
  have hIntegral := tendsto_integral_filter_of_dominated_convergence
    B hmeas hbound hBint hlim
  have hlimitIntegral : ∫ a, limit a ∂parameterMeasure (-R) R =
      Jstar θ p ε := by
    dsimp [limit]
    rw [integral_mul_const, (sequentialVTPrior_facts hR).normalized, one_mul]
  rw [hlimitIntegral] at hIntegral
  change Tendsto (fun n =>
    sequentialPriorInformationEnvelope θ p ε R hp hθ hε n)
    atTop (nhds (Jstar θ p ε))
  simpa only [sequentialPriorInformationEnvelope, F, v] using hIntegral

end CausalSmith.Stat.LdpAteEfficiencySurface
