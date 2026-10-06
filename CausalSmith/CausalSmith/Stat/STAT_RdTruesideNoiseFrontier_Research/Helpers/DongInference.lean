module
public import Causalean.PO.Analysis.Regression
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


/-- Dong's comparison allows real-valued potential outcomes. -/
abbrev DongLatent := ℝ × ℝ × ℝ × ℝ
/-- Observed-treatment outcome in Dong's experiment. Given [the displayed inputs and assumptions](hyp:z), [this definition specifies the stated object](goal). -/
def dongY (z : DongLatent) : ℝ := if 0 ≤ z.1 then z.2.2.1 else z.2.1
/-- Ordinary characteristic function, with the source's positive Fourier sign. Given [the displayed inputs and assumptions](hyp:Ω,P,X,t), [this definition specifies the stated object](goal). -/
def dongChar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℂ :=
  ∫ z, Complex.exp (Complex.I * (t * X z : ℝ)) ∂P
/-- Fourier transform of the source's real kernel. Given [the displayed inputs and assumptions](hyp:K,t), [this definition specifies the stated object](goal). -/
def dongFourier (K : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, (K x : ℂ) * Complex.exp (Complex.I * (t*x : ℝ))
/-- The source's iterated Fourier derivative. Given [the displayed inputs and assumptions](hyp:K,k), [this definition specifies the stated object](goal). -/
def dongFourierDeriv (K : ℝ → ℝ) (k : ℕ) : ℝ → ℂ := deriv^[k] (dongFourier K)
/-- Actual observed-treatment deconvolution weights, Section 2.3.1, printed p.53. Given [the displayed inputs and assumptions](hyp:P,K,h,k,r), [this definition specifies the stated object](goal). -/
def dongWeight (P : Measure DongLatent) (K : ℝ → ℝ) (h : ℝ) (k : ℕ) (r : ℝ) : ℝ :=
  ((1 / (2 * (Real.pi : ℂ) * Complex.I ^ k)) *
    ∫ t : ℝ, dongFourierDeriv K k (t*h) / dongChar P (fun z => z.2.2.2) (-t) *
      Complex.exp (-Complex.I * (t*r : ℝ))).re
/-- Arm membership uses true treatment status, as in the source. Given [the displayed inputs and assumptions](hyp:s,x), [this definition specifies the stated object](goal). -/
def dongArm (s : Bool) (x : ℝ) : ℝ := if (decide (0 ≤ x) : Bool) = s then 1 else 0
/-- Source's unmarked sample average. Given [the displayed inputs and assumptions](hyp:P,K,h,s,k,n,z), [this definition specifies the stated object](goal). -/
def dongA (P : Measure DongLatent) (K : ℝ → ℝ) (h : ℝ) (s : Bool) (k : ℕ)
    {n : ℕ} (z : Fin n → DongLatent) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, dongWeight P K h k ((z i).1 + (z i).2.2.2) * dongArm s (z i).1
/-- Source's marked sample average. Given [the displayed inputs and assumptions](hyp:P,K,h,s,k,n,z), [this definition specifies the stated object](goal). -/
def dongB (P : Measure DongLatent) (K : ℝ → ℝ) (h : ℝ) (s : Bool) (k : ℕ)
    {n : ℕ} (z : Fin n → DongLatent) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, dongWeight P K h k ((z i).1 + (z i).2.2.2) * dongY (z i) * dongArm s (z i).1
/-- Source's local-linear arm intercept, with exactly its displayed ratio. Given [the displayed inputs and assumptions](hyp:P,K,h,s,n,z), [this definition specifies the stated object](goal). -/
def dongIntercept (P : Measure DongLatent) (K : ℝ → ℝ) (h : ℝ) (s : Bool)
    {n : ℕ} (z : Fin n → DongLatent) : ℝ :=
  (dongA P K h s 2 z * dongB P K h s 0 z - dongA P K h s 1 z * dongB P K h s 1 z) /
    (dongA P K h s 2 z * dongA P K h s 0 z - dongA P K h s 1 z ^ 2)
/-- Dong's observed-treatment contrast estimator (2.3.3). Given [the displayed inputs and assumptions](hyp:P,K,h,n,z), [this definition specifies the stated object](goal). -/
def dongEstimator (P : Measure DongLatent) (K : ℝ → ℝ) (h : ℝ)
    {n : ℕ} (z : Fin n → DongLatent) : ℝ :=
  dongIntercept P K h true z - dongIntercept P K h false z
/-- Genuine conditional potential means on a cutoff neighborhood. The reused regression
predicate requires integrability of each potential outcome and of its mean representative
on that neighborhood before its measurable-slice integral characterization applies. Given [the displayed inputs and assumptions](hyp:P,mu), [this definition specifies the stated object](goal). -/
def DongConditionalMeans (P : Measure DongLatent) (mu : Bool → ℝ → ℝ) : Prop :=
  ∃ r > 0, ∀ d : Bool,
    Causalean.PO.IsRegressionFunction (P.restrict {z | z.1 ∈ Ioo (-r) r})
      (fun z => z.1) (fun z => if d then z.2.2.1 else z.2.1) (mu d)
/-- The score density and well-defined local conditional potential means are pinned to the law.
No unrestricted Bochner integral of a nonintegrable counterfactual is used as a version certificate. Given [the displayed inputs and assumptions](hyp:P,f,mu), [this definition specifies the stated object](goal). -/
def DongVersions (P : Measure DongLatent) (f : ℝ → ℝ) (mu : Bool → ℝ → ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ x, 0 ≤ f x) ∧
  P.map (fun z => z.1) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
  DongConditionalMeans P mu
/-- Dong's cutoff target. Given [the displayed inputs and assumptions](hyp:mu), [this definition specifies the stated object](goal). -/
def dongTarget (mu : Bool → ℝ → ℝ) : ℝ := mu true 0 - mu false 0
/-- Continuous part of the observed regression after removing the cutoff jump. Given [the displayed inputs and assumptions](hyp:mu,x), [this definition specifies the stated object](goal). -/
def dongRegression (mu : Bool → ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then mu true x - dongTarget mu else mu false x
/-- Assumption 8: positive cutoff density and continuous potential means at zero. Given [the displayed inputs and assumptions](hyp:f,mu), [this definition specifies the stated object](goal). -/
def DongA8 (f : ℝ → ℝ) (mu : Bool → ℝ → ℝ) : Prop :=
  0 < f 0 ∧ ∀ d, ContinuousAt (mu d) 0
/-- Assumption 9, specialized to a fixed positive-scale Gaussian error. Given [the displayed inputs and assumptions](hyp:P,σ), [this definition specifies the stated object](goal). -/
def DongA9Gaussian (P : Measure DongLatent) (σ : ℝ) : Prop :=
  0 < σ ∧ P.map (fun z => z.2.2.2) = gaussianReal 0 ⟨σ^2, sq_nonneg σ⟩ ∧
  IndepFun (fun z => z.2.2.2) (fun z => (dongY z, z.1)) P
/-- Source's Assumption 11 on transforms, local smoothness, and real symmetric kernel moments.
IID sampling and a known fixed error law are built into the experiment and weights. Given [the displayed inputs and assumptions](hyp:P,f,mu,K), [this definition specifies the stated object](goal). -/
def DongA11 (P : Measure DongLatent) (f : ℝ → ℝ) (mu : Bool → ℝ → ℝ)
    (K : ℝ → ℝ) : Prop :=
  Integrable (fun t => ‖dongChar P (fun z => z.1) t‖) ∧
  (∀ t, dongChar P (fun z => z.2.2.2) t ≠ 0) ∧
  (∀ k ≤ 2, (∃ t, dongFourierDeriv K k t ≠ 0) ∧
    ∀ h > 0, Integrable (fun t => ‖dongFourierDeriv K k (t*h) /
      dongChar P (fun z => z.2.2.2) t‖)) ∧
  (∃ r > 0, ContDiffOn ℝ 2 f (Ioo (-r) r) ∧
    (∃ c > 0, ∀ x ∈ Ioo (-r) r, c ≤ f x) ∧
    ContDiffOn ℝ 2 (dongRegression mu) (Ioo (-r) 0 ∪ Ioo 0 r) ∧
    ContinuousAt (dongRegression mu) 0 ∧
    (∀ k ∈ ({1, 2} : Finset ℕ), ∃ left right : ℝ,
      Tendsto (deriv^[k] (dongRegression mu)) (nhdsWithin 0 (Iio 0)) (nhds left) ∧
      Tendsto (deriv^[k] (dongRegression mu)) (nhdsWithin 0 (Ioi 0)) (nhds right))) ∧
  (∀ x, K (-x) = K x) ∧ (∫ x, K x) = 1 ∧
  (∀ k ≤ 3, Integrable (fun x => |x|^k * |K x|))
/-- One-sided kernel moments and the population linearization constants. Given [the displayed inputs and assumptions](hyp:K,s,k), [this definition specifies the stated object](goal). -/
def dongKernelMoment (K : ℝ → ℝ) (s : Bool) (k : ℕ) : ℝ :=
  ∫ x in (if s then Ioi (0 : ℝ) else Iio (0 : ℝ)), x^k * K x
/-- Source's Section 2.8.1 leading summand P_{1,n,1}, with its displayed residual. Given [the displayed inputs and assumptions](hyp:P,f,mu,K,h,s,z), [this definition specifies the stated object](goal). -/
def dongLeading (P : Measure DongLatent) (f : ℝ → ℝ) (mu : Bool → ℝ → ℝ)
    (K : ℝ → ℝ) (h : ℝ) (s : Bool) (z : DongLatent) : ℝ :=
  let a0 := f 0 * dongKernelMoment K s 0
  let a1 := f 0 * dongKernelMoment K s 1
  let a2 := f 0 * dongKernelMoment K s 2
  let residual := dongY z - (if 0 ≤ z.1 then dongTarget mu else 0) - dongRegression mu 0
  (a2 * dongWeight P K h 0 (z.1 + z.2.2.2) - a1 * dongWeight P K h 1 (z.1 + z.2.2.2)) /
    (a0*a2 - a1^2) * residual * dongArm s z.1
/-- The source's logarithmic bandwidth at Gaussian supersmooth exponent two. Given [the displayed inputs and assumptions](hyp:σ,b,n), [this definition specifies the stated object](goal). -/
def dongBandwidth (σ b : ℝ) (n : ℕ) : ℝ :=
  (b * (σ^2/2)) ^ (1/2 : ℝ) * (Real.log n) ^ (-1/2 : ℝ)
/-- Assumption 13 at fixed Gaussian scale, with the exact leading-summand Lyapunov restriction. Given [the displayed inputs and assumptions](hyp:P,f,mu,K,σ,b), [this definition specifies the stated object](goal). -/
def DongA13Gaussian (P : Measure DongLatent) (f : ℝ → ℝ) (mu : Bool → ℝ → ℝ)
    (K : ℝ → ℝ) (σ b : ℝ) : Prop :=
  (∀ t ∉ Icc (-1 : ℝ) 1, dongFourier K t = 0) ∧
  (∀ k ≤ 2, ∃ C : ℝ, ∀ t, ‖dongFourierDeriv K k t‖ ≤ C) ∧
  ∃ η > 0, ∀ s : Bool,
    Tendsto (fun n : ℕ =>
      (∫ z, |dongLeading P f mu K (dongBandwidth σ b n) s z|^2 ∂P) *
        (n : ℝ) ^ (η/(2+η)) * (dongBandwidth σ b n) ^ ((2+2*η)/(2+η)) *
        Real.exp (-(σ^2) * (dongBandwidth σ b n) ^ (-2 : ℝ))) atTop atTop
/-- Dong's IID latent sample experiment, with the observed estimator using only observable coordinates. Given [the displayed inputs and assumptions](hyp:P,n), [this definition specifies the stated object](goal). -/
def dongExperiment (P : Measure DongLatent) (n : ℕ) : Measure (Fin n → DongLatent) :=
  Measure.pi (fun _ : Fin n => P)
/-- Actual estimator bias; no freely supplied centering sequence. Given [the displayed inputs and assumptions](hyp:P,mu,K,σ,b,n), [this definition specifies the stated object](goal). -/
def dongBias (P : Measure DongLatent) (mu : Bool → ℝ → ℝ) (K : ℝ → ℝ)
    (σ b : ℝ) (n : ℕ) : ℝ :=
  (∫ z, dongEstimator P K (dongBandwidth σ b n) z ∂dongExperiment P n) - dongTarget mu
/-- Actual estimator variance; no freely supplied normalization sequence. Given [the displayed inputs and assumptions](hyp:P,K,σ,b,n), [this definition specifies the stated object](goal). -/
def dongVariance (P : Measure DongLatent) (K : ℝ → ℝ) (σ b : ℝ) (n : ℕ) : ℝ :=
  ProbabilityTheory.variance (dongEstimator P K (dongBandwidth σ b n)) (dongExperiment P n)
/-- Pointwise asymptotic normality, using the equivalent CDF convergence for a continuous Gaussian limit. Given [the displayed inputs and assumptions](hyp:P,mu,K,σ,b), [this definition specifies the stated object](goal). -/
def DongGaussianAsymptoticNormality (P : Measure DongLatent) (mu : Bool → ℝ → ℝ)
    (K : ℝ → ℝ) (σ b : ℝ) : Prop :=
  ∀ t : ℝ, Tendsto (fun n : ℕ => (dongExperiment P n).real {z |
    (dongEstimator P K (dongBandwidth σ b n) z - dongTarget mu - dongBias P mu K σ b n) /
      Real.sqrt (dongVariance P K σ b n) ≤ t}) atTop ((nhds ((gaussianReal 0 1).real (Iic t))))

end CausalSmith.Stat.RdTruesideNoiseFrontier
