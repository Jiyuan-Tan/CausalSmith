module
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.HonestConfidenceSet
public import Causalean.Stat.Minimax.MinimaxValue
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

/-!
# True-side Gaussian measurement-error endpoint frontier

Law-level constructions and the obligations specified by the typed core.
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


/-- The latent coordinates are score, two binary potential outcomes, and error. -/
abbrev Latent := ℝ × Bool × Bool × ℝ -- @realizes X(real carrier) @realizes Ypot(binary pair carrier) @realizes epsilon(real carrier)
/-- The observed coordinates are proxy score, true treatment side, and binary outcome. -/
abbrev Obs := ℝ × Bool × Bool -- @realizes O(carrier of observed triple)
/-- Binary outcomes take their usual numerical values. Given [the displayed inputs and assumptions](hyp:y), [this definition specifies the stated object](goal). -/
def bit (y : Bool) : ℝ := if y then 1 else 0
/-- The latent score coordinate. Given [the displayed inputs and assumptions](hyp:ω), [this definition specifies the stated object](goal). -/
def score (ω : Latent) : ℝ := ω.1 -- @realizes X(real coordinate)
/-- Both potential outcomes remain in the latent schedule. Given [the displayed inputs and assumptions](hyp:d,ω), [this definition specifies the stated object](goal). -/
def pot (d : Bool) (ω : Latent) : ℝ := -- @realizes Ypot(binary potential coordinates)
  bit (if d then ω.2.2.1 else ω.2.1)
/-- The latent perturbation coordinate. Given [the displayed inputs and assumptions](hyp:ω), [this definition specifies the stated object](goal). -/
def errorCoord (ω : Latent) : ℝ := ω.2.2.2 -- @realizes epsilon(real coordinate)
/-- Treatment uses the true latent score. Given [the displayed inputs and assumptions](hyp:ω), [this definition specifies the stated object](goal). -/
def side (ω : Latent) : Bool := decide (0 ≤ score ω) -- @realizes D(true-side cutoff)
/-- The observed outcome is the potential outcome at the assigned side. Given [the displayed inputs and assumptions](hyp:ω), [this definition specifies the stated object](goal). -/
def outcome (ω : Latent) : Bool := -- @realizes Y(binary consistency map)
  if side ω then ω.2.2.1 else ω.2.1
/-- Known-scale perturbation of the latent score. Given [the displayed inputs and assumptions](hyp:σ,ω), [this definition specifies the stated object](goal). -/
def proxy (σ : ℝ) (ω : Latent) : ℝ := score ω + σ * errorCoord ω -- @realizes W(additive proxy)
/-- The common observation map. Given [the displayed inputs and assumptions](hyp:σ,ω), [this definition specifies the stated object](goal). -/
def obs (σ : ℝ) (ω : Latent) : Obs := (proxy σ ω, side ω, outcome ω)

/-- Ambient latent law with its density and continuous conditional-mean versions. -/
structure LatentLaw where
  P : Measure Latent -- @realizes P(latent law)
  prob : IsProbabilityMeasure P -- @realizes P(probability normalization)
  supp : ∀ᵐ ω ∂P, score ω ∈ Icc (-1) 1 -- @realizes X(latent interval)
  f : ℝ → ℝ -- @realizes f(density carrier)
  f_cont : ContinuousOn f (Icc (-1) 1) -- @realizes f(continuous on latent interval)
  f_zero : ∀ x ∉ Icc (-1) 1, f x = 0 -- @realizes f(density supported on latent interval)
  f_nonneg : ∀ x, 0 ≤ f x -- @realizes f(nonnegative density)
  f_int : (∫ x in (-1)..1, f x) = 1 -- @realizes f(density integrates to one)
  density : P.map score = volume.withDensity (fun x => ENNReal.ofReal (f x)) -- @realizes f(score marginal identity)
  mu : Bool → ℝ → ℝ -- @realizes mu(conditional-mean carrier)
  mu_cont : ∀ d, ContinuousOn (mu d) (Icc (-1) 1) -- @realizes mu(full-interval continuous versions)
  mu_version : ∀ d B, MeasurableSet B →
    (∫ ω in {ω | score ω ∈ B}, pot d ω ∂P) =
      ∫ x in B ∩ Icc (-1) 1, mu d x * f x -- @realizes mu(conditional potential-mean identity)

/-- The observed law is the common pushforward. Given [the displayed inputs and assumptions](hyp:L,σ), [this definition specifies the stated object](goal). -/
def Pobs (L : LatentLaw) (σ : ℝ) : Measure Obs := L.P.map (obs σ) -- @realizes Pobs(pushforward)
/-- The cutoff causal contrast. Given [the displayed inputs and assumptions](hyp:L), [this definition specifies the stated object](goal). -/
def theta (L : LatentLaw) : ℝ := L.mu true 0 - L.mu false 0 -- @realizes theta(cutoff potential contrast)
/-- The fractional seminorm on the whole latent interval. Given [the displayed inputs and assumptions](hyp:β,v), [this definition specifies the stated object](goal). -/
def holderSeminorm (β : ℝ) (v : ℝ → ℝ) : ℝ≥0∞ := -- @realizes Hseminorm(full-interval difference quotients)
  sSup {r | ∃ x ∈ Icc (-1 : ℝ) 1, ∃ t ∈ Icc (-1 : ℝ) 1,
    x ≠ t ∧ r = ENNReal.ofReal (|v x - v t| / |x - t| ^ β)}
/-- Arm reflection. Given [the displayed inputs and assumptions](hyp:d), [this definition specifies the stated object](goal). -/
def sgn (d : Bool) : ℝ := if d then 1 else -1 -- @realizes Sign(arm reflection)
/-- Centered Gaussian density at the public noise scale. Given [the displayed inputs and assumptions](hyp:σ,w), [this definition specifies the stated object](goal). -/
def phi (σ w : ℝ) : ℝ := -- @realizes phi(centered Gaussian density)
  (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (-w ^ 2 / (2 * σ ^ 2))
/-- Mathlib shifted Legendre uses the reversed interval orientation. Given [the displayed inputs and assumptions](hyp:j,t), [this definition specifies the stated object](goal). -/
def legendreP (j : ℕ) (t : ℝ) : ℝ := -- @realizes Legendre(normalized Mathlib polynomial)
  Polynomial.aeval ((1 - t) / 2) (Polynomial.shiftedLegendre j)

-- @env: S1
variable (β σ : ℝ) -- @realizes beta(public smoothness parameter) @realizes sigma(public noise parameter)

/-- Standard Gaussian error. Given [the displayed inputs and assumptions](hyp:L), [this definition specifies the stated object](goal). -/
-- @node: ass:gaussian
def GaussianError (L : LatentLaw) : Prop := L.P.map errorCoord = gaussianReal 0 1
/-- Error is independent of the whole potential-outcome schedule jointly with the score. Given [the displayed inputs and assumptions](hyp:L), [this definition specifies the stated object](goal). -/
-- @node: ass:error-independence
def ErrorIndependence (L : LatentLaw) : Prop :=
  IndepFun errorCoord (fun ω : Latent => (score ω, ω.2.1, ω.2.2.1)) L.P
/-- Global lower and upper density bounds. Given [the displayed inputs and assumptions](hyp:L), [this definition specifies the stated object](goal). -/
-- @node: ass:density-bounds
def DensityBounds (L : LatentLaw) : Prop :=
  ∀ x ∈ Icc (-1 : ℝ) 1, 1/4 ≤ L.f x ∧ L.f x ≤ 3/4 -- @realizes f(global density bounds)
/-- Interior bounds for each potential-mean version. Given [the displayed inputs and assumptions](hyp:L), [this definition specifies the stated object](goal). -/
-- @node: ass:mean-bounds
def MeanBounds (L : LatentLaw) : Prop :=
  ∀ d, ∀ x ∈ Icc (-1 : ℝ) 1, 1/4 ≤ L.mu d x ∧ L.mu d x ≤ 3/4 -- @realizes mu(global interior bounds)
/-- Radius-two Hölder restriction, written pointwise to avoid a real-supremum junk value. Given [the displayed inputs and assumptions](hyp:L), [this definition specifies the stated object](goal). -/
-- @node: ass:mean-holder
def MeanHolder (L : LatentLaw) : Prop :=
  ∀ d, ∀ x ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
    |L.mu d x - L.mu d t| ≤ 2 * |x - t| ^ β -- @realizes mu(full-interval Holder modulus)
/-- The exact benchmark class contains precisely the five maintained member atoms. -/
-- @node: def:model
structure LatentModel (β σ : ℝ) (L : LatentLaw) : Prop where -- @realizes Model(benchmark class)
  gaussian : GaussianError L
  independent : ErrorIndependence L
  density : DensityBounds L
  means : MeanBounds L
  holder : MeanHolder β L

/-- The noise scale indexes the observed experiment, and does not change latent membership. -/
abbrev Model (β σ : ℝ) (L : LatentLaw) : Prop := LatentModel β σ L

-- @env: S2
variable (n : ℕ) -- @realizes n(sample size, restricted to n≥2 in statements)
/-- Finite observed sample. -/
abbrev Sample (n : ℕ) := Fin n → Obs -- @realizes Sample(finite observed product) @realizes i(finite unit index)
/-- Randomized procedure input, with an independent unit-interval seed. -/
abbrev Input (n : ℕ) := Sample n × unitInterval -- @realizes U(unit interval seed carrier)
/-- The seed has uniform probability measure on the unit interval. Given the displayed inputs, [this definition specifies the stated object](goal). -/
def seedLaw : Measure unitInterval := volume -- @realizes U(uniform seed law)
/-- IID observation law before procedure randomization. Given [the displayed inputs and assumptions](hyp:L,σ,n), [this definition specifies the stated object](goal). -/
def sampleLaw (L : LatentLaw) (σ : ℝ) (n : ℕ) : Measure (Sample n) :=
  Measure.pi (fun _ : Fin n => Pobs L σ) -- @realizes Sample(IID observed law)
/-- The sample experiment includes the independent uniform seed. Given [the displayed inputs and assumptions](hyp:L,σ,n), [this definition specifies the stated object](goal). -/
def experiment (L : LatentLaw) (σ : ℝ) (n : ℕ) : Measure (Input n) := -- @realizes Experiment(product law) @realizes U(independent seed via sampleLaw.prod seedLaw)
  (sampleLaw L σ n).prod seedLaw
/-- Every measurable real-valued procedure is permitted. -/
abbrev Estimator (n : ℕ) := {T : Input n → ℝ // Measurable T} -- @realizes Estimators(all measurable maps)
/-- Connected closed intervals with measurable endpoints, lying in the declared target region. -/
structure IntervalProc (n : ℕ) where -- @realizes Intervals(interval procedure carrier)
  lo : Input n → ℝ
  hi : Input n → ℝ
  lo_meas : Measurable lo
  hi_meas : Measurable hi
  endpoints : ∀ z, -1 ≤ lo z ∧ lo z ≤ hi z ∧ hi z ≤ 1
/-- Uniform ninety-percent coverage on the exact benchmark. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
-- @node: def:honest-class
def honestIntervals (β : ℝ) (n : ℕ) (σ : ℝ) : Set (IntervalProc n) := -- @realizes Intervals(uniform honesty)
  {I | ∀ L, Model β σ L →
    (9/10 : ℝ) ≤ (experiment L σ n).real (Causalean.Stat.coverageEvent I.lo I.hi (theta L))}
/-- Extended absolute loss risk retains infinite loss of arbitrary procedures. Given [the displayed inputs and assumptions](hyp:L,σ,n,T), [this definition specifies the stated object](goal). -/
def absRisk (L : LatentLaw) (σ : ℝ) (n : ℕ) (T : Input n → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal |T z - theta L| ∂experiment L σ n
/-- Extended expected length. Given [the displayed inputs and assumptions](hyp:L,σ,n,I), [this definition specifies the stated object](goal). -/
def expectedLength (L : LatentLaw) (σ : ℝ) (n : ℕ) (I : IntervalProc n) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (Causalean.Stat.intervalLength (I.lo z) (I.hi z)) ∂experiment L σ n
/-- Minimax absolute risk, converted to real only after minimizing extended loss. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def risk (β : ℝ) (n : ℕ) (σ : ℝ) : ℝ := -- @realizes Risk(extended minimax absolute loss)
  (Causalean.Stat.minimaxValueENNReal
    (fun (T : Estimator n) (L : {L // Model β σ L}) => absRisk L.val σ n T.val)).toReal
/-- Minimax honest expected length. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def lengthRisk (β : ℝ) (n : ℕ) (σ : ℝ) : ℝ := -- @realizes Length(extended minimax honest length)
  (Causalean.Stat.minimaxValueENNReal
    (fun (I : {I // I ∈ honestIntervals β n σ}) (L : {L // Model β σ L}) =>
      expectedLength L.val σ n I.val)).toReal
open Classical in
/-- Extended chi-square, with infinity when absolute continuity fails. Given [the displayed inputs and assumptions](hyp:Ω,μ,ν), [this definition specifies the stated object](goal). -/
def chiSqExt {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) : ℝ≥0∞ := -- @realizes Chisq(extended divergence)
  if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (((μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν else ⊤
/-- Event-supremum total variation. -/
abbrev tvDist {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) : ℝ := -- @realizes TV(event supremum)
  Causalean.Stat.tvDist μ ν
/-- Off absolute continuity, the extended divergence is infinite. Given [the displayed inputs and assumptions](hyp:Ω,μ,ν,h), [the stated mathematical conclusion holds](goal). -/
lemma chiSqExt_of_not_ac {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    (h : ¬ μ ≪ ν) : chiSqExt μ ν = ⊤ := by
  simp only [chiSqExt, if_neg h]
/-- The extended divergence agrees with the finite-real substrate when the density square is integrable. Given [the displayed inputs and assumptions](hyp:Ω,μ,ν,hac,hint), [the stated mathematical conclusion holds](goal). -/
lemma chiSqExt_eq_ofReal_chiSqDiv {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1)^2) ν) :
    chiSqExt μ ν = ENNReal.ofReal (Causalean.Stat.chiSqDiv μ ν) := by
  rw [chiSqExt, if_pos hac, Causalean.Stat.chiSqDiv]
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
/-- Finiteness discharges both hypotheses needed by the finite-real chi-square API. Given [the displayed inputs and assumptions](hyp:Ω,μ,ν), [the stated mathematical conclusion holds](goal). -/
lemma chiSqExt_ne_top_iff {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    chiSqExt μ ν ≠ ⊤ ↔ μ ≪ ν ∧
      Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1)^2) ν := by
  by_cases hac : μ ≪ ν
  · rw [chiSqExt, if_pos hac]
    have hmeas : AEStronglyMeasurable (fun x => ((μ.rnDeriv ν x).toReal - 1)^2) ν := by
      exact (((μ.measurable_rnDeriv ν).ennreal_toReal.sub measurable_const).pow_const 2).aestronglyMeasurable
    rw [lintegral_ofReal_ne_top_iff_integrable hmeas
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    exact (and_iff_right hac).symm
  · rw [chiSqExt_of_not_ac μ ν hac]
    simp only [ne_eq, not_true_eq_false, hac, false_and]

/-- Laws on the unrestricted score space with locally continuous potential-mean versions. -/
structure GaussianLawData where
  Q : Measure Latent
  prob : IsProbabilityMeasure Q
  a : ℝ → ℝ
  density : Q.map score = volume.withDensity (fun x => ENNReal.ofReal (a x))
  density_nonneg : ∀ x, 0 ≤ a x
  v : Bool → ℝ → ℝ
  version : ∀ d B, MeasurableSet B →
    (∫ ω in {ω | score ω ∈ B}, pot d ω ∂Q) = ∫ x in B, v d x * a x
  mean_cont : ∃ r > 0, ∀ d, ContinuousOn (v d) (Ioo (-r) r)
/-- The larger Gaussian observed-treatment identification class. The cutoff versions
are means of binary potentials, so their range is explicitly recorded as `[0,1]`. Given [the displayed inputs and assumptions](hyp:σ,Q), [this definition specifies the stated object](goal). -/
def GaussianIdClass (σ : ℝ) (Q : GaussianLawData) : Prop :=
  (∃ r > 0, ContinuousOn Q.a (Ioo (-r) r) ∧ ∀ x ∈ Ioo (-r) r, 0 < Q.a x) ∧
  Q.Q.map errorCoord = gaussianReal 0 1 ∧
  IndepFun errorCoord (fun ω => (score ω, bit (outcome ω))) Q.Q ∧
  (∀ d, 0 ≤ Q.v d 0 ∧ Q.v d 0 ≤ 1)
/-- Observed law in the larger identification class. Given [the displayed inputs and assumptions](hyp:Q,σ), [this definition specifies the stated object](goal). -/
def gaussianPobs (Q : GaussianLawData) (σ : ℝ) : Measure Obs := Q.Q.map (obs σ)
/-- The larger-class causal target. Given [the displayed inputs and assumptions](hyp:Q), [this definition specifies the stated object](goal). -/
def gaussianTarget (Q : GaussianLawData) : ℝ := Q.v true 0 - Q.v false 0
/-- The larger-class experiment uses the same finite product and independent seed. Given [the displayed inputs and assumptions](hyp:Q,σ,n), [this definition specifies the stated object](goal). -/
def gaussianExperiment (Q : GaussianLawData) (σ : ℝ) (n : ℕ) : Measure (Input n) :=
  (Measure.pi (fun _ : Fin n => gaussianPobs Q σ)).prod seedLaw
/-- Honest intervals on the larger identification class. Given [the displayed inputs and assumptions](hyp:n,σ), [this definition specifies the stated object](goal). -/
def gaussianHonestIntervals (n : ℕ) (σ : ℝ) : Set (IntervalProc n) :=
  {I | ∀ Q, GaussianIdClass σ Q → (9/10 : ℝ) ≤
    (gaussianExperiment Q σ n).real (Causalean.Stat.coverageEvent I.lo I.hi (gaussianTarget Q))}
/-- Extended minimax risk on the larger class, before its finite value is converted to real. Given [the displayed inputs and assumptions](hyp:n,σ), [this definition specifies the stated object](goal). -/
def gaussianRisk (n : ℕ) (σ : ℝ) : ℝ :=
  (Causalean.Stat.minimaxValueENNReal
    (fun (T : Estimator n) (Q : {Q // GaussianIdClass σ Q}) =>
      ∫⁻ z, ENNReal.ofReal |T.val z - gaussianTarget Q.val| ∂gaussianExperiment Q.val σ n)).toReal
/-- Minimax honest expected length on the larger class. Given [the displayed inputs and assumptions](hyp:n,σ), [this definition specifies the stated object](goal). -/
def gaussianLength (n : ℕ) (σ : ℝ) : ℝ :=
  (Causalean.Stat.minimaxValueENNReal
    (fun (I : {I // I ∈ gaussianHonestIntervals n σ}) (Q : {Q // GaussianIdClass σ Q}) =>
      ∫⁻ z, ENNReal.ofReal (Causalean.Stat.intervalLength (I.val.lo z) (I.val.hi z))
        ∂gaussianExperiment Q.val σ n)).toReal
/-- Pei and Shen Assumption 1Y, jointly nondifferential measurement error. Given [the displayed inputs and assumptions](hyp:σ,Q), [this definition specifies the stated object](goal). -/
def PeiShen1Y (σ : ℝ) (Q : GaussianLawData) : Prop :=
  IndepFun (fun ω => σ * errorCoord ω) (fun ω => (score ω, bit (outcome ω))) Q.Q
/-- Pei and Shen Assumption 2C, positive score density on a cutoff neighborhood. Given [the displayed inputs and assumptions](hyp:Q), [this definition specifies the stated object](goal). -/
def PeiShen2C (Q : GaussianLawData) : Prop :=
  ∃ r > 0, ∀ x ∈ Ioo (-r) r, 0 < Q.a x
/-- Pei and Shen Assumption 7, centered Gaussian measurement error. Given [the displayed inputs and assumptions](hyp:σ,Q), [this definition specifies the stated object](goal). -/
def PeiShen7 (σ : ℝ) (Q : GaussianLawData) : Prop :=
  Q.Q.map (fun ω => σ * errorCoord ω) = gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩

end CausalSmith.Stat.RdTruesideNoiseFrontier
