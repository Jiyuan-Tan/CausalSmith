module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.LegendreFacts
public import Causalean.Mathlib.Probability.HermiteFacts

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


/-- The exact cited Legendre interface follows from the neutral Mathlib/Causalean proof. Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
-- @node: lem:classical-legendre-facts
theorem classicalLegendreFacts : ClassicalLegendreFacts :=
  classicalLegendreFacts_of_mathlib

/-- The exact cited Hermite interface follows from the reusable neutral substrate. Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
theorem classicalHermiteFacts : ClassicalHermiteFacts :=
  Causalean.Mathlib.Probability.classicalHermiteFacts

/-- Pei--Shen's score, real observed outcome, and measurement error; no binary or
potential-mean-continuity restriction is built into this cited theorem's domain. -/
abbrev PeiShenLatent := ℝ × ℝ × ℝ
/-- Source convention: treatment is assigned below the cutoff, Section 2, display (1). Given [the displayed inputs and assumptions](hyp:Q), [this definition specifies the stated object](goal). -/
def peiShenObservedLaw (Q : Measure PeiShenLatent) : Measure (ℝ × Bool × ℝ) :=
  Q.map (fun z => (z.1 + z.2.2, decide (z.1 < 0), z.2.1))
/-- The continuous-score sharp-RD domain: a score density and a genuine local observed
regression with finite left and right limits. These are the meanings of the conditional
means and limit contrast in Section 2, not continuity assumptions on potential outcomes. Given [the displayed inputs and assumptions](hyp:Q,a,m,left,right), [this definition specifies the stated object](goal). -/
def PeiShenSharpRDDomain (Q : Measure PeiShenLatent) (a m : ℝ → ℝ)
    (left right : ℝ) : Prop :=
  IsProbabilityMeasure Q ∧ AEMeasurable a volume ∧ (∀ x, 0 ≤ a x) ∧
  Q.map (fun z => z.1) = volume.withDensity (fun x => ENNReal.ofReal (a x)) ∧
  (∃ r > 0, Causalean.PO.IsRegressionFunction (Q.restrict {z | z.1 ∈ Ioo (-r) r})
    (fun z => z.1) (fun z => z.2.1) m) ∧
  Tendsto m (nhdsWithin 0 (Iio 0)) (nhds left) ∧
  Tendsto m (nhdsWithin 0 (Ioi 0)) (nhds right)
/-- Assumption 1Y on the full real-outcome cited domain. Given [the displayed inputs and assumptions](hyp:Q), [this definition specifies the stated object](goal). -/
def PeiShenObserved1Y (Q : Measure PeiShenLatent) : Prop :=
  IndepFun (fun z => z.2.2) (fun z => (z.1, z.2.1)) Q
/-- Assumption 2C requires positivity throughout an open cutoff neighborhood. Given [the displayed inputs and assumptions](hyp:a), [this definition specifies the stated object](goal). -/
def PeiShenObserved2C (a : ℝ → ℝ) : Prop :=
  ∃ r > 0, ∀ x ∈ Ioo (-r) r, 0 < a x
/-- Assumption 7 specifies the actual centered Gaussian measurement error. Given [the displayed inputs and assumptions](hyp:Q,σ), [this definition specifies the stated object](goal). -/
def PeiShenObserved7 (Q : Measure PeiShenLatent) (σ : ℝ) : Prop :=
  Q.map (fun z => z.2.2) = gaussianReal 0 ⟨σ^2, sq_nonneg σ⟩
/-- Pei and Shen (2017), cite:peishen2017, Section 2 and Section 4.1,
Assumptions 1Y, 2C, 7 and Proposition 4(b), printed pp.4,18,28--29;
https://arxiv.org/pdf/1609.01396. Identification of the real-outcome continuous-score
sharp RD contrast, the left observed-regression limit minus the right limit under
source display (1). The domain is not restricted to the benchmark's binary potentials
or locally continuous potential-mean versions. Given the displayed inputs, [this definition specifies the stated object](goal). -/
-- @node: lem:pei-shen-identification-hypotheses
def PeiShenIdentificationHypotheses : Sort 0 :=
  ∀ (Q₁ Q₂ : Measure PeiShenLatent) (a₁ a₂ m₁ m₂ : ℝ → ℝ)
    (left₁ right₁ left₂ right₂ σ₁ σ₂ : ℝ), 0 < σ₁ → 0 < σ₂ →
    PeiShenSharpRDDomain Q₁ a₁ m₁ left₁ right₁ →
    PeiShenSharpRDDomain Q₂ a₂ m₂ left₂ right₂ →
    PeiShenObserved1Y Q₁ → PeiShenObserved2C a₁ → PeiShenObserved7 Q₁ σ₁ →
    PeiShenObserved1Y Q₂ → PeiShenObserved2C a₂ → PeiShenObserved7 Q₂ σ₂ →
    peiShenObservedLaw Q₁ = peiShenObservedLaw Q₂ → left₁ - right₁ = left₂ - right₂
/-- Dong (2018), cite:dong2018-identification, Chapter 2 Section 2.2,
Assumptions 8--9, printed p.49;
https://etheses.lse.ac.uk/3756/1/Dong__essays-in-microeconometrics.pdf.
Frozen bibliographic metadata, with zero logical consumers.
Attested literal source:
Assumption 8. f_{R*}(0) > 0 and E[Y_d|R* = r] is continuous at r = 0 for d = 0, 1.
Assumption 9. R* and ε are continuous, and ε ⊥⊥ (Y, R*). Given the displayed inputs, [this definition specifies the stated object](goal). -/
-- @node: lem:dong-identification-hypotheses
def dongIdentificationHypothesesRecord : _root_.String := "Dong (2018, PhD thesis, LSE), Chapter 2, Section 2.2, printed p. 49. Assumption 8: f_{R*}(0) > 0 and E[Y_d | R* = r] is continuous at r = 0 for d = 0, 1. Assumption 9: R* and epsilon are continuous (continuous random variables, not necessarily continuous densities), and epsilon is independent of (Y, R*). These are identification-level conditions. Assumption 8 credits Hahn, Todd and Van der Klaauw (2001) A1-2; Assumption 9 is Dong's own measurement-error summary."
/-- Dong (2018), cite:dong2018-inference, Chapter 2 Section 2.4, Assumptions 11,13
and Theorem 6, printed pp.59,61, PDF pages 69,71;
https://researchonline.lse.ac.uk/id/eprint/134713/1/Dong_essays-in-microeconometrics.pdf.
Pointwise Gaussian specialization of the actual observed-treatment local-linear estimator
(2.3.3), with the source's defining averages and leading Lyapunov summand.
This is a logical cited claim, with no consumers in this paper. Given the displayed inputs, [this definition specifies the stated object](goal). -/
-- @node: lem:dong-supersmooth-inference-comparison
def DongSupersmoothInferenceComparison : Sort 0 :=
  ∀ (P : Measure DongLatent) (f : ℝ → ℝ) (mu : Bool → ℝ → ℝ)
    (K : ℝ → ℝ) (σ b : ℝ),
    DongVersions P f mu → DongA8 f mu → DongA9Gaussian P σ → DongA11 P f mu K →
    DongA13Gaussian P f mu K σ b → 2 < b → DongGaussianAsymptoticNormality P mu K σ b
/-- Zhang and Karunamuni (2009), cite:zhangkarunamuni2009,
DOI 10.1016/j.jspi.2008.10.021; publisher abstract, Section 1 introduction and estimator (1.3),
Section 4 opening and Section 5 excerpt; https://www.sciencedirect.com/science/article/abs/pii/S0378375808004175.
Frozen bibliographic metadata, with zero logical consumers. Given the displayed inputs, [this definition specifies the stated object](goal). -/
-- @node: lem:zhang-karunamuni-accessible-scope
def zhangKarunamuniAccessibleScopeRecord : _root_.String := "Zhang and Karunamuni (2009), Journal of Statistical Planning and Inference 139, 2269--2283, DOI 10.1016/j.jspi.2008.10.021. Verified accessible scope (publisher abstract; Section 1 introduction and derivative-estimator display (1.3); Section 4 opening; Section 5 excerpt): boundary estimation of a density or its derivatives from the additive model Y = X + epsilon with epsilon independent of X and known error law F_epsilon, for ordinary-smooth and supersmooth errors, analysed by asymptotic mean squared error. These are statistical density targets under a squared-error criterion, not the present causal contrast and honest interval-length criterion. The full statements of Theorems 4.1--4.2 are inaccessible in the inspected material. No exact theorem-rate, class-dominance, or supersmooth endpoint priority claim is attributed to this comparison."

end CausalSmith.Stat.RdTruesideNoiseFrontier
