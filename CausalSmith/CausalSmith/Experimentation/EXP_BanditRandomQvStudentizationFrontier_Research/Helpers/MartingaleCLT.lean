/- Cited martingale-CLT boundaries and the paper's early-measurable mixture lemma. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Basic
import Causalean.Mathlib.Probability.StdNormalCDF
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Martingale central-limit interfaces -/

open Filter MeasureTheory ProbabilityTheory Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

/-- Genuine finite-row martingale differences: probability normalization,
adaptedness, integrability, and conditional centering are all explicit. -/
def martingaleDifference {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Filtration ℕ ‹MeasurableSpace Ω›) (N : ℕ) (X : ℕ → Ω → ℝ) : Prop :=
  μ Set.univ = 1 ∧ ∀ i, 1 ≤ i → i ≤ N →
    Measurable[G i] (X i) ∧ Integrable (X i) μ ∧ μ[X i | G (i - 1)] =ᵐ[μ] 0

def scalarVariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (X : ℕ → Ω → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, ∫ ω, (X i ω) ^ 2 ∂μ

def normalizedPredictableVariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : Filtration ℕ ‹MeasurableSpace Ω›)
    (n : ℕ) (X : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => (scalarVariance μ n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n,
    μ[(fun ω' => (X i ω') ^ 2) | G (i - 1)] ω

def martingaleKolmogorovDistance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (X : ℕ → Ω → ℝ) : ℝ :=
  sSup {r | ∃ z, r = |(μ {ω | (scalarVariance μ n X).sqrt⁻¹ *
    (∑ i ∈ Finset.Icc 1 n, X i ω) ≤ z}).toReal - Causalean.Mathlib.stdNormalCDF z|}

/-- Jean-Christophe Mourrat (2013), *On the Rate of Convergence in the
Martingale Central Limit Theorem*, Theorem 1.5, inequality (1.6),
arXiv:1103.5050. -/
-- @node: lem:mourrat-bounded-martingale-clt
def MourratBoundedMartingaleCLT : Sort 0 :=
  ∀ (p γ : ℝ), 1 ≤ p → 0 < γ → ∃ C > 0,
  ∀ (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω)
    (G : Filtration ℕ m0) (n : ℕ) (X : ℕ → Ω → ℝ),
    2 ≤ n → martingaleDifference μ G n X →
    (∀ i, 1 ≤ i → i ≤ n → ∀ᵐ ω ∂μ, |X i ω| ≤ γ) →
    let s2 := scalarVariance μ n X
    let V2 := normalizedPredictableVariance μ G n X
    martingaleKolmogorovDistance μ n X ≤ C *
      ((n : ℝ) * Real.log n / s2.sqrt ^ 3 +
        ((∫ ω, |V2 ω - 1| ^ p ∂μ) + s2 ^ (-p)).rpow (1 / (2 * p + 1)))

/-- Aldous and Eagleson (1978), *On Mixing and Stability of Limit Theorems*,
Annals of Probability 6(2), abstract and martingale application pp. 329--331,
DOI 10.1214/aop/1176995577.  This carrier records an actual stable martingale
limit assertion rather than an automatically inhabited metadata shell. -/
-- @node: lem:aldous-eagleson-stable-martingale-apparatus
def AldousEaglesonStableMartingaleApparatus : Sort 0 :=
  ∀ (Ω : Type) (m0 : MeasurableSpace Ω)
    (μ : ℕ → Measure Ω) (G : ℕ → Filtration ℕ m0)
    (N : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ),
    (∀ n, martingaleDifference (μ n) (G n) (N n) (X n)) →
    Tendsto N atTop atTop →
    (∀ ε > 0, Tendsto (fun n => (μ n {ω |
      ε < |normalizedPredictableVariance (μ n) (G n) (N n) (X n) ω - 1|}).toReal)
      atTop (nhds 0)) →
    CDFConverges μ
      (fun n ω => (scalarVariance (μ n) (N n) (X n)).sqrt⁻¹ *
        ∑ i ∈ Finset.Icc 1 (N n), X n i ω)
      Causalean.Mathlib.stdNormalCDF

-- @node: lem:early-measurable-martingale-mixture
lemma early_measurable_martingale_mixture
    (hMourrat : MourratBoundedMartingaleCLT)
    {Ω I : Type*} [MeasurableSpace Ω]
    (μ : ℕ → I → Measure Ω) (G : ℕ → I → Filtration ℕ ‹MeasurableSpace Ω›)
    (X : ℕ → I → ℕ → Ω → ℝ) (k : ℕ → ℕ) (lambda : ℕ → I → Ω → ℝ)
    (L vmin vmax : ℝ)
    (hcut : ∀ T, 0 < T → k T < T)
    (hmd : ∀ T i, martingaleDifference (μ T i) (G T i) T (X T i))
    (hbounded : ∀ T i t, 1 ≤ t → t ≤ T → ∀ᵐ ω ∂μ T i, |X T i t ω| ≤ L)
    (hscale : ∀ T i, Measurable[G T i (k T)] (lambda T i))
    (hscaleBounds : ∀ T i, ∀ᵐ ω ∂μ T i,
      vmin ≤ lambda T i ω ∧ lambda T i ω ≤ vmax)
    (hvmin : 0 < vmin)
    (hdelta : ∀ ε > 0, ∀ᶠ T in atTop, ∀ i, (∫ ω, |(T : ℝ)⁻¹ *
      (∑ t ∈ Finset.Icc (k T + 1) T,
        (μ T i)[(fun ω' => (X T i t ω') ^ 2) | G T i (t - 1)] ω) -
          lambda T i ω| ∂μ T i) ≤ ε) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∀ i z,
      |(μ T i {ω | (T : ℝ)⁻¹.sqrt *
        (∑ t ∈ Finset.Icc (k T + 1) T, X T i t ω) ≤ z}).toReal -
        ∫ ω, Causalean.Mathlib.stdNormalCDF
          (z / Real.sqrt (lambda T i ω)) ∂μ T i| ≤ ε := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV
