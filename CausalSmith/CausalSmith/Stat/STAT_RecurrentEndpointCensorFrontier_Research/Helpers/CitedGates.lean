module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Cited scope and threshold gates

The first two declarations are closed bibliographic records of published
assumption and delivery scopes. The remaining declarations record cited
Kaplan–Meier and Pareto-tail threshold claims as logical comparison interfaces.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Rytgaard and van der Laan (2024), arXiv:2404.01736v4, Assumption 1
and the recurrent-event asymptotic-normality result. -/
-- @node: lem:rytgaard-horizon-positivity-scope
def rytgaardHorizonPositivityScope : _root_.String :=
  "In the longitudinal recurrent-event model of Rytgaard and van der Laan, \
   Assumption 1 requires nuisance parameters (Λy, Λd, Λc, π) to have cadlag \
   parametrizations with finite sectional variation norm. At the chosen horizon \
   τ > 0, K_c(τ | F_{τ-}) is the product over 0 < t < τ of \
   (1 - Λc(dt | F_{t-})); some η > 0 satisfies K_c(τ | F_{τ-}) π(a | L) > η \
   for both a = 0, 1, P-almost every joint realization of baseline L and \
   predictable history. Their recurrent-event asymptotic-linearity and \
   Gaussian-inference conclusion is stated within this entire Assumption 1 \
   scope. Source: arXiv:2404.01736v4, Assumption 1 and the recurrent-event \
   asymptotic-normality result."

/-- Baer, Bui, Mork, Strawderman, and Ertefaie (2025), arXiv:2306.16571v3,
Supplement S2 Assumption 6 and Theorem 5. -/
-- @node: lem:baer-horizon-positivity-scope
def baerHorizonPositivityScope : _root_.String :=
  "In the recurrent-event analysis of Baer, Bui, Mork, Strawderman, and \
   Ertefaie, Supplement S2 Assumption 6 requires some ε > 0 with \
   ε < π₀(a; l) K*(τ; a, l) almost surely for every supported treatment and \
   covariate value (a, l). Theorem 5 is stated for the true observed-data law \
   in the authors' n-sample estimation model and assumes cross-fit nuisance \
   estimators θ̂_n. For all sufficiently large n, it further requires some \
   ε' > 0 and C'_F < ∞ such that, almost surely, for both a = 0, 1, \
   ε' < π_n(a; l) K_n(τ; a, l) and F_n(u, t; a, L) ≤ C'_F H_n(u; a, L) \
   for every u, t > 0. The cited cross-fitted expansion is stated within this \
   Theorem 5 scope. Source: arXiv:2306.16571v3, Supplement S2 Assumption 6 \
   and Theorem 5."

noncomputable def akritasObserve (z : ℝ × ℝ) : ℝ × Bool :=
  (min z.1 z.2, decide (z.1 ≤ z.2))

noncomputable def akritasObservedLaw (F G : Measure ℝ) : Measure (ℝ × Bool) :=
  (F.prod G).map akritasObserve

noncomputable def akritasSampleLaw (F G : Measure ℝ) (n : ℕ) :
    Measure (Fin n → ℝ × Bool) :=
  Measure.pi (fun _ : Fin n => akritasObservedLaw F G)

noncomputable def akritasRisk {n : ℕ} (s : Fin n → ℝ × Bool) (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => t ≤ (s i).1)).card

noncomputable def akritasDeathJump {n : ℕ} (s : Fin n → ℝ × Bool)
    (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => (s i).1 = t ∧ (s i).2)).card

noncomputable def akritasKMLeft {n : ℕ} (s : Fin n → ℝ × Bool)
    (t : ℝ) : ℝ :=
  ∏ u ∈ (Finset.univ.image (fun i : Fin n => (s i).1)).filter (fun u => u < t),
    (1 - (if akritasRisk s u = 0 then 0 else
      (akritasDeathJump s u : ℝ) / akritasRisk s u))

noncomputable def akritasKMIntegral (φ : ℝ → ℝ) {n : ℕ}
    (s : Fin n → ℝ × Bool) : ℝ :=
  ∑ i : Fin n, if (s i).2 then
    φ (s i).1 * akritasKMLeft s (s i).1 /
      (if akritasRisk s (s i).1 = 0 then 1 else akritasRisk s (s i).1)
    else 0

noncomputable def akritasRetention (G : Measure ℝ) (t : ℝ) : ℝ :=
  G.real {u | t ≤ u}

noncomputable def akritasEndpoint (F G : Measure ℝ) : EReal :=
  sSup (((fun t : ℝ => (t : EReal)) ''
    ((F.prod G).map (fun z : ℝ × ℝ => min z.1 z.2)).support))

def akritasIntegrationDomain (F G : Measure ℝ) : Set ℝ :=
  {t | (t : EReal) ≤ akritasEndpoint F G}

noncomputable def akritasSampleEndpoint {n : ℕ} (s : Fin n → ℝ × Bool) : ℝ :=
  sSup (Set.range (fun i : Fin n => (s i).1))

noncomputable def akritasLifetimeEndpoint (F : Measure ℝ) : EReal :=
  sSup ((fun t : ℝ => (t : EReal)) '' F.support)

noncomputable def akritasPhiTilde (F : Measure ℝ) (φ : ℝ → ℝ)
    (τ : EReal) (s : ℝ) : ℝ :=
  F.real {t | s ≤ t} *
    (φ s - (∫ t in {t : ℝ | s < t ∧ (t : EReal) ≤ τ}, φ t ∂F) /
      F.real {t | s < t})

noncomputable def akritasObservedRetention (F G : Measure ℝ) (s : ℝ) : ℝ :=
  (akritasObservedLaw F G).real {o | s ≤ o.1}

noncomputable def akritasInfluence (F G : Measure ℝ) (φ : ℝ → ℝ)
    (o : ℝ × Bool) : ℝ :=
  let τ := akritasEndpoint F G
  (if o.2 then
    akritasPhiTilde F φ τ o.1 / akritasObservedRetention F G o.1 else 0) -
  ∫ s in Set.Iic o.1,
    akritasPhiTilde F φ τ s /
      (akritasObservedRetention F G s * F.real {t | s ≤ t}) ∂F

/-- Michael G. Akritas (2000), "The central limit theorem under censoring",
Bernoulli 6(6), Assumption 1 and Theorems 5–6, pp. 1110–1114,
DOI 10.2307/3318473. The cited result gives a root-n centered Gaussian
Kaplan–Meier integral and an iid asymptotic representation with the same
variance under the weighted square-integrability and endpoint conditions. -/
-- @node: lem:akritas-km-integral-threshold
def AkritasKMIntegralThreshold : Sort 0 :=
  ∀ (F G : Measure ℝ) (φ : ℝ → ℝ),
    F Set.univ = 1 → G Set.univ = 1 → Measurable φ →
    (∫⁻ t in akritasIntegrationDomain F G,
      ENNReal.ofReal (φ t ^ 2) /
        ENNReal.ofReal (akritasRetention G t) ∂F) < ⊤ →
    ((∀ n : ℕ, 0 < n → akritasSampleLaw F G n
      {s | (akritasSampleEndpoint s : EReal) < akritasLifetimeEndpoint F} = 1) ∨
      (∃ τF : ℝ, akritasLifetimeEndpoint F = (τF : EReal) ∧ φ τF = 0)) →
    ∃ σ2 : ℝ,
      0 ≤ σ2 ∧
      (∫ o, akritasInfluence F G φ o ∂akritasObservedLaw F G) = 0 ∧
      (∫ o, (akritasInfluence F G φ o) ^ 2 ∂akritasObservedLaw F G) = σ2 ∧
      ConvergesInLaw (fun n : ℕ =>
        (akritasSampleLaw F G n).map (fun s =>
          Real.sqrt n * (akritasKMIntegral φ s -
            ∫ t in akritasIntegrationDomain F G, φ t ∂F)))
        (gaussianReal 0 (Real.toNNReal σ2)) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => (akritasSampleLaw F G n).real
          {s | ε < |Real.sqrt n * (akritasKMIntegral φ s -
            ∫ t in akritasIntegrationDomain F G, φ t ∂F) -
            1 / Real.sqrt n *
              (∑ i : Fin n, akritasInfluence F G φ (s i))|}) atTop (nhds 0))

noncomputable def beirlantUpperOrder {n : ℕ} (s : Fin n → ℝ × Bool)
    (j : ℕ) : ℝ :=
  sInf {t : ℝ | (Finset.univ.filter (fun i => t < (s i).1)).card < j}

noncomputable def beirlantRisk {n : ℕ} (s : Fin n → ℝ × Bool)
    (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => t ≤ (s i).1)).card

noncomputable def beirlantKM {n : ℕ} (s : Fin n → ℝ × Bool) (t : ℝ) : ℝ :=
  ∏ i ∈ (Finset.univ.filter (fun i : Fin n => (s i).1 ≤ t ∧ (s i).2)),
    (1 - (beirlantRisk s (s i).1 : ℝ)⁻¹)

noncomputable def beirlantBoxCox (η x : ℝ) : ℝ :=
  if η = 0 then Real.log x else (1 - x ^ (-η)) / η

noncomputable def beirlantT (η : ℝ) (k : ℕ) {n : ℕ}
    (s : Fin n → ℝ × Bool) : ℝ :=
  ∑ j ∈ Finset.Icc 2 k,
    beirlantKM s (beirlantUpperOrder s j) /
      beirlantKM s (beirlantUpperOrder s (k + 1)) *
        (beirlantBoxCox η (beirlantUpperOrder s j /
          beirlantUpperOrder s (k + 1)) -
         beirlantBoxCox η (beirlantUpperOrder s (j + 1) /
          beirlantUpperOrder s (k + 1)))

def HallTail (F : Measure ℝ) (γ β C : ℝ) (D : ℝ) : Prop :=
  0 < γ ∧ 0 < β ∧ 0 < C ∧
    ∃ r : ℝ → ℝ, Tendsto r atTop (nhds 0) ∧
      ∀ᶠ x : ℝ in atTop,
        F.real {t | x < t} =
          C * x ^ (-1 / γ) * (1 + D * x ^ (-β) * (1 + r x))

inductive HistoricalStatus where
  | unknown
  | conjecturedSlowerNormalRate (exponent : ℝ)
  | outsideRemark

inductive Regime where
  | unweightedDistribution
  | weightedDistribution
  | unweightedRate

/-- Remark 3 reports historical knowledge, not an asserted limit law. -/
noncomputable def beirlantRemark3Status (p pη : ℝ) : Regime → HistoricalStatus
  | .unweightedDistribution =>
      if p ≤ 1 / 2 then .unknown else .outsideRemark
  | .weightedDistribution =>
      if pη ≤ 1 / 2 then .unknown else .outsideRemark
  | .unweightedRate =>
      if p < 1 / 2 then .conjecturedSlowerNormalRate (-p) else .outsideRemark

/-- Jan Beirlant, Julien Worms, and Rym Worms (2019), arXiv:1804.06583v1,
Estimator (10), Theorem 1, Corollary 1, and Remarks 1 and 3, pp. 3–5. The weighted tail-index
statistic has a square-root-k Gaussian limit when p_η > 1/2; setting η = 0
recovers the unweighted p > 1/2 threshold. The polynomial n-versus-k
condition when the bias limit is zero is explicit. Remark 3's low-threshold
determination and conjecture are recorded as a historical report. -/
-- @node: lem:beirlant-censored-tail-threshold
def BeirlantCensoredTailThreshold : Sort 0 :=
  ∀ (F G : Measure ℝ) (γ1 γ2 β1 β2 C1 C2 D1 D2 η lamLimit : ℝ)
    (k : ℕ → ℕ),
    F Set.univ = 1 → G Set.univ = 1 →
    F (Set.Iio 0) = 0 → G (Set.Iio 0) = 0 →
    (∀ x : ℝ, F {x} = 0) → (∀ x : ℝ, G {x} = 0) →
    HallTail F γ1 β1 C1 D1 → HallTail G γ2 β2 C2 D2 →
    let γ := (γ1⁻¹ + γ2⁻¹)⁻¹
    let p := γ / γ1
    let pη := p + γ * η
    let βstar := min β1 β2
    let mbias := if β1 ≤ β2 then
      -(γ ^ 2 * β1 * D1 * (C1 * C2) ^ (-γ * β1) /
        (pη * (pη + γ * β1))) else 0
    (((-1 / γ1 < η ∧ 1 / 2 < pη ∧
      Tendsto k atTop atTop ∧
      Tendsto (fun n => (k n : ℝ) / n) atTop (nhds 0) ∧
      Tendsto (fun n => Real.sqrt (k n) *
        ((k n : ℝ) / n) ^ (γ * βstar)) atTop (nhds lamLimit) ∧
      (lamLimit = 0 → ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
        ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ C * (k n : ℝ) ^ B)) →
      (ConvergesInLaw (fun n =>
        (Measure.pi (fun _ : Fin n => akritasObservedLaw F G)).map
          (fun s => Real.sqrt (k n) *
            (beirlantT η (k n) s - γ1 / (1 + γ1 * η))))
        (gaussianReal (lamLimit * mbias)
          (Real.toNNReal (γ ^ 2 / pη ^ 2 * p / (2 * pη - 1)))) ∧
      ConvergesInLaw (fun n =>
        (Measure.pi (fun _ : Fin n => akritasObservedLaw F G)).map
          (fun s => Real.sqrt (k n) *
            (beirlantT η (k n) s / (1 - η * beirlantT η (k n) s) - γ1)))
        (gaussianReal (lamLimit * mbias * (1 + η * γ1) ^ 2)
          (Real.toNNReal (γ ^ 2 / pη ^ 2 * p /
            (2 * pη - 1) * (1 + η * γ1) ^ 4))))) ∧
    (p ≤ 1 / 2 →
      beirlantRemark3Status p pη .unweightedDistribution = .unknown) ∧
    (pη ≤ 1 / 2 →
      beirlantRemark3Status p pη .weightedDistribution = .unknown) ∧
    (p < 1 / 2 →
      beirlantRemark3Status p pη .unweightedRate =
        .conjecturedSlowerNormalRate (-p) ∧ -p > -(1 / 2 : ℝ)))


end CausalSmith.Stat.RecurrentEndpointCensorFrontier
