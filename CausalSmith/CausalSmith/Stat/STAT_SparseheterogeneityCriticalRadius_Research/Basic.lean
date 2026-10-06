module
public import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Basic

/-! The finite-cell known-radius observational experiment.  The Causalean PO and
estimation systems describe a different, measure-theoretic carrier; this file
specializes the accepted finite-cell real-law development instead. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open scoped BigOperators ENNReal


-- @env: S1
variable (n : ℕ) (M rho : ℝ)
  -- @realizes n(sample size and cell count)
  -- @realizes M(outcome scale; range via KnownRadiusClass.M_ge_one)
  -- @realizes rho_n(known radius)

abbrev Law (n : ℕ) := -- @realizes p_k(inherited RealLaw.cellMass)
  DiscreteAteHeterogeneityFrontier.RealLaw n
  -- @realizes P(full-data law) @realizes n(sample size and cell count)
abbrev SampleObs (n : ℕ) :=
  DiscreteAteHeterogeneityFrontier.Obs n
  -- @realizes O(observed record) @realizes O_i(sample record)
  -- @realizes X(Fin n observed cell) @realizes A(Bool observed treatment)

noncomputable abbrev benchmarkLog (n : ℕ) : ℝ :=
  DiscreteAteHeterogeneityFrontier.logEN n
  -- @realizes L_n(log(e n))

noncomputable abbrev ateTarget {n : ℕ} (P : Law n) : ℝ :=
  DiscreteAteHeterogeneityFrontier.rawAteFormula P
  -- @realizes tau(P)(sum of cell-mass-weighted effects)

-- @node: ass:iid-sampling
def IidSampling (n : ℕ) (P : Law n)
    (Q : Measure (Fin n → SampleObs n)) : Prop :=
  Q = DiscreteAteHeterogeneityFrontier.productLaw n P
  -- @realizes Q_P^{(n)}(observed iid product law)

-- @node: ass:consistency
def Consistency {n : ℕ} (P : Law n) : Prop := DiscreteAteHeterogeneityFrontier.Consistency P

-- @node: ass:exchangeability
def ConditionalExchangeability {n : ℕ} (P : Law n) : Prop :=
  ∀ arm : Bool, ∀ k : Fin n, ∀ a : Bool, ∀ s : Set ℝ, MeasurableSet s →
    P.fullLaw {z | z.x = k ∧ z.a = a ∧
      (if arm then z.y1 else z.y0) ∈ s} * P.fullLaw {z | z.x = k} =
    P.fullLaw {z | z.x = k ∧ z.a = a} *
      P.fullLaw {z | z.x = k ∧ (if arm then z.y1 else z.y0) ∈ s}
  -- @realizes Y(a)(separate conditional independence for each arm)

-- @node: ass:fixed-overlap
def FixedOverlap {n : ℕ} (P : Law n) : Prop := DiscreteAteHeterogeneityFrontier.Overlap (1 / 4) P
  -- @realizes pi_k(occupied-cell range [1/4,3/4])

-- @node: ass:mean-envelope
def MeanEnvelope {n : ℕ} (M : ℝ) (P : Law n) : Prop :=
  DiscreteAteHeterogeneityFrontier.MeanNormalization M P
  -- @realizes mu_{ak}(mean envelope)

-- @node: ass:variance-envelope
def VarianceEnvelope {n : ℕ} (M : ℝ) (P : Law n) : Prop :=
  DiscreteAteHeterogeneityFrontier.SecondCentralMoment M P
  -- @realizes V_{ak}(bounded central variance)

-- @node: ass:critical-radius
def KnownRadius (M rho : ℝ) {n : ℕ} (P : Law n) : Prop :=
  (0 ≤ rho ∧ rho ≤ 2) ∧ DiscreteAteHeterogeneityFrontier.ApproximateHomogeneity M rho P
  -- @realizes rho_n(supplied radius in [0,2]) @realizes tau_k(cell-effect deviation)

-- @node: def:critical-class
structure KnownRadiusClass (n : ℕ) (M rho : ℝ) where
  law : Law n -- @realizes P(class law) @realizes mathcal P_n(M,rho_n)(known-radius class)
  n_ge_three : 3 ≤ n -- @realizes n(standing range n >= 3)
  M_ge_one : 1 ≤ M -- @realizes M(range [1,infinity) for every class law)
  consistency : Consistency law
  exchangeability : ConditionalExchangeability law
  overlap : FixedOverlap law
  mean_envelope : MeanEnvelope M law
  variance_envelope : VarianceEnvelope M law
  radius : KnownRadius M rho law -- @realizes rho_n(radius restriction)

noncomputable def criticalRadius (n : ℕ) : ℝ :=
  benchmarkLog n / Real.sqrt n -- @realizes sigma_n(L_n/sqrt n)

abbrev CriticalClass (n : ℕ) (M : ℝ) := KnownRadiusClass n M (criticalRadius n)
  -- @realizes mathcal P_n(M)(critical class specialization)

lemma separate_exchangeability_of_joint {n : ℕ} (P : Law n)
    (h : DiscreteAteHeterogeneityFrontier.ConditionalExchangeability P) :
    ConditionalExchangeability P := by
  intro arm k a s hs
  cases arm
  · simpa using
      h k a s Set.univ hs MeasurableSet.univ
  · simpa using
      h k a Set.univ s MeasurableSet.univ hs

def KnownRadiusClass.ofModelClass {n : ℕ} {M rho : ℝ}
    (hn : 3 ≤ n)
    (P : DiscreteAteHeterogeneityFrontier.ModelClass n (1 / 4) M rho) :
    KnownRadiusClass n M rho :=
  { law := P.law
    n_ge_three := hn
    M_ge_one := P.M_ge_one
    consistency := P.consistency
    exchangeability := separate_exchangeability_of_joint P.law P.exchangeability
    overlap := P.overlap
    mean_envelope := P.mean_normalization
    variance_envelope := P.second_moment
    radius := ⟨⟨P.sigma_nonneg, P.sigma_le_two⟩, P.homogeneity⟩ }

@[simp] lemma KnownRadiusClass.ofModelClass_law {n : ℕ} {M rho : ℝ}
    (hn : 3 ≤ n)
    (P : DiscreteAteHeterogeneityFrontier.ModelClass n (1 / 4) M rho) :
    (KnownRadiusClass.ofModelClass hn P).law = P.law := rfl

noncomputable def worstRisk (n : ℕ) (M rho : ℝ)
    (est : (Fin n → SampleObs n) → ℝ) : ℝ :=
  ⨆ P : KnownRadiusClass n M rho, DiscreteAteHeterogeneityFrontier.mse P.law est

noncomputable def knownRadiusMinimaxRisk (n : ℕ) (M rho : ℝ) : ℝ :=
  ⨅ est : DiscreteAteHeterogeneityFrontier.Estimator n n M, worstRisk n M rho est.1
  -- @realizes \mathsf R_n(M,\rho_n)(infimum of worst-case MSE)

noncomputable def Hrho (n : ℕ) (rho : ℝ) : ℝ :=
  Real.log (Real.exp 1 + (n : ℝ) * rho ^ 2)
  -- @realizes H_n(rho_n)(effective radius logarithm)

noncomputable def rate (n : ℕ) (rho : ℝ) : ℝ :=
  1 / (n : ℝ) + rho ^ 2 / (Hrho n rho) ^ 2
  -- @realizes r_n(rho_n)(known-radius rate)

noncomputable def Hcrit (n : ℕ) : ℝ :=
  Real.log (Real.exp 1 + benchmarkLog n ^ 2)
  -- @realizes H_n(critical effective logarithm)

noncomputable def rateCrit (n : ℕ) : ℝ :=
  1 / (n : ℝ) + benchmarkLog n ^ 2 / ((n : ℝ) * (Hcrit n) ^ 2)
  -- @realizes r_n(critical minimax rate)

-- keep: named critical-radius specialization of the paper's minimax risk functional
noncomputable def criticalClassRisk (n : ℕ) (M : ℝ) : ℝ :=
  knownRadiusMinimaxRisk n M (criticalRadius n)
  -- @realizes \mathsf R_n(M)(critical minimax risk)

-- keep: paper notation for the general-radius converse separation scale
noncomputable def separationScale (n : ℕ) (M rho : ℝ) : ℝ :=
  M * rho / Hrho n rho
  -- @realizes Delta_n(rho_n)(known-radius target separation)

-- keep: named critical-radius specialization used to state the paper's separation scale
noncomputable def criticalSeparationScale (n : ℕ) (M : ℝ) : ℝ :=
  M * criticalRadius n / Hcrit n
  -- @realizes Delta_n(critical target separation)

def clipM (M z : ℝ) : ℝ := max (-M) (min M z)
  -- @realizes operatorname{clip}_M(clipping to [-M,M])

-- @node: def:zeng-anchor-class
structure ZengAnchorClass (n : ℕ) (rho : ℝ) where
  law : Law n -- @realizes mathcal Z_n(rho_n)(binary anchor class)
  n_ge_three : 3 ≤ n -- @realizes n(standing range n >= 3)
  rho_range : 0 ≤ rho ∧ rho ≤ 2
  consistency : Consistency law
  exchangeability : ConditionalExchangeability law
  overlap : FixedOverlap law
  binary_potential : law.fullLaw {z | z.y0 ∉ ({0, 1} : Set ℝ) ∨
    z.y1 ∉ ({0, 1} : Set ℝ)} = 0
  binary_outcome : ∀ a k, 0 < law.cellMass k →
    law.outcomeLaw a k (({0, 1} : Set ℝ)ᶜ) = 0
  radius : DiscreteAteHeterogeneityFrontier.ApproximateHomogeneity 1 rho law

noncomputable def anchorMinimaxRisk (n : ℕ) (rho : ℝ) : ℝ :=
  ⨅ est : DiscreteAteHeterogeneityFrontier.Estimator n n 1,
    ⨆ P : ZengAnchorClass n rho, DiscreteAteHeterogeneityFrontier.mse P.law est.1

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
