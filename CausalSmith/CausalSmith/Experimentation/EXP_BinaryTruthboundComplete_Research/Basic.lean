import Causalean.Experimentation.DesignBased.DesignCore
import Causalean.Panel.PO.Mobius
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Binary observable-margin variance bounds

Shared finite-design objects for the binary truth-table characterization, optimization programs,
and comparison classes.  The schedule is fixed and all randomness comes from `FiniteDesign`.
-/

open scoped BigOperators ENNReal
open Finset Set Filter Topology

namespace CausalSmith.Experimentation.BinaryTruthbound

open Causalean.Experimentation.DesignBased

/-- A finite binary potential-outcome experiment with positive support probabilities. -/
structure Setup where
  K : ℕ -- @realizes K(coordinate count in ℕ₀)
  Omega : Type -- @realizes Z(finite assignment support); @realizes z(assignment atom carrier)
  fintypeOmega : Fintype Omega
  design : @FiniteDesign Omega fintypeOmega -- @realizes p(probability vector on Z)
  support_pos : ∀ z, 0 < design.p z -- @realizes p(strict positivity on support)
  O : Omega → Finset (Fin K) -- @realizes O_z(observed subset of I)
  v : Omega → Fin K → ℝ -- @realizes v_z(score vector in ℝ^K)

attribute [instance] Setup.fintypeOmega

-- @env: S1
-- @realizes I(Fin K); @realizes \Theta(binary schedules on I); @realizes \theta(fixed schedule)
/-- For [an experiment](hyp:E), [the schedule space](goal) is the collection of binary potential-outcome schedules. -/
abbrev Theta (E : Setup) := Fin E.K → Fin 2

-- @env: S2
-- @realizes S(finite coordinate subset); @realizes T(Moebius inversion subset)
/-- For [an experiment](hyp:E), [a coordinate set](goal) is a finite subset of its score coordinates. -/
abbrev CoordinateSet (E : Setup) := Finset (Fin E.K)

-- @realizes i(coordinate index in I); @realizes k(second coordinate index in I)
/-- For [an experiment](hyp:E), [a coordinate](goal) is one of its score coordinates. -/
abbrev Coordinate (E : Setup) := Fin E.K

/-- Design compatibility: every nonzero score coordinate is observed. -/
-- @node: ass:observable-score
def ObservableScore (E : Setup) : Prop :=
  ∀ z i, E.v z i ≠ 0 → i ∈ E.O z

/-- The coordinate subsets jointly observed under some assignment. -/
-- @node: def:observable-complex
def observableComplex (E : Setup) : Finset (Finset (Fin E.K)) :=
  Finset.univ.powerset.filter fun S => ∃ z, S ⊆ E.O z
  -- @realizes \mathcal J(subsets S contained in some O_z)

/-- The squarefree Boolean monomial indexed by `S`. -/
def monomial (E : Setup) (S : Finset (Fin E.K)) : Theta E → ℝ := fun θ =>
  ∏ i ∈ S, ((θ i : ℕ) : ℝ)
  -- @realizes m_S(product of binary coordinates)

/-- Observable Boolean functions of degree at most `r`; `r = ⊤` is the unrestricted span. -/
-- @node: def:boolean-mobius-spaces
noncomputable def observableSpan (E : Setup) (r : WithTop ℕ) : Submodule ℝ (Theta E → ℝ) :=
  Submodule.span ℝ {u | ∃ S, S ∈ observableComplex E ∧ (S.card : WithTop ℕ) ≤ r ∧ u = monomial E S}
  -- @realizes r(degree limit); @realizes \mathcal E_{\mathcal J,r}(degree-restricted span); @realizes \mathcal E_{\mathcal J}(take r=top)

/-- The realized linear assignment score. -/
def score (E : Setup) (z : E.Omega) (θ : Theta E) : ℝ :=
  ∑ i, E.v z i * ((θ i : ℕ) : ℝ)
  -- @realizes X_z(v_z dot theta)

/-- Coefficients of the design-mean target. -/
def targetCoeff (E : Setup) (i : Fin E.K) : ℝ :=
  E.design.E fun z => E.v z i
  -- @realizes c(sum_z p_z v_z)

/-- The fixed-schedule causal contrast targeted by the score. -/
def targetTau (E : Setup) (θ : Theta E) : ℝ :=
  ∑ i, targetCoeff E i * ((θ i : ℕ) : ℝ)
  -- @realizes \tau(c dot theta)

/-- Coefficient matrix of the randomization variance. -/
def varianceMatrix (E : Setup) (i k : Fin E.K) : ℝ :=
  E.design.E (fun z => E.v z i * E.v z k) - targetCoeff E i * targetCoeff E k
  -- @realizes A(sum_z p_z v_z v_z^T - c c^T)

/-- Matrix-form packaging of `varianceMatrix`. -/
def varianceMatrixAsMatrix (E : Setup) : Matrix (Fin E.K) (Fin E.K) ℝ :=
  fun i k => varianceMatrix E i k

/-- The true randomization variance as a Boolean quadratic function. -/
def trueVarianceFn (E : Setup) (θ : Theta E) : ℝ :=
  ∑ i, ∑ k, varianceMatrix E i k * ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ)
  -- @realizes f(theta^T A theta = Var_p X_z(theta))

/-- The complete linear-score construction required by the paper: realized scores, their design
mean coefficient and target, the covariance matrix, and its quadratic variance function. -/
structure ScoreVarianceData (E : Setup) where
  X : E.Omega → Theta E → ℝ
  c : Fin E.K → ℝ
  tau : Theta E → ℝ
  A : Matrix (Fin E.K) (Fin E.K) ℝ
  f : Theta E → ℝ

/-- Package all five parts of the score/target/variance construction, under design compatibility. -/
-- @node: def:score-variance
def designVarianceFn (E : Setup) (_hobs : ObservableScore E) : ScoreVarianceData E where
  X := score E
  c := targetCoeff E
  tau := targetTau E
  A := varianceMatrixAsMatrix E
  f := trueVarianceFn E

/-- For [an experiment and a fixed binary schedule](hyp:E,θ), [the quadratic variance function equals the randomization variance of its realized score](goal). -/
lemma designVarianceFn_eq_Var (E : Setup) (θ : Theta E) :
    trueVarianceFn E θ = E.design.Var (fun z => score E z θ) := by
  have hscore : (fun z => score E z θ) =
      (fun z => ∑ i ∈ Finset.univ, ((θ i : ℕ) : ℝ) * E.v z i) := by
    funext z
    simp only [score]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hscore]
  rw [E.design.Var_linear_comb Finset.univ
    (fun i => ((θ i : ℕ) : ℝ)) (fun i z => E.v z i)]
  unfold trueVarianceFn varianceMatrix targetCoeff
  simp only [FiniteDesign.Cov_eq]
  congr 1
  funext i
  congr 1
  funext k
  ring

/-- The restriction of a full schedule to the coordinates observed by assignment `z`. -/
def restrict (E : Setup) (z : E.Omega) (θ : Theta E) : E.O z → Fin 2 := fun i => θ i.1

/-- Assignment-specific observed-data truth tables. -/
abbrev AssignmentRule (E : Setup) := (z : E.Omega) → (E.O z → Fin 2) → ℝ
  -- @realizes g_z(truth table on observed coordinates)

/-- Design expectation of an assignment-specific observed-data rule. -/
-- @node: def:expected-rule
def expectedRule (E : Setup) (g : AssignmentRule E) : Theta E → ℝ := fun θ =>
  E.design.E fun z => g z (restrict E z θ)
  -- @realizes b_g(sum_z p_z g_z(theta restricted to O_z))

/-- Full-support schedule weights used only to select an objective. -/
def FullSupportWeight (E : Setup) (q : Theta E → ℝ) : Prop :=
  (∀ θ, 0 < q θ) ∧ ∑ θ, q θ = 1
  -- @realizes q(full-support simplex on Theta)

/-- The paper's objective domain, the interior of the finite schedule simplex. -/
abbrev FullSupportObjective (E : Setup) := {q : Theta E → ℝ // FullSupportWeight E q}

/-- Degree-restricted observable functions that dominate the true variance pointwise. -/
def conservativeCone (E : Setup) (r : WithTop ℕ) : Set (Theta E → ℝ) :=
  {b | b ∈ observableSpan E r ∧ ∀ θ, trueVarianceFn E θ ≤ b θ}
  -- @realizes b(primal candidate in the degree-restricted conservative cone)

/-- The unrestricted observable conservative cone denoted `C_J(f)` in the paper. -/
def unrestrictedConservativeCone (E : Setup) : Set (Theta E → ℝ) :=
  conservativeCone E ⊤
  -- @realizes \mathcal C_{\mathcal J}(f)(unrestricted observable b dominating f)

/-- The infimal schedule-weighted value of the degree-restricted conservative program. -/
-- @node: def:bound-program
noncomputable def optValue (E : Setup) (q : FullSupportObjective E) (r : WithTop ℕ) : ℝ :=
  sInf ((fun b => ∑ θ, q.1 θ * b θ) '' conservativeCone E r)
  -- @realizes F_{\mathcal J,r}(restricted optimum); @realizes F_{\mathcal J}(take r=top)

/-- Nonnegative schedule weights matching every observable Boolean moment of `q`. -/
def dualMarginSet (E : Setup) (q : FullSupportObjective E) : Set (Theta E → ℝ) :=
  {μ | (∀ θ, 0 ≤ μ θ) ∧
    ∀ S ∈ observableComplex E,
      ∑ θ, μ θ * monomial E S θ = ∑ θ, q.1 θ * monomial E S θ}
  -- @realizes \mu(nonnegative schedule weights); @realizes \mathcal D_{\mathcal J}(q)(observable-moment matching)

/-- Pointwise Pareto admissibility within the unrestricted conservative cone. -/
def ParetoAdmissible (E : Setup) (b : Theta E → ℝ) : Prop :=
  b ∈ unrestrictedConservativeCone E ∧
    ¬ ∃ b', b' ∈ unrestrictedConservativeCone E ∧
      (∀ θ, b' θ ≤ b θ) ∧ ∃ θ, b' θ < b θ
  -- @realizes b'(pointwise domination comparator)

/-- The paper's dual moment polytope together with its Pareto-admissibility predicate. -/
structure DualAndAdmissibilityData (E : Setup) where
  dual : Set (Theta E → ℝ)
  paretoAdmissible : (Theta E → ℝ) → Prop

/-- Package the dual and Pareto notions on their declared full-support objective domain. -/
-- @node: def:dual-and-admissibility
def dualMarginPolytope (E : Setup) (q : FullSupportObjective E) :
    DualAndAdmissibilityData E where
  dual := dualMarginSet E q
  paretoAdmissible := ParetoAdmissible E

/-- Complementation of every binary coordinate. -/
def complement (E : Setup) (θ : Theta E) : Theta E := fun i => ⟨1 - (θ i : ℕ), by omega⟩
  -- @realizes \mathbf 1_K(all-one schedule and theta-complement)

/-- Row sums of the variance matrix vanish, equivalently `A 1 = 0`. -/
-- @node: ass:complement-invariant-variance
def ComplementInvariantVariance (E : Setup) : Prop :=
  ∀ i, ∑ k, varianceMatrix E i k = 0

/-- The objective gives complementary schedules equal weight. -/
-- @node: ass:complement-invariant-objective
def ComplementInvariantObjective (E : Setup) (q : Theta E → ℝ) : Prop :=
  ∀ θ, q θ = q (complement E θ)

/-- The Boolean restriction of a homogeneous quadratic form. -/
def hQuad (E : Setup) (H : Matrix (Fin E.K) (Fin E.K) ℝ) : Theta E → ℝ := fun θ =>
  ∑ i, ∑ k, H i k * ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ)
  -- @realizes H(symmetric quadratic-bound matrix); @realizes h_H(theta^T H theta)

-- @env: S3
-- The program, dual, Pareto order, and published comparators are introduced above.

end CausalSmith.Experimentation.BinaryTruthbound
