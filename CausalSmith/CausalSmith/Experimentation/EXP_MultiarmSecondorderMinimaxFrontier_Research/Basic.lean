import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.OrbitLikelihood
import Causalean.Mathlib.Optimization.RationalLP
import Causalean.Experimentation.DesignBased.Product
import Causalean.Stat.Minimax.MinimaxValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Core objects for the unrestricted labeled game, its response-type orbit game,
the contrast-weighted first-order procedure, and the rational grid LP.

The LP feasibility predicate intentionally has no sign row and no upper bound
for its epigraph coordinate.  Nonnegativity and attainment are theorem-level
consequences handled by the rational LP bridge.
-/

open scoped BigOperators
open Finset Set Filter

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

variable {K n : ℕ} (c : Contrast ℝ K)

-- @node: def:labeled-schedule-game
/-- Unrestricted design-and-estimator minimax risk over complete labeled schedules. -/
noncomputable def rhoN (K n : ℕ) (c : Contrast ℝ K) : ℝ :=
  Causalean.Stat.minimaxValue (fun (p : Procedure K n c) (z : Schedule K n) =>
    labeledRisk c p z)
-- @realizes \rho_n(c)(inf_{D,τ̂} max_z R_n(D,τ̂;z))

/-- Second-order improvement for the paper's own minimax risk (not an arbitrary sequence). -/
noncomputable def dN (K : ℕ) (c : Contrast ℝ K) (n : ℕ) : ℝ :=
  C0 c / n - rhoN K n c
-- @realizes d_n(c)(C_0(c)/n-ρ_n(c))

/-- The cluster-owned minimax-envelope property pinning the improvement to `[0,∞)`. -/
def MinimaxEnvelopeBound (K : ℕ) (c : Contrast ℝ K) : Prop :=
  ∀ n, rhoN K n c ≤ C0 c / n
-- @realizes d_n(c)(nonnegative range via ρ_n(c)≤C_0(c)/n)

/-- Orbit risk of a mixture/invariant-estimator pair. -/
noncomputable def orbitRisk (q : OrbitProcedure K n c) (m : CountVec K n) : ℝ :=
  ∑ r, q.1.p r * ∑ x : ObsVec r,
    (orbitLik m r x : ℝ) * ((q.2 r x : ℝ) - tauCount c m) ^ 2

-- @node: def:finite-orbit-game
/-- Minimax value of the finite response-type orbit experiment. -/
noncomputable def orbitGameValue (K n : ℕ) (c : Contrast ℝ K) : ℝ :=
  Causalean.Stat.minimaxValue (fun (q : OrbitProcedure K n c) (m : CountVec K n) =>
    orbitRisk c q m)
-- @realizes G_n(c)(inf_{π,δ} max_m ∑_r π_r ∑_x P_m(x|r)(δ-τ_c(m))²)

/-- [the contrast norm is positive](goal). -/
lemma Lc_pos (c : Contrast ℝ K) : 0 < Lc c := by
  have hnonneg : 0 ≤ Lc c := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hne : Lc c ≠ 0 := by
    intro hsum
    apply c.nonzero
    funext a
    apply abs_eq_zero.mp
    exact congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg (fun a => abs_nonneg (c a))).mp hsum) a
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- [the q star is nonnegative](goal). -/
lemma qStar_nonneg (c : Contrast ℝ K) (a : Arm K) : 0 ≤ qStar c a := by
  exact div_nonneg (abs_nonneg _) (le_of_lt (Lc_pos c))

/-- [the q star sums](goal). -/
lemma qStar_sum (c : Contrast ℝ K) : ∑ a, qStar c a = 1 := by
  simp only [qStar]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (Lc_pos c))

/-- One-unit contrast-weighted categorical design. -/
noncomputable def qStarDesign (c : Contrast ℝ K) :
    Causalean.Experimentation.DesignBased.FiniteDesign (Arm K) where
  p := qStar c
  p_nonneg := qStar_nonneg c
  p_sum := qStar_sum c

/-- The unprojected centered inverse-allocation contrast score. -/
noncomputable def centeredContrastScore (c : Contrast ℝ K) (A : Assign K n)
    (y : ObservedOutcome n) : ℝ :=
  ((n : ℝ)⁻¹) * ∑ i,
    if _h : qStar c (A i) = 0 then 0
    else c (A i) * ((if y i then 1 else 0) - 1 / 2) / qStar c (A i)

-- @node: def:first-order-procedure
/-- Independent contrast-weighted allocation and the clipped centered score rule. -/
noncomputable def contrastWeightedProcedure (K n : ℕ) (c : Contrast ℝ K) :
    Procedure K n c :=
  (Causalean.Experimentation.DesignBased.prodDesign (fun _ : Unit n => qStarDesign c),
    fun A y => ⟨clip c (centeredContrastScore c A y), clip_mem c _⟩)
-- @realizes \widehat\tau_{\mathrm{cHT}}^\star(projected contrast-weighted centered HT rule)

variable (M : ℕ) (cq : RatContrast K)

/-- Exact rational grid-program feasibility.  In particular, there is no `u ≥ 0`
row and no false `u ≤ h_c²` feasibility clause. -/
def GridLPFeasible (K n M : ℕ) (c : RatContrast K)
    (pi : GridPi K n) (w : RationalGridWeight K n M) (u : ℚ) : Prop :=
  (∑ r, pi r = 1) ∧
  (∀ r x, ∑ g, w r x g = pi r) ∧
  (∀ r, 0 ≤ pi r) ∧
  RationalGridWeightNonnegative M w ∧
  (∀ m : CountVec K n,
    ∑ r, ∑ x, ∑ g,
      orbitLik m r x * w r x g * (gammaMC M c g - tauCountRat c m) ^ 2 ≤ u)
-- @realizes u(epigraph upper-risk variable; nonnegative is derived from risk rows)

/-- The raw grid-program value is the infimum feasible epigraph coordinate, with no positivity assumptions imposed at the definition stage. -/
noncomputable def gridLPValueRaw (K n M : ℕ) (c : RatContrast K) : ℝ :=
  sInf {v : ℝ | ∃ (pi : GridPi K n) (w : RationalGridWeight K n M) (u : ℚ),
    GridLPFeasible K n M c pi w u ∧ v = (u : ℝ)}

-- @node: def:rational-contrast-grid-lp
/-- Real infimum of the exact rational feasible objective values on `n, M ≥ 1`. -/
noncomputable def gridLPValue (K n M : ℕ) (c : RatContrast K)
    (_hn : 0 < n) (_hM : 0 < M) : ℝ := gridLPValueRaw K n M c
-- @realizes \Lambda_{n,M}(c)(minimum epigraph value of the rational contrast grid LP)

/-- The diagnostic three-arm contrast `(1,-1/2,-1/2)`. -/
def cDaggerQ : RatContrast 3 where
  coeff := fun i => Fin.cases 1 (Fin.cases (-1 / 2) (fun _ => -1 / 2)) i
  nonzero := by
    intro h
    have h0 := congrFun h (0 : Fin 3)
    norm_num at h0
  sum_zero := by
    simp [Fin.sum_univ_succ]
-- @realizes c^\dagger((1,-1/2,-1/2))

/-- The witness contrast is the centered and normalized three-arm contrast used for the certified separation. -/
noncomputable def cDagger : Contrast ℝ 3 := ratContrastToReal cDaggerQ

-- @node: def:k3-rational-lp
/-- Three-arm specialization of the rational contrast grid value. -/
noncomputable def gridLPValueK3 (n M : ℕ) (hM : 0 < M) : ℝ :=
  gridLPValueRaw 3 n M cDaggerQ
-- @realizes \Lambda_{n,M}^\dagger(Λ_{n,M}(c†))

/-- Three-arm unrestricted minimax risk. -/
noncomputable def rhoNDagger (n : ℕ) : ℝ := rhoN 3 n cDagger
-- @realizes \rho_n^\dagger(ρ_n(c†))

/-- Two-arm contrast `(1,-1)`. -/
def twoArmContrastQ : RatContrast 2 where
  coeff := fun i => Fin.cases 1 (fun _ => -1) i
  nonzero := by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    norm_num at h0
  sum_zero := by simp [Fin.sum_univ_succ]

/-- The canonical two-arm contrast assigns coefficients one and minus one to the two treatment arms. -/
noncomputable def twoArmContrast : Contrast ℝ 2 := ratContrastToReal twoArmContrastQ

/-- The unrestricted two-arm value. -/
noncomputable def rho2 (n : ℕ) : ℝ := rhoN 2 n twoArmContrast

/-- Airy-rate scaling used only by the cited comparison gates. -/
noncomputable def secondOrderScale (n : ℕ) : ℝ := (n : ℝ) ^ (4 / 3 : ℝ)

/-- Witness that the conditional second-order branch exists. -/
structure PositiveLimitBranch (a : PositiveSequence) (K : ℕ) (c : Contrast ℝ K) where
  limit : ℝ -- @realizes C_{\mathrm{so}}(c)(positive convergent limit)
  positive : 0 < limit
  converges : Tendsto (fun n => a n * dN K c n) atTop (nhds limit)

/-- Carrier for the paper's positive Airy constant. -/
def AiryConstant := {C : ℝ // 0 < C}
-- @realizes C_A(carrier (0,∞))

/-- Identification of the Airy constant through a normalized Airy ground state. -/
def IsAiryGroundStateConstant (C : AiryConstant) : Prop :=
  ∃ (Ai dAi : ℝ → ℝ) (aPrime : ℝ),
    (∀ x, HasDerivAt Ai (dAi x) x) ∧
    (∀ x, HasDerivAt dAi (x * Ai x) x) ∧
    Tendsto Ai atTop (nhds 0) ∧ Ai 0 > 0 ∧ aPrime < 0 ∧ dAi aPrime = 0 ∧
    (∀ b, b < 0 → dAi b = 0 → b ≤ aPrime) ∧
    C.1 = -(4 : ℝ) ^ (1 / 3 : ℝ) * aPrime

/-- The numerical bracket is benchmark information, separate from the symbol's space. -/
def IsPublishedAiryConstant (C : AiryConstant) : Prop :=
  IsAiryGroundStateConstant C ∧ 1.617 < C.1 ∧ C.1 < 1.618

/-- State space of the published scalar two-arm experiment. -/
def ScalarTriple (n : ℕ) :=
  {θ : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) //
    (θ.1 : ℕ) + (θ.2.1 : ℕ) + (θ.2.2 : ℕ) = n}

/-- The scalar triple collection has a finite enumeration. -/
instance (n : ℕ) : Fintype (ScalarTriple n) := by unfold ScalarTriple; infer_instance

/-- Scalar experiment risk is the mean squared estimation error under the fair Bernoulli score experiment. -/
noncomputable def scalarExperimentRisk (n : ℕ) (f : Fin (n + 1) → ℝ)
    (θ : ScalarTriple n) : ℝ :=
  ∑ k : Fin ((θ.1.2.2 : ℕ) + 1),
    ((Nat.choose (θ.1.2.2 : ℕ) k : ℝ) / 2 ^ (θ.1.2.2 : ℕ)) *
      (f ⟨(θ.1.1 : ℕ) + (k : ℕ), by
        have ht := θ.property
        have hk : (k : ℕ) ≤ (θ.1.2.2 : ℕ) := Nat.le_of_lt_succ k.isLt
        omega⟩ -
        (((θ.1.1 : ℕ) : ℝ) - ((θ.1.2.1 : ℕ) : ℝ)) / n) ^ 2

/-- The scalar minimax value is the least worst-case scalar experiment risk over all clipped estimators. -/
noncomputable def scalarMinimaxValue (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ f : Fin (n + 1) → ℝ,
    v = ⨆ θ : ScalarTriple n, scalarExperimentRisk n f θ}

/--
Sudijono, Dobriban, and Tchetgen Tchetgen (2026), Theorems 2.1–2.2 and
3.1, arXiv:2608.13822.  This proposition records exactly the scalar reduction
and Airy expansion used as secondary context.
-/
-- @node: lem:published-two-arm-minimax-airy
def PublishedTwoArmMinimaxAiry : Sort 0 :=
  (∀ n, 0 < n → rho2 n = scalarMinimaxValue n) ∧
  ∃ C : AiryConstant, IsPublishedAiryConstant C ∧
    Tendsto (fun n => secondOrderScale n *
      (rho2 n - ((n : ℝ)⁻¹ - C.1 / secondOrderScale n))) atTop (nhds 0)

/-- A hull schedule assigns each unit and treatment arm a potential outcome in the unit interval. -/
abbrev HullSchedule (N : ℕ) (L U : ℝ) :=
  {Y : Fin N → Fin 2 → ℝ // ∀ i a, Y i a ∈ Icc L U}

/-- A hull estimator maps an assignment and its real-valued observed outcomes to a clipped contrast estimate. -/
abbrev HullEstimator (N : ℕ) := Assign 2 N → (Fin N → ℝ) → ℝ

/-- The source optimizes only over estimators measurable in their real data argument. -/
def IsMeasurableHullEstimator (est : HullEstimator N) : Prop :=
  ∀ A, Measurable (est A)

/-- The hull target is the population average of the contrast-weighted real potential outcomes. -/
noncomputable def hullTarget {N : ℕ} {L U : ℝ} (Y : HullSchedule N L U) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (Y.1 i 1 - Y.1 i 0)

/-- Hull risk is the design expectation of squared error for a hull decision at a fixed hull schedule. -/
noncomputable def hullRisk {N : ℕ} {L U : ℝ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 N))
    (est : HullEstimator N) (Y : HullSchedule N L U) : ℝ :=
  D.E fun A => (est A (fun i => Y.1 i (A i)) - hullTarget Y) ^ 2

/-- The hull minimax value is the least worst-case hull risk over all hull decisions. -/
noncomputable def hullMinimaxValue (N : ℕ) (L U : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 N))
      (est : HullEstimator N), IsMeasurableHullEstimator est ∧
        v = ⨆ Y : HullSchedule N L U, hullRisk D est Y}

/-- The hull observation kernel gives the probability of an observed assignment–outcome pair under a hull schedule and assignment design. -/
noncomputable def hullKernel (_N k m x : ℕ) : ℝ :=
  if k ≤ x then (Nat.choose m (x - k) : ℝ) / 2 ^ m else 0

/-- A hull decision combines a finite assignment design with a hull estimator. -/
abbrev HullDecision (N : ℕ) := Fin (N + 1) → Set.Icc (0 : ℝ) 2

/-- The finite maximum in Hull's displayed definition of `κ_N`. -/
noncomputable def hullObjective (N : ℕ) (d : HullDecision N) : ℝ :=
  ⨆ km : {q : ℕ × ℕ // q.1 + q.2 ≤ N},
    ∑ x : Fin (N + 1), hullKernel N km.1.1 km.1.2 x *
      ((d x : ℝ) - (2 * km.1.1 + km.1.2 : ℕ) / (N : ℝ)) ^ 2

/-- Hull's displayed finite min--max constant. -/
noncomputable def hullKappa (N : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ d : HullDecision N, v = hullObjective N d}

/-- The independent fair assignment mechanism used by Hull's attaining procedure. -/
noncomputable def hullIndependentDesign (N : ℕ) :
    Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 N) :=
  Causalean.Experimentation.DesignBased.prodDesign
    (fun _ : Unit N => qStarDesign twoArmContrast)

-- keep: the positive quantitative theorem is retained separately from the bibliographic scope node.
/-- The positive mathematical content of Hull's Theorem 1 at fixed `N`, `L`, and `U`. -/
def HullPublishedTheoremAt (N : ℕ) (L U : ℝ) : Prop :=
  hullMinimaxValue N L U = (U - L) ^ 2 * hullKappa N ∧
  (∃ dStar : HullDecision N, hullObjective N dStar = hullKappa N) ∧
  (∃ est : HullEstimator N,
    IsMeasurableHullEstimator est ∧
    (⨆ Y : HullSchedule N L U, hullRisk (hullIndependentDesign N) est Y) =
      hullMinimaxValue N L U)

/-- Bibliographic scope metadata for Hull (2026), Theorem 1. This non-Prop
payload records the source boundary without turning a literature-scope judgment
into a mathematical premise of this paper. -/
-- keep: bibliographic scope metadata, intentionally non-Prop.
-- @node: lem:published-hull-two-arm-bounded-scope
def PublishedHullTwoArmBoundedScope : _root_.List _root_.String :=
  ["Hull's unrestricted minimax theorem concerns a finite population with two treatment arms",
   "potential outcomes are bounded in a known interval",
   "optimization is over arbitrary assignment mechanisms and measurable estimators",
   "the source does not state a fixed-K-at-least-three bounded-outcome orbit-game theorem"]

/-- Balanced, treatment-label-blinded two-arm assignment designs. -/
def IsBalancedLabelBlinded {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n)) : Prop :=
  (∀ A, D.p A ≠ 0 → (Finset.univ.filter fun i => A i = 0).card = n / 2) ∧
  (∀ A, D.p A = D.p (fun i => if A i = 0 then 1 else 0))

/-- A procedure is inference-capped when every estimate lies in the natural closed interval determined by the contrast norm. -/
def IsInferenceCapped {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (cap : ℝ) : Prop := ∀ A, D.p A ≤ cap

/-- A two-arm potential-outcome schedule in Kallus's real conditional-mean model. -/
abbrev KallusSchedule (n : ℕ) := Fin n → Fin 2 → ℝ

/-- The sample-average treatment effect attached to a Kallus schedule. -/
noncomputable def kallusTarget {n : ℕ} (Y : KallusSchedule n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (Y i 1 - Y i 0)

/-- Kallus's fixed sample-average-treatment-effect estimator `2 n⁻¹ ⟨W,Yobs⟩`. -/
noncomputable def kallusSATEEstimator (n : ℕ) : HullEstimator n :=
  fun A y => 2 * (n : ℝ)⁻¹ * ∑ i, (if A i = 1 then 1 else -1) * y i

/-- A procedure is unbiased for the sample average treatment effect when its expected estimate equals the finite-population contrast target for every response schedule. -/
def IsUnbiasedSATE {n : ℕ} (est : HullEstimator n) : Prop :=
  ∀ (Y : KallusSchedule n)
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n)),
    IsBalancedLabelBlinded D →
    D.E (fun A => est A (fun i => Y i (A i))) = kallusTarget Y

/-- Kallus's worst-case design-dependent variance contribution over conditional means.
The extended-real codomain faithfully includes arbitrary unbounded specified classes. -/
noncomputable def kallusWorstRisk {n : ℕ} (M : Set (Fin n → ℝ))
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n)) : ENNReal :=
  ⨆ μ : M, ENNReal.ofReal
    (D.E fun A => (∑ i, (if A i = 1 then 1 else -1) * μ.1 i) ^ 2)

/-- Ordinary MSOD optimality in the balanced label-blinded design class. -/
def IsOrdinaryMSOD {n : ℕ} (M : Set (Fin n → ℝ))
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n)) : Prop :=
  IsBalancedLabelBlinded D ∧
  ∀ D', IsBalancedLabelBlinded D' → kallusWorstRisk M D ≤ kallusWorstRisk M D'

/-- Inference-constrained MSOD optimality among designs satisfying the probability cap. -/
def IsInferenceConstrainedMSOD {n : ℕ} (M : Set (Fin n → ℝ)) (cap : ℝ)
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n)) : Prop :=
  IsBalancedLabelBlinded D ∧ IsInferenceCapped D cap ∧
  ∀ D', IsBalancedLabelBlinded D' → IsInferenceCapped D' cap →
    kallusWorstRisk M D ≤ kallusWorstRisk M D'

/-- The source-specified conditional-mean class, fixed SATE rule, and feasible cap. -/
structure KallusMsodScope (n : ℕ) where
  conditionalMeanClass : Set (Fin n → ℝ)
  fixedUnbiasedEstimator : HullEstimator n
  fixed_estimator_spec : fixedUnbiasedEstimator = kallusSATEEstimator n
  estimator_unbiased : IsUnbiasedSATE fixedUnbiasedEstimator
  significanceLevel : ℝ
  significanceLevel_pos : 0 < significanceLevel
  significanceLevel_le_one : significanceLevel ≤ 1
  probabilityCap : ℝ
  probabilityCap_pos : 0 < probabilityCap
  probabilityCap_eq : probabilityCap = significanceLevel / 2
  capped_class_feasible : ∃ D :
      Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n),
    IsBalancedLabelBlinded D ∧ IsInferenceCapped D probabilityCap

/--
Kallus (2020), Sections 2 and 7, arXiv:2005.03151.  This records the two-arm,
even-population, balanced label-blinded ordinary MSOD and the separate capped
feasible-class MSOD for an arbitrary specified conditional-mean class,
fixed unbiased SATE estimator, and significance-linked cap `α / 2`.  The source
notes that ordinary MSOD may lack the uniformity
needed for Fisher randomization inference; no universal strict separation from
the capped class is asserted here.
-/
-- @node: lem:published-kallus-msod-inference-scope
def PublishedKallusMsodInferenceScope : Sort 0 :=
  (∀ n : ℕ, 0 < n → Even n →
    ∀ scope : KallusMsodScope n,
      ∃ Dordinary :
          Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n),
        IsOrdinaryMSOD scope.conditionalMeanClass Dordinary) ∧
  (∃ (n : ℕ) (_hn : 0 < n) (_heven : Even n)
      (scope : KallusMsodScope n)
      (Dordinary :
        Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n)),
      scope.conditionalMeanClass.Nonempty ∧
        IsOrdinaryMSOD scope.conditionalMeanClass Dordinary ∧
        ¬ IsInferenceCapped Dordinary scope.probabilityCap) ∧
  (∀ n : ℕ, 0 < n → Even n →
    ∀ scope : KallusMsodScope n,
      ∃ Dinference :
          Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n),
        IsInferenceConstrainedMSOD scope.conditionalMeanClass
          scope.probabilityCap Dinference)

/-- A sampling design assigns a probability to every subset of the finite population, with total mass one. -/
abbrev SamplingDesign (N : ℕ) :=
  Causalean.Experimentation.DesignBased.FiniteDesign (Finset (Fin N))

/-- An estimator sees only the values of sampled coordinates. -/
abbrev SamplingEstimator (N : ℕ) :=
  (S : Finset (Fin N)) → ({j : Fin N // j ∈ S} → ℝ) → ℝ

/-- Each sample-specific estimator component is measurable, as required by the source. -/
def IsSamplingEstimatorMeasurable {N : ℕ} (est : SamplingEstimator N) : Prop :=
  ∀ S, Measurable (est S)

/-- A unit’s inclusion probability is the total sampling-design mass of subsets containing that unit. -/
noncomputable def inclusionProbability {N : ℕ} (D : SamplingDesign N) (j : Fin N) : ℝ :=
  ∑ S with j ∈ S, D.p S

/-- Design unbiasedness on the source's bounded finite-population parameter box. -/
def IsDesignUnbiasedBoundedTotal {N : ℕ} (lower upper : Fin N → ℝ)
    (D : SamplingDesign N) (est : SamplingEstimator N) : Prop :=
  ∀ y : Fin N → ℝ, (∀ j, y j ∈ Icc (lower j) (upper j)) →
    D.E (fun S => est S (fun j => y j.1)) = ∑ j, y j

/-- Sampling worst-case risk is the largest mean squared estimation error over all bounded finite-population outcome vectors. -/
noncomputable def samplingWorstRisk {N : ℕ} (lower upper : Fin N → ℝ)
    (D : SamplingDesign N) (est : SamplingEstimator N) : ℝ :=
  ⨆ y : {y : Fin N → ℝ // ∀ j, y j ∈ Icc (lower j) (upper j)},
    D.E (fun S => (est S (fun j => y.1 j.1) - ∑ j, y.1 j) ^ 2)

/-- A sampling design is independent when every subset has the product probability generated by unit-specific inclusion probabilities. -/
def IsIndependentSampling {N : ℕ} (D : SamplingDesign N) (pi : Fin N → ℝ) : Prop :=
  ∀ S, D.p S = ∏ j, if j ∈ S then pi j else 1 - pi j

/-- The source's midpoint-differenced Horvitz--Thompson estimator. -/
noncomputable def midpointDifferencedHT {N : ℕ} (lower upper : Fin N → ℝ)
    (D : SamplingDesign N) : SamplingEstimator N :=
  fun S y =>
    (∑ j, (lower j + upper j) / 2) +
      ∑ j : {j : Fin N // j ∈ S},
        (y j - (lower j.1 + upper j.1) / 2) / inclusionProbability D j.1

/--
Aronow and Lopatto (2026), Theorems 1–3, arXiv:2605.20572.  This is the cited
unit-inclusion, design-unbiased bounded-total statement, not a multi-arm result.
-/
-- @node: lem:published-aronow-lopatto-bounded-unbiased
def PublishedAronowLopattoBoundedUnbiased : Sort 0 :=
  ∀ (N : ℕ) (lower upper : Fin N → ℝ) (D : SamplingDesign N),
    (∀ j, lower j ≤ upper j) →
    (∀ j, 0 < inclusionProbability D j ∧ inclusionProbability D j ≤ 1) →
    (∀ est : SamplingEstimator N,
      IsDesignUnbiasedBoundedTotal lower upper D est →
      ∀ ε : ℝ, 0 < ε →
      ∃ y : {y : Fin N → ℝ // ∀ j, y j ∈ Icc (lower j) (upper j)},
        (∑ j, ((upper j - lower j) / 2) ^ 2 *
          (1 - inclusionProbability D j) / inclusionProbability D j) - ε ≤
            D.E (fun S =>
              (est S (fun j => y.1 j.1) - ∑ j, y.1 j) ^ 2)) ∧
    IsSamplingEstimatorMeasurable (midpointDifferencedHT lower upper D) ∧
    IsDesignUnbiasedBoundedTotal lower upper D
      (midpointDifferencedHT lower upper D) ∧
    ((samplingWorstRisk lower upper D (midpointDifferencedHT lower upper D) =
        ∑ j, ((upper j - lower j) / 2) ^ 2 *
          (1 - inclusionProbability D j) / inclusionProbability D j) ↔
      ∀ i j, i ≠ j → 0 < upper i - lower i → 0 < upper j - lower j →
        D.Pr (fun S => i ∈ S ∧ j ∈ S) =
          inclusionProbability D i * inclusionProbability D j) ∧
    ((∀ j, 0 < upper j - lower j) →
      ∀ b : ℝ, 0 < b → b ≤ N →
      ∃ (γ : ℝ) (Dstar : SamplingDesign N)
        (estar : SamplingEstimator N),
        0 < γ ∧
        (∀ j, inclusionProbability Dstar j =
          min 1 (γ * ((upper j - lower j) / 2))) ∧
        ∑ j, inclusionProbability Dstar j = b ∧
        IsIndependentSampling Dstar (inclusionProbability Dstar) ∧
        estar = midpointDifferencedHT lower upper Dstar ∧
        IsSamplingEstimatorMeasurable estar ∧
        IsDesignUnbiasedBoundedTotal lower upper Dstar estar ∧
        (∀ (D' : SamplingDesign N)
          (e' : SamplingEstimator N),
          (∀ j, 0 < inclusionProbability D' j) →
          (∑ j, inclusionProbability D' j) ≤ b →
          IsDesignUnbiasedBoundedTotal lower upper D' e' →
          ∀ ε : ℝ, 0 < ε →
          ∃ y : {y : Fin N → ℝ // ∀ j, y j ∈ Icc (lower j) (upper j)},
            samplingWorstRisk lower upper Dstar estar - ε ≤
              D'.E (fun S =>
                (e' S (fun j => y.1 j.1) - ∑ j, y.1 j) ^ 2)))

/-- Scalar prior Bayes risk is the least prior-averaged scalar squared-error risk over all estimators. -/
noncomputable def scalarPriorBayesRisk (n : ℕ)
    (prior : Causalean.Experimentation.DesignBased.FiniteDesign (ScalarTriple n)) : ℝ :=
  sInf {v : ℝ | ∃ f : Fin (n + 1) → ℝ,
    v = ∑ θ, prior.p θ * scalarExperimentRisk n f θ}

/-- A scalar procedure is balanced Bernoulli when the design is the fair product design and the estimator depends only on the observed score count. -/
def IsBalancedBernoulliScalarProcedure (n : ℕ) (f : Fin (n + 1) → ℝ)
    (p : Procedure 2 n twoArmContrast) : Prop :=
  p.1 = Causalean.Experimentation.DesignBased.prodDesign
    (fun _ : Unit n => qStarDesign twoArmContrast) ∧
  ∀ (A : Assign 2 n) (y : ObservedOutcome n), (p.2 A y : ℝ) = f ⟨(Finset.univ.filter fun i =>
    if A i = 0 then y i else !(y i)).card,
    Nat.lt_succ_iff.mpr (by
      simpa using Finset.card_le_card
        (Finset.filter_subset (fun i => if A i = 0 then y i else !(y i)) Finset.univ))⟩

/-- Decision-theoretic admissibility: no procedure weakly dominates everywhere and strictly somewhere. -/
def IsAdmissibleTwoArmProcedure {n : ℕ} (p : Procedure 2 n twoArmContrast) : Prop :=
  ¬ ∃ q : Procedure 2 n twoArmContrast,
    (∀ z, labeledRisk twoArmContrast q z ≤ labeledRisk twoArmContrast p z) ∧
    (∃ z, labeledRisk twoArmContrast q z < labeledRisk twoArmContrast p z)

/-- A prior is least favorable for the scalar experiment when it maximizes scalar Bayes risk. -/
def IsLeastFavorableScalarPrior {n : ℕ}
    (prior : Causalean.Experimentation.DesignBased.FiniteDesign (ScalarTriple n)) : Prop :=
  ∀ prior' : Causalean.Experimentation.DesignBased.FiniteDesign (ScalarTriple n),
    scalarPriorBayesRisk n prior' ≤ scalarPriorBayesRisk n prior

/-- Source-specific Airy shrinkage and squared-ground-state data. -/
structure PublishedAiryAsymptoticData where
  hA : ℝ → ℝ
  phiA : ℝ → ℝ
  constant : AiryConstant
  constant_spec : IsPublishedAiryConstant constant
  phiA_smooth : ContDiff ℝ 2 phiA
  phiA_positive : ∀ t, 0 < phiA t
  phiA_even : ∀ t, phiA (-t) = phiA t
  phiA_normalized : ∫ t in Ioi (0 : ℝ), phiA t ^ 2 ∂MeasureTheory.volume = 1
  phiA_ground_state : ∀ t,
    -4 * deriv (deriv phiA) t + |t| * phiA t = constant.1 * phiA t
  hA_formula : ∀ t, hA t = -2 * deriv phiA t / phiA t

/-- The published nonlinear rule `X/n - n⁻²ᐟ³ h_A(X/n²ᐟ³)`. -/
noncomputable def publishedAiryUpperEstimator (data : PublishedAiryAsymptoticData)
    (n : ℕ) (X : ℝ) : ℝ :=
  X / n - (n : ℝ) ^ (-(2 / 3 : ℝ)) *
    data.hA (X / (n : ℝ) ^ (2 / 3 : ℝ))

/-- The explicit symmetric `φ_A²` weights from the published lower sequence. -/
noncomputable def publishedAiryPriorWeight (data : PublishedAiryAsymptoticData)
    (n : ℕ) (θ : ScalarTriple n) : ℝ :=
  if (θ.1.1 : ℕ) = 0 ∧ (θ.1.2.1 : ℕ) = 0 then data.phiA 0 ^ 2
  else if (θ.1.2.1 : ℕ) = 0 then
    (1 / 2 : ℝ) * data.phiA (((θ.1.1 : ℕ) : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ)) ^ 2
  else if (θ.1.1 : ℕ) = 0 then
    (1 / 2 : ℝ) * data.phiA (((θ.1.2.1 : ℕ) : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ)) ^ 2
  else 0

/-- A scalar prior is exactly the normalized published symmetric `φ_A²` prior. -/
def IsPublishedAiryPrior (data : PublishedAiryAsymptoticData) (n : ℕ)
    (prior : Causalean.Experimentation.DesignBased.FiniteDesign (ScalarTriple n)) : Prop :=
  ∀ θ, prior.p θ = publishedAiryPriorWeight data n θ /
    ∑ θ', publishedAiryPriorWeight data n θ'

/-- Bibliographic boundary: the cited scalar prior is not lifted by the source to
complete response schedules.  This metadata is deliberately separate from the
source's positive logical carrier below. -/
-- keep: public metadata preserving the frozen source boundary while the F5 logical carrier stays Prop-valued.
def publishedTwoArmScalarAttainmentScopeBoundary : List String :=
  ["the cited source supplies no lift of its scalar least-favorable prior to complete response schedules"]

/--
Sudijono, Dobriban, and Tchetgen Tchetgen (2026), Theorems 2.1–2.2, 3.1,
and C.1–C.2, arXiv:2608.13822.  The four positive clauses retained here are:
posterior-mean/least-favorable scalar attainment and Bayes-risk equality;
scalar/full-game equality with balanced attainment and admissibility; the
explicit `h_A` nonlinear-shrinkage upper sequence; and the explicit symmetric
`φ_A²` scalar-prior lower sequence.  The cited prior is on scalar effect-class
triples; no complete-schedule lift is asserted here.
-/
-- @node: lem:published-two-arm-scalar-attainment-scope
def PublishedTwoArmScalarAttainmentScope : Sort 0 :=
  publishedTwoArmScalarAttainmentScopeBoundary =
    ["the cited source supplies no lift of its scalar least-favorable prior to complete response schedules"] ∧
  (∀ n : ℕ, 0 < n →
    ∃ (f : Fin (n + 1) → ℝ)
      (prior : Causalean.Experimentation.DesignBased.FiniteDesign (ScalarTriple n))
      (bayesRisk : ℝ),
      (∀ x : Fin (n + 1), 0 <
          (∑ θ, prior.p θ *
            ∑ k ∈ Finset.range ((θ.1.2.2 : ℕ) + 1),
              if (x : ℕ) = (θ.1.1 : ℕ) + k then
                (Nat.choose (θ.1.2.2 : ℕ) k : ℝ) / 2 ^ (θ.1.2.2 : ℕ) else 0) →
        f x =
        (∑ θ, prior.p θ *
          (∑ k ∈ Finset.range ((θ.1.2.2 : ℕ) + 1),
            if (x : ℕ) = (θ.1.1 : ℕ) + k then
              ((Nat.choose (θ.1.2.2 : ℕ) k : ℝ) / 2 ^ (θ.1.2.2 : ℕ)) *
                ((((θ.1.1 : ℕ) : ℝ) - ((θ.1.2.1 : ℕ) : ℝ)) / n)
            else 0)) /
        (∑ θ, prior.p θ *
          ∑ k ∈ Finset.range ((θ.1.2.2 : ℕ) + 1),
            if (x : ℕ) = (θ.1.1 : ℕ) + k then
              (Nat.choose (θ.1.2.2 : ℕ) k : ℝ) / 2 ^ (θ.1.2.2 : ℕ) else 0)) ∧
      (∀ f', f' ≠ f → (⨆ θ, scalarExperimentRisk n f θ) <
        (⨆ θ, scalarExperimentRisk n f' θ)) ∧
      bayesRisk = scalarPriorBayesRisk n prior ∧
      bayesRisk = scalarMinimaxValue n ∧
      IsLeastFavorableScalarPrior prior ∧ rho2 n = scalarMinimaxValue n ∧
      (∃ fullProcedure : Procedure 2 n twoArmContrast,
        IsBalancedBernoulliScalarProcedure n f fullProcedure ∧
        Causalean.Stat.worstCaseRisk
          (fun (p : Procedure 2 n twoArmContrast) (z : Schedule 2 n) =>
            labeledRisk twoArmContrast p z) fullProcedure = rho2 n ∧
        IsAdmissibleTwoArmProcedure fullProcedure)) ∧
  (∃ (data : PublishedAiryAsymptoticData)
      (priorSequence : (m : ℕ) →
        Causalean.Experimentation.DesignBased.FiniteDesign (ScalarTriple m))
      (upperRemainder lowerRemainder : ℕ → ℝ),
    (∀ m, IsPublishedAiryPrior data m (priorSequence m)) ∧
    Tendsto (fun m => secondOrderScale m * upperRemainder m) atTop (nhds 0) ∧
    Tendsto (fun m => secondOrderScale m * lowerRemainder m) atTop (nhds 0) ∧
    (∀ m, (⨆ θ : ScalarTriple m,
        scalarExperimentRisk m
          (fun X₂ => publishedAiryUpperEstimator data m (2 * (X₂ : ℝ) - m)) θ) ≤
      (m : ℝ)⁻¹ - data.constant.1 / secondOrderScale m + upperRemainder m) ∧
    (∀ m : ℕ, (m : ℝ)⁻¹ - data.constant.1 / secondOrderScale m + lowerRemainder m ≤
      scalarPriorBayesRisk m (priorSequence m)))

/-- Descriptive, nonassertive payload for the unresolved active-face program. -/
structure BoundaryLayerHandle where
  startingObject : String
  faceEnumeration : String
  steinExpansion : String
  normalizerSelection : String
  limitProblem : String
  compatibilityConditions : String
  nonassertionDisclaimer : String

-- @node: def:boundary-layer-handle
/-- The active-face boundary-layer handle records the paper’s boundary-layer scaling quantities for a contrast and population size. -/
def activeFaceBoundaryLayerHandle : BoundaryLayerHandle :=
  { startingObject := "Start from the exact response-type orbit game."
    faceEnumeration := "Enumerate binding response-type and allocation faces."
    steinExpansion := "Expand risk by a vector Stein identity within each stratum."
    normalizerSelection := "Use the certified c-dagger LP sequence to select a normalizer."
    limitProblem := "Pass the primal and dual games to a stratified diffusion-control or spectral value problem."
    compatibilityConditions := "Impose face and corner compatibility conditions."
    nonassertionDisclaimer := "No limiting operator, normalizer, or value problem is asserted." }

/-- Descriptive, nonassertive payload for the unresolved feedback construction. -/
structure FeedbackHandle where
  scoreVector : String
  saddleCorrection : String
  finiteLift : String
  priorDiscretization : String
  nonassertionDisclaimer : String

-- @node: def:attainment-handle
/-- The contrast-score feedback handle records the score mean, variance, and shrinkage quantities used in the upper-risk analysis. -/
def contrastScoreFeedbackHandle : FeedbackHandle :=
  { scoreVector := "Begin with the centered arm-score vector generated by q-star."
    saddleCorrection := "Derive an orbit-saddle posterior mean or feedback correction from the limiting value function."
    finiteLift := "Lift that correction to finite n."
    priorDiscretization := "Discretize the squared ground state or dual occupation measure into a least-favorable prior on response-type counts."
    nonassertionDisclaimer := "Optimizer and prior convergence remain unresolved." }

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
