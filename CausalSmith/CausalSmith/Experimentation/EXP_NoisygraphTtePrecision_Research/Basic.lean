module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Fixed schedules and the two-sided acquisition experiment

Cold scaffold: definitions are complete; proof obligations are reserved for Stage 3.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

-- @env: S1
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The population carrier indexed by the public number of units. -/
abbrev PopulationCarrier (n : ℕ) : Type := Fin n -- @realizes V(n-indexed finite carrier)

/-- The admitted population and degree regime. -/
def PopulationDomain (n d : ℕ) : Prop :=
  4 ≤ n ∧ -- @realizes n(population size at least four)
  1 ≤ d ∧ d ≤ n - 1 -- @realizes d(off-diagonal degree cap in {1,...,n-1})

/-- The inherited concrete affine schedule, with directed irreflexive arrows. -/
abbrev Schedule (V : Type*) : Type _ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.Schedule V -- @realizes eta(fixed graph and real coefficient schedule) -- @realizes G(arbitrary directed graph carried by inherited Schedule.edge and constrained off diagonal by Schedule.irrefl)
/-- Off-diagonal arrow labels. -/
abbrev OffDiag (V : Type*) : Type _ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.OffDiag V -- @realizes E(ordered pairs j≠i)
/-- Assignment arguments. -/
abbrev Assign (V : Type*) : Type _ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.Assign V -- @realizes z(Bool-valued assignment argument)
/-- Affine deterministic responses from the inherited schedule. -/
abbrev potentialOutcome (η : Schedule V) (i : V) (z : Assign V) : ℝ :=
  CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η i z -- @realizes Y(a_i+t_i z_i+sum on true arrows of b_ij z_j)
/-- The finite-population all-treated minus all-control average. -/
abbrev tte (η : Schedule V) : ℝ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η -- @realizes theta(average contrast of the constructed affine responses)
/-- The incoming off-diagonal degree. -/
def incomingDegree (η : Schedule V) (i : V) : ℕ := (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i).card -- @realizes e(cardinality of true incoming donors)
/-- [An incoming degree is at most the number of other units.](goal) -/
-- @node: incomingDegree_le
lemma incomingDegree_le (η : Schedule V) (i : V) : incomingDegree η i ≤ Fintype.card V - 1 := by
  classical
  have hsub : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i ⊆
      Finset.univ.erase i := by
    intro j hj
    have he := (Finset.mem_filter.mp hj).2
    exact Finset.mem_erase.mpr ⟨fun h => η.irrefl i (h ▸ he), Finset.mem_univ j⟩
  simpa [incomingDegree] using Finset.card_le_card hsub
/-- The incoming-degree atom. -/
-- @node: ass:in-degree
def InDegreeLE (η : Schedule V) (d : ℕ) : Prop := ∀ i, (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i).card ≤ d
/-- The out-degree atom is the substrate block-degree predicate on incoming neighborhoods. -/
-- @node: ass:out-degree
def OutDegreeLE (η : Schedule V) (d : ℕ) : Prop :=
  Causalean.Experimentation.DesignBased.BlockDegreeLE (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η) d
/-- The row coefficient-mass atom includes the baseline. -/
-- @node: ass:coefficient-mass
def CoefficientMassLE (η : Schedule V) : Prop :=
  ∀ i, |η.a i| + |η.t i| + ∑ j ∈ CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i, |η.b i j| ≤ 1
/-- The complete fixed-schedule class, with all three member atoms. -/
-- @node: def:model
structure ScheduleClass (η : Schedule V) (d : ℕ) : Prop where
  inDegree : InDegreeLE η d
  outDegree : OutDegreeLE η d
  coeffMass : CoefficientMassLE η
-- @realizes Mclass(the conjunction of both degree caps and the row coefficient envelope)
/-- [The local class has exactly the inherited class's content.](goal) -/
-- @node: scheduleClass_iff_thin
lemma scheduleClass_iff_thin (η : Schedule V) (d : ℕ) :
    ScheduleClass η d ↔ CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.ScheduleClass η d := by
  constructor
  · intro h
    exact ⟨h.inDegree, h.outDegree, h.coeffMass⟩
  · intro h
    exact ⟨h.inDegree, h.outDegree, h.coeffMass⟩
/-- Given [the stated assumptions](hyp:h,hdd'), [Enlarging the degree cap preserves class membership.](goal) -/
-- @node: ScheduleClass.mono
lemma ScheduleClass.mono {η : Schedule V} {d d' : ℕ}
    (h : ScheduleClass η d) (hdd' : d ≤ d') : ScheduleClass η d' := by
  exact (scheduleClass_iff_thin η d').mpr
    (((scheduleClass_iff_thin η d).mp h).mono hdd')
/-- Given [the stated assumptions](hyp:h), [Every class response is bounded by one.](goal) -/
-- @node: abs_potentialOutcome_le_one
lemma abs_potentialOutcome_le_one {η : Schedule V} {d : ℕ} (h : ScheduleClass η d)
    (i : V) (z : Assign V) : |CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η i z| ≤ 1 := by
  exact CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.abs_potentialOutcome_le_one
    ((scheduleClass_iff_thin η d).mp h) i z
/-- Given [the stated assumptions](hyp:h), [Every class causal target is bounded by one.](goal) -/
-- @node: abs_tte_le_one
lemma abs_tte_le_one {η : Schedule V} {d : ℕ} (h : ScheduleClass η d) :
    |CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η| ≤ 1 := by
  exact CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.abs_tte_le_one
    ((scheduleClass_iff_thin η d).mp h)
-- @realizes theta(derived target range [-1,1] on the fixed-schedule class)

-- @env: S2
variable (V)
/-- The acquired off-diagonal graph array. -/
abbrev Acq : Type _ := OffDiag V → Bool -- @realizes H(Bool array on all off-diagonal arrow labels)
/-- The original standard Borel record space, keeping all graph, treatment, and outcome labels. -/
abbrev Record : Type _ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.Record V -- @realizes Omega({0,1}^E × {0,1}^V × ℝ^V)
variable {V}
/-- Centered assignment signs. -/
abbrev signOf (z : Bool) : ℝ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf z -- @realizes X(centered sign 2Z_j-1 in {-1,1})
/-- The public channel domain. -/
def ChannelDomain (q r : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ q ∧ -- @realizes r(false-edge probability in [0,q])
  q ≤ 1 -- @realizes q(true-edge probability in [0,1], with nonnegativity from r≤q)
/-- Independent edge reports at q on true arrows and r otherwise. -/
def acquisitionLaw (η : Schedule V) (q r : ℝ) : Measure (Acq V) :=
  Measure.pi (fun e : OffDiag V => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (if η.edge e.1.1 e.1.2 then q else r))
/-- Population-indexed joint assignment and report laws. -/
abbrev Design (V : Type*) : Type _ := Schedule V → Measure (Assign V × Acq V)
/-- The canonical independent two-sided design. -/
def noisyDesign (q r : ℝ) : Design V :=
  fun η => (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V).prod (acquisitionLaw η q r)
/-- The full assignment marginal is the product half-Bernoulli law at every population. -/
-- @node: ass:assignment
def AssignmentLaw (D : Design V) : Prop := ∀ η, (D η).map Prod.fst = CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V
-- @realizes Z(independent half-Bernoulli treatment coordinates)
/-- The complete acquired-graph marginal is the calibrated product law. -/
-- @node: ass:acquisition
def AcquisitionLaw (D : Design V) (q r : ℝ) : Prop :=
  ∀ η, (D η).map Prod.snd = acquisitionLaw η q r
/-- Graph acquisition and assignment are independent at each fixed population. -/
-- @node: ass:design-independence
def DesignIndependent (D : Design V) : Prop :=
  ∀ η, ProbabilityTheory.IndepFun Prod.fst Prod.snd (D η)
/-- The complete numerical record, with no graph coordinate discarded. -/
def recordOf (η : Schedule V) (ω : Assign V × Acq V) : Record V :=
  (ω.2, ω.1, fun i => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η i ω.1) -- @realizes O(full H,Z,Y(Z) record)
/-- The independent uniform seed law on the closed unit interval. -/
abbrev seedLaw : Measure ℝ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.seedLaw -- @realizes U(uniform [0,1] seed independent of the record)
/-- The seeded experiment law, for a fixed population. -/
def recordLaw (D : Design V) (η : Schedule V) : Measure (Record V × ℝ) :=
  ((D η).prod seedLaw).map (fun ω => (recordOf η ω.1, ω.2)) -- @realizes P(law of (O,U), population fixed) -- @realizes U(product construction makes the uniform seed independent of the complete record)

end CausalSmith.Experimentation.NoisygraphTtePrecision
