import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Estimator
import Causalean.Experimentation.DesignBased.Chebyshev
import Causalean.Experimentation.DesignBased.InProb
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.EReal.Basic

/-!
# Triangular arrays and the dense schedule class

This file bundles each deterministic row of the experiment and defines exactly
the five asymptotic/support conditions used by the paper.
-/

open Filter

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

/-- A triangular array of feasible dense random-group experiment rows. -/
structure ScheduleArray (M : ℕ) where -- @realizes M(fixed across rows)
  groupSize_ge_two : 2 ≤ M -- @realizes M(common group size at least two)
  popSize : ℕ → ℕ -- @realizes n(row population size)
  groups : ℕ → ℕ -- @realizes G_n(row group count)
  treated : ℕ → ℕ -- @realizes G_{1n}(row treated-group count)
  groups_pos : ∀ r, 0 < groups r
  grouped_le : ∀ r, M * groups r ≤ popSize r
    -- @realizes N_n(M times G and at most n)
  treated_pos : ∀ r, 0 < treated r -- @realizes G_{1n}(at least one treated group)
  treated_lt : ∀ r, treated r < groups r -- @realizes G_{1n}(strictly below all groups)
  treated_le : ∀ r, treated r ≤ groups r
  schedule : ∀ r, PotentialOutcome (popSize r) M
    -- @realizes Y_{i,n}(z,A)(deterministic row schedule)

/-- Row control-group count. -/
def ScheduleArray.controls {M : ℕ} (A : ScheduleArray M) (r : ℕ) : ℕ :=
  A.groups r - A.treated r
  -- @realizes G_{0n}(row G minus G1)

/-- Row grouped-unit count. -/
def ScheduleArray.grouped {M : ℕ} (A : ScheduleArray M) (r : ℕ) : ℕ :=
  M * A.groups r
  -- @realizes N_n(row M times G)

/-- Row treatment fraction. -/
noncomputable def ScheduleArray.treatmentFraction {M : ℕ} (A : ScheduleArray M)
    (r : ℕ) : ℝ := pFrac (A.groups r) (A.treated r) (A.treated_pos r) (A.treated_lt r)
  -- @realizes p_n(row treated fraction)

/-- The row's joint finite design. -/
noncomputable def ScheduleArray.design {M : ℕ} (A : ScheduleArray M) (r : ℕ) :=
  randomPartitionDesign (A.popSize r) M (A.groups r) (A.treated r)
    (A.grouped_le r) (A.treated_le r)

/-- The row's exact PAME variance. -/
noncomputable def ScheduleArray.variance {M : ℕ} (A : ScheduleArray M) (r : ℕ) : ℝ :=
  sigmaSq (A.schedule r) (A.grouped_le r) (A.treated_pos r) (A.treated_lt r)

/-- [Each feasible row contains at least one whole group](goal). -/
lemma ScheduleArray.groupSize_le {M : ℕ} (A : ScheduleArray M) (r : ℕ) : M ≤ A.popSize r := by
  exact le_trans (Nat.le_mul_of_pos_right M (A.groups_pos r)) (A.grouped_le r)

/-- Row arm variance. -/
noncomputable def ScheduleArray.armVariance {M : ℕ} (A : ScheduleArray M)
    (r : ℕ) (z : Arm) : ℝ :=
  armVar (A.popSize r) M (A.groupSize_le r) (A.schedule r) z

/-- Row ordered-disjoint covariance. -/
noncomputable def ScheduleArray.armCrossCov {M : ℕ} (A : ScheduleArray M)
    (r : ℕ) (a b : Arm) : ℝ :=
  crossCov (A.popSize r) M (A.groupSize_le r) (A.schedule r) a b

/-- Row ordered-disjoint arm-contrast covariance. -/
noncomputable def ScheduleArray.contrastCrossCov {M : ℕ} (A : ScheduleArray M)
    (r : ℕ) : ℝ :=
  crossCovContrast (A.popSize r) M (A.groupSize_le r) (A.schedule r)

/-- Row independent-group leading variance. -/
noncomputable def ScheduleArray.leadingVariance {M : ℕ} (A : ScheduleArray M)
    (r : ℕ) : ℝ :=
  indepGroupVar (A.popSize r) M (A.groups r) (A.treated r)
    (A.groupSize_le r) (A.treated_pos r) (A.treated_lt r) (A.schedule r)

/-- Row degree-one arm-difference energy. -/
noncomputable def ScheduleArray.degreeOne {M : ℕ} (A : ScheduleArray M)
    (hMpos : 0 < M) (J : ∀ r, JohnsonProjections (A.popSize r) M) (r : ℕ) : ℝ :=
  degreeOneEnergy (A.popSize r) M hMpos (A.groupSize_le r) (J r) (A.schedule r)

/-- Row scalar CR2 statistic. -/
noncomputable def ScheduleArray.cr2 {M : ℕ} (A : ScheduleArray M) (r : ℕ) :
    PartitionTuple (A.popSize r) M (A.groups r) ×
      TreatmentSpace (A.groups r) (A.treated r) → ℝ :=
  if h : 2 ≤ A.treated r ∧ 2 ≤ A.controls r then
    cr2Var (A.schedule r) h.1 (by simpa [ScheduleArray.controls] using h.2)
  else fun _ => 0

-- @node: ass:group-count-growth
/-- The number of randomized groups tends to infinity. -/
def GroupCountGrowth {M : ℕ} (A : ScheduleArray M) : Prop :=
  Tendsto A.groups atTop atTop

-- @node: ScheduleArray.popSize_tendsto_atTop
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,hGrowth), [the indicated sequence converges to its stated limit](goal). -/
lemma ScheduleArray.popSize_tendsto_atTop {M : ℕ} (A : ScheduleArray M)
    (hGrowth : GroupCountGrowth A) : Tendsto A.popSize atTop atTop := by
  unfold GroupCountGrowth at hGrowth
  rw [tendsto_atTop_atTop] at hGrowth ⊢
  intro b
  obtain ⟨R, hR⟩ := hGrowth b
  refine ⟨R, fun r hr => (hR r hr).trans ?_⟩
  have hMpos : 0 < M := lt_of_lt_of_le (by omega) A.groupSize_ge_two
  exact le_trans (Nat.le_mul_of_pos_left (A.groups r) hMpos)
    (A.grouped_le r)

-- @node: ass:stable-treatment-fraction
/-- Treatment fractions converge to an interior limit. -/
def StableTreatmentFraction {M : ℕ} (A : ScheduleArray M) (p : ℝ) : Prop :=
  0 < p ∧ -- @realizes p(interior limiting fraction)
  p < 1 ∧ -- @realizes p(interior limiting fraction)
  Tendsto A.treatmentFraction atTop (nhds p) -- @realizes p(limit of p_n)

-- @node: ass:sampling-fraction
/-- Grouped-unit fractions converge in the closed unit interval. -/
def SamplingFractionLimit {M : ℕ} (A : ScheduleArray M) (rho : ℝ) : Prop :=
  0 ≤ rho ∧ -- @realizes \rho(closed unit interval)
  rho ≤ 1 ∧ -- @realizes \rho(closed unit interval)
  Tendsto (fun r => (A.grouped r : ℝ) / (A.popSize r : ℝ)) atTop (nhds rho)
    -- @realizes \rho(limit of N_n over n)

-- @node: ass:bounded-potential-outcomes
/-- The schedule is uniformly bounded over rows, groups, members, and arms. -/
def BoundedSchedule {M : ℕ} (A : ScheduleArray M) (B : ℝ) : Prop :=
  0 < B ∧ -- @realizes B(strictly positive finite uniform envelope)
  ∀ r (S : Omega (A.popSize r) M) (i : {j // j ∈ S.1}) (z : Arm),
    |A.schedule r S i z| ≤ B -- @realizes B(bounds all potential outcomes)

-- @node: ass:scaled-variance-nondegeneracy
/-- The liminf of the group-scaled exact variance has a positive uniform floor. -/
noncomputable def ScaledVarianceNondegenerate {M : ℕ} (A : ScheduleArray M)
    (cSigma : ℝ) : Prop :=
  0 < cSigma ∧ -- @realizes c_\sigma(strictly positive uniform constant)
  (cSigma : EReal) ≤ Filter.liminf (fun r =>
    (((A.groups r : ℝ) * A.variance r : ℝ) : EReal)) atTop
    -- @realizes c_\sigma(lower bound on scaled variance liminf)

-- @node: def:dense-schedule-class
/-- The paper's dense bounded schedule-array class. -/
structure DenseScheduleClass {M : ℕ} (A : ScheduleArray M)
    (p rho B cSigma : ℝ) : Prop where
  growth : GroupCountGrowth A
  fraction : StableTreatmentFraction A p
  sampling : SamplingFractionLimit A rho
  bounded : BoundedSchedule A B
  nondegenerate : ScaledVarianceNondegenerate A cSigma
  -- @realizes \mathcal C_{\mathrm{dense}}(five-condition schedule class)

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
