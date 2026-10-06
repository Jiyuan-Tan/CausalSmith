module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Basic

/-!
# Symmetric causal law certificates

Finite Bernoulli sums establish normalization and the ancillary assignment law.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology Classical

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

variable {d : ℕ}

/-- Assume [the stated htheta condition](hyp:htheta). [Every weight in the symmetric construction is nonnegative on the parameter cube. [](](goal). -/
-- @node: symmetric_weight_nonneg
lemma symmetric_weight_nonneg (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (w : FullRecord d) :
    0 ≤ (d : ℝ)⁻¹ * (1/2) *
      bernMass ((1 - theta (cell w))/2) (outcome0 w) *
      bernMass ((1 + theta (cell w))/2) (outcome1 w) *
      (if outcome w = potential (arm w) w then 1 else 0) := by
  have h := htheta (cell w)
  have h0 : 0 ≤ bernMass ((1 - theta (cell w))/2) (outcome0 w) := by
    cases outcome0 w <;> simp only [bernMass, Bool.false_eq_true, ↓reduceIte] <;> linarith [h.1, h.2]
  have h1 : 0 ≤ bernMass ((1 + theta (cell w))/2) (outcome1 w) := by
    cases outcome1 w <;> simp only [bernMass, Bool.false_eq_true, ↓reduceIte] <;> linarith [h.1, h.2]
  positivity

/-- Assume [the stated hw condition](hyp:hw). [Real probabilities of finite atomic events are sums of the nonnegative weights](goal). -/
-- @node: atomLaw_real_event
lemma atomLaw_real_event {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (weights : α → ℝ) (hw : ∀ a, 0 ≤ weights a)
    (E : Set α) : (atomLaw weights).real E = ∑ a, if a ∈ E then weights a else 0 := by
  classical
  simp only [Measure.real, atomLaw, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply]
  rw [ENNReal.toReal_sum (by intro a ha; by_cases h : a ∈ E <;> simp [h])]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a ∈ E <;> simp [h, ENNReal.toReal_ofReal (hw a)]

/-- Assume [the stated htheta condition](hyp:htheta). [Event probabilities in the symmetric construction have their explicit Bernoulli expansion. [](](goal). -/
-- @node: symmetricLaw_real_event
lemma symmetricLaw_real_event (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (E : Set (FullRecord d)) :
    (symmetricLaw theta).real E = ∑ w : FullRecord d,
      if w ∈ E then (d : ℝ)⁻¹ * (1/2) *
        bernMass ((1 - theta (cell w))/2) (outcome0 w) *
        bernMass ((1 + theta (cell w))/2) (outcome1 w) *
        (if outcome w = potential (arm w) w then 1 else 0) else 0 := by
  exact atomLaw_real_event _ (symmetric_weight_nonneg theta htheta) E

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Summing the Bernoulli potentials and consistent outcome gives unit total mass](goal). -/
-- @node: symmetricLaw_probability
lemma symmetricLaw_probability (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (hd : 0 < d) : IsProbabilityMeasure (symmetricLaw theta) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hmass : (symmetricLaw theta).real Set.univ = 1 := by
    rw [symmetricLaw_real_event theta htheta]
    simp only [Set.mem_univ, ↓reduceIte]
    rw [Fintype.sum_prod_type]
    have hcell : ∀ j : Fin d, (∑ w : Bool × Bool × Bool × Bool,
        (d : ℝ)⁻¹ * (1/2) *
          bernMass ((1 - theta (cell (j,w)))/2) (outcome0 (j,w)) *
          bernMass ((1 + theta (cell (j,w)))/2) (outcome1 (j,w)) *
          (if outcome (j,w) = potential (arm (j,w)) (j,w) then 1 else 0)) = (d : ℝ)⁻¹ := by
      intro j
      simp [Fintype.sum_prod_type, Fintype.sum_bool, cell, outcome0, outcome1, outcome,
        potential, arm, bernMass]
      <;> ring
    simp_rw [hcell]
    simp [hdR]
  constructor
  exact (ENNReal.toReal_eq_one_iff _).mp hmass

/-- Assume [the stated htheta condition](hyp:htheta). [A fair assignment is ancillary to the signed input under the symmetric law. [](](goal). -/
-- @node: symmetricLaw_ancillary
lemma symmetricLaw_ancillary (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (j : Fin d) (s a : Bool) :
    (symmetricLaw theta).real
      {w | cell w = j ∧ signedObserve (observe w) = (j,s) ∧ arm w = a} =
      (pairedLaw theta).real {(j,s)}/2 := by
  rw [symmetricLaw_real_event theta htheta]
  have hpaired : (pairedLaw theta).real {(j,s)} = (1 + signVal s * theta j)/(2*d) := by
    unfold pairedLaw
    rw [atomLaw_real_event]
    · simp
    · intro v
      have h := htheta v.1
      apply div_nonneg _ (by positivity)
      cases v.2 <;> simp only [signVal, Bool.false_eq_true, ↓reduceIte] <;> linarith [h.1, h.2]
  rw [hpaired, Fintype.sum_prod_type]
  simp only [Set.mem_setOf_eq, cell, observe, arm, outcome, signedObserve, Prod.mk.injEq]
  cases s <;> cases a <;>
    simp [Fintype.sum_prod_type, Fintype.sum_bool, outcome0, outcome1, potential,
      outcome, arm, cell, bernMass, signVal]
  <;> ring

/-- Assume [the stated htheta condition](hyp:htheta). [Each public cell has mass one over the dimension. [](](goal). -/
-- @node: symmetricLaw_uniform
lemma symmetricLaw_uniform (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) :
    UniformCovariates (symmetricLaw theta) := by
  intro j
  rw [symmetricLaw_real_event theta htheta]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, cell, outcome0, outcome1, outcome,
    potential, arm, bernMass]
  <;> ring

/-- Assume [the stated htheta condition](hyp:htheta). [The cellwise potential marginals are the two declared Bernoulli arm means. [](](goal). -/
-- @node: symmetricLaw_potential_mass
lemma symmetricLaw_potential_mass (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (j : Fin d) (a : Bool) :
    (symmetricLaw theta).real {w | cell w = j ∧ potential a w = true} =
      (d : ℝ)⁻¹ * ((1 + signVal a * theta j)/2) := by
  rw [symmetricLaw_real_event theta htheta]
  cases a <;>
    simp [Fintype.sum_prod_type, Fintype.sum_bool, cell, outcome0, outcome1, outcome,
      potential, arm, bernMass, signVal]
  <;> ring

/-- Assume [the stated htheta condition](hyp:htheta). [Independent fair assignment remains fair conditional on both potential outcomes. [](](goal). -/
-- @node: symmetricLaw_fair
lemma symmetricLaw_fair (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) :
    FairRandomization (symmetricLaw theta) := by
  intro j a y0 y1
  rw [symmetricLaw_real_event theta htheta, symmetricLaw_real_event theta htheta]
  cases a <;> cases y0 <;> cases y1 <;>
    simp [Fintype.sum_prod_type, Fintype.sum_bool, cell, outcome0, outcome1, outcome,
      potential, arm, bernMass]
  <;> ring

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [All symmetric-law mass is supported on consistent records](goal). -/
-- @node: symmetricLaw_consistent
lemma symmetricLaw_consistent (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (hd : 0 < d) : Consistency (symmetricLaw theta) := by
  haveI := symmetricLaw_probability theta htheta hd
  have heq : (symmetricLaw theta).real {w | outcome w = potential (arm w) w} =
      (symmetricLaw theta).real Set.univ := by
    rw [symmetricLaw_real_event theta htheta, symmetricLaw_real_event theta htheta]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : outcome w = potential (arm w) w <;> simp [h]
  exact heq.trans (by simp)

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [The symmetric construction has the specified arm means in every nonempty cell](goal). -/
-- @node: symmetricLaw_armMean
lemma symmetricLaw_armMean (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (hd : 0 < d) (a : Bool) (j : Fin d) :
    armMean (symmetricLaw theta) a j = (1 + signVal a * theta j)/2 := by
  unfold armMean
  rw [symmetricLaw_potential_mass theta htheta, symmetricLaw_uniform theta htheta j]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Cube parameters give the interior means required by the causal model](goal). -/
-- @node: symmetricLaw_causalModel
lemma symmetricLaw_causalModel (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (hd : 0 < d) : CausalModel (symmetricLaw theta) := by
  refine ⟨symmetricLaw_uniform theta htheta, symmetricLaw_fair theta htheta,
    symmetricLaw_consistent theta htheta hd, ?_⟩
  intro a j
  rw [symmetricLaw_armMean theta htheta hd]
  have h := htheta j
  cases a <;> simp only [signVal, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc] <;>
    constructor <;> linarith [h.1, h.2]

end CausalSmith.Stat.LdpOptvalueUniformFrontier
