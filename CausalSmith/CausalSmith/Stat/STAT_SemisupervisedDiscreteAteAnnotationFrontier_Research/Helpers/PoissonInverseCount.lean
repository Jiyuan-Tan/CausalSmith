module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Basic
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Causalean.Stat.Concentration.Poisson.SelfNormalized.Chernoff
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.Splitting
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.CellLaws
public import Causalean.Mathlib.Probability.Poisson.Poincare.Tensorization
public import Causalean.Mathlib.Probability.Poisson.InverseMoments

/-! Bias and variance of the all-heavy Poisson inverse-count statistic. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators


/-- Per-cell, per-arm outcome and marginal counts.  [the stated conditions](hyp:d) [the stated conclusion](goal). -/
abbrev PoissonCounts (d : Nat) := Fin d → Bool → Nat × Nat

/-- Independent outcome/marginal Poisson count law.  [the stated conditions](hyp:P,u,t) [the stated conclusion](goal). -/
noncomputable def poissonCountLaw {d : Nat} (P : DiscreteLaw d) (u t : Real) :
    Measure (PoissonCounts d) :=
  Measure.pi fun x : Fin d => Measure.pi fun a : Bool =>
    (poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
      (poissonMeasure (Real.toNNReal (t * armMass P x a)))

/-- The all-heavy inverse-count statistic.  [the stated conditions](hyp:u,K) [the stated conclusion](goal). -/
noncomputable def inverseCountStatistic {d : Nat} (u : Real) (K : PoissonCounts d) : Real :=
  ∑ x : Fin d,
    ((K x true).1 / u * ((K x false).2 + (K x true).2 + 1 : Nat) /
          ((K x true).2 + 1 : Nat) -
        (K x false).1 / u * ((K x false).2 + (K x true).2 + 1 : Nat) /
          ((K x false).2 + 1 : Nat))

/-- Expectation of a statistic under a supplied law.  [the stated conditions](hyp:mu,f) [the stated conclusion](goal). -/
noncomputable def expectationUnder {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (f : α → Real) : Real := ∫ z, f z ∂mu

/-- Centered second moment under a supplied law.  [the stated conditions](hyp:mu,f) [the stated conclusion](goal). -/
noncomputable def varianceUnder {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (f : α → Real) : Real :=
  ∫ z, (f z - expectationUnder mu f) ^ 2 ∂mu

-- @node: markedMass_eq_armMass_mul_outcomeMean
/-- The marked mass factors into arm mass and the corresponding outcome mean,
including at zero-mass arm cells.  [the stated conclusion](goal). -/
lemma markedMass_eq_armMass_mul_outcomeMean {d : Nat} (P : DiscreteLaw d)
    (x : Fin d) (a : Bool) :
    markedMass P x a = armMass P x a * outcomeMean P a x := by
  rw [markedMass, outcomeMean]
  by_cases h : armMass P x a = 0
  · have hj_nonneg := (jointMass_mem_unitInterval P x a true).1
    have hj_le : jointMass P x a true ≤ armMass P x a := by
      simp [armMass]
      exact (jointMass_mem_unitInterval P x a false).1
    have hj : jointMass P x a true = 0 := by linarith
    simp [h, hj]
  · field_simp

-- @node: cellMass_sum_eq_one_annotation
/-- The covariate cell masses sum to one.  [the stated conclusion](goal). -/
lemma cellMass_sum_eq_one_annotation {d : Nat} (P : DiscreteLaw d) :
    ∑ x : Fin d, cellMass P x = 1 := by
  have htotal : ∑ z : Obs d, (P.pmf z).toReal = 1 := by
    simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : Real))).symm
  calc
    ∑ x : Fin d, cellMass P x = ∑ z : Obs d, (P.pmf z).toReal := by
      simp [cellMass, jointMass, Fintype.sum_prod_type]
    _ = 1 := htotal

-- @node: overlap_armMass_bounds
/-- Occupied-cell overlap gives the two arm-mass comparisons used in the
inverse-count moment calculation.  [the stated conditions](hyp:hP) [the stated conclusion](goal). -/
lemma overlap_armMass_bounds {d : Nat} {eps : Real} (P : DiscreteLaw d)
    (hP : Overlap eps P) (x : Fin d) (a : Bool) :
    eps * cellMass P x ≤ armMass P x a ∧
      armMass P x a ≤ (1 - eps) * cellMass P x := by
  have hcell := (cellMass_mem_unitInterval P x).1
  by_cases hz : cellMass P x = 0
  · have harm_nonneg : 0 ≤ armMass P x a := by
      exact Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P x a y).1
    have harm_le : armMass P x a ≤ cellMass P x := by
      have hsum : armMass P x false + armMass P x true = cellMass P x := by
        simp [armMass, cellMass]
        ring
      cases a
      · linarith [show 0 ≤ armMass P x true from
          Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P x true y).1]
      · linarith [show 0 ≤ armMass P x false from
          Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P x false y).1]
    have harm : armMass P x a = 0 := by linarith
    simp [hz, harm]
  · have hcpos : 0 < cellMass P x := lt_of_le_of_ne hcell (Ne.symm hz)
    have hov := hP x hcpos
    have hfactor : armMass P x true = cellMass P x * propensity P x := by
      rw [propensity]
      field_simp
    cases a
    · have hsum : armMass P x false + armMass P x true = cellMass P x := by
        simp [armMass, cellMass]
        ring
      constructor
      · rw [hfactor] at hsum
        nlinarith [mul_le_mul_of_nonneg_left hov.2 hcell]
      · rw [hfactor] at hsum
        nlinarith [mul_le_mul_of_nonneg_left hov.1 hcell]
    · rw [hfactor]
      constructor
      · simpa [mul_comm] using mul_le_mul_of_nonneg_left hov.1 hcell
      · simpa [mul_comm] using mul_le_mul_of_nonneg_left hov.2 hcell

-- @node: poisson_bias_envelope
/-- The elementary exponential envelope used to sum the inverse-count bias
over cells without imposing a minimum cell mass.  [the stated conditions](hyp:heps,ht,_hz) [the stated conclusion](goal). -/
lemma poisson_bias_envelope {eps t z : Real} (heps : 0 < eps) (ht : 0 < t)
    (_hz : 0 ≤ z) :
    z * Real.exp (-eps * t * z) ≤ 1 / (eps * Real.exp 1 * t) := by
  have hc : 0 < eps * t := mul_pos heps ht
  have hbase : Real.exp 1 * (eps * t * z) ≤ Real.exp (eps * t * z) :=
    Real.exp_one_mul_le_exp
  have hmul := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (-(eps * t * z))).le
  have hprod : Real.exp 1 * (eps * t * z) * Real.exp (-(eps * t * z)) ≤ 1 := by
    calc
      _ ≤ Real.exp (eps * t * z) * Real.exp (-(eps * t * z)) := hmul
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
  apply (le_div_iff₀ (by positivity : 0 < eps * Real.exp 1 * t)).2
  calc
    z * Real.exp (-eps * t * z) * (eps * Real.exp 1 * t) =
        Real.exp 1 * (eps * t * z) * Real.exp (-(eps * t * z)) := by ring
    _ ≤ 1 := hprod

-- @node: poisson_bias_sum_le
/-- Summing the exponential envelope gives the dimension-over-intensity part
of the inverse-count bias bound.  [the stated conditions](hyp:heps,ht,hp) [the stated conclusion](goal). -/
lemma poisson_bias_sum_le {d : Nat} (p : Fin d → Real) {eps t : Real}
    (heps : 0 < eps) (ht : 0 < t) (hp : ∀ x, 0 ≤ p x) :
    (∑ x, p x * Real.exp (-eps * t * p x)) ≤
      d / (eps * Real.exp 1 * t) := by
  calc
    (∑ x, p x * Real.exp (-eps * t * p x)) ≤
        ∑ _x : Fin d, 1 / (eps * Real.exp 1 * t) :=
      Finset.sum_le_sum fun x _ ↦ poisson_bias_envelope heps ht (hp x)
    _ = d / (eps * Real.exp 1 * t) := by
      simp [div_eq_mul_inv]

-- @node: poisson_bias_sum_le_min
/-- The same cellwise sum also has its probability-mass cap, yielding exactly
the minimum used in the uniform bias estimate.  [the stated conditions](hyp:heps,ht,hp,hsum) [the stated conclusion](goal). -/
lemma poisson_bias_sum_le_min {d : Nat} (p : Fin d → Real) {eps t : Real}
    (heps : 0 < eps) (ht : 0 < t) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) :
    (∑ x, p x * Real.exp (-eps * t * p x)) ≤
      min 1 (d / (eps * Real.exp 1 * t)) := by
  apply le_min
  · calc
      (∑ x, p x * Real.exp (-eps * t * p x)) ≤ ∑ x, p x := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_of_le_one_right (hp x)
        rw [Real.exp_le_one_iff]
        have hx : 0 ≤ eps * t * p x :=
          mul_nonneg (mul_nonneg heps.le ht.le) (hp x)
        nlinarith
      _ = 1 := hsum
  · exact poisson_bias_sum_le p heps ht hp

-- @node: poisson_bias_min_rescale
/-- Absorb the overlap factor in the exponential-envelope bound into a
constant depending only on `eps`, leaving the paper's `min 1 (d / t)` rate.  [the stated conditions](hyp:heps,ht) [the stated conclusion](goal). -/
lemma poisson_bias_min_rescale (d : Nat) {eps t : Real}
    (heps : 0 < eps) (ht : 0 < t) :
    2 * min 1 (d / (eps * Real.exp 1 * t)) ≤
      (2 * max 1 (eps * Real.exp 1)⁻¹) * min 1 (d / t) := by
  let x : Real := d / t
  let a : Real := eps * Real.exp 1
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hrewrite : d / (eps * Real.exp 1 * t) = x / a := by
    dsimp [x, a]
    field_simp
  rw [hrewrite]
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    have hxa : min 1 (x / a) ≤ x / a := min_le_right _ _
    have hainv : a⁻¹ ≤ max 1 a⁻¹ := le_max_right _ _
    have hscale : x / a ≤ max 1 a⁻¹ * x := by
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right hainv hx
    nlinarith
  · have hx1' : 1 ≤ x := le_of_not_ge hx1
    rw [min_eq_left hx1']
    have hmin : min 1 (x / a) ≤ 1 := min_le_left _ _
    have hmax : 1 ≤ max 1 a⁻¹ := le_max_left _ _
    nlinarith

-- @node: inverse_count_bias_aggregate
/-- Once each arm/cell mean has the Poisson missing-cell envelope, summing the
two arm errors gives the complete inverse-count bias bound.  [the stated conditions](hyp:heps,ht,hg) [the stated conclusion](goal). -/
lemma inverse_count_bias_aggregate {d : Nat} (P : DiscreteLaw d)
    {eps t : Real} (heps : 0 < eps) (ht : 0 < t)
    (g : Fin d → Bool → Real)
    (hg : ∀ x a,
      |g x a - cellMass P x * outcomeMean P a x| ≤
        cellMass P x * Real.exp (-eps * t * cellMass P x)) :
    |∑ x, (g x true - g x false) - ateFunctional P| ≤
      2 * min 1 (d / (eps * Real.exp 1 * t)) := by
  have hp (x : Fin d) : 0 ≤ cellMass P x := (cellMass_mem_unitInterval P x).1
  have hsum := poisson_bias_sum_le_min
    (fun x ↦ cellMass P x) heps ht hp (cellMass_sum_eq_one_annotation P)
  rw [ateFunctional, ← Finset.sum_sub_distrib]
  calc
    |∑ x, ((g x true - g x false) -
        cellMass P x * (outcomeMean P true x - outcomeMean P false x))| =
        |∑ x, ((g x true - cellMass P x * outcomeMean P true x) -
          (g x false - cellMass P x * outcomeMean P false x))| := by
            congr 1
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ ≤ ∑ x, |(g x true - cellMass P x * outcomeMean P true x) -
          (g x false - cellMass P x * outcomeMean P false x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, (|g x true - cellMass P x * outcomeMean P true x| +
          |g x false - cellMass P x * outcomeMean P false x|) := by
      apply Finset.sum_le_sum
      intro x _
      exact abs_sub _ _
    _ ≤ ∑ x, (2 * (cellMass P x *
          Real.exp (-eps * t * cellMass P x))) := by
      apply Finset.sum_le_sum
      intro x _
      nlinarith [hg x true, hg x false]
    _ = 2 * ∑ x, cellMass P x * Real.exp (-eps * t * cellMass P x) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * min 1 (d / (eps * Real.exp 1 * t)) := by
      gcongr

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
