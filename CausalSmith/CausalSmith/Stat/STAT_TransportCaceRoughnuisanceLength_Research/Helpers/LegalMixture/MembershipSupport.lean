module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.TargetLaws

/-! # Primitive support for the legal IV completion

These lemmas implement the no-defiers and bounded-potential-outcome checks in
steps (13)--(18) of the legal-mixture roadmap, directly on the primitive atoms.
-/

public section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- An atomwise support condition survives covariate mixing.  Under [the displayed assumptions and inputs](hyp:s,density,mass,hm,p,hp,hatom), [the stated conclusion holds](goal). -/
-- @node: primitivePopulation_ae_of_atoms
lemma primitivePopulation_ae_of_atoms (s : Bool) (density : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1)
    (p : FullData → Prop) (hp : MeasurableSet {o | p o})
    (hatom : ∀ x d0 d1 y0 y1, mass x d0 d1 y0 y1 ≠ 0 →
      p (s, x, d0, d1, boolReal y0, boolReal y1)) :
    ∀ᵐ o ∂primitivePopulation s density mass, p o := by
  have hk (x : ℝ) : ∀ᵐ o ∂primitiveKernel s x mass, p o := by
    unfold primitiveKernel
    simp only [ae_finsetSum_measure_iff]
    intro d0 _ d1 _ y0 _ y1 _
    by_cases hz : mass x d0 d1 y0 y1 = 0
    · simp [hz]
    · apply Measure.ae_smul_measure
      simpa only [ae_dirac_eq, Filter.eventually_pure] using hatom x d0 d1 y0 y1 hz
  rw [ae_iff]
  unfold primitivePopulation
  rw [Measure.bind_apply (show MeasurableSet {o | ¬p o} from hp.compl)
    (primitiveKernel_measurable_of s mass hm).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact Filter.Eventually.of_forall fun x => ae_iff.mp (hk x)

/-- The primitive completion places no mass on the defier stratum.  Under [the displayed assumptions and inputs](hyp:s,density,b,u,v,hm), [the stated conclusion holds](goal). -/
-- @node: primitivePopulation_no_defiers
lemma primitivePopulation_no_defiers (s : Bool) (density : ℝ → ℝ)
    (b u v : ℝ → ℝ)
    (hm : ∀ d0 d1 y0 y1,
      Measurable fun x => primitiveMass (b x) (u x) (v x) d0 d1 y0 y1) :
    ∀ᵐ o ∂primitivePopulation s density
      (fun x => primitiveMass (b x) (u x) (v x)),
      boolReal (receipt0 o) ≤ boolReal (receipt1 o) := by
  apply primitivePopulation_ae_of_atoms s density _ hm
  · have h0 : Measurable (fun o : FullData => boolReal (receipt0 o)) := by
      unfold receipt0 boolReal
      exact Measurable.ite ((measurableSet_singleton true).preimage (by fun_prop))
        measurable_const measurable_const
    have h1 : Measurable (fun o : FullData => boolReal (receipt1 o)) := by
      unfold receipt1 boolReal
      exact Measurable.ite ((measurableSet_singleton true).preimage (by fun_prop))
        measurable_const measurable_const
    exact measurableSet_le h0 h1
  · intro x d0 d1 y0 y1 hmass
    cases d0 <;> cases d1 <;>
      simp_all [primitiveMass, receipt0, receipt1, boolReal]

/-- Both potential outcomes in the binary completion lie in the unit interval.  Under [the displayed assumptions and inputs](hyp:s,density,mass,hm), [the stated conclusion holds](goal). -/
-- @node: primitivePopulation_outcome_bounds
lemma primitivePopulation_outcome_bounds (s : Bool) (density : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1) :
    ∀ᵐ o ∂primitivePopulation s density mass,
      outcome0 o ∈ Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Icc (0 : ℝ) 1 := by
  apply primitivePopulation_ae_of_atoms s density mass hm
  · unfold outcome0 outcome1
    measurability
  · intro x d0 d1 y0 y1 _
    cases y0 <;> cases y1 <;> norm_num [outcome0, outcome1, boolReal]

/-- The no-defiers property holds for the full source-target component law.  Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_monotonicity
lemma legalIVComponent_monotonicity (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool) :
    Monotonicity (legalIVComponent a n cStar τ sgn) := by
  change ∀ᵐ o ∂(1 / 2 : ℝ≥0∞) •
      primitivePopulation true (fun _ => 1) (lowerMass a n cStar τ sgn) +
      (1 / 2 : ℝ≥0∞) • primitivePopulation false
        (fun x => 1 + tiledPerturbation cStar n sgn x) (lowerMass a n cStar τ sgn),
      boolReal (receipt0 o) ≤ boolReal (receipt1 o)
  rw [ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure
  · exact primitivePopulation_no_defiers true (fun _ => 1)
      (fun _ => actualStrength a n) (tiledPerturbation cStar n sgn)
      (coupledPerturbation cStar τ n sgn)
      (lowerMass_measurable a n cStar τ sgn)
  · exact primitivePopulation_no_defiers false
      (fun x => 1 + tiledPerturbation cStar n sgn x)
      (fun _ => actualStrength a n) (tiledPerturbation cStar n sgn)
      (coupledPerturbation cStar τ n sgn)
      (lowerMass_measurable a n cStar τ sgn)

/-- The baseline center also has no defiers.  Under [the displayed assumptions and inputs](hyp:a,n), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_monotonicity
lemma mixtureCenter_monotonicity (a : ℝ) (n : ℕ) :
    Monotonicity (mixtureCenter a n) := by
  change ∀ᵐ o ∂(1 / 2 : ℝ≥0∞) • primitivePopulation true (fun _ => 1)
      (fun _ => primitiveMass (actualStrength a n) 0 0) +
      (1 / 2 : ℝ≥0∞) • primitivePopulation false (fun _ => 1)
        (fun _ => primitiveMass (actualStrength a n) 0 0),
      boolReal (receipt0 o) ≤ boolReal (receipt1 o)
  rw [ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure
  · exact primitivePopulation_no_defiers true (fun _ => 1)
      (fun _ => actualStrength a n) (fun _ => 0) (fun _ => 0)
      (fun _ _ _ _ => measurable_const)
  · exact primitivePopulation_no_defiers false (fun _ => 1)
      (fun _ => actualStrength a n) (fun _ => 0) (fun _ => 0)
      (fun _ _ _ _ => measurable_const)

/-- Exclusion is built into the component's assignment potential outcomes.  Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_exclusion
lemma legalIVComponent_exclusion (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool) :
    Exclusion (legalIVComponent a n cStar τ sgn) := by
  intro z
  exact Filter.Eventually.of_forall fun _ => rfl

/-- Exclusion is also built into the baseline center.  Under [the displayed assumptions and inputs](hyp:a,n), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_exclusion
lemma mixtureCenter_exclusion (a : ℝ) (n : ℕ) :
    Exclusion (mixtureCenter a n) := by
  intro z
  exact Filter.Eventually.of_forall fun _ => rfl

/-- The component's full-data law retains both potential-outcome bounds.  Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_full_outcome_bounds
lemma legalIVComponent_full_outcome_bounds (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool) :
    ∀ᵐ o ∂(legalIVComponent a n cStar τ sgn).fullLaw,
      outcome0 o ∈ Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Icc (0 : ℝ) 1 := by
  change ∀ᵐ o ∂(1 / 2 : ℝ≥0∞) •
      primitivePopulation true (fun _ => 1) (lowerMass a n cStar τ sgn) +
      (1 / 2 : ℝ≥0∞) • primitivePopulation false
        (fun x => 1 + tiledPerturbation cStar n sgn x) (lowerMass a n cStar τ sgn),
      outcome0 o ∈ Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Icc (0 : ℝ) 1
  rw [ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure
  · exact primitivePopulation_outcome_bounds true (fun _ => 1)
      (lowerMass a n cStar τ sgn) (lowerMass_measurable a n cStar τ sgn)
  · exact primitivePopulation_outcome_bounds false
      (fun x => 1 + tiledPerturbation cStar n sgn x)
      (lowerMass a n cStar τ sgn) (lowerMass_measurable a n cStar τ sgn)

/-- The center's full-data law retains both potential-outcome bounds.  Under [the displayed assumptions and inputs](hyp:a,n), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_full_outcome_bounds
lemma mixtureCenter_full_outcome_bounds (a : ℝ) (n : ℕ) :
    ∀ᵐ o ∂(mixtureCenter a n).fullLaw,
      outcome0 o ∈ Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Icc (0 : ℝ) 1 := by
  change ∀ᵐ o ∂(1 / 2 : ℝ≥0∞) • primitivePopulation true (fun _ => 1)
      (fun _ => primitiveMass (actualStrength a n) 0 0) +
      (1 / 2 : ℝ≥0∞) • primitivePopulation false (fun _ => 1)
        (fun _ => primitiveMass (actualStrength a n) 0 0),
      outcome0 o ∈ Icc (0 : ℝ) 1 ∧ outcome1 o ∈ Icc (0 : ℝ) 1
  rw [ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure
  · exact primitivePopulation_outcome_bounds true (fun _ => 1)
      (fun _ => primitiveMass (actualStrength a n) 0 0)
      (fun _ _ _ _ => measurable_const)
  · exact primitivePopulation_outcome_bounds false (fun _ => 1)
      (fun _ => primitiveMass (actualStrength a n) 0 0)
      (fun _ _ _ _ => measurable_const)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
