module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.ObservedArm

/-! # Assignment and transport conditions of the mixture components and center

The finite primitive populations give the same conditional complier margins
in both populations. Their assignment kernels satisfy randomization and
consistency, completing the law-level clauses in roadmap (13)--(18).
-/

public section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Either center population is the corresponding normalized primitive population.  Under [the displayed assumptions and inputs](hyp:a,n,hb,s), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_populationLaw_eq_primitive
lemma mixtureCenter_populationLaw_eq_primitive (a : ℝ) (n : ℕ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) (s : Bool) :
    populationLaw (mixtureCenter a n) s = primitivePopulation s (fun _ => 1)
      (fun _ => primitiveMass (actualStrength a n) 0 0) := by
  let mass : ℝ → Bool → Bool → Bool → Bool → ℝ :=
    fun _ => primitiveMass (actualStrength a n) 0 0
  have hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1 :=
    fun _ _ _ _ => measurable_const
  have hm0 : ∀ x d0 d1 y0 y1, 0 ≤ mass x d0 d1 y0 y1 := by
    intro x d0 d1 y0 y1
    exact primitiveMass_nonneg_of_bounds (actualStrength a n) 0 0 hb
      (by norm_num) (by norm_num) (by nlinarith [hb.1]) d0 d1 y0 y1
  have hsum (x : ℝ) : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1 :=
    primitiveMass_sum (actualStrength a n) 0 0 (ne_of_gt hb.1) (by norm_num)
  have hu (t : Bool) : primitivePopulation t (fun _ => 1) mass univ = 1 := by
    rw [primitivePopulation_univ t _ mass hm hm0 hsum]
    simp [covariateSpace]
  unfold populationLaw mixtureCenter lawFromMass
  dsimp
  cases s
  · apply cond_half_supported_mixture_event
    · unfold population; measurability
    · simpa using primitivePopulation_population_event true false (fun _ => 1) mass hm
    · simpa using (primitivePopulation_population_event false false (fun _ => 1) mass hm).trans
        (by simpa using hu false)
    · exact hu false
  · rw [add_comm]
    apply cond_half_supported_mixture_event
    · unfold population; measurability
    · simpa using primitivePopulation_population_event false true (fun _ => 1) mass hm
    · simpa using (primitivePopulation_population_event true true (fun _ => 1) mass hm).trans
        (by simpa using hu true)
    · exact hu true

/-- The component assignment realizes randomized encouragement and consistent records. Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn,hb,hAdm,hn,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_assignment_conditions
lemma legalIVComponent_assignment_conditions (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1) (hn : 0 < n) :
    ReceiptConsistency (legalIVComponent a n cStar τ sgn) ∧
    OutcomeConsistency (legalIVComponent a n cStar τ sgn) ∧
    InstrumentRandomization (legalIVComponent a n cStar τ sgn) := by
  apply lawFromMass_assignment_conditions
  · exact lowerMass_measurable a n cStar τ sgn
  · exact lowerMass_nonneg a n cStar τ sgn hb hAdm hτ
  · intro x
    apply primitiveMass_sum _ _ _ (ne_of_gt hb.1)
    have hu := (tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le).trans hAdm.2.1
    nlinarith [sq_abs (tiledPerturbation cStar n sgn x),
      abs_nonneg (tiledPerturbation cStar n sgn x)]
  · simp [covariateSpace]
  · exact measurable_const.add (tiledPerturbation_measurable cStar n sgn)
  · intro x
    exact lowerAssignmentWeight_mem_Icc a n cStar τ sgn hAdm x true
  · simpa only [legalIVComponent, if_true] using
      legalIVComponent_populationLaw_eq_primitive a n cStar τ sgn hb hAdm hτ hn true

/-- The center assignment also realizes the model's consistency and randomization clauses.  Under [the displayed assumptions and inputs](hyp:a,n,hb), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_assignment_conditions
lemma mixtureCenter_assignment_conditions (a : ℝ) (n : ℕ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) :
    ReceiptConsistency (mixtureCenter a n) ∧ OutcomeConsistency (mixtureCenter a n) ∧
    InstrumentRandomization (mixtureCenter a n) := by
  apply lawFromMass_assignment_conditions
  · exact fun _ _ _ _ => measurable_const
  · intro x d0 d1 y0 y1
    exact primitiveMass_nonneg_of_bounds (actualStrength a n) 0 0 hb
      (by norm_num) (by norm_num) (by nlinarith [hb.1]) d0 d1 y0 y1
  · intro x
    exact primitiveMass_sum (actualStrength a n) 0 0 (ne_of_gt hb.1) (by norm_num)
  · simp [covariateSpace]
  · exact measurable_const
  · intro x; norm_num
  · exact mixtureCenter_populationLaw_eq_primitive a n hb true

/-- A bounded finite primitive mean gives the center's conditional mean in either population.  Under [the displayed assumptions and inputs](hyp:a,n,hb,s,f,hf,bound,hbound,q,hq,hmean), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_conditionalMean_of_pointwise
lemma mixtureCenter_conditionalMean_of_pointwise (a : ℝ) (n : ℕ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (s : Bool) (f : FullData → ℝ) (hf : Measurable f) (bound : ℝ)
    (hbound : ∀ x d0 d1 y0 y1, ‖f (s, x, d0, d1, boolReal y0, boolReal y1)‖ ≤ bound)
    (q : ℝ → ℝ) (hq : Measurable q)
    (hmean : ∀ x, (∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      primitiveMass (actualStrength a n) 0 0 d0 d1 y0 y1 *
        f (s, x, d0, d1, boolReal y0, boolReal y1)) = q x) :
    ConditionalMean (mixtureCenter a n) s f q := by
  let mass : ℝ → Bool → Bool → Bool → Bool → ℝ :=
    fun _ => primitiveMass (actualStrength a n) 0 0
  have hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1 :=
    fun _ _ _ _ => measurable_const
  have hm0 : ∀ x d0 d1 y0 y1, 0 ≤ mass x d0 d1 y0 y1 := by
    intro x d0 d1 y0 y1
    exact primitiveMass_nonneg_of_bounds (actualStrength a n) 0 0 hb
      (by norm_num) (by norm_num) (by nlinarith [hb.1]) d0 d1 y0 y1
  have hsum (x : ℝ) : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1 :=
    primitiveMass_sum (actualStrength a n) 0 0 (ne_of_gt hb.1) (by norm_num)
  have : IsFiniteMeasure ((volume.restrict covariateSpace).withDensity
      (fun _ => ENNReal.ofReal (1 : ℝ))) := by
    simp only [ENNReal.ofReal_one]
    rw [show (fun _ : ℝ => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one]
    change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)); infer_instance
  refine ⟨hq, ?_⟩
  intro B hB
  rw [mixtureCenter_populationLaw_eq_primitive a n hb s,
    map_covariate_primitivePopulation s (fun _ => 1) mass measurable_const hm hm0 hsum,
    primitivePopulation_setIntegral s (fun _ => 1) mass hm hm0 hsum f hf bound hbound B hB]
  apply setIntegral_congr_fun hB
  exact fun x _ => hmean x

/-- Both center populations have the same constant share and zero weighted outcome margins.  Under [the displayed assumptions and inputs](hyp:a,n,hb,s), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_conditional_complier_margins
lemma mixtureCenter_conditional_complier_margins (a : ℝ) (n : ℕ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) (s : Bool) :
    ConditionalMean (mixtureCenter a n) s complier (fun _ => actualStrength a n) ∧
    ConditionalMean (mixtureCenter a n) s
      (fun o => (outcome1 o - outcome0 o) * complier o) (fun _ => 0) := by
  have hm : Measurable complier := by
    have hset : MeasurableSet {o : FullData | receipt1 o = true ∧ receipt0 o = false} :=
      (measurableSet_eq_fun (by unfold receipt1; fun_prop) measurable_const).inter
        (measurableSet_eq_fun (by unfold receipt0; fun_prop) measurable_const)
    convert (measurable_const : Measurable (fun _ : FullData => (1 : ℝ))).ite hset
      (measurable_const : Measurable (fun _ : FullData => (0 : ℝ))) using 1
    · funext o; simp [complier]
    · infer_instance
  have hy : Measurable (fun o : FullData => (outcome1 o - outcome0 o) * complier o) := by
    unfold outcome1 outcome0
    fun_prop
  constructor
  · apply mixtureCenter_conditionalMean_of_pointwise a n hb s complier hm 1
    · intro x d0 d1 y0 y1
      cases d0 <;> cases d1 <;> norm_num [complier, receipt0, receipt1]
    · exact measurable_const
    · intro x
      simpa [complier, receipt0, receipt1] using
        primitiveMass_complier_sum (actualStrength a n) 0 0 (ne_of_gt hb.1)
  · apply mixtureCenter_conditionalMean_of_pointwise a n hb s _ hy 1
    · intro x d0 d1 y0 y1
      cases d0 <;> cases d1 <;> cases y0 <;> cases y1 <;>
        norm_num [complier, receipt0, receipt1, outcome0, outcome1, boolReal]
    · exact measurable_const
    · intro x
      simpa [complier, receipt0, receipt1, outcome0, outcome1] using
        primitiveMass_complier_outcome_sum (actualStrength a n) 0 0 (ne_of_gt hb.1)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
