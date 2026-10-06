module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.LargeAlphabet.ComparisonLaw
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.LargeAlphabet.CollisionTV
public import Mathlib.Probability.Independence.Integration

/-! Independence of distinct treated prior coordinates and sample-atom matching. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:ι,d,x,hx,f), [the stated mathematical conclusion holds](goal). -/
-- @node: binaryCellPrior_integral_distinct_prod
lemma binaryCellPrior_integral_distinct_prod {ι : Type*} [Fintype ι]
    {d : ℕ} (x : ι → Fin d) (hx : Function.Injective x) (f : ι → Bool → ℝ) :
    (∫ ξ, ∏ i, f i (ξ (x i)) ∂binaryCellPrior d) =
      ∏ i, (f i false + f i true) / 2 := by
  let μ : Measure Bool := (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true
  let : IsProbabilityMeasure μ := fairBinary_probability
  have hi : iIndepFun (fun j : Fin d => fun ξ : Fin d → Bool => ξ j)
      (binaryCellPrior d) := iIndepFun_pi (fun _ => aemeasurable_id)
  have hprod := (hi.precomp hx).integral_fun_prod_comp
    (f := f) (fun i => (measurable_pi_apply (x i)).aemeasurable)
    (fun _ => by fun_prop)
  rw [hprod]
  apply Finset.prod_congr rfl
  intro i _
  change (∫ ξ, f i (ξ (x i)) ∂Measure.pi (fun _ : Fin d => μ)) = _
  have hp := measurePreserving_eval (fun _ : Fin d => μ) (x i)
  rw [← integral_map hp.measurable.aemeasurable (by fun_prop), hp.map_eq]
  exact fairBinary_integral (f i)

/-- Given [the specified inputs and assumptions](hyp:ι,d,p,x,f,hx,hc), [the stated mathematical conclusion holds](goal). -/
-- @node: binaryCellPrior_integral_partial_distinct_prod
lemma binaryCellPrior_integral_partial_distinct_prod {ι : Type*} [Fintype ι]
    {d : ℕ} (p : ι → Prop) (x : ι → Fin d) (f : ι → Bool → ℝ)
    (hx : Function.Injective (fun i : {i // p i} => x i))
    (hc : ∀ i, ¬ p i → f i true = f i false) :
    (∫ ξ, ∏ i, f i (ξ (x i)) ∂binaryCellPrior d) =
      ∏ i, (f i false + f i true) / 2 := by
  classical
  let μ : Measure Bool := (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true
  let : IsProbabilityMeasure μ := fairBinary_probability
  let : IsProbabilityMeasure (binaryCellPrior d) := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin d => μ)))
  have hconst (ξ : Fin d → Bool) (i : {i // ¬ p i}) :
      f i (ξ (x i)) = f i false := by
    cases ξ (x i)
    · rfl
    · exact hc i i.property
  have heq : (fun ξ : Fin d → Bool => ∏ i, f i (ξ (x i))) =
      (fun ξ => (∏ i : {i // p i}, f i (ξ (x i))) *
        (∏ i : {i // ¬ p i}, f i false)) := by
    funext ξ
    rw [← Fintype.prod_subtype_mul_prod_subtype p]
    simp_rw [hconst]
  rw [heq, integral_mul_const,
    binaryCellPrior_integral_distinct_prod (fun i : {i // p i} => x i) hx]
  rw [← Fintype.prod_subtype_mul_prod_subtype p]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hc i i.property]
  ring

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1,o), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_atom_coordinate
lemma largeAlphabetLaw_atom_coordinate {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (o : ObsRecord d) :
    ((largeAlphabetLaw q ξ hd hq hq1).1.map obs).real {o} =
      ((largeAlphabetLaw q (fun _ : Fin d => ξ o.X) hd hq hq1).1.map obs).real {o} := by
  simp only [largeAlphabetLaw_observed_atom, largeAlphabetArrival]

/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1,o,ha), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_control_atom_constant
lemma largeAlphabetLaw_control_atom_constant {d : ℕ} (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (o : ObsRecord d)
    (ha : o.A ≠ true) :
    ((largeAlphabetLaw q (fun _ : Fin d => true) hd hq hq1).1.map obs).real {o} =
      ((largeAlphabetLaw q (fun _ : Fin d => false) hd hq hq1).1.map obs).real {o} := by
  have hf : o.A = false := Bool.eq_false_iff.mpr ha
  simp only [largeAlphabetLaw_observed_atom, largeAlphabetArrival, hf,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false]

/-- Given [the specified inputs and assumptions](hyp:n,d,P,s), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_sample_atom_prod
lemma largeAlphabet_sample_atom_prod {n d : ℕ} (P : FullLaw d)
    (s : Fin n → ObsRecord d) :
    (sampleLaw n P).real {s} = ∏ i, (P.1.map obs).real {s i} := by
  let := P.2
  rw [sampleLaw, Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hd,hq,hq1,s,hs), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_sample_atom_matching
lemma largeAlphabet_sample_atom_matching {n d : ℕ} (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (s : Fin n → ObsRecord d)
    (hs : noRepeatedTreatedCell s) :
    (∫ ξ, (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)).real {s}
      ∂binaryCellPrior d) =
      (sampleLaw n (largeAlphabetComparisonLaw d q hd hq hq1)).real {s} := by
  classical
  simp_rw [largeAlphabet_sample_atom_prod, largeAlphabetLaw_atom_coordinate]
  rw [binaryCellPrior_integral_partial_distinct_prod
    (fun i => (s i).A = true) (fun i => (s i).X)
    (fun i b => ((largeAlphabetLaw q (fun _ : Fin d => b) hd hq hq1).1.map obs).real {s i})]
  · apply Finset.prod_congr rfl
    intro i _
    simpa only [fairBinary_integral] using
      largeAlphabet_one_visit_matching d q hd hq hq1 (s i)
  · intro i j hij
    apply Subtype.ext
    by_contra hne
    exact hs i j hne i.property j.property hij
  · intro i hi
    exact largeAlphabetLaw_control_atom_constant q hd hq hq1 (s i) hi

/-- For [the specified inputs and assumptions](hyp:n,d,q,hd,hq,hq1), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: largeAlphabetSampleMixture
noncomputable def largeAlphabetSampleMixture (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    Measure (Fin n → ObsRecord d) :=
  ∑ s, ENNReal.ofReal (∫ ξ,
    (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)).real {s}
      ∂binaryCellPrior d) • Measure.dirac s

-- @node: largeAlphabetSampleMixture_real_singleton
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hd,hq,hq1,s), [the stated mathematical conclusion holds](goal). -/
lemma largeAlphabetSampleMixture_real_singleton (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (s : Fin n → ObsRecord d) :
    (largeAlphabetSampleMixture n d q hd hq hq1).real {s} =
      ∫ ξ, (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)).real {s}
        ∂binaryCellPrior d := by
  classical
  unfold largeAlphabetSampleMixture Measure.real
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun _ => measureReal_nonneg))

-- @node: largeAlphabetSampleMixture_probability
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
lemma largeAlphabetSampleMixture_probability (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    IsProbabilityMeasure (largeAlphabetSampleMixture n d q hd hq hq1) := by
  classical
  let μ : Measure Bool := (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true
  let : IsProbabilityMeasure μ := fairBinary_probability
  let : IsProbabilityMeasure (binaryCellPrior d) := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin d => μ)))
  have hsum : (∑ s : Fin n → ObsRecord d,
      ∫ ξ, (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)).real {s}
        ∂binaryCellPrior d) = 1 := by
    rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    have hnorm (ξ : Fin d → Bool) :
        (∑ s : Fin n → ObsRecord d,
          (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)).real {s}) = 1 := by
      let := (largeAlphabetLaw q ξ hd hq hq1).2
      let : IsProbabilityMeasure ((largeAlphabetLaw q ξ hd hq hq1).1.map obs) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      let : IsProbabilityMeasure (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)) := by
        unfold sampleLaw
        infer_instance
      rw [sum_measureReal_singleton]
      simp
    simp_rw [hnorm]
    simp
  constructor
  unfold largeAlphabetSampleMixture
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun _ _ => integral_nonneg (fun _ => measureReal_nonneg)), hsum]
  simp

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hd,hq,hq1,s,hs), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetSampleMixture_matching
lemma largeAlphabetSampleMixture_matching (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (s : Fin n → ObsRecord d)
    (hs : noRepeatedTreatedCell s) :
    (largeAlphabetSampleMixture n d q hd hq hq1).real {s} =
      (sampleLaw n (largeAlphabetComparisonLaw d q hd hq hq1)).real {s} := by
  rw [largeAlphabetSampleMixture_real_singleton]
  exact largeAlphabet_sample_atom_matching q hd hq hq1 s hs

end CausalSmith.Stat.MarRareqLogfrontier
