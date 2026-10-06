module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.LargeAlphabet.SampleMatching

/-! Actual iid treated-cell collision probabilities for the large-alphabet experiment. -/

public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:d,q,ξ,hd,hq,hq1,x), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_treated_cell_mass
lemma largeAlphabetLaw_treated_cell_mass {d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (x : Fin d) :
    ((largeAlphabetLaw q ξ hd hq hq1).1.map obs).real
      {o | o.A = true ∧ o.X = x} = 1 / (2 * (d : ℝ)) := by
  classical
  rw [measureReal_def, Measure.map_apply (by fun_prop) (by measurability)]
  change (largeAlphabetLaw q ξ hd hq hq1).1.real _ = _
  rw [largeAlphabetLaw_real_event]
  simp [obs, largeAlphabetRecord, completeBernWeight,
    Finset.sum_ite_irrel, Finset.sum_ite_eq']
  ring

/-- Given [the specified inputs and assumptions](hyp:n,d,μ,hd,hm,i,j,hij), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_iid_pair_collision
lemma largeAlphabet_iid_pair_collision {n d : ℕ}
    (μ : Measure (ObsRecord d)) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hm : ∀ x : Fin d, μ.real {o | o.A = true ∧ o.X = x} = 1 / (2 * (d : ℝ)))
    (i j : Fin n) (hij : i ≠ j) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {s | (s i).A = true ∧ (s j).A = true ∧ (s i).X = (s j).X} ≤
      1 / (4 * (d : ℝ)) := by
  classical
  let Q := Measure.pi (fun _ : Fin n => μ)
  let C (x : Fin d) : Set (ObsRecord d) := {o | o.A = true ∧ o.X = x}
  have hind : iIndepFun (fun k : Fin n => fun s : Fin n → ObsRecord d => s k) Q :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have hcoord (k : Fin n) (x : Fin d) : Q.real {s | s k ∈ C x} =
      1 / (2 * (d : ℝ)) := by
    have hp := (measurePreserving_eval (fun _ : Fin n => μ) k).map_eq
    have heq := congrArg (fun ν : Measure (ObsRecord d) => ν.real (C x)) hp
    rw [measureReal_def, Measure.map_apply (by fun_prop) (by measurability)] at heq
    exact heq.trans (hm x)
  have hp (x : Fin d) : Q.real {s | s i ∈ C x ∧ s j ∈ C x} =
      (1 / (2 * (d : ℝ))) ^ 2 := by
    have heq := (hind.indepFun hij).measure_inter_preimage_eq_mul (C x) (C x)
      (by measurability) (by measurability)
    have hr := congrArg ENNReal.toReal heq
    rw [ENNReal.toReal_mul] at hr
    change Q.real {s | s i ∈ C x ∧ s j ∈ C x} =
      Q.real {s | s i ∈ C x} * Q.real {s | s j ∈ C x} at hr
    rw [hcoord, hcoord] at hr
    simpa [pow_two] using hr
  have hcover : {s : Fin n → ObsRecord d | (s i).A = true ∧ (s j).A = true ∧ (s i).X = (s j).X} ⊆
      ⋃ x : Fin d, {s | s i ∈ C x ∧ s j ∈ C x} := by
    intro s hs
    exact mem_iUnion.mpr ⟨(s i).X, ⟨⟨hs.1, rfl⟩, ⟨hs.2.1, hs.2.2.symm⟩⟩⟩
  calc
    Q.real _ ≤ Q.real (⋃ x : Fin d, {s | s i ∈ C x ∧ s j ∈ C x}) :=
      measureReal_mono hcover (measure_ne_top Q _)
    _ ≤ ∑ x : Fin d, Q.real {s | s i ∈ C x ∧ s j ∈ C x} :=
      measureReal_iUnion_fintype_le _
    _ = 1 / (4 * (d : ℝ)) := by
      simp_rw [hp]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
      field_simp
      <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,q,hd,hq,hq1,x), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_treated_cell_mass
lemma largeAlphabetComparisonLaw_treated_cell_mass (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (x : Fin d) :
    ((largeAlphabetComparisonLaw d q hd hq hq1).1.map obs).real
      {o | o.A = true ∧ o.X = x} = 1 / (2 * (d : ℝ)) := by
  classical
  rw [measureReal_def, Measure.map_apply (by fun_prop) (by measurability)]
  change (largeAlphabetComparisonLaw d q hd hq hq1).1.real _ = _
  rw [largeAlphabetComparisonLaw_real_event]
  simp [obs, largeAlphabetComparisonWeight, completeBernWeight,
    largeAlphabetComparisonArrival, Finset.sum_ite_irrel, Finset.sum_ite_eq']
  ring

/-- Given [the specified inputs and assumptions](hyp:n,d,q,ξ,hd,hq,hq1,i,j,hij), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_pair_collision
lemma largeAlphabetLaw_pair_collision {n d : ℕ} (q : ℝ) (ξ : Fin d → Bool)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (i j : Fin n) (hij : i ≠ j) :
    (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)).real
      {s | (s i).A = true ∧ (s j).A = true ∧ (s i).X = (s j).X} ≤
      1 / (4 * (d : ℝ)) := by
  let := (largeAlphabetLaw q ξ hd hq hq1).2
  let : IsProbabilityMeasure ((largeAlphabetLaw q ξ hd hq hq1).1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact largeAlphabet_iid_pair_collision _ hd
    (largeAlphabetLaw_treated_cell_mass q ξ hd hq hq1) i j hij

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hd,hq,hq1,i,j,hij), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_pair_collision
lemma largeAlphabetComparisonLaw_pair_collision {n d : ℕ} (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (i j : Fin n) (hij : i ≠ j) :
    (sampleLaw n (largeAlphabetComparisonLaw d q hd hq hq1)).real
      {s | (s i).A = true ∧ (s j).A = true ∧ (s i).X = (s j).X} ≤
      1 / (4 * (d : ℝ)) := by
  let := (largeAlphabetComparisonLaw d q hd hq hq1).2
  let : IsProbabilityMeasure ((largeAlphabetComparisonLaw d q hd hq hq1).1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact largeAlphabet_iid_pair_collision _ hd
    (largeAlphabetComparisonLaw_treated_cell_mass d q hd hq hq1) i j hij

/-- Given [the specified inputs and assumptions](hyp:n,d,hn,hd), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_collision_budget
lemma largeAlphabet_collision_budget (n d : ℕ) (hn : 1 ≤ n)
    (hd : 1024 * n ^ 2 ≤ d) :
    (n.choose 2 : ℝ) * (1 / (4 * (d : ℝ))) ≤ 1 / 8192 := by
  have hnat : 2 * n.choose 2 ≤ n ^ 2 := by
    rw [Nat.choose_two_right]
    have hm := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    simp only [pow_two]
    omega
  have hc : 2 * (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hnat
  have hdreal : 1024 * (n : ℝ) ^ 2 ≤ d := by exact_mod_cast hd
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hdpos : 0 < (d : ℝ) := by nlinarith
  rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 4 * (d : ℝ))]
  nlinarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,ξ,hn,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetLaw_collision_probability
lemma largeAlphabetLaw_collision_probability (n d : ℕ) (q : ℝ) (ξ : Fin d → Bool)
    (hn : 1 ≤ n) (hd : 1024 * n ^ 2 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    (sampleLaw n (largeAlphabetLaw q ξ (by nlinarith) hq hq1)).real
      {s | ¬ noRepeatedTreatedCell s} ≤ 1 / 8192 := by
  have hdpos : 1 ≤ d := by nlinarith
  let := (largeAlphabetLaw q ξ hdpos hq hq1).2
  let : IsProbabilityMeasure ((largeAlphabetLaw q ξ hdpos hq hq1).1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (sampleLaw n (largeAlphabetLaw q ξ hdpos hq hq1)) := by
    unfold sampleLaw
    infer_instance
  exact (largeAlphabet_collision_union_bound _ (1 / (4 * (d : ℝ)))
    (fun i j hij => largeAlphabetLaw_pair_collision q ξ hdpos hq hq1 i j hij.ne)).trans
    (largeAlphabet_collision_budget n d hn hd)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetComparisonLaw_collision_probability
lemma largeAlphabetComparisonLaw_collision_probability (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1024 * n ^ 2 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    (sampleLaw n (largeAlphabetComparisonLaw d q (by nlinarith) hq hq1)).real
      {s | ¬ noRepeatedTreatedCell s} ≤ 1 / 8192 := by
  have hdpos : 1 ≤ d := by nlinarith
  let := (largeAlphabetComparisonLaw d q hdpos hq hq1).2
  let : IsProbabilityMeasure ((largeAlphabetComparisonLaw d q hdpos hq hq1).1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (sampleLaw n (largeAlphabetComparisonLaw d q hdpos hq hq1)) := by
    unfold sampleLaw
    infer_instance
  exact (largeAlphabet_collision_union_bound _ (1 / (4 * (d : ℝ)))
    (fun i j hij => largeAlphabetComparisonLaw_pair_collision q hdpos hq hq1 i j hij.ne)).trans
    (largeAlphabet_collision_budget n d hn hd)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hd,hq,hq1,E), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetSampleMixture_real_event
lemma largeAlphabetSampleMixture_real_event (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) (E : Set (Fin n → ObsRecord d)) :
    (largeAlphabetSampleMixture n d q hd hq hq1).real E =
      ∫ ξ, (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)).real E
        ∂binaryCellPrior d := by
  classical
  let μ : Measure Bool := (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true
  let : IsProbabilityMeasure μ := fairBinary_probability
  let : IsProbabilityMeasure (binaryCellPrior d) := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin d => μ)))
  let : IsProbabilityMeasure (largeAlphabetSampleMixture n d q hd hq hq1) :=
    largeAlphabetSampleMixture_probability n d q hd hq hq1
  rw [Causalean.Stat.probability_measureReal_eq_tsum_singletons _ E (by measurability),
    tsum_fintype]
  have hterm (s : Fin n → ObsRecord d) :
      E.indicator (fun s => (largeAlphabetSampleMixture n d q hd hq hq1).real {s}) s =
      ∫ ξ, E.indicator (fun s => (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)).real {s}) s
        ∂binaryCellPrior d := by
    by_cases hs : s ∈ E
    · simp only [Set.indicator_of_mem hs, largeAlphabetSampleMixture_real_singleton]
    · simp [Set.indicator_of_notMem hs]
  simp_rw [hterm]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  let := (largeAlphabetLaw q ξ hd hq hq1).2
  let : IsProbabilityMeasure ((largeAlphabetLaw q ξ hd hq hq1).1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)) := by
    unfold sampleLaw
    infer_instance
  rw [Causalean.Stat.probability_measureReal_eq_tsum_singletons _ E (by measurability),
    tsum_fintype]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetSampleMixture_collision_probability
lemma largeAlphabetSampleMixture_collision_probability (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1024 * n ^ 2 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    (largeAlphabetSampleMixture n d q (by nlinarith) hq hq1).real
      {s | ¬ noRepeatedTreatedCell s} ≤ 1 / 8192 := by
  let μ : Measure Bool := (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true
  let : IsProbabilityMeasure μ := fairBinary_probability
  let : IsProbabilityMeasure (binaryCellPrior d) := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin d => μ)))
  rw [largeAlphabetSampleMixture_real_event]
  calc
    _ ≤ ∫ _ξ : Fin d → Bool, (1 / 8192 : ℝ) ∂binaryCellPrior d :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (fun ξ => largeAlphabetLaw_collision_probability n d q ξ hn hd hq hq1)
    _ = 1 / 8192 := by simp

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hq1,κ,T,hT), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_actual_collision_testing
lemma largeAlphabet_actual_collision_testing (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1024 * n ^ 2 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1)
    (κ : BoundedKernel (Fin n → ObsRecord d))
    (T : Set ((Fin n → ObsRecord d) × ℝ)) (hT : MeasurableSet T) :
    1 - (1 / 8192 : ℝ) ≤
      (largeAlphabetSampleMixture n d q (by nlinarith) hq hq1 ⊗ₘ κ.1).real T +
      (sampleLaw n (largeAlphabetComparisonLaw d q (by nlinarith) hq hq1) ⊗ₘ κ.1).real Tᶜ := by
  have hdpos : 1 ≤ d := by nlinarith
  let := (largeAlphabetComparisonLaw d q hdpos hq hq1).2
  let : IsProbabilityMeasure ((largeAlphabetComparisonLaw d q hdpos hq hq1).1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (sampleLaw n (largeAlphabetComparisonLaw d q hdpos hq hq1)) := by
    unfold sampleLaw
    infer_instance
  let : IsProbabilityMeasure (largeAlphabetSampleMixture n d q hdpos hq hq1) :=
    largeAlphabetSampleMixture_probability n d q hdpos hq hq1
  exact largeAlphabet_collision_testing _ _
    (largeAlphabetSampleMixture_matching n d q hdpos hq hq1)
    (largeAlphabetSampleMixture_collision_probability n d q hn hd hq hq1)
    (largeAlphabetComparisonLaw_collision_probability n d q hn hd hq hq1) κ T hT

end CausalSmith.Stat.MarRareqLogfrontier
