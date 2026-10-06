module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationMoments

/-!
# Population averages over the two roles

Finite role counts, integrability of localized treatment features, and exact
expectations of the independent rectangular role products.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Localization weights a covariate feature and its treatment bit.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input f](hyp:f), [the specified input z](hyp:z), [weighted treatment feature](goal) is the corresponding construction. -/
def weightedTreatmentFeature {d : ℕ} (h : ℝ) (f : Cov d → ℝ)
    (z : Cov d × Bool) : ℝ := locWeight h z.1 * f z.1 * bit z.2

/-- Given [bandwidth h](hyp:h) and [a Borel covariate feature f](hyp:hf), [the localized treatment feature is Borel](goal). -/
@[fun_prop] lemma measurable_weightedTreatmentFeature {d : ℕ} (h : ℝ)
    (f : Cov d → ℝ) (hf : Measurable f) : Measurable (weightedTreatmentFeature h f) := by
  unfold weightedTreatmentFeature
  have hb : Measurable bit := measurable_of_finite bit
  fun_prop

/-- A localized feature inherits a global bound from its bound on the localization box.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input f](hyp:f), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hfB](hyp:hfB), [the specified input z](hyp:z), [the weighted treatment feature norm bound conclusion](goal) holds. -/
lemma weightedTreatmentFeature_norm_bound {d : ℕ} (h : ℝ) (hh : 0 < h)
    (f : Cov d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ x ∈ locCube d h, ‖f x‖ ≤ B) (z : Cov d × Bool) :
    ‖weightedTreatmentFeature h f z‖ ≤ h^(-(d:ℝ)) * B := by
  rcases z with ⟨x, a⟩
  cases a
  · simp only [weightedTreatmentFeature, bit, Bool.false_eq_true, if_false, mul_zero, norm_zero]
    positivity
  · simpa only [weightedTreatmentFeature, bit, if_true, mul_one] using
      locWeight_mul_norm_bound h hh f B hB hfB x

/-- For [record position i](hyp:i), [evaluating the concatenated treatment record at i is Borel](goal). -/
@[fun_prop] lemma measurable_treatmentRecord_eval {d n m : ℕ} (i : Fin (n+m)) :
    Measurable (fun D : Dataset d n m => treatmentRecords D i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [treatmentRecords, Fin.addCases_left]
    fun_prop
  · simp only [treatmentRecords, Fin.addCases_right]
    fun_prop

/-- Bounded Borel statistics are integrable under a probability measure.  Given [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the population integrable bounded conclusion](goal) holds. -/
lemma population_integrable_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) : Integrable f μ := by
  exact (integrable_const B).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hB)

/-- The outcome and treatment roles have their prescribed cardinalities.  Given [the specified input n](hyp:n), [the specified input m](hyp:m), [the population role cardinalities conclusion](goal) holds. -/
lemma population_role_cardinalities (n m : ℕ) :
    (roleSplit n m).1.card = outcomeCount n ∧
    (roleSplit n m).2.card = treatmentCount n m := by
  classical
  have hl : n/2 ≤ n := Nat.div_le_self n 2
  have ht : n/2 ≤ n+m := by omega
  constructor
  · simpa only [roleSplit, outcomeCount, Fin.card_filter_val_lt, min_eq_right hl]
  · have heq : (roleSplit n m).2 =
        Finset.univ \ (Finset.univ.filter (fun i : Fin (n+m) => i.val < n/2)) := by
      ext i
      simp [roleSplit]
    rw [heq, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin, Fin.card_filter_val_lt, min_eq_right ht]
    rfl

/-- Both role counts are strictly positive whenever there are at least two labeled records.  Given [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the population role counts pos conclusion](goal) holds. -/
lemma population_role_counts_pos (n m : ℕ) (hn : 2 ≤ n) :
    0 < outcomeCount n ∧ 0 < treatmentCount n m := by
  unfold outcomeCount treatmentCount
  omega

/-- Averaging the labeled outcome-role treatment features preserves their population mean.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input hn](hyp:hn), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hfB](hyp:hfB), [the population outcome role mean conclusion](goal) holds. -/
lemma population_outcome_role_mean {d n m : ℕ} (P : PrimitiveLaw d) (hn : 2 ≤ n)
    (f : Cov d × Bool → ℝ) (hf : Measurable f) (B : ℝ) (hfB : ∀ z, ‖f z‖ ≤ B) :
    (∫ w : Sample d n m, (outcomeCount n : ℝ)⁻¹ *
      ∑ j ∈ (roleSplit n m).1, f ((w.1.1 j).1, (w.1.1 j).2.1) ∂experiment P n m) =
      ∫ z, f z ∂xaLaw P := by
  classical
  letI := population_experiment_probability P n m
  have hi (j : Fin n) : Integrable
      (fun w : Sample d n m => f ((w.1.1 j).1, (w.1.1 j).2.1)) (experiment P n m) :=
    population_integrable_bounded _ _ (hf.comp (by fun_prop)) B (fun w => hfB _)
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)]
  simp_rw [experiment_labeled_treatment_integral P f hf]
  simp only [Finset.sum_const, nsmul_eq_mul, (population_role_cardinalities n m).1]
  have hn0 : (outcomeCount n : ℝ) ≠ 0 := by
    exact_mod_cast (population_role_counts_pos n m hn).1.ne'
  field_simp

/-- Independent rectangular averaging gives the product of the two marginal means.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input hn](hyp:hn), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input hfB](hyp:hfB), [the specified input hgC](hyp:hgC), [the population rectangular role mean conclusion](goal) holds. -/
lemma population_rectangular_role_mean {d n m : ℕ} (P : PrimitiveLaw d) (hn : 2 ≤ n)
    (f g : Cov d × Bool → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hfB : ∀ z, ‖f z‖ ≤ B) (hgC : ∀ z, ‖g z‖ ≤ C) :
    (∫ w : Sample d n m, ((treatmentCount n m : ℝ)*(outcomeCount n : ℝ))⁻¹ *
      ∑ i ∈ (roleSplit n m).2, ∑ j ∈ (roleSplit n m).1,
        f (treatmentRecords w.1 i) * g ((w.1.1 j).1, (w.1.1 j).2.1) ∂experiment P n m) =
      (∫ z, f z ∂xaLaw P) * (∫ z, g z ∂xaLaw P) := by
  classical
  letI := population_experiment_probability P n m
  have hi (i : Fin (n+m)) (j : Fin n) : Integrable
      (fun w : Sample d n m => f (treatmentRecords w.1 i) *
        g ((w.1.1 j).1, (w.1.1 j).2.1)) (experiment P n m) := by
    apply population_integrable_bounded _ _ (by fun_prop) (B*C)
    intro w
    rw [norm_mul]
    exact mul_le_mul (hfB _) (hgC _) (norm_nonneg _) ((norm_nonneg (f (treatmentRecords w.1 i))).trans (hfB _))
  rw [integral_const_mul, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hi i j))]
  have hcount : ((treatmentCount n m : ℝ)*(outcomeCount n : ℝ))⁻¹ *
      (∑ i ∈ (roleSplit n m).2, ∑ j ∈ (roleSplit n m).1,
        (∫ z, f z ∂xaLaw P) * (∫ z, g z ∂xaLaw P)) =
      (∫ z, f z ∂xaLaw P) * (∫ z, g z ∂xaLaw P) := by
    simp only [Finset.sum_const, nsmul_eq_mul, (population_role_cardinalities n m).1,
      (population_role_cardinalities n m).2]
    have hn0 : (outcomeCount n : ℝ) ≠ 0 := by exact_mod_cast (population_role_counts_pos n m hn).1.ne'
    have ht0 : (treatmentCount n m : ℝ) ≠ 0 := by exact_mod_cast (population_role_counts_pos n m hn).2.ne'
    field_simp
  apply Eq.trans ?_ hcount
  congr 1
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j hj'
  exact experiment_role_product_integral P f g hf hg i j hi' hj'

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
