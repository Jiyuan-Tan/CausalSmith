module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.BaselineShift
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingSizeTail
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.ResponseMarks
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockSupport

/-!
# Support, target separation, and finite-size tail of the matching prior

The response mark is centered and its energy is controlled by baseline translation.
The matching prior has legal degree-one schedules and the exact signed target.
The finite matching-size tail follows from counting and consecutive size-weight ratios.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- [Multiplication by the balanced density cancels the mark denominator, including at zero.](goal) -/
-- @node: responseMark_mul_density
lemma responseMark_mul_density (δ y : ℝ) :
    responseMark δ y * balancedDensity δ y =
      (baselineDensity (y-δ) - baselineDensity (y+δ))/2 := by
  have ha := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y-δ)
  have hb := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y+δ)
  unfold responseMark
  split_ifs with hg
  · field_simp
    <;> ring
  · have hz : balancedDensity δ y = 0 := le_antisymm (le_of_not_gt hg)
      ((balancedDensity_probability δ).2.1 y)
    have ha0 : baselineDensity (y-δ) = 0 := by
      dsimp [balancedDensity] at hz
      dsimp [baselineDensity]
      linarith
    have hb0 : baselineDensity (y+δ) = 0 := by
      dsimp [balancedDensity] at hz
      dsimp [baselineDensity]
      linarith
    simp [ha0, hb0]

/-- [The two translated unit-mass densities give a centered mark.](goal) -/
-- @node: responseMark_centered
lemma responseMark_centered (δ : ℝ) :
    (∫ y, responseMark δ y * balancedDensity δ y) = 0 := by
  simp_rw [responseMark_mul_density]
  have ha := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized δ
  have hb := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized (-δ)
  simp only [sub_neg_eq_add] at hb
  rw [integral_div, integral_sub ha.1 hb.1, ha.2, hb.2]
  norm_num

/-- [The squared mark density is bounded by the square-root translation discrepancy.](goal) -/
-- @node: responseMark_sq_density_le
lemma responseMark_sq_density_le (δ y : ℝ) :
    responseMark δ y ^ 2 * balancedDensity δ y ≤
      (Real.sqrt (baselineDensity (y-δ)) - Real.sqrt (baselineDensity (y+δ))) ^ 2 := by
  have ha := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y-δ)
  have hb := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y+δ)
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  unfold responseMark
  split_ifs with hg
  · have hden : 0 < 2 * balancedDensity δ y := by positivity
    have hid :
        ((baselineDensity (y-δ) - baselineDensity (y+δ)) / (2 * balancedDensity δ y)) ^ 2 *
          balancedDensity δ y =
        (baselineDensity (y-δ) - baselineDensity (y+δ)) ^ 2 /
          (2 * (baselineDensity (y-δ) + baselineDensity (y+δ))) := by
      dsimp [balancedDensity, baselineDensity] at *
      have hn : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y-δ) +
          CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y+δ) ≠ 0 := by linarith
      field_simp
      <;> ring
    rw [hid]
    apply (div_le_iff₀ (show 0 < 2 * (baselineDensity (y-δ) + baselineDensity (y+δ)) by
      dsimp [balancedDensity, baselineDensity] at *; linarith)).mpr
    dsimp [baselineDensity]
    rw [← hsa, ← hsb]
    rw [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg _)]
    nlinarith only [sq_nonneg ((Real.sqrt (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y-δ)) -
      Real.sqrt (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y+δ))) ^ 2)]
  · simpa using sq_nonneg (Real.sqrt (baselineDensity (y-δ)) - Real.sqrt (baselineDensity (y+δ)))

/-- [Integrating the pointwise comparison and the baseline shift bound controls mark energy.](goal) -/
-- @node: markEnergy_translation_bound
lemma markEnergy_translation_bound (δ : ℝ) : markEnergy δ ≤ 16 * Real.pi^2 * δ^2 := by
  have ha := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized δ
  have hb := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized (-δ)
  simp only [sub_neg_eq_add] at hb
  have hi : Integrable (fun y =>
      (Real.sqrt (baselineDensity (y-δ)) - Real.sqrt (baselineDensity (y+δ))) ^ 2) := by
    apply ((ha.1.add hb.1).const_mul 2).mono' ?_ (Filter.Eventually.of_forall ?_)
    · first | fun_prop | exact ((Real.continuous_sqrt.comp_aestronglyMeasurable ha.1.aestronglyMeasurable).sub
        (Real.continuous_sqrt.comp_aestronglyMeasurable hb.1.aestronglyMeasurable)).pow 2
    · intro y
      have h0 := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y-δ)
      have h1 := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y+δ)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      dsimp [baselineDensity, Pi.add_apply]
      nlinarith [Real.sq_sqrt h0, Real.sq_sqrt h1,
        sq_nonneg (Real.sqrt (baselineDensity (y-δ)) + Real.sqrt (baselineDensity (y+δ)))]
  calc
    markEnergy δ ≤ ∫ y, (Real.sqrt (baselineDensity (y-δ)) - Real.sqrt (baselineDensity (y+δ))) ^ 2 :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y =>
        mul_nonneg (sq_nonneg _) ((balancedDensity_probability δ).2.1 y))) hi
        (Filter.Eventually.of_forall (responseMark_sq_density_le δ))
    _ ≤ 4 * Real.pi^2 * (δ - (-δ))^2 := by
      simpa only [sub_neg_eq_add] using
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.baseline_translation_energy δ (-δ)
    _ = 16 * Real.pi^2 * δ^2 := by ring

/-- Given [the stated assumptions](hyp:hfit), [Distinct donor indices retain their labels in the population.](goal) -/
-- @node: donorOf_injective
lemma donorOf_injective (n m : ℕ) (hfit : 2*m ≤ n) :
    Function.Injective (donorOf n m hfit) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin n => i.val) h

/-- Given [the stated assumptions](hyp:hfit), [Distinct recipient indices retain their labels in the population.](goal) -/
-- @node: recipientOf_injective
lemma recipientOf_injective (n m : ℕ) (hfit : 2*m ≤ n) :
    Function.Injective (recipientOf n m hfit) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change m + a.val = m + b.val at hv
  omega

/-- Given [the stated assumptions](hyp:hfit), [Embedding a candidate edge preserves both of its indices.](goal) -/
-- @node: matching_pair_embedding_injective
lemma matching_pair_embedding_injective (n m : ℕ) (hfit : 2*m ≤ n) :
    Function.Injective (fun e : Fin m × Fin m =>
      (donorOf n m hfit e.1, recipientOf n m hfit e.2)) := by
  intro e e' h
  exact Prod.ext (donorOf_injective n m hfit (congrArg Prod.fst h))
    (recipientOf_injective n m hfit (congrArg Prod.snd h))

/-- Given [the stated assumptions](hyp:hfit), [The embedded matching edges are precisely the schedule's graph arrows.](goal) -/
-- @node: matching_population_edges
lemma matching_population_edges (n m : ℕ) (hfit : 2*m ≤ n) (M : Matching m) :
    Finset.univ.filter (fun e : Fin n × Fin n => matchingEdge n m hfit M e.1 e.2) =
      M.edges.image (fun e => (donorOf n m hfit e.1, recipientOf n m hfit e.2)) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨c, a, hi, hj, hM⟩
    exact ⟨(a,c), by simpa [Matching.edges] using hM, Prod.ext hj.symm hi.symm⟩
  · rintro ⟨⟨a,c⟩, hM, he⟩
    exact ⟨c, a, (congrArg Prod.snd he).symm, (congrArg Prod.fst he).symm,
      (Finset.mem_filter.mp hM).2⟩

/-- Given [the stated assumptions](hyp:hfit), [Summing a constant over all population arrows counts exactly the matching size.](goal) -/
-- @node: matching_arrow_sum
lemma matching_arrow_sum (n m : ℕ) (hfit : 2*m ≤ n) (M : Matching m) (x : ℝ) :
    (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => matchingEdge n m hfit M j i), x) =
      (M.size : ℝ) * x := by
  let E := Finset.univ.filter (fun e : Fin n × Fin n => matchingEdge n m hfit M e.1 e.2)
  have hs := Finset.sum_finset_product_right' E Finset.univ
    (fun i => Finset.univ.filter (fun j => matchingEdge n m hfit M j i))
    (by intro e; simp [E]) (f := fun _ _ => x)
  rw [← hs]
  have hc : E.card = M.size := by
    dsimp [E]
    rw [matching_population_edges, Finset.card_image_of_injective _
      (matching_pair_embedding_injective n m hfit)]
    rfl
  rw [Finset.sum_const, hc, nsmul_eq_mul]

/-- Given [the stated assumptions](hyp:hfit), [Every matched recipient contributes twice the signed amplitude to the causal contrast.](goal) -/
-- @node: balancedSchedule_tte
lemma balancedSchedule_tte (n m : ℕ) (hfit : 2*m ≤ n) (σ : Bool) (δ : ℝ)
    (ξ : PriorParam m) :
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte
      (balancedSchedule n m hfit σ δ ξ) =
      2*CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ*δ*
        (ξ.1.size : ℝ)/n := by
  have hcontrast (i : Fin n) :
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome
        (balancedSchedule n m hfit σ δ ξ) i (fun _ => true) -
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome
        (balancedSchedule n m hfit σ δ ξ) i (fun _ => false) =
      ∑ j ∈ Finset.univ.filter (fun j => matchingEdge n m hfit ξ.1 j i),
        2*CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ*δ := by
    simp [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome,
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.treatment,
      balancedSchedule, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd]
    left
    rfl
  rw [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte]
  simp_rw [hcontrast]
  rw [Fintype.card_fin, matching_arrow_sum]
  ring

/-- Given [the stated assumptions](hyp:hfit), [A recipient of a matching has at most one donor.](goal) -/
-- @node: matching_inDegree_one
lemma matching_inDegree_one (n m : ℕ) (hfit : 2*m ≤ n) (M : Matching m) (i : Fin n) :
    (Finset.univ.filter (fun j => matchingEdge n m hfit M j i)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro j hj j' hj'
  obtain ⟨c,a,hi,hj,ha⟩ := (Finset.mem_filter.mp hj).2
  obtain ⟨c',a',hi',hj',ha'⟩ := (Finset.mem_filter.mp hj').2
  have hc := recipientOf_injective n m hfit (hi.symm.trans hi')
  subst c'
  have haa := Option.some.inj (ha.symm.trans ha')
  subst a'
  exact hj.trans hj'.symm

/-- Given [the stated assumptions](hyp:hfit), [Injectivity of the partial matching bounds every donor's outgoing degree.](goal) -/
-- @node: matching_outDegree_one
lemma matching_outDegree_one (n m : ℕ) (hfit : 2*m ≤ n) (M : Matching m) (j : Fin n) :
    (Finset.univ.filter (fun i => matchingEdge n m hfit M j i)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi i' hi'
  obtain ⟨c,a,hi,hj,ha⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨c',a',hi',hj',ha'⟩ := (Finset.mem_filter.mp hi').2
  have haa := donorOf_injective n m hfit (hj.symm.trans hj')
  subst a'
  have hc := M.2 c c' a ha ha'
  subst c'
  exact hi.trans hi'.symm

/-- Given [the stated assumptions](hyp:hδ,hw), [The absolute sign is one, so either recipient baseline shift costs at most δ.](goal) -/
-- @node: balanced_baseline_shift_bound
lemma balanced_baseline_shift_bound (σ ε : Bool) (δ w : ℝ)
    (hδ : 0 ≤ δ) (hw : |w| ≤ 1/4) :
    |w + δ*CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf ε| ≤ 1/4+δ ∧
    |w - CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ*δ| ≤ 1/4+δ := by
  have hs (s : Bool) : |CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf s| = 1 := by
    cases s <;> norm_num [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf]
  constructor
  · calc
      |w + δ*CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf ε| ≤
        |w| + |δ*CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf ε| := abs_add_le _ _
      _ ≤ 1/4+δ := by rw [abs_mul, hs, abs_of_nonneg hδ]; linarith
  · calc
      |w - CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ*δ| ≤
        |w| + |CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ*δ| := abs_sub _ _
      _ ≤ 1/4+δ := by rw [abs_mul, hs, abs_of_nonneg hδ]; linarith

/-- Given [the stated assumptions](hyp:hfit,hδ,hw), [A row has only its unique recipient baseline, or is identically zero.](goal) -/
-- @node: balancedSchedule_baseline_bound
lemma balancedSchedule_baseline_bound (n m : ℕ) (hfit : 2*m ≤ n) (σ : Bool) (δ : ℝ)
    (ξ : PriorParam m) (hδ : 0 ≤ δ) (hw : ∀ c, |ξ.2.1 c| ≤ 1/4) (i : Fin n) :
    |(balancedSchedule n m hfit σ δ ξ).a i| ≤ 1/4+δ := by
  by_cases hi : ∃ c, i = recipientOf n m hfit c
  · obtain ⟨c,hc⟩ := hi
    have ha : (balancedSchedule n m hfit σ δ ξ).a i =
        if ξ.1.1 c = none then ξ.2.1 c + δ*CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf (ξ.2.2 c)
        else ξ.2.1 c - CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ*δ := by
      dsimp only [balancedSchedule]
      rw [Finset.sum_eq_single c]
      · simp [hc]
      · intro c' _ hne
        have hn : i ≠ recipientOf n m hfit c' := by
          intro he
          exact hne (recipientOf_injective n m hfit (he.symm.trans hc))
        simp [hn]
      · simp
    rw [ha]
    split_ifs
    · exact (balanced_baseline_shift_bound σ (ξ.2.2 c) δ _ hδ (hw c)).1
    · exact (balanced_baseline_shift_bound σ (ξ.2.2 c) δ _ hδ (hw c)).2
  · have ha : (balancedSchedule n m hfit σ δ ξ).a i = 0 := by
      dsimp only [balancedSchedule]
      apply Finset.sum_eq_zero
      intro c _
      simp [show i ≠ recipientOf n m hfit c from fun h => hi ⟨c,h⟩]
    rw [ha, abs_zero]
    linarith

/-- Given [the stated assumptions](hyp:hfit,hδ,hδu,hw), [Baselines in the compact support make the balanced schedule legal with both degrees one.](goal) -/
-- @node: balancedSchedule_mem_class
lemma balancedSchedule_mem_class (n m : ℕ) (hfit : 2*m ≤ n) (σ : Bool) (δ : ℝ)
    (ξ : PriorParam m) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/12)
    (hw : ∀ c, |ξ.2.1 c| ≤ 1/4) :
    ScheduleClass (balancedSchedule n m hfit σ δ ξ) 1 := by
  have hn (i : Fin n) :
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd
        (balancedSchedule n m hfit σ δ ξ) i =
      Finset.univ.filter (fun j => matchingEdge n m hfit ξ.1 j i) := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hn]
    exact matching_inDegree_one n m hfit ξ.1 i
  · intro j
    simp_rw [hn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact matching_outDegree_one n m hfit ξ.1 j
  · intro i
    have ha := balancedSchedule_baseline_bound n m hfit σ δ ξ hδ hw i
    have hs : |2*CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ*δ| = 2*δ := by
      cases σ <;> simp [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf,
        abs_mul, abs_of_nonneg hδ]
    have hdeg := matching_inDegree_one n m hfit ξ.1 i
    change |(balancedSchedule n m hfit σ δ ξ).a i| + |(0 : ℝ)| +
      (∑ j ∈ CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd
        (balancedSchedule n m hfit σ δ ξ) i,
        |2*CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ*δ|) ≤ 1
    rw [hn, hs, Finset.sum_const, nsmul_eq_mul, abs_zero, add_zero]
    have hdegR : ((Finset.univ.filter (fun j => matchingEdge n m hfit ξ.1 j i)).card : ℝ) ≤ 1 := by
      exact_mod_cast hdeg
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hdegR)]

/-- [The independent baseline coordinates remain in their support under the full parameter law.](goal) -/
-- @node: balancedParamLaw_ae_support
lemma balancedParamLaw_ae_support (m : ℕ) :
    ∀ᵐ ξ ∂balancedParamLaw m, ∀ c, |ξ.2.1 c| ≤ (1/4 : ℝ) := by
  have hb := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockBaselineLaw_ae_support m
  have hp : ∀ᵐ p ∂((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.blockBaselineLaw m).prod
      (Measure.pi (fun _ : Fin m => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2)))),
      ∀ c, |p.1 c| ≤ (1/4 : ℝ) := Measure.quasiMeasurePreserving_fst.ae hb
  exact Measure.quasiMeasurePreserving_snd.ae hp

/-- Given [the stated assumptions](hyp:hm), [The threshold is at least four once the matching pool has size 256.](goal) -/
-- @node: kZero_ge_four
lemma kZero_ge_four (m : ℕ) (hm : 256 ≤ m) : 4 ≤ kZero m := by
  dsimp [kZero]
  omega

/-- Given [the stated assumptions](hyp:hm), [The threshold retains at least one half of its unrounded scale.](goal) -/
-- @node: kZero_ge_pool_fraction
lemma kZero_ge_pool_fraction (m : ℕ) (hm : 256 ≤ m) :
    (m : ℝ) / 128 ≤ kZero m := by
  have hround : m ≤ 128 * kZero m := by
    dsimp [kZero]
    omega
  have hcast : (m : ℝ) ≤ 128 * (kZero m : ℝ) := by exact_mod_cast hround
  linarith

/-- Given [the stated assumptions](hyp:hm), [Exponent monotonicity turns the threshold lower bound into the numerical tail bound.](goal) -/
-- @node: kZero_geometric_tail_le
lemma kZero_geometric_tail_le (m : ℕ) (hm : 256 ≤ m) :
    (4 : ℝ)⁻¹ ^ kZero m ≤ 1 / 256 := by
  calc
    (4 : ℝ)⁻¹ ^ kZero m ≤ (4 : ℝ)⁻¹ ^ 4 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (kZero_ge_four m hm)
    _ = 1 / 256 := by norm_num

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hm,hfit,hδ,hδu), [The balanced prior has degree-one supported schedules, exact causal target,
centered marks, bounded mark energy, and the stated finite matching-size tail.](goal) -/
-- @node: lem:matching-support
lemma matching_support (n m d : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n-1)
    (hm : 1 ≤ m) (hfit : 2*m ≤ n) (σ : Bool) (δ : ℝ) (hδ : 0 < δ) (hδu : δ ≤ 1/12) : -- @realizes delta(real amplitude with 0<δ≤1/12)
    (∀ᵐ ξ ∂balancedParamLaw m,
      ScheduleClass (balancedSchedule n m hfit σ δ ξ) d ∧
      ScheduleClass (balancedSchedule n m hfit σ δ ξ) 1 ∧
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (balancedSchedule n m hfit σ δ ξ) =
        2*CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ*δ*(ξ.1.size : ℝ)/n) ∧
    (∫ y, responseMark δ y * balancedDensity δ y) = 0 ∧
    markEnergy δ ≤ 16*Real.pi^2*δ^2 ∧
    (256 ≤ m → (matchingPrior m).real {M | M.size < kZero m} ≤ (4 : ℝ)⁻¹ ^ kZero m ∧
      (4 : ℝ)⁻¹ ^ kZero m ≤ 1/256 ∧ (m : ℝ)/128 ≤ kZero m) := by
  refine ⟨?_, responseMark_centered δ, markEnergy_translation_bound δ, ?_⟩
  · filter_upwards [balancedParamLaw_ae_support m] with ξ hξ
    have hc := balancedSchedule_mem_class n m hfit σ δ ξ hδ.le hδu hξ
    exact ⟨hc.mono hd, hc, balancedSchedule_tte n m hfit σ δ ξ⟩
  · intro hm256
    refine ⟨?_, kZero_geometric_tail_le m hm256, kZero_ge_pool_fraction m hm256⟩
    exact matchingPrior_size_tail_bound m hm256

end CausalSmith.Experimentation.NoisygraphTtePrecision
