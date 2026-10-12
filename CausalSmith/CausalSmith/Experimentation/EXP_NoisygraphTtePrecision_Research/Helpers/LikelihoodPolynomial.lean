module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.PosteriorImageDecomposition
public import Mathlib.MeasureTheory.Integral.Pi
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingSupport

/-!
# Finite donor-image likelihood expansion

Expand each matching product over its arrow subsets, then group by the recipient
set and its collective donor image, as in the marked-contraction proof. Centered
recipient marks and fair donor signs then give full-reference orthogonality.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- [Recipient projection is injective on the arrows of a matching.](goal) -/
-- @node: matching_edges_snd_injOn
lemma matching_edges_snd_injOn {m : ℕ} (M : Matching m) :
    Set.InjOn Prod.snd (M.edges : Set (Fin m × Fin m)) := by
  intro e he e' he' h
  apply Prod.ext _ h
  exact Option.some.inj (((Finset.mem_filter.mp he).2).symm.trans
    (h ▸ (Finset.mem_filter.mp he').2))

/-- [Donor projection is injective on the arrows of a matching.](goal) -/
-- @node: matching_edges_fst_injOn
lemma matching_edges_fst_injOn {m : ℕ} (M : Matching m) :
    Set.InjOn Prod.fst (M.edges : Set (Fin m × Fin m)) := by
  intro e he e' he' h
  apply Prod.ext h
  exact M.2 _ _ _ (Finset.mem_filter.mp he).2
    (h ▸ (Finset.mem_filter.mp he').2)

/-- [All selected recipients are matched precisely when they lie in the matched set.](goal) -/
-- @node: matching_selected_iff_subset
lemma matching_selected_iff_subset {m : ℕ} (M : Matching m) (S : Finset (Fin m)) :
    (∀ c ∈ S, ∃ a, M.1 c = some a) ↔ S ⊆ matchingRecipients M := by
  constructor
  · intro h c hc
    obtain ⟨a, ha⟩ := h c hc
    simp [matchingRecipients, ha]
  · intro h c hc
    have hs := (Finset.mem_filter.mp (h hc)).2
    cases ha : M.1 c with
    | none => simp [ha] at hs
    | some a => exact ⟨a, rfl⟩

/-- Given [the stated assumptions](hyp:hS), [Restricting to a matched recipient subset recovers that subset under projection.](goal) -/
-- @node: matching_selected_edges_image
lemma matching_selected_edges_image {m : ℕ} (M : Matching m) (S : Finset (Fin m))
    (hS : S ⊆ matchingRecipients M) :
    (M.edges.filter (fun e => e.2 ∈ S)).image Prod.snd = S := by
  ext c
  constructor
  · intro hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_filter.mp he).2
  · intro hc
    obtain ⟨a, ha⟩ := (matching_selected_iff_subset M S).mpr hS c hc
    exact Finset.mem_image.mpr ⟨(a,c), by simp [Matching.edges, ha, hc], rfl⟩

/-- Given [the stated assumptions](hyp:hT), [An arrow subset is uniquely recovered from its recipient projection.](goal) -/
-- @node: matching_edgeSubset_recover
lemma matching_edgeSubset_recover {m : ℕ} (M : Matching m)
    (T : Finset (Fin m × Fin m)) (hT : T ⊆ M.edges) :
    M.edges.filter (fun e => e.2 ∈ T.image Prod.snd) = T := by
  ext e
  constructor
  · intro he
    obtain ⟨heM, heS⟩ := Finset.mem_filter.mp he
    obtain ⟨e', he', h⟩ := Finset.mem_image.mp heS
    have heq : e' = e := matching_edges_snd_injOn M (hT he') heM h
    exact heq ▸ he'
  · intro he
    exact Finset.mem_filter.mpr ⟨hT he, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩

/-- Given [the stated assumptions](hyp:h), [The two projected sets of a selected matching have equal cardinality.](goal) -/
-- @node: imageEvent_card_eq
lemma imageEvent_card_eq {m : ℕ} (M : Matching m) (S J : Finset (Fin m))
    (h : ImageEvent M S J) : J.card = S.card := by
  let T := M.edges.filter (fun e => e.2 ∈ S)
  have ht : T ⊆ M.edges := Finset.filter_subset _ _
  have hi : T.image Prod.snd = S :=
    matching_selected_edges_image M S ((matching_selected_iff_subset M S).mp h.1)
  have hj : T.image Prod.fst = J := h.2
  rw [← hj, Finset.card_image_of_injOn (fun _ he _ he' heq =>
    matching_edges_fst_injOn M (ht he) (ht he') heq), ← hi,
    Finset.card_image_of_injOn (fun _ he _ he' heq =>
      matching_edges_snd_injOn M (ht he) (ht he') heq)]

/-- Given [the stated assumptions](hyp:hS), [Selected-arrow products factor into recipient marks and collective donor signs.](goal) -/
-- @node: matching_selected_product
lemma matching_selected_product {m : ℕ} (M : Matching m) (S : Finset (Fin m))
    (hS : S ⊆ matchingRecipients M) (s : ℝ) (a b : Fin m → ℝ) :
    (∏ e ∈ M.edges.filter (fun e => e.2 ∈ S), s * a e.2 * b e.1) =
      s ^ S.card * (∏ c ∈ S, a c) * ∏ j ∈ donorImage M S, b j := by
  let T := M.edges.filter (fun e => e.2 ∈ S)
  have ht : T ⊆ M.edges := Finset.filter_subset _ _
  have his : Set.InjOn Prod.snd (T : Set (Fin m × Fin m)) :=
    fun _ he _ he' h => matching_edges_snd_injOn M (ht he) (ht he') h
  have hif : Set.InjOn Prod.fst (T : Set (Fin m × Fin m)) :=
    fun _ he _ he' h => matching_edges_fst_injOn M (ht he) (ht he') h
  have hi : T.image Prod.snd = S := matching_selected_edges_image M S hS
  have hc : T.card = S.card := by rw [← hi, Finset.card_image_of_injOn his]
  change (∏ e ∈ T, s * a e.2 * b e.1) = _
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, hc]
  rw [← Finset.prod_image his, hi, ← Finset.prod_image hif]
  rfl

/-- [Expanding a matching product can be indexed by matched recipient subsets.](goal) -/
-- @node: matching_product_recipient_expansion
lemma matching_product_recipient_expansion {m : ℕ} (M : Matching m)
    (s : ℝ) (a b : Fin m → ℝ) :
    (∏ e ∈ M.edges, (1 + s * a e.2 * b e.1)) =
      ∑ S ∈ (matchingRecipients M).powerset,
        s ^ S.card * (∏ c ∈ S, a c) * ∏ j ∈ donorImage M S, b j := by
  rw [Finset.prod_one_add]
  apply Finset.sum_bij (fun T _ => T.image Prod.snd)
  · intro T hT
    apply Finset.mem_powerset.mpr
    intro c hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
    have ha := (Finset.mem_filter.mp ((Finset.mem_powerset.mp hT) he)).2
    simp [matchingRecipients, ha]
  · intro T hT U hU h
    have ht := matching_edgeSubset_recover M T (Finset.mem_powerset.mp hT)
    have hu := matching_edgeSubset_recover M U (Finset.mem_powerset.mp hU)
    rw [h] at ht
    exact ht.symm.trans hu
  · intro S hS
    refine ⟨M.edges.filter (fun e => e.2 ∈ S),
      Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    exact matching_selected_edges_image M S (Finset.mem_powerset.mp hS)
  · intro T hT
    have hs : T.image Prod.snd ⊆ matchingRecipients M := by
      intro c hc
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
      have ha := (Finset.mem_filter.mp ((Finset.mem_powerset.mp hT) he)).2
      simp [matchingRecipients, ha]
    have h := matching_selected_product M (T.image Prod.snd) hs s a b
    rw [matching_edgeSubset_recover M T (Finset.mem_powerset.mp hT)] at h
    exact h

/-- [A matching expansion groups every selected-arrow term by its donor-image event.](goal) -/
-- @node: matching_product_image_expansion
lemma matching_product_image_expansion {m : ℕ} (M : Matching m)
    (s : ℝ) (a b : Fin m → ℝ) :
    (∏ e ∈ M.edges, (1 + s * a e.2 * b e.1)) =
      ∑ S : Finset (Fin m), ∑ J : Finset (Fin m),
        if ImageEvent M S J then
          s ^ S.card * (∏ c ∈ S, a c) * ∏ j ∈ J, b j else 0 := by
  rw [matching_product_recipient_expansion]
  have hinner (S : Finset (Fin m)) :
      (∑ J : Finset (Fin m), if ImageEvent M S J then
        s ^ S.card * (∏ c ∈ S, a c) * ∏ j ∈ J, b j else 0) =
      if S ⊆ matchingRecipients M then
        s ^ S.card * (∏ c ∈ S, a c) * ∏ j ∈ donorImage M S, b j else 0 := by
    by_cases hs : S ⊆ matchingRecipients M
    · rw [if_pos hs]
      have he : ∀ J, ImageEvent M S J ↔ donorImage M S = J := by
        intro J
        exact and_iff_right ((matching_selected_iff_subset M S).mpr hs)
      simp_rw [he]
      simp
    · rw [if_neg hs]
      apply Finset.sum_eq_zero
      intro J _
      apply if_neg
      intro he
      exact hs ((matching_selected_iff_subset M S).mp he.1)
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext S
    simp
  · intro S _
    rfl

/-- Given [the stated assumptions](hyp:hfit), [Averaging the finite expansion gives the exact posterior donor-image coefficients.](goal) -/
-- @node: likelihoodPoly_image_expansion
lemma likelihoodPoly_image_expansion (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (σ : Bool) (o : Record (Fin n)) :
    likelihoodPoly n m hfit q r δ σ o =
      ∑ S : Finset (Fin m), ∑ J : Finset (Fin m),
        imageProb n m hfit q r o.1 S J *
          (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ ^ S.card *
            (∏ c ∈ S, responseMark δ (o.2.2 (recipientOf n m hfit c))) *
            ∏ j ∈ J, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
              (o.2.1 (donorOf n m hfit j))) := by
  unfold likelihoodPoly
  simp_rw [matching_product_image_expansion _
    (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ)
    (fun c => responseMark δ (o.2.2 (recipientOf n m hfit c)))
    (fun j => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
      (o.2.1 (donorOf n m hfit j))), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  unfold imageProb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro M _
  split_ifs <;> simp

/-- Given [the stated assumptions](hyp:hfit,h), [Image coefficients vanish when the recipient and donor cardinalities differ.](goal) -/
-- @node: imageProb_eq_zero_of_card_ne
lemma imageProb_eq_zero_of_card_ne (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (H : Acq (Fin n)) (S J : Finset (Fin m)) (h : S.card ≠ J.card) :
    imageProb n m hfit q r H S J = 0 := by
  apply Finset.sum_eq_zero
  intro M _
  apply if_neg
  intro he
  exact h (imageEvent_card_eq M S J he).symm

/-- Given [the stated assumptions](hyp:hfit), [The sign difference selects exactly the odd recipient-set orders.](goal) -/
-- @node: likelihoodPoly_odd_image_expansion
lemma likelihoodPoly_odd_image_expansion (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (o : Record (Fin n)) :
    likelihoodPoly n m hfit q r δ true o - likelihoodPoly n m hfit q r δ false o =
      2 * ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => Odd S.card),
        ∑ J : Finset (Fin m), imageProb n m hfit q r o.1 S J *
          ((∏ c ∈ S, responseMark δ (o.2.2 (recipientOf n m hfit c))) *
            ∏ j ∈ J, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
              (o.2.1 (donorOf n m hfit j))) := by
  rw [likelihoodPoly_image_expansion, likelihoodPoly_image_expansion]
  simp only [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf,
    Bool.false_eq_true, ↓reduceIte, one_pow, one_mul]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hs : Odd S.card
  · rw [if_pos hs, Finset.mul_sum, ← Finset.sum_sub_distrib, hs.neg_one_pow]
    apply Finset.sum_congr rfl
    intro J _
    ring
  · rw [if_neg hs, ← Finset.sum_sub_distrib]
    have he : Even S.card := Nat.not_odd_iff_even.mp hs
    rw [he.neg_one_pow]
    apply Finset.sum_eq_zero
    intro J _
    ring

/-- Given [the stated assumptions](hyp:hzero,hsecond), [Product-measure orthogonality, using the zero first moment at any differing coordinate.](goal) -/
-- @node: subset_product_integral_orthogonality
lemma subset_product_integral_orthogonality {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ) (hzero : (∫ x, w x ∂μ) = 0) (γ : ℝ)
    (hsecond : (∫ x, w x ^ 2 ∂μ) = γ) (S T : Finset ι) :
    (∫ x : ι → α, (∏ i ∈ S, w (x i)) * (∏ i ∈ T, w (x i))
      ∂Measure.pi (fun _ => μ)) = if S = T then γ ^ S.card else 0 := by
  have hprod (x : ι → α) :
      (∏ i ∈ S, w (x i)) * (∏ i ∈ T, w (x i)) =
      ∏ i : ι, (if i ∈ S then w (x i) else 1) *
        (if i ∈ T then w (x i) else 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq]
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_prod
    (fun i x => (if i ∈ S then w x else 1) * (if i ∈ T then w x else 1))]
  by_cases hST : S = T
  · subst T
    rw [if_pos rfl]
    have hfactor (i : ι) :
        (∫ x, (if i ∈ S then w x else 1) * (if i ∈ S then w x else 1) ∂μ) =
        if i ∈ S then γ else 1 := by
      by_cases hi : i ∈ S
      · simp only [hi, ↓reduceIte, ← sq]
        exact hsecond
      · simp [hi]
    simp_rw [hfactor]
    rw [Finset.prod_ite_mem_eq, Finset.prod_const]
  · rw [if_neg hST]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra h
      apply hST
      ext i
      exact not_not.mp (not_exists.mp h i)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T
    · exact False.elim (hi (by simp [hS, hT]))
    · simpa only [hS, hT, ↓reduceIte, mul_one] using hzero
    · simpa only [hS, hT, ↓reduceIte, one_mul] using hzero
    · exact False.elim (hi (by simp [hS, hT]))

/-- [Recipient monomials have the diagonal norm specified by the mark energy.](goal) -/
-- @node: response_subset_integral_orthogonality
lemma response_subset_integral_orthogonality (m : ℕ) (δ : ℝ)
    (S T : Finset (Fin m)) :
    (∫ y : Fin m → ℝ,
      (∏ c ∈ S, responseMark δ (y c)) * (∏ c ∈ T, responseMark δ (y c))
      ∂Measure.pi (fun _ => volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y)))) =
      if S = T then markEnergy δ ^ S.card else 0 := by
  letI := balancedResponseLaw_probability δ
  exact subset_product_integral_orthogonality _ _
    (responseMark_balanced_integral_zero δ) _ (responseMark_balanced_secondMoment δ) S T

/-- [Fair assignment signs are centered and have unit second moment.](goal) -/
-- @node: fair_sign_integral_moments
lemma fair_sign_integral_moments :
    (∫ b, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf b
      ∂CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2)) = 0 ∧
    (∫ b, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf b ^ 2
      ∂CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2)) = 1 := by
  rw [show CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2) =
    Causalean.Mathlib.Probability.bernoulliBool (1/2) from add_comm _ _]
  constructor <;>
    rw [Causalean.Mathlib.Probability.bernoulliBool_integral (by norm_num) (by norm_num)] <;>
    norm_num [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf]

/-- Given [the stated assumptions](hyp:hfit), [Donor characters are orthogonal even though every ancillary assignment coordinate is retained.](goal) -/
-- @node: donor_subset_integral_orthogonality
lemma donor_subset_integral_orthogonality (n m : ℕ) (hfit : 2*m ≤ n)
    (J K : Finset (Fin m)) :
    (∫ z : Assign (Fin n),
      (∏ j ∈ J, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
        (z (donorOf n m hfit j))) *
      (∏ j ∈ K, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
        (z (donorOf n m hfit j)))
      ∂CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli (Fin n)) =
      if J = K then 1 else 0 := by
  have hinj : Function.Injective (donorOf n m hfit) := by
    intro j k h
    apply Fin.ext
    exact congrArg (fun i : Fin n => i.val) h
  have himage : J.image (donorOf n m hfit) = K.image (donorOf n m hfit) ↔ J = K :=
    Finset.image_injective hinj |>.eq_iff
  letI := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
    (1/2) (by constructor <;> norm_num)
  have h := subset_product_integral_orthogonality
    (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1/2))
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
    fair_sign_integral_moments.1 1 fair_sign_integral_moments.2
    (J.image (donorOf n m hfit)) (K.image (donorOf n m hfit))
  simp only [Finset.prod_image hinj.injOn, himage, one_pow] at h
  exact h

/-- A recipient-mark monomial paired with its collective donor character. -/
-- @node: imageMonomial
def imageMonomial (n m : ℕ) (hfit : 2*m ≤ n) (δ : ℝ)
    (S J : Finset (Fin m)) (o : Record (Fin n)) : ℝ :=
  (∏ c ∈ S, responseMark δ (o.2.2 (recipientOf n m hfit c))) *
    ∏ j ∈ J, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
      (o.2.1 (donorOf n m hfit j))

/-- Given [the stated assumptions](hyp:hfit), [Every finite recipient/donor monomial is Borel.](goal) -/
-- @node: imageMonomial_measurable
@[fun_prop] lemma imageMonomial_measurable (n m : ℕ) (hfit : 2*m ≤ n) (δ : ℝ)
    (S J : Finset (Fin m)) : Measurable (imageMonomial n m hfit δ S J) := by
  unfold imageMonomial
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro c _
    fun_prop
  · fun_prop

/-- Given [the stated assumptions](hyp:hfit), [Recipient coordinates of the reference embedding equal the independently drawn responses.](goal) -/
-- @node: referenceRecordOf_recipient
lemma referenceRecordOf_recipient (n m : ℕ) (hfit : 2*m ≤ n)
    (ω : Acq (Fin n) × (Assign (Fin n) × (Fin m → ℝ))) (c : Fin m) :
    (referenceRecordOf n m hfit ω).2.2 (recipientOf n m hfit c) = ω.2.2 c := by
  simp only [referenceRecordOf,
    (recipientOf_injective n m hfit).eq_iff, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- Given [the stated assumptions](hyp:hfit,hqr,hf), [The full reference orthogonality retains an arbitrary Borel function of the graph.](goal) -/
-- @node: reference_imageMonomial_pair_integral
lemma reference_imageMonomial_pair_integral (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (hqr : ChannelDomain q r) (S J T K : Finset (Fin m))
    (f : Acq (Fin n) → ℝ) (hf : Measurable f) :
    (∫ o, f o.1 * imageMonomial n m hfit δ S J o * imageMonomial n m hfit δ T K o
      ∂referenceLaw n m hfit q r δ) =
      if S = T ∧ J = K then
        (∫ H, f H ∂plantedGraphLaw n m hfit q r) * markEnergy δ ^ S.card else 0 := by
  letI := plantedGraphLaw_probability n m hfit q r hqr
  letI := balancedResponseLaw_probability δ
  letI := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
    (1/2) (by constructor <;> norm_num)
  have hmeas : Measurable (fun o : Record (Fin n) =>
      f o.1 * imageMonomial n m hfit δ S J o * imageMonomial n m hfit δ T K o) := by
    fun_prop
  unfold referenceLaw
  rw [integral_map (referenceRecordOf_measurable n m hfit).aemeasurable hmeas.aestronglyMeasurable]
  simp only [imageMonomial, referenceRecordOf_recipient]
  have hrearr (ω : Acq (Fin n) × (Assign (Fin n) × (Fin m → ℝ))) :
      f (referenceRecordOf n m hfit ω).1 *
          ((∏ c ∈ S, responseMark δ (ω.2.2 c)) *
            ∏ j ∈ J, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
              ((referenceRecordOf n m hfit ω).2.1 (donorOf n m hfit j))) *
          ((∏ c ∈ T, responseMark δ (ω.2.2 c)) *
            ∏ j ∈ K, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
              ((referenceRecordOf n m hfit ω).2.1 (donorOf n m hfit j))) =
      f ω.1 *
        (((∏ j ∈ J, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
            (ω.2.1 (donorOf n m hfit j))) *
          ∏ j ∈ K, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
            (ω.2.1 (donorOf n m hfit j))) *
         ((∏ c ∈ S, responseMark δ (ω.2.2 c)) * ∏ c ∈ T, responseMark δ (ω.2.2 c))) := by
    dsimp [referenceRecordOf]
    ring
  simp_rw [hrearr]
  rw [integral_prod_mul f (fun zy : Assign (Fin n) × (Fin m → ℝ) =>
    ((∏ j ∈ J, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
      (zy.1 (donorOf n m hfit j))) *
     ∏ j ∈ K, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
      (zy.1 (donorOf n m hfit j))) *
    ((∏ c ∈ S, responseMark δ (zy.2 c)) * ∏ c ∈ T, responseMark δ (zy.2 c)))]
  rw [integral_prod_mul
    (fun z : Assign (Fin n) =>
      (∏ j ∈ J, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
        (z (donorOf n m hfit j))) *
      ∏ j ∈ K, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
        (z (donorOf n m hfit j)))
    (fun y : Fin m → ℝ => (∏ c ∈ S, responseMark δ (y c)) * ∏ c ∈ T, responseMark δ (y c)),
    donor_subset_integral_orthogonality, response_subset_integral_orthogonality]
  by_cases hST : S = T <;> by_cases hJK : J = K <;> simp [hST, hJK]

end CausalSmith.Experimentation.NoisygraphTtePrecision
