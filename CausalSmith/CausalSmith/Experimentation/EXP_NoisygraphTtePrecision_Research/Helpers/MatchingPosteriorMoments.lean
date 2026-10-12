module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.ConditionalBitMoments

/-!
# Posterior inclusion and pair moments under the planted graph marginal

Proves the one-bit likelihood-ratio moments and the channel second-moment bounds.
Residual deletion proves the prior and posterior inclusion bounds. Full-report
Bayes weights factor into matching-edge products, including the deterministic
channel endpoint. Arbitrary edge-set inclusion and nonnegative product expansion
bound all finite prior interactions. Conditional independence and the bounded
one-bit likelihood ratio prove the pair moment under the planted marginal,
including the deterministic channel endpoint.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- Given [the stated assumptions](hyp:hr,hr1), [The nonedge bit has mean-one likelihood ratio for every interior false-positive rate.](goal) -/
-- @node: edgeRatio_nonedge_mean
lemma edgeRatio_nonedge_mean (q r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    r * edgeRatio q r true + (1-r) * edgeRatio q r false = 1 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have h1r : 1-r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  simp only [edgeRatio, if_neg hr0, if_neg (show ¬(r = 1 ∧ q = 1) by
    intro h; linarith [h.1]), Bool.coe_false, if_true, if_false]
  field_simp
  ring

/-- Given [the stated assumptions](hyp:hr,hr1), [The nonedge bit second moment equals the declared channel factor.](goal) -/
-- @node: edgeRatio_nonedge_second_moment
lemma edgeRatio_nonedge_second_moment (q r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    r * edgeRatio q r true ^ 2 + (1-r) * edgeRatio q r false ^ 2 = kappa q r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have h1r : 1-r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  have he : ¬(r = 1 ∧ q = 1) := by intro h; linarith [h.1]
  simp only [edgeRatio, kappa, if_neg hr0, if_neg he, Bool.coe_false, if_true, if_false]
  field_simp

/-- Given [the stated assumptions](hyp:hr,hr1,hrq,hq), [Ordered channel probabilities control the negative-bit contribution by one minus q.](goal) -/
-- @node: kappa_le_one_add_signal
lemma kappa_le_one_add_signal (q r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hrq : r ≤ q) (hq : q ≤ 1) : kappa q r ≤ 1 + q^2/r := by
  have hterm : (1-q)^2/(1-r) ≤ 1-q := by
    apply (div_le_iff₀ (sub_pos.mpr hr1)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hrq)]
  have he : ¬(r = 1 ∧ q = 1) := by intro h; linarith [h.1]
  rw [kappa, if_neg (ne_of_gt hr), if_neg he]
  linarith

/-- Given [the stated assumptions](hyp:h,hc), [Edge-set containment forces every prescribed recipient assignment.](goal) -/
-- @node: matching_assignment_of_subset
lemma matching_assignment_of_subset {m : ℕ} {F M : Matching m}
    (h : F.edges ⊆ M.edges) {c a : Fin m} (hc : F.1 c = some a) :
    M.1 c = some a := by
  have he : (a, c) ∈ F.edges := by simp [Matching.edges, hc]
  exact (Finset.mem_filter.mp (h he)).2

/-- Delete the recipients already occupied by a fixed matching. -/
-- @node: matchingResidual
def matchingResidual {m : ℕ} (F M : Matching m) : Matching m :=
  ⟨fun c => if F.1 c = none then M.1 c else none, by
    intro c c' a hc hc'
    dsimp only at hc hc'
    split_ifs at hc hc' with h h'
    · exact M.2 c c' a hc hc'
    all_goals simp_all⟩

/-- Given [the stated assumptions](hyp:h), [On supersets, deletion removes exactly the fixed edge set.](goal) -/
-- @node: matchingResidual_edges
lemma matchingResidual_edges {m : ℕ} {F M : Matching m} (h : F.edges ⊆ M.edges) :
    (matchingResidual F M).edges = M.edges \ F.edges := by
  ext e
  simp only [Matching.edges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff, matchingResidual]
  by_cases hc : F.1 e.2 = none
  · simp [hc]
  · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hc
    have hm := matching_assignment_of_subset h ha
    simp [hc, ha, hm]

/-- [Deletion is injective on matchings containing the fixed matching.](goal) -/
-- @node: matchingResidual_injOn
lemma matchingResidual_injOn {m : ℕ} (F : Matching m) :
    Set.InjOn (matchingResidual F) (supersets m F : Set (Matching m)) := by
  intro M hM M' hM' heq
  apply Subtype.ext
  funext c
  have hMsub := (Finset.mem_filter.mp hM).2
  have hM'sub := (Finset.mem_filter.mp hM').2
  by_cases hc : F.1 c = none
  · have hv := congrArg (fun R : Matching m => R.1 c) heq
    simpa [matchingResidual, hc] using hv
  · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hc
    exact (matching_assignment_of_subset hMsub ha).trans
      (matching_assignment_of_subset hM'sub ha).symm

/-- Given [the stated assumptions](hyp:hw), [Nonnegative edge weights give the residual-partition inclusion bound.](goal) -/
-- @node: matching_weighted_inclusion
lemma matching_weighted_inclusion {m : ℕ} (w : Fin m × Fin m → ℝ)
    (hw : ∀ e, 0 ≤ w e) (F : Matching m) :
    (∑ M ∈ supersets m F, ∏ e ∈ M.edges, w e) ≤
      (∏ e ∈ F.edges, w e) * ∑ M : Matching m, ∏ e ∈ M.edges, w e := by
  have hfactor (M : Matching m) (hM : M ∈ supersets m F) :
      (∏ e ∈ M.edges, w e) =
        (∏ e ∈ F.edges, w e) * ∏ e ∈ (matchingResidual F M).edges, w e := by
    have hs := (Finset.mem_filter.mp hM).2
    rw [matchingResidual_edges hs, mul_comm]
    exact (Finset.prod_sdiff hs).symm
  have hres : (∑ M ∈ supersets m F, ∏ e ∈ (matchingResidual F M).edges, w e) ≤
      ∑ M : Matching m, ∏ e ∈ M.edges, w e := by
    rw [← Finset.sum_image (f := fun M : Matching m => ∏ e ∈ M.edges, w e)
      (matchingResidual_injOn F)]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro M _ _
    exact Finset.prod_nonneg (fun e _ => hw e)
  calc
    (∑ M ∈ supersets m F, ∏ e ∈ M.edges, w e) =
        (∏ e ∈ F.edges, w e) * ∑ M ∈ supersets m F,
          ∏ e ∈ (matchingResidual F M).edges, w e := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hfactor
    _ ≤ _ := mul_le_mul_of_nonneg_left hres (Finset.prod_nonneg (fun e _ => hw e))

/-- Given [the stated assumptions](hyp:hw), [The empty matching keeps every nonnegative weighted partition strictly positive.](goal) -/
-- @node: matching_weighted_partition_pos
lemma matching_weighted_partition_pos {m : ℕ} (w : Fin m × Fin m → ℝ)
    (hw : ∀ e, 0 ≤ w e) : 0 < ∑ M : Matching m, ∏ e ∈ M.edges, w e := by
  let empty : Matching m := ⟨fun _ => none, by simp⟩
  have hempty : (∏ e ∈ empty.edges, w e) = 1 := by
    simp [Matching.edges, empty]
  have hle := Finset.single_le_sum (f := fun M : Matching m => ∏ e ∈ M.edges, w e)
    (fun M _ => Finset.prod_nonneg (fun e _ => hw e)) (Finset.mem_univ empty)
  rw [hempty] at hle
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hle

/-- Given [the stated assumptions](hyp:hw), [Normalizing the residual-partition comparison bounds weighted matching inclusions.](goal) -/
-- @node: matching_normalized_weighted_inclusion
lemma matching_normalized_weighted_inclusion {m : ℕ} (w : Fin m × Fin m → ℝ)
    (hw : ∀ e, 0 ≤ w e) (F : Matching m) :
    (∑ M ∈ supersets m F,
      (∏ e ∈ M.edges, w e) / ∑ M' : Matching m, ∏ e ∈ M'.edges, w e) ≤
      ∏ e ∈ F.edges, w e := by
  rw [← Finset.sum_div]
  exact (div_le_iff₀ (matching_weighted_partition_pos w hw)).mpr
    (matching_weighted_inclusion w hw F)

/-- [Constant activity weights specialize residual deletion to the dilute prior.](goal) -/
-- @node: matchingPrior_inclusion
lemma matchingPrior_inclusion (m : ℕ) (F : Matching m) :
    (∑ M ∈ supersets m F, matchingPriorMass m M) ≤ activity m ^ F.size := by
  have ha : 0 ≤ activity m := by unfold activity; positivity
  have h := matching_weighted_inclusion (fun _ => activity m) (fun _ => ha) F
  simp only [Finset.prod_const] at h
  change (∑ M ∈ supersets m F, matchingWeight m M) ≤
    activity m ^ F.size * matchingPartition m at h
  simp only [matchingPriorMass, ← Finset.sum_div]
  exact (div_le_iff₀ (matchingPartition_pos m)).mpr h

/-- Restrict a planted matching to an arbitrary candidate edge set. -/
-- @node: matchingRestrict
def matchingRestrict {m : ℕ} (M : Matching m) (B : Finset (Fin m × Fin m)) : Matching m :=
  ⟨fun c => (M.1 c).filter (fun a => (a,c) ∈ B), by
    intro c c' a hc hc'
    exact M.2 c c' a (Option.filter_eq_some_iff.mp hc).1
      (Option.filter_eq_some_iff.mp hc').1⟩

/-- [Restriction retains exactly the planted edges in the candidate set.](goal) -/
-- @node: matchingRestrict_edges
lemma matchingRestrict_edges {m : ℕ} (M : Matching m) (B : Finset (Fin m × Fin m)) :
    (matchingRestrict M B).edges = M.edges ∩ B := by
  ext e
  simp [Matching.edges, matchingRestrict, Option.filter_eq_some_iff]

/-- [Even a candidate edge set with conflicting endpoints obeys the prior inclusion bound.](goal) -/
-- @node: matchingPrior_arbitrary_inclusion
lemma matchingPrior_arbitrary_inclusion (m : ℕ) (B : Finset (Fin m × Fin m)) :
    (∑ M : Matching m, if B ⊆ M.edges then matchingPriorMass m M else 0) ≤
      activity m ^ B.card := by
  by_cases hex : ∃ M : Matching m, B ⊆ M.edges
  · obtain ⟨M₀, hM₀⟩ := hex
    let F := matchingRestrict M₀ B
    have hF : F.edges = B := by
      exact (matchingRestrict_edges M₀ B).trans (Finset.inter_eq_right.mpr hM₀)
    have h := matchingPrior_inclusion m F
    simpa only [supersets, Finset.sum_filter, hF, Matching.size] using h
  · have hno (M : Matching m) : ¬B ⊆ M.edges := fun h => hex ⟨M,h⟩
    simp only [hno, if_false, Finset.sum_const_zero]
    exact pow_nonneg (by unfold activity; positivity) _

/-- [A product of edge indicators is the indicator of their joint inclusion.](goal) -/
-- @node: matching_indicator_product
lemma matching_indicator_product {m : ℕ} (M : Matching m)
    (B : Finset (Fin m × Fin m)) (t : ℝ) :
    (∏ e ∈ B, if e ∈ M.edges then t else 0) =
      if B ⊆ M.edges then t ^ B.card else 0 := by
  by_cases hB : B ⊆ M.edges
  · simp only [if_pos hB]
    calc
      _ = ∏ _e ∈ B, t := Finset.prod_congr rfl (fun e he => if_pos (hB he))
      _ = _ := Finset.prod_const t
  · rw [if_neg hB]
    obtain ⟨e, he, hne⟩ := Finset.not_subset.mp hB
    exact Finset.prod_eq_zero he (if_neg hne)

/-- Given [the stated assumptions](hyp:ht), [Nonnegative product expansion and prior inclusion dominate all planted edge interactions.](goal) -/
-- @node: matchingPrior_product_domination
lemma matchingPrior_product_domination (m : ℕ) (S : Finset (Fin m × Fin m))
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ M : Matching m, matchingPriorMass m M *
      ∏ e ∈ S, (1 + if e ∈ M.edges then t else 0)) ≤
      (1 + activity m * t) ^ S.card := by
  simp_rw [Finset.prod_one_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ B ∈ S.powerset, t ^ B.card *
        ∑ M : Matching m, if B ⊆ M.edges then matchingPriorMass m M else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M hM
      rw [matching_indicator_product]
      split_ifs <;> ring
    _ ≤ ∑ B ∈ S.powerset, (activity m * t) ^ B.card := by
      apply Finset.sum_le_sum
      intro B hB
      calc
        _ ≤ t ^ B.card * activity m ^ B.card :=
          mul_le_mul_of_nonneg_left (matchingPrior_arbitrary_inclusion m B) (pow_nonneg ht _)
        _ = _ := by rw [mul_pow, mul_comm]
    _ = _ := by
      simpa only [Finset.prod_const] using
        (Finset.prod_one_add (f := fun _ : Fin m × Fin m => activity m * t) S).symm

/-- Given [the stated assumptions](hyp:hm,hr,hregime), [The planted-matching regime bounds the dilute activity times the maximal bit ratio.](goal) -/
-- @node: activity_edgeRatio_bound
lemma activity_edgeRatio_bound (m : ℕ) (hm : 1 ≤ m) (q r : ℝ) (hr : 0 < r)
    (hregime : q/2 ≤ m*r) : activity m * (q/r) ≤ 1/2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hid : activity m * (q/r) = q / (4*(m : ℝ)*r) := by
    dsimp [activity]
    ring
  rw [hid]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

/-- Given [the stated assumptions](hyp:hm,hr,hrq,hregime), [The edge-union expansion is bounded by one factor of three halves per distinct edge.](goal) -/
-- @node: matchingPrior_product_three_halves
lemma matchingPrior_product_three_halves (m : ℕ) (hm : 1 ≤ m)
    (q r : ℝ) (hr : 0 < r) (hrq : r ≤ q) (hregime : q/2 ≤ m*r)
    (S : Finset (Fin m × Fin m)) :
    (∑ M : Matching m, matchingPriorMass m M *
      ∏ e ∈ S, (1 + if e ∈ M.edges then q/r else 0)) ≤ (3/2 : ℝ)^S.card := by
  have ht : 0 ≤ q/r := div_nonneg (hr.le.trans hrq) hr.le
  refine (matchingPrior_product_domination m S (q/r) ht).trans ?_
  apply pow_le_pow_left₀ (by unfold activity; positivity)
  linarith [activity_edgeRatio_bound m hm q r hr hregime]

/-- Given [the stated assumptions](hyp:hF,hF'), [Equal matching sizes identify the number of distinct edges in the pair product.](goal) -/
-- @node: matching_pair_union_card
lemma matching_pair_union_card {m : ℕ} (F F' : Matching m) (k : ℕ)
    (hF : F.size = k) (hF' : F'.size = k) :
    (F.edges ∪ F'.edges).card = 2*k - (F.edges ∩ F'.edges).card := by
  have h := Finset.card_union_add_card_inter F.edges F'.edges
  change F.edges.card = k at hF
  change F'.edges.card = k at hF'
  omega

/-- Given [the stated assumptions](hyp:hfit), [Candidate labels retain both finite donor and recipient indices.](goal) -/
-- @node: candidateArrow_injective
lemma candidateArrow_injective (n m : ℕ) (hfit : 2*m ≤ n) :
    Function.Injective (candidateArrow n m hfit) := by
  intro e e' h
  have hd := congrArg (fun a : OffDiag (Fin n) => a.1.1.val) h
  have hc := congrArg (fun a : OffDiag (Fin n) => a.1.2.val) h
  apply Prod.ext
  · exact Fin.ext hd
  · apply Fin.ext
    change m + e.2.val = m + e'.2.val at hc
    omega

/-- Given [the stated assumptions](hyp:hfit), [The true-arrow coordinates are exactly the embedded matching edges.](goal) -/
-- @node: matchingEdge_coordinates
lemma matchingEdge_coordinates (n m : ℕ) (hfit : 2*m ≤ n) (M : Matching m) :
    (Finset.univ.filter (fun a : OffDiag (Fin n) =>
      matchingEdge n m hfit M a.1.1 a.1.2)) =
      M.edges.image (candidateArrow n m hfit) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨c, d, hc, hd, hM⟩
    refine ⟨(d,c), ?_, ?_⟩
    · simpa [Matching.edges] using hM
    · apply Subtype.ext
      exact Prod.ext hd.symm hc.symm
  · rintro ⟨e, he, rfl⟩
    exact ⟨e.2, e.1, rfl, rfl, (Finset.mem_filter.mp he).2⟩

/-- Given [the stated assumptions](hyp:hfit), [A candidate arrow is true exactly when its local edge belongs to the matching.](goal) -/
-- @node: matchingEdge_candidate_iff
lemma matchingEdge_candidate_iff (n m : ℕ) (hfit : 2*m ≤ n) (M : Matching m)
    (e : Fin m × Fin m) :
    matchingEdge n m hfit M (candidateArrow n m hfit e).1.1
      (candidateArrow n m hfit e).1.2 ↔ e ∈ M.edges := by
  have h := congrArg (fun s : Finset (OffDiag (Fin n)) => candidateArrow n m hfit e ∈ s)
    (matchingEdge_coordinates n m hfit M)
  simpa [Finset.mem_image, (candidateArrow_injective n m hfit).eq_iff] using h

/-- Given [the stated assumptions](hyp:hr,hr1), [An interior nonedge bit supplies a positive common likelihood factor.](goal) -/
-- @node: nonedge_graph_factor_pos
lemma nonedge_graph_factor_pos (n : ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (H : Acq (Fin n)) :
    0 < ∏ e : OffDiag (Fin n), (if H e then r else 1-r) := by
  apply Finset.prod_pos
  intro e _
  split_ifs <;> linarith

/-- Given [the stated assumptions](hyp:hfit,hr,hr1), [Every full-report likelihood is its all-nonedge likelihood times edge ratios.](goal) -/
-- @node: graphLikelihood_factorization
lemma graphLikelihood_factorization (n m : ℕ) (hfit : 2*m ≤ n)
    (q r : ℝ) (hr : 0 < r) (hr1 : r < 1) (H : Acq (Fin n)) (M : Matching m) :
    graphLikelihood n m hfit q r H M =
      (∏ e : OffDiag (Fin n), (if H e then r else 1-r)) *
        ∏ e ∈ M.edges, edgeRatio q r (H (candidateArrow n m hfit e)) := by
  have hr0 := ne_of_gt hr
  have h1r := ne_of_gt (sub_pos.mpr hr1)
  have he : ¬(r = 1 ∧ q = 1) := by intro h; linarith [h.1]
  have hbit (b : Bool) :
      (if b then q else 1-q) =
        (if b then r else 1-r) * edgeRatio q r b := by
    cases b <;> simp [edgeRatio, hr0, he] <;> field_simp
  have hprod : (∏ e : OffDiag (Fin n),
      if matchingEdge n m hfit M e.1.1 e.1.2 then edgeRatio q r (H e) else 1) =
      ∏ e ∈ M.edges, edgeRatio q r (H (candidateArrow n m hfit e)) := by
    rw [← Finset.prod_filter, matchingEdge_coordinates]
    exact Finset.prod_image (candidateArrow_injective n m hfit).injOn
  rw [← hprod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases hm : matchingEdge n m hfit M e.1.1 e.1.2
  · simp only [if_pos hm]
    exact hbit (H e)
  · simp [hm]

/-- Given [the stated assumptions](hyp:hfit,hr,hr1,hrq,hq), [The positive common graph factor cancels from the finite Bayes normalization.](goal) -/
-- @node: matchingPosterior_product_interior
lemma matchingPosterior_product_interior (n m : ℕ) (hfit : 2*m ≤ n)
    (q r : ℝ) (hr : 0 < r) (hr1 : r < 1) (hrq : r ≤ q) (hq : q ≤ 1)
    (H : Acq (Fin n)) (M : Matching m) :
    matchingPosterior n m hfit q r H M =
      (∏ e ∈ M.edges, activity m * edgeRatio q r (H (candidateArrow n m hfit e))) /
        ∑ M' : Matching m,
          ∏ e ∈ M'.edges, activity m * edgeRatio q r (H (candidateArrow n m hfit e)) := by
  let w := fun e => activity m * edgeRatio q r (H (candidateArrow n m hfit e))
  let c := (∏ e : OffDiag (Fin n), (if H e then r else 1-r)) / matchingPartition m
  have hc : 0 < c := div_pos (nonedge_graph_factor_pos n r hr hr1 H)
    (matchingPartition_pos m)
  have hw (e : Fin m × Fin m) : 0 ≤ w e :=
    mul_nonneg (by unfold activity; positivity) (edgeRatio_nonneg q r ⟨hr.le, hrq, hq⟩ _)
  have hweight (M' : Matching m) : posteriorWeight n m hfit q r H M' =
      c * ∏ e ∈ M'.edges, w e := by
    rw [posteriorWeight, graphLikelihood_factorization n m hfit q r hr hr1 H M']
    simp only [w, Finset.prod_mul_distrib, Finset.prod_const]
    dsimp [c, matchingPriorMass, matchingWeight, Matching.size]
    ring
  have hz := matching_weighted_partition_pos w hw
  have hsum : (∑ M' : Matching m, posteriorWeight n m hfit q r H M') =
      c * ∑ M' : Matching m, ∏ e ∈ M'.edges, w e := by
    simp_rw [hweight]
    rw [Finset.mul_sum]
  rw [matchingPosterior, if_neg (by rw [hsum]; exact ne_of_gt (mul_pos hc hz)),
    hweight, hsum, mul_div_mul_left _ _ (ne_of_gt hc)]

/-- Given [the stated assumptions](hyp:hfit), [At the single-point channel every matching has the same report likelihood.](goal) -/
-- @node: matchingPosterior_product_endpoint
lemma matchingPosterior_product_endpoint (n m : ℕ) (hfit : 2*m ≤ n)
    (H : Acq (Fin n)) (M : Matching m) :
    matchingPosterior n m hfit 1 1 H M =
      (∏ e ∈ M.edges, activity m * edgeRatio 1 1 (H (candidateArrow n m hfit e))) /
        ∑ M' : Matching m,
          ∏ e ∈ M'.edges, activity m * edgeRatio 1 1 (H (candidateArrow n m hfit e)) := by
  have hratio (b : Bool) : edgeRatio 1 1 b = 1 := by simp [edgeRatio]
  simp_rw [hratio, mul_one, Finset.prod_const]
  change matchingPosterior n m hfit 1 1 H M = matchingPriorMass m M
  let c : ℝ := ∏ e : OffDiag (Fin n), (if H e then 1 else 0)
  have hweight (M' : Matching m) : posteriorWeight n m hfit 1 1 H M' =
      matchingPriorMass m M' * c := by
    simp [posteriorWeight, graphLikelihood, c]
  have hsum : (∑ M' : Matching m, posteriorWeight n m hfit 1 1 H M') = c := by
    simp_rw [hweight]
    rw [← Finset.sum_mul, matchingPriorMass_sum_one, one_mul]
  rw [matchingPosterior, hsum]
  split_ifs with hc
  · rfl
  · rw [hweight, mul_div_cancel_right₀ _ hc]

/-- Given [the stated assumptions](hyp:hr,hr1,hrq,hq), [Conditional single and doubled edge moments have their nonedge scale times a planted factor.](goal) -/
-- @node: reportBitMoment_conditional_le
lemma reportBitMoment_conditional_le (q r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hrq : r ≤ q) (hq : q ≤ 1) (planted doubled : Prop) [Decidable planted]
    [Decidable doubled] :
    reportBitMoment (if planted then q else r) q r (if doubled then 2 else 1) ≤
      (if doubled then kappa q r else 1) * (1 + if planted then q/r else 0) := by
  have hbase : reportBitMoment r q r (if doubled then 2 else 1) =
      (if doubled then kappa q r else 1) := by
    split_ifs
    · exact edgeRatio_nonedge_second_moment q r hr hr1
    · simpa [reportBitMoment] using edgeRatio_nonedge_mean q r hr hr1
  by_cases hp : planted
  · simp only [if_pos hp]
    calc
      _ ≤ (q/r) * reportBitMoment r q r (if doubled then 2 else 1) :=
        reportBitMoment_true_le q r hr hr1 hrq hq _
      _ ≤ (1 + q/r) * reportBitMoment r q r (if doubled then 2 else 1) :=
        mul_le_mul_of_nonneg_right (by linarith)
          (reportBitMoment_nonneg r q r ⟨hr.le, hr1.le⟩ ⟨hr.le, hrq, hq⟩ _)
      _ = _ := by rw [hbase]; ring
  · simp only [if_neg hp, add_zero, mul_one]
    exact hbase.le

/-- Given [the stated assumptions](hyp:hr,hr1,hrq,hq), [Conditional independence leaves one channel factor for each doubled arrow.](goal) -/
-- @node: matching_conditional_product_le
lemma matching_conditional_product_le (m : ℕ) (q r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hrq : r ≤ q) (hq : q ≤ 1) (F F' M : Matching m) :
    (∏ e ∈ F.edges ∪ F'.edges,
      reportBitMoment (if e ∈ M.edges then q else r) q r
        (if e ∈ F.edges ∩ F'.edges then 2 else 1)) ≤
      kappa q r ^ (F.edges ∩ F'.edges).card *
        ∏ e ∈ F.edges ∪ F'.edges, (1 + if e ∈ M.edges then q/r else 0) := by
  calc
    _ ≤ ∏ e ∈ F.edges ∪ F'.edges,
        (if e ∈ F.edges ∩ F'.edges then kappa q r else 1) *
          (1 + if e ∈ M.edges then q/r else 0) := by
      apply Finset.prod_le_prod
      · intro e he
        apply reportBitMoment_nonneg _ q r _ ⟨hr.le, hrq, hq⟩
        split_ifs
        · exact ⟨hr.le.trans hrq, hq⟩
        · exact ⟨hr.le, hr1.le⟩
      · intro e he
        exact reportBitMoment_conditional_le q r hr hr1 hrq hq _ _
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
      have hfilter : (F.edges ∪ F'.edges).filter (fun e => e ∈ F.edges ∩ F'.edges) =
          F.edges ∩ F'.edges := by ext e; simp; tauto
      rw [hfilter, Finset.prod_const]

/-- Given [the stated assumptions](hyp:hm,hfit,hr,hrq,hq,hH), [Full Bayes weights reduce to matching products almost surely under the planted marginal;
posterior and prior inclusions and all pair moments obey the dilute bounds.](goal) -/
-- @node: lem:matching-posterior-moments
lemma matching_posterior_moments (n m : ℕ) (hm : 1 ≤ m) (hfit : 2*m ≤ n)
    (q r : ℝ) (hr : 0 < r) (hrq : r ≤ q) (hq : q ≤ 1)
    (D : Design (Fin n)) (hH : AcquisitionLaw D q r) :
    let PH := (matchingPrior m).bind (fun M => (D (matchingGraphSchedule n m hfit M)).map Prod.snd)
    let W := fun (H : Acq (Fin n)) (e : Fin m × Fin m) => edgeRatio q r (H (candidateArrow n m hfit e))
    let lam := activity m
    (∀ᵐ H ∂PH, ∀ M : Matching m, matchingPosterior n m hfit q r H M =
      (∏ e ∈ M.edges, lam * W H e) / ∑ M' : Matching m, ∏ e ∈ M'.edges, lam * W H e) ∧
    (∀ᵐ H ∂PH, ∀ F : Matching m,
      (∑ M ∈ supersets m F, matchingPosterior n m hfit q r H M) ≤
        lam^F.size * ∏ e ∈ F.edges, W H e) ∧
    (∀ F : Matching m, (∑ M ∈ supersets m F, matchingPriorMass m M) ≤ lam^F.size) ∧
    (q/2 ≤ m*r → ∀ (F F' : Matching m) (k : ℕ), F.size = k → F'.size = k →
      (∫ H, (∏ e ∈ F.edges, W H e) * (∏ e ∈ F'.edges, W H e) ∂PH) ≤
        kappa q r ^ (F.edges ∩ F'.edges).card * (3/2 : ℝ)^(2*k-(F.edges ∩ F'.edges).card)) ∧
    1 ≤ kappa q r ∧ (r < 1 → kappa q r ≤ 1+q^2/r) := by
  dsimp only
  have hBayes : ∀ᵐ H ∂(matchingPrior m).bind
      (fun M => (D (matchingGraphSchedule n m hfit M)).map Prod.snd),
      ∀ M : Matching m, matchingPosterior n m hfit q r H M =
        (∏ e ∈ M.edges, activity m * edgeRatio q r (H (candidateArrow n m hfit e))) /
          ∑ M' : Matching m,
            ∏ e ∈ M'.edges, activity m * edgeRatio q r (H (candidateArrow n m hfit e)) := by
    apply Filter.Eventually.of_forall
    intro H M
    by_cases hr1 : r < 1
    · exact matchingPosterior_product_interior n m hfit q r hr hr1 hrq hq H M
    · have hr_eq : r = 1 := le_antisymm (hrq.trans hq) (le_of_not_gt hr1)
      have hq_eq : q = 1 := le_antisymm hq (hr_eq ▸ hrq)
      subst r
      subst q
      exact matchingPosterior_product_endpoint n m hfit H M
  refine ⟨hBayes, ?_, matchingPrior_inclusion m, ?_,
    kappa_ge_one_of_positive q r hr hrq hq, ?_⟩
  · filter_upwards [hBayes] with H hprod
    intro F
    simp_rw [hprod]
    have hw (e : Fin m × Fin m) :
        0 ≤ activity m * edgeRatio q r (H (candidateArrow n m hfit e)) :=
      mul_nonneg (activity_pos m hm).le (edgeRatio_nonneg q r ⟨hr.le, hrq, hq⟩ _)
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Matching.size] using
      matching_normalized_weighted_inclusion
        (fun e => activity m * edgeRatio q r (H (candidateArrow n m hfit e))) hw F
  · intro hregime F F' k hF hF'
    have hgraph := hH
    dsimp only [AcquisitionLaw] at hgraph
    simp_rw [hgraph]
    change (∫ H, (∏ e ∈ F.edges, edgeRatio q r (H (candidateArrow n m hfit e))) *
      (∏ e ∈ F'.edges, edgeRatio q r (H (candidateArrow n m hfit e)))
      ∂plantedGraphLaw n m hfit q r) ≤ _
    by_cases hr1 : r < 1
    · have hconditional :
          (∫ H, (∏ e ∈ F.edges, edgeRatio q r (H (candidateArrow n m hfit e))) *
            (∏ e ∈ F'.edges, edgeRatio q r (H (candidateArrow n m hfit e)))
            ∂plantedGraphLaw n m hfit q r) ≤
          kappa q r ^ (F.edges ∩ F'.edges).card *
            ∑ M : Matching m, matchingPriorMass m M *
              ∏ e ∈ F.edges ∪ F'.edges, (1 + if e ∈ M.edges then q/r else 0) := by
        have hconditional_eq :
            (∫ H, (∏ e ∈ F.edges, edgeRatio q r (H (candidateArrow n m hfit e))) *
              (∏ e ∈ F'.edges, edgeRatio q r (H (candidateArrow n m hfit e)))
              ∂plantedGraphLaw n m hfit q r) =
            ∑ M : Matching m, matchingPriorMass m M *
              ∏ e ∈ F.edges ∪ F'.edges,
                reportBitMoment (if e ∈ M.edges then q else r) q r
                  (if e ∈ F.edges ∩ F'.edges then 2 else 1) := by
          rw [integral_plantedGraphLaw n m hfit q r ⟨hr.le, hrq, hq⟩]
          apply Finset.sum_congr rfl
          intro M _
          congr 1
          simp_rw [edge_products_merge]
          have hp (a : OffDiag (Fin n)) :
              (if (matchingGraphSchedule n m hfit M).edge a.1.1 a.1.2 then q else r) ∈
                Set.Icc 0 1 := by
            split_ifs
            · exact ⟨hr.le.trans hrq, hq⟩
            · exact ⟨hr.le, hr1.le⟩
          unfold acquisitionLaw
          rw [integral_edgeRatio_power_pi _ hp q r (candidateArrow n m hfit)
            (candidateArrow_injective n m hfit)]
          apply Finset.prod_congr rfl
          intro e _
          simp only [matchingGraphSchedule, matchingEdge_candidate_iff]
        rw [hconditional_eq, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro M _
        calc
          _ ≤ matchingPriorMass m M *
              (kappa q r ^ (F.edges ∩ F'.edges).card *
                ∏ e ∈ F.edges ∪ F'.edges, (1 + if e ∈ M.edges then q/r else 0)) :=
            mul_le_mul_of_nonneg_left
              (matching_conditional_product_le m q r hr hr1 hrq hq F F' M)
              (matchingPriorMass_nonneg m M)
          _ = _ := by ring
      calc
        _ ≤ _ := hconditional
        _ ≤ kappa q r ^ (F.edges ∩ F'.edges).card *
            (3/2 : ℝ)^(F.edges ∪ F'.edges).card :=
          mul_le_mul_of_nonneg_left
            (matchingPrior_product_three_halves m hm q r hr hrq hregime _)
            (pow_nonneg (kappa_nonneg q r ⟨hr.le, hrq, hq⟩) _)
        _ = _ := by rw [matching_pair_union_card F F' k hF hF']
    · have hr_eq : r = 1 := le_antisymm (hrq.trans hq) (le_of_not_gt hr1)
      have hq_eq : q = 1 := le_antisymm hq (hr_eq ▸ hrq)
      subst r
      subst q
      let := plantedGraphLaw_probability n m hfit 1 1 ⟨by norm_num, le_rfl, le_rfl⟩
      simp [edgeRatio, kappa]
      exact one_le_pow₀ (by norm_num)
  · intro hr1
    exact kappa_le_one_add_signal q r hr hr1 hrq hq

end CausalSmith.Experimentation.NoisygraphTtePrecision
