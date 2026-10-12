module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.ReferenceLaw
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingPosteriorMoments
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingSizeTail

/-!
# Disjoint fixed-matching decomposition of donor-image events

Restricting a matching to selected recipients gives the unique fixed matching
whose inclusion realizes the selected donor-image event. This implements the
finite event decomposition in the all-order posterior-energy proof.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable

/-- Keep exactly the arrows arriving at the selected recipients. -/
-- @node: matchingOnRecipients
def matchingOnRecipients {m : ℕ} (M : Matching m) (S : Finset (Fin m)) : Matching m :=
  ⟨fun c => if c ∈ S then M.1 c else none, by
    intro c c' a hc hc'
    dsimp only at hc hc'
    split_ifs at hc hc' with h h'
    · exact M.2 c c' a hc hc'
    all_goals simp_all⟩

/-- [Recipient restriction deletes exactly the arrows outside the selected set.](goal) -/
-- @node: matchingOnRecipients_edges
lemma matchingOnRecipients_edges {m : ℕ} (M : Matching m) (S : Finset (Fin m)) :
    (matchingOnRecipients M S).edges = M.edges.filter (fun e => e.2 ∈ S) := by
  ext e
  by_cases he : e.2 ∈ S <;> simp [Matching.edges, matchingOnRecipients, he]

/-- [Restriction preserves the collective donor image of the selected recipients.](goal) -/
-- @node: matchingOnRecipients_donorImage
lemma matchingOnRecipients_donorImage {m : ℕ} (M : Matching m) (S : Finset (Fin m)) :
    donorImage (matchingOnRecipients M S) S = donorImage M S := by
  simp [donorImage, matchingOnRecipients_edges, Finset.filter_filter]

/-- Given [the stated assumptions](hyp:h), [When all selected recipients are matched, restriction has precisely that recipient set.](goal) -/
-- @node: matchingOnRecipients_recipients
lemma matchingOnRecipients_recipients {m : ℕ} (M : Matching m) (S : Finset (Fin m))
    (h : ∀ c ∈ S, ∃ a, M.1 c = some a) :
    matchingRecipients (matchingOnRecipients M S) = S := by
  ext c
  change c ∈ Finset.univ.filter (fun i => (if i ∈ S then M.1 i else none).isSome) ↔ c ∈ S
  by_cases hc : c ∈ S
  · obtain ⟨a, ha⟩ := h c hc
    simp [matchingRecipients, matchingOnRecipients, Finset.mem_filter, hc, ha]
  · simp [matchingRecipients, matchingOnRecipients, Finset.mem_filter, hc]

/-- Given [the stated assumptions](hyp:hF,hsub), [A submatching with exactly the selected recipients must equal the restriction.](goal) -/
-- @node: matchingOnRecipients_unique
lemma matchingOnRecipients_unique {m : ℕ} (M F : Matching m) (S : Finset (Fin m))
    (hF : matchingRecipients F = S) (hsub : F.edges ⊆ M.edges) :
    F = matchingOnRecipients M S := by
  apply Subtype.ext
  funext c
  by_cases hc : c ∈ S
  · have hsome : (F.1 c).isSome := by
      have := hF.symm ▸ hc
      exact (Finset.mem_filter.mp this).2
    cases hf : F.1 c with
    | none => simp [hf] at hsome
    | some a =>
      have hm := matching_assignment_of_subset hsub hf
      simp [matchingOnRecipients, hc, hf, hm]
  · have hnone : F.1 c = none := by
      cases hf : F.1 c with
      | none => rfl
      | some a =>
        have : c ∈ matchingRecipients F := by simp [matchingRecipients, hf]
        exact False.elim (hc (hF ▸ this))
    simp [matchingOnRecipients, hc, hnone]

/-- [The image event is the disjoint union of inclusions of fixed recipient-image matchings.](goal) -/
-- @node: imageEvent_fixedMatching_iff
lemma imageEvent_fixedMatching_iff {m : ℕ} (M : Matching m) (S J : Finset (Fin m)) :
    ImageEvent M S J ↔ ∃ F : Matching m,
      matchingRecipients F = S ∧ donorImage F S = J ∧ F.edges ⊆ M.edges := by
  constructor
  · rintro ⟨hmatched, himage⟩
    refine ⟨matchingOnRecipients M S, matchingOnRecipients_recipients M S hmatched, ?_, ?_⟩
    · exact (matchingOnRecipients_donorImage M S).trans himage
    · rw [matchingOnRecipients_edges]
      exact Finset.filter_subset _ _
  · rintro ⟨F, hF, himage, hsub⟩
    have heq := matchingOnRecipients_unique M F S hF hsub
    constructor
    · intro c hc
      have hmem : c ∈ matchingRecipients F := hF.symm ▸ hc
      have hsome : (F.1 c).isSome := (Finset.mem_filter.mp hmem).2
      cases hf : F.1 c with
      | none => simp [hf] at hsome
      | some a => exact ⟨a, matching_assignment_of_subset hsub hf⟩
    · rw [heq, matchingOnRecipients_donorImage] at himage
      exact himage

/-- [Each image event has a unique fixed matching witness, so its weight is a disjoint sum.](goal) -/
-- @node: imageEvent_weight_decomposition
lemma imageEvent_weight_decomposition {m : ℕ} (M : Matching m)
    (S J : Finset (Fin m)) (w : ℝ) :
    (if ImageEvent M S J then w else 0) =
      ∑ F : Matching m, if matchingRecipients F = S ∧ donorImage F S = J ∧
        F.edges ⊆ M.edges then w else 0 := by
  by_cases h : ImageEvent M S J
  · obtain ⟨F, hF, hJ, hsub⟩ := (imageEvent_fixedMatching_iff M S J).mp h
    rw [if_pos h]
    symm
    calc
      _ = (if matchingRecipients F = S ∧ donorImage F S = J ∧
          F.edges ⊆ M.edges then w else 0) := by
        apply Finset.sum_eq_single F
        · intro F' _ hne
          split_ifs with h'
          · have heq : F' = F :=
              (matchingOnRecipients_unique M F' S h'.1 h'.2.2).trans
                (matchingOnRecipients_unique M F S hF hsub).symm
            exact False.elim (hne heq)
          · rfl
        · simp
      _ = w := if_pos ⟨hF, hJ, hsub⟩
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro F _
    apply if_neg
    intro hF
    exact h ((imageEvent_fixedMatching_iff M S J).mpr ⟨F, hF⟩)

/-- Given [the stated assumptions](hyp:hfit), [Posterior donor-image probabilities sum the inclusions of their fixed matchings.](goal) -/
-- @node: imageProb_fixedMatching_sum
lemma imageProb_fixedMatching_sum (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (H : Acq (Fin n)) (S J : Finset (Fin m)) :
    imageProb n m hfit q r H S J =
      ∑ F ∈ Finset.univ.filter (fun F : Matching m =>
        matchingRecipients F = S ∧ donorImage F S = J),
        ∑ M ∈ supersets m F, matchingPosterior n m hfit q r H M := by
  unfold imageProb
  simp_rw [imageEvent_weight_decomposition]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter, supersets]
  apply Finset.sum_congr rfl
  intro F _
  by_cases hF : matchingRecipients F = S ∧ donorImage F S = J
  · simp only [hF, true_and, if_true, Finset.sum_filter]
  · have hno (M : Matching m) : ¬(matchingRecipients F = S ∧ donorImage F S = J ∧ F.edges ⊆ M.edges) :=
      fun h => hF ⟨h.1, h.2.1⟩
    simp only [hF, hno, if_false, Finset.sum_const_zero]

/-- Given [the stated assumptions](hyp:hF), [Every fixed matching in the image decomposition has the selected recipient cardinality.](goal) -/
-- @node: imageMatching_size
lemma imageMatching_size {m : ℕ} (F : Matching m) (S : Finset (Fin m))
    (hF : matchingRecipients F = S) : F.size = S.card := by
  rw [← matchingRecipients_card, hF]

/-- Given [the stated assumptions](hyp:hfit,hr,hrq,hq), [The image probability inherits the residual-partition bound term by term.](goal) -/
-- @node: imageProb_le_edgeProducts
lemma imageProb_le_edgeProducts (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (hr : 0 < r) (hrq : r ≤ q) (hq : q ≤ 1)
    (H : Acq (Fin n)) (S J : Finset (Fin m)) :
    imageProb n m hfit q r H S J ≤
      activity m ^ S.card *
        ∑ F ∈ Finset.univ.filter (fun F : Matching m =>
          matchingRecipients F = S ∧ donorImage F S = J),
          ∏ e ∈ F.edges, edgeRatio q r (H (candidateArrow n m hfit e)) := by
  have hprod (M : Matching m) := by
    by_cases hr1 : r < 1
    · exact matchingPosterior_product_interior n m hfit q r hr hr1 hrq hq H M
    · have hr_eq : r = 1 := le_antisymm (hrq.trans hq) (le_of_not_gt hr1)
      have hq_eq : q = 1 := le_antisymm hq (hr_eq ▸ hrq)
      subst r; subst q
      exact matchingPosterior_product_endpoint n m hfit H M
  rw [imageProb_fixedMatching_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro F hF
  have hsize := imageMatching_size F S (Finset.mem_filter.mp hF).2.1
  simp_rw [hprod]
  have hw (e : Fin m × Fin m) :
      0 ≤ activity m * edgeRatio q r (H (candidateArrow n m hfit e)) :=
    mul_nonneg (by unfold activity; positivity) (edgeRatio_nonneg q r ⟨hr.le, hrq, hq⟩ _)
  have hb := matching_normalized_weighted_inclusion
    (fun e => activity m * edgeRatio q r (H (candidateArrow n m hfit e))) hw F
  change F.edges.card = S.card at hsize
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, hsize] using hb

end CausalSmith.Experimentation.NoisygraphTtePrecision
