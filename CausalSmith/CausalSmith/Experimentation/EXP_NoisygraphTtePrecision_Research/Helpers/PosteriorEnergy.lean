module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingPosteriorMoments
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.PosteriorImageDecomposition

/-!
# All-order planted posterior image energy bound

Disjoint donor-image events, planted pair moments, and injection counts yield
the simultaneous all-order bound, including the channel endpoints.
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

/-- A fixed recipient-image matching assigns each selected recipient a donor in that image. -/
-- @node: imageMatchingEmbedding
def imageMatchingEmbedding {m : ℕ} (S J : Finset (Fin m))
    (F : {F : Matching m // matchingRecipients F = S ∧ donorImage F S = J}) :
    ↥S ↪ ↥J where
  toFun i :=
    let hi : (F.1.1 i.1).isSome := by
      have hmem : i.1 ∈ matchingRecipients F.1 := F.2.1.symm ▸ i.2
      exact (Finset.mem_filter.mp hmem).2
    ⟨(F.1.1 i.1).get hi, by
      have hmem : (F.1.1 i.1).get hi ∈ donorImage F.1 S := by
        unfold donorImage
        apply Finset.mem_image.mpr
        refine ⟨((F.1.1 i.1).get hi, i.1), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Matching.edges]
        exact ⟨(Option.some_get _).symm, i.2⟩
      exact (congrArg (fun T : Finset (Fin m) => (F.1.1 i.1).get hi ∈ T) F.2.2).mp hmem⟩
  inj' := by
    intro i j h
    apply Subtype.ext
    exact F.1.2 i j _ (Option.some_get _).symm
      ((Option.some_get _).symm.trans (congrArg some (congrArg Subtype.val h).symm))

/-- [Distinct fixed-image matchings give distinct donor assignments.](goal) -/
-- @node: imageMatchingEmbedding_injective
lemma imageMatchingEmbedding_injective {m : ℕ} (S J : Finset (Fin m)) :
    Function.Injective (imageMatchingEmbedding S J) := by
  intro F G h
  apply Subtype.ext
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ S
  · have he := congrArg (fun e : ↥S ↪ ↥J => (e ⟨i, hi⟩).1) h
    dsimp only [imageMatchingEmbedding] at he
    exact ((Option.some_get _).symm.trans (congrArg some he)).trans (Option.some_get _)
  · have hn (M : Matching m) (hM : matchingRecipients M = S) : M.1 i = none := by
      have hnot : ¬ (M.1 i).isSome := by
        intro hs
        apply hi
        rw [← hM]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
      cases he : M.1 i <;> simp_all
    rw [hn F.1 F.2.1, hn G.1 G.2.1]

/-- Given [the stated assumptions](hyp:hS,hJ), [A pair of size-k recipient and donor sets admits at most k! matching assignments.](goal) -/
-- @node: imageMatching_count_le
lemma imageMatching_count_le {m k : ℕ} (S J : Finset (Fin m))
    (hS : S.card = k) (hJ : J.card = k) :
    (Finset.univ.filter (fun F : Matching m =>
      matchingRecipients F = S ∧ donorImage F S = J)).card ≤ k.factorial := by
  rw [← Fintype.card_subtype]
  calc
    _ ≤ Fintype.card (↥S ↪ ↥J) :=
      Fintype.card_le_of_injective _ (imageMatchingEmbedding_injective S J)
    _ = k.factorial := by
      rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_coe, hS, hJ,
        Nat.descFactorial_self]

/-- Given [the stated assumptions](hyp:hm,hfit,hr,hrq,hq,hregime,hF,hG), [Every pair of size-k matching products has a uniform planted-marginal moment bound.](goal) -/
-- @node: imageMatching_pair_moment_le
lemma imageMatching_pair_moment_le (n m : ℕ) (hm : 1 ≤ m) (hfit : 2*m ≤ n)
    (q r : ℝ) (hr : 0 < r) (hrq : r ≤ q) (hq : q ≤ 1) (hregime : q/2 ≤ m*r)
    (k : ℕ) (F G : Matching m) (hF : F.size = k) (hG : G.size = k) :
    (∫ H, (∏ e ∈ F.edges, edgeRatio q r (H (candidateArrow n m hfit e))) *
      (∏ e ∈ G.edges, edgeRatio q r (H (candidateArrow n m hfit e)))
      ∂plantedGraphLaw n m hfit q r) ≤ kappa q r ^ k * (3/2 : ℝ)^(2*k) := by
  have hH := (noisyDesign_atoms (V := Fin n) q r ⟨hr.le, hrq, hq⟩).2.1
  have h := (matching_posterior_moments n m hm hfit q r hr hrq hq
    (noisyDesign q r) hH).2.2.2.1 hregime F G k hF hG
  dsimp only at h
  dsimp only [AcquisitionLaw] at hH
  simp_rw [hH] at h
  have hs : (F.edges ∩ G.edges).card ≤ k := by
    exact (Finset.card_le_card (Finset.inter_subset_left (s₁ := F.edges) (s₂ := G.edges))).trans_eq hF
  exact h.trans (mul_le_mul
    (pow_le_pow_right₀ (kappa_ge_one_of_positive q r hr hrq hq) hs)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3/2) (Nat.sub_le _ _))
    (by positivity) (pow_nonneg (kappa_nonneg q r ⟨hr.le, hrq, hq⟩) _))

/-- Given [the stated assumptions](hyp:hm,hfit,hr,hrq,hq,hregime,hS,hJ), [Squaring the disjoint image decomposition retains every pair of donor assignments.](goal) -/
-- @node: imageProb_squared_integral_le
lemma imageProb_squared_integral_le (n m : ℕ) (hm : 1 ≤ m) (hfit : 2*m ≤ n)
    (q r : ℝ) (hr : 0 < r) (hrq : r ≤ q) (hq : q ≤ 1) (hregime : q/2 ≤ m*r)
    (k : ℕ) (S J : Finset (Fin m)) (hS : S.card = k) (hJ : J.card = k) :
    (∫ H, imageProb n m hfit q r H S J ^ 2 ∂plantedGraphLaw n m hfit q r) ≤
      (k.factorial : ℝ)^2 * activity m ^ (2*k) * kappa q r ^ k * (3/2 : ℝ)^(2*k) := by
  letI := plantedGraphLaw_probability n m hfit q r ⟨hr.le, hrq, hq⟩
  let A := Finset.univ.filter (fun F : Matching m =>
    matchingRecipients F = S ∧ donorImage F S = J)
  let W := fun (H : Acq (Fin n)) (F : Matching m) =>
    ∏ e ∈ F.edges, edgeRatio q r (H (candidateArrow n m hfit e))
  have hw (H) (F) : 0 ≤ W H F :=
    Finset.prod_nonneg (fun e _ => edgeRatio_nonneg q r ⟨hr.le, hrq, hq⟩ _)
  have hpoint (H : Acq (Fin n)) : imageProb n m hfit q r H S J ^ 2 ≤
      ∑ F ∈ A, ∑ G ∈ A, activity m ^ (2*k) * (W H F * W H G) := by
    have hp := imageProb_le_edgeProducts n m hfit q r hr hrq hq H S J
    rw [hS] at hp
    have hsq := pow_le_pow_left₀ (imageProb_mem_Icc n m hfit q r ⟨hr.le, hrq, hq⟩ H S J).1 hp 2
    refine hsq.trans_eq ?_
    change (activity m ^ k * ∑ F ∈ A, W H F)^2 = _
    rw [mul_pow, ← pow_mul, pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    simp only [Nat.mul_comm]
  calc
    _ ≤ ∫ H, ∑ F ∈ A, ∑ G ∈ A,
        activity m ^ (2*k) * (W H F * W H G) ∂plantedGraphLaw n m hfit q r :=
      integral_mono Integrable.of_finite Integrable.of_finite hpoint
    _ = ∑ F ∈ A, ∑ G ∈ A, activity m ^ (2*k) *
        ∫ H, W H F * W H G ∂plantedGraphLaw n m hfit q r := by
      rw [integral_finsetSum A (by intros; exact Integrable.of_finite)]
      apply Finset.sum_congr rfl
      intro F hF
      rw [integral_finsetSum A (by intros; exact Integrable.of_finite)]
      simp_rw [integral_const_mul]
    _ ≤ ∑ F ∈ A, ∑ G ∈ A,
        activity m ^ (2*k) * (kappa q r ^ k * (3/2 : ℝ)^(2*k)) := by
      apply Finset.sum_le_sum
      intro F hF
      apply Finset.sum_le_sum
      intro G hG
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (activity_pos m hm).le _)
      exact imageMatching_pair_moment_le n m hm hfit q r hr hrq hq hregime k F G
        ((imageMatching_size F S (Finset.mem_filter.mp hF).2.1).trans hS)
        ((imageMatching_size G S (Finset.mem_filter.mp hG).2.1).trans hS)
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : (A.card : ℝ) ≤ k.factorial := by exact_mod_cast imageMatching_count_le S J hS hJ
      have hc2 := pow_le_pow_left₀ (Nat.cast_nonneg A.card) hc 2
      have hn : 0 ≤ activity m ^ (2*k) * (kappa q r ^ k * (3/2 : ℝ)^(2*k)) := by
        apply mul_nonneg (pow_nonneg (activity_pos m hm).le _)
        exact mul_nonneg (pow_nonneg (kappa_nonneg q r ⟨hr.le, hrq, hq⟩) _) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hc2 hn]

/-- Given [the stated assumptions](hyp:hm,hfit,hr,hrq,hq,hregime,hk), [Posterior pair moments and matching counts bound every interaction order simultaneously.](goal) -/
lemma posterior_order_energy_le (n m : ℕ) (hm : 1 ≤ m) (hfit : 2*m ≤ n) (q r : ℝ)
    (hr : 0 < r) (hrq : r ≤ q) (hq : q ≤ 1) (hregime : q/2 ≤ m*r) (k : ℕ)
    (hk : k ∈ Finset.Icc 1 m) : -- @realizes k(order constrained by 1≤k≤m)
    orderEnergy n m hfit q r k ≤ ((9/64)*kappa q r)^k := by
  letI := plantedGraphLaw_probability n m hfit q r ⟨hr.le, hrq, hq⟩
  let A := Finset.univ.powerset.filter (fun S : Finset (Fin m) => S.card = k)
  have hcard : A.card = m.choose k := by
    have hA : A = Finset.univ.powersetCard k := by
      ext S
      simp [A, Finset.mem_powersetCard]
    rw [hA, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hsum : orderEnergy n m hfit q r k ≤
      (m.choose k : ℝ)^2 * (k.factorial : ℝ)^2 * activity m ^ (2*k) *
        kappa q r ^ k * (3/2 : ℝ)^(2*k) := by
    unfold orderEnergy
    change (∫ H, ∑ S ∈ A, ∑ J ∈ A, imageProb n m hfit q r H S J ^ 2
      ∂plantedGraphLaw n m hfit q r) ≤ _
    rw [integral_finsetSum A (by intros; exact Integrable.of_finite)]
    have hinner (S : Finset (Fin m)) :
        (∫ H, ∑ J ∈ A, imageProb n m hfit q r H S J ^ 2 ∂plantedGraphLaw n m hfit q r) =
          ∑ J ∈ A, ∫ H, imageProb n m hfit q r H S J ^ 2 ∂plantedGraphLaw n m hfit q r :=
      integral_finsetSum A (by intros; exact Integrable.of_finite)
    simp_rw [hinner]
    calc
      _ ≤ ∑ S ∈ A, ∑ J ∈ A,
          (k.factorial : ℝ)^2 * activity m ^ (2*k) * kappa q r ^ k * (3/2 : ℝ)^(2*k) := by
        apply Finset.sum_le_sum
        intro S hS
        apply Finset.sum_le_sum
        intro J hJ
        exact imageProb_squared_integral_le n m hm hfit q r hr hrq hq hregime k S J
          (Finset.mem_filter.mp hS).2 (Finset.mem_filter.mp hJ).2
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  have hcount : (m.choose k : ℝ) * (k.factorial : ℝ) ≤ (m : ℝ)^k := by
    have h := Nat.descFactorial_le_pow m k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    exact_mod_cast (by simpa [Nat.mul_comm] using h)
  have hcount2 := pow_le_pow_left₀ (by positivity :
    0 ≤ (m.choose k : ℝ) * (k.factorial : ℝ)) hcount 2
  have hnonneg : 0 ≤ activity m ^ (2*k) * kappa q r ^ k * (3/2 : ℝ)^(2*k) :=
    mul_nonneg (mul_nonneg (pow_nonneg (activity_pos m hm).le _)
      (pow_nonneg (kappa_nonneg q r ⟨hr.le, hrq, hq⟩) _)) (by positivity)
  calc
    _ ≤ _ := hsum
    _ ≤ ((m : ℝ)^k)^2 * activity m ^ (2*k) * kappa q r ^ k * (3/2 : ℝ)^(2*k) := by
      nlinarith [mul_le_mul_of_nonneg_right hcount2 hnonneg]
    _ = ((9/64)*kappa q r)^k := by
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      have hscale : ((m : ℝ) * activity m)^2 * kappa q r * (3/2 : ℝ)^2 =
          (9/64)*kappa q r := by
        unfold activity
        field_simp
        <;> ring
      calc
        _ = (((m : ℝ) * activity m)^2 * kappa q r * (3/2 : ℝ)^2)^k := by
          simp only [mul_pow, ← pow_mul, Nat.mul_comm]
        _ = _ := congrArg (fun x : ℝ => x^k) hscale


end CausalSmith.Experimentation.NoisygraphTtePrecision
