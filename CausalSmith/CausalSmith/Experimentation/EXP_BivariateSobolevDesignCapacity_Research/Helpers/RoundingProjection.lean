module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingLottery

/-! # Projection contraction for the constructed rounding basis

Ordered Gram--Schmidt produces orthogonal unit directions. Its residual energy
identity bounds the basis quadratic form by the active-coordinate row energy.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {n : ℕ}

/-- [ Dotting a finite projection residual distributes over its basis list.](goal) -/
-- @node: removeProjections_rowDot
lemma removeProjections_rowDot (bs : List (Fin n → ℝ)) (v b : Fin n → ℝ) :
    rowDot (removeProjections bs v) b = rowDot v b -
      (bs.map (fun c => rowDot v c * rowDot c b)).sum := by
  induction bs with
  | nil => simp [removeProjections_nil]
  | cons c bs ih =>
    have he : removeProjections (c :: bs) v =
        removeProjections bs v - rowDot v c • c := by
      funext i
      simp only [removeProjections, List.map_cons, List.sum_cons,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he]
    change dotProduct (removeProjections bs v - rowDot v c • c) b = _
    rw [sub_dotProduct, smul_dotProduct]
    change rowDot (removeProjections bs v) b - rowDot v c * rowDot c b = _
    rw [ih]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- An orthogonal unit list extracts the coefficient of each member exactly. Under [the stated conditions](hyp:ho,hu), [the asserted mathematical result follows](goal). -/
-- @node: orthogonal_list_coefficient
lemma orthogonal_list_coefficient (bs : List (Fin n → ℝ))
    (ho : bs.Pairwise (fun b c => rowDot b c = 0))
    (hu : ∀ b ∈ bs, rowDot b b = 1) (v : Fin n → ℝ) :
    ∀ b ∈ bs, (bs.map (fun c => rowDot v c * rowDot c b)).sum = rowDot v b := by
  induction bs with
  | nil => simp
  | cons c bs ih =>
    obtain ⟨hc, ht⟩ := List.pairwise_cons.mp ho
    intro b hb
    rcases List.mem_cons.mp hb with he | hb
    · subst b
      have hz : (bs.map (fun b => rowDot v b * rowDot b c)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        have hbc : rowDot b c = 0 := by
          change dotProduct b c = 0
          rw [dotProduct_comm]
          exact hc b hb
        simp [hbc]
      simp [hu c (by simp), hz]
    · have htail := ih ht (fun b hb => hu b (by simp [hb])) b hb
      simp [hc b hb, htail]

/-- [ The residual is orthogonal to every direction already in the basis.](goal) Under [the stated conditions](hyp:ho,hu). -/
-- @node: removeProjections_orthogonal
lemma removeProjections_orthogonal (bs : List (Fin n → ℝ))
    (ho : bs.Pairwise (fun b c => rowDot b c = 0))
    (hu : ∀ b ∈ bs, rowDot b b = 1) (v : Fin n → ℝ) :
    ∀ b ∈ bs, rowDot (removeProjections bs v) b = 0 := by
  intro b hb
  rw [removeProjections_rowDot, orthogonal_list_coefficient bs ho hu v b hb, sub_self]

/-- [ Gram--Schmidt insertion preserves orthogonality, including discarded residuals.](goal) Under [the stated conditions](hyp:ho,hu). -/
-- @node: insertOrtho_pairwise_orthogonal
lemma insertOrtho_pairwise_orthogonal (bs : List (Fin n → ℝ)) (v : Fin n → ℝ)
    (ho : bs.Pairwise (fun b c => rowDot b c = 0))
    (hu : ∀ b ∈ bs, rowDot b b = 1) :
    (insertOrtho bs v).Pairwise (fun b c => rowDot b c = 0) := by
  dsimp only [insertOrtho]
  split_ifs with hp
  · rw [List.pairwise_append]
    refine ⟨ho, by simp, ?_⟩
    intro b hb c hc
    rw [List.mem_singleton.mp hc]
    have hz := removeProjections_orthogonal bs ho hu v b hb
    have hr : rowDot b (removeProjections bs v) = 0 := by
      change dotProduct b (removeProjections bs v) = 0
      rw [dotProduct_comm]
      exact hz
    simp only [rowDot, ← mul_div_assoc, ← Finset.sum_div]
    change rowDot b (removeProjections bs v) / _ = 0
    rw [hr, zero_div]
  · exact ho

/-- The actual ordered construction yields pairwise orthogonal directions. [The asserted mathematical result follows](goal). -/
-- @node: orderedOrtho_pairwise_orthogonal
lemma orderedOrtho_pairwise_orthogonal (vs : List (Fin n → ℝ)) :
    (orderedOrtho vs).Pairwise (fun b c => rowDot b c = 0) := by
  have hf (ls : List (Fin n → ℝ)) : ∀ bs,
      bs.Pairwise (fun b c => rowDot b c = 0) →
      (∀ b ∈ bs, rowDot b b = 1) →
      (ls.foldl insertOrtho bs).Pairwise (fun b c => rowDot b c = 0) := by
    induction ls with
    | nil => intro bs ho _; exact ho
    | cons v ls ih =>
      intro bs ho hu
      exact ih (insertOrtho bs v) (insertOrtho_pairwise_orthogonal bs v ho hu)
        (insertOrtho_unit_length bs v hu)
  exact hf vs [] (by simp) (by simp)

/-- Pythagoras for the explicit residual accounts for every basis coefficient. Under [the stated conditions](hyp:ho,hu), [the asserted mathematical result follows](goal). -/
-- @node: removeProjections_energy_identity
lemma removeProjections_energy_identity (bs : List (Fin n → ℝ))
    (ho : bs.Pairwise (fun b c => rowDot b c = 0))
    (hu : ∀ b ∈ bs, rowDot b b = 1) (v : Fin n → ℝ) :
    rowDot (removeProjections bs v) (removeProjections bs v) +
      (bs.map (fun b => rowDot v b ^ 2)).sum = rowDot v v := by
  induction bs with
  | nil => simp [removeProjections_nil]
  | cons c bs ih =>
    obtain ⟨hc, ht⟩ := List.pairwise_cons.mp ho
    have he : removeProjections (c :: bs) v =
        removeProjections bs v - rowDot v c • c := by
      funext i
      simp only [removeProjections, List.map_cons, List.sum_cons,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hz : (bs.map (fun b => rowDot v b * rowDot b c)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      have hbc : rowDot b c = 0 := by
        change dotProduct b c = 0
        rw [dotProduct_comm]
        exact hc b hb
      simp [hbc]
    have hd : rowDot (removeProjections bs v) c = rowDot v c := by
      rw [removeProjections_rowDot, hz, sub_zero]
    have hd' : rowDot c (removeProjections bs v) = rowDot v c := by
      change dotProduct c (removeProjections bs v) = _
      rw [dotProduct_comm]
      exact hd
    have hi := ih ht (fun b hb => hu b (by simp [hb]))
    rw [he]
    change dotProduct (removeProjections bs v - rowDot v c • c)
      (removeProjections bs v - rowDot v c • c) + _ = _
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    change rowDot (removeProjections bs v) (removeProjections bs v) -
      rowDot v c * rowDot c (removeProjections bs v) -
      (rowDot v c * (rowDot (removeProjections bs v) c -
        rowDot v c * rowDot c c)) + _ = _
    rw [hd, hd', hu c (by simp)]
    simp only [List.map_cons, List.sum_cons]
    nlinarith [hi]

/-- [ Nonnegative residual energy gives Bessel contraction for the explicit list.](goal) Under [the stated conditions](hyp:ho,hu). -/
-- @node: orthogonal_list_bessel
lemma orthogonal_list_bessel (bs : List (Fin n → ℝ))
    (ho : bs.Pairwise (fun b c => rowDot b c = 0))
    (hu : ∀ b ∈ bs, rowDot b b = 1) (v : Fin n → ℝ) :
    (bs.map (fun b => rowDot v b ^ 2)).sum ≤ rowDot v v := by
  have he := removeProjections_energy_identity bs ho hu v
  have hn : 0 ≤ rowDot (removeProjections bs v) (removeProjections bs v) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  linarith

/-- The actual nullspace basis contracts every test-row quadratic form. [The asserted mathematical result follows](goal). -/
-- @node: nullspaceBasis_bessel
lemma nullspaceBasis_bessel (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u c : Fin n → ℝ) :
    ((nullspaceBasis a q u).map (fun v => rowDot c v ^ 2)).sum ≤ rowDot c c := by
  exact orthogonal_list_bessel _ (orderedOrtho_pairwise_orthogonal _)
    (orderedOrtho_unit_length _) c

/-- Inactive coordinates contribute no coefficient against any nullspace direction. Under [the stated conditions](hyp:hv), [the asserted mathematical result follows](goal). -/
-- @node: nullspaceBasis_rowDot_activeMask
lemma nullspaceBasis_rowDot_activeMask (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u c : Fin n → ℝ) (v : Fin n → ℝ)
    (hv : v ∈ nullspaceBasis a q u) : rowDot (activeMask u c) v = rowDot c v := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : |u i| < 1
  · simp [activeMask, hi]
  · simp [activeMask, hi, nullspaceBasis_active_support a q u v hv i hi]

/-- Projection contraction can be localized to the current active coordinates. [The asserted mathematical result follows](goal). -/
-- @node: nullspaceBasis_active_bessel
lemma nullspaceBasis_active_bessel (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u c : Fin n → ℝ) :
    ((nullspaceBasis a q u).map (fun v => rowDot c v ^ 2)).sum ≤
      rowDot (activeMask u c) (activeMask u c) := by
  have he : (nullspaceBasis a q u).map (fun v => rowDot c v ^ 2) =
      (nullspaceBasis a q u).map (fun v => rowDot (activeMask u c) v ^ 2) := by
    apply List.map_congr_left
    intro v hv
    rw [nullspaceBasis_rowDot_activeMask a q u c v hv]
  rw [he]
  exact nullspaceBasis_bessel a q u (activeMask u c)

/-- A bounded test row has at most one squared-entry budget per active coordinate. Under [the stated conditions](hyp:hc), [the asserted mathematical result follows](goal). -/
-- @node: activeMask_row_energy_le
lemma activeMask_row_energy_le (u c : Fin n → ℝ) (Λ : ℝ)
    (hc : ∀ i, |c i| ≤ Λ) :
    rowDot (activeMask u c) (activeMask u c) ≤ Λ ^ 2 * (activeIndices u).length := by
  rw [activeIndices_length_eq_trace, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : |u i| < 1
  · simp only [activeMask, if_pos hi, mul_one]
    have hab := hc i
    have hs := mul_self_le_mul_self (abs_nonneg (c i)) hab
    simpa only [← pow_two, sq_abs] using hs
  · simp [activeMask, hi]

/-- [ The roadmap's localized projection quadratic bound holds for the actual basis.](goal) Under [the stated conditions](hyp:hc). -/
-- @node: nullspaceBasis_bounded_row_energy
lemma nullspaceBasis_bounded_row_energy (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u c : Fin n → ℝ) (Λ : ℝ) (hc : ∀ i, |c i| ≤ Λ) :
    ((nullspaceBasis a q u).map (fun v => rowDot c v ^ 2)).sum ≤
      Λ ^ 2 * (activeIndices u).length := by
  exact (nullspaceBasis_active_bessel a q u c).trans (activeMask_row_energy_le u c Λ hc)

/-- [ Each actual two-seed row variance is bounded by gamma times active row energy.](goal) Under [the stated conditions](hyp:hc,hne). -/
-- @node: roundingStep_lottery_row_variance_le
lemma roundingStep_lottery_row_variance_le (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u c : Fin n → ℝ) (Λ : ℝ) (hc : ∀ i, |c i| ≤ Λ)
    (hne : nullspaceBasis a q u ≠ []) :
    (∫ seed₁, ∫ seed₂, rowDot c (roundingStep a q u seed₁ seed₂ - u) ^ 2
      ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) ≤
        ((nullspaceBasis a q u).map
          (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)).sum⁻¹ *
        (Λ ^ 2 * (activeIndices u).length) := by
  rw [roundingStep_lottery_row_variance a q u c hne]
  exact mul_le_mul_of_nonneg_left (nullspaceBasis_bounded_row_energy a q u c Λ hc)
    (inv_nonneg.mpr (nullspaceBasis_boundary_weight_sum_pos a q u hne).le)

/-- [ The actual row variance and norm increment obey the same gamma-weighted
budget, with the constructed basis length retained explicitly.](goal) Under [the stated conditions](hyp:hc,hne). -/
-- @node: roundingStep_row_variance_energy_le
lemma roundingStep_row_variance_energy_le (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u c : Fin n → ℝ) (Λ : ℝ) (hc : ∀ i, |c i| ≤ Λ)
    (hne : nullspaceBasis a q u ≠ []) :
    (∫ seed₁, ∫ seed₂, rowDot c (roundingStep a q u seed₁ seed₂ - u) ^ 2
      ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) *
        (nullspaceBasis a q u).length ≤
      (Λ ^ 2 * (activeIndices u).length) *
        (∫ seed₁, ∫ seed₂,
          rowDot (roundingStep a q u seed₁ seed₂) (roundingStep a q u seed₁ seed₂) -
            rowDot u u
          ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [roundingStep_lottery_energy_increment a q u hne]
  have hb := mul_le_mul_of_nonneg_right
    (roundingStep_lottery_row_variance_le a q u c Λ hc hne)
    (show 0 ≤ ((nullspaceBasis a q u).length : ℝ) by positivity)
  calc
    _ ≤ _ := hb
    _ = _ := by ring

/-- [ Only initially active coordinates can spend endpoint norm energy; their
combined increase is bounded by the phase's initial count.](goal) Under [the stated conditions](hyp:hw,hfix). -/
-- @node: active_endpoint_energy_le
lemma active_endpoint_energy_le (u w : Fin n → ℝ)
    (hw : ∀ i, |w i| ≤ 1) (hfix : ∀ i, ¬ |u i| < 1 → w i = u i) :
    rowDot w w - rowDot u u ≤ (activeIndices u).length := by
  rw [activeIndices_length_eq_trace]
  unfold rowDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : |u i| < 1
  · simp only [if_pos hi]
    have hs := mul_self_le_mul_self (abs_nonneg (w i)) (hw i)
    have hs' : w i * w i ≤ 1 := by simpa only [← pow_two, sq_abs, one_pow] using hs
    nlinarith [mul_self_nonneg (u i)]
  · simp [hi, hfix i hi]

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
