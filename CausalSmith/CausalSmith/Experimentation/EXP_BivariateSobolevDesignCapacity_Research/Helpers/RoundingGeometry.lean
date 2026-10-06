module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.OrderedRoundingCore

/-! # Support and nonzero directions in ordered boundary rounding

Ordered Gram--Schmidt preserves active-coordinate support and discards zero
vectors. Finite inverse-CDF sampling therefore selects a valid direction from
any nonempty constructed nullspace basis, yielding strict active-count progress.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {n : ℕ}

/-- [ Removing projections onto active-supported vectors preserves active support.](goal) Under [the stated conditions](hyp:hv,hbs). -/
-- @node: removeProjections_active_support
lemma removeProjections_active_support (u v : Fin n → ℝ) (bs : List (Fin n → ℝ))
    (hv : ∀ i, ¬|u i| < 1 → v i = 0)
    (hbs : ∀ b ∈ bs, ∀ i, ¬|u i| < 1 → b i = 0) :
    ∀ i, ¬|u i| < 1 → removeProjections bs v i = 0 := by
  intro i hi
  have hz : (bs.map (fun b => rowDot v b * b i)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    simp [hbs b hb i hi]
  simp [removeProjections, hv i hi, hz]

/-- [ Gram--Schmidt insertion cannot introduce a coordinate outside the input support.](goal) Under [the stated conditions](hyp:hv,hbs). -/
-- @node: insertOrtho_active_support
lemma insertOrtho_active_support (u v : Fin n → ℝ) (bs : List (Fin n → ℝ))
    (hv : ∀ i, ¬|u i| < 1 → v i = 0)
    (hbs : ∀ b ∈ bs, ∀ i, ¬|u i| < 1 → b i = 0) :
    ∀ b ∈ insertOrtho bs v, ∀ i, ¬|u i| < 1 → b i = 0 := by
  intro b hb i hi
  dsimp only [insertOrtho] at hb
  split_ifs at hb with hp
  · rcases List.mem_append.mp hb with hb | hb
    · exact hbs b hb i hi
    · have he := List.mem_singleton.mp hb
      rw [he]
      simp [removeProjections_active_support u v bs hv hbs i hi]
  · exact hbs b hb i hi

/-- [ Every vector returned by ordered Gram--Schmidt has the common input support.](goal) Under [the stated conditions](hyp:hvs). -/
-- @node: orderedOrtho_active_support
lemma orderedOrtho_active_support (u : Fin n → ℝ) (vs : List (Fin n → ℝ))
    (hvs : ∀ v ∈ vs, ∀ i, ¬|u i| < 1 → v i = 0) :
    ∀ b ∈ orderedOrtho vs, ∀ i, ¬|u i| < 1 → b i = 0 := by
  have hf (ls : List (Fin n → ℝ)) :
      (∀ v ∈ ls, ∀ i, ¬|u i| < 1 → v i = 0) →
      ∀ bs, (∀ b ∈ bs, ∀ i, ¬|u i| < 1 → b i = 0) →
      ∀ b ∈ ls.foldl insertOrtho bs, ∀ i, ¬|u i| < 1 → b i = 0 := by
    induction ls with
    | nil => intro _ bs hbs; exact hbs
    | cons v ls ih =>
      intro hls bs hbs
      apply ih (fun w hw => hls w (by simp [hw]))
      exact insertOrtho_active_support u v bs (hls v (by simp)) hbs
  exact hf vs hvs [] (by simp)

/-- The constructed constraint projection vanishes on inactive coordinates. [The asserted mathematical result follows](goal). -/
-- @node: constraintProjection_active_support
lemma constraintProjection_active_support (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u v : Fin n → ℝ) :
    ∀ i, ¬|u i| < 1 → constraintProjection a q u v i = 0 := by
  apply removeProjections_active_support
  · intro i hi; simp [activeMask, hi]
  · apply orderedOrtho_active_support
    intro b hb i hi
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hb
    simp [activeMask, hi]

/-- [ Every constructed nullspace basis vector is supported on active coordinates.](goal) -/
-- @node: nullspaceBasis_active_support
lemma nullspaceBasis_active_support (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) :
    ∀ b ∈ nullspaceBasis a q u, ∀ i, ¬|u i| < 1 → b i = 0 := by
  apply orderedOrtho_active_support
  intro b hb
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
  exact constraintProjection_active_support a q u _

/-- A positive residual norm makes its normalized direction nonzero. Under [the stated conditions](hyp:hp), [the asserted mathematical result follows](goal). -/
-- @node: normalized_residual_ne_zero
lemma normalized_residual_ne_zero (w : Fin n → ℝ)
    (hp : 0 < Real.sqrt (rowDot w w)) :
    (fun i => w i / Real.sqrt (rowDot w w)) ≠ 0 := by
  intro hz
  have hw : w = 0 := by
    funext i
    have hi := congrFun hz i
    have hd : Real.sqrt (rowDot w w) ≠ 0 := ne_of_gt hp
    exact (div_eq_zero_iff.mp hi).resolve_right hd
  subst w
  simpa [rowDot] using hp

/-- [ The insertion rule preserves nonzero old directions and adds only a nonzero residual.](goal) Under [the stated conditions](hyp:hbs). -/
-- @node: insertOrtho_nonzero
lemma insertOrtho_nonzero (bs : List (Fin n → ℝ)) (v : Fin n → ℝ)
    (hbs : ∀ b ∈ bs, b ≠ 0) : ∀ b ∈ insertOrtho bs v, b ≠ 0 := by
  intro b hb
  dsimp only [insertOrtho] at hb
  split_ifs at hb with hp
  · rcases List.mem_append.mp hb with hb | hb
    · exact hbs b hb
    · rw [List.mem_singleton.mp hb]
      exact normalized_residual_ne_zero _ hp
  · exact hbs b hb

/-- Zero residuals are discarded throughout the structural Gram--Schmidt fold. [The asserted mathematical result follows](goal). -/
-- @node: orderedOrtho_nonzero
lemma orderedOrtho_nonzero (vs : List (Fin n → ℝ)) :
    ∀ b ∈ orderedOrtho vs, b ≠ 0 := by
  have hf (ls : List (Fin n → ℝ)) :
      ∀ bs, (∀ b ∈ bs, b ≠ 0) → ∀ b ∈ ls.foldl insertOrtho bs, b ≠ 0 := by
    induction ls with
    | nil => intro bs hbs; exact hbs
    | cons v ls ih =>
      intro bs hbs
      exact ih (insertOrtho bs v) (insertOrtho_nonzero bs v hbs)
  exact hf vs [] (by simp)

/-- Normalization gives the unit squared length used in the covariance trace. Under [the stated conditions](hyp:hp), [the asserted mathematical result follows](goal). -/
-- @node: normalized_residual_rowDot
lemma normalized_residual_rowDot (w : Fin n → ℝ)
    (hp : 0 < Real.sqrt (rowDot w w)) :
    rowDot (fun i => w i / Real.sqrt (rowDot w w))
      (fun i => w i / Real.sqrt (rowDot w w)) = 1 := by
  have hn : 0 ≤ rowDot w w := Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  have hs := Real.sq_sqrt hn
  have hd : Real.sqrt (rowDot w w) ≠ 0 := ne_of_gt hp
  unfold rowDot
  simp only [div_mul_div_comm, ← Finset.sum_div]
  rw [← pow_two]
  change rowDot w w / Real.sqrt (rowDot w w) ^ 2 = 1
  rw [hs]
  exact div_self (by nlinarith [sq_pos_of_ne_zero hd])

/-- [ Every inserted Gram--Schmidt residual has unit squared length.](goal) Under [the stated conditions](hyp:hbs). -/
-- @node: insertOrtho_unit_length
lemma insertOrtho_unit_length (bs : List (Fin n → ℝ)) (v : Fin n → ℝ)
    (hbs : ∀ b ∈ bs, rowDot b b = 1) :
    ∀ b ∈ insertOrtho bs v, rowDot b b = 1 := by
  intro b hb
  dsimp only [insertOrtho] at hb
  split_ifs at hb with hp
  · rcases List.mem_append.mp hb with hb | hb
    · exact hbs b hb
    · rw [List.mem_singleton.mp hb]
      exact normalized_residual_rowDot _ hp
  · exact hbs b hb

/-- All output directions of the ordered Gram--Schmidt construction are unit vectors. [The asserted mathematical result follows](goal). -/
-- @node: orderedOrtho_unit_length
lemma orderedOrtho_unit_length (vs : List (Fin n → ℝ)) :
    ∀ b ∈ orderedOrtho vs, rowDot b b = 1 := by
  have hf (ls : List (Fin n → ℝ)) :
      ∀ bs, (∀ b ∈ bs, rowDot b b = 1) →
      ∀ b ∈ ls.foldl insertOrtho bs, rowDot b b = 1 := by
    induction ls with
    | nil => intro bs hbs; exact hbs
    | cons v ls ih =>
      intro bs hbs
      exact ih (insertOrtho bs v) (insertOrtho_unit_length bs v hbs)
  exact hf vs [] (by simp)

/-- [ Each inverse boundary-product weight in the actual nullspace basis is positive.](goal) -/
-- @node: nullspaceBasis_boundary_weight_pos
lemma nullspaceBasis_boundary_weight_pos (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) :
    ∀ b ∈ nullspaceBasis a q u, 0 < (boundaryPlus u b * boundaryMinus u b)⁻¹ := by
  intro b hb
  have hs : ∀ i, b i ≠ 0 → |u i| < 1 := by
    intro i hi
    by_contra hn
    exact hi (nullspaceBasis_active_support a q u b hb i hn)
  have hn := orderedOrtho_nonzero _ b hb
  exact inv_pos.mpr (mul_pos (boundaryPlus_pos u b hs hn) (boundaryMinus_pos u b hs hn))

/-- The finite basis-sampling normalizer is strictly positive whenever a direction exists. Under [the stated conditions](hyp:hne), [the asserted mathematical result follows](goal). -/
-- @node: nullspaceBasis_boundary_weight_sum_pos
lemma nullspaceBasis_boundary_weight_sum_pos (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) (hne : nullspaceBasis a q u ≠ []) :
    0 < ((nullspaceBasis a q u).map
      (fun b => (boundaryPlus u b * boundaryMinus u b)⁻¹)).sum := by
  have hp := nullspaceBasis_boundary_weight_pos a q u
  cases he : nullspaceBasis a q u with
  | nil => exact (hne he).elim
  | cons b bs =>
    have hb : 0 < (boundaryPlus u b * boundaryMinus u b)⁻¹ := hp b (by rw [he]; simp)
    have ht : 0 ≤ (bs.map (fun b => (boundaryPlus u b * boundaryMinus u b)⁻¹)).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      exact (hp v (by rw [he]; simp [hv])).le
    simpa only [List.map_cons, List.sum_cons] using add_pos_of_pos_of_nonneg hb ht

/-- [ Sampling a nonempty finite distribution always returns one of its directions,
including seeds at interval ties and at the final endpoint.](goal) Under [the stated conditions](hyp:hne). -/
-- @node: inverseCDF_mem_directions
lemma inverseCDF_mem_directions (xs : List ((Fin n → ℝ) × ℝ))
    (hne : xs ≠ []) (t : ℝ) : inverseCDF xs t ∈ xs.map Prod.fst := by
  induction xs generalizing t with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
    cases xs with
    | nil => simp [inverseCDF]
    | cons y ys =>
      simp only [inverseCDF]
      split_ifs
      · simp
      · exact List.mem_cons_of_mem _ (ih (by simp) _)

/-- [ Any nonempty nullspace basis makes the actual move preserve the cube and
strictly decrease the active count; no seed restrictions or generic rank are needed.](goal) Under [the stated conditions](hyp:hu,hne). -/
-- @node: roundingStep_progress_of_nonempty_basis
lemma roundingStep_progress_of_nonempty_basis (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) (seed₁ seed₂ : ℝ)
    (hu : ∀ i, |u i| ≤ 1) (hne : nullspaceBasis a q u ≠ []) :
    (∀ i, |roundingStep a q u seed₁ seed₂ i| ≤ 1) ∧
    (activeIndices (roundingStep a q u seed₁ seed₂)).length <
      (activeIndices u).length := by
  let bs := nullspaceBasis a q u
  let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
  let xs := bs.zip (ws.map (fun w => w / ws.sum))
  have hlen : (ws.map (fun w => w / ws.sum)).length = bs.length := by
    simp [ws]
  have hxne : xs ≠ [] := by
    intro hz
    have hl : xs.length = bs.length := by simp [xs, hlen]
    rw [hz] at hl
    exact hne (by simpa using hl.symm)
  have hfst : xs.map Prod.fst = bs := by
    exact List.map_fst_zip hlen.ge
  have hm : inverseCDF xs seed₁ ∈ bs := by
    rw [← hfst]
    exact inverseCDF_mem_directions xs hxne seed₁
  apply roundingStep_progress_of_direction a q u seed₁ seed₂ hu
  · intro i hi
    by_contra hn
    exact hi (nullspaceBasis_active_support a q u _ hm i hn)
  · exact orderedOrtho_nonzero _ _ hm

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
