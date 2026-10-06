module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingProjection
/-! # Quantitative rank and protected rows in ordered rounding

The actual ordered orthonormalization preserves its input orthogonal complement.
A trace argument gives the exact constraint-plus-nullspace rank identity on active
coordinates, even for dependent rows. The live-phase rank estimate bounds each
fresh-seed row variance by four times its squared-norm energy increment. Retained
rows are fixed by every boundary move. Finite phase accumulation is separate.
-/
public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {n : ℕ}

/-- [ A test vector orthogonal to the basis sees the same coefficient before and after projection.](goal) Under [the stated conditions](hyp:hw). -/
-- @node: removeProjections_rowDot_of_orthogonal
lemma removeProjections_rowDot_of_orthogonal (bs : List (Fin n → ℝ))
    (v w : Fin n → ℝ) (hw : ∀ b ∈ bs, rowDot w b = 0) :
    rowDot w (removeProjections bs v) = rowDot w v := by
  rw [show rowDot w (removeProjections bs v) =
    rowDot (removeProjections bs v) w from dotProduct_comm _ _, removeProjections_rowDot]
  have hz : (bs.map (fun b => rowDot v b * rowDot b w)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    rw [show rowDot b w = rowDot w b from dotProduct_comm _ _, hw b hb, mul_zero]
  rw [hz, sub_zero]
  exact dotProduct_comm _ _

/-- One insertion preserves exactly the orthogonal complement of the old basis and new input. [The asserted mathematical result follows](goal). -/
-- @node: insertOrtho_orthogonal_iff
lemma insertOrtho_orthogonal_iff (bs : List (Fin n → ℝ)) (v w : Fin n → ℝ) :
    (∀ b ∈ insertOrtho bs v, rowDot w b = 0) ↔
      (∀ b ∈ bs, rowDot w b = 0) ∧ rowDot w v = 0 := by
  have hd (h : ∀ b ∈ bs, rowDot w b = 0) :
      rowDot w (removeProjections bs v) = rowDot w v :=
    removeProjections_rowDot_of_orthogonal bs v w h
  constructor
  · intro h
    have hb : ∀ b ∈ bs, rowDot w b = 0 := fun b hb =>
      h b (insertOrtho_contains_old bs v b hb)
    refine ⟨hb, ?_⟩
    by_cases hp : 0 < Real.sqrt (rowDot (removeProjections bs v) (removeProjections bs v))
    · have hn := h (fun i => removeProjections bs v i /
        Real.sqrt (rowDot (removeProjections bs v) (removeProjections bs v)))
        (by simp [insertOrtho, hp])
      have he : rowDot w (fun i => removeProjections bs v i /
          Real.sqrt (rowDot (removeProjections bs v) (removeProjections bs v))) =
          rowDot w (removeProjections bs v) /
            Real.sqrt (rowDot (removeProjections bs v) (removeProjections bs v)) := by
        simp only [rowDot, ← mul_div_assoc, ← Finset.sum_div]
      rw [he, hd hb] at hn
      exact (div_eq_zero_iff.mp hn).resolve_right hp.ne'
    · have hz : removeProjections bs v = 0 := by
        apply (rowDot_self_eq_zero_iff _).mp
        have hnon : 0 ≤ rowDot (removeProjections bs v) (removeProjections bs v) :=
          Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
        exact le_antisymm (by simpa using Real.sqrt_pos.not.mp hp) hnon
      rw [← hd hb, hz]
      simp [rowDot]
  · rintro ⟨hb, hv⟩ b hmem
    dsimp only [insertOrtho] at hmem
    split_ifs at hmem with hp
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact hb b hmem
      · rw [List.mem_singleton.mp hmem]
        simp only [rowDot, ← mul_div_assoc, ← Finset.sum_div]
        change rowDot w (removeProjections bs v) / _ = 0
        rw [hd hb, hv, zero_div]
    · exact hb b hmem

/-- [ Discarding zero residuals preserves the orthogonal complement of all input vectors.](goal) -/
-- @node: orderedOrtho_orthogonal_iff
lemma orderedOrtho_orthogonal_iff (vs : List (Fin n → ℝ)) (w : Fin n → ℝ) :
    (∀ b ∈ orderedOrtho vs, rowDot w b = 0) ↔ ∀ v ∈ vs, rowDot w v = 0 := by
  have hf (ls : List (Fin n → ℝ)) : ∀ bs,
      (∀ b ∈ ls.foldl insertOrtho bs, rowDot w b = 0) ↔
        (∀ b ∈ bs, rowDot w b = 0) ∧ ∀ v ∈ ls, rowDot w v = 0 := by
    induction ls with
    | nil => intro bs; simp
    | cons v ls ih =>
      intro bs
      rw [List.foldl_cons, ih, insertOrtho_orthogonal_iff]
      simp only [List.mem_cons, forall_eq_or_imp]
      exact and_assoc
  simpa [orderedOrtho] using hf vs []

/-- An active-supported vector pairs with a masked coordinate vector to give that coordinate. Under [the stated conditions](hyp:hw), [the asserted mathematical result follows](goal). -/
-- @node: rowDot_active_coordinate
lemma rowDot_active_coordinate (u w : Fin n → ℝ) (j : Fin n)
    (hw : ∀ i, ¬ |u i| < 1 → w i = 0) :
    rowDot w (activeMask u (fun i => if i = j then 1 else 0)) = w j := by
  classical
  have hm : activeMask u (fun i => if i = j then 1 else 0) =
      (fun i => if i = j then (if |u j| < 1 then 1 else 0) else 0) := by
    funext i
    by_cases hi : i = j
    · subst i; simp [activeMask]
    · simp [activeMask, hi]
  rw [hm]
  by_cases hj : |u j| < 1
  · simp [rowDot, hj]
  · simp [rowDot, hj, hw j hj]

/-- [ Every constructed nullspace direction is orthogonal to every constraint-basis vector.](goal) Under [the stated conditions](hyp:hb). -/
-- @node: nullspaceBasis_orthogonal_constraints
lemma nullspaceBasis_orthogonal_constraints (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) (b : Fin n → ℝ) (hb : b ∈ constraintBasis a q u) :
    ∀ v ∈ nullspaceBasis a q u, rowDot b v = 0 := by
  apply (orderedOrtho_orthogonal_iff _ b).mpr
  intro v hv
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
  rw [show rowDot b (constraintProjection a q u (fun i => if i = j then 1 else 0)) =
    rowDot (constraintProjection a q u (fun i => if i = j then 1 else 0)) b
      from dotProduct_comm _ _]
  exact removeProjections_orthogonal _ (orderedOrtho_pairwise_orthogonal _)
    (orderedOrtho_unit_length _) _ b hb

/-- [ An active-supported vector orthogonal to both constructed bases must vanish.](goal) Under [the stated conditions](hyp:hs,hc,hn). -/
-- @node: nullspaceBasis_complete_active
lemma nullspaceBasis_complete_active (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u w : Fin n → ℝ)
    (hs : ∀ i, ¬ |u i| < 1 → w i = 0)
    (hc : ∀ b ∈ constraintBasis a q u, rowDot w b = 0)
    (hn : ∀ b ∈ nullspaceBasis a q u, rowDot w b = 0) : w = 0 := by
  have hp := (orderedOrtho_orthogonal_iff _ w).mp hn
  funext j
  have hz := hp (constraintProjection a q u (fun i => if i = j then 1 else 0))
    (List.mem_map.mpr ⟨j, by simp, rfl⟩)
  rw [constraintProjection, removeProjections_rowDot_of_orthogonal _ _ _ hc,
    rowDot_active_coordinate u w j hs] at hz
  exact hz

/-- [ A unit active-supported basis resolving every active coordinate has size equal to the active
count.](goal) Under [the stated conditions](hyp:hu,hs,hz). -/
-- @node: active_complete_basis_trace
lemma active_complete_basis_trace (u : Fin n → ℝ) (bs : List (Fin n → ℝ))
    (hu : ∀ b ∈ bs, rowDot b b = 1)
    (hs : ∀ b ∈ bs, ∀ j, ¬ |u j| < 1 → b j = 0)
    (hz : ∀ j : Fin n, removeProjections bs
      (activeMask u (fun i => if i = j then 1 else 0)) = 0) :
    (activeIndices u).length = bs.length := by
  have hd (j : Fin n) : (if |u j| < 1 then (1 : ℝ) else 0) =
      (bs.map (fun b => b j * b j)).sum := by
    have he := congrFun (hz j) j
    have hm : (bs.map (fun b =>
        rowDot (activeMask u (fun i => if i = j then 1 else 0)) b * b j)) =
        bs.map (fun b => b j * b j) := by
      apply List.map_congr_left
      intro b hb
      rw [show rowDot (activeMask u (fun i => if i = j then 1 else 0)) b =
        rowDot b (activeMask u (fun i => if i = j then 1 else 0)) from dotProduct_comm _ _,
        rowDot_active_coordinate u b j (hs b hb)]
    change (if |u j| < 1 then (if j = j then (1 : ℝ) else 0) else 0) -
      (bs.map (fun b =>
        rowDot (activeMask u (fun i => if i = j then 1 else 0)) b * b j)).sum = 0 at he
    simp only [if_true, hm] at he
    linarith
  have ht : ((activeIndices u).length : ℝ) = bs.length := by
    rw [activeIndices_length_eq_trace, Finset.sum_congr rfl (fun j _ => hd j),
      basis_diagonal_trace, basis_unit_trace bs hu]
  exact_mod_cast ht

/-- The actual constraint and nullspace basis sizes sum exactly to the active-coordinate count. [The asserted mathematical result follows](goal). -/
-- @node: nullspaceBasis_rank_identity
lemma nullspaceBasis_rank_identity (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) :
    (constraintBasis a q u).length + (nullspaceBasis a q u).length =
      (activeIndices u).length := by
  let bs := constraintBasis a q u ++ nullspaceBasis a q u
  have hc : ∀ b ∈ constraintBasis a q u, ∀ i, ¬ |u i| < 1 → b i = 0 := by
    apply orderedOrtho_active_support
    intro b hb i hi
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hb
    simp [activeMask, hi]
  have hs : ∀ b ∈ bs, ∀ i, ¬ |u i| < 1 → b i = 0 := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hc b hb
    · exact nullspaceBasis_active_support a q u b hb
  have hu : ∀ b ∈ bs, rowDot b b = 1 := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact orderedOrtho_unit_length _ b hb
    · exact orderedOrtho_unit_length _ b hb
  have ho : bs.Pairwise (fun b c => rowDot b c = 0) := by
    rw [List.pairwise_append]
    exact ⟨orderedOrtho_pairwise_orthogonal _, orderedOrtho_pairwise_orthogonal _,
      fun b hb c hc => nullspaceBasis_orthogonal_constraints a q u b hb c hc⟩
  have hz (j : Fin n) : removeProjections bs
      (activeMask u (fun i => if i = j then 1 else 0)) = 0 := by
    apply nullspaceBasis_complete_active a q u
    · apply removeProjections_active_support
      · intro i hi; simp [activeMask, hi]
      · exact hs
    · intro b hb
      exact removeProjections_orthogonal bs ho hu _ b (List.mem_append_left _ hb)
    · intro b hb
      exact removeProjections_orthogonal bs ho hu _ b (List.mem_append_right _ hb)
  have ht := active_complete_basis_trace u bs hu hs hz
  simpa only [bs, List.length_append] using ht.symm

/-- [ Dependent constraints only increase the constructed nullspace rank above active count minus
row count.](goal) -/
-- @node: nullspaceBasis_rank_lower_bound
lemma nullspaceBasis_rank_lower_bound (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) :
    (activeIndices u).length - q ≤ (nullspaceBasis a q u).length := by
  have ht := nullspaceBasis_rank_identity a q u
  have hq := constraintBasis_length_le a q u
  omega

/-- Before the phase stopping threshold, the actual nullspace rank is at least one quarter of
the initial count. Under [the stated conditions](hyp:hlive), [the asserted mathematical result follows](goal). -/
-- @node: nullspaceBasis_phase_rank
lemma nullspaceBasis_phase_rank (a : Fin (n / 4) → Fin n → ℝ)
    (r : ℕ) (u : Fin n → ℝ) (hlive : r / 2 < (activeIndices u).length) :
    (r : ℝ) / 4 ≤ ((nullspaceBasis a (r / 4) u).length : ℝ) := by
  have ht := nullspaceBasis_rank_identity a (r / 4) u
  have hq := constraintBasis_length_le a (r / 4) u
  have hn : r ≤ 4 * (nullspaceBasis a (r / 4) u).length := by omega
  have hr : (r : ℝ) ≤ 4 * (nullspaceBasis a (r / 4) u).length := by exact_mod_cast hn
  linarith

/-- [ A live phase has at most four active coordinates per constructed nullspace direction.](goal) Under [the stated conditions](hyp:hlive). -/
-- @node: nullspaceBasis_phase_active_ratio
lemma nullspaceBasis_phase_active_ratio (a : Fin (n / 4) → Fin n → ℝ)
    (r : ℕ) (u : Fin n → ℝ) (hlive : r / 2 < (activeIndices u).length) :
    (activeIndices u).length ≤ 4 * (nullspaceBasis a (r / 4) u).length := by
  have ht := nullspaceBasis_rank_identity a (r / 4) u
  have hq := constraintBasis_length_le a (r / 4) u
  omega

/-- [ The fresh two-seed row variance in a live phase is bounded by four times its norm-energy
increment and squared entry bound.](goal) Under [the stated conditions](hyp:hc,hlive). -/
-- @node: roundingStep_phase_variance_energy_le
lemma roundingStep_phase_variance_energy_le (a : Fin (n / 4) → Fin n → ℝ)
    (r : ℕ) (u c : Fin n → ℝ) (Λ : ℝ) (hc : ∀ i, |c i| ≤ Λ)
    (hlive : r / 2 < (activeIndices u).length) :
    (∫ seed₁, ∫ seed₂, rowDot c (roundingStep a (r / 4) u seed₁ seed₂ - u) ^ 2
      ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) ≤
      4 * Λ ^ 2 * (∫ seed₁, ∫ seed₂,
        rowDot (roundingStep a (r / 4) u seed₁ seed₂)
          (roundingStep a (r / 4) u seed₁ seed₂) - rowDot u u
        ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) := by
  have hq : r / 4 < (activeIndices u).length := by omega
  have hne := nullspaceBasis_nonempty_of_active_count a (r / 4) u hq
  have hk : 0 < ((nullspaceBasis a (r / 4) u).length : ℝ) := by
    exact_mod_cast List.length_pos_iff.mpr hne
  have ha : ((activeIndices u).length : ℝ) ≤
      4 * (nullspaceBasis a (r / 4) u).length := by
    exact_mod_cast nullspaceBasis_phase_active_ratio a r u hlive
  have he : 0 ≤ (∫ seed₁, ∫ seed₂,
        rowDot (roundingStep a (r / 4) u seed₁ seed₂)
          (roundingStep a (r / 4) u seed₁ seed₂) - rowDot u u
        ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [roundingStep_lottery_energy_increment a (r / 4) u hne]
    exact mul_nonneg (inv_nonneg.mpr
      (nullspaceBasis_boundary_weight_sum_pos a (r / 4) u hne).le) hk.le
  have hb := roundingStep_row_variance_energy_le a (r / 4) u c Λ hc hne
  have hm := mul_le_mul_of_nonneg_left ha (mul_nonneg (sq_nonneg Λ) he)
  nlinarith

/-- [ Each constructed nullspace direction annihilates every retained original row.](goal) Under [the stated conditions](hyp:hv,hh). -/
-- @node: nullspaceBasis_retained_row_zero
lemma nullspaceBasis_retained_row_zero (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u v : Fin n → ℝ) (hv : v ∈ nullspaceBasis a q u)
    (h : Fin (n / 4)) (hh : h.val < q) : rowDot (a h) v = 0 := by
  have hc : ∀ b ∈ constraintBasis a q u, rowDot v b = 0 := by
    intro b hb
    rw [show rowDot v b = rowDot b v from dotProduct_comm _ _]
    exact nullspaceBasis_orthogonal_constraints a q u b hb v hv
  have hr := (orderedOrtho_orthogonal_iff _ v).mp hc
  have hm : activeMask u (a h) ∈ (List.range q).map (fun k =>
      activeMask u (if hk : k < n / 4 then a ⟨k, hk⟩ else 0)) := by
    exact List.mem_map.mpr ⟨h.val, List.mem_range.mpr hh, by simp [h.isLt]⟩
  have hz := hr (activeMask u (a h)) hm
  rw [show rowDot v (activeMask u (a h)) = rowDot (activeMask u (a h)) v
    from dotProduct_comm _ _, nullspaceBasis_rowDot_activeMask a q u (a h) v hv] at hz
  exact hz

/-- [ The asymmetric boundary move fixes each retained row for every seed, including empty-basis
padding.](goal) Under [the stated conditions](hyp:hh). -/
-- @node: roundingStep_retained_row_fixed
lemma roundingStep_retained_row_fixed (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) (seed₁ seed₂ : ℝ)
    (h : Fin (n / 4)) (hh : h.val < q) :
    rowDot (a h) (roundingStep a q u seed₁ seed₂) = rowDot (a h) u := by
  by_cases he : nullspaceBasis a q u = []
  · simp [roundingStep, he, inverseCDF, boundaryPlus, boundaryMinus, finiteMin,
      rowDot, activeIndices]
  · let bs := nullspaceBasis a q u
    let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
    let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed₁
    have hv : v ∈ nullspaceBasis a q u := rounding_selected_direction_mem a q u seed₁ he
    have hz := nullspaceBasis_retained_row_zero a q u v hv h hh
    change rowDot (a h) (if seed₂ < boundaryMinus u v /
      (boundaryPlus u v + boundaryMinus u v) then u + boundaryPlus u v • v
      else u - boundaryMinus u v • v) = _
    split_ifs
    · change dotProduct (a h) (u + boundaryPlus u v • v) = _
      rw [dotProduct_add, dotProduct_smul]
      change rowDot (a h) u + _ * rowDot (a h) v = _
      rw [hz, mul_zero, add_zero]
    · change dotProduct (a h) (u - boundaryMinus u v • v) = _
      rw [dotProduct_sub, dotProduct_smul]
      change rowDot (a h) u - _ * rowDot (a h) v = _
      rw [hz, mul_zero, sub_zero]
end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
