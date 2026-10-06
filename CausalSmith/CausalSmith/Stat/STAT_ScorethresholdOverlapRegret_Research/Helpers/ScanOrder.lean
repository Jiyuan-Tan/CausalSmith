module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.Estimator

/-! # Ordering of the score scan

The comparison-counting sort orders keys, and grouping ties makes this order strict.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

/-- The counted merge preserves nondecreasing score order. -/
-- @node: mergeWithCost_pairwise
lemma mergeWithCost_pairwise (xs ys : List (ℝ × ℝ))
    (hx : xs.Pairwise (fun p q => p.1 ≤ q.1))
    (hy : ys.Pairwise (fun p q => p.1 ≤ q.1)) :
    ((mergeWithCost (fun p q => decide (p.1 ≤ q.1)) xs ys).1).Pairwise
      (fun p q => p.1 ≤ q.1) := by
  fun_induction mergeWithCost (fun p q => decide (p.1 ≤ q.1)) xs ys with
  | case1 ys => exact hy
  | case2 xs hxs => exact hx
  | case3 x xs y ys h out ih =>
    obtain ⟨hxhead, hxtail⟩ := List.pairwise_cons.mp hx
    obtain ⟨hyhead, hytail⟩ := List.pairwise_cons.mp hy
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih hxtail hy⟩
    intro z hz
    rcases (mergeWithCost_mem _ _ _ z).mp hz with hz | hz
    · exact hxhead z hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact of_decide_eq_true h
      · exact (of_decide_eq_true h).trans (hyhead z hz)
  | case4 x xs y ys h out ih =>
    obtain ⟨hxhead, hxtail⟩ := List.pairwise_cons.mp hx
    obtain ⟨hyhead, hytail⟩ := List.pairwise_cons.mp hy
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih hx hytail⟩
    have hyx : y.1 ≤ x.1 := le_of_not_ge (by simpa using h)
    intro z hz
    rcases (mergeWithCost_mem _ _ _ z).mp hz with hz | hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hyx
      · exact hyx.trans (hxhead z hz)
    · exact hyhead z hz

/-- Sufficient structural fuel makes the counted sort order the score keys. -/
-- @node: mergeSortWithCostAux_pairwise
lemma mergeSortWithCostAux_pairwise (fuel : ℕ) (xs : List (ℝ × ℝ))
    (hfuel : xs.length ≤ fuel) :
    ((mergeSortWithCostAux (fun p q => decide (p.1 ≤ q.1)) fuel xs).1).Pairwise
      (fun p q => p.1 ≤ q.1) := by
  fun_induction mergeSortWithCostAux (fun p q => decide (p.1 ≤ q.1)) fuel xs with
  | case1 xs => have : xs = [] := List.length_eq_zero_iff.mp (by omega); subst xs; simp
  | case2 n => simp
  | case3 n x => simp
  | case4 fuel xs hnil hsingle halves left right merged ihL ihR =>
    have hlen : 2 ≤ xs.length := by
      cases xs with
      | nil => exact False.elim (hnil rfl)
      | cons x rest =>
        cases rest with
        | nil => exact False.elim (hsingle x rfl)
        | cons y ys => simp
    have hL : halves.1.length ≤ fuel := by
      simp [halves, List.splitAt_eq]; omega
    have hR : halves.2.length ≤ fuel := by
      simp [halves, List.splitAt_eq]; omega
    exact mergeWithCost_pairwise left.1 right.1 (ihL hL) (ihR hR)

/-- Consecutive grouping turns nondecreasing keys into strictly increasing keys. -/
-- @node: groupedScores_pairwise
lemma groupedScores_pairwise (xs : List (ℝ × ℝ))
    (hs : xs.Pairwise (fun p q => p.1 ≤ q.1)) :
    (groupedScores xs).Pairwise (fun p q => p.1 < q.1) := by
  let step : List (ℝ × ℝ) → (ℝ × ℝ) → List (ℝ × ℝ) := fun acc p =>
    match acc with
    | [] => [p]
    | q :: rest =>
      if q.1 = p.1 then (q.1, q.2 + p.2) :: rest else p :: acc
  have hfold (ys acc : List (ℝ × ℝ))
      (hs : ys.Pairwise (fun p q => p.1 ≤ q.1))
      (hacc : acc.Pairwise (fun p q => q.1 < p.1))
      (hcross : ∀ p ∈ acc, ∀ q ∈ ys, p.1 ≤ q.1) :
      (ys.foldl step acc).Pairwise (fun p q => q.1 < p.1) := by
    induction ys generalizing acc with
    | nil => exact hacc
    | cons p ys ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
      apply ih (step acc p) htail
      · cases acc with
        | nil => simp [step]
        | cons q rest =>
          obtain ⟨hq, hr⟩ := List.pairwise_cons.mp hacc
          have hqp := hcross q (by simp) p (by simp)
          by_cases heq : q.1 = p.1
          · simpa [step, heq] using hacc
          · simp only [step, heq, ↓reduceIte, List.pairwise_cons]
            refine ⟨?_, List.pairwise_cons.mp hacc⟩
            intro r hmem
            rcases List.mem_cons.mp hmem with rfl | hmem
            · exact lt_of_le_of_ne hqp heq
            · exact (hq r hmem).trans_le hqp
      · intro r hr s hsmem
        cases acc with
        | nil =>
          have hrp : r = p := by simpa [step] using hr
          subst r
          exact hhead s hsmem
        | cons q rest =>
          by_cases heq : q.1 = p.1
          · simp only [step, heq, ↓reduceIte, List.mem_cons] at hr
            rcases hr with rfl | hr
            · exact heq ▸ hhead s hsmem
            · exact hcross r (by simp [hr]) s (by simp [hsmem])
          · simp only [step, heq, ↓reduceIte, List.mem_cons] at hr
            rcases hr with rfl | hr
            · exact hhead s hsmem
            · exact hcross r (List.mem_cons.mpr hr) s (by simp [hsmem])
  have h := hfold xs [] hs (by simp) (by simp)
  change ((xs.foldl step []).reverse).Pairwise _
  exact List.pairwise_reverse.mpr h

/-- The actual scan visits distinct scores in increasing order. -/
-- @node: sortedScoreGroups_pairwise
lemma sortedScoreGroups_pairwise {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) :
    (sortedScoreGroups a e d).Pairwise (fun p q => p.1 < q.1) := by
  apply groupedScores_pairwise
  exact mergeSortWithCostAux_pairwise _ _ le_rfl

/-- Each scan entry records the prefix before, or the suffix after, one group. -/
-- @node: scoreScan_fold_witness
lemma scoreScan_fold_witness (xs : List (ℝ × ℝ)) (scale total before : ℝ)
    (acc : List ((ℝ → Bool) × ℝ)) :
    ∀ q ∈ (xs.foldl (fun state p =>
      (state.1 + p.2,
        (rightThr (clampScore p.1), scale * state.1) ::
        (leftThr (clampScore p.1), scale * (total - (state.1 + p.2))) :: state.2))
      (before, acc)).2,
      q ∈ acc ∨ ∃ pre p post, xs = pre ++ p :: post ∧
        (q = (rightThr (clampScore p.1), scale * (before + (pre.map Prod.snd).sum)) ∨
         q = (leftThr (clampScore p.1),
           scale * (total - (before + (pre.map Prod.snd).sum + p.2)))) := by
  induction xs generalizing before acc with
  | nil => intro q hq; exact Or.inl hq
  | cons p xs ih =>
    intro q hq
    obtain h | ⟨pre, r, post, hx, hq⟩ := ih (before + p.2) _ q hq
    · simp only [List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact Or.inr ⟨[], p, xs, rfl, Or.inl (by simp)⟩
      · exact Or.inr ⟨[], p, xs, rfl, Or.inr (by simp)⟩
      · exact Or.inl h
    · refine Or.inr ⟨p :: pre, r, post, by simp [hx], ?_⟩
      simpa only [List.map_cons, List.sum_cons, add_assoc] using hq

/-- At a group key, strict ordering identifies both cutoff sums with prefixes. -/
-- @node: scoreScan_cutoff_sums
lemma scoreScan_cutoff_sums (pre post : List (ℝ × ℝ)) (p : ℝ × ℝ)
    (hs : (pre ++ p :: post).Pairwise (fun p q => p.1 < q.1)) :
    ((pre ++ p :: post).map (fun r => if r.1 < p.1 then r.2 else 0)).sum =
        (pre.map Prod.snd).sum ∧
    ((pre ++ p :: post).map (fun r => if r.1 ≤ p.1 then r.2 else 0)).sum =
        (pre.map Prod.snd).sum + p.2 := by
  obtain ⟨hpre, hrest, hcross⟩ := List.pairwise_append.mp hs
  have hbefore : ∀ r ∈ pre, r.1 < p.1 := fun r hr => hcross r hr p (by simp)
  have hafter : ∀ r ∈ post, p.1 < r.1 := (List.pairwise_cons.mp hrest).1
  have hprelt : pre.map (fun r => if r.1 < p.1 then r.2 else 0) = pre.map Prod.snd := by
    apply List.map_congr_left
    intro r hr
    simp [hbefore r hr]
  have hprele : pre.map (fun r => if r.1 ≤ p.1 then r.2 else 0) = pre.map Prod.snd := by
    apply List.map_congr_left
    intro r hr
    simp [(hbefore r hr).le]
  have hpostlt : post.map (fun r => if r.1 < p.1 then r.2 else 0) = post.map (fun _ => (0:ℝ)) := by
    apply List.map_congr_left
    intro r hr
    simp [not_lt.mpr (hafter r hr).le]
  have hpostle : post.map (fun r => if r.1 ≤ p.1 then r.2 else 0) = post.map (fun _ => (0:ℝ)) := by
    apply List.map_congr_left
    intro r hr
    simp [not_le.mpr (hafter r hr)]
  simp [List.map_append, List.sum_append, hprelt, hprele, hpostlt, hpostle]

/-- The strict suffix weight is the total minus the inclusive prefix weight. -/
-- @node: scoreScan_sum_above_eq_sub
lemma scoreScan_sum_above_eq_sub (xs : List (ℝ × ℝ)) (t : ℝ) :
    (xs.map (fun p => if t < p.1 then p.2 else 0)).sum =
      (xs.map Prod.snd).sum - (xs.map (fun p => if p.1 ≤ t then p.2 else 0)).sum := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    by_cases h : p.1 ≤ t <;> simp [h, not_lt.mpr, lt_of_not_ge] <;> ring

/-- The scan's running total equals the sum of all group weights. -/
-- @node: scoreScan_total_fold
lemma scoreScan_total_fold (xs : List (ℝ × ℝ)) (s : ℝ) :
    xs.foldl (fun t p => t + p.2) s = s + (xs.map Prod.snd).sum := by
  induction xs generalizing s with
  | nil => simp
  | cons p xs ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

end CausalSmith.Stat.ScorethresholdOverlapRegret
