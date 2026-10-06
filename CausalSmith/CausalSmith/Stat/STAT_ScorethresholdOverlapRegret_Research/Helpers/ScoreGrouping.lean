module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.ScanOrder
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.SelectorMeasurability

/-! # Score-threshold overlap regret — cutoff sums of grouped scores

Grouping tied scores and sorting preserve the weighted mass on either side of
every cutoff. These identities connect the prefix scan to empirical objectives.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open scoped BigOperators

-- @node: groupedScores_key_complete
/-- Every input score remains a key after consecutive ties are grouped. -/
lemma groupedScores_key_complete (xs : List (ℝ × ℝ)) (z : ℝ)
    (hz : z ∈ xs.map Prod.fst) : z ∈ (groupedScores xs).map Prod.fst := by
  let step : List (ℝ × ℝ) → (ℝ × ℝ) → List (ℝ × ℝ) := fun acc p =>
    match acc with
    | [] => [p]
    | q :: rest =>
      if q.1 = p.1 then (q.1, q.2 + p.2) :: rest else p :: acc
  have hstep (acc : List (ℝ × ℝ)) (p : ℝ × ℝ) (z : ℝ) :
      z ∈ acc.map Prod.fst ∨ z = p.1 → z ∈ (step acc p).map Prod.fst := by
    cases acc with
    | nil => simp [step]
    | cons q rest =>
      by_cases h : q.1 = p.1
      · simp only [step, h, ↓reduceIte, List.map_cons, List.mem_cons]
        intro hz
        rcases hz with hz | hz
        · simpa only [List.map_cons, List.mem_cons] using hz
        · left; exact hz
      · simp only [step, h, ↓reduceIte, List.map_cons, List.mem_cons]
        intro hz
        rcases hz with hz | hz
        · exact Or.inr hz
        · exact Or.inl hz
  have hfold (acc ys : List (ℝ × ℝ)) (z : ℝ) :
      z ∈ acc.map Prod.fst ∨ z ∈ ys.map Prod.fst →
        z ∈ (ys.foldl step acc).map Prod.fst := by
    induction ys generalizing acc with
    | nil => simp
    | cons p rest ih =>
      intro hz
      apply ih (step acc p)
      simp only [List.map_cons, List.mem_cons] at hz
      rcases hz with hacc | hp | hrest
      · exact Or.inl (hstep acc p z (Or.inl hacc))
      · exact Or.inl (hstep acc p z (Or.inr hp))
      · exact Or.inr hrest
  have hout := hfold [] xs z (Or.inr hz)
  change z ∈ (List.map Prod.fst (List.reverse (List.foldl step [] xs)))
  simpa only [List.map_reverse, List.mem_reverse] using hout

-- @node: sortedScoreGroups_key_complete
/-- Both endpoints and every observed score occur in the grouped scan. -/
lemma sortedScoreGroups_key_complete {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (z : ℝ)
    (hz : z = 0 ∨ z = 1 ∨ ∃ i : Fin n, z = (d i).X) :
    z ∈ (sortedScoreGroups a e d).map Prod.fst := by
  unfold sortedScoreGroups
  apply groupedScores_key_complete
  obtain ⟨p, hp, rfl⟩ : ∃ p : ℝ × ℝ,
      p ∈ ([(0,0),(1,0)] ++ List.ofFn
        (fun i : Fin n => ((d i).X, zScore a e (d i)))) ∧ p.1 = z := by
    rcases hz with hzero | hone | ⟨i, hi⟩
    · exact ⟨(0,0), by simp, hzero.symm⟩
    · exact ⟨(1,0), by simp, hone.symm⟩
    · refine ⟨((d i).X, zScore a e (d i)), ?_, hi.symm⟩
      apply List.mem_append.mpr
      right
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
  apply List.mem_map.mpr
  exact ⟨p, (mergeSortWithCost_mem _ _ p).mpr hp, rfl⟩

-- @node: groupedScores_sum_at_cutoff
/-- Grouping equal keys preserves the weight at or below every cutoff. -/
lemma groupedScores_sum_at_cutoff (xs : List (ℝ × ℝ)) (t : ℝ) :
    (((groupedScores xs).map (fun p => if p.1 ≤ t then p.2 else 0)).sum : ℝ) =
      (xs.map (fun p => if p.1 ≤ t then p.2 else 0)).sum := by
  let weight : ℝ × ℝ → ℝ := fun p => if p.1 ≤ t then p.2 else 0
  let step : List (ℝ × ℝ) → (ℝ × ℝ) → List (ℝ × ℝ) := fun acc p =>
    match acc with
    | [] => [p]
    | q :: rest =>
      if q.1 = p.1 then (q.1, q.2 + p.2) :: rest else p :: acc
  have hfold (acc ys : List (ℝ × ℝ)) :
      ((ys.foldl step acc).map weight).sum =
        (acc.map weight).sum + (ys.map weight).sum := by
    induction ys generalizing acc with
    | nil => simp
    | cons p rest ih =>
      rw [List.foldl_cons, ih]
      cases acc with
      | nil => simp [step, weight]
      | cons q tail =>
        by_cases h : q.1 = p.1
        · simp only [step, h, ↓reduceIte, List.map_cons, List.sum_cons]
          simp only [weight, h]
          split_ifs <;> ring
        · simp only [step, h, ↓reduceIte, List.map_cons, List.sum_cons]
          ring
  change (((xs.foldl step []).reverse.map weight).sum : ℝ) =
    (xs.map weight).sum
  rw [List.map_reverse, List.sum_reverse]
  simpa using hfold [] xs

-- @node: sortedScoreGroups_sum_at_cutoff
/-- Sorting and grouping preserve the empirical weight at or below a cutoff. -/
lemma sortedScoreGroups_sum_at_cutoff {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (t : ℝ) :
    (((sortedScoreGroups a e d).map
      (fun p => if p.1 ≤ t then p.2 else 0)).sum : ℝ) =
      ∑ i : Fin n, if (d i).X ≤ t then zScore a e (d i) else 0 := by
  unfold sortedScoreGroups
  rw [groupedScores_sum_at_cutoff, mergeSortWithCost_sum]
  simp [List.sum_ofFn]

-- @node: groupedScores_sum_below_cutoff
/-- Grouping equal keys preserves the weight strictly below a cutoff. -/
lemma groupedScores_sum_below_cutoff (xs : List (ℝ × ℝ)) (t : ℝ) :
    (((groupedScores xs).map (fun p => if p.1 < t then p.2 else 0)).sum : ℝ) =
      (xs.map (fun p => if p.1 < t then p.2 else 0)).sum := by
  let weight : ℝ × ℝ → ℝ := fun p => if p.1 < t then p.2 else 0
  let step : List (ℝ × ℝ) → (ℝ × ℝ) → List (ℝ × ℝ) := fun acc p =>
    match acc with
    | [] => [p]
    | q :: rest =>
      if q.1 = p.1 then (q.1, q.2 + p.2) :: rest else p :: acc
  have hfold (acc ys : List (ℝ × ℝ)) :
      ((ys.foldl step acc).map weight).sum =
        (acc.map weight).sum + (ys.map weight).sum := by
    induction ys generalizing acc with
    | nil => simp
    | cons p rest ih =>
      rw [List.foldl_cons, ih]
      cases acc with
      | nil => simp [step, weight]
      | cons q tail =>
        by_cases h : q.1 = p.1
        · simp only [step, h, ↓reduceIte, List.map_cons, List.sum_cons]
          simp only [weight, h]
          split_ifs <;> ring
        · simp only [step, h, ↓reduceIte, List.map_cons, List.sum_cons]
          ring
  change (((xs.foldl step []).reverse.map weight).sum : ℝ) =
    (xs.map weight).sum
  rw [List.map_reverse, List.sum_reverse]
  simpa using hfold [] xs

-- @node: sortedScoreGroups_sum_below_cutoff
/-- Sorting and grouping preserve empirical weight strictly below a cutoff. -/
lemma sortedScoreGroups_sum_below_cutoff {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (t : ℝ) :
    (((sortedScoreGroups a e d).map
      (fun p => if p.1 < t then p.2 else 0)).sum : ℝ) =
      ∑ i : Fin n, if (d i).X < t then zScore a e (d i) else 0 := by
  unfold sortedScoreGroups
  rw [groupedScores_sum_below_cutoff, mergeSortWithCost_sum]
  simp [List.sum_ofFn]

-- @node: groupedScores_sum_above_cutoff
/-- Grouping equal keys preserves the weight strictly above a cutoff. -/
lemma groupedScores_sum_above_cutoff (xs : List (ℝ × ℝ)) (t : ℝ) :
    (((groupedScores xs).map (fun p => if t < p.1 then p.2 else 0)).sum : ℝ) =
      (xs.map (fun p => if t < p.1 then p.2 else 0)).sum := by
  let weight : ℝ × ℝ → ℝ := fun p => if t < p.1 then p.2 else 0
  let step : List (ℝ × ℝ) → (ℝ × ℝ) → List (ℝ × ℝ) := fun acc p =>
    match acc with
    | [] => [p]
    | q :: rest =>
      if q.1 = p.1 then (q.1, q.2 + p.2) :: rest else p :: acc
  have hfold (acc ys : List (ℝ × ℝ)) :
      ((ys.foldl step acc).map weight).sum =
        (acc.map weight).sum + (ys.map weight).sum := by
    induction ys generalizing acc with
    | nil => simp
    | cons p rest ih =>
      rw [List.foldl_cons, ih]
      cases acc with
      | nil => simp [step, weight]
      | cons q tail =>
        by_cases h : q.1 = p.1
        · simp only [step, h, ↓reduceIte, List.map_cons, List.sum_cons]
          simp only [weight, h]
          split_ifs <;> ring
        · simp only [step, h, ↓reduceIte, List.map_cons, List.sum_cons]
          ring
  change (((xs.foldl step []).reverse.map weight).sum : ℝ) =
    (xs.map weight).sum
  rw [List.map_reverse, List.sum_reverse]
  simpa using hfold [] xs

-- @node: sortedScoreGroups_sum_above_cutoff
/-- Sorting and grouping preserve empirical weight strictly above a cutoff. -/
lemma sortedScoreGroups_sum_above_cutoff {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (t : ℝ) :
    (((sortedScoreGroups a e d).map
      (fun p => if t < p.1 then p.2 else 0)).sum : ℝ) =
      ∑ i : Fin n, if t < (d i).X then zScore a e (d i) else 0 := by
  unfold sortedScoreGroups
  rw [groupedScores_sum_above_cutoff, mergeSortWithCost_sum]
  simp [List.sum_ofFn]

-- @node: empObjective_rightThr_grouped
/-- The grouped prefix before a cutoff is the right-threshold empirical cost. -/
lemma empObjective_rightThr_grouped {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (t : ℝ) :
    empObjective a e d (rightThr t) = (n:ℝ)⁻¹ *
      ((sortedScoreGroups a e d).map
        (fun p => if p.1 < t then p.2 else 0)).sum := by
  rw [sortedScoreGroups_sum_below_cutoff]
  simp only [empObjective, empiricalAverage, rightThr]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : t ≤ (d i).X <;> simp [h, lt_iff_not_ge]

-- @node: empObjective_leftThr_grouped
/-- The grouped suffix after a cutoff is the left-threshold empirical cost. -/
lemma empObjective_leftThr_grouped {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (t : ℝ) :
    empObjective a e d (leftThr t) = (n:ℝ)⁻¹ *
      ((sortedScoreGroups a e d).map
        (fun p => if t < p.1 then p.2 else 0)).sum := by
  rw [sortedScoreGroups_sum_above_cutoff]
  simp only [empObjective, empiricalAverage, leftThr]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (d i).X ≤ t <;> simp [h, lt_iff_not_ge]

-- @node: scannedPrefix_total
/-- The scan's running state is exactly the accumulated group weight. -/
lemma scannedPrefix_total (xs : List (ℝ × ℝ)) (before : ℝ)
    (costs : List ((ℝ → Bool) × ℝ)) (total invN : ℝ) :
    (xs.foldl (fun state p =>
      let after := state.1 + p.2
      (after, ((rightThr (clampScore p.1), invN * state.1) ::
        (leftThr (clampScore p.1), invN * (total - after)) :: state.2)))
      (before, costs)).1 = before + (xs.map Prod.snd).sum := by
  induction xs generalizing before costs with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      simpa only [add_assoc] using
        (ih (before + p.2)
          ((rightThr (clampScore p.1), invN * before) ::
            (leftThr (clampScore p.1), invN * (total - (before + p.2))) :: costs))

-- @node: scannedPolicyCosts_cutoff_mem
/-- The scan visits both orientations at every grouped score. -/
lemma scannedPolicyCosts_cutoff_mem {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (p : ℝ × ℝ)
    (hp : p ∈ sortedScoreGroups a e d) :
    (∃ c : ℝ, (leftThr (clampScore p.1), c) ∈ scannedPolicyCosts a e d) ∧
    (∃ c : ℝ, (rightThr (clampScore p.1), c) ∈ scannedPolicyCosts a e d) := by
  let groups := sortedScoreGroups a e d
  let total := groups.foldl (fun s p => s + p.2) 0
  let step : (ℝ × List ((ℝ → Bool) × ℝ)) → (ℝ × ℝ) →
      ℝ × List ((ℝ → Bool) × ℝ) := fun state p =>
    let before := state.1
    let after := before + p.2
    (after, ((rightThr (clampScore p.1), (n:ℝ)⁻¹ * before) ::
      (leftThr (clampScore p.1), (n:ℝ)⁻¹ * (total - after)) :: state.2))
  have preserved (xs : List (ℝ × ℝ)) (state : ℝ × List ((ℝ → Bool) × ℝ))
      (q : (ℝ → Bool) × ℝ) (hq : q ∈ state.2) :
      q ∈ (xs.foldl step state).2 := by
    induction xs generalizing state with
    | nil => simpa using hq
    | cons p rest ih =>
        apply ih
        simp only [step, List.mem_cons]
        exact Or.inr (Or.inr hq)
  have visited (xs : List (ℝ × ℝ)) (state : ℝ × List ((ℝ → Bool) × ℝ))
      (p : ℝ × ℝ) (hp : p ∈ xs) :
      (∃ c : ℝ, (leftThr (clampScore p.1), c) ∈ (xs.foldl step state).2) ∧
      (∃ c : ℝ, (rightThr (clampScore p.1), c) ∈ (xs.foldl step state).2) := by
    induction xs generalizing state with
    | nil => simp at hp
    | cons q rest ih =>
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp hp with rfl | hp
        · constructor
          · refine ⟨(n:ℝ)⁻¹ * (total - (state.1 + p.2)), ?_⟩
            apply preserved
            simp [step]
          · refine ⟨(n:ℝ)⁻¹ * state.1, ?_⟩
            apply preserved
            simp [step]
        · exact ih (step state q) hp
  obtain ⟨⟨cl, hl⟩, ⟨cr, hr⟩⟩ := visited groups (0, []) p hp
  constructor
  · exact ⟨cl, by simpa only [scannedPolicyCosts, groups, total,
        List.mem_append, List.mem_reverse] using Or.inr hl⟩
  · exact ⟨cr, by simpa only [scannedPolicyCosts, groups, total,
        List.mem_append, List.mem_reverse] using Or.inr hr⟩

-- @node: scannedPolicyCosts_observed_cutoff_mem
/-- Each observed score in the score space is scanned in both orientations. -/
lemma scannedPolicyCosts_observed_cutoff_mem {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (i : Fin n)
    (hi : (d i).X ∈ Set.Icc (0 : ℝ) 1) :
    (∃ c : ℝ, (leftThr (d i).X, c) ∈ scannedPolicyCosts a e d) ∧
    (∃ c : ℝ, (rightThr (d i).X, c) ∈ scannedPolicyCosts a e d) := by
  have hkey : (d i).X ∈ (sortedScoreGroups a e d).map Prod.fst :=
    sortedScoreGroups_key_complete a e d (d i).X (Or.inr (Or.inr ⟨i, rfl⟩))
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hkey
  obtain ⟨hl, hr⟩ := scannedPolicyCosts_cutoff_mem a e d p hp
  have hc : clampScore p.1 = (d i).X := by
    rw [hpe, clampScore_eq _ hi]
  simpa only [hc] using And.intro hl hr

-- @node: sortedSelector_min_of_scanned_costs_correct
/-- Exact stored scan costs reduce full-class minimization to the finite scan. -/
lemma sortedSelector_min_of_scanned_costs_correct {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation)
    (hd : ∀ i : Fin n, (d i).X ∈ Set.Icc (0:ℝ) 1)
    (hcost : ∀ q ∈ scannedPolicyCosts a e d,
      q.2 = empObjective a e d q.1)
    (π : ℝ → Bool) (hπ : π ∈ thresholdClass) :
    empObjective a e d (sortedSelector a e d) ≤ empObjective a e d π := by
  obtain ⟨q, hq, hselector, hmin⟩ := sortedSelector_scanned_min_cost a e d
  obtain ⟨ρ, hρ, hπρ⟩ := threshold_sample_candidate a e d hd π hπ
  have hcandidate : ∃ c : ℝ, (ρ, c) ∈ scannedPolicyCosts a e d := by
    rcases hρ with hfalse | htrue | ⟨j, hj⟩ | ⟨j, hj⟩
    · subst ρ
      exact ⟨_, (scannedPolicyCosts_constant_costs a e d).1⟩
    · subst ρ
      exact ⟨_, (scannedPolicyCosts_constant_costs a e d).2⟩
    · subst ρ
      exact (scannedPolicyCosts_observed_cutoff_mem a e d j (hd j)).1
    · subst ρ
      exact (scannedPolicyCosts_observed_cutoff_mem a e d j (hd j)).2
  obtain ⟨c, hc⟩ := hcandidate
  calc
    empObjective a e d (sortedSelector a e d) = q.2 := by
      rw [← hselector, hcost q hq]
    _ ≤ c := hmin (ρ, c) hc
    _ = empObjective a e d ρ := hcost (ρ, c) hc
    _ = empObjective a e d π := hπρ.symm

/-- Every cost stored by the ordered group scan is its policy's empirical objective. -/
-- @node: scannedPolicyCosts_correct
lemma scannedPolicyCosts_correct {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (hd : ∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1) :
    ∀ q ∈ scannedPolicyCosts a e d, q.2 = empObjective a e d q.1 := by
  intro q hq
  dsimp only [scannedPolicyCosts] at hq
  rw [scoreScan_total_fold] at hq
  simp only [zero_add, List.mem_append, List.mem_reverse] at hq
  rcases hq with hconstant | hscan
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hconstant
    rcases hconstant with rfl | rfl
    · exact (empObjective_constant_false a e d).symm
    · exact (empObjective_constant_true a e d).symm
  · obtain h | ⟨pre, p, post, hgroups, hq⟩ :=
      scoreScan_fold_witness _ (n:ℝ)⁻¹ _ 0 [] q hscan
    · simpa using h
    have hp : p ∈ sortedScoreGroups a e d := by rw [hgroups]; simp
    have hprange : p.1 ∈ Set.Icc (0:ℝ) 1 := by
      rcases sortedScoreGroups_key_mem a e d p hp with h | h | ⟨i, h⟩
      · rw [h]; norm_num
      · rw [h]; norm_num
      · rw [h]; exact hd i
    have hclamp := clampScore_eq p.1 hprange
    have hs := sortedScoreGroups_pairwise a e d
    rw [hgroups] at hs
    obtain ⟨hbefore, hafter⟩ := scoreScan_cutoff_sums pre post p hs
    rcases hq with rfl | rfl
    · simp only [hclamp, zero_add]
      rw [empObjective_rightThr_grouped, hgroups, hbefore]
    · simp only [hclamp, zero_add]
      rw [empObjective_leftThr_grouped, scoreScan_sum_above_eq_sub, hgroups, hafter]

/-- The selector minimizes the empirical objective over the full threshold class. -/
-- @node: sortedSelector_empObjective_le
lemma sortedSelector_empObjective_le {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (hd : ∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1)
    (π : ℝ → Bool) (hπ : π ∈ thresholdClass) :
    empObjective a e d (sortedSelector a e d) ≤ empObjective a e d π := by
  exact sortedSelector_min_of_scanned_costs_correct a e d hd
    (scannedPolicyCosts_correct a e d hd) π hπ

-- @node: prop:selector-exact
/-- Membership, exact full-class minimization, tie grouping, and joint measurability. -/
lemma sortedSelector_exact {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (ha : 0 < a ∧ a ≤ 1/4) -- @realizes a(0<a≤1/4)
    (he : Measurable (fun x : Set.Icc (0:ℝ) 1 => e x))
    (heRange : ∀ x ∈ Set.Icc (0:ℝ) 1, e x ∈ Set.Ioo (0:ℝ) 1)
    (hn : 0 < n) :
    (∀ d : Fin n → Observation,
      (∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1) →
      sortedSelector a e d ∈ thresholdClass) ∧
    (∀ d : Fin n → Observation,
      (∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1) →
      ∀ π ∈ thresholdClass,
      empObjective a e d (sortedSelector a e d) ≤ empObjective a e d π) ∧
    (∀ d : Fin n → Observation, ∀ i j : Fin n,
      (d i).X = (d j).X →
      sortedSelector a e d (d i).X = sortedSelector a e d (d j).X) ∧
    Measurable (fun dx : {d : Fin n → Observation //
        ∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1} ×
        Set.Icc (0:ℝ) 1 => sortedSelector a e dx.1.1 dx.2.1) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ (m : ℕ) (d : Fin m → Observation),
      selectorOperationCount a e d ≤
        C * (m + 2) * (Nat.log2 (m + 2) + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d _
    exact firstScannedMinimizer_mem_thresholdClass a e d
  · intro d hd π hπ
    exact sortedSelector_empObjective_le a e d (fun i => (hd i).1) π hπ
  · intro d i j hij
    exact congrArg (sortedSelector a e d) hij
  · exact sortedSelector_measurable a e he
  · exact ⟨9, by omega, fun m d => selectorOperationCount_bound a e d⟩

end CausalSmith.Stat.ScorethresholdOverlapRegret
