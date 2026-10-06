module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Basic

/-! # Score-threshold overlap regret — selector and localized process

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

-- @env: S5
variable (P : RowLaw)
variable (a : {a : ℝ // 0 < a ∧ a ≤ 1/4}) -- @realizes a(standing deletion-level range 0<a≤1/4)
variable (z : {z : ℝ // 0 < z}) -- @realizes z(standing localization radius z>0)

/-- Tie-favoring offset. -/
noncomputable def offsetG (a : ℝ) (e : ℝ → ℝ) (x : ℝ) : ℝ :=
  min 1 (a / min (e x) (1-e x)) -- @realizes ga(g_a=min(1,a/p))

/-- Whole-observation deleted inverse-propensity contrast. -/
noncomputable def gammaScore (a : ℝ) (e : ℝ → ℝ) (o : Observation) : ℝ :=
  if a ≤ min (e o.X) (1-e o.X) then
    (if o.A then o.Y / e o.X else -(o.Y / (1-e o.X))) else 0 -- @realizes Gammaa(deleted IPW contrast)

/-- Regularized observable score. -/
noncomputable def zScore (a : ℝ) (e : ℝ → ℝ) (o : Observation) : ℝ :=
  gammaScore a e o + offsetG a e o.X -- @realizes Za(Gamma_a+g_a)

/-- Empirical negative-action objective. -/
noncomputable def empObjective {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (π : ℝ → Bool) : ℝ :=
  empiricalAverage (fun o => (if π o.X then (0:ℝ) else 1) * zScore a e o) d -- @realizes Jhata(P_n[(1-pi)Z_a])

/-- Consecutive equal scores are accumulated in one pass after sorting. -/
noncomputable def groupedScores (xs : List (ℝ × ℝ)) : List (ℝ × ℝ) :=
  (xs.foldl (fun acc p =>
    match acc with
    | [] => [p]
    | q :: rest =>
      if q.1 = p.1 then (q.1, q.2 + p.2) :: rest else p :: acc) []).reverse

-- @node: groupedScores_sum
/-- Grouping equal score keys preserves the sum of their observable weights. -/
lemma groupedScores_sum (xs : List (ℝ × ℝ)) :
    ((groupedScores xs).map Prod.snd).sum = (xs.map Prod.snd).sum := by
  let step : List (ℝ × ℝ) → (ℝ × ℝ) → List (ℝ × ℝ) := fun acc p =>
    match acc with
    | [] => [p]
    | q :: rest =>
      if q.1 = p.1 then (q.1, q.2 + p.2) :: rest else p :: acc
  have hfold (acc xs : List (ℝ × ℝ)) :
      (((xs.foldl step acc).map Prod.snd).sum : ℝ) =
        (acc.map Prod.snd).sum + (xs.map Prod.snd).sum := by
    induction xs generalizing acc with
    | nil => simp
    | cons p rest ih =>
      rw [List.foldl_cons, ih]
      cases acc with
      | nil => simp [step]
      | cons q tail =>
        simp only [List.map_cons, List.sum_cons]
        dsimp [step]
        split_ifs <;> simp [add_assoc, add_left_comm, add_comm]
  simpa [groupedScores, step, List.sum_reverse] using hfold [] xs

-- @node: groupedScores_key_mem
/-- Tie grouping keeps every score key in the input list. -/
lemma groupedScores_key_mem (xs : List (ℝ × ℝ)) (p : ℝ × ℝ)
    (hp : p ∈ groupedScores xs) : p.1 ∈ xs.map Prod.fst := by
  let step : List (ℝ × ℝ) → (ℝ × ℝ) → List (ℝ × ℝ) := fun acc p =>
    match acc with
    | [] => [p]
    | q :: rest =>
      if q.1 = p.1 then (q.1, q.2 + p.2) :: rest else p :: acc
  have hstep (acc : List (ℝ × ℝ)) (p : ℝ × ℝ) (z : ℝ) :
      z ∈ (step acc p).map Prod.fst ↔
        z ∈ acc.map Prod.fst ∨ z = p.1 := by
    cases acc with
    | nil => simp [step]
    | cons q rest =>
      by_cases h : q.1 = p.1
      · simp only [step, h, ↓reduceIte, List.map_cons, List.mem_cons]
        tauto
      · simp only [step, h, ↓reduceIte, List.map_cons, List.mem_cons]
        tauto
  have hfold (acc ys : List (ℝ × ℝ)) (z : ℝ) :
      z ∈ ((ys.foldl step acc).map Prod.fst) ↔
        z ∈ acc.map Prod.fst ∨ z ∈ ys.map Prod.fst := by
    induction ys generalizing acc with
    | nil => simp
    | cons q rest ih =>
      rw [List.foldl_cons, ih, hstep]
      simp only [List.map_cons, List.mem_cons]
      tauto
  have hmem : p ∈ xs.foldl step [] := by
    simpa only [groupedScores, step, List.mem_reverse] using hp
  have hkey : p.1 ∈ ((xs.foldl step []).map Prod.fst) :=
    List.mem_map.mpr ⟨p, hmem, rfl⟩
  exact (hfold [] xs p.1).mp hkey |>.resolve_left (by simp)

/-- Merge with the exact number of score comparisons. -/
def mergeWithCost {α : Type} (le : α → α → Bool) :
    List α → List α → List α × ℕ
  | [], ys => (ys, 0)
  | xs, [] => (xs, 0)
  | x :: xs, y :: ys =>
    if le x y then
      let out := mergeWithCost le xs (y :: ys)
      (x :: out.1, out.2 + 1)
    else
      let out := mergeWithCost le (x :: xs) ys
      (y :: out.1, out.2 + 1)
termination_by xs ys => xs.length + ys.length

/-- Stable merge sort paired with its actual comparison count, using structural fuel. -/
def mergeSortWithCostAux {α : Type} (le : α → α → Bool) :
    ℕ → List α → List α × ℕ
  | 0, xs => (xs, 0)
  | _ + 1, [] => ([], 0)
  | _ + 1, [x] => ([x], 0)
  | fuel + 1, xs =>
    let halves := xs.splitAt ((xs.length + 1) / 2)
    let left := mergeSortWithCostAux le fuel halves.1
    let right := mergeSortWithCostAux le fuel halves.2
    let merged := mergeWithCost le left.1 right.1
    (merged.1, left.2 + right.2 + merged.2)

def mergeSortWithCost {α : Type} (xs : List α) (le : α → α → Bool) :
    List α × ℕ :=
  mergeSortWithCostAux le xs.length xs

-- @node: mergeWithCost_mem
/-- A merge introduces no new list entries. -/
lemma mergeWithCost_mem {α : Type} (le : α → α → Bool)
    (xs ys : List α) (z : α) :
    z ∈ (mergeWithCost le xs ys).1 ↔ z ∈ xs ∨ z ∈ ys := by
  fun_induction mergeWithCost le xs ys with
  | case1 ys => simp
  | case2 xs hxs => simp
  | case3 x xs y ys h out ih =>
    simp only [List.mem_cons]
    dsimp [out]
    rw [ih]
    simp only [List.mem_cons]
    tauto
  | case4 x xs y ys out h ih =>
    simp only [List.mem_cons]
    dsimp [h]
    rw [ih]
    simp only [List.mem_cons]
    tauto

-- @node: mergeSortWithCostAux_mem
/-- Every entry produced by the structural sort came from its input. -/
lemma mergeSortWithCostAux_mem {α : Type} (le : α → α → Bool)
    (fuel : ℕ) (xs : List α) (z : α) :
    z ∈ (mergeSortWithCostAux le fuel xs).1 ↔ z ∈ xs := by
  fun_induction mergeSortWithCostAux le fuel xs with
  | case1 xs => rfl
  | case2 n => rfl
  | case3 n x => rfl
  | case4 fuel xs hnil hsingle halves left right merged ihL ihR =>
    have hsplit : halves.1 ++ halves.2 = xs := by
      simpa [halves, List.splitAt_eq] using
        List.take_append_drop ((xs.length + 1) / 2) xs
    rw [mergeWithCost_mem le left.1 right.1 z, ihL, ihR]
    rw [← hsplit, List.mem_append]

-- @node: mergeSortWithCost_mem
/-- The comparison-counting sort preserves list membership. -/
lemma mergeSortWithCost_mem {α : Type} (le : α → α → Bool)
    (xs : List α) (z : α) :
    z ∈ (mergeSortWithCost xs le).1 ↔ z ∈ xs := by
  exact mergeSortWithCostAux_mem le xs.length xs z

-- @node: mergeWithCost_sum
/-- Merging preserves the sum of an arbitrary real-valued weight. -/
lemma mergeWithCost_sum {α : Type} (le : α → α → Bool)
    (f : α → ℝ) (xs ys : List α) :
    (((mergeWithCost le xs ys).1.map f).sum : ℝ) =
      (xs.map f).sum + (ys.map f).sum := by
  fun_induction mergeWithCost le xs ys with
  | case1 ys => simp
  | case2 xs hxs => simp
  | case3 x xs y ys h out ih =>
    simpa only [List.map_cons, List.sum_cons, add_assoc] using
      congrArg (fun z : ℝ => f x + z) ih
  | case4 x xs y ys out h ih =>
    simp only [List.map_cons, List.sum_cons] at *
    linarith

-- @node: mergeSortWithCostAux_sum
/-- Every level of the structural merge sort preserves observable weights. -/
lemma mergeSortWithCostAux_sum {α : Type} (le : α → α → Bool)
    (f : α → ℝ) (fuel : ℕ) (xs : List α) :
    (((mergeSortWithCostAux le fuel xs).1.map f).sum : ℝ) =
      (xs.map f).sum := by
  fun_induction mergeSortWithCostAux le fuel xs with
  | case1 xs => rfl
  | case2 n => rfl
  | case3 n x => rfl
  | case4 fuel xs hnil hsingle halves left right merged ihL ihR =>
    have hsplit : halves.1 ++ halves.2 = xs := by
      simpa [halves, List.splitAt_eq] using List.take_append_drop ((xs.length + 1) / 2) xs
    rw [mergeWithCost_sum le f left.1 right.1, ihL, ihR]
    rw [← hsplit, List.map_append, List.sum_append]

-- @node: mergeSortWithCost_sum
lemma mergeSortWithCost_sum {α : Type} (le : α → α → Bool)
    (f : α → ℝ) (xs : List α) :
    (((mergeSortWithCost xs le).1.map f).sum : ℝ) = (xs.map f).sum := by
  exact mergeSortWithCostAux_sum le f xs.length xs

/-- One sort of observed scores, with the public endpoints inserted. -/
noncomputable def sortedScoreGroups {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) : List (ℝ × ℝ) :=
  groupedScores ((mergeSortWithCost ([(0,0),(1,0)] ++
    List.ofFn (fun i : Fin n => ((d i).X, zScore a e (d i))))
      (fun p q => decide (p.1 ≤ q.1))).1)

-- @node: sortedScoreGroups_sum
/-- Sorting and tie grouping preserve the total observable score. -/
lemma sortedScoreGroups_sum {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) :
    ((sortedScoreGroups a e d).map Prod.snd).sum =
      ∑ i : Fin n, zScore a e (d i) := by
  unfold sortedScoreGroups
  rw [groupedScores_sum, mergeSortWithCost_sum]
  simp [List.sum_ofFn]

-- @node: sortedScoreGroups_key_mem
/-- Each grouped cutoff is an endpoint or an observed score. -/
lemma sortedScoreGroups_key_mem {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (p : ℝ × ℝ)
    (hp : p ∈ sortedScoreGroups a e d) :
    p.1 = 0 ∨ p.1 = 1 ∨ ∃ i : Fin n, p.1 = (d i).X := by
  have hk := groupedScores_key_mem _ p hp
  obtain ⟨q, hq, hkey⟩ := List.mem_map.mp hk
  have hsource := (mergeSortWithCost_mem
    (fun v w : ℝ × ℝ => decide (v.1 ≤ w.1))
    ([(0,0),(1,0)] ++ List.ofFn
      (fun i : Fin n => ((d i).X, zScore a e (d i)))) q).mp hq
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil] at hsource
  rcases hsource with (hzero | hone | hnil) | hsample
  · left
    simpa [hzero] using hkey.symm
  · right; left
    simpa [hone] using hkey.symm
  · exact False.elim hnil
  · right; right
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hsample
    exact ⟨i, hkey.symm.trans (congrArg Prod.fst hi.symm)⟩

-- @node: empObjective_constant_false
/-- The scan's all-untreated cost is the empirical objective of that rule. -/
lemma empObjective_constant_false {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) :
    empObjective a e d (fun _ => false) =
      (n:ℝ)⁻¹ * ((sortedScoreGroups a e d).map Prod.snd).sum := by
  simp [empObjective, empiricalAverage, sortedScoreGroups_sum]

-- @node: empObjective_constant_true
/-- The all-treated empirical cost is zero. -/
lemma empObjective_constant_true {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) :
    empObjective a e d (fun _ => true) = 0 := by
  simp [empObjective, empiricalAverage]

/-- Actual comparisons in sorting, plus a fixed charge for each linear scan. -/
noncomputable def selectorOperationCount {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) : ℕ :=
  (mergeSortWithCost ([(0,0),(1,0)] ++
    List.ofFn (fun i : Fin n => ((d i).X, zScore a e (d i))))
      (fun p q => decide (p.1 ≤ q.1))).2 + 8*(n+2)

-- @node: clampScore
/-- A total cutoff used to keep the selector in the policy class on malformed inputs. -/
def clampScore (x : ℝ) : ℝ := max 0 (min 1 x)

-- @node: clampScore_mem
lemma clampScore_mem (x : ℝ) : clampScore x ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

-- @node: clampScore_eq
lemma clampScore_eq (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    clampScore x = x := by
  simp [clampScore, hx.1, hx.2]

/-- Each group yields both orientation costs from one running prefix sum. -/
noncomputable def scannedPolicyCosts {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) : List ((ℝ → Bool) × ℝ) :=
  let groups := sortedScoreGroups a e d
  let total := groups.foldl (fun s p => s + p.2) 0
  let initial : List ((ℝ → Bool) × ℝ) :=
    [((fun _ => false), (n:ℝ)⁻¹ * total), ((fun _ => true), 0)]
  initial ++ ((groups.foldl (fun state p =>
    let before := state.1
    let after := before + p.2
    -- The accumulated list is reversed: reversal below makes left precede right at each cutoff.
    (after, ((rightThr (clampScore p.1), (n:ℝ)⁻¹ * before) ::
      (leftThr (clampScore p.1), (n:ℝ)⁻¹ * (total - after)) :: state.2))
    ) ((0:ℝ), ([] : List ((ℝ → Bool) × ℝ)))).2.reverse)

-- @node: scannedPolicyCosts_constant_costs
/-- Both constant policies enter the scan with their exact empirical costs. -/
lemma scannedPolicyCosts_constant_costs {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) :
    ((fun _ => false), empObjective a e d (fun _ => false)) ∈
        scannedPolicyCosts a e d ∧
      ((fun _ => true), empObjective a e d (fun _ => true)) ∈
        scannedPolicyCosts a e d := by
  have hsum (xs : List (ℝ × ℝ)) (s : ℝ) :
      xs.foldl (fun t p => t + p.2) s = s + (xs.map Prod.snd).sum := by
    induction xs generalizing s with
    | nil => simp
    | cons p rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring
  rw [empObjective_constant_false, empObjective_constant_true]
  dsimp only [scannedPolicyCosts]
  rw [hsum]
  constructor <;> simp

/-- First minimum in the order: false, true, then increasing cutoffs, left before right. -/
noncomputable def firstScannedMinimizer {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) : ℝ → Bool :=
  match scannedPolicyCosts a e d with
  | [] => fun _ => false
  | first :: rest =>
    (rest.foldl (fun best item => if item.2 < best.2 then item else best) first).1

-- @node: scannedPolicyCosts_mem_thresholdClass
/-- Every scanned candidate is an admissible threshold or constant policy. -/
lemma scannedPolicyCosts_mem_thresholdClass {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) :
    ∀ q ∈ scannedPolicyCosts a e d, q.1 ∈ thresholdClass := by
  have hleft (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      leftThr t ∈ thresholdClass := by
    exact Or.inr (Or.inr (Or.inl ⟨t, ht, fun _ _ => rfl⟩))
  have hright (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      rightThr t ∈ thresholdClass := by
    exact Or.inr (Or.inr (Or.inr ⟨t, ht, fun _ _ => rfl⟩))
  have hscan (xs : List (ℝ × ℝ)) (total : ℝ) (state : ℝ ×
      List ((ℝ → Bool) × ℝ))
      (hs : ∀ q ∈ state.2, q.1 ∈ thresholdClass) :
      ∀ q ∈ (xs.foldl (fun state p =>
        let before := state.1
        let after := before + p.2
        (after, ((rightThr (clampScore p.1), (n:ℝ)⁻¹ * before) ::
          (leftThr (clampScore p.1), (n:ℝ)⁻¹ * (total - after)) :: state.2))) state).2,
          q.1 ∈ thresholdClass := by
    induction xs generalizing state with
    | nil => simpa using hs
    | cons p rest ih =>
      simp only [List.foldl_cons]
      apply ih
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with hq | hq | hq
      · subst q; exact hright _ (clampScore_mem _)
      · subst q; exact hleft _ (clampScore_mem _)
      · exact hs q hq
  intro q hq
  unfold scannedPolicyCosts at hq
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
    List.mem_reverse] at hq
  rcases hq with (hq | hq | hfalse) | hq
  · subst q; exact Or.inl (fun _ _ => rfl)
  · subst q; exact Or.inr (Or.inl (fun _ _ => rfl))
  · exact False.elim hfalse
  · exact hscan _ _ _ (by simp) q hq

-- @node: firstScannedMinimizer_mem_thresholdClass
/-- Choosing the first smallest cost preserves membership of the scan list. -/
lemma firstScannedMinimizer_mem_thresholdClass {n : ℕ} (a : ℝ)
    (e : ℝ → ℝ) (d : Fin n → Observation) :
    firstScannedMinimizer a e d ∈ thresholdClass := by
  have hfold (xs : List ((ℝ → Bool) × ℝ)) (best : (ℝ → Bool) × ℝ)
      (hb : best.1 ∈ thresholdClass)
      (hs : ∀ q ∈ xs, q.1 ∈ thresholdClass) :
      (xs.foldl (fun best item => if item.2 < best.2 then item else best) best).1 ∈
        thresholdClass := by
    induction xs generalizing best with
    | nil => simpa using hb
    | cons item rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · split_ifs <;> first | exact hs item (by simp) | exact hb
      · intro q hq
        exact hs q (by simp [hq])
  unfold firstScannedMinimizer
  split
  · exact Or.inl (fun _ _ => rfl)
  · rename_i first rest hlist
    apply hfold rest first
    · exact scannedPolicyCosts_mem_thresholdClass a e d first (by simp [hlist])
    · intro q hq
      exact scannedPolicyCosts_mem_thresholdClass a e d q (by simp [hlist, hq])

-- @node: def:sorted-selector
/-- Sorted exact selector: false, true, then increasing cutoffs with left before right. -/
noncomputable def sortedSelector {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) : ℝ → Bool :=
  firstScannedMinimizer a e d -- @realizes pihata(first empirical minimizer by one sort and prefix scan)

-- @node: sortedSelector_congr_logger
/-- The selector uses the supplied logger only at observed scores. -/
lemma sortedSelector_congr_logger {n : ℕ} (a : ℝ) (e e' : ℝ → ℝ)
    (d : Fin n → Observation)
    (hd : ∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1)
    (he : Set.EqOn e e' (Set.Icc (0:ℝ) 1)) :
    sortedSelector a e d = sortedSelector a e' d := by
  have hs (i : Fin n) : zScore a e (d i) = zScore a e' (d i) := by
    simp [zScore, gammaScore, offsetG, he (hd i)]
  have hg : sortedScoreGroups a e d = sortedScoreGroups a e' d := by
    simp [sortedScoreGroups, hs]
  simp [sortedSelector, firstScannedMinimizer, scannedPolicyCosts, hg]

/-- Deterministic deletion schedule. -/
noncomputable def deletionSchedule (α γ θ : ℝ) (n : ℕ) : ℝ :=
  min (1/4) ((n:ℝ) ^ (-(1/(sExp α γ θ+1)))) -- @realizes an(min(1/4,n^(-1/(s+1))))

/-- Rate-balanced selector. -/
noncomputable def rateSelector {n : ℕ} (α γ θ : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) : ℝ → Bool :=
  sortedSelector (deletionSchedule α γ θ n) e d -- @realizes pihatn(pi_hat at a_n)

/-- Disagreement set from the canonical rule. -/
def disagreementSet (P : RowLaw) (π : ℝ → Bool) : Set ℝ :=
  {x | π x ≠ canonicalPolicy P x} -- @realizes Dpi({x:pi(x)≠pi*(x)})

/-- Offset-weighted disagreement. -/
noncomputable def offsetDisagreement (P : RowLaw) (a : ℝ) (π : ℝ → Bool) : ℝ :=
  ∫ x, offsetG a P.logger x * (if π x = canonicalPolicy P x then (0:ℝ) else 1) ∂P.PX -- @realizes Ga(E[g_a 1_Dpi])

-- @node: def:regularized-loss
/-- Regret plus the offset disagreement penalty. -/
noncomputable def regularizedLoss (P : RowLaw) (a : ℝ) (π : ℝ → Bool) : ℝ :=
  rawRegret P π + offsetDisagreement P a π -- @realizes Ta(T_a=R+G_a)

/-- Tie-safe regularization bias. -/
noncomputable def biasFunctional (P : RowLaw) (a : ℝ) : ℝ :=
  P.PX.real {x | overlap P x < a ∧ P.tau x < 0} +
    ∫ x, offsetG a P.logger x *
      (if a ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
          effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX -- @realizes Ha(deletion and small-effect bias)

/-- Population negative-action objective. -/
noncomputable def popObjective (P : RowLaw) (a : ℝ) (π : ℝ → Bool) : ℝ :=
  ∫ o, (if π o.X then (0:ℝ) else 1) * zScore a P.logger o ∂P.obsLaw -- @realizes Ja(E[(1-pi)Z_a])

/-- Uncentered threshold comparison integrand. -/
noncomputable def comparisonIntegrand (P : RowLaw) (a : ℝ)
    (π : ℝ → Bool) (o : Observation) : ℝ :=
  ((if π o.X then (0:ℝ) else 1) -
    (if canonicalPolicy P o.X then (0:ℝ) else 1)) * zScore a P.logger o -- @realizes fpi([(1-pi)-(1-pi*)]Z_a)

-- @node: def:localized-process
/-- Localized supremum over the actual two-orientation threshold class. -/
noncomputable def localizedProcess {n : ℕ} (P : RowLaw) (a z : ℝ)
    (d : Fin n → Observation) : ℝ :=
  ⨆ π : {π : ℝ → Bool // π ∈ thresholdClass ∧ regularizedLoss P a π ≤ z},
    |empiricalAverage (comparisonIntegrand P a π.1) d -
      ∫ o, comparisonIntegrand P a π.1 o ∂P.obsLaw| -- @realizes Sa(sup localized absolute empirical process)

-- @node: mergeWithCost_bound
lemma mergeWithCost_bound {α : Type} (le : α → α → Bool) (xs ys : List α) :
    (mergeWithCost le xs ys).1.length = xs.length + ys.length ∧
    (mergeWithCost le xs ys).2 ≤ xs.length + ys.length := by
  fun_induction mergeWithCost le xs ys with
  | case1 ys => simp
  | case2 xs hxs => simp
  | case3 x xs y ys h out ih =>
    simp only [List.length_cons]
    change (mergeWithCost le xs (y :: ys)).1.length + 1 = _ ∧
      (mergeWithCost le xs (y :: ys)).2 + 1 ≤ _
    simp only [List.length_cons] at *
    omega
  | case4 x xs y ys out h ih =>
    simp only [h, List.length_cons]
    simp only [List.length_cons] at *
    omega

-- @node: splitAt_clog_bound
lemma splitAt_clog_bound {α : Type} (xs : List α) (hxs : 2 ≤ xs.length) :
    let halves := xs.splitAt ((xs.length + 1) / 2)
    halves.1.length + halves.2.length = xs.length ∧
    Nat.clog 2 halves.1.length + 1 ≤ Nat.clog 2 xs.length ∧
    Nat.clog 2 halves.2.length + 1 ≤ Nat.clog 2 xs.length := by
  dsimp
  have hhalf : (xs.length + 1) / 2 ≤ xs.length := by omega
  have hclog : Nat.clog 2 xs.length = Nat.clog 2 ((xs.length + 1) / 2) + 1 := by
    exact Nat.clog_of_two_le (by omega) hxs
  rw [List.splitAt_eq]
  simp only [List.length_take, List.length_drop]
  rw [Nat.min_eq_left hhalf]
  constructor
  · omega
  constructor
  · omega
  · have hright : xs.length - (xs.length + 1) / 2 ≤ (xs.length + 1) / 2 := by omega
    have hm := Nat.clog_mono_right 2 hright
    omega

-- @node: mergeSortWithCostAux_bound
lemma mergeSortWithCostAux_bound {α : Type} (le : α → α → Bool)
    (fuel : ℕ) (xs : List α) :
    (mergeSortWithCostAux le fuel xs).1.length = xs.length ∧
    (mergeSortWithCostAux le fuel xs).2 ≤ xs.length * Nat.clog 2 xs.length := by
  fun_induction mergeSortWithCostAux le fuel xs with
  | case1 xs => simp
  | case2 n => simp
  | case3 n x => simp
  | case4 fuel xs hnil hsingle halves left right merged ihL ihR =>
    have hxs : 2 ≤ xs.length := by
      cases xs with
      | nil => exact False.elim (hnil rfl)
      | cons x rest =>
        cases rest with
        | nil => exact False.elim (hsingle x rfl)
        | cons y ys => simp
    have hs := splitAt_clog_bound xs hxs
    change halves.1.length + halves.2.length = xs.length ∧
      Nat.clog 2 halves.1.length + 1 ≤ Nat.clog 2 xs.length ∧
      Nat.clog 2 halves.2.length + 1 ≤ Nat.clog 2 xs.length at hs
    have hm := mergeWithCost_bound le left.1 right.1
    change merged.1.length = left.1.length + right.1.length ∧
      merged.2 ≤ left.1.length + right.1.length at hm
    change left.1.length = halves.1.length ∧
      left.2 ≤ halves.1.length * Nat.clog 2 halves.1.length at ihL
    change right.1.length = halves.2.length ∧
      right.2 ≤ halves.2.length * Nat.clog 2 halves.2.length at ihR
    have hl := Nat.mul_le_mul_left halves.1.length hs.2.1
    have hr := Nat.mul_le_mul_left halves.2.length hs.2.2
    simp only [Nat.mul_add] at hl hr
    change merged.1.length = xs.length ∧
      left.2 + right.2 + merged.2 ≤ xs.length * Nat.clog 2 xs.length
    have hprod : xs.length * Nat.clog 2 xs.length =
        halves.1.length * Nat.clog 2 xs.length +
        halves.2.length * Nat.clog 2 xs.length := by
      calc
        xs.length * Nat.clog 2 xs.length =
            (halves.1.length + halves.2.length) * Nat.clog 2 xs.length :=
          congrArg (fun k => k * Nat.clog 2 xs.length) hs.1.symm
        _ = _ := Nat.add_mul _ _ _
    constructor
    · omega
    · rw [hprod]
      omega

-- @node: clog_two_le_log2_succ
lemma clog_two_le_log2_succ (k : ℕ) : Nat.clog 2 k ≤ Nat.log2 k + 1 := by
  rw [Nat.log2_eq_log_two]
  exact Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega) k))

-- @node: mergeSortWithCost_bound
lemma mergeSortWithCost_bound {α : Type} (le : α → α → Bool) (xs : List α) :
    (mergeSortWithCost xs le).2 ≤ xs.length * (Nat.log2 xs.length + 1) := by
  have h := (mergeSortWithCostAux_bound le xs.length xs).2
  have hc := Nat.mul_le_mul_left xs.length (clog_two_le_log2_succ xs.length)
  exact le_trans h hc

-- @node: selectorOperationCount_bound
lemma selectorOperationCount_bound {m : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin m → Observation) :
    selectorOperationCount a e d ≤ 9 * (m+2) * (Nat.log2 (m+2)+1) := by
  let xs : List (ℝ × ℝ) := [(0,0),(1,0)] ++
    List.ofFn (fun i : Fin m => ((d i).X, zScore a e (d i)))
  have hlen : xs.length = m+2 := by simp [xs]
  have h := mergeSortWithCost_bound
    (fun p q : ℝ × ℝ => decide (p.1 ≤ q.1)) xs
  change selectorOperationCount a e d ≤ _
  unfold selectorOperationCount
  change (mergeSortWithCost xs (fun p q => decide (p.1 ≤ q.1))).2 + 8*(m+2) ≤ _
  rw [hlen] at h
  have hlog : 1 ≤ Nat.log2 (m+2)+1 := by omega
  have h8 := Nat.mul_le_mul_left (8*(m+2)) hlog
  simp only [mul_one] at h8
  calc
    (mergeSortWithCost xs (fun p q => decide (p.1 ≤ q.1))).2 + 8*(m+2)
        ≤ (m+2)*(Nat.log2 (m+2)+1) + 8*(m+2) := Nat.add_le_add_right h _
    _ ≤ (m+2)*(Nat.log2 (m+2)+1) + 8*(m+2)*(Nat.log2 (m+2)+1) := Nat.add_le_add_left h8 _
    _ = 9*(m+2)*(Nat.log2 (m+2)+1) := by ring


/-- Every admissible threshold is a Borel binary policy on the score interval. -/
-- @node: thresholdClass_mem_binaryPolicyClass
lemma thresholdClass_mem_binaryPolicyClass (π : ℝ → Bool)
    (hπ : π ∈ thresholdClass) : π ∈ binaryPolicyClass := by
  rcases hπ with hfalse | htrue | ⟨t, ht, hleft⟩ | ⟨t, ht, hright⟩
  · have h : (fun x : Set.Icc (0:ℝ) 1 => π x.1) = fun _ => false := by
      funext x
      exact hfalse x.1 x.2
    rw [binaryPolicyClass, Set.mem_ofPred_eq, h]
    fun_prop
  · have h : (fun x : Set.Icc (0:ℝ) 1 => π x.1) = fun _ => true := by
      funext x
      exact htrue x.1 x.2
    rw [binaryPolicyClass, Set.mem_ofPred_eq, h]
    fun_prop
  · have h : (fun x : Set.Icc (0:ℝ) 1 => π x.1) =
        fun x => leftThr t x.1 := by
      funext x
      exact hleft x.1 x.2
    rw [binaryPolicyClass, Set.mem_ofPred_eq, h]
    change Measurable (fun x : Set.Icc (0:ℝ) 1 =>
      if x.1 ≤ t then true else false)
    exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      measurable_const measurable_const
  · have h : (fun x : Set.Icc (0:ℝ) 1 => π x.1) =
        fun x => rightThr t x.1 := by
      funext x
      exact hright x.1 x.2
    rw [binaryPolicyClass, Set.mem_ofPred_eq, h]
    change Measurable (fun x : Set.Icc (0:ℝ) 1 =>
      if t ≤ x.1 then true else false)
    exact Measurable.ite (measurableSet_le measurable_const (by fun_prop))
      measurable_const measurable_const

-- @node: scannedFold_min_cost
/-- The running scan retains a candidate whose cost is no larger than every
candidate already visited. -/
lemma scannedFold_min_cost (xs : List ((ℝ → Bool) × ℝ))
    (best : (ℝ → Bool) × ℝ) :
    (xs.foldl (fun best item => if item.2 < best.2 then item else best) best).2 ≤ best.2 ∧
    ∀ item ∈ xs,
      (xs.foldl (fun best item => if item.2 < best.2 then item else best) best).2 ≤ item.2 := by
  induction xs generalizing best with
  | nil => simp
  | cons item rest ih =>
    simp only [List.foldl_cons]
    let next := if item.2 < best.2 then item else best
    have hnextBest : next.2 ≤ best.2 := by
      dsimp [next]
      split_ifs with h
      · exact le_of_lt h
      · exact le_rfl
    have hnextItem : next.2 ≤ item.2 := by
      dsimp [next]
      split_ifs with h
      · exact le_rfl
      · exact le_of_not_gt h
    obtain ⟨hhead, htail⟩ := ih next
    constructor
    · exact hhead.trans hnextBest
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hhead.trans hnextItem
      · exact htail q hq

-- @node: scannedFold_mem
/-- The running minimum is one of the candidates already visited. -/
lemma scannedFold_mem (xs : List ((ℝ → Bool) × ℝ))
    (best : (ℝ → Bool) × ℝ) :
    (xs.foldl (fun best item => if item.2 < best.2 then item else best) best) ∈
      best :: xs := by
  induction xs generalizing best with
  | nil => simp
  | cons item rest ih =>
    simp only [List.foldl_cons]
    let next := if item.2 < best.2 then item else best
    have hnext : next ∈ best :: item :: rest := by
      dsimp [next]
      split_ifs <;> simp
    have hfinal := ih next
    rcases List.mem_cons.mp hfinal with h | h
    · rw [h]
      exact hnext
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

-- @node: sortedSelector_scanned_min_cost
/-- The selector is represented by a scanned candidate of minimum stored cost. -/
lemma sortedSelector_scanned_min_cost {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) :
    ∃ q ∈ scannedPolicyCosts a e d,
      q.1 = sortedSelector a e d ∧
      ∀ r ∈ scannedPolicyCosts a e d, q.2 ≤ r.2 := by
  have hnonempty : scannedPolicyCosts a e d ≠ [] := by
    simp [scannedPolicyCosts]
  obtain ⟨first, rest, hlist⟩ := List.exists_cons_of_ne_nil hnonempty
  let q := rest.foldl (fun best item => if item.2 < best.2 then item else best) first
  have hmem : q ∈ first :: rest := scannedFold_mem rest first
  obtain ⟨hfirst, hrest⟩ := scannedFold_min_cost rest first
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa only [hlist] using hmem
  · simp [sortedSelector, firstScannedMinimizer, hlist, q]
  · intro r hr
    rw [hlist] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hfirst
    · exact hrest r hr

-- @node: rightThr_sample_representative
/-- On a finite sample, a right threshold has either no treated observations or
the same labels as a threshold at its smallest treated observed score. -/
lemma rightThr_sample_representative {n : ℕ} (d : Fin n → Observation) (t : ℝ) :
    (∀ i : Fin n, rightThr t (d i).X = false) ∨
      ∃ j : Fin n, ∀ i : Fin n,
        rightThr t (d i).X = rightThr (d j).X (d i).X := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => t ≤ (d i).X)
  by_cases hs : s.Nonempty
  · let v : ℝ := (s.image (fun i => (d i).X)).min' (Finset.Nonempty.image hs _)
    obtain ⟨j, hjs, hjv⟩ : ∃ j ∈ s, (d j).X = v := by
      have hv := (Finset.isLeast_min' (s.image (fun i => (d i).X))
        (Finset.Nonempty.image hs _)).1
      rcases Finset.mem_image.mp hv with ⟨j, hjs, hjv⟩
      exact ⟨j, hjs, hjv⟩
    right
    refine ⟨j, ?_⟩
    intro i
    by_cases hi : t ≤ (d i).X
    · have his : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      have hle : v ≤ (d i).X :=
        (Finset.isLeast_min' (s.image (fun i => (d i).X))
          (Finset.Nonempty.image hs _)).2 (Finset.mem_image.mpr ⟨i, his, rfl⟩)
      simp [rightThr, hi, hjv, hle]
    · have hj : t ≤ (d j).X := (Finset.mem_filter.mp hjs).2
      have hnot : ¬ (d j).X ≤ (d i).X := by linarith
      simp [rightThr, hi, hnot]
  · left
    intro i
    have hi : ¬ t ≤ (d i).X := by
      intro hit
      apply hs
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩⟩
    simp [rightThr, hi]

-- @node: leftThr_sample_representative
/-- On a finite sample, a left threshold has either no treated observations or
the same labels as a threshold at its largest treated observed score. -/
lemma leftThr_sample_representative {n : ℕ} (d : Fin n → Observation) (t : ℝ) :
    (∀ i : Fin n, leftThr t (d i).X = false) ∨
      ∃ j : Fin n, ∀ i : Fin n,
        leftThr t (d i).X = leftThr (d j).X (d i).X := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => (d i).X ≤ t)
  by_cases hs : s.Nonempty
  · let v : ℝ := (s.image (fun i => (d i).X)).max' (Finset.Nonempty.image hs _)
    obtain ⟨j, hjs, hjv⟩ : ∃ j ∈ s, (d j).X = v := by
      have hv := (Finset.isGreatest_max' (s.image (fun i => (d i).X))
        (Finset.Nonempty.image hs _)).1
      rcases Finset.mem_image.mp hv with ⟨j, hjs, hjv⟩
      exact ⟨j, hjs, hjv⟩
    right
    refine ⟨j, ?_⟩
    intro i
    by_cases hi : (d i).X ≤ t
    · have his : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      have hle : (d i).X ≤ v :=
        (Finset.isGreatest_max' (s.image (fun i => (d i).X))
          (Finset.Nonempty.image hs _)).2 (Finset.mem_image.mpr ⟨i, his, rfl⟩)
      simp [leftThr, hi, hjv, hle]
    · have hj : (d j).X ≤ t := (Finset.mem_filter.mp hjs).2
      have hnot : ¬ (d i).X ≤ (d j).X := by linarith
      simp [leftThr, hi, hnot]
  · left
    intro i
    have hi : ¬ (d i).X ≤ t := by
      intro hit
      apply hs
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩⟩
    simp [leftThr, hi]

-- @node: empObjective_congr_sample_labels
/-- The empirical objective sees a policy only through its labels on observed scores. -/
lemma empObjective_congr_sample_labels {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (π ρ : ℝ → Bool)
    (h : ∀ i : Fin n, π (d i).X = ρ (d i).X) :
    empObjective a e d π = empObjective a e d ρ := by
  unfold empObjective empiricalAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [h i]

-- @node: threshold_sample_candidate
/-- Every admissible threshold has the empirical objective of a constant rule
or a threshold at an observed score. -/
lemma threshold_sample_candidate {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation)
    (hd : ∀ i : Fin n, (d i).X ∈ Set.Icc (0:ℝ) 1)
    (π : ℝ → Bool) (hπ : π ∈ thresholdClass) :
    (∃ ρ : ℝ → Bool,
      (ρ = (fun _ => false) ∨ ρ = (fun _ => true) ∨
        (∃ j : Fin n, ρ = leftThr (d j).X) ∨
        (∃ j : Fin n, ρ = rightThr (d j).X)) ∧
      empObjective a e d π = empObjective a e d ρ) := by
  rcases hπ with hfalse | htrue | ⟨t, _, hleft⟩ | ⟨t, _, hright⟩
  · refine ⟨fun _ => false, Or.inl rfl, ?_⟩
    exact empObjective_congr_sample_labels a e d π _
      (fun i => hfalse (d i).X (hd i))
  · refine ⟨fun _ => true, Or.inr (Or.inl rfl), ?_⟩
    exact empObjective_congr_sample_labels a e d π _
      (fun i => htrue (d i).X (hd i))
  · rcases leftThr_sample_representative d t with hzero | ⟨j, hj⟩
    · refine ⟨fun _ => false, Or.inl rfl, ?_⟩
      exact empObjective_congr_sample_labels a e d π _
        (fun i => (hleft (d i).X (hd i)).trans (hzero i))
    · refine ⟨leftThr (d j).X, Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)), ?_⟩
      exact empObjective_congr_sample_labels a e d π _
        (fun i => (hleft (d i).X (hd i)).trans (hj i))
  · rcases rightThr_sample_representative d t with hzero | ⟨j, hj⟩
    · refine ⟨fun _ => false, Or.inl rfl, ?_⟩
      exact empObjective_congr_sample_labels a e d π _
        (fun i => (hright (d i).X (hd i)).trans (hzero i))
    · refine ⟨rightThr (d j).X, Or.inr (Or.inr (Or.inr ⟨j, rfl⟩)), ?_⟩
      exact empObjective_congr_sample_labels a e d π _
        (fun i => (hright (d i).X (hd i)).trans (hj i))

end CausalSmith.Stat.ScorethresholdOverlapRegret
