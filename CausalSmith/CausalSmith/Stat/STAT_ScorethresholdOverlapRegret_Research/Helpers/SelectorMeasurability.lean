module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.Estimator

/-! # Borel measurability of the sorted selector

Finite lists of measurable coordinates, with finitely many Borel branches,
provide a direct measurability proof for sorting, tie grouping, and scanning.
No measurable space on policy-valued lists is required: policies are evaluated
at the new score before checking measurability.
-/

@[expose] public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory

/-- A list-valued map assembled from measurable coordinates and finite Borel branches. -/
-- @node: BorelList
inductive BorelList {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] :
    (Ω → List α) → Prop
  | coordinates (fs : List (Ω → α)) (hf : ∀ f ∈ fs, Measurable f) :
      BorelList (fun ω => fs.map (fun f => f ω))
  | branch (p : Ω → Prop) [DecidablePred p] (hp : MeasurableSet {ω | p ω})
      (f g : Ω → List α) : BorelList f → BorelList g →
      BorelList (fun ω => if p ω then f ω else g ω)

/-- It suffices to check a deterministic list transformation on fixed coordinate lists. -/
-- @node: borelList_transform
lemma borelList_transform {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (T : Ω → List α → List β)
    (hT : ∀ fs : List (Ω → α), (∀ f ∈ fs, Measurable f) →
      BorelList (fun ω => T ω (fs.map (fun f => f ω))))
    {f : Ω → List α} (hf : BorelList f) : BorelList (fun ω => T ω (f ω)) := by
  induction hf with
  | coordinates fs hm => exact hT fs hm
  | branch p hp f g hf hg ihf ihg =>
    convert BorelList.branch p hp _ _ ihf ihg using 1
    funext ω
    dsimp only
    split_ifs <;> rfl

/-- A scalar observation of a Borel list is measurable if it is so on coordinate lists. -/
-- @node: borelList_measurable_transform
lemma borelList_measurable_transform {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (T : Ω → List α → β)
    (hT : ∀ fs : List (Ω → α), (∀ f ∈ fs, Measurable f) →
      Measurable (fun ω => T ω (fs.map (fun f => f ω))))
    {f : Ω → List α} (hf : BorelList f) : Measurable (fun ω => T ω (f ω)) := by
  induction hf with
  | coordinates fs hm => exact hT fs hm
  | branch p hp f g hf hg ihf ihg =>
    convert Measurable.ite hp ihf ihg using 1
    · funext ω
      dsimp only
      split_ifs <;> rfl
    · exact ‹DecidablePred p›

/-- Prepending a measurable coordinate preserves finite Borel branching. -/
-- @node: borelList_cons
lemma borelList_cons {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {x : Ω → α} {xs : Ω → List α} (hx : Measurable x) (hxs : BorelList xs) :
    BorelList (fun ω => x ω :: xs ω) := by
  apply borelList_transform (fun ω ys => x ω :: ys) _ hxs
  intro fs hfs
  exact BorelList.coordinates (x :: fs) (by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hx
    · exact hfs f hf)

/-- A jointly measurable coordinate map preserves Borel lists. -/
-- @node: borelList_map
lemma borelList_map {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (T : Ω → α → β)
    (hT : Measurable (fun p : Ω × α => T p.1 p.2))
    {xs : Ω → List α} (hxs : BorelList xs) :
    BorelList (fun ω => (xs ω).map (T ω)) := by
  apply borelList_transform (fun ω ys => ys.map (T ω)) _ hxs
  intro fs hfs
  convert BorelList.coordinates (fs.map (fun f ω => T ω (f ω))) ?_ using 1
  · funext ω; simp [List.map_map, Function.comp_def]
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact hT.comp (measurable_id.prodMk (hfs g hg))

/-- Concatenating Borel lists preserves finite Borel branching. -/
-- @node: borelList_append
lemma borelList_append {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {xs ys : Ω → List α} (hx : BorelList xs) (hy : BorelList ys) :
    BorelList (fun ω => xs ω ++ ys ω) := by
  apply borelList_transform (fun ω zs => zs ++ ys ω) _ hx
  intro fs hfs
  induction fs with
  | nil => simpa using hy
  | cons f fs ih =>
    simpa using borelList_cons (hfs f (by simp))
      (ih (fun g hg => hfs g (by simp [hg])))

/-- Reversing a Borel list only reorders its measurable coordinates. -/
-- @node: borelList_reverse
lemma borelList_reverse {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {xs : Ω → List α} (hx : BorelList xs) : BorelList (fun ω => (xs ω).reverse) := by
  apply borelList_transform (fun _ ys => ys.reverse) _ hx
  intro fs hfs
  simpa only [List.map_reverse] using
    BorelList.coordinates fs.reverse (fun f hf => hfs f (List.mem_reverse.mp hf))

/-- A measurable fold step makes any scalar fold of a Borel list measurable. -/
-- @node: borelList_foldl
lemma borelList_foldl {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] (step : Ω → β → α → β)
    (hs : Measurable (fun p : Ω × β × α => step p.1 p.2.1 p.2.2))
    {init : Ω → β} (hi : Measurable init) {xs : Ω → List α} (hx : BorelList xs) :
    Measurable (fun ω => (xs ω).foldl (step ω) (init ω)) := by
  apply borelList_measurable_transform (fun ω ys => ys.foldl (step ω) (init ω)) _ hx
  intro fs hfs
  induction fs generalizing init with
  | nil => exact hi
  | cons f fs ih =>
    exact ih (hs.comp (measurable_id.prodMk (hi.prodMk (hfs f (by simp)))))
      (fun g hg => hfs g (by simp [hg]))

/-- Every comparison of the counted merge is a Borel branch. -/
-- @node: borelList_merge_coordinates
lemma borelList_merge_coordinates {Ω : Type*} [MeasurableSpace Ω]
    (fs gs : List (Ω → ℝ × ℝ)) (hf : ∀ f ∈ fs, Measurable f)
    (hg : ∀ g ∈ gs, Measurable g) :
    BorelList (fun ω => (mergeWithCost (fun p q => decide (p.1 ≤ q.1))
      (fs.map (fun f => f ω)) (gs.map (fun g => g ω))).1) := by
  induction fs generalizing gs with
  | nil => simpa [mergeWithCost] using BorelList.coordinates gs hg
  | cons f fs ihf =>
    induction gs with
    | nil => simpa [mergeWithCost] using BorelList.coordinates (f :: fs) hf
    | cons g gs ihg =>
      have hfm := hf f (by simp)
      have hgm := hg g (by simp)
      have hleft := borelList_cons hfm
        (ihf (g :: gs) (fun u hu => hf u (by simp [hu])) hg)
      have hright := borelList_cons hgm (ihg (fun u hu => hg u (by simp [hu])))
      convert BorelList.branch (fun ω => (f ω).1 ≤ (g ω).1)
        (measurableSet_le hfm.fst hgm.fst) _ _ hleft hright using 1
      funext ω
      simp only [List.map_cons, mergeWithCost]
      split_ifs <;> simp_all

/-- Merging two Borel score lists preserves their measurable finite representation. -/
-- @node: borelList_merge
lemma borelList_merge {Ω : Type*} [MeasurableSpace Ω]
    {xs ys : Ω → List (ℝ × ℝ)} (hx : BorelList xs) (hy : BorelList ys) :
    BorelList (fun ω => (mergeWithCost (fun p q => decide (p.1 ≤ q.1))
      (xs ω) (ys ω)).1) := by
  apply borelList_transform (fun ω zs =>
    (mergeWithCost (fun p q => decide (p.1 ≤ q.1)) zs (ys ω)).1) _ hx
  intro fs hfs
  apply borelList_transform (fun ω zs =>
    (mergeWithCost (fun p q => decide (p.1 ≤ q.1))
      (fs.map (fun f => f ω)) zs).1) _ hy
  intro gs hgs
  exact borelList_merge_coordinates fs gs hfs hgs

/-- Structural merge-sort fuel yields finitely many Borel comparison branches. -/
-- @node: borelList_sortAux
lemma borelList_sortAux {Ω : Type*} [MeasurableSpace Ω] (fuel : ℕ)
    {xs : Ω → List (ℝ × ℝ)} (hx : BorelList xs) :
    BorelList (fun ω => (mergeSortWithCostAux
      (fun p q => decide (p.1 ≤ q.1)) fuel (xs ω)).1) := by
  induction fuel generalizing xs with
  | zero => simpa [mergeSortWithCostAux] using hx
  | succ fuel ih =>
    apply borelList_transform (fun _ zs => (mergeSortWithCostAux
      (fun p q => decide (p.1 ≤ q.1)) (fuel+1) zs).1) _ hx
    intro fs hfs
    cases fs with
    | nil => simpa [mergeSortWithCostAux] using BorelList.coordinates [] (by simp)
    | cons f fs =>
      cases fs with
      | nil => simpa [mergeSortWithCostAux] using BorelList.coordinates [f] hfs
      | cons g fs =>
        let all := f :: g :: fs
        let k := (all.length + 1) / 2
        have hL := ih (BorelList.coordinates (all.take k)
          (fun u hu => hfs u (List.mem_of_mem_take hu)))
        have hR := ih (BorelList.coordinates (all.drop k)
          (fun u hu => hfs u (List.mem_of_mem_drop hu)))
        convert borelList_merge hL hR using 1
        funext ω
        simp [mergeSortWithCostAux, List.splitAt_eq, List.map_take,
          List.map_drop, all, k]

/-- The implemented score sort has a finite Borel representation. -/
-- @node: borelList_sort
lemma borelList_sort {Ω : Type*} [MeasurableSpace Ω]
    {xs : Ω → List (ℝ × ℝ)} (hx : BorelList xs) :
    BorelList (fun ω => (mergeSortWithCost (xs ω)
      (fun p q => decide (p.1 ≤ q.1))).1) := by
  apply borelList_transform (fun _ zs => (mergeSortWithCost zs
    (fun p q => decide (p.1 ≤ q.1))).1) _ hx
  intro fs hfs
  simpa [mergeSortWithCost] using
    borelList_sortAux fs.length (BorelList.coordinates fs hfs)

/-- A tie test and addition of group weights are measurable operations. -/
-- @node: borelList_group_step
lemma borelList_group_step {Ω : Type*} [MeasurableSpace Ω]
    {p : Ω → ℝ × ℝ} (hp : Measurable p)
    {acc : Ω → List (ℝ × ℝ)} (ha : BorelList acc) :
    BorelList (fun ω => match acc ω with
      | [] => [p ω]
      | q :: rest => if q.1 = (p ω).1 then
          (q.1, q.2 + (p ω).2) :: rest else p ω :: acc ω) := by
  apply borelList_transform (fun ω zs => match zs with
    | [] => [p ω]
    | q :: rest => if q.1 = (p ω).1 then
        (q.1, q.2 + (p ω).2) :: rest else p ω :: zs) _ ha
  intro fs hfs
  cases fs with
  | nil => exact BorelList.coordinates [p] (by simpa)
  | cons q fs =>
    have hq := hfs q (by simp)
    have hm : Measurable (fun ω => ((q ω).1, (q ω).2 + (p ω).2)) := by fun_prop
    simpa only [List.map_cons] using BorelList.branch
      (fun ω => (q ω).1 = (p ω).1) (measurableSet_eq_fun hq.fst hp.fst) _ _
      (borelList_cons hm (BorelList.coordinates fs (fun u hu => hfs u (by simp [hu]))))
      (borelList_cons hp (BorelList.coordinates (q :: fs) hfs))

/-- Consecutive tie grouping preserves finite Borel branching. -/
-- @node: borelList_groupedScores
lemma borelList_groupedScores {Ω : Type*} [MeasurableSpace Ω]
    {xs : Ω → List (ℝ × ℝ)} (hx : BorelList xs) :
    BorelList (fun ω => groupedScores (xs ω)) := by
  let step : List (ℝ × ℝ) → (ℝ × ℝ) → List (ℝ × ℝ) := fun acc p =>
    match acc with
    | [] => [p]
    | q :: rest => if q.1 = p.1 then (q.1, q.2 + p.2) :: rest else p :: acc
  have hfold {acc : Ω → List (ℝ × ℝ)} (ha : BorelList acc) :
      BorelList (fun ω => (xs ω).foldl step (acc ω)) := by
    apply borelList_transform (fun ω zs => zs.foldl step (acc ω)) _ hx
    intro fs hfs
    induction fs generalizing acc with
    | nil => exact ha
    | cons f fs ih =>
      exact ih (borelList_group_step (hfs f (by simp)) ha)
        (fun u hu => hfs u (by simp [hu]))
  exact borelList_reverse (hfold (BorelList.coordinates [] (by simp)))

/-- The running scan with each policy evaluated immediately at a new score. -/
-- @node: evaluatedScoreScan
noncomputable def evaluatedScoreScan (inv total x : ℝ) (groups : List (ℝ × ℝ))
    (state : ℝ × List (Bool × ℝ)) : ℝ × List (Bool × ℝ) :=
  groups.foldl (fun state p =>
    let after := state.1 + p.2
    (after, (rightThr (clampScore p.1) x, inv * state.1) ::
      (leftThr (clampScore p.1) x, inv * (total-after)) :: state.2)) state

/-- A left threshold is jointly Borel in its cutoff and evaluation score. -/
@[fun_prop]
-- @node: measurable_leftThr_evaluation
lemma measurable_leftThr_evaluation {Ω : Type*} [MeasurableSpace Ω]
    {t x : Ω → ℝ} (ht : Measurable t) (hx : Measurable x) :
    Measurable (fun ω => leftThr (t ω) (x ω)) := by
  apply measurable_to_bool
  simpa [leftThr, Set.preimage] using measurableSet_le hx ht

/-- A right threshold is jointly Borel in its cutoff and evaluation score. -/
@[fun_prop]
-- @node: measurable_rightThr_evaluation
lemma measurable_rightThr_evaluation {Ω : Type*} [MeasurableSpace Ω]
    {t x : Ω → ℝ} (ht : Measurable t) (hx : Measurable x) :
    Measurable (fun ω => rightThr (t ω) (x ω)) := by
  apply measurable_to_bool
  simpa [rightThr, Set.preimage] using measurableSet_le ht hx

/-- Prefix and suffix costs and their evaluated threshold labels are Borel. -/
-- @node: borelList_evaluatedScoreScan
lemma borelList_evaluatedScoreScan {Ω : Type*} [MeasurableSpace Ω]
    (inv : ℝ) {total x running : Ω → ℝ}
    (ht : Measurable total) (hx : Measurable x) (hp : Measurable running)
    {groups : Ω → List (ℝ × ℝ)} (hg : BorelList groups)
    {acc : Ω → List (Bool × ℝ)} (ha : BorelList acc) :
    BorelList (fun ω => (evaluatedScoreScan inv (total ω) (x ω)
      (groups ω) (running ω, acc ω)).2) := by
  apply borelList_transform (fun ω zs => (evaluatedScoreScan inv
    (total ω) (x ω) zs (running ω, acc ω)).2) _ hg
  intro fs hfs
  induction fs generalizing running acc with
  | nil => exact ha
  | cons f fs ih =>
    have hf := hfs f (by simp)
    have hcut : Measurable (fun ω => clampScore (f ω).1) := by
      dsimp [clampScore]; fun_prop
    have hright : Measurable (fun ω => (rightThr (clampScore (f ω).1) (x ω),
        inv * running ω)) := by fun_prop
    have hleft : Measurable (fun ω => (leftThr (clampScore (f ω).1) (x ω),
        inv * (total ω - (running ω + (f ω).2)))) := by fun_prop
    exact ih (by fun_prop : Measurable (fun ω => running ω + (f ω).2))
      (borelList_cons hright (borelList_cons hleft ha))
      (fun u hu => hfs u (by simp [hu]))

/-- Evaluating policy labels commutes with every step of the implemented score scan. -/
-- @node: evaluatedScoreScan_eq
lemma evaluatedScoreScan_eq (inv total x : ℝ) (groups : List (ℝ × ℝ))
    (state : ℝ × List ((ℝ → Bool) × ℝ)) :
    evaluatedScoreScan inv total x groups
        (state.1, state.2.map (fun q => (q.1 x, q.2))) =
      let out := groups.foldl (fun state p =>
        let after := state.1 + p.2
        (after, (rightThr (clampScore p.1), inv * state.1) ::
          (leftThr (clampScore p.1), inv * (total-after)) :: state.2)) state
      (out.1, out.2.map (fun q => (q.1 x, q.2))) := by
  induction groups generalizing state with
  | nil => rfl
  | cons p ps ih =>
    simpa only [evaluatedScoreScan, List.foldl_cons, List.map_cons] using
      ih (state.1 + p.2, (rightThr (clampScore p.1), inv * state.1) ::
        (leftThr (clampScore p.1), inv * (total-(state.1+p.2))) :: state.2)

/-- The first-minimizer fold on already evaluated policy labels and their costs. -/
-- @node: evaluatedFirstMin
noncomputable def evaluatedFirstMin (xs : List (Bool × ℝ)) : Bool :=
  match xs with
  | [] => false
  | first :: rest =>
    (rest.foldl (fun best item => if item.2 < best.2 then item else best) first).1

/-- Choosing the first smallest score is a finite sequence of measurable comparisons. -/
-- @node: measurable_evaluatedFirstMin
lemma measurable_evaluatedFirstMin {Ω : Type*} [MeasurableSpace Ω]
    {xs : Ω → List (Bool × ℝ)} (hx : BorelList xs) :
    Measurable (fun ω => evaluatedFirstMin (xs ω)) := by
  apply borelList_measurable_transform (fun _ zs => evaluatedFirstMin zs) _ hx
  intro fs hfs
  cases fs with
  | nil => exact measurable_const
  | cons f fs =>
    have hstep : Measurable (fun p : Ω × (Bool × ℝ) × (Bool × ℝ) =>
        if p.2.2.2 < p.2.1.2 then p.2.2 else p.2.1) := by
      exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
        (by fun_prop) (by fun_prop)
    exact (borelList_foldl (fun _ best item => if item.2 < best.2 then item else best)
      hstep (hfs f (by simp))
      (BorelList.coordinates fs (fun u hu => hfs u (by simp [hu])))).fst

/-- Evaluation commutes with first-minimizer selection, including its tie convention. -/
-- @node: evaluatedFirstMin_eq
lemma evaluatedFirstMin_eq (xs : List ((ℝ → Bool) × ℝ)) (x : ℝ) :
    evaluatedFirstMin (xs.map (fun q => (q.1 x, q.2))) =
      (match xs with
       | [] => fun _ => false
       | first :: rest =>
         (rest.foldl (fun (best item : (ℝ → Bool) × ℝ) =>
           if item.2 < best.2 then item else best) first).1) x := by
  have hfold (rest : List ((ℝ → Bool) × ℝ)) (best : (ℝ → Bool) × ℝ) :
      (rest.map (fun q => (q.1 x, q.2))).foldl
          (fun best item => if item.2 < best.2 then item else best) (best.1 x, best.2) =
        let out := rest.foldl
          (fun best item => if item.2 < best.2 then item else best) best
        (out.1 x, out.2) := by
    induction rest generalizing best with
    | nil => rfl
    | cons q rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      split_ifs <;> apply ih
  cases xs with
  | nil => rfl
  | cons first rest =>
    exact congrArg Prod.fst (hfold rest first)

/-- The evaluated scan is exactly the policy-cost list used by the selector. -/
-- @node: scannedPolicyCosts_evaluation_eq
lemma scannedPolicyCosts_evaluation_eq {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (d : Fin n → Observation) (x : ℝ) :
    (scannedPolicyCosts a e d).map (fun q => (q.1 x, q.2)) =
      let groups := sortedScoreGroups a e d
      let total := groups.foldl (fun s p => s + p.2) 0
      [(false, (n:ℝ)⁻¹ * total), (true, 0)] ++
        (evaluatedScoreScan (n:ℝ)⁻¹ total x groups (0, [])).2.reverse := by
  simp only [scannedPolicyCosts, List.map_append, List.map_cons, List.map_nil,
    List.map_reverse]
  have h := congrArg (fun p : ℝ × List (Bool × ℝ) => p.2.reverse)
    (evaluatedScoreScan_eq (n:ℝ)⁻¹
      ((sortedScoreGroups a e d).foldl (fun s p => s + p.2) 0) x
      (sortedScoreGroups a e d) (0, []))
  simpa using congrArg (fun zs =>
    [(false, (n:ℝ)⁻¹ * (sortedScoreGroups a e d).foldl (fun s p => s + p.2) 0),
      (true, 0)] ++ zs) h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The implemented selector evaluates jointly measurably in the sample and a new score. -/
@[fun_prop]
-- @node: sortedSelector_measurable
lemma sortedSelector_measurable {n : ℕ} (a : ℝ) (e : ℝ → ℝ)
    (he : Measurable (fun x : Set.Icc (0:ℝ) 1 => e x)) :
    Measurable (fun dx : {d : Fin n → Observation //
        ∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1} ×
        Set.Icc (0:ℝ) 1 => sortedSelector a e dx.1.1 dx.2.1) := by
  let Ω := {d : Fin n → Observation //
    ∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1} × Set.Icc (0:ℝ) 1
  have hobs : Measurable (fun o : Observation => (o.X, o.A, o.Y)) := comap_measurable _
  have hX : Measurable (fun o : Observation => o.X) := hobs.fst
  have hA : Measurable (fun o : Observation => o.A) := hobs.snd.fst
  have hY : Measurable (fun o : Observation => o.Y) := hobs.snd.snd
  have hd (i : Fin n) : Measurable (fun ω : Ω => ω.1.1 i) := by
    exact (measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_fst)
  have heX (i : Fin n) : Measurable (fun ω : Ω => e (ω.1.1 i).X) := by
    exact he.comp ((hX.comp (hd i)).subtype_mk (h := fun ω : Ω => (ω.1.2 i).1))
  have hz (i : Fin n) : Measurable (fun ω : Ω => zScore a e (ω.1.1 i)) := by
    have hei := heX i
    have hYi := hY.comp (hd i)
    dsimp [zScore, gammaScore, offsetG]
    have hp : Measurable (fun ω : Ω => min (e (ω.1.1 i).X) (1-e (ω.1.1 i).X)) := by
      exact hei.min (measurable_const.sub hei)
    have hg : Measurable (fun ω : Ω => if a ≤ min (e (ω.1.1 i).X) (1-e (ω.1.1 i).X)
        then (if (ω.1.1 i).A then (ω.1.1 i).Y / e (ω.1.1 i).X
          else -((ω.1.1 i).Y / (1-e (ω.1.1 i).X))) else 0) := by
      apply Measurable.ite (measurableSet_le measurable_const hp)
      · apply Measurable.ite ((hA.comp (hd i)) (measurableSet_singleton true))
        · exact hYi.div hei
        · exact (hYi.div (measurable_const.sub hei)).neg
      · fun_prop
    exact hg.add (by dsimp [Ω] at *; fun_prop)
  have hinput : BorelList (fun ω : Ω => [(0,0),(1,0)] ++
      List.ofFn (fun i : Fin n => ((ω.1.1 i).X, zScore a e (ω.1.1 i)))) := by
    apply borelList_append
    · exact BorelList.coordinates [fun _ => (0,0), fun _ => (1,0)] (by simp [measurable_const])
    · convert BorelList.coordinates (List.ofFn (fun i : Fin n =>
        fun ω : Ω => ((ω.1.1 i).X, zScore a e (ω.1.1 i)))) ?_ using 1
      · funext ω; simp [List.map_ofFn, Function.comp_def]
      · intro f hf
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
        exact (hX.comp (hd i)).prodMk (hz i)
  have hgroups : BorelList (fun ω : Ω => sortedScoreGroups a e ω.1.1) :=
    borelList_groupedScores (borelList_sort hinput)
  have htotal : Measurable (fun ω : Ω =>
      (sortedScoreGroups a e ω.1.1).foldl (fun s p => s + p.2) 0) :=
    borelList_foldl (fun _ s p => s + p.2) (by dsimp [Ω] at *; fun_prop) measurable_const hgroups
  have hscan := borelList_evaluatedScoreScan (running := fun _ : Ω => (0:ℝ))
    (acc := fun _ : Ω => ([] : List (Bool × ℝ))) (n:ℝ)⁻¹ htotal
    (by dsimp [Ω] at *; fun_prop : Measurable (fun ω : Ω => ω.2.1)) measurable_const hgroups
    (BorelList.coordinates [] (by simp))
  have hinitial : BorelList (fun ω : Ω =>
      [(false, (n:ℝ)⁻¹ * (sortedScoreGroups a e ω.1.1).foldl (fun s p => s + p.2) 0),
        (true, 0)]) := by
    apply borelList_cons (by dsimp [Ω] at *; fun_prop)
    exact BorelList.coordinates [fun _ => (true,0)] (by simp [measurable_const])
  have hcosts : BorelList (fun ω : Ω =>
      (scannedPolicyCosts a e ω.1.1).map (fun q => (q.1 ω.2.1, q.2))) := by
    simpa only [scannedPolicyCosts_evaluation_eq] using
      borelList_append hinitial (borelList_reverse hscan)
  convert measurable_evaluatedFirstMin hcosts using 1
  funext ω
  exact (evaluatedFirstMin_eq (scannedPolicyCosts a e ω.1.1) ω.2.1).symm

end CausalSmith.Stat.ScorethresholdOverlapRegret
