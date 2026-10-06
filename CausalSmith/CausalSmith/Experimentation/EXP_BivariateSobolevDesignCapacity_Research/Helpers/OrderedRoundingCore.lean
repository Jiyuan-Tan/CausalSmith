module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! # Ordered boundary rounding

Exact finite arithmetic, ordered Gram--Schmidt, half-open inverse-CDF choices, and a
structural n-step iteration implement the prescribed procedure. The fractional terminal
state is retained separately so termination is a substantive proof obligation.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {n : ℕ}

/-- [ Euclidean dot product on the original coordinates. -/
def rowDot (v w : Fin n → ℝ) : ℝ := ∑ i, v i * w i
/-- Subtract rank-one projections onto an ordered orthonormal list. -/
def removeProjections (bs : List (Fin n → ℝ)) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => v i - (bs.map (fun b => rowDot v b * b i)).sum
/-- One ordered Gram--Schmidt insertion, discarding zero residuals. -/
def insertOrtho (bs : List (Fin n → ℝ)) (v : Fin n → ℝ) : List (Fin n → ℝ) :=
  let w := removeProjections bs v
  let r := Real.sqrt (rowDot w w)
  if 0 < r then bs ++ [fun i => w i / r] else bs
/-- Structural ordered Gram--Schmidt; no well-founded recursion enters the algorithm. -/
def orderedOrtho (vs : List (Fin n → ℝ)) : List (Fin n → ℝ) :=
  vs.foldl insertOrtho []
/-- Active coordinates in increasing original-unit order. -/
def activeIndices (u : Fin n → ℝ) : List (Fin n) :=
  (List.finRange n).filter (fun i => decide (|u i| < 1))
/-- Restrict a vector to active coordinates. -/
def activeMask (u v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if |u i| < 1 then v i else 0
/-- First q restricted constraints, including zero rows outside the supplied prefix. -/
def constraintBasis (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u : Fin n → ℝ) : List (Fin n → ℝ) :=
  orderedOrtho ((List.range q).map (fun h =>
    activeMask u (if hh : h < n / 4 then a ⟨h, hh⟩ else 0)))
/-- The projection onto the active-coordinate nullspace of the retained prefix. -/
def constraintProjection (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u v : Fin n → ℝ) : Fin n → ℝ :=
  removeProjections (constraintBasis a q u) (activeMask u v)
/-- Process projected standard basis vectors in index order. -/
def nullspaceBasis (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u : Fin n → ℝ) : List (Fin n → ℝ) :=
  orderedOrtho ((List.finRange n).map (fun j =>
    constraintProjection a q u (fun i => if i = j then 1 else 0)))
/-- Finite minimum, in original index order. -/
def finiteMin (xs : List ℝ) : ℝ :=
  match xs with
  | [] => 0
  | a :: as => as.foldl min a
/-- The positive boundary-hit distance along a nonzero active direction. -/
def boundaryPlus (u v : Fin n → ℝ) : ℝ :=
  finiteMin ((activeIndices u).filterMap (fun i =>
    if 0 < v i then some ((1 - u i) / v i)
    else if v i < 0 then some ((1 + u i) / (-v i)) else none))
/-- The negative boundary-hit distance. -/
def boundaryMinus (u v : Fin n → ℝ) : ℝ := boundaryPlus u (-v)
/-- Select with half-open cumulative intervals; seed one selects the last interval. -/
def inverseCDF : List ((Fin n → ℝ) × ℝ) → ℝ → Fin n → ℝ
  | [], _ => 0
  | [(v, _)], _ => v
  | (v, w) :: rest, t => if t < w then v else inverseCDF rest (t - w)
/-- One asymmetric boundary move with direction weights proportional to 1/(δ⁺δ⁻). -/
def roundingStep (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u : Fin n → ℝ) (seed₁ seed₂ : ℝ) : Fin n → ℝ :=
  let bs := nullspaceBasis a q u
  let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
  let S := ws.sum
  let v := inverseCDF (bs.zip (ws.map (fun w => w / S))) seed₁
  let dp := boundaryPlus u v
  let dm := boundaryMinus u v
  if seed₂ < dm / (dp + dm) then u + dp • v else u - dm • v
/-- State is (fractional vector, phase stopping count, retained constraint count). -/
abbrev RoundingState (n : ℕ) := (Fin n → ℝ) × ℕ × ℕ
/-- A move preserves the phase prefix until the phase stopping count is reached.
Only at a new phase start is an active count at most three independently rounded,
one coordinate per move with its own seed. -/
def phaseMove (a : Fin (n / 4) → Fin n → ℝ) (st : RoundingState n)
    (seed₁ seed₂ : ℝ) : RoundingState n :=
  let u := st.1
  let active := activeIndices u
  let r := active.length
  if r ≤ st.2.1 ∧ r ≤ 3 then
    match active with
    | [] => st
    | i :: _ => (Function.update u i (if seed₂ < (1 + u i) / 2 then 1 else -1), n, 0)
  else
    let stop := if r ≤ st.2.1 then r / 2 else st.2.1
    let q := if r ≤ st.2.1 then r / 4 else st.2.2
    (roundingStep a q u seed₁ seed₂, stop, q)
/-- Uniform independent seeds, represented as 3n coordinates. -/
abbrev RoundingSeeds (n : ℕ) := Fin (3 * n) → ℝ
/-- Read a seed; out-of-range padding is never used during the n actual moves. -/
def roundingSeed (seeds : RoundingSeeds n) (h : ℕ) : ℝ :=
  if hh : h < 3 * n then seeds ⟨h, hh⟩ else 0
/-- Structural k-step fractional-state iteration. -/
def roundingIteration (a : Fin (n / 4) → Fin n → ℝ) (seeds : RoundingSeeds n) :
    ℕ → RoundingState n
  | 0 => (0, n, 0)
  | k + 1 => phaseMove a (roundingIteration a seeds k)
      (roundingSeed seeds (2 * k)) (roundingSeed seeds (2 * k + 1))

-- @node: def:ordered-boundary-rounding
/-- The prescribed finite exact-real randomized signing map. -/
def orderedBoundaryRounding (n : ℕ) (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) : Signs n :=
  fun i => decide (0 < (roundingIteration a seeds n).1 i)
/-- Independent uniform seed law. -/
def roundingSeedLaw (n : ℕ) : Measure (RoundingSeeds n) := cubeMeasure (3 * n)
/-- Prefix supplied to the algorithm; rows are numbered starting at one. -/
def rowPrefix (rows : ℕ → Fin n → ℝ) : Fin (n / 4) → Fin n → ℝ :=
  fun h => rows (h.val + 1)

/-- Active membership is exactly strict interior membership of the coordinate.](goal) This uses [the stated conclusion](goal). -/
-- @node: mem_activeIndices
lemma mem_activeIndices (u : Fin n → ℝ) (i : Fin n) :
    i ∈ activeIndices u ↔ |u i| < 1 := by
  simp [activeIndices]

/-- Taking a finite nonempty minimum preserves strict positivity. Under [the stated conditions](hyp:hne,hpos), [the asserted mathematical result follows](goal). -/
-- @node: finiteMin_pos
lemma finiteMin_pos (xs : List ℝ) (hne : xs ≠ [])
    (hpos : ∀ x ∈ xs, 0 < x) : 0 < finiteMin xs := by
  have hf (ys : List ℝ) : ∀ a : ℝ, 0 < a →
      (∀ y ∈ ys, 0 < y) → 0 < ys.foldl min a := by
    induction ys with
    | nil => intro a ha _; exact ha
    | cons y ys ih =>
      intro a ha hy
      exact ih (min a y) (lt_min ha (hy y (by simp)))
        (fun z hz => hy z (by simp [hz]))
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x xs =>
    exact hf xs x (hpos x (by simp)) (fun y hy => hpos y (by simp [hy]))

/-- [ A nonempty finite minimum is one of the entries and is no larger than any entry.](goal) Under [the stated conditions](hyp:hne). -/
-- @node: finiteMin_spec
lemma finiteMin_spec (xs : List ℝ) (hne : xs ≠ []) :
    finiteMin xs ∈ xs ∧ ∀ x ∈ xs, finiteMin xs ≤ x := by
  have hf (ys : List ℝ) : ∀ a : ℝ,
      ys.foldl min a ∈ a :: ys ∧ ∀ x ∈ a :: ys, ys.foldl min a ≤ x := by
    induction ys with
    | nil => intro a; simp
    | cons y ys ih =>
      intro a
      obtain ⟨hm, hl⟩ := ih (min a y)
      constructor
      · rcases List.mem_cons.mp hm with hm | hm
        · change ys.foldl min (min a y) ∈ a :: y :: ys
          rw [hm]
          rcases le_total a y with h | h
          · simp [min_eq_left h]
          · simp [min_eq_right h]
        · simp [hm]
      · intro x hx
        have hmin := hl (min a y) (by simp)
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hmin.trans (min_le_left _ _)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hmin.trans (min_le_right _ _)
          · exact hl x (by simp [hx])
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x xs => exact hf xs x

/-- [ A nonzero direction supported inside the active coordinates has positive
positive boundary distance; sign guards keep every candidate denominator positive.](goal) Under [the stated conditions](hyp:hsupport,hv). -/
-- @node: boundaryPlus_pos
lemma boundaryPlus_pos (u v : Fin n → ℝ)
    (hsupport : ∀ i, v i ≠ 0 → |u i| < 1) (hv : v ≠ 0) :
    0 < boundaryPlus u v := by
  unfold boundaryPlus
  apply finiteMin_pos
  · intro he
    have hex : ∃ i, v i ≠ 0 := by
      by_contra h
      apply hv
      funext i
      simpa using (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hex
    have hm : i ∈ activeIndices u := (mem_activeIndices u i).mpr (hsupport i hi)
    have hc : ∃ t : ℝ,
        (if 0 < v i then some ((1 - u i) / v i)
         else if v i < 0 then some ((1 + u i) / (-v i)) else none) = some t := by
      rcases lt_or_gt_of_ne hi with hn | hp
      · exact ⟨(1 + u i) / (-v i), by simp [hn, not_lt.mpr hn.le]⟩
      · exact ⟨(1 - u i) / v i, by simp [hp]⟩
    obtain ⟨t, ht⟩ := hc
    have : t ∈ (activeIndices u).filterMap (fun i =>
        if 0 < v i then some ((1 - u i) / v i)
        else if v i < 0 then some ((1 + u i) / (-v i)) else none) := by
      exact List.mem_filterMap.mpr ⟨i, hm, ht⟩
    rw [he] at this
    simp at this
  · intro t ht
    obtain ⟨i, hi, ht⟩ := List.mem_filterMap.mp ht
    have hu := (abs_lt.mp ((mem_activeIndices u i).mp hi))
    split_ifs at ht with hp hn
    · have he := Option.some.inj ht
      rw [← he]
      exact div_pos (by linarith) hp
    · have he := Option.some.inj ht
      rw [← he]
      exact div_pos (by linarith) (neg_pos.mpr hn)

/-- [ Moving by the positive boundary distance stays inside the cube and hits a boundary.
This uses the actual finite minimum, without a symmetry or generic-position assumption.](goal) Under [the stated conditions](hyp:hu,hsupport,hv). -/
-- @node: boundaryPlus_hits_cube
lemma boundaryPlus_hits_cube (u v : Fin n → ℝ) (hu : ∀ i, |u i| ≤ 1)
    (hsupport : ∀ i, v i ≠ 0 → |u i| < 1) (hv : v ≠ 0) :
    (∀ i, |u i + boundaryPlus u v * v i| ≤ 1) ∧
    (∃ i, |u i| < 1 ∧ |u i + boundaryPlus u v * v i| = 1) := by
  let candidates := (activeIndices u).filterMap (fun i =>
    if 0 < v i then some ((1 - u i) / v i)
    else if v i < 0 then some ((1 + u i) / (-v i)) else none)
  have hp := boundaryPlus_pos u v hsupport hv
  have he : candidates ≠ [] := by
    intro h
    have hz : boundaryPlus u v = 0 := by
      change finiteMin candidates = 0
      rw [h]
      rfl
    linarith
  have hspec := finiteMin_spec candidates he
  have hmin (t : ℝ) (ht : t ∈ candidates) : boundaryPlus u v ≤ t := hspec.2 t ht
  constructor
  · intro i
    have hui := abs_le.mp (hu i)
    apply abs_le.mpr
    rcases lt_trichotomy (v i) 0 with hn | hz | hn
    · have hm : (1 + u i) / (-v i) ∈ candidates := by
        apply List.mem_filterMap.mpr
        exact ⟨i, (mem_activeIndices u i).mpr (hsupport i hn.ne),
          by simp [hn, not_lt.mpr hn.le]⟩
      have hh := (le_div_iff₀ (neg_pos.mpr hn)).mp (hmin _ hm)
      have hprod : boundaryPlus u v * v i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le hn.le
      constructor <;> nlinarith
    · simp only [hz, mul_zero, add_zero]
      exact hui
    · have hm : (1 - u i) / v i ∈ candidates := by
        apply List.mem_filterMap.mpr
        exact ⟨i, (mem_activeIndices u i).mpr (hsupport i hn.ne'), by simp [hn]⟩
      have hh := (le_div_iff₀ hn).mp (hmin _ hm)
      have hprod : 0 ≤ boundaryPlus u v * v i := mul_nonneg hp.le hn.le
      constructor <;> linarith
  · obtain ⟨i, hi, ht⟩ := List.mem_filterMap.mp hspec.1
    refine ⟨i, (mem_activeIndices u i).mp hi, ?_⟩
    change (if 0 < v i then some ((1 - u i) / v i)
      else if v i < 0 then some ((1 + u i) / (-v i)) else none) =
        some (boundaryPlus u v) at ht
    split_ifs at ht with hn hn
    · have ht := Option.some.inj ht
      have hh := (div_eq_iff hn.ne').mp ht
      rw [show u i + boundaryPlus u v * v i = 1 by linarith]
      norm_num
    · have ht := Option.some.inj ht
      have hh := (div_eq_iff (neg_ne_zero.mpr hn.ne)).mp ht
      rw [show u i + boundaryPlus u v * v i = -1 by nlinarith]
      norm_num

/-- [ Reversing a nonzero active direction gives a positive negative boundary distance.](goal) Under [the stated conditions](hyp:hsupport,hv). -/
-- @node: boundaryMinus_pos
lemma boundaryMinus_pos (u v : Fin n → ℝ)
    (hsupport : ∀ i, v i ≠ 0 → |u i| < 1) (hv : v ≠ 0) :
    0 < boundaryMinus u v := by
  apply boundaryPlus_pos u (-v)
  · intro i hi
    apply hsupport i
    simpa using hi
  · simpa using hv

/-- [ The asymmetric boundary coin is a probability strictly between zero and one.](goal) Under [the stated conditions](hyp:hp,hm). -/
-- @node: boundary_coin_probability
lemma boundary_coin_probability (dp dm : ℝ) (hp : 0 < dp) (hm : 0 < dm) :
    0 < dm / (dp + dm) ∧ dm / (dp + dm) < 1 := by
  have hd : 0 < dp + dm := add_pos hp hm
  exact ⟨div_pos hm hd, (div_lt_one hd).mpr (by linarith)⟩

/-- [ The prescribed asymmetric coin makes each direction increment mean zero.](goal) Under [the stated conditions](hyp:hp,hm). -/
-- @node: boundary_coin_mean_zero
lemma boundary_coin_mean_zero (dp dm : ℝ) (hp : 0 < dp) (hm : 0 < dm) :
    dm / (dp + dm) * dp + (1 - dm / (dp + dm)) * (-dm) = 0 := by
  have hd : dp + dm ≠ 0 := ne_of_gt (add_pos hp hm)
  field_simp
  ring

/-- [ The scalar increment variance is exactly the product of the two boundary distances.](goal) Under [the stated conditions](hyp:hp,hm). -/
-- @node: boundary_coin_second_moment
lemma boundary_coin_second_moment (dp dm : ℝ) (hp : 0 < dp) (hm : 0 < dm) :
    dm / (dp + dm) * dp ^ 2 + (1 - dm / (dp + dm)) * (-dm) ^ 2 = dp * dm := by
  have hd : dp + dm ≠ 0 := ne_of_gt (add_pos hp hm)
  field_simp
  ring

/-- The active-coordinate list has no repetitions. [The asserted mathematical result follows](goal). -/
-- @node: activeIndices_nodup
lemma activeIndices_nodup (u : Fin n → ℝ) : (activeIndices u).Nodup := by
  exact List.Nodup.filter _ (List.nodup_finRange n)

/-- A cube move that fixes inactive coordinates and hits a new boundary strictly
reduces the active count, regardless of the number of other simultaneous hits. Under [the stated conditions](hyp:hfix,hhit), [the asserted mathematical result follows](goal). -/
-- @node: activeIndices_strict_decrease
lemma activeIndices_strict_decrease (u w : Fin n → ℝ)
    (hfix : ∀ j, ¬|u j| < 1 → w j = u j)
    (hhit : ∃ i, |u i| < 1 ∧ |w i| = 1) :
    (activeIndices w).length < (activeIndices u).length := by
  obtain ⟨i, hi, hwi⟩ := hhit
  have he : activeIndices w =
      ((activeIndices u).erase i).filter (fun j => decide (|w j| < 1)) := by
    rw [(activeIndices_nodup u).erase_eq_filter]
    unfold activeIndices
    rw [List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro j _
    by_cases hji : j = i
    · subst j
      simp [hwi]
    · by_cases hj : |u j| < 1
      · simp [hji, hj]
      · simp [hj, hfix j hj]
  rw [he]
  have hle := List.length_filter_le (fun j => decide (|w j| < 1)) ((activeIndices u).erase i)
  have hm := (mem_activeIndices u i).mpr hi
  rw [List.length_erase_of_mem hm] at hle
  have hpos := List.length_pos_of_mem hm
  omega

/-- [ A positive boundary move fixes inactive coordinates and strictly decreases their count.](goal) Under [the stated conditions](hyp:hu,hsupport,hv). -/
-- @node: boundaryPlus_active_progress
lemma boundaryPlus_active_progress (u v : Fin n → ℝ) (hu : ∀ i, |u i| ≤ 1)
    (hsupport : ∀ i, v i ≠ 0 → |u i| < 1) (hv : v ≠ 0) :
    (activeIndices (fun i => u i + boundaryPlus u v * v i)).length <
      (activeIndices u).length := by
  apply activeIndices_strict_decrease
  · intro j hj
    have hz : v j = 0 := by
      by_contra h
      exact hj (hsupport j h)
    simp [hz]
  · exact (boundaryPlus_hits_cube u v hu hsupport hv).2

/-- [ Negative boundary moves have the same cube and progress guarantees by direction reversal.](goal) Under [the stated conditions](hyp:hu,hsupport,hv). -/
-- @node: boundaryMinus_hits_cube_and_progress
lemma boundaryMinus_hits_cube_and_progress (u v : Fin n → ℝ) (hu : ∀ i, |u i| ≤ 1)
    (hsupport : ∀ i, v i ≠ 0 → |u i| < 1) (hv : v ≠ 0) :
    (∀ i, |u i - boundaryMinus u v * v i| ≤ 1) ∧
    (activeIndices (fun i => u i - boundaryMinus u v * v i)).length <
      (activeIndices u).length := by
  have hs : ∀ i, (-v) i ≠ 0 → |u i| < 1 := by
    intro i hi
    apply hsupport i
    simpa using hi
  have hn : -v ≠ 0 := by simpa using hv
  have hc := (boundaryPlus_hits_cube u (-v) hu hs hn).1
  have hp := boundaryPlus_active_progress u (-v) hu hs hn
  simpa only [boundaryMinus, Pi.neg_apply, mul_neg, sub_eq_add_neg] using And.intro hc hp

/-- [ Once the selected nullspace direction is nonzero and active-supported, the
actual asymmetric rounding step preserves the cube and makes strict progress.](goal) Under [the stated conditions](hyp:hu). -/
-- @node: roundingStep_progress_of_direction
lemma roundingStep_progress_of_direction (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u : Fin n → ℝ) (seed₁ seed₂ : ℝ) (hu : ∀ i, |u i| ≤ 1) :
    let bs := nullspaceBasis a q u
    let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
    let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed₁
    (∀ i, v i ≠ 0 → |u i| < 1) → v ≠ 0 →
      (∀ i, |roundingStep a q u seed₁ seed₂ i| ≤ 1) ∧
      (activeIndices (roundingStep a q u seed₁ seed₂)).length < (activeIndices u).length := by
  dsimp only
  intro hs hv
  let bs := nullspaceBasis a q u
  let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
  let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed₁
  change (∀ i, v i ≠ 0 → |u i| < 1) at hs
  change v ≠ 0 at hv
  change (∀ i, |(if seed₂ < boundaryMinus u v / (boundaryPlus u v + boundaryMinus u v)
    then u + boundaryPlus u v • v else u - boundaryMinus u v • v) i| ≤ 1) ∧
    (activeIndices (if seed₂ < boundaryMinus u v / (boundaryPlus u v + boundaryMinus u v)
      then u + boundaryPlus u v • v else u - boundaryMinus u v • v)).length <
        (activeIndices u).length
  split_ifs
  · exact ⟨(boundaryPlus_hits_cube u v hu hs hv).1,
      boundaryPlus_active_progress u v hu hs hv⟩
  · exact boundaryMinus_hits_cube_and_progress u v hu hs hv

/-- [ Setting a coordinate to a boundary value removes exactly that active index.](goal) Under [the stated conditions](hyp:hb). -/
-- @node: activeIndices_update_boundary
lemma activeIndices_update_boundary (u : Fin n → ℝ) (i : Fin n) (b : ℝ)
    (hb : |b| = 1) :
    activeIndices (Function.update u i b) = (activeIndices u).erase i := by
  rw [(activeIndices_nodup u).erase_eq_filter]
  unfold activeIndices
  rw [List.filter_filter]
  apply List.filter_congr
  intro j _
  by_cases hji : j = i
  · subst j
    simp [hb]
  · simp [hji]

/-- [ A terminal boundary update removes one active coordinate and preserves the cube.](goal) Under [the stated conditions](hyp:hu,hi,hb). -/
-- @node: terminal_update_progress
lemma terminal_update_progress (u : Fin n → ℝ) (i : Fin n) (b : ℝ)
    (hu : ∀ j, |u j| ≤ 1) (hi : |u i| < 1) (hb : |b| = 1) :
    (∀ j, |Function.update u i b j| ≤ 1) ∧
    (activeIndices (Function.update u i b)).length = (activeIndices u).length - 1 := by
  constructor
  · intro j
    by_cases hji : j = i
    · subst j; simp [hb]
    · simpa [Function.update_of_ne hji] using hu j
  · rw [activeIndices_update_boundary u i b hb]
    exact List.length_erase_of_mem ((mem_activeIndices u i).mpr hi)

/-- [ The actual terminal branch preserves the cube and strictly decreases the active count.](goal) Under [the stated conditions](hyp:hu,hsmall,hne). -/
-- @node: phaseMove_terminal_progress
lemma phaseMove_terminal_progress (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (seed₁ seed₂ : ℝ)
    (hu : ∀ j, |st.1 j| ≤ 1)
    (hsmall : (activeIndices st.1).length ≤ st.2.1 ∧ (activeIndices st.1).length ≤ 3)
    (hne : activeIndices st.1 ≠ []) :
    (∀ j, |(phaseMove a st seed₁ seed₂).1 j| ≤ 1) ∧
    (activeIndices (phaseMove a st seed₁ seed₂).1).length < (activeIndices st.1).length := by
  cases ha : activeIndices st.1 with
  | nil => exact (hne ha).elim
  | cons i is =>
    have hi : |st.1 i| < 1 := (mem_activeIndices st.1 i).mp (by rw [ha]; simp)
    have hb : |(if seed₂ < (1 + st.1 i) / 2 then (1 : ℝ) else -1)| = 1 := by
      split_ifs <;> norm_num
    have ht := terminal_update_progress st.1 i _ hu hi hb
    have hstep : (phaseMove a st seed₁ seed₂).1 =
        Function.update st.1 i (if seed₂ < (1 + st.1 i) / 2 then 1 else -1) := by
      dsimp only [phaseMove]
      rw [if_pos hsmall]
      simp only [ha]
    rw [hstep]
    refine ⟨ht.1, ?_⟩
    rw [ht.2, ha]
    simp

/-- Terminal single-coordinate rounding preserves its current conditional mean. [The asserted mathematical result follows](goal). -/
-- @node: terminal_coin_mean
lemma terminal_coin_mean (u : ℝ) :
    ((1 + u) / 2) * 1 + (1 - (1 + u) / 2) * (-1) = u := by
  ring

/-- [ The terminal centered increment has variance one minus the current squared coordinate.](goal) -/
-- @node: terminal_coin_increment_second_moment
lemma terminal_coin_increment_second_moment (u : ℝ) :
    ((1 + u) / 2) * (1 - u) ^ 2 + (1 - (1 + u) / 2) * (-1 - u) ^ 2 = 1 - u ^ 2 := by
  ring

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
