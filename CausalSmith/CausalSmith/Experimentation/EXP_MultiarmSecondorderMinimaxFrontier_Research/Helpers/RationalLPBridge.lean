import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Basic

/-!
Exact finite-dimensional encoding of the rational grid program.  The bridge
uses rational LP attainment to show that the real infimum is attained at a
rational feasible objective value.
-/

open scoped BigOperators
open Finset Set

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

/-- The inst decidable equals causal smith. -/
noncomputable local instance (priority := low) {α : Type} : DecidableEq α :=
  Classical.decEq α

-- @node: GV
/-- The grid-program variable index is the disjoint union of the epigraph coordinate, allocation masses, and allocation–observation–action weights. -/
abbrev GV (K n M : ℕ) : Type :=
  PUnit ⊕ (AllocVec K n ⊕ (Σ r : AllocVec K n, ObsVec r × Fin (2 * M + 1)))

-- @node: gvEquiv
/-- The gv equiv property holds. -/
noncomputable def gvEquiv (K n M : ℕ) :
    GV K n M ≃ Fin (Fintype.card (GV K n M)) := Fintype.equivFin _

-- @node: gvDecode
/-- The gv decode property holds. -/
noncomputable def gvDecode (x : Fin (Fintype.card (GV K n M)) → ℚ) : GV K n M → ℚ :=
  fun v => x (gvEquiv K n M v)

-- @node: gvDot_eq
/-- [the gv dot equals property holds](goal). -/
lemma gvDot_eq (a : GV K n M → ℚ)
    (x : Fin (Fintype.card (GV K n M)) → ℚ) :
    Causalean.Mathlib.Optimization.RationalLP.dot
      (fun j => a ((gvEquiv K n M).symm j)) x =
      ∑ v, a v * gvDecode x v := by
  unfold Causalean.Mathlib.Optimization.RationalLP.dot gvDecode
  exact Fintype.sum_equiv (gvEquiv K n M).symm _ _ (fun _ => by simp)

-- @node: objCoeff
/-- The obj coeff property holds. -/
def objCoeff : GV K n M → ℚ
  | .inl _ => 1
  | .inr _ => 0

-- @node: sum_objCoeff
/-- [the sums obj coeff](goal). -/
lemma sum_objCoeff (z : GV K n M → ℚ) :
    ∑ v, objCoeff v * z v = z (.inl PUnit.unit) := by
  rw [Fintype.sum_sum_type]
  simp [objCoeff]

-- @node: GR
/-- The grid-program row index distinguishes normalization, nonnegativity, occupancy, and risk constraints. -/
inductive GR (K n M : ℕ) where
  | norm (lower : Bool)
  | occ (r : AllocVec K n) (x : ObsVec r) (lower : Bool)
  | piNonneg (r : AllocVec K n)
  | wNonneg (r : AllocVec K n) (x : ObsVec r) (g : Fin (2 * M + 1))
  | risk (m : CountVec K n)
  deriving Fintype

/-- The [grid-program row index type is finite](goal). -/
add_decl_doc instFintypeGR

-- @node: rowCoeff
/-- The row coeff property holds. -/
noncomputable def rowCoeff (c : RatContrast K) : GR K n M → GV K n M → ℚ
  | .norm lower, .inr (.inl _) => if lower then -1 else 1
  | .occ r x lower, .inr (.inl r') =>
      if r' = r then (if lower then 1 else -1) else 0
  | .occ r x lower, .inr (.inr ⟨r', (x', _)⟩) =>
      if h : r' = r then
        if h ▸ x' = x then (if lower then -1 else 1) else 0
      else 0
  | .piNonneg r, .inr (.inl r') => if r' = r then -1 else 0
  | .wNonneg r x g, .inr (.inr ⟨r', (x', g')⟩) =>
      if h : r' = r then if h ▸ x' = x ∧ g' = g then -1 else 0 else 0
  | .risk m, .inl _ => -1
  | .risk m, .inr (.inr ⟨r, (x, g)⟩) =>
      orbitLik m r x * (gammaMC M c g - tauCountRat c m) ^ 2
  | _, _ => 0

-- @node: rowBound
/-- The row bound property holds. -/
def rowBound : GR K n M → ℚ
  | .norm false => 1
  | .norm true => -1
  | _ => 0

-- @node: gridProgram
/-- The rational grid program minimizes its epigraph coordinate subject to normalization, nonnegativity, occupancy, and risk inequalities. -/
noncomputable def gridProgram (c : RatContrast K) :
    Causalean.Mathlib.Optimization.RationalLP.Program (GR K n M) (Fintype.card (GV K n M)) where
  A i j := rowCoeff c i ((gvEquiv K n M).symm j)
  b := rowBound
  c j := objCoeff ((gvEquiv K n M).symm j)

-- @node: encodePoint
/-- A paper-level primal point is encoded as a vector of rational grid-program variables. -/
noncomputable def encodePoint (pi : GridPi K n) (w : RationalGridWeight K n M)
    (u : ℚ) : Fin (Fintype.card (GV K n M)) → ℚ :=
  fun j => match (gvEquiv K n M).symm j with
    | .inl _ => u
    | .inr (.inl r) => pi r
    | .inr (.inr ⟨r, (x, g)⟩) => w r x g

-- @node: decodeU
/-- The decoded epigraph coordinate is the grid-program vector’s distinguished scalar entry. -/
noncomputable def decodeU (x : Fin (Fintype.card (GV K n M)) → ℚ) : ℚ :=
  gvDecode x (.inl PUnit.unit)

-- @node: decodePi
/-- The decoded allocation mass reads the corresponding allocation coordinate of a grid-program vector. -/
noncomputable def decodePi (x : Fin (Fintype.card (GV K n M)) → ℚ) : GridPi K n :=
  fun r => gvDecode x (.inr (.inl r))

-- @node: decodeW
/-- The decoded joint weight reads the corresponding allocation–observation–action coordinate of a grid-program vector. -/
noncomputable def decodeW (x : Fin (Fintype.card (GV K n M)) → ℚ) :
    RationalGridWeight K n M := fun r y g => gvDecode x (.inr (.inr ⟨r, (y, g)⟩))

-- @node: dot_norm
/-- [the dot norm property holds](goal). -/
lemma dot_norm (c : RatContrast K) (x : Fin (Fintype.card (GV K n M)) → ℚ)
    (lower : Bool) :
    Causalean.Mathlib.Optimization.RationalLP.dot ((gridProgram c).A (.norm lower)) x =
      if lower then -∑ r, decodePi x r else ∑ r, decodePi x r := by
  change Causalean.Mathlib.Optimization.RationalLP.dot
    (fun j => rowCoeff c (.norm lower) ((gvEquiv K n M).symm j)) x = _
  rw [gvDot_eq, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [rowCoeff, decodePi, gvDecode]

-- @node: dot_piNonneg
/-- [the dot pi is nonnegative](goal). -/
lemma dot_piNonneg (c : RatContrast K)
    (x : Fin (Fintype.card (GV K n M)) → ℚ) (r : AllocVec K n) :
    Causalean.Mathlib.Optimization.RationalLP.dot ((gridProgram c).A (.piNonneg r)) x = -decodePi x r := by
  change Causalean.Mathlib.Optimization.RationalLP.dot
    (fun j => rowCoeff c (.piNonneg r) ((gvEquiv K n M).symm j)) x = _
  rw [gvDot_eq, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [rowCoeff, decodePi, gvDecode]

-- @node: dot_wNonneg
/-- [the dot w is nonnegative](goal). -/
lemma dot_wNonneg (c : RatContrast K)
    (x : Fin (Fintype.card (GV K n M)) → ℚ)
    (r : AllocVec K n) (y : ObsVec r) (g : Fin (2 * M + 1)) :
    Causalean.Mathlib.Optimization.RationalLP.dot ((gridProgram c).A (.wNonneg r y g)) x = -decodeW x r y g := by
  change Causalean.Mathlib.Optimization.RationalLP.dot
    (fun j => rowCoeff c (.wNonneg r y g) ((gvEquiv K n M).symm j)) x = _
  rw [gvDot_eq, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  simp [rowCoeff, decodeW, gvDecode]
  change (∑ y' ∈ (Finset.univ : Finset (ObsVec r)),
    (∑ g' ∈ (Finset.univ : Finset (Fin (2 * M + 1))),
      if y' = y ∧ g' = g then
        -x (gvEquiv K n M (.inr (.inr ⟨r, (y', g')⟩))) else 0)) = _
  calc
    _ = ∑ g' ∈ (Finset.univ : Finset (Fin (2 * M + 1))),
        if y = y ∧ g' = g then
          -x (gvEquiv K n M (.inr (.inr ⟨r, (y, g')⟩))) else 0 := by
      apply Finset.sum_eq_single y
      · intro y' _ hy
        simp [hy]
      · simp
    _ = (if y = y ∧ g = g then
          -x (gvEquiv K n M (.inr (.inr ⟨r, (y, g)⟩))) else 0) := by
      apply Finset.sum_eq_single g
      · intro g' _ hg
        simp [hg]
      · simp
    _ = _ := by simp

-- @node: dot_occ
/-- [the dot occ property holds](goal). -/
lemma dot_occ (c : RatContrast K)
    (x : Fin (Fintype.card (GV K n M)) → ℚ)
    (r : AllocVec K n) (y : ObsVec r) (lower : Bool) :
    Causalean.Mathlib.Optimization.RationalLP.dot ((gridProgram c).A (.occ r y lower)) x =
      if lower then decodePi x r - ∑ g, decodeW x r y g
      else ∑ g, decodeW x r y g - decodePi x r := by
  change Causalean.Mathlib.Optimization.RationalLP.dot
    (fun j => rowCoeff c (.occ r y lower) ((gvEquiv K n M).symm j)) x = _
  rw [gvDot_eq, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  simp [rowCoeff, decodePi, decodeW, gvDecode]
  cases lower <;> simp <;> ring

-- @node: dot_risk
/-- [the dot risk property holds](goal). -/
lemma dot_risk (c : RatContrast K)
    (x : Fin (Fintype.card (GV K n M)) → ℚ) (m : CountVec K n) :
    Causalean.Mathlib.Optimization.RationalLP.dot ((gridProgram c).A (.risk m)) x =
      (∑ r, ∑ y, ∑ g, orbitLik m r y * decodeW x r y g *
        (gammaMC M c g - tauCountRat c m) ^ 2) - decodeU x := by
  change Causalean.Mathlib.Optimization.RationalLP.dot
    (fun j => rowCoeff c (.risk m) ((gvEquiv K n M).symm j)) x = _
  rw [gvDot_eq, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  simp [rowCoeff, decodeW, decodeU, gvDecode]
  rw [sub_eq_add_neg, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro g _
  ring

-- @node: decode_encode_u
/-- [the decode encode u property holds](goal). -/
lemma decode_encode_u (pi : GridPi K n) (w : RationalGridWeight K n M) (u : ℚ) :
    gvDecode (encodePoint pi w u) (.inl PUnit.unit) = u := by simp [gvDecode, encodePoint]

-- @node: gridProgram_objective_encode
/-- [the grid program objective encode property holds](goal). -/
lemma gridProgram_objective_encode (c : RatContrast K)
    (pi : GridPi K n) (w : RationalGridWeight K n M) (u : ℚ) :
    (gridProgram c).objective (encodePoint pi w u) = u := by
  rw [Causalean.Mathlib.Optimization.RationalLP.Program.objective]
  change Causalean.Mathlib.Optimization.RationalLP.dot
    (fun j => objCoeff ((gvEquiv K n M).symm j)) (encodePoint pi w u) = u
  rw [gvDot_eq, sum_objCoeff]
  exact decode_encode_u pi w u

-- @node: gridProgram_objective
/-- [the grid program objective property holds](goal). -/
lemma gridProgram_objective (c : RatContrast K)
    (x : Fin (Fintype.card (GV K n M)) → ℚ) :
    (gridProgram c).objective x = decodeU x := by
  rw [Causalean.Mathlib.Optimization.RationalLP.Program.objective]
  change Causalean.Mathlib.Optimization.RationalLP.dot
    (fun j => objCoeff ((gvEquiv K n M).symm j)) x = _
  rw [gvDot_eq, sum_objCoeff]
  rfl

-- @node: gridProgram_feasible_iff
/-- [the grid program feasible if and only if property holds](goal). -/
lemma gridProgram_feasible_iff (c : RatContrast K)
    (x : Fin (Fintype.card (GV K n M)) → ℚ) :
    (gridProgram c).PrimalFeasible x ↔
      GridLPFeasible K n M c (decodePi x) (decodeW x) (decodeU x) := by
  constructor
  · intro hx
    have hnormU := hx (.norm false)
    have hnormL := hx (.norm true)
    rw [dot_norm] at hnormU hnormL
    simp [gridProgram, rowBound] at hnormU hnormL
    refine ⟨le_antisymm hnormU (by linarith), ?_, ?_, ?_, ?_⟩
    · intro r y
      have hu := hx (.occ r y false)
      have hl := hx (.occ r y true)
      rw [dot_occ] at hu hl
      simp [gridProgram, rowBound] at hu hl
      linarith
    · intro r
      have h := hx (.piNonneg r)
      rw [dot_piNonneg] at h
      simp [gridProgram, rowBound] at h
      linarith
    · intro r y g
      have h := hx (.wNonneg r y g)
      rw [dot_wNonneg] at h
      simp [gridProgram, rowBound] at h
      linarith
    · intro m
      have h := hx (.risk m)
      rw [dot_risk] at h
      simp [gridProgram, rowBound] at h
      linarith
  · intro h row
    cases row with
    | norm lower =>
        rw [dot_norm]
        cases lower <;> simp [gridProgram, rowBound, h.1] <;> linarith
    | occ r y lower =>
        rw [dot_occ]
        cases lower <;> simp [gridProgram, rowBound, h.2.1 r y] <;> linarith
    | piNonneg r =>
        rw [dot_piNonneg]
        simp [gridProgram, rowBound]
        exact h.2.2.1 r
    | wNonneg r y g =>
        rw [dot_wNonneg]
        simp [gridProgram, rowBound]
        exact h.2.2.2.1 r y g
    | risk m =>
        rw [dot_risk]
        simp [gridProgram, rowBound]
        exact h.2.2.2.2 m

-- @node: decode_encode_pi
/-- [the decode encode pi property holds](goal). -/
lemma decode_encode_pi (pi : GridPi K n) (w : RationalGridWeight K n M) (u : ℚ) :
    decodePi (encodePoint pi w u) = pi := by
  funext r
  simp [decodePi, gvDecode, encodePoint]

-- @node: decode_encode_w
/-- [the decode encode w property holds](goal). -/
lemma decode_encode_w (pi : GridPi K n) (w : RationalGridWeight K n M) (u : ℚ) :
    decodeW (encodePoint pi w u) = w := by
  funext r y g
  simp [decodeW, gvDecode, encodePoint]

-- @node: gridProgram_encode_feasible
/-- [the grid program encode feasible property holds](goal). -/
lemma gridProgram_encode_feasible (c : RatContrast K)
    {pi : GridPi K n} {w : RationalGridWeight K n M} {u : ℚ}
    (h : GridLPFeasible K n M c pi w u) :
    (gridProgram c).PrimalFeasible (encodePoint pi w u) := by
  rw [gridProgram_feasible_iff, decode_encode_pi, decode_encode_w]
  change GridLPFeasible K n M c pi w
    (gvDecode (encodePoint pi w u) (.inl PUnit.unit))
  rw [decode_encode_u]
  exact h

-- @node: gridLPFeasible_u_nonneg
/-- [the grid lpfeasible u is nonnegative](goal). -/
lemma gridLPFeasible_u_nonneg {pi : GridPi K n} {w : RationalGridWeight K n M}
    {u : ℚ} (h : GridLPFeasible K n M c pi w u) : 0 ≤ u := by
  let m₀ : CountVec K n := scheduleCounts (fun _ _ => false)
  calc
    0 ≤ ∑ r, ∑ x, ∑ g,
        orbitLik m₀ r x * w r x g * (gammaMC M c g - tauCountRat c m₀) ^ 2 := by
      apply Finset.sum_nonneg
      intro r _
      apply Finset.sum_nonneg
      intro x _
      apply Finset.sum_nonneg
      intro g _
      exact mul_nonneg (mul_nonneg (orbitLik_nonneg m₀ r x) (h.2.2.2.1 r x g))
        (sq_nonneg _)
    _ ≤ u := h.2.2.2.2 m₀

-- @node: gridLPFeasible_exists
/-- [the grid resolution is positive](hyp:hM), [the grid lpfeasible exists](goal). -/
lemma gridLPFeasible_exists (c : RatContrast K) (hM : 0 < M) :
    ∃ (pi : GridPi K n) (w : RationalGridWeight K n M) (u : ℚ),
      GridLPFeasible K n M c pi w u := by
  classical
  have hK : K ≠ 0 := by
    intro hzero
    apply c.nonzero
    funext a
    exact Fin.elim0 (hzero ▸ a)
  letI : Nonempty (Arm K) :=
    Fintype.card_pos_iff.mp (by simpa using Nat.pos_of_ne_zero hK)
  let r₀ : AllocVec K n := assignmentCounts (fun _ => Classical.choice inferInstance)
  let g₀ : Fin (2 * M + 1) := ⟨M, by omega⟩
  let pi : GridPi K n := fun r => if r = r₀ then 1 else 0
  let w : RationalGridWeight K n M := fun r _ g =>
    if r = r₀ ∧ g = g₀ then 1 else 0
  let risk : CountVec K n → ℚ := fun m =>
    ∑ r, ∑ x, ∑ g,
      orbitLik m r x * w r x g * (gammaMC M c g - tauCountRat c m) ^ 2
  let u : ℚ := ∑ m, risk m
  refine ⟨pi, w, u, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pi]
  · intro r x
    by_cases hr : r = r₀
    · subst r
      simp [pi, w]
    · simp [pi, w, hr]
  · intro r
    dsimp [pi]
    split <;> norm_num
  · intro r x g
    dsimp [w]
    split <;> norm_num
  · intro m
    change risk m ≤ u
    apply Finset.single_le_sum
    · intro m' _
      dsimp [risk]
      apply Finset.sum_nonneg
      intro r _
      apply Finset.sum_nonneg
      intro x _
      apply Finset.sum_nonneg
      intro g _
      apply mul_nonneg
      · apply mul_nonneg (orbitLik_nonneg m' r x)
        dsimp [w]
        split <;> norm_num
      · exact sq_nonneg _
    · exact Finset.mem_univ m

-- @node: gridProgram_bounded_below
/-- [the grid program bounded below property holds](goal). -/
lemma gridProgram_bounded_below (K n M : ℕ) (c : RatContrast K) :
    ∃ l : ℚ, ∀ x : Fin (Fintype.card (GV K n M)) → ℚ,
      (gridProgram (n := n) (M := M) c).PrimalFeasible x →
      l ≤ (gridProgram (n := n) (M := M) c).objective x := by
  refine ⟨0, ?_⟩
  intro x hx
  rw [gridProgram_objective]
  exact gridLPFeasible_u_nonneg ((gridProgram_feasible_iff c x).mp hx)

set_option maxHeartbeats 800000 in
-- Fourier–Motzkin elimination on the dependent finite coordinate encoding needs extra heartbeats.
-- @node: gridLP_rational_value_exists
/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [the grid lp rational value exists](goal). -/
lemma gridLP_rational_value_exists (K n M : ℕ) (c : RatContrast K)
    (hn : 0 < n) (hM : 0 < M) :
    ∃ q : ℚ, (q : ℝ) = gridLPValue K n M c hn hM := by
  classical
  obtain ⟨pi₀, w₀, u₀, hfeas₀⟩ := gridLPFeasible_exists (n := n) c hM
  let P : Causalean.Mathlib.Optimization.RationalLP.Program (GR K n M) (Fintype.card (GV K n M)) :=
    gridProgram (n := n) (M := M) c
  have hne : ∃ x : Fin (Fintype.card (GV K n M)) → ℚ, P.PrimalFeasible x :=
    ⟨encodePoint pi₀ w₀ u₀, gridProgram_encode_feasible c hfeas₀⟩
  obtain ⟨xStar, hxStar, hopt⟩ :=
    Causalean.Mathlib.Optimization.RationalLP.exists_rational_primal_optimizer
      P hne (by simpa [P] using gridProgram_bounded_below K n M c)
  let q : ℚ := P.objective xStar
  have hqdecode : q = decodeU xStar := gridProgram_objective c xStar
  have hfeasStar : GridLPFeasible K n M c (decodePi xStar) (decodeW xStar) q := by
    rw [hqdecode]
    exact (gridProgram_feasible_iff c xStar).mp hxStar
  let S : Set ℝ := {v : ℝ | ∃ (pi : GridPi K n) (w : RationalGridWeight K n M)
      (u : ℚ), GridLPFeasible K n M c pi w u ∧ v = (u : ℝ)}
  have hSnonempty : S.Nonempty := by
    exact ⟨(u₀ : ℝ), pi₀, w₀, u₀, hfeas₀, rfl⟩
  have hSbounded : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro v ⟨pi, w, u, hfeas, rfl⟩
    exact_mod_cast gridLPFeasible_u_nonneg hfeas
  refine ⟨q, ?_⟩
  change (q : ℝ) = sInf S
  apply le_antisymm
  · apply le_csInf hSnonempty
    rintro v ⟨pi, w, u, hfeas, rfl⟩
    have hqle : q ≤ u := by
      dsimp [q]
      calc
        P.objective xStar ≤ P.objective (encodePoint pi w u) :=
          hopt (encodePoint pi w u) (gridProgram_encode_feasible c hfeas)
        _ = u := by
          dsimp [P]
          exact gridProgram_objective_encode c pi w u
    exact_mod_cast hqle
  · apply csInf_le hSbounded
    exact ⟨decodePi xStar, decodeW xStar, q, hfeasStar, rfl⟩

/-- The exact rational representative supplied by rational LP attainment. -/
-- @node: gridLPValueRat
noncomputable def gridLPValueRat (K n M : ℕ) (c : RatContrast K)
    (hn : 0 < n) (hM : 0 < M) : ℚ :=
  Classical.choose (gridLP_rational_value_exists K n M c hn hM)

/-- [Compatibility name for nonnegativity derived from a risk row.](goal) -/
-- @node: gridLP_u_nonneg
lemma gridLP_u_nonneg {pi : GridPi K n} {w : RationalGridWeight K n M} {u : ℚ}
    (h : GridLPFeasible K n M c pi w u) : 0 ≤ u :=
  gridLPFeasible_u_nonneg h

/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [A rational optimizer coerces to a real feasible objective value.](goal) -/
-- @node: gridLPValue_le_rat
lemma gridLPValue_le_rat (hn : 0 < n) (hM : 0 < M) :
    gridLPValue K n M c hn hM ≤ (gridLPValueRat K n M c hn hM : ℝ) := by
  exact le_of_eq (Classical.choose_spec (gridLP_rational_value_exists K n M c hn hM)).symm

/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [Rational dual multipliers lower-bound every real feasible point.](goal) -/
-- @node: gridLP_dual_bound_real
lemma gridLP_dual_bound_real (hn : 0 < n) (hM : 0 < M) :
    (gridLPValueRat K n M c hn hM : ℝ) ≤ gridLPValue K n M c hn hM := by
  exact le_of_eq (Classical.choose_spec (gridLP_rational_value_exists K n M c hn hM))

-- @node: gridLPValue_eq_rat
/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [the grid lpvalue equals rat](goal). -/
lemma gridLPValue_eq_rat (hn : 0 < n) (hM : 0 < M) :
    gridLPValue K n M c hn hM = (gridLPValueRat K n M c hn hM : ℝ) := by
  exact le_antisymm (gridLPValue_le_rat hn hM) (gridLP_dual_bound_real hn hM)

-- @node: gridProgram_optimal_primal_dual_exists
/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [Rational LP strong duality supplies a feasible primal/dual pair whose primal objective is exactly the real grid-program infimum.](goal) -/
lemma gridProgram_optimal_primal_dual_exists (hn : 0 < n) (hM : 0 < M) :
    ∃ (x : Fin (Fintype.card (GV K n M)) → ℚ) (y : GR K n M → ℚ),
      (gridProgram c).PrimalFeasible x ∧
      (gridProgram c).DualFeasible y ∧
      (gridProgram c).objective x = (gridProgram c).dualObjective y ∧
      ((gridProgram c).objective x : ℝ) = gridLPValue K n M c hn hM := by
  classical
  obtain ⟨pi₀, w₀, u₀, hfeas₀⟩ := gridLPFeasible_exists (n := n) c hM
  let P : Causalean.Mathlib.Optimization.RationalLP.Program (GR K n M) (Fintype.card (GV K n M)) :=
    gridProgram (n := n) (M := M) c
  have hne : ∃ x : Fin (Fintype.card (GV K n M)) → ℚ, P.PrimalFeasible x :=
    ⟨encodePoint pi₀ w₀ u₀, gridProgram_encode_feasible c hfeas₀⟩
  obtain ⟨x, y, hx, hy, hduality, hopt⟩ :=
    Causalean.Mathlib.Optimization.RationalLP.exists_rational_optimal_primal_dual
      P hne (by simpa [P] using gridProgram_bounded_below K n M c)
  let q : ℚ := P.objective x
  have hqdecode : q = decodeU x := gridProgram_objective c x
  have hfeas : GridLPFeasible K n M c (decodePi x) (decodeW x) q := by
    rw [hqdecode]
    exact (gridProgram_feasible_iff c x).mp hx
  let S : Set ℝ := {v : ℝ | ∃ (pi : GridPi K n) (w : RationalGridWeight K n M)
      (u : ℚ), GridLPFeasible K n M c pi w u ∧ v = (u : ℝ)}
  have hSne : S.Nonempty := ⟨(u₀ : ℝ), pi₀, w₀, u₀, hfeas₀, rfl⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro v ⟨pi, w, u, hu, rfl⟩
    exact_mod_cast gridLPFeasible_u_nonneg hu
  have hqeq : (q : ℝ) = sInf S := by
    apply le_antisymm
    · apply le_csInf hSne
      rintro v ⟨pi, w, u, hu, rfl⟩
      have hqu : q ≤ u := by
        dsimp [q]
        calc
          P.objective x ≤ P.objective (encodePoint pi w u) :=
            hopt (encodePoint pi w u) (gridProgram_encode_feasible c hu)
          _ = u := by simpa [P] using gridProgram_objective_encode c pi w u
      exact_mod_cast hqu
    · apply csInf_le hSbdd
      exact ⟨decodePi x, decodeW x, q, hfeas, rfl⟩
  refine ⟨x, y, hx, hy, hduality, ?_⟩
  simpa [P, q, gridLPValue, gridLPValueRaw, S] using hqeq

/-- [the dual vector is feasible](hyp:hy), [Risk-row dual multipliers are nonnegative.](goal) -/
-- @node: dualRiskRow_nonneg
lemma dualRiskRow_nonneg {y : GR K n M → ℚ}
    (hy : (gridProgram c).DualFeasible y) :
    ∀ m, 0 ≤ y (.risk m) := by
  exact fun m => hy.1 (.risk m)

/-- [the dual vector is feasible](hyp:hy), [With no epigraph sign row, stationarity at `u` normalizes risk multipliers.](goal) -/
-- @node: dualRiskRow_sum_eq_one
lemma dualRiskRow_sum_eq_one {y : GR K n M → ℚ}
    (hy : (gridProgram c).DualFeasible y) :
    ∑ m, y (.risk m) = 1 := by
  classical
  have hu := hy.2 (gvEquiv K n M (.inl PUnit.unit))
  simp only [gridProgram, gvEquiv, Equiv.symm_apply_apply] at hu
  have hsum :
      (∑ i : GR K n M, y i * rowCoeff c i (.inl PUnit.unit)) =
        ∑ m : CountVec K n, y (.risk m) * (-1) := by
    have hrestrict :
        (∑ i : GR K n M, y i * rowCoeff c i (.inl PUnit.unit)) =
          ∑ i ∈ Finset.univ.image GR.risk,
            y i * rowCoeff c i (.inl PUnit.unit) := by
      symm
      apply Finset.sum_subset
      · exact Finset.image_subset_iff.mpr (fun _ _ => Finset.mem_univ _)
      · intro i _ hi
        cases i <;> simp_all [rowCoeff]
    rw [hrestrict, Finset.sum_image]
    · simp [rowCoeff]
    · intro a _ b _ hab
      injection hab
  rw [hsum] at hu
  simp [objCoeff] at hu
  linarith

/-- [The generic program's dual objective is the difference of the two normalization-row multipliers used by the paper-level decoder.](goal) -/
-- @node: gridProgram_dualObjective_eq_normalization
lemma gridProgram_dualObjective_eq_normalization (c : RatContrast K)
    (y : GR K n M → ℚ) :
    (gridProgram c).dualObjective y =
      y (.norm true) - y (.norm false) := by
  classical
  rw [Causalean.Mathlib.Optimization.RationalLP.Program.dualObjective]
  have hrestrict :
      (∑ i : GR K n M, y i * (gridProgram c).b i) =
        ∑ i ∈ Finset.univ.image GR.norm,
          y i * (gridProgram c).b i := by
    symm
    apply Finset.sum_subset
    · exact Finset.image_subset_iff.mpr (fun _ _ => Finset.mem_univ _)
    · intro i _ hi
      cases i <;> simp_all [gridProgram, rowBound]
  rw [hrestrict, Finset.sum_image]
  · simp [gridProgram, rowBound]
    ring
  · intro a _ b _ hab
    injection hab


end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
