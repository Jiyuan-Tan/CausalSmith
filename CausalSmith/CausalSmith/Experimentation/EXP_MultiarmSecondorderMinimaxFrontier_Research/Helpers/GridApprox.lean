import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.RationalLPBridge
import Mathlib.Algebra.Order.Round

/-! Posterior-mean lower certificates and barycenter upper certificates. -/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

variable {K n M : ℕ}

/-- Rational probability vectors on response-count orbits. -/
def IsRationalPrior (nu : CountVec K n → ℚ) : Prop :=
  (∀ m, 0 ≤ nu m) ∧ ∑ m, nu m = 1

/-- Prior predictive mass of an allocation-observation orbit. -/
noncomputable def predictiveMass (_c : RatContrast K) (nu : CountVec K n → ℚ)
    (r : AllocVec K n) (x : ObsVec r) : ℚ :=
  ∑ m, nu m * orbitLik m r x

/-- Prior predictive target numerator. -/
noncomputable def predictiveTarget (c : RatContrast K) (nu : CountVec K n → ℚ)
    (r : AllocVec K n) (x : ObsVec r) : ℚ :=
  ∑ m, nu m * orbitLik m r x * tauCountRat c m

/-- Posterior-mean Bayes lower certificate for an allocation orbit. -/
noncomputable def allocationBayesRisk (c : RatContrast K) (nu : CountVec K n → ℚ)
    (r : AllocVec K n) : ℚ :=
  (∑ m, nu m * tauCountRat c m ^ 2) -
    ∑ x : ObsVec r,
      if _h : 0 < predictiveMass c nu r x then
        predictiveTarget c nu r x ^ 2 / predictiveMass c nu r x else 0

/-- The unrestricted prior lower certificate `B`. -/
noncomputable def lowerCertificate (c : RatContrast K) (nu : CountVec K n → ℚ) : ℝ :=
  sInf {v : ℝ | ∃ r : AllocVec K n, v = (allocationBayesRisk c nu r : ℝ)}

/-- Worst-case risk of a rational allocation mixture and real orbit rule. -/
noncomputable def upperCertificate (c : RatContrast K) (pi : GridPi K n)
    (delta : ∀ r : AllocVec K n, ObsVec r → ℝ) : ℝ :=
  ⨆ m : CountVec K n,
    ∑ r, (pi r : ℝ) * ∑ x : ObsVec r,
      (orbitLik m r x : ℝ) * (delta r x - (tauCountRat c m : ℝ)) ^ 2

/-- Full rational dual multipliers for every equality, nonnegativity, and risk row. -/
structure GridDualMultipliers (K n M : ℕ) where
  normalizationUpper : ℚ
  normalizationLower : ℚ
  occupancyUpper : ∀ r : AllocVec K n, ObsVec r → ℚ
  occupancyLower : ∀ r : AllocVec K n, ObsVec r → ℚ
  piNonnegative : AllocVec K n → ℚ
  weightNonnegative : RationalGridWeight K n M
  risk : CountVec K n → ℚ

-- @node: decodeGridDualMultipliers
/-- Decode the row multipliers of the generic rational program into the
paper's named normalization, occupancy, sign, and risk multipliers. -/
noncomputable def decodeGridDualMultipliers
    (y : GR K n M → ℚ) : GridDualMultipliers K n M where
  normalizationUpper := y (.norm false)
  normalizationLower := y (.norm true)
  occupancyUpper r x := y (.occ r x false)
  occupancyLower r x := y (.occ r x true)
  piNonnegative r := y (.piNonneg r)
  weightNonnegative r x g := y (.wNonneg r x g)
  risk m := y (.risk m)

/-- Feasibility of all full-dual multipliers and every primal-coordinate stationarity row. -/
def GridDualFeasible (c : RatContrast K) (y : GridDualMultipliers K n M) : Prop :=
  0 ≤ y.normalizationUpper ∧ 0 ≤ y.normalizationLower ∧
  (∀ r x, 0 ≤ y.occupancyUpper r x ∧ 0 ≤ y.occupancyLower r x) ∧
  (∀ r, 0 ≤ y.piNonnegative r) ∧
  (∀ r x g, 0 ≤ y.weightNonnegative r x g) ∧
  (∀ m, 0 ≤ y.risk m) ∧
  (∑ m, y.risk m = 1) ∧
  (∀ r, y.normalizationUpper - y.normalizationLower -
      ∑ x, (y.occupancyUpper r x - y.occupancyLower r x) -
      y.piNonnegative r = 0) ∧
  (∀ r x g, y.occupancyUpper r x - y.occupancyLower r x -
      y.weightNonnegative r x g +
      ∑ m, y.risk m * orbitLik m r x *
        (gammaMC M c g - tauCountRat c m) ^ 2 = 0)

/-- Objective of the full rational dual in the sign convention of `RationalLP.Program`. -/
def gridDualObjective (y : GridDualMultipliers K n M) : ℚ :=
  y.normalizationLower - y.normalizationUpper

/-- Exact rational primal/dual certificate, coupled by full dual feasibility and equal objectives. -/
def ExactGridPrimalDualCertificate (c : RatContrast K)
    (pi : GridPi K n) (w : GridWeight K n M) (u : ℚ)
    (nu : CountVec K n → ℚ) : Prop :=
  ∃ (wQ : RationalGridWeight K n M) (y : GridDualMultipliers K n M),
    w = rationalGridWeightToReal M wQ ∧
    GridLPFeasible K n M c pi wQ u ∧
    GridDualFeasible c y ∧
    nu = y.risk ∧ u = gridDualObjective y

/-- `δ` is exactly the conditional barycenter `Σ_g g w/π`, with zero convention. -/
def IsGridBarycenter (c : RatContrast K) (pi : GridPi K n)
    (w : GridWeight K n M) (delta : ∀ r : AllocVec K n, ObsVec r → ℝ) : Prop :=
  ∀ r x, delta r x = if _h : 0 < pi r then
    ∑ g, (gammaMC M c g : ℝ) * w r x g / (pi r : ℝ) else 0

/-- [the grid resolution is positive](hyp:hM), [the stated side condition holds](hyp:hv), [the nearest grid error property holds](goal). -/
lemma nearest_grid_error (c : RatContrast K) (M : ℕ) (hM : 0 < M)
    (v : ℝ) (hv : v ∈ Set.Icc (-(hRat c : ℝ)) (hRat c : ℝ)) :
    ∃ j : Fin (2 * M + 1),
      |v - (gammaMC M c j : ℝ)| ≤ (hRat c : ℝ) / (2 * M) := by
  have hLc : 0 < LcRat c := by
    have hnonneg : 0 ≤ LcRat c := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hne : LcRat c ≠ 0 := by
      intro hsum
      apply c.nonzero
      funext a
      apply abs_eq_zero.mp
      exact congrFun
        ((Fintype.sum_eq_zero_iff_of_nonneg (fun a => abs_nonneg (c a))).mp hsum) a
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hhQ : 0 < hRat c := by
    simp only [hRat]
    positivity
  have hh : 0 < (hRat c : ℝ) := by exact_mod_cast hhQ
  let x : ℝ := (v + (hRat c : ℝ)) * M / (hRat c : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (mul_nonneg (by linarith [hv.1]) (Nat.cast_nonneg M)) (le_of_lt hh)
  have hx2 : x ≤ (2 * M : ℕ) := by
    dsimp [x]
    rw [div_le_iff₀ hh]
    have := hv.2
    push_cast
    nlinarith
  let z : ℤ := round x
  have hz0 : 0 ≤ z := by
    have hr := abs_sub_round x
    by_contra h
    have hz : z ≤ -1 := by omega
    have hcast : (z : ℝ) ≤ -1 := by exact_mod_cast hz
    dsimp [z] at hcast ⊢
    rw [abs_of_nonneg] at hr
    · linarith
    · linarith
  have hz2 : z ≤ (2 * M : ℕ) := by
    have hr := abs_sub_round x
    by_contra h
    have hz : (2 * M : ℤ) + 1 ≤ z := by omega
    have hcast : ((2 * M : ℤ) : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hz
    dsimp [z] at hcast ⊢
    norm_num [Nat.cast_mul] at hx2 hcast
    have hsign : x - (round x : ℝ) ≤ 0 := by linarith [hx2, hcast]
    rw [abs_of_nonpos hsign] at hr
    linarith [hx2, hcast]
  let j : Fin (2 * M + 1) := ⟨z.toNat, by
    have hnat := Int.toNat_le_toNat hz2
    have : z.toNat ≤ 2 * M := by simpa [Int.toNat_of_nonneg hz0] using hnat
    omega⟩
  refine ⟨j, ?_⟩
  have hjz : ((j : ℕ) : ℤ) = z := by
    dsimp [j]
    simp [Int.toNat_of_nonneg hz0]
  have hjzR : ((j : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast hjz
  have hr := abs_sub_round x
  change |v - (-((hRat c : ℚ)) + (j : ℚ) * hRat c / M : ℚ)| ≤ _
  push_cast
  rw [hjzR]
  have hMR : (0 : ℝ) < M := by positivity
  have hid : v - (-((hRat c : ℝ)) + (z : ℝ) * (hRat c : ℝ) / M) =
      ((hRat c : ℝ) / M) * (x - (z : ℝ)) := by
    dsimp [x]
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos (div_pos hh hMR)]
  calc
    (hRat c : ℝ) / M * |x - (z : ℝ)| ≤ (hRat c : ℝ) / M * (1 / 2) := by
      gcongr
    _ = (hRat c : ℝ) / (2 * M) := by field_simp

-- @node: GridRowIndex
/-- A grid row index pairs an allocation-count vector with a compatible observed-success vector. -/
abbrev GridRowIndex (K n M : ℕ) :=
  Bool ⊕ (Σ r : AllocVec K n, ObsVec r × Bool) ⊕
    AllocVec K n ⊕ (Σ r : AllocVec K n, ObsVec r × Fin (2 * M + 1)) ⊕
      CountVec K n

-- @node: gridRowEquiv
/-- The grid row equiv property holds. -/
def gridRowEquiv : GR K n M ≃ GridRowIndex K n M where
  toFun
    | .norm b => .inl b
    | .occ r z b => .inr (.inl ⟨r, (z, b)⟩)
    | .piNonneg r => .inr (.inr (.inl r))
    | .wNonneg r z g => .inr (.inr (.inr (.inl ⟨r, (z, g)⟩)))
    | .risk m => .inr (.inr (.inr (.inr m)))
  invFun
    | .inl b => .norm b
    | .inr (.inl ⟨r, (z, b)⟩) => .occ r z b
    | .inr (.inr (.inl r)) => .piNonneg r
    | .inr (.inr (.inr (.inl ⟨r, (z, g)⟩))) => .wNonneg r z g
    | .inr (.inr (.inr (.inr m))) => .risk m
  left_inv i := by cases i <;> rfl
  right_inv i := by
    rcases i with b | i
    · rfl
    rcases i with i | i
    · rcases i with ⟨r, z, b⟩
      rfl
    rcases i with r | i
    · rfl
    rcases i with i | m
    · rcases i with ⟨r, z, g⟩
      rfl
    · rfl

-- @node: sum_grid_rows
/-- [the sums grid rows](goal). -/
lemma sum_grid_rows (f : GR K n M → ℚ) :
    ∑ i, f i =
      ∑ b, f (.norm b) +
      ∑ r, ∑ z, ∑ b, f (.occ r z b) +
      ∑ r, f (.piNonneg r) +
      ∑ r, ∑ z, ∑ g, f (.wNonneg r z g) +
      ∑ m, f (.risk m) := by
  rw [show (∑ i, f i) = ∑ j : GridRowIndex K n M, f ((gridRowEquiv).symm j) by
    exact Fintype.sum_equiv gridRowEquiv _ _
      (fun i => congrArg f (gridRowEquiv.symm_apply_apply i).symm)]
  simp only [GridRowIndex, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp [gridRowEquiv]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  ring

-- @node: exists_exact_grid_primal_dual_certificate
/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [The generic rational optimizer decodes to the paper's exact primal/dual certificate, and its rational objective is the real grid-program value.](goal) -/
lemma exists_exact_grid_primal_dual_certificate (c : RatContrast K)
    (hn : 0 < n) (hM : 0 < M) :
    ∃ (pi : GridPi K n) (w : GridWeight K n M) (u : ℚ)
      (nu : CountVec K n → ℚ),
      ExactGridPrimalDualCertificate c pi w u nu ∧
      (u : ℝ) = gridLPValue K n M c hn hM := by
  classical
  obtain ⟨x, y, hx, hy, hxy, hvalue⟩ :=
    gridProgram_optimal_primal_dual_exists (c := c) hn hM
  let pi : GridPi K n := decodePi x
  let wQ : RationalGridWeight K n M := decodeW x
  let w : GridWeight K n M := rationalGridWeightToReal M wQ
  let u : ℚ := decodeU x
  let yd : GridDualMultipliers K n M := decodeGridDualMultipliers y
  let nu : CountVec K n → ℚ := fun m => y (.risk m)
  have hprimal : GridLPFeasible K n M c pi wQ u := by
    exact (gridProgram_feasible_iff c x).mp hx
  have hdual : GridDualFeasible c yd := by
    refine ⟨hy.1 (.norm false), hy.1 (.norm true), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r z
      exact ⟨hy.1 (.occ r z false), hy.1 (.occ r z true)⟩
    · exact fun r => hy.1 (.piNonneg r)
    · exact fun r z g => hy.1 (.wNonneg r z g)
    · exact dualRiskRow_nonneg hy
    · exact dualRiskRow_sum_eq_one hy
    · intro r
      have hs := hy.2 (gvEquiv K n M (.inr (.inl r)))
      simp only [gridProgram, gvEquiv, Equiv.symm_apply_apply] at hs
      rw [show (∑ i : GR K n M,
          y i * rowCoeff c i (.inr (.inl r))) =
          y (.norm false) - y (.norm true) -
            ∑ z, (y (.occ r z false) - y (.occ r z true)) -
            y (.piNonneg r) by
        rw [sum_grid_rows]
        simp [rowCoeff]
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
        ring] at hs
      simpa [yd, decodeGridDualMultipliers, objCoeff] using hs
    · intro r z g
      have hs := hy.2 (gvEquiv K n M (.inr (.inr ⟨r, (z, g)⟩)))
      simp only [gridProgram, gvEquiv, Equiv.symm_apply_apply] at hs
      rw [show (∑ i : GR K n M,
          y i * rowCoeff c i (.inr (.inr ⟨r, (z, g)⟩))) =
          y (.occ r z false) - y (.occ r z true) - y (.wNonneg r z g) +
            ∑ m, y (.risk m) * orbitLik m r z *
              (gammaMC M c g - tauCountRat c m) ^ 2 by
        rw [sum_grid_rows]
        simp [rowCoeff, Finset.sum_ite_irrel]
        rw [show (∑ x : ObsVec r, ∑ g' : Fin (2 * M + 1),
            if z = x ∧ g = g' then -y (.wNonneg r x g') else 0) =
            -y (.wNonneg r z g) by
          calc
            _ = ∑ g' : Fin (2 * M + 1),
                if z = z ∧ g = g' then -y (.wNonneg r z g') else 0 := by
                  apply Finset.sum_eq_single z
                  · intro z' _ hz'
                    have hzz' : z ≠ z' := Ne.symm hz'
                    simp only [hzz', false_and, if_false, Finset.sum_const_zero]
                  · intro hz
                    exact (hz (Finset.mem_univ z)).elim
            _ = -y (.wNonneg r z g) := by
                  simp only [eq_self, true_and]
                  simpa only [eq_comm] using (Fintype.sum_ite_eq' g
                    (fun g' => -y (.wNonneg r z g')))]
        rw [show (∑ m, y (.risk m) *
            (orbitLik m r z * (gammaMC M c g - tauCountRat c m) ^ 2)) =
            ∑ m, y (.risk m) * orbitLik m r z *
              (gammaMC M c g - tauCountRat c m) ^ 2 by
          apply Finset.sum_congr rfl
          intro m _
          ring]
        ring] at hs
      simpa [yd, decodeGridDualMultipliers, objCoeff] using hs
  have huobj : (gridProgram c).objective x = u := gridProgram_objective c x
  have hdualobj : (gridProgram c).dualObjective y = gridDualObjective yd := by
    rw [gridProgram_dualObjective_eq_normalization]
    rfl
  refine ⟨pi, w, u, nu, ?_, ?_⟩
  · refine ⟨wQ, yd, rfl, hprimal, hdual, rfl, ?_⟩
    rw [← hdualobj, ← hxy, huobj]
  · rw [← huobj]
    exact hvalue

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
