module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ExactCalibrations

/-! # Exact calibrated singleton cancellation

The normalized covariance equation cancels the mixed-margin second moment in
all four cells. The fair risk equation matches the comparator. Uniform finite
priors reproduce both local two-sign averages, with the roots substituted.
-/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The two local mixed tables have identical averages whenever the normalized
root equation holds. [the documented result](goal) Under [the stated assumptions](hyp:hroot). -/
-- @node: localMixedCell_singleton_matching
lemma localMixedCell_singleton_matching (η ζ u : ℝ)
    (hroot : mixedEquation η ζ u (mixedRoot η ζ u) = 0) (a y : Bool) :
    signAverage (fun s => localMixedCell false s a y ![η, ζ, u]) =
      signAverage (fun s => localMixedCell true s a y ![η, ζ, u]) := by
  have hcov := mixedEquation_covariance_matching η ζ u _ hroot
  have hmoment := Real.sin_sq_add_cos_sq (Real.pi*u/2)
  simp [signAverage, Fintype.sum_prod_type, localSignField, signValue] at hcov
  cases a <;> cases y <;>
    simp [signAverage, Fintype.sum_prod_type, localMixedCell, tableCell,
      localSignField, signValue]
  · linear_combination -4*hcov + 8*η*ζ*mixedRoot η ζ u * hmoment
  · linear_combination 4*hcov - 8*η*ζ*mixedRoot η ζ u * hmoment
  · linear_combination 4*hcov - 8*η*ζ*mixedRoot η ζ u * hmoment
  · linear_combination -4*hcov + 8*η*ζ*mixedRoot η ζ u * hmoment

/-- Two distinct coordinates of the uniform Boolean prior are independent fair
signs; the other coordinates contribute exactly their multiplicity. [the documented result](goal) Under [the stated assumptions](hyp:hij,F). -/
-- @node: signPrior_pair_sum
lemma signPrior_pair_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (F : Bool × Bool → ℝ) :
    (∑ σ : ι → Bool, F (σ i, σ j)) =
      (Fintype.card (ι → Bool) : ℝ) * signAverage F := by
  classical
  let flip (i : ι) : (ι → Bool) ≃ (ι → Bool) :=
    { toFun := fun σ => Function.update σ i (!(σ i))
      invFun := fun σ => Function.update σ i (!(σ i))
      left_inv := by
        intro σ
        funext l
        by_cases h : l = i
        · subst l; simp
        · simp [Function.update_of_ne h]
      right_inv := by
        intro σ
        funext l
        by_cases h : l = i
        · subst l; simp
        · simp [Function.update_of_ne h] }
  have hi : (∑ σ : ι → Bool, F ((flip i σ) i, (flip i σ) j)) =
      ∑ σ : ι → Bool, F (σ i, σ j) := (flip i).sum_comp (fun σ => F (σ i, σ j))
  have hj : (∑ σ : ι → Bool, F ((flip j σ) i, (flip j σ) j)) =
      ∑ σ : ι → Bool, F (σ i, σ j) := (flip j).sum_comp (fun σ => F (σ i, σ j))
  have hij' : (∑ σ : ι → Bool, F ((flip i (flip j σ)) i, (flip i (flip j σ)) j)) =
      ∑ σ : ι → Bool, F (σ i, σ j) := ((flip j).trans (flip i)).sum_comp (fun σ => F (σ i, σ j))
  have hpoint (σ : ι → Bool) :
      F (σ i, σ j) + F ((flip i σ) i, (flip i σ) j) +
        F ((flip j σ) i, (flip j σ) j) +
        F ((flip i (flip j σ)) i, (flip i (flip j σ)) j) = 4 * signAverage F := by
    simp only [flip, Equiv.coe_fn_mk, Function.update_self,
      Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
    cases σ i <;> cases σ j <;>
      simp [signAverage, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring
  have hsum := congrArg (fun f : (ι → Bool) → ℝ => ∑ σ, f σ) (funext hpoint)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hi, hj, hij'] at hsum
  unfold signAverage at *
  linarith

/-- [A positive cell count gives two distinct endpoint indices.](goal) Under [the stated assumptions](hyp:hk,x). -/
-- @node: cellIndex_lt
lemma cellIndex_lt (k : ℕ) (hk : 1 ≤ k) (x : Covariate) : cellIndex k x < k := by
  have h := min_le_left (k-1) ((⌊(k : ℝ)*(x : ℝ)⌋ : ℤ).toNat)
  unfold cellIndex
  omega

/-- [Even at the rightmost endpoint, the selected within-cell coordinate lies
in the closed unit interval. [the documented result](goal) Under [the stated assumptions](hyp:hk). -/
-- @node: cellCoord_mem_unit
lemma cellCoord_mem_unit (k : ℕ) (hk : 1 ≤ k) (x : Covariate) :
    cellCoord k x ∈ Set.Icc (0 : ℝ) 1 := by
  have hnonneg : 0 ≤ (k : ℝ)*(x : ℝ) := mul_nonneg (Nat.cast_nonneg _) x.property.1
  have hfnonneg : 0 ≤ (⌊(k : ℝ)*(x : ℝ)⌋ : ℤ) := Int.floor_nonneg.mpr hnonneg
  have hcast : (((⌊(k : ℝ)*(x : ℝ)⌋ : ℤ).toNat : ℕ) : ℝ) =
      ((⌊(k : ℝ)*(x : ℝ)⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hfnonneg
  have hfloor := Int.floor_le ((k : ℝ)*(x : ℝ))
  have hnext := Int.lt_floor_add_one ((k : ℝ)*(x : ℝ))
  have hupper : (k : ℝ)*(x : ℝ) ≤ k := by
    nlinarith [x.property.2, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hkcast : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by
    rw [Nat.cast_sub hk]; norm_num
  unfold cellCoord cellIndex
  rcases le_total (k-1) ((⌊(k : ℝ)*(x : ℝ)⌋ : ℤ).toNat) with h | h
  · rw [min_eq_left h]
    have hle : ((k-1 : ℕ) : ℝ) ≤ ((⌊(k : ℝ)*(x : ℝ)⌋ : ℤ).toNat : ℝ) :=
      Nat.cast_le.mpr h
    constructor <;> linarith
  · rw [min_eq_right h, hcast]
    constructor <;> linarith

/-- [The full finite prior reproduces the exact local cancellation at each covariate.](goal) Under [the stated assumptions](hyp:hk,x). Under [the stated assumptions](hyp:hroot). -/
-- @node: mixedCells_singleton_matching
lemma mixedCells_singleton_matching (k : ℕ) (hk : 1 ≤ k) (η ζ : ℝ)
    (x : Covariate)
    (hroot : mixedEquation η ζ (cellCoord k x) (mixedRoot η ζ (cellCoord k x)) = 0)
    (a y : Bool) :
    (∑ σ : Fin (k+1) → Bool, mixedCells false k σ η ζ a y x) =
      ∑ σ : Fin (k+1) → Bool, mixedCells true k σ η ζ a y x := by
  let i : Fin (k+1) := ⟨min (cellIndex k x) k, Nat.lt_succ_of_le (min_le_right _ _)⟩
  let j : Fin (k+1) := ⟨min (cellIndex k x+1) k, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hij : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [i, j] at hv
    have hc := cellIndex_lt k hk x
    omega
  change (∑ σ : Fin (k+1) → Bool,
    localMixedCell false (σ i, σ j) a y ![η, ζ, cellCoord k x]) =
      ∑ σ : Fin (k+1) → Bool,
        localMixedCell true (σ i, σ j) a y ![η, ζ, cellCoord k x]
  rw [signPrior_pair_sum i j hij (fun s => localMixedCell false s a y ![η, ζ, cellCoord k x]),
    signPrior_pair_sum i j hij (fun s => localMixedCell true s a y ![η, ζ, cellCoord k x]),
    localMixedCell_singleton_matching η ζ (cellCoord k x) hroot]

/-- [Validity transfers the cancellation to the actual ambient laws, so the
fallback of the totalized construction is never used. [the documented result](goal) Under [the stated assumptions](hyp:hvalid,x,hroot). Under [the stated assumptions](hyp:hk). -/
-- @node: mixedLaw_singleton_matching
lemma mixedLaw_singleton_matching (k : ℕ) (hk : 1 ≤ k) (η ζ : ℝ)
    (hvalid : ∀ b σ, ValidCells (mixedCells b k σ η ζ)) (x : Covariate)
    (hroot : mixedEquation η ζ (cellCoord k x) (mixedRoot η ζ (cellCoord k x)) = 0)
    (a y : Bool) :
    (∑ σ : Fin (k+1) → Bool, (mixedLaw false k σ η ζ).cells a y x) =
      ∑ σ : Fin (k+1) → Bool, (mixedLaw true k σ η ζ).cells a y x := by
  simp only [mixedLaw, totalCellLaw, dif_pos (hvalid _ _), lawFromCells]
  exact mixedCells_singleton_matching k hk η ζ x hroot a y

/-- [Exact calibrated risk matching implies matching of each fair singleton
cell; the control arm uses the mean-zero sign field. [the documented result](goal) Under [the stated assumptions](hyp:hmatch). -/
-- @node: localFairCell_singleton_matching
lemma localFairCell_singleton_matching (t δ u : ℝ)
    (hmatch : signAverage (fun s => riskShift t
      (fairRoot t δ u + δ*localSignField u s)) =
      riskShift (comparatorEffect t δ) (fairRoot t δ u)) (a y : Bool) :
    signAverage (fun s => localFairCell true s a y ![t, δ, u]) =
      localFairCell false (false, false) a y ![t, δ, u] := by
  simp [signAverage, Fintype.sum_prod_type, localSignField, signValue] at hmatch
  cases a <;> cases y <;>
    simp [signAverage, Fintype.sum_prod_type, localFairCell, localSignField, signValue]
  · ring
  · ring
  · linarith
  · linarith

/-- The full fair sign prior has exactly the deterministic comparator's
singleton cells whenever the calibrated risk equation holds. [the documented result](goal) Under [the stated assumptions](hyp:x,hmatch). Under [the stated assumptions](hyp:hk). -/
-- @node: fairCells_singleton_matching
lemma fairCells_singleton_matching (k : ℕ) (hk : 1 ≤ k) (t δ : ℝ)
    (x : Covariate)
    (hmatch : signAverage (fun s => riskShift t
      (fairRoot t δ (cellCoord k x) + δ*localSignField (cellCoord k x) s)) =
      riskShift (comparatorEffect t δ) (fairRoot t δ (cellCoord k x))) (a y : Bool) :
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      (∑ σ : Fin (k+1) → Bool, fairCells true k σ t δ a y x) =
      fairCells false k (fun _ => false) t δ a y x := by
  let i : Fin (k+1) := ⟨min (cellIndex k x) k, Nat.lt_succ_of_le (min_le_right _ _)⟩
  let j : Fin (k+1) := ⟨min (cellIndex k x+1) k, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hij : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [i, j] at hv
    have hc := cellIndex_lt k hk x
    omega
  change (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      (∑ σ : Fin (k+1) → Bool,
        localFairCell true (σ i, σ j) a y ![t, δ, cellCoord k x]) =
      localFairCell false (false, false) a y ![t, δ, cellCoord k x]
  rw [signPrior_pair_sum i j hij (fun s => localFairCell true s a y ![t, δ, cellCoord k x]),
    localFairCell_singleton_matching t δ (cellCoord k x) hmatch]
  have hc : (Fintype.card (Fin (k+1) → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- [Validity transfers fair singleton matching to the actual law and comparator.](goal) Under [the stated assumptions](hyp:hk,x). Under [the stated assumptions](hyp:hvalid,hcomparator,hmatch). -/
-- @node: fairLaw_singleton_matching
lemma fairLaw_singleton_matching (k : ℕ) (hk : 1 ≤ k) (t δ : ℝ)
    (hvalid : ∀ σ, ValidCells (fairCells true k σ t δ))
    (hcomparator : ValidCells (fairCells false k (fun _ => false) t δ)) (x : Covariate)
    (hmatch : signAverage (fun s => riskShift t
      (fairRoot t δ (cellCoord k x) + δ*localSignField (cellCoord k x) s)) =
      riskShift (comparatorEffect t δ) (fairRoot t δ (cellCoord k x))) (a y : Bool) :
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      (∑ σ : Fin (k+1) → Bool, (fairLaw k σ t δ).cells a y x) =
      (fairComparator k t δ).cells a y x := by
  simp only [fairLaw, fairComparator, totalCellLaw, dif_pos (hvalid _),
    dif_pos hcomparator, lawFromCells]
  exact fairCells_singleton_matching k hk t δ x hmatch a y

/-- [Rate scaling by a nonnegative exponent stays inside the fixed amplitude
neighborhood for every positive cell count. [the documented result](goal) Under [the stated assumptions](hyp:hk). Under [the stated assumptions](hyp:hε,hγ). -/
-- @node: calibrated_amplitude_abs_le
lemma calibrated_amplitude_abs_le (ε γ : ℝ) (hε : 0 ≤ ε) (hγ : 0 ≤ γ)
    (k : ℕ) (hk : 1 ≤ k) : |ε*(k : ℝ)^(-γ)| ≤ ε := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 ≤ (k : ℝ)^(-γ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [abs_of_nonneg (mul_nonneg hε hp)]
  calc
    _ ≤ ε*1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hk' (neg_nonpos.mpr hγ)) hε
    _ = ε := mul_one ε

end CausalSmith.Stat.LogoddsLowsmoothFrontier
