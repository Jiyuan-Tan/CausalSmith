module
public import Causalean.Stat.Concentration.BoundedVariation.ChainingReconstruction

/-!
# Second moments of one signed dyadic increment level

The finite-class sign maximal estimate bounds the adjacent increments on one
control grid. Keeping this estimate separate makes the later infinite-level
triangle inequality independent of grid indexing.
-/

public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- If [every one of the m + 1 consecutive increments of a finite time
grid has summed squared path increments at most δ](hyp:hδ), then [the
sign-average of the squared largest absolute signed increment over the grid
is at most 32 (1 + log(m + 1)) δ](goal).
-/
theorem signed_grid_abs_max_energy_le {m n : ℕ}
    (w : Fin n → Path) (t : Fin (m + 2) → Time) (δ : ℝ)
    (hδ : ∀ i : Fin (m + 1),
      (∑ j, (w j (t i.succ) - w j (t i.castSucc)) ^ 2) ≤ δ) :
    (∑ σ : Fin n → Bool,
      (Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (m + 1) =>
          |∑ j, (if σ j then (1 : ℝ) else -1) *
            (w j (t i.succ) - w j (t i.castSucc))|)) ^ 2) /
      (2 ^ n : ℝ) ≤ 32 * (1 + Real.log (m + 1)) * δ := by
  /- Rewrite the square of the finite supremum of absolute values as the
  supremum of squares, using monotonicity of squaring on nonnegative reals.
  The result is `signMaxEnergy` and follows from
  `signed_grid_increment_max_energy_le`. -/
  classical
  let a : Fin (m + 1) → Fin n → ℝ :=
    fun i j => w j (t i.succ) - w j (t i.castSucc)
  let X : (Fin n → Bool) → Fin (m + 1) → ℝ :=
    fun σ i => ∑ j, (if σ j then (1 : ℝ) else -1) * a i j
  have hmax (σ : Fin n → Bool) :
      (Finset.univ.sup' Finset.univ_nonempty (fun i => |X σ i|)) ^ 2 =
        Finset.univ.sup' Finset.univ_nonempty (fun i => (X σ i) ^ 2) := by
    let M := Finset.univ.sup' Finset.univ_nonempty (fun i => |X σ i|)
    have hM : 0 ≤ M :=
      (abs_nonneg (X σ 0)).trans
        (Finset.le_sup' (fun i : Fin (m + 1) => |X σ i|) (by simp))
    apply le_antisymm
    · obtain ⟨i, _, hi⟩ :=
        Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => |X σ i|)
      rw [hi]
      simpa only [sq_abs, abs_abs] using
        (Finset.le_sup' (fun i : Fin (m + 1) => (X σ i) ^ 2)
          (Finset.mem_univ i))
    · apply Finset.sup'_le
      intro i _
      have hi : |X σ i| ≤ M :=
        Finset.le_sup' (fun i : Fin (m + 1) => |X σ i|) (by simp)
      nlinarith [abs_nonneg (X σ i), sq_abs (X σ i)]
  have heq :
      (∑ σ : Fin n → Bool,
        (Finset.univ.sup' Finset.univ_nonempty (fun i => |X σ i|)) ^ 2) /
        (2 ^ n : ℝ) = signMaxEnergy a := by
    unfold signMaxEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro σ _
    exact hmax σ
  change (∑ σ : Fin n → Bool,
      (Finset.univ.sup' Finset.univ_nonempty (fun i => |X σ i|)) ^ 2) /
      (2 ^ n : ℝ) ≤ _
  rw [heq]
  exact signed_grid_increment_max_energy_le w t δ hδ

/-- Suppose a scalar control u is [nondecreasing](hyp:hmono), [zero at
time zero](hyp:hzero), and [dominates the summed squared path increments
over every interval](hyp:henergy), and [the dyadic grids](hyp:grid) are
[monotone at every level](hyp:hgridmono) and [place their i-th level-k
point at control value i/2^k times the terminal value](hyp:hgridval). Then
at every level k [the sign-average of the squared maximal signed increment
is at most 32 (1 + log 2^(k+1)) times u(1)/2^(k+1)](goal).
-/
theorem signedDyadicIncrementMax_energy_le {n : ℕ} (w : Fin n → Path)
    (u : Path) (hmono : Monotone (u : Time → ℝ)) (hzero : u timeZero = 0)
    (henergy : ∀ s t : Time, s ≤ t →
      (∑ j, (w j t - w j s) ^ 2) ≤ u t - u s)
    (grid : ∀ k : ℕ, Fin (2 ^ k + 1) → Time)
    (hgridmono : ∀ k, Monotone (grid k))
    (hgridval : ∀ k i,
      u (grid k i) = ((i.val : ℝ) / (2 ^ k : ℝ)) * u timeOne)
    (k : ℕ) :
    (∑ σ : Fin n → Bool, (signedDyadicIncrementMax w grid k σ) ^ 2) /
      (2 ^ n : ℝ) ≤
      32 * (1 + Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) *
        (u timeOne / (2 : ℝ) ^ (k + 1)) := by
  /- Identify the `2^(k+1)` edges with `Fin (m+1)` for
  `m = 2^(k+1)-1`. Monotonicity orders each edge, and `hgridval` makes its
  control increment exactly `u(1)/2^(k+1)`. Apply
  `signed_grid_abs_max_energy_le`. -/
  classical
  let m := 2 ^ (k + 1) - 1
  have hp : 1 ≤ 2 ^ (k + 1) := by
    have : 0 < 2 ^ (k + 1) := by positivity
    omega
  have hm : m + 1 = 2 ^ (k + 1) := by
    dsimp [m]
    omega
  let t : Fin (m + 2) → Time := fun i => grid (k + 1) (i.cast (by omega))
  have hδ : ∀ i : Fin (m + 1),
      (∑ j, (w j (t i.succ) - w j (t i.castSucc)) ^ 2) ≤
        u timeOne / (2 : ℝ) ^ (k + 1) := by
    intro i
    have hs : t i.castSucc ≤ t i.succ := by
      dsimp [t]
      apply hgridmono
      exact_mod_cast Nat.le_succ i.val
    have h := henergy _ _ hs
    have hv (x : Fin (m + 2)) :
        u (t x) = ((x.val : ℝ) / (2 ^ (k + 1) : ℝ)) * u timeOne := by
      simpa [t, Fin.cast] using hgridval (k + 1) (x.cast (by omega))
    rw [hv, hv] at h
    convert h using 1 <;>
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] <;> ring
  have hbound := signed_grid_abs_max_energy_le w t
    (u timeOne / (2 : ℝ) ^ (k + 1)) hδ
  have hindex : ∀ σ : Fin n → Bool,
      signedDyadicIncrementMax w grid k σ =
        Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (m + 1) =>
            |∑ j, (if σ j then (1 : ℝ) else -1) *
              (w j (t i.succ) - w j (t i.castSucc))|) := by
    intro σ
    unfold signedDyadicIncrementMax
    have hedge (i : Fin (m + 1)) :
        grid (k + 1) (i.cast hm).succ = t i.succ ∧
        grid (k + 1) (i.cast hm).castSucc = t i.castSucc := by
      constructor <;> dsimp [t]
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      let j : Fin (m + 1) := i.cast hm.symm
      have hij : j.cast hm = i := Fin.ext rfl
      have hj := hedge j
      rw [← hij, hj.1, hj.2]
      exact Finset.le_sup'
        (fun i : Fin (m + 1) =>
          |∑ l, (if σ l then (1 : ℝ) else -1) *
            (w l (t i.succ) - w l (t i.castSucc))|)
        (Finset.mem_univ j)
    · apply Finset.sup'_le
      intro i _
      have hi := hedge i
      rw [← hi.1, ← hi.2]
      exact Finset.le_sup'
        (fun i : Fin (2 ^ (k + 1)) =>
          |∑ l, (if σ l then (1 : ℝ) else -1) *
            (w l (grid (k + 1) i.succ) - w l (grid (k + 1) i.castSucc))|)
        (Finset.mem_univ (i.cast hm))
  simp_rw [hindex]
  have hmr : (m : ℝ) + 1 = ((2 ^ (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hm
  rw [hmr] at hbound
  exact hbound

end Causalean.Stat.Concentration.BoundedVariation
