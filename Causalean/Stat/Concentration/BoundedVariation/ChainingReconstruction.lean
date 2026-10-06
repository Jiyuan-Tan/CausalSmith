module
public import Causalean.Stat.Concentration.BoundedVariation.DyadicApproximation

/-!
# Reconstructing a signed path from control quantiles

The compatible dyadic sections of a scalar increment control recover every
point of a continuous signed path. This module separates the deterministic
continuum argument from the later second-moment estimates.
-/

@[expose] public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [The largest absolute signed increment at dyadic level k](goal): given
[a family of n paths](hyp:w), [a family of dyadic time grids, the level-k
grid having 2^k + 1 points](hyp:grid), [a level k](hyp:k), and [a sign
pattern σ on the n paths](hyp:σ), it is [the maximum, over the 2^(k+1)
adjacent pairs of points of the level-(k+1) grid, of the absolute value of
the σ-signed sum of the path increments across that pair](step:1).
-/
noncomputable def signedDyadicIncrementMax {n : ℕ} (w : Fin n → Path)
    (grid : ∀ k : ℕ, Fin (2 ^ k + 1) → Time) (k : ℕ)
    (σ : Fin n → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin (2 ^ (k + 1)) =>
      |∑ j, (if σ j then (1 : ℝ) else -1) *
        (w j (grid (k + 1) i.succ) - w j (grid (k + 1) i.castSucc))|)

/-- If a scalar control u is [nondecreasing](hyp:hmono) and [zero at time
zero](hyp:hzero), [the squared increments of the n paths over every interval
from s to t sum to at most u(t) − u(s)](hyp:henergy), and [the dyadic
grids](hyp:grid) are [monotone at every level](hyp:hgridmono) and [place
their i-th level-k point where the control equals i/2^k times its terminal
value](hyp:hgridval), then for every sign pattern [the maximal signed
increments at successive levels form a summable sequence](goal).

The terms are dominated by a geometric series of ratio 1/√2.
-/
theorem signedDyadicIncrementMax_summable {n : ℕ} (w : Fin n → Path)
    (u : Path) (hmono : Monotone (u : Time → ℝ)) (hzero : u timeZero = 0)
    (henergy : ∀ s t : Time, s ≤ t →
      (∑ j, (w j t - w j s) ^ 2) ≤ u t - u s)
    (grid : ∀ k : ℕ, Fin (2 ^ k + 1) → Time)
    (hgridmono : ∀ k, Monotone (grid k))
    (hgridval : ∀ k i,
      u (grid k i) = ((i.val : ℝ) / (2 ^ k : ℝ)) * u timeOne)
    (σ : Fin n → Bool) :
    Summable (fun k => signedDyadicIncrementMax w grid k σ) := by
  /- Cauchy--Schwarz bounds every signed edge by the square root of `n`
  times the square root of its coefficient energy. Every edge at level
  `k + 1` has control mass `u(1) / 2 ^ (k + 1)`. Compare the maxima with a
  geometric series of ratio `1 / sqrt 2`, including the case `u(1) = 0`. -/
  classical
  have hU : 0 ≤ u timeOne := by
    simpa only [hzero] using hmono (show timeZero ≤ timeOne by
      change (0 : ℝ) ≤ 1; norm_num)
  let r : ℝ := Real.sqrt (1 / 2 : ℝ)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r < 1 := by
    dsimp [r]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num),
      Real.sqrt_nonneg (1 / 2 : ℝ)]
  have hgeom : Summable (fun k : ℕ => (n : ℝ) * Real.sqrt (u timeOne) * r ^ (k + 1)) :=
    ((summable_geometric_of_lt_one hr0 hr1).comp_injective Nat.succ_injective).mul_left _
  have hsqrt_pow (m : ℕ) : Real.sqrt ((1 / 2 : ℝ) ^ m) = r ^ m := by
    induction m with
    | zero => simp [r]
    | succ m ih =>
      rw [pow_succ, Real.sqrt_mul (by norm_num), ih, pow_succ]
  apply Summable.of_nonneg_of_le
    (fun k => by
      unfold signedDyadicIncrementMax
      have h := Finset.le_sup'
        (fun i : Fin (2 ^ (k + 1)) =>
          |∑ j, (if σ j then (1 : ℝ) else -1) *
            (w j (grid (k + 1) i.succ) - w j (grid (k + 1) i.castSucc))|)
        (by simp : (0 : Fin (2 ^ (k + 1))) ∈ Finset.univ)
      exact (abs_nonneg _).trans h)
    ?_ hgeom
  intro k
  apply Finset.sup'_le
  intro i hi
  let a : Fin n → ℝ := fun j => w j (grid (k + 1) i.succ) -
    w j (grid (k + 1) i.castSucc)
  have hs : grid (k + 1) i.castSucc ≤ grid (k + 1) i.succ :=
    hgridmono _ (by exact_mod_cast Nat.le_succ i.val)
  have henergy' : (∑ j, a j ^ 2) ≤ u timeOne / (2 : ℝ) ^ (k + 1) := by
    have h := henergy _ _ hs
    rw [hgridval, hgridval] at h
    dsimp [a]
    convert h using 1 <;> simp only [Fin.val_succ, Fin.val_castSucc,
      Nat.cast_add, Nat.cast_one] <;> ring
  have hcoord (j : Fin n) : |a j| ≤ Real.sqrt (u timeOne / (2 : ℝ) ^ (k + 1)) := by
    rw [Real.le_sqrt (abs_nonneg _) (div_nonneg hU (by positivity)), sq_abs]
    calc
      a j ^ 2 ≤ ∑ l, a l ^ 2 := Finset.single_le_sum (fun l hl => sq_nonneg _) (by simp)
      _ ≤ _ := henergy'
  calc
    |∑ j, (if σ j then (1 : ℝ) else -1) * a j| ≤
        ∑ j, |(if σ j then (1 : ℝ) else -1) * a j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |a j| := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjσ : σ j = true <;> simp [hjσ]
    _ ≤ ∑ _j : Fin n, Real.sqrt (u timeOne / (2 : ℝ) ^ (k + 1)) :=
      Finset.sum_le_sum (fun j _ => hcoord j)
    _ = (n : ℝ) * Real.sqrt (u timeOne) * r ^ (k + 1) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      dsimp [r]
      rw [div_eq_mul_inv, ← inv_pow, Real.sqrt_mul hU]
      norm_num only [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      rw [hsqrt_pow]
      ring

/-- Let [the dyadic grids](hyp:grid) be [compatible across levels: grid
points at different levels with the same dyadic fraction are the same
time](hyp:hgridcompat). If [the level-(k+1) index j is a child (2i or
2i + 1) of the level-k index i](hyp:hparent), then [the absolute signed
path sum at the child grid point is at most the absolute signed sum at the
parent grid point plus the maximal signed increment at level k](goal).
-/
theorem signed_dyadic_chain_step_le {n : ℕ} (w : Fin n → Path)
    (grid : ∀ k : ℕ, Fin (2 ^ k + 1) → Time)
    (hgridcompat : ∀ k i l j,
      ((i.val : ℝ) / (2 ^ k : ℝ)) = ((j.val : ℝ) / (2 ^ l : ℝ)) →
        grid k i = grid l j)
    (σ : Fin n → Bool) (k : ℕ)
    (i : Fin (2 ^ k + 1)) (j : Fin (2 ^ (k + 1) + 1))
    (hparent : j.val = 2 * i.val ∨ j.val = 2 * i.val + 1) :
    |∑ a, (if σ a then (1 : ℝ) else -1) * w a (grid (k + 1) j)| ≤
      |∑ a, (if σ a then (1 : ℝ) else -1) * w a (grid k i)| +
        signedDyadicIncrementMax w grid k σ := by
  /- In the even case `hgridcompat` identifies the two grid points. In the
  odd case construct the edge indexed by `2 * i.val` in `Fin (2^(k+1))`.
  Its `castSucc` is the even child and its `succ` is `j`; apply the triangle
  inequality and `Finset.le_sup'` to that edge. -/
  rcases hparent with hp | hp
  · have hcompat : grid k i = grid (k + 1) j := by
      apply hgridcompat
      simp only [hp]
      push_cast
      rw [pow_succ]
      field_simp
    rw [← hcompat]
    exact le_add_of_nonneg_right (by
      unfold signedDyadicIncrementMax
      exact (abs_nonneg _).trans (Finset.le_sup'
        (fun e : Fin (2 ^ (k + 1)) =>
          |∑ a, (if σ a then (1 : ℝ) else -1) *
            (w a (grid (k + 1) e.succ) - w a (grid (k + 1) e.castSucc))|)
        (Finset.mem_univ (0 : Fin (2 ^ (k + 1))))))
  · have heven : 2 * i.val < 2 ^ (k + 1) := by
      have hj := j.isLt
      omega
    let e : Fin (2 ^ (k + 1)) := ⟨2 * i.val, heven⟩
    have hcompat : grid k i = grid (k + 1) e.castSucc := by
      apply hgridcompat
      simp only [Fin.val_castSucc]
      change (i.val : ℝ) / (2 ^ k : ℝ) = (2 * i.val : ℕ) / (2 ^ (k + 1) : ℝ)
      push_cast
      rw [pow_succ]
      field_simp
    have hj : j = e.succ := Fin.ext hp
    rw [hj, hcompat]
    have hsplit : (∑ a, (if σ a then (1 : ℝ) else -1) * w a (grid (k + 1) e.succ)) =
        (∑ a, (if σ a then (1 : ℝ) else -1) * w a (grid (k + 1) e.castSucc)) +
          (∑ a, (if σ a then (1 : ℝ) else -1) *
            (w a (grid (k + 1) e.succ) - w a (grid (k + 1) e.castSucc))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hsplit]
    have hedge : |∑ a, (if σ a then (1 : ℝ) else -1) *
        (w a (grid (k + 1) e.succ) - w a (grid (k + 1) e.castSucc))| ≤
        signedDyadicIncrementMax w grid k σ := by
      unfold signedDyadicIncrementMax
      exact Finset.le_sup' (fun e : Fin (2 ^ (k + 1)) =>
        |∑ a, (if σ a then (1 : ℝ) else -1) *
          (w a (grid (k + 1) e.succ) - w a (grid (k + 1) e.castSucc))|)
        (Finset.mem_univ e)
    exact (abs_add_le _ _).trans (add_le_add_right hedge _)

/-- Suppose the control u is [zero at time zero](hyp:hzero) and [dominates
the summed squared path increments over every interval](hyp:henergy), and
[the dyadic grids](hyp:grid) [place their i-th level-k point at control
value i/2^k times the terminal value](hyp:hgridval) and [are compatible
across levels](hyp:hgridcompat). If [a chain of indices, one per
level](hyp:i), [starts at index 0](hyp:hi0) and [moves from each level to
a child at the next](hyp:hiparent), then [at every level m the absolute
signed path sum at the chain's grid point is at most the absolute signed
sum at time zero plus the maximal signed increments of levels 0 through
m − 1](goal).
-/
theorem signed_dyadic_chain_finite_le {n : ℕ} (w : Fin n → Path)
    (u : Path) (hzero : u timeZero = 0)
    (henergy : ∀ s t : Time, s ≤ t →
      (∑ j, (w j t - w j s) ^ 2) ≤ u t - u s)
    (grid : ∀ k : ℕ, Fin (2 ^ k + 1) → Time)
    (hgridval : ∀ k i,
      u (grid k i) = ((i.val : ℝ) / (2 ^ k : ℝ)) * u timeOne)
    (hgridcompat : ∀ k i l j,
      ((i.val : ℝ) / (2 ^ k : ℝ)) = ((j.val : ℝ) / (2 ^ l : ℝ)) →
        grid k i = grid l j)
    (i : ∀ k : ℕ, Fin (2 ^ k + 1)) (hi0 : (i 0).val = 0)
    (hiparent : ∀ k, (i (k + 1)).val = 2 * (i k).val ∨
      (i (k + 1)).val = 2 * (i k).val + 1)
    (σ : Fin n → Bool) (m : ℕ) :
    |∑ j, (if σ j then (1 : ℝ) else -1) * w j (grid m (i m))| ≤
      |∑ j, (if σ j then (1 : ℝ) else -1) * w j timeZero| +
        ∑ k ∈ Finset.range m, signedDyadicIncrementMax w grid k σ := by
  /- Induct on m. At level zero, `hgridval` and `hi0` put the grid point
  on the zero-control plateau, so `controlled_path_eq_of_same_control`
  identifies its coefficient values with those at timeZero. For the step,
  `hiparent` and `hgridcompat` identify the parent with the even child;
  the odd child differs by exactly one adjacent grid increment. -/
  have hbase : ∀ j : Fin n, w j (grid 0 (i 0)) = w j timeZero := by
    have hu : u timeZero = u (grid 0 (i 0)) := by
      rw [hzero, hgridval]
      simp [hi0]
    intro j
    exact (controlled_path_eq_of_same_control w u henergy
      timeZero (grid 0 (i 0)) hu j).symm
  induction m with
  | zero =>
      have heq : (∑ j, (if σ j then (1 : ℝ) else -1) * w j (grid 0 (i 0))) =
          ∑ j, (if σ j then (1 : ℝ) else -1) * w j timeZero := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hbase j]
      simpa only [Finset.sum_range_zero, add_zero] using
        le_of_eq (congrArg abs heq)
  | succ m ih =>
      calc
        |∑ j, (if σ j then (1 : ℝ) else -1) * w j (grid (m + 1) (i (m + 1)))| ≤
            |∑ j, (if σ j then (1 : ℝ) else -1) * w j (grid m (i m))| +
              signedDyadicIncrementMax w grid m σ :=
          signed_dyadic_chain_step_le w grid hgridcompat σ m (i m) (i (m + 1))
            (hiparent m)
        _ ≤ (|∑ j, (if σ j then (1 : ℝ) else -1) * w j timeZero| +
            ∑ k ∈ Finset.range m, signedDyadicIncrementMax w grid k σ) +
              signedDyadicIncrementMax w grid m σ := add_le_add ih (le_refl _)
        _ = _ := by rw [Finset.sum_range_succ]; ring

/-- Suppose the control u is [nondecreasing](hyp:hmono), [zero at time
zero](hyp:hzero), and [dominates the summed squared path increments over
every interval](hyp:henergy), and [the dyadic grids](hyp:grid) [place their
i-th level-k point at control value i/2^k times the terminal
value](hyp:hgridval). If [the control at time s equals x times its terminal
value](hyp:hx) and [a chain of indices, one per level](hyp:i), [brackets x
between i_k/2^k and (i_k + 1)/2^k at every level k](hyp:hiapprox), then
[each path coordinate evaluated along the chain's grid points converges to
its value at s](goal).

This holds even when the control has flat intervals.
-/
theorem controlled_grid_coordinate_tendsto {n : ℕ} (w : Fin n → Path)
    (u : Path) (hmono : Monotone (u : Time → ℝ)) (hzero : u timeZero = 0)
    (henergy : ∀ s t : Time, s ≤ t →
      (∑ a, (w a t - w a s) ^ 2) ≤ u t - u s)
    (grid : ∀ k : ℕ, Fin (2 ^ k + 1) → Time)
    (hgridval : ∀ k i,
      u (grid k i) = ((i.val : ℝ) / (2 ^ k : ℝ)) * u timeOne)
    (i : ∀ k : ℕ, Fin (2 ^ k + 1))
    (s : Time) (x : ℝ) (hx : u s = x * u timeOne)
    (hiapprox : ∀ k, (i k).val / (2 ^ k : ℝ) ≤ x ∧
      x ≤ ((i k).val + 1) / (2 ^ k : ℝ))
    (j : Fin n) :
    Filter.Tendsto (fun k => w j (grid k (i k)))
      Filter.atTop (nhds (w j s)) := by
  /- `controlled_path_error_le` bounds the squared coordinate difference
  by the absolute control gap. Using `hgridval`, `hx`, and `hiapprox`, that
  gap is at most `u timeOne / 2^k`, which tends to zero. Prove convergence
  of the absolute difference, then of the coordinate itself. -/
  have hU : 0 ≤ u timeOne := by
    simpa only [hzero] using hmono (show timeZero ≤ timeOne by
      change (0 : ℝ) ≤ 1; norm_num)
  have hgap (k : ℕ) :
      |u (grid k (i k)) - u s| ≤ u timeOne / (2 : ℝ) ^ k := by
    rcases hiapprox k with ⟨hl, hu⟩
    have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hq : 0 ≤ x - (i k).val / (2 ^ k : ℝ) ∧
        x - (i k).val / (2 ^ k : ℝ) ≤ 1 / (2 ^ k : ℝ) := by
      constructor
      · linarith
      · have heq : (((i k).val : ℝ) + 1) / (2 ^ k : ℝ) =
            (i k).val / (2 ^ k : ℝ) + 1 / (2 ^ k : ℝ) := by
          ring
        rw [heq] at hu
        linarith
    calc
      _ = (x - (i k).val / (2 ^ k : ℝ)) * u timeOne := by
        rw [hgridval, hx, ← sub_mul, abs_mul,
          abs_of_nonpos (by linarith [hq.1]), abs_of_nonneg hU]
        ring
      _ ≤ (1 / (2 ^ k : ℝ)) * u timeOne :=
        mul_le_mul_of_nonneg_right hq.2 hU
      _ = u timeOne / (2 : ℝ) ^ k := by ring
  have hgeom : Filter.Tendsto (fun k : ℕ => u timeOne / (2 : ℝ) ^ k)
      Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 : ℝ) / 2 < 1 by norm_num)
    have ht := h.const_mul (u timeOne)
    simpa [div_eq_mul_inv, ← inv_pow] using ht
  have hsq (k : ℕ) :
      (w j (grid k (i k)) - w j s) ^ 2 ≤ u timeOne / (2 : ℝ) ^ k := by
    calc
      _ ≤ ∑ a, (w a (grid k (i k)) - w a s) ^ 2 :=
        Finset.single_le_sum (fun a _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ |u (grid k (i k)) - u s| :=
        controlled_path_error_le w u henergy s (grid k (i k))
      _ ≤ _ := hgap k
  have hsqtend : Filter.Tendsto
      (fun k => (w j (grid k (i k)) - w j s) ^ 2)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom
      (fun k => sq_nonneg _) hsq
  have habs : Filter.Tendsto
      (fun k => |w j (grid k (i k)) - w j s|)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsqtend
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

/-- Suppose the control u is [nondecreasing](hyp:hmono), [zero at time
zero](hyp:hzero), and [dominates the summed squared path increments over
every interval](hyp:henergy), and [the dyadic grids](hyp:grid) [place their
i-th level-k point at control value i/2^k times the terminal
value](hyp:hgridval). If [the control at time s equals x times its terminal
value](hyp:hx) and [a chain of indices, one per level](hyp:i), [brackets x
between i_k/2^k and (i_k + 1)/2^k at every level k](hyp:hiapprox), then
[the σ-signed path sums along the chain's grid points converge to the
σ-signed sum at s](goal).

This holds even when the control has flat intervals.
-/
theorem signed_dyadic_chain_tendsto {n : ℕ} (w : Fin n → Path)
    (u : Path) (hmono : Monotone (u : Time → ℝ)) (hzero : u timeZero = 0)
    (henergy : ∀ s t : Time, s ≤ t →
      (∑ j, (w j t - w j s) ^ 2) ≤ u t - u s)
    (grid : ∀ k : ℕ, Fin (2 ^ k + 1) → Time)
    (hgridval : ∀ k i,
      u (grid k i) = ((i.val : ℝ) / (2 ^ k : ℝ)) * u timeOne)
    (i : ∀ k : ℕ, Fin (2 ^ k + 1))
    (s : Time) (x : ℝ) (hx : u s = x * u timeOne)
    (hiapprox : ∀ k, (i k).val / (2 ^ k : ℝ) ≤ x ∧
      x ≤ ((i k).val + 1) / (2 ^ k : ℝ))
    (σ : Fin n → Bool) :
    Filter.Tendsto
      (fun k => ∑ j, (if σ j then (1 : ℝ) else -1) * w j (grid k (i k)))
      Filter.atTop
      (nhds (∑ j, (if σ j then (1 : ℝ) else -1) * w j s)) := by
  /- The grid-control gap is at most `u(timeOne)/2^k`. Apply
  `controlled_path_error_le` to every coefficient, then finite-sum
  continuity and `2^k → ∞`. Equality of control values handles plateaus. -/
  classical
  have hj (j : Fin n) : Filter.Tendsto
      (fun k => (if σ j then (1 : ℝ) else -1) * w j (grid k (i k)))
      Filter.atTop
      (nhds ((if σ j then (1 : ℝ) else -1) * w j s)) :=
    (controlled_grid_coordinate_tendsto w u hmono hzero henergy grid
      hgridval i s x hx hiapprox j).const_mul _
  simpa using
    (tendsto_finsetSum (Finset.univ : Finset (Fin n))
      (fun j _ => hj j))

/-- If a control path is [nondecreasing](hyp:hmono) and [zero at time
zero](hyp:hzero), then [its value at any time s equals x times its terminal
value for some x between 0 and 1](goal).

This also covers a zero terminal value.
-/
theorem control_value_unit_fraction (u : Path)
    (hmono : Monotone (u : Time → ℝ)) (hzero : u timeZero = 0)
    (s : Time) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ u s = x * u timeOne := by
  have h0s : 0 ≤ u s := by
    have hts : timeZero ≤ s := by
      change (0 : ℝ) ≤ (s : ℝ)
      exact s.property.1
    simpa only [hzero] using hmono hts
  have hs1 : u s ≤ u timeOne := hmono s.property.2
  by_cases hU : u timeOne = 0
  · refine ⟨0, by norm_num, by norm_num, ?_⟩
    simp [hU, le_antisymm (by simpa [hU] using hs1) h0s]
  · have hUpos : 0 < u timeOne := lt_of_le_of_ne (h0s.trans hs1) (Ne.symm hU)
    refine ⟨u s / u timeOne, div_nonneg h0s hUpos.le, ?_, ?_⟩
    · exact (div_le_iff₀ hUpos).2 (by simpa using hs1)
    · exact (div_mul_cancel₀ (u s) hU).symm

/-- Suppose the control u is [nondecreasing](hyp:hmono), [zero at time
zero](hyp:hzero), and [dominates the summed squared path increments over
every interval](hyp:henergy), and [the dyadic grids](hyp:grid) are
[monotone at every level](hyp:hgridmono), [place their i-th level-k point
at control value i/2^k times the terminal value](hyp:hgridval), and [are
compatible across levels](hyp:hgridcompat). If [the maximal signed
increments over the levels are summable](hyp:hsum), then [the absolute
σ-signed path sum at any time s is at most the absolute σ-signed sum at
time zero plus the total of the maximal signed increments over all
levels](goal).

This includes points inside flat intervals of the control.
-/
theorem signed_path_le_dyadic_increment_series {n : ℕ} (w : Fin n → Path)
    (u : Path) (hmono : Monotone (u : Time → ℝ)) (hzero : u timeZero = 0)
    (henergy : ∀ s t : Time, s ≤ t →
      (∑ j, (w j t - w j s) ^ 2) ≤ u t - u s)
    (grid : ∀ k : ℕ, Fin (2 ^ k + 1) → Time)
    (hgridmono : ∀ k, Monotone (grid k))
    (hgridval : ∀ k i,
      u (grid k i) = ((i.val : ℝ) / (2 ^ k : ℝ)) * u timeOne)
    (hgridcompat : ∀ k i l j,
      ((i.val : ℝ) / (2 ^ k : ℝ)) = ((j.val : ℝ) / (2 ^ l : ℝ)) →
        grid k i = grid l j)
    (σ : Fin n → Bool) (s : Time)
    (hsum : Summable (fun k => signedDyadicIncrementMax w grid k σ)) :
    |∑ j, (if σ j then (1 : ℝ) else -1) * w j s| ≤
      |∑ j, (if σ j then (1 : ℝ) else -1) * w j timeZero| +
        ∑' k, signedDyadicIncrementMax w grid k σ := by
  /- Approximate `u(s)` from below by dyadic levels. Compatibility makes
  the parent grid point literally the same at the next level, so each
  new value costs one adjacent increment. The coefficient-energy bound
  makes all `w_j` constant on each level set of `u`; hence the limiting
  signed value is the one at `s` even when `u` has a plateau. Pass the
  finite telescoping inequality to the limit using
  `Summable.tendsto_sum_tsum_nat hsum`. The chain exists by
  `exists_dyadic_lower_chain`; for `u(1) = 0`, take its index at `x = 0`,
  and otherwise use `x = u(s) / u(1)`. -/
  obtain ⟨x, hx0, hx1, hx⟩ := control_value_unit_fraction u hmono hzero s
  obtain ⟨i, hi0, _, hiapprox, hiparent⟩ :=
    exists_dyadic_lower_chain x hx0 hx1
  have hfinite (m : ℕ) :
      |∑ j, (if σ j then (1 : ℝ) else -1) * w j (grid m (i m))| ≤
        |∑ j, (if σ j then (1 : ℝ) else -1) * w j timeZero| +
          ∑ k ∈ Finset.range m, signedDyadicIncrementMax w grid k σ :=
    signed_dyadic_chain_finite_le w u hzero henergy grid hgridval
      hgridcompat i hi0 hiparent σ m
  have hleft : Filter.Tendsto
      (fun m => |∑ j, (if σ j then (1 : ℝ) else -1) * w j (grid m (i m))|)
      Filter.atTop
      (nhds |∑ j, (if σ j then (1 : ℝ) else -1) * w j s|) :=
    (signed_dyadic_chain_tendsto w u hmono hzero henergy grid
      hgridval i s x hx hiapprox σ).abs
  have hright : Filter.Tendsto
      (fun m => |∑ j, (if σ j then (1 : ℝ) else -1) * w j timeZero| +
        ∑ k ∈ Finset.range m, signedDyadicIncrementMax w grid k σ)
      Filter.atTop
      (nhds (|∑ j, (if σ j then (1 : ℝ) else -1) * w j timeZero| +
        ∑' k, signedDyadicIncrementMax w grid k σ)) :=
    tendsto_const_nhds.add (hsum.tendsto_sum_tsum_nat)
  exact le_of_tendsto_of_tendsto' hleft hright hfinite

end Causalean.Stat.Concentration.BoundedVariation
