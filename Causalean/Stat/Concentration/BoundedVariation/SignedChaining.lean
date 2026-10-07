module
public import Causalean.Stat.Concentration.BoundedVariation.FiniteSignL2
public import Causalean.Stat.Concentration.BoundedVariation.SignedChainNumerics
public import Causalean.Stat.Concentration.BoundedVariation.SignedLevelEnergy
public import Causalean.Stat.Concentration.BoundedVariation.SignedSeriesL2

/-!
# Continuum chaining for finite signed path sums

A scalar continuous control of squared coefficient increments bounds the
signed process over the whole unit interval. This isolates the continuum
argument from the construction of variation controls for particular paths.
-/

@[expose] public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [The Rademacher energy](goal) of [a finite collection of continuous
paths on the unit interval](hyp:w) is [the uniform average, over all sign
patterns, of the squared supremum norm of the signed sum of the
paths](step:1).
-/
noncomputable def rademacherEnergy {n : ℕ} (w : Fin n → Path) : ℝ :=
  (∑ σ : Fin n → Bool,
    ‖∑ j, (if σ j then (1 : ℝ) else -1) • w j‖ ^ 2) / (2 ^ n : ℝ)

/-- If a continuous scalar control u is [nondecreasing](hyp:hmono), [zero
at time zero](hyp:hzero), and [dominates the summed squared increments of
the paths over every interval from s to t](hyp:henergy), then [the
Rademacher energy of the paths is at most 4096 times the total of the sum
of their squared values at time zero and the terminal control value](goal).

The constant is independent of the number of paths.
-/
theorem rademacherEnergy_le_scalar_control {n : ℕ} (w : Fin n → Path)
    (u : Path) (hmono : Monotone (u : Time → ℝ))
    (hzero : u timeZero = 0)
    (henergy : ∀ s t : Time, s ≤ t →
      (∑ j, (w j t - w j s) ^ 2) ≤ u t - u s) :
    rademacherEnergy w ≤
      4096 * ((∑ j, (w j timeZero) ^ 2) + u timeOne) := by
  /- Use `exists_control_dyadic_grid` for dyadic levels of u. The
  summability and deterministic continuum passage are separated in
  `ChainingReconstruction`. At level
  k, the parent-child increments have squared coefficient energy at most
  2^(-k) u(1). Apply `signed_grid_increment_max_energy_le` to each finite
  edge family, sum its
  square-root bounds by `finite_sign_l2_sum_le`, and pass to the continuous
  supremum using `signed_path_le_dyadic_increment_series`.
  On a plateau of u, henergy makes every coefficient path constant, so the
  section represents the signed process even if its times are not dense.
  Bound the initial value by sign orthogonality. The level-root series is at
  most `40 * sqrt (u timeOne)`, so `(a + b)^2 ≤ 2*a^2 + 2*b^2` gives
  `2 * initialEnergy + 3200 * u timeOne`, within the stated `4096` bound.
  The supremum over time can be taken by evaluating the `Path` norm and
  applying `signed_path_le_dyadic_increment_series` pointwise. -/
  classical
  let E : ℝ := ∑ j, (w j timeZero) ^ 2
  let U : ℝ := u timeOne
  have hE : 0 ≤ E := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hU : 0 ≤ U := by
    dsimp [U]
    simpa only [hzero] using hmono (show timeZero ≤ timeOne by
      change (0 : ℝ) ≤ 1; norm_num)
  obtain ⟨grid, hgridmono, hgridval, hgridcompat⟩ :=
    exists_control_dyadic_grid u hmono hzero
  let A (σ : Fin n → Bool) : ℝ :=
    |∑ j, (if σ j then (1 : ℝ) else -1) * w j timeZero|
  let B (k : ℕ) (σ : Fin n → Bool) : ℝ :=
    signedDyadicIncrementMax w grid k σ
  let Q (k : ℕ) : ℝ :=
    32 * (1 + Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) /
      (2 : ℝ) ^ (k + 1)
  have hAenergy :
      (∑ σ : Fin n → Bool, (A σ) ^ 2) / (2 ^ n : ℝ) ≤ 32 * E := by
    have h := signMaxEnergy_le (m := 0)
      (fun (_ : Fin 1) (j : Fin n) => w j timeZero)
    simpa [signMaxEnergy, A, E] using h
  have hBenergy (k : ℕ) :
      (∑ σ : Fin n → Bool, (B k σ) ^ 2) / (2 ^ n : ℝ) ≤ Q k * U := by
    have h := signedDyadicIncrementMax_energy_le w u henergy
      grid hgridmono hgridval k
    convert h using 1 <;> dsimp [B, Q, U] <;> ring
  have hQ (k : ℕ) : 0 ≤ Q k := by
    dsimp [Q]
    have hk : 1 ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity : 2 ^ (k + 1) ≠ 0)
    have := Real.log_nonneg hk
    positivity
  have hroot (k : ℕ) :
      Real.sqrt ((∑ σ : Fin n → Bool, (B k σ) ^ 2) / (2 ^ n : ℝ)) ≤
        Real.sqrt U * Real.sqrt (Q k) := by
    rw [← Real.sqrt_mul hU]
    exact Real.sqrt_le_sqrt (by simpa [mul_comm] using hBenergy k)
  have hBsum (σ : Fin n → Bool) : Summable (fun k => B k σ) :=
    signedDyadicIncrementMax_summable w u hmono hzero henergy grid
      hgridmono hgridval σ
  have hR : Summable (fun k =>
      Real.sqrt ((∑ σ : Fin n → Bool, (B k σ) ^ 2) / (2 ^ n : ℝ))) := by
    apply Summable.of_nonneg_of_le (fun k => Real.sqrt_nonneg _) hroot
    exact dyadic_log_sqrt_summable.mul_left (Real.sqrt U)
  have hRbound :
      (∑' k, Real.sqrt ((∑ σ : Fin n → Bool, (B k σ) ^ 2) /
        (2 ^ n : ℝ))) ≤ 40 * Real.sqrt U := by
    calc
      _ ≤ ∑' k, Real.sqrt U * Real.sqrt (Q k) :=
        Summable.tsum_le_tsum hroot hR
          (dyadic_log_sqrt_summable.mul_left (Real.sqrt U))
      _ = Real.sqrt U * (∑' k, Real.sqrt (Q k)) := by rw [tsum_mul_left]
      _ ≤ 40 * Real.sqrt U := by
        have hn : (∑' k, Real.sqrt (Q k)) ≤ 40 := by
          simpa only [Q] using dyadic_log_sqrt_tsum_le_40
        simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg U))
  have hBtotal :
      (∑ σ : Fin n → Bool, (∑' k, B k σ) ^ 2) / (2 ^ n : ℝ) ≤
        (∑' k, Real.sqrt ((∑ σ : Fin n → Bool, (B k σ) ^ 2) /
          (2 ^ n : ℝ))) ^ 2 :=
    finite_sign_l2_tsum_le B hR
  have hpoint (σ : Fin n → Bool) :
      ‖∑ j, (if σ j then (1 : ℝ) else -1) • w j‖ ≤
        A σ + ∑' k, B k σ := by
    let f : Path := ∑ j, (if σ j then (1 : ℝ) else -1) • w j
    have hBn (k : ℕ) : 0 ≤ B k σ := by
      unfold B signedDyadicIncrementMax
      exact (abs_nonneg _).trans
        (Finset.le_sup' (fun i : Fin (2 ^ (k + 1)) =>
          |∑ j, (if σ j then (1 : ℝ) else -1) *
            (w j (grid (k + 1) i.succ) - w j (grid (k + 1) i.castSucc))|)
          (by simp : (0 : Fin (2 ^ (k + 1))) ∈ Finset.univ))
    apply (ContinuousMap.norm_le f
      (add_nonneg (abs_nonneg _) (tsum_nonneg hBn))).2
    intro s
    have hs := signed_path_le_dyadic_increment_series w u hmono hzero
      henergy grid hgridval hgridcompat σ s (hBsum σ)
    simpa only [f, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul, Real.norm_eq_abs, A, B] using hs
  have hsup :
      rademacherEnergy w ≤
        (∑ σ : Fin n → Bool, (A σ + ∑' k, B k σ) ^ 2) /
          (2 ^ n : ℝ) := by
    unfold rademacherEnergy
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro σ _
    nlinarith [hpoint σ, norm_nonneg (∑ j, (if σ j then (1 : ℝ) else -1) • w j)]
  have htwo := finite_sign_l2_sum_le
    (fun i : Fin 2 => if i.val = 0 then A else fun σ => ∑' k, B k σ)
  have hfinal :
      (∑ σ : Fin n → Bool, (A σ + ∑' k, B k σ) ^ 2) /
        (2 ^ n : ℝ) ≤
      (Real.sqrt ((∑ σ : Fin n → Bool, (A σ) ^ 2) / (2 ^ n : ℝ)) +
        Real.sqrt ((∑ σ : Fin n → Bool, (∑' k, B k σ) ^ 2) /
          (2 ^ n : ℝ))) ^ 2 := by
    simpa [Fin.sum_univ_two] using htwo
  have hR0 : Real.sqrt ((∑ σ : Fin n → Bool, (A σ) ^ 2) /
      (2 ^ n : ℝ)) ^ 2 ≤ 32 * E := by
    rw [Real.sq_sqrt (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity))]
    exact hAenergy
  have hR1 : Real.sqrt ((∑ σ : Fin n → Bool, (∑' k, B k σ) ^ 2) /
      (2 ^ n : ℝ)) ^ 2 ≤ (40 * Real.sqrt U) ^ 2 := by
    rw [Real.sq_sqrt (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity))]
    exact hBtotal.trans ((sq_le_sq₀
      (tsum_nonneg fun _ => Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40) (Real.sqrt_nonneg U))).2 hRbound)
  calc
    rademacherEnergy w ≤ _ := hsup
    _ ≤ _ := hfinal
    _ ≤ 4096 * (E + U) := by
      have hs := Real.sq_sqrt hU
      nlinarith [sq_nonneg (Real.sqrt ((∑ σ : Fin n → Bool, (A σ) ^ 2) /
        (2 ^ n : ℝ)) - Real.sqrt ((∑ σ : Fin n → Bool,
          (∑' k, B k σ) ^ 2) / (2 ^ n : ℝ)))]
    _ = _ := rfl

end Causalean.Stat.Concentration.BoundedVariation
