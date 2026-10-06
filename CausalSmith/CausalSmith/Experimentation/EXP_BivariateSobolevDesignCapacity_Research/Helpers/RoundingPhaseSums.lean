module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingFairness
public import Causalean.Tactic.IntegralLinearity

/-! # Finite phase sums for ordered rounding

The deterministic halving estimate gives the total active-count allowance after
any row loses protection. Orthogonal finite increments have additive second
moments. Terminal single-coordinate rounding has the exact test-row variance
and norm-energy increment required by the phase argument. The actual row seed
iteration has centered increments and exact finite second-moment accumulation.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Halving phase counts telescope, including the unused terminal endpoint.](goal) Under [the stated conditions](hyp:hr). -/
-- @node: halving_phase_sum_with_endpoint
lemma halving_phase_sum_with_endpoint (r : ℕ → ℕ) (m : ℕ)
    (hr : ∀ j < m, 2 * r (j + 1) ≤ r j) :
    (∑ j ∈ Finset.range m, r j) + 2 * r m ≤ 2 * r 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hprev := ih (fun j hj => hr j (by omega))
    have hlast := hr m (by omega)
    rw [Finset.sum_range_succ]
    omega

/-- [ A finite halving chain spends at most twice its initial active count.](goal) Under [the stated conditions](hyp:hr). -/
-- @node: halving_phase_sum_le
lemma halving_phase_sum_le (r : ℕ → ℕ) (m : ℕ)
    (hr : ∀ j < m, 2 * r (j + 1) ≤ r j) :
    (∑ j ∈ Finset.range m, r j) ≤ 2 * r 0 := by
  have h := halving_phase_sum_with_endpoint r m hr
  omega

/-- [ Once a row is unprotected, the halving phase chain spends at most eight times
its row index, and also at most twice the original sample size.](goal) Under [the stated conditions](hyp:hr,hn,hh). -/
-- @node: unprotected_phase_sum_le
lemma unprotected_phase_sum_le (r : ℕ → ℕ) (m n h : ℕ)
    (hr : ∀ j < m, 2 * r (j + 1) ≤ r j)
    (hn : r 0 ≤ n) (hh : r 0 < 4 * h) :
    (∑ j ∈ Finset.range m, r j) ≤ 8 * min h n := by
  have hs := halving_phase_sum_le r m hr
  omega

/-- [ The paper's constant 32 is the product of the phase variance allowance 4
and the deterministic unprotected-count allowance 8.](goal) Under [the stated conditions](hyp:hr,hn,hh). -/
-- @node: unprotected_phase_variance_allowance
lemma unprotected_phase_variance_allowance (r : ℕ → ℕ) (m n h : ℕ) (Λ : ℝ)
    (hr : ∀ j < m, 2 * r (j + 1) ≤ r j)
    (hn : r 0 ≤ n) (hh : r 0 < 4 * h) :
    4 * Λ ^ 2 * (∑ j ∈ Finset.range m, (r j : ℝ)) ≤
      32 * Λ ^ 2 * (min h n : ℕ) := by
  have hs : (∑ j ∈ Finset.range m, (r j : ℝ)) ≤ 8 * (min h n : ℕ) := by
    exact_mod_cast unprotected_phase_sum_le r m n h hr hn hh
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * Λ ^ 2 by positivity)
  nlinarith

/-- [ Orthogonality to the preceding partial sum removes exactly the cross term
in a finite second-moment expansion.](goal) Under [the stated conditions](hyp:hD,horth). -/
-- @node: finite_orthogonal_increment_second_moment
lemma finite_orthogonal_increment_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℕ → Ω → ℝ) (m : ℕ)
    (hD : ∀ j < m, MemLp (D j) 2 μ)
    (horth : ∀ j < m, (∫ ω, (∑ k ∈ Finset.range j, D k ω) * D j ω ∂μ) = 0) :
    (∫ ω, (∑ j ∈ Finset.range m, D j ω) ^ 2 ∂μ) =
      ∑ j ∈ Finset.range m, ∫ ω, D j ω ^ 2 ∂μ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hprev := ih (fun j hj => hD j (by omega)) (fun j hj => horth j (by omega))
    have hsum : MemLp (fun ω => ∑ j ∈ Finset.range m, D j ω) 2 μ :=
      memLp_finsetSum _ (fun j hj => hD j (by have := Finset.mem_range.mp hj; omega))
    have hj := hD m (by omega)
    have hexp (ω : Ω) : (∑ j ∈ Finset.range (m + 1), D j ω) ^ 2 =
        (∑ j ∈ Finset.range m, D j ω) ^ 2 + D m ω ^ 2 +
          2 * ((∑ j ∈ Finset.range m, D j ω) * D m ω) := by
      rw [Finset.sum_range_succ]
      ring
    simp_rw [hexp]
    have hsqi := hsum.integrable_sq
    have hjqi := hj.integrable_sq
    have hprod : Integrable (fun ω => (∑ j ∈ Finset.range m, D j ω) * D m ω) μ :=
      hsum.integrable_mul hj
    integral_linearity
    rw [horth m (by omega), mul_zero, add_zero, hprev, Finset.sum_range_succ]


/-- [ Finite orthogonal phase increments inherit the sum of their separate
variance allowances. The increments and counts can be zero-padded.](goal) Under [the stated conditions](hyp:hD,horth,hphase,hr,hn,hh). -/
-- @node: finite_phase_second_moment_le
lemma finite_phase_second_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℕ → Ω → ℝ) (r : ℕ → ℕ) (m n h : ℕ) (Λ : ℝ)
    (hD : ∀ j < m, MemLp (D j) 2 μ)
    (horth : ∀ j < m, (∫ ω, (∑ k ∈ Finset.range j, D k ω) * D j ω ∂μ) = 0)
    (hphase : ∀ j < m, (∫ ω, D j ω ^ 2 ∂μ) ≤ 4 * Λ ^ 2 * r j)
    (hr : ∀ j < m, 2 * r (j + 1) ≤ r j)
    (hn : r 0 ≤ n) (hh : r 0 < 4 * h) :
    (∫ ω, (∑ j ∈ Finset.range m, D j ω) ^ 2 ∂μ) ≤
      32 * Λ ^ 2 * (min h n : ℕ) := by
  rw [finite_orthogonal_increment_second_moment μ D m hD horth]
  calc
    _ ≤ ∑ j ∈ Finset.range m, 4 * Λ ^ 2 * (r j : ℝ) :=
      Finset.sum_le_sum (fun j hj => hphase j (by simpa using hj))
    _ = 4 * Λ ^ 2 * (∑ j ∈ Finset.range m, (r j : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ _ := unprotected_phase_variance_allowance r m n h Λ hr hn hh

/-- [ A preceding seed-history statistic is orthogonal to a fresh centered increment.
This is the conditional-mean argument used for padded moves and phases.](goal) Under [the stated conditions](hyp:hA,hD,hignore,hmean). -/
-- @node: cube_fresh_increment_orthogonal
lemma cube_fresh_increment_orthogonal {m : ℕ} (j : Fin m)
    (A D : Cube m → ℝ) (hA : MemLp A 2 (cubeMeasure m))
    (hD : MemLp D 2 (cubeMeasure m))
    (hignore : ∀ x t, A (Function.update x j t) = A x)
    (hmean : ∀ x, (∫ t, D (Function.update x j t)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 0) :
    (∫ x, A x * D x ∂cubeMeasure m) = 0 := by
  have he : (∫ x, A x * D x ∂cubeMeasure m) =
      ∫ _ : Cube m, (0 : ℝ) ∂cubeMeasure m := by
    apply cube_integral_eq_of_fresh_coordinate j _ _ (hA.integrable_mul hD)
      (integrable_zero _ _ _)
    · intro x
      change (∫ t, A (Function.update x j t) * D (Function.update x j t)
        ∂volume.restrict (Icc (0 : ℝ) 1)) = 0
      simp_rw [hignore]
      rw [integral_const_mul, hmean x, mul_zero]
    · intro x t
      rfl
  simpa using he

/-- [ Random realized phase counts obey the same pathwise halving budget before
integration. This keeps the active-count bound inside the seed expectation.](goal) Under [the stated conditions](hyp:hD,hR,horth,hphase,hr,hn,hh). -/
-- @node: random_phase_second_moment_le
lemma random_phase_second_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (R : ℕ → Ω → ℕ) (m n h : ℕ) (Λ : ℝ)
    (hD : ∀ j < m, MemLp (D j) 2 μ)
    (hR : ∀ j < m, Integrable (fun ω => (R j ω : ℝ)) μ)
    (horth : ∀ j < m, (∫ ω, (∑ k ∈ Finset.range j, D k ω) * D j ω ∂μ) = 0)
    (hphase : ∀ j < m, (∫ ω, D j ω ^ 2 ∂μ) ≤
      4 * Λ ^ 2 * ∫ ω, (R j ω : ℝ) ∂μ)
    (hr : ∀ ω j, j < m → 2 * R (j + 1) ω ≤ R j ω)
    (hn : ∀ ω, R 0 ω ≤ n) (hh : ∀ ω, R 0 ω < 4 * h) :
    (∫ ω, (∑ j ∈ Finset.range m, D j ω) ^ 2 ∂μ) ≤
      32 * Λ ^ 2 * (min h n : ℕ) := by
  rw [finite_orthogonal_increment_second_moment μ D m hD horth]
  have hi : Integrable (fun ω => ∑ j ∈ Finset.range m, (R j ω : ℝ)) μ :=
    integrable_finsetSum _ (fun j hj => hR j (Finset.mem_range.mp hj))
  have hcount : (∫ ω, ∑ j ∈ Finset.range m, (R j ω : ℝ) ∂μ) ≤
      8 * (min h n : ℕ) := by
    calc
      _ ≤ ∫ _ : Ω, (8 * (min h n : ℕ) : ℝ) ∂μ := by
        apply integral_mono hi (integrable_const _)
        intro ω
        change (∑ j ∈ Finset.range m, (R j ω : ℝ)) ≤ 8 * (min h n : ℕ)
        exact_mod_cast unprotected_phase_sum_le (fun j => R j ω) m n h
          (hr ω) (hn ω) (hh ω)
      _ = _ := by simp
  calc
    _ ≤ ∑ j ∈ Finset.range m, 4 * Λ ^ 2 * ∫ ω, (R j ω : ℝ) ∂μ :=
      Finset.sum_le_sum (fun j hj => hphase j (Finset.mem_range.mp hj))
    _ = 4 * Λ ^ 2 * (∫ ω, ∑ j ∈ Finset.range m, (R j ω : ℝ) ∂μ) := by
      rw [integral_finsetSum _ (fun j hj => hR j (Finset.mem_range.mp hj)), Finset.mul_sum]
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hcount (show 0 ≤ 4 * Λ ^ 2 by positivity)
      nlinarith

/-- Updating one coordinate changes a test row by its coefficient times the
single-coordinate increment. [The asserted mathematical result follows](goal). -/
-- @node: terminal_update_row_increment
lemma terminal_update_row_increment {n : ℕ} (u c : Fin n → ℝ) (i : Fin n) (b : ℝ) :
    rowDot c (Function.update u i b - u) = c i * (b - u i) := by
  classical
  have he : Function.update u i b - u =
      (fun j => if j = i then b - u i else 0) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  rw [he]
  simp [rowDot]

/-- The actual terminal coordinate update contributes exactly its coefficient
square times one minus the current coordinate square to the row variance. Under [the stated conditions](hyp:hu), [the asserted mathematical result follows](goal). -/
-- @node: terminal_seed_row_second_moment
lemma terminal_seed_row_second_moment {n : ℕ} (u c : Fin n → ℝ) (i : Fin n)
    (hu : |u i| ≤ 1) :
    (∫ t, rowDot c (Function.update u i
      (if t < (1 + u i) / 2 then 1 else -1) - u) ^ 2
      ∂volume.restrict (Icc (0 : ℝ) 1)) = c i ^ 2 * (1 - u i ^ 2) := by
  simp_rw [terminal_update_row_increment, mul_pow]
  have he (t : ℝ) : ((if t < (1 + u i) / 2 then (1 : ℝ) else -1) - u i) ^ 2 =
      if t < (1 + u i) / 2 then (1 - u i) ^ 2 else (-1 - u i) ^ 2 := by
    split_ifs <;> rfl
  simp_rw [he]
  rw [integral_const_mul, terminal_seed_increment_second_moment _ hu]

/-- [ Each terminal row increment spends at most one coefficient-square allowance.](goal) Under [the stated conditions](hyp:hu,hc). -/
-- @node: terminal_seed_row_second_moment_le
lemma terminal_seed_row_second_moment_le {n : ℕ} (u c : Fin n → ℝ) (i : Fin n)
    (Λ : ℝ) (hu : |u i| ≤ 1) (hc : |c i| ≤ Λ) :
    (∫ t, rowDot c (Function.update u i
      (if t < (1 + u i) / 2 then 1 else -1) - u) ^ 2
      ∂volume.restrict (Icc (0 : ℝ) 1)) ≤ Λ ^ 2 := by
  rw [terminal_seed_row_second_moment u c i hu]
  have hsq : c i ^ 2 ≤ Λ ^ 2 := by
    have hΛ := (abs_nonneg (c i)).trans hc
    simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg (c i)) hc
  nlinarith [sq_nonneg (u i), mul_nonneg (sq_nonneg (c i)) (sq_nonneg (u i))]

/-- A single-coordinate terminal update changes norm energy only at that coordinate. [The asserted mathematical result follows](goal). -/
-- @node: terminal_update_energy_increment
lemma terminal_update_energy_increment {n : ℕ} (u : Fin n → ℝ) (i : Fin n) (b : ℝ) :
    rowDot (Function.update u i b) (Function.update u i b) - rowDot u u =
      b ^ 2 - u i ^ 2 := by
  classical
  change (∑ j, Function.update u i b j * Function.update u i b j) -
    (∑ j, u j * u j) = _
  rw [← Finset.sum_sub_distrib]
  have he (j : Fin n) : Function.update u i b j * Function.update u i b j - u j * u j =
      if j = i then b ^ 2 - u i ^ 2 else 0 := by
    by_cases hj : j = i
    · subst j; simp [pow_two]
    · simp [hj]
  simp_rw [he]
  simp

/-- [ Every fresh terminal coin spends exactly one minus the current coordinate square
in norm energy, independently of the threshold's asymmetry.](goal) -/
-- @node: terminal_seed_energy_increment
lemma terminal_seed_energy_increment {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    (∫ t, rowDot (Function.update u i (if t < (1 + u i) / 2 then 1 else -1))
      (Function.update u i (if t < (1 + u i) / 2 then 1 else -1)) - rowDot u u
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 1 - u i ^ 2 := by
  simp_rw [terminal_update_energy_increment]
  have he (t : ℝ) : (if t < (1 + u i) / 2 then (1 : ℝ) else -1) ^ 2 = 1 := by
    split_ifs <;> norm_num
  simp_rw [he]
  simp [integral_const, measureReal_def, Real.volume_Icc]

/-- Terminal moves satisfy the row variance-to-energy comparison with constant one. Under [the stated conditions](hyp:hu,hc), [the asserted mathematical result follows](goal). -/
-- @node: terminal_seed_row_variance_energy_le
lemma terminal_seed_row_variance_energy_le {n : ℕ} (u c : Fin n → ℝ) (i : Fin n)
    (Λ : ℝ) (hu : |u i| ≤ 1) (hc : |c i| ≤ Λ) :
    (∫ t, rowDot c (Function.update u i
      (if t < (1 + u i) / 2 then 1 else -1) - u) ^ 2
      ∂volume.restrict (Icc (0 : ℝ) 1)) ≤
    Λ ^ 2 * (∫ t, rowDot (Function.update u i (if t < (1 + u i) / 2 then 1 else -1))
      (Function.update u i (if t < (1 + u i) / 2 then 1 else -1)) - rowDot u u
      ∂volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [terminal_seed_row_second_moment u c i hu, terminal_seed_energy_increment]
  have hsq : c i ^ 2 ≤ Λ ^ 2 := by
    simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg (c i)) hc
  have he : 0 ≤ 1 - u i ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (u i)) hu
    simp only [← pow_two, sq_abs, one_pow] at h
    linarith
  exact mul_le_mul_of_nonneg_right hsq he

variable {n : ℕ}

/-- Every actual fractional coordinate has all finite moments, by cube preservation. [The asserted mathematical result follows](goal). -/
-- @node: roundingIteration_coordinate_memLp
lemma roundingIteration_coordinate_memLp (a : Fin (n / 4) → Fin n → ℝ)
    (k : ℕ) (i : Fin n) :
    MemLp (fun seeds => (roundingIteration a seeds k).1 i) 2 (roundingSeedLaw n) := by
  have : IsFiniteMeasure (roundingSeedLaw n) := by
    unfold roundingSeedLaw cubeMeasure
    infer_instance
  apply MemLp.of_bound (roundingIteration_coordinate_measurable a k i).aestronglyMeasurable 1
  filter_upwards [] with seeds
  simpa only [Real.norm_eq_abs] using (roundingIteration_cube_and_count a seeds k).1 i

/-- [ A finite deterministic test row preserves square-integrability of the state.](goal) -/
-- @node: roundingIteration_row_memLp
lemma roundingIteration_row_memLp (a : Fin (n / 4) → Fin n → ℝ)
    (c : Fin n → ℝ) (k : ℕ) :
    MemLp (fun seeds => rowDot c (roundingIteration a seeds k).1) 2 (roundingSeedLaw n) := by
  unfold rowDot
  exact memLp_finsetSum _ (fun i _ => (roundingIteration_coordinate_memLp a k i).const_mul (c i))

/-- Integrating the next fresh actual coin centers each coordinate increment. Under [the stated conditions](hyp:hk), [the asserted mathematical result follows](goal). -/
-- @node: roundingIteration_next_coordinate_increment_mean
lemma roundingIteration_next_coordinate_increment_mean (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k : ℕ) (hk : k < n) (i : Fin n) :
    (∫ t, (roundingIteration a (Function.update seeds ⟨2 * k + 1, by omega⟩ t)
      (k + 1)).1 i - (roundingIteration a
      (Function.update seeds ⟨2 * k + 1, by omega⟩ t) k).1 i
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 0 := by
  have hpost : Integrable (fun t =>
      (roundingIteration a (Function.update seeds ⟨2 * k + 1, by omega⟩ t) (k + 1)).1 i)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    apply Integrable.of_bound
      ((roundingIteration_coordinate_measurable a (k + 1) i).comp
        (by fun_prop : Measurable (fun t : ℝ =>
          Function.update seeds ⟨2 * k + 1, by omega⟩ t))).aestronglyMeasurable 1
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs, Function.comp_apply] using
      (roundingIteration_cube_and_count a (Function.update seeds ⟨2 * k + 1, by omega⟩ t)
        (k + 1)).1 i
  simp_rw [roundingIteration_update_future a seeds k
    (⟨2 * k + 1, by omega⟩ : Fin (3 * n)) _ (by dsimp; omega)]
  rw [integral_sub hpost (integrable_const _), roundingIteration_next_coin_mean a seeds k hk i]
  simp [integral_const, measureReal_def, Real.volume_Icc]

/-- [ The actual row increment has zero conditional mean under its fresh coin.](goal) Under [the stated conditions](hyp:hk). -/
-- @node: roundingIteration_next_row_increment_mean
lemma roundingIteration_next_row_increment_mean (a : Fin (n / 4) → Fin n → ℝ)
    (c : Fin n → ℝ) (seeds : RoundingSeeds n) (k : ℕ) (hk : k < n) :
    (∫ t, rowDot c ((roundingIteration a
      (Function.update seeds ⟨2 * k + 1, by omega⟩ t) (k + 1)).1 -
      (roundingIteration a (Function.update seeds ⟨2 * k + 1, by omega⟩ t) k).1)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 0 := by
  have hi (i : Fin n) : Integrable (fun t => c i *
      ((roundingIteration a (Function.update seeds ⟨2 * k + 1, by omega⟩ t) (k + 1)).1 i -
       (roundingIteration a (Function.update seeds ⟨2 * k + 1, by omega⟩ t) k).1 i))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    apply Integrable.of_bound (by fun_prop) (2 * |c i|)
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_mul]
    have hp := (roundingIteration_cube_and_count a
      (Function.update seeds ⟨2 * k + 1, by omega⟩ t) (k + 1)).1 i
    have hb := (roundingIteration_cube_and_count a
      (Function.update seeds ⟨2 * k + 1, by omega⟩ t) k).1 i
    have hd := abs_sub
      ((roundingIteration a (Function.update seeds ⟨2 * k + 1, by omega⟩ t) (k + 1)).1 i)
      ((roundingIteration a (Function.update seeds ⟨2 * k + 1, by omega⟩ t) k).1 i)
    nlinarith [abs_nonneg (c i)]
  simp only [rowDot, Pi.sub_apply]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_const_mul, roundingIteration_next_coordinate_increment_mean a seeds k hk]
  simp

/-- Finite increment sums telescope without any convergence or stopping-time theorem. [The asserted mathematical result follows](goal). -/
-- @node: finite_increment_sum_telescope
lemma finite_increment_sum_telescope (f : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range m, (f (k + 1) - f k)) = f m - f 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- Orthogonality holds for the actual row increments and the preceding fractional row. Under [the stated conditions](hyp:hk), [the asserted mathematical result follows](goal). -/
-- @node: roundingIteration_row_increment_orthogonal
lemma roundingIteration_row_increment_orthogonal (a : Fin (n / 4) → Fin n → ℝ)
    (c : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    (∫ seeds, rowDot c (roundingIteration a seeds k).1 *
      (rowDot c (roundingIteration a seeds (k + 1)).1 -
        rowDot c (roundingIteration a seeds k).1) ∂roundingSeedLaw n) = 0 := by
  apply cube_fresh_increment_orthogonal ⟨2 * k + 1, by omega⟩ _ _
    (roundingIteration_row_memLp a c k)
    ((roundingIteration_row_memLp a c (k + 1)).sub (roundingIteration_row_memLp a c k))
  · intro seeds t
    rw [roundingIteration_update_future a seeds k _ _ (by dsimp; omega)]
  · intro seeds
    change (∫ t, rowDot c (roundingIteration a
      (Function.update seeds ⟨2 * k + 1, by omega⟩ t) (k + 1)).1 -
      rowDot c (roundingIteration a
      (Function.update seeds ⟨2 * k + 1, by omega⟩ t) k).1
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 0
    simp_rw [show ∀ u v : Fin n → ℝ, rowDot c u - rowDot c v = rowDot c (u - v)
      from fun u v => (dotProduct_sub c u v).symm]
    exact roundingIteration_next_row_increment_mean a c seeds k hk

/-- The constructed signing's second moment is exactly the finite sum of its move
variances. The initial state is zero and the terminal state is the actual signing. [The asserted mathematical result follows](goal). -/
-- @node: orderedBoundaryRounding_row_second_moment_sum
lemma orderedBoundaryRounding_row_second_moment_sum (a : Fin (n / 4) → Fin n → ℝ)
    (c : Fin n → ℝ) :
    (∫ seeds, (∑ i, c i * sgn (orderedBoundaryRounding n a seeds i)) ^ 2
      ∂roundingSeedLaw n) =
      ∑ k ∈ Finset.range n, ∫ seeds,
        (rowDot c (roundingIteration a seeds (k + 1)).1 -
          rowDot c (roundingIteration a seeds k).1) ^ 2 ∂roundingSeedLaw n := by
  have ht (seeds : RoundingSeeds n) (m : ℕ) :
      (∑ k ∈ Finset.range m, (rowDot c (roundingIteration a seeds (k + 1)).1 -
        rowDot c (roundingIteration a seeds k).1)) =
        rowDot c (roundingIteration a seeds m).1 := by
    rw [finite_increment_sum_telescope (fun k => rowDot c (roundingIteration a seeds k).1) m]
    simp [roundingIteration, rowDot]
  have he := finite_orthogonal_increment_second_moment (roundingSeedLaw n)
    (fun k seeds => rowDot c (roundingIteration a seeds (k + 1)).1 -
      rowDot c (roundingIteration a seeds k).1) n
    (fun k _ => (roundingIteration_row_memLp a c (k + 1)).sub
      (roundingIteration_row_memLp a c k))
    (fun k hk => by
      simp_rw [ht]
      exact roundingIteration_row_increment_orthogonal a c k hk)
  simp_rw [ht] at he
  rw [← he]
  congr 1
  funext seeds
  congr 1
  simp_rw [← roundingIteration_terminal_eq_sign a]
  rfl


end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
