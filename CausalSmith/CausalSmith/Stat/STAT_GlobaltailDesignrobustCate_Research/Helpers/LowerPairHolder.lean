module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairTensorDerivatives

/-! # Bandwidth-uniform whole-space Hölder bounds for the witness means

Dilation of the tensor jets proves equations (9)--(12) of the lower-pair
membership roadmap, with constants independent of bandwidth and sign.
-/
public section

namespace CausalSmith.Stat.GlobalTailDesignRobustCate

/-- The signed mean jets obey the exact amplitude and bandwidth dilation formula. -/
-- @node: witnessMean_iteratedFDeriv
lemma witnessMean_iteratedFDeriv (d j : ℕ) (β δ h : ℝ) (sign : Bool)
    (x : Fin d → ℝ) :
    iteratedFDeriv ℝ j (witnessMean d β δ h sign) x =
      ((if sign then 1 else -1) * δ * h ^ β) •
        ((h⁻¹) ^ j • iteratedFDeriv ℝ j (witnessBump d) (h⁻¹ • x)) := by
  have heq : witnessMean d β δ h sign = fun z =>
      ((if sign then 1 else -1) * δ * h ^ β) • witnessBump d (h⁻¹ • z) := by
    funext z
    simp only [witnessMean, smul_eq_mul]
    congr 1
    congr 1
    funext i
    simp [Pi.smul_apply, div_eq_mul_inv, mul_comm]
  have hg : ContDiff ℝ (j : WithTop ℕ∞)
      (fun z : Fin d → ℝ => witnessBump d (h⁻¹ • z)) :=
    (witnessBump_contDiff d (n := j)).comp (by fun_prop)
  rw [heq, iteratedFDeriv_const_smul_apply' hg.contDiffAt]
  rw [show iteratedFDeriv ℝ j
      (fun z : Fin d → ℝ => witnessBump d (h⁻¹ • z)) =
      fun z => (h⁻¹) ^ j • iteratedFDeriv ℝ j (witnessBump d) (h⁻¹ • z) from
    iteratedFDeriv_comp_const_smul h⁻¹ (witnessBump_contDiff d (n := j))]

/-- The norms of the signed jets retain the precise bandwidth scaling factor. -/
-- @node: witnessMean_iteratedFDeriv_norm
lemma witnessMean_iteratedFDeriv_norm (d j : ℕ) (β δ h : ℝ)
    (hδ : 0 ≤ δ) (hh : 0 < h) (sign : Bool) (x : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ j (witnessMean d β δ h sign) x‖ =
      δ * h ^ β * ((h⁻¹) ^ j * ‖iteratedFDeriv ℝ j (witnessBump d) (h⁻¹ • x)‖) := by
  rw [witnessMean_iteratedFDeriv, norm_smul, norm_smul]
  cases sign <;> simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg hδ,
    abs_of_nonneg (Real.rpow_nonneg hh.le β), abs_of_pos hh, abs_pow, abs_inv]

/-- A fixed constant controls all lower jets uniformly in the bandwidth. -/
-- @node: witnessMean_uniform_deriv_bound
lemma witnessMean_uniform_deriv_bound (d : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ h : ℝ), 0 ≤ δ → 0 < h → h ≤ 1 →
      ∀ (sign : Bool) (j : ℕ), j ≤ ⌈β⌉₊ - 1 → ∀ x : Fin d → ℝ,
        ‖iteratedFDeriv ℝ j (witnessMean d β δ h sign) x‖ ≤ δ * B := by
  let m := ⌈β⌉₊ - 1
  have hmpos : 0 < ⌈β⌉₊ := Nat.ceil_pos.mpr hβ
  have hmlt : (m : ℝ) < β := Nat.lt_ceil.mp (by omega : m < ⌈β⌉₊)
  let D : ℕ → ℝ := fun j => (witnessBump_iteratedFDeriv_bounded d j).choose
  have hD0 : ∀ j, 0 ≤ D j := fun j =>
    (witnessBump_iteratedFDeriv_bounded d j).choose_spec.1
  have hD : ∀ j x, ‖iteratedFDeriv ℝ j (witnessBump d) x‖ ≤ D j :=
    fun j x => (witnessBump_iteratedFDeriv_bounded d j).choose_spec.2 x
  let B := ∑ j ∈ Finset.range (m + 1), D j
  refine ⟨B, Finset.sum_nonneg (fun j _ => hD0 j), ?_⟩
  intro δ h hδ hh hh1 sign j hj x
  have hjβ : (j : ℝ) ≤ β := by
    have hjm : (j : ℝ) ≤ m := Nat.cast_le.mpr hj
    linarith
  have hscale : h ^ β * (h⁻¹) ^ j ≤ 1 := by
    have hp := Real.rpow_le_rpow_of_exponent_ge' hh.le hh1 (Nat.cast_nonneg j) hjβ
    calc
      _ ≤ h ^ (j : ℝ) * (h⁻¹) ^ j :=
        mul_le_mul_of_nonneg_right hp (pow_nonneg (inv_nonneg.mpr hh.le) j)
      _ = 1 := by rw [Real.rpow_natCast, ← mul_pow, mul_inv_cancel₀ hh.ne', one_pow]
  have hjB : D j ≤ B := Finset.single_le_sum (fun i _ => hD0 i)
    (by simpa only [Finset.mem_range] using (Nat.lt_succ_of_le hj))
  rw [witnessMean_iteratedFDeriv_norm d j β δ h hδ hh sign x]
  calc
    _ ≤ δ * (h ^ β * (h⁻¹) ^ j) * D j := by
      calc
        _ ≤ δ * h ^ β * ((h⁻¹) ^ j * D j) := by
          gcongr
          exact hD j _
        _ = _ := by ring
    _ ≤ δ * D j := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right hδ hscale) (hD0 j)
    _ ≤ δ * B := mul_le_mul_of_nonneg_left hjB hδ

/-- The bandwidth powers cancel exactly in the top-jet Hölder modulus. -/
-- @node: witnessMean_uniform_holder_modulus
lemma witnessMean_uniform_holder_modulus (d : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ h : ℝ), 0 ≤ δ → 0 < h →
      ∀ (sign : Bool) (x y : Fin d → ℝ),
        ‖iteratedFDeriv ℝ (⌈β⌉₊ - 1) (witnessMean d β δ h sign) x -
          iteratedFDeriv ℝ (⌈β⌉₊ - 1) (witnessMean d β δ h sign) y‖ ≤
          δ * B * ‖x - y‖ ^ (β - ((⌈β⌉₊ - 1 : ℕ) : ℝ)) := by
  let m := ⌈β⌉₊ - 1
  let α := β - (m : ℝ)
  have hmpos : 0 < ⌈β⌉₊ := Nat.ceil_pos.mpr hβ
  have hmadd : m + 1 = ⌈β⌉₊ := Nat.sub_add_cancel (by omega)
  have hmlt : (m : ℝ) < β := Nat.lt_ceil.mp (by omega : m < ⌈β⌉₊)
  have hα : 0 < α := by dsimp [α]; linarith
  have hα1 : α ≤ 1 := by
    have hceil := Nat.le_ceil β
    have hcast : (m : ℝ) + 1 = (⌈β⌉₊ : ℝ) := by exact_mod_cast hmadd
    dsimp [α]; linarith
  obtain ⟨B, hB, hb⟩ := witnessBump_iteratedFDeriv_holder_bound d m α hα hα1
  refine ⟨B, hB, ?_⟩
  intro δ h hδ hh sign x y
  have hdist : ‖h⁻¹ • x - h⁻¹ • y‖ = ‖x - y‖ / h := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
    exact inv_mul_eq_div _ _
  have hcancel : h ^ β * (h⁻¹) ^ m * (‖x - y‖ / h) ^ α = ‖x - y‖ ^ α := by
    rw [Real.div_rpow (norm_nonneg _) hh.le, div_eq_mul_inv]
    have hp : h ^ β * (h⁻¹) ^ m * (h ^ α)⁻¹ = 1 := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hh.le,
        ← Real.rpow_neg hh.le, ← Real.rpow_add hh, ← Real.rpow_add hh]
      have hexp : β + -(m : ℝ) + -α = 0 := by dsimp [α]; ring
      rw [hexp, Real.rpow_zero]
    calc
      _ = (h ^ β * (h⁻¹) ^ m * (h ^ α)⁻¹) * ‖x - y‖ ^ α := by ring
      _ = _ := by rw [hp, one_mul]
  rw [witnessMean_iteratedFDeriv, witnessMean_iteratedFDeriv,
    ← smul_sub, ← smul_sub, norm_smul, norm_smul]
  have habs : ‖(if sign then (1 : ℝ) else -1) * δ * h ^ β‖ = δ * h ^ β := by
    cases sign <;> simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg hδ,
      abs_of_nonneg (Real.rpow_nonneg hh.le β)]
  rw [habs]
  rw [Real.norm_eq_abs, abs_pow, abs_inv, abs_of_pos hh]
  calc
    _ ≤ δ * h ^ β * ((h⁻¹) ^ m * (B * ‖h⁻¹ • x - h⁻¹ • y‖ ^ α)) := by
      gcongr
      exact hb _ _
    _ = δ * B * ‖x - y‖ ^ α := by rw [hdist]; rw [← hcancel]; ring

/-- A single positive radius controls both signs at every admissible bandwidth. -/
-- @node: witnessMean_uniform_holderBall
lemma witnessMean_uniform_holderBall (d : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ B : ℝ, 0 < B ∧ ∀ (δ h : ℝ), 0 ≤ δ → 0 < h → h ≤ 1 →
      ∀ sign : Bool,
        Causalean.Stat.Nonparametric.HolderBallStd (witnessMean d β δ h sign)
          β (δ * B) Set.univ := by
  obtain ⟨D, hD0, hD⟩ := witnessMean_uniform_deriv_bound d β hβ
  obtain ⟨H, hH0, hH⟩ := witnessMean_uniform_holder_modulus d β hβ
  let B := max 1 (max D H)
  have hDB : D ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hHB : H ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro δ h hδ hh hh1 sign
  refine ⟨(witnessMean_contDiff d β δ h sign (n := ⌈β⌉₊ - 1)).contDiffOn, ?_, ?_⟩
  · intro j hj x hx
    exact (hD δ h hδ hh hh1 sign j hj x).trans (mul_le_mul_of_nonneg_left hDB hδ)
  · intro x hx y hy
    exact (hH δ h hδ hh sign x y).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHB hδ)
        (Real.rpow_nonneg (norm_nonneg _) _))

/-- The same fixed witness constant controls the ambient Euclidean extensions.
The coordinate projection is a contraction, so no radius enlargement is needed
in this direction. -/
lemma witnessMean_uniform_holderBall_euclid (d : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ B : ℝ, 0 < B ∧ ∀ (δ h : ℝ), 0 ≤ δ → 0 < h → h ≤ 1 →
      ∀ sign : Bool,
        HolderBallEuclid
          (fun x => witnessMean d β δ h sign (WithLp.ofLp x)) β (δ * B) := by
  obtain ⟨B, hB, hball⟩ := witnessMean_uniform_holderBall d β hβ
  refine ⟨B, hB, ?_⟩
  intro δ h hδ hh hh1 sign
  exact holderBallStd_to_euclid hβ (hball δ h hδ hh hh1 sign)

end CausalSmith.Stat.GlobalTailDesignRobustCate
