module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Procedure
public import Causalean.Tactic.IntegralLinearity
public import Mathlib.Probability.Moments.Variance

/-! Scalar deviation consequences of the energy bias and variance budgets. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The first absolute centered moment is bounded by the standard deviation. -/
-- @node: integral_abs_centered_le_sqrt_variance
lemma integral_abs_centered_le_sqrt_variance {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (Z : E → ℝ) (hZ : MemLp Z 2 ν) :
    (∫ x, |Z x - ∫ y, Z y ∂ν| ∂ν) ≤ Real.sqrt (variance Z ν) := by
  let c := ∫ x, |Z x - ∫ y, Z y ∂ν| ∂ν
  have hcL2 := hZ.sub (memLp_const (∫ y, Z y ∂ν))
  have hi : Integrable (fun x => |Z x - ∫ y, Z y ∂ν|) ν :=
    (hcL2.integrable (by norm_num)).abs
  have hs : Integrable (fun x => |Z x - ∫ y, Z y ∂ν| ^ 2) ν := by
    simpa only [sq_abs, Pi.sub_apply] using hcL2.integrable_sq
  have hn : 0 ≤ ∫ x, (|Z x - ∫ y, Z y ∂ν| - c) ^ 2 ∂ν :=
    integral_nonneg (fun _ => sq_nonneg _)
  have heq : (∫ x, (|Z x - ∫ y, Z y ∂ν| - c) ^ 2 ∂ν) =
      variance Z ν - c ^ 2 := by
    have hf : (fun x => (|Z x - ∫ y, Z y ∂ν| - c) ^ 2) =
        fun x => |Z x - ∫ y, Z y ∂ν| ^ 2 -
          (2 * c) * |Z x - ∫ y, Z y ∂ν| + c ^ 2 := by
      funext x
      ring
    rw [hf]
    have hsub : Integrable (fun x => |Z x - ∫ y, Z y ∂ν| ^ 2 -
        (2 * c) * |Z x - ∫ y, Z y ∂ν|) ν := hs.sub (hi.const_mul (2 * c))
    rw [integral_add hsub (integrable_const (c ^ 2)),
      integral_sub hs (hi.const_mul (2 * c)), integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul, sq_abs]
    rw [← variance_eq_integral hZ.aemeasurable]
    change variance Z ν - (2 * c) * c + c ^ 2 = variance Z ν - c ^ 2
    ring
  rw [heq] at hn
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _)) (variance_nonneg Z ν)).2
    (by dsimp [c] at hn ⊢; linarith)

/-- Chebyshev at five standard deviations gives at least 24/25 coverage,
including when the variance and radius vanish. -/
-- @node: centered_five_sigma_coverage
lemma centered_five_sigma_coverage {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (Z : E → ℝ)
    (hMeas : Measurable Z) (hZ : MemLp Z 2 ν) (r : ℝ) (hr : 0 ≤ r)
    (hvar : 25 * variance Z ν ≤ r ^ 2) :
    (24 / 25 : ℝ) ≤ ν.real {x | |Z x - ∫ y, Z y ∂ν| ≤ r} := by
  by_cases hr0 : r = 0
  · have hv : variance Z ν = 0 := by
      rw [hr0] at hvar
      nlinarith [variance_nonneg Z ν]
    have hae := ae_eq_integral_of_variance_eq_zero hZ hv
    have hevent : ν {x | |Z x - ∫ y, Z y ∂ν| ≤ r} = 1 := by
      have hfull : ν {x | |Z x - ∫ y, Z y ∂ν| ≤ r} = ν Set.univ := by
        apply measure_congr
        filter_upwards [hae] with x hx
        change (|Z x - ∫ y, Z y ∂ν| ≤ r) = True
        simp [hx, hr0]
      simpa using hfull
    simp [Measure.real, hevent]
    norm_num
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have htail := meas_ge_le_variance_div_sq hZ hrpos
    have hratio : variance Z ν / r ^ 2 ≤ 1 / 25 := by
      apply (div_le_iff₀ (sq_pos_of_pos hrpos)).2
      linarith
    have hbad : ν.real {x | r < |Z x - ∫ y, Z y ∂ν|} ≤ 1 / 25 := by
      have hm : ν {x | r < |Z x - ∫ y, Z y ∂ν|} ≤ ENNReal.ofReal (1 / 25) :=
        (measure_mono (show {x | r < |Z x - ∫ y, Z y ∂ν|} ⊆
          {x | r ≤ |Z x - ∫ y, Z y ∂ν|} from fun x hx => by
            change r < |Z x - ∫ y, Z y ∂ν| at hx
            change r ≤ |Z x - ∫ y, Z y ∂ν|
            exact hx.le)).trans
          (htail.trans (ENNReal.ofReal_le_ofReal hratio))
      have ht := ENNReal.toReal_mono (by finiteness) hm
      simpa [Measure.real] using ht
    have hmeas : MeasurableSet {x | |Z x - ∫ y, Z y ∂ν| ≤ r} := by
      have hm : Measurable (fun x => |Z x - ∫ y, Z y ∂ν|) := by fun_prop
      exact measurableSet_le hm measurable_const
    have hcompl := measureReal_compl (μ := ν) hmeas
    have hset : {x | |Z x - ∫ y, Z y ∂ν| ≤ r}ᶜ =
        {x | r < |Z x - ∫ y, Z y ∂ν|} := by
      ext x
      simp
    rw [hset, probReal_univ] at hcompl
    linarith

/-- Adding a deterministic bias budget to the five-sigma radius controls
both coverage and the first absolute error moment. -/
-- @node: scalar_bias_variance_guarantees
lemma scalar_bias_variance_guarantees {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (Z : E → ℝ)
    (hMeas : Measurable Z) (hZ : MemLp Z 2 ν) (s b r : ℝ)
    (hr : 0 ≤ r) (hbias : |(∫ x, Z x ∂ν) - s| ≤ b)
    (hvar : 25 * variance Z ν ≤ r ^ 2) :
    (19 / 20 : ℝ) ≤ ν.real {x | |Z x - s| ≤ b + r} ∧
      (∫ x, |Z x - s| ∂ν) ≤ b + r := by
  have htriangle (x : E) : |Z x - s| ≤ |Z x - ∫ y, Z y ∂ν| + b := by
    calc
      _ = |(Z x - ∫ y, Z y ∂ν) + ((∫ y, Z y ∂ν) - s)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add_right hbias _)
  constructor
  · have hc := centered_five_sigma_coverage ν Z hMeas hZ r hr hvar
    have hm : ν.real {x | |Z x - ∫ y, Z y ∂ν| ≤ r} ≤
        ν.real {x | |Z x - s| ≤ b + r} := by
      apply measureReal_mono (h₂ := by finiteness)
      intro x hx
      change |Z x - ∫ y, Z y ∂ν| ≤ r at hx
      exact (htriangle x).trans (by linarith)
    linarith
  · have hc := integral_abs_centered_le_sqrt_variance ν Z hZ
    have hs : Real.sqrt (variance Z ν) ≤ r := by
      apply (Real.sqrt_le_iff).2
      exact ⟨hr, by nlinarith [variance_nonneg Z ν]⟩
    have hi : Integrable (fun x => Z x - ∫ y, Z y ∂ν) ν :=
      (hZ.integrable (by norm_num)).sub (integrable_const (∫ y, Z y ∂ν))
    calc
      _ ≤ ∫ x, |Z x - ∫ y, Z y ∂ν| + b ∂ν :=
        integral_mono ((hZ.integrable (by norm_num)).sub (integrable_const s)).abs
          (hi.abs.add (integrable_const b)) htriangle
      _ = (∫ x, |Z x - ∫ y, Z y ∂ν| ∂ν) + b := by
        rw [integral_add hi.abs (integrable_const b)]
        simp
      _ ≤ b + r := by linarith

/-- The public stochastic allowance is at least five times the variance-budget
standard deviation; the deterministic part is exactly the stated bias allowance. -/
-- @node: energy_scalar_guarantees
lemma energy_scalar_guarantees {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (Z : E → ℝ)
    (hMeas : Measurable Z) (hZ : MemLp Z 2 ν) (s B W V : ℝ) (J : ℕ)
    (hB : 0 ≤ B) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hbias : |(∫ x, Z x ∂ν) - s| ≤
      2 * B * Real.sqrt s + B ^ 2 + 400 * (J : ℝ) ^ (-2 : ℤ))
    (hvar : variance Z ν ≤ 2 * W * (Real.sqrt s + B) ^ 2 + V) :
    (19 / 20 : ℝ) ≤ ν.real {x | |Z x - s| ≤ aci B W * Real.sqrt s + dci B W V J} ∧
      (∫ x, |Z x - s| ∂ν) ≤ aci B W * Real.sqrt s + dci B W V J := by
  let r := 10 * Real.sqrt W * (Real.sqrt s + B) + 5 * Real.sqrt V
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hcross : 0 ≤ Real.sqrt W * (Real.sqrt s + B) * Real.sqrt V := by positivity
  have hsqW := Real.sq_sqrt hW
  have hsqV := Real.sq_sqrt hV
  have hrad : 25 * variance Z ν ≤ r ^ 2 := by
    dsimp [r]
    nlinarith [sq_nonneg (Real.sqrt W * (Real.sqrt s + B)),
      mul_le_mul_of_nonneg_right hsqW.le (sq_nonneg (Real.sqrt s + B)),
      mul_le_mul_of_nonneg_right hsqW.ge (sq_nonneg (Real.sqrt s + B))]
  have htotal : 2 * B * Real.sqrt s + B ^ 2 + 400 * (J : ℝ) ^ (-2 : ℤ) + r =
      aci B W * Real.sqrt s + dci B W V J := by
    dsimp [r, aci, dci]
    ring
  rw [← htotal]
  exact scalar_bias_variance_guarantees ν Z hMeas hZ s _ r hr hbias hrad

/-- The deterministic pilot allowance is nonnegative for positive public multipliers. -/
-- @node: hAllow_nonneg
lemma hAllow_nonneg (C0 : ℝ) (hC0 : 0 ≤ C0) (m mx my : ℕ) :
    0 ≤ hAllow C0 m mx my := by
  unfold hAllow
  split_ifs with hm
  · norm_num
  · have hm3 : 3 ≤ m := Nat.le_of_not_gt hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hlog : 0 ≤ Real.log m := Real.log_nonneg hm1
    positivity

/-- The bias allowance is nonnegative on a nonnegative pilot allowance. -/
-- @node: BAllow_nonneg
lemma BAllow_nonneg (C h : ℝ) (hC : 0 ≤ C) (hh : 0 ≤ h)
    (m K L T q : ℕ) (kt : ℕ → ℕ) : 0 ≤ BAllow C h m K L T q kt := by
  unfold BAllow
  split_ifs <;> positivity

/-- The covariance operator allowance is nonnegative. -/
-- @node: WAllow_nonneg
lemma WAllow_nonneg (C : ℝ) (hC : 0 ≤ C) (m T : ℕ) (kt : ℕ → ℕ) :
    0 ≤ WAllow C m T kt := by
  unfold WAllow
  split_ifs <;> positivity

/-- The covariance square-trace allowance is nonnegative. -/
-- @node: VAllow_nonneg
lemma VAllow_nonneg (C : ℝ) (m J L T : ℕ) (kt : ℕ → ℕ) :
    0 ≤ VAllow C m J L T kt := by
  have hsum : 0 ≤ ∑ t ∈ Finset.range (T + 1),
      (bandDimension L t : ℝ) * (kt t : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun t _ => by positivity)
  unfold VAllow
  split_ifs <;> positivity

end CausalSmith.Stat.DensityEffectRoughNull
