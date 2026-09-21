module
public import Causalean.ML.Lasso.SubGaussian
public import Causalean.Mathlib.MeasureTheory.CompactArgminSelection

/-!
# High-probability fixed-design Lasso oracle bounds

This module constructs a Borel measurable exact Lasso minimizer and combines
the deterministic oracle inequality with the sub-Gaussian score event.
-/

@[expose] public section

namespace Causalean.ML

open MeasureTheory ProbabilityTheory Metric Matrix

private lemma euclidean_norm_coeff_le_l1 {p : ℕ} (β : Fin p → ℝ) :
    ‖(EuclideanSpace.equiv (Fin p) ℝ).symm β‖ ≤ l1penalty β := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  constructor
  · exact l1penalty_nonneg β
  · simpa [l1penalty, sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset (Fin p))) (f := fun j => |β j|)
        (fun _ _ => abs_nonneg _))

/-- [Exact Lasso solutions admit a Borel measurable response rule](goal) for
[a fixed design](hyp:X) with [positive sample and coefficient dimensions](hyp:hn,hp) and
[a strictly positive penalty](hyp:lam,hlam). Measurability makes the
optimizer usable as a random estimator. -/
theorem exists_measurable_lassoMinimizer
    {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (lam : ℝ)
    (hn : 0 < n) (hp : 0 < p) (hlam : 0 < lam) :
    ∃ βhat : (Fin n → ℝ) → (Fin p → ℝ),
      Measurable βhat ∧ ∀ y, IsLassoMinimizer X y lam (βhat y) := by
  classical
  let _ : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp hp
  let E := EuclideanSpace.equiv (Fin p) ℝ
  let K : Set (EuclideanSpace ℝ (Fin p)) := closedBall 0 1
  let r : (Fin n → ℝ) → ℝ := fun y => fixedDesignLoss X y 0 / lam + 1
  let f : (Fin n → ℝ) × EuclideanSpace ℝ (Fin p) → ℝ := fun yg =>
    normalizedLassoObjective X yg.1 lam (r yg.1 • E yg.2)
  have hr_pos : ∀ y, 0 < r y := by
    intro y
    have hloss : 0 ≤ fixedDesignLoss X y 0 := by
      unfold fixedDesignLoss
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    dsimp [r]
    positivity
  have hK : IsCompact K := ProperSpace.isCompact_closedBall 0 1
  have hKne : K.Nonempty := ⟨0, by simp [K]⟩
  have hf : Measurable f := by
    unfold f r normalizedLassoObjective fixedDesignLoss l1penalty
    fun_prop
  have hfc : ∀ y, ContinuousOn (fun g => f (y, g)) K := by
    intro y
    apply Continuous.continuousOn
    unfold f r normalizedLassoObjective fixedDesignLoss l1penalty
    fun_prop
  obtain ⟨g, hgmeas, hgmin⟩ :=
    Causalean.Mathlib.MeasureTheory.borelMeasurable_compact_argmin_selector
      K hK hKne f hf hfc
  let βhat : (Fin n → ℝ) → (Fin p → ℝ) := fun y => r y • E (g y)
  refine ⟨βhat, ?_, ?_⟩
  · unfold βhat r fixedDesignLoss
    fun_prop
  · intro y β
    have hzeroK : (0 : EuclideanSpace ℝ (Fin p)) ∈ K := by simp [K]
    have hselected_zero : normalizedLassoObjective X y lam (βhat y) ≤
        normalizedLassoObjective X y lam 0 := by
      simpa [βhat, f] using (hgmin y).2 0 hzeroK
    by_cases hβ : ‖E.symm β‖ ≤ r y
    · let u : EuclideanSpace ℝ (Fin p) := (r y)⁻¹ • E.symm β
      have huK : u ∈ K := by
        change u ∈ closedBall (0 : EuclideanSpace ℝ (Fin p)) 1
        rw [mem_closedBall, dist_zero_right, norm_smul]
        dsimp [u]
        have hinvabs : |(r y)⁻¹| = (r y)⁻¹ := abs_of_pos (inv_pos.mpr (hr_pos y))
        rw [hinvabs]
        rw [inv_mul_le_one₀ (hr_pos y)]
        exact hβ
      have hmin := (hgmin y).2 u huK
      have hscale : r y • E u = β := by
        dsimp [u]
        rw [map_smul, smul_smul, mul_inv_cancel₀ (hr_pos y).ne', one_smul,
          E.apply_symm_apply]
      simpa [βhat, f, hscale] using hmin
    · have hr_lt_l1 : r y < l1penalty β :=
        lt_of_not_ge hβ |>.trans_le (euclidean_norm_coeff_le_l1 β)
      have hlossβ : 0 ≤ fixedDesignLoss X y β := by
        unfold fixedDesignLoss
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have hzero : normalizedLassoObjective X y lam 0 <
          normalizedLassoObjective X y lam β := by
        unfold normalizedLassoObjective
        have hr_eq : lam * r y = fixedDesignLoss X y 0 + lam := by
          dsimp [r]
          field_simp [hlam.ne']
        have := mul_lt_mul_of_pos_left hr_lt_l1 hlam
        change fixedDesignLoss X y 0 + lam * l1penalty 0 <
          fixedDesignLoss X y β + lam * l1penalty β
        rw [show l1penalty (0 : Fin p → ℝ) = 0 by simp [l1penalty], mul_zero, add_zero]
        nlinarith [hr_eq]
      exact hselected_zero.trans hzero.le

/-- **Sub-Gaussian Lasso oracle inequality.** Given [a probability law](hyp:μ), a
[fixed design](hyp:X), [noise coordinates](hyp:w), [positive noise scale and confidence
level](hyp:sigma,delta), a [true coefficient](hyp:βstar) with [support](hyp:S) of
[size](hyp:s), and [restricted-eigenvalue constant](hyp:kappa), assume [positive
dimensions](hyp:hn,hp), [positive scale](hyp:hsigma), [a confidence level strictly
between zero and one](hyp:hdelta,hdelta1), [measurable noise](hyp:hwmeas),
[independence](hyp:hindep), [sub-Gaussian moment bounds](hyp:hsubg), [normalized design
columns](hyp:hcol), [support containment](hyp:hsupp), [the asserted support
size](hyp:hcard), [positive curvature](hyp:hkappa), and [restricted
eigenvalues](hyp:hRE). Then [there is a measurable exact Lasso minimizer whose Euclidean,
one-norm, and prediction errors simultaneously obey the stated bounds with probability at
least `1 - delta`](goal). -/
theorem lasso_oracle_inequality_of_subgaussian
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → Ω → ℝ)
    (sigma delta : ℝ) (βstar : Fin p → ℝ) (S : Finset (Fin p)) (s : ℕ)
    (kappa : ℝ)
    (hn : 0 < n) (hp : 0 < p) (hsigma : 0 < sigma)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hwmeas : ∀ i, Measurable (w i)) (hindep : iIndepFun w μ)
    (hsubg : ∀ i, HasSubgaussianMGF (w i) ⟨sigma ^ 2, sq_nonneg sigma⟩ μ)
    (hcol : ∀ j, ∑ i, X i j ^ 2 ≤ (n : ℝ))
    (hsupp : ∀ j ∉ S, βstar j = 0) (hcard : S.card = s)
    (hkappa : 0 < kappa) (hRE : RestrictedEigenvalue X S kappa) :
    ∃ βhat : Ω → (Fin p → ℝ),
      Measurable βhat ∧
      (∀ ω, IsLassoMinimizer X
        (X *ᵥ βstar + fun i => w i ω)
        (2 * sigma * Real.sqrt (2 * Real.log (2 * p / delta) / n)) (βhat ω)) ∧
      μ.real {ω |
        finiteL2Norm (βhat ω - βstar) ≤
            6 * sigma * Real.sqrt (2 * s * Real.log (2 * p / delta) / n) / kappa ∧
        l1penalty (βhat ω - βstar) ≤
            24 * sigma * s * Real.sqrt (2 * Real.log (2 * p / delta) / n) / kappa ∧
        fixedDesignPredictionError X (βhat ω - βstar) ≤
            36 * s * sigma ^ 2 * (2 * Real.log (2 * p / delta) / n) / kappa} ≥
        1 - delta := by
  classical
  let a : ℝ := 2 * Real.log (2 * (p : ℝ) / delta) / n
  let lam : ℝ := 2 * sigma * Real.sqrt a
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hratio : 1 < 2 * (p : ℝ) / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith [hp1, hdelta1]
  have hlog : 0 < Real.log (2 * (p : ℝ) / delta) := Real.log_pos hratio
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hlam : 0 < lam := by
    dsimp [lam]
    positivity
  obtain ⟨select, hselectMeas, hselectMin⟩ :=
    exists_measurable_lassoMinimizer X lam hn hp hlam
  let y : Ω → (Fin n → ℝ) := fun ω => X *ᵥ βstar + fun i => w i ω
  let βhat : Ω → (Fin p → ℝ) := fun ω => select (y ω)
  have hyMeas : Measurable y := by
    unfold y
    fun_prop
  have hβhatMeas : Measurable βhat := hselectMeas.comp hyMeas
  have hβhatMin : ∀ ω, IsLassoMinimizer X (y ω) lam (βhat ω) := fun ω =>
    hselectMin (y ω)
  have hscore := lasso_score_event_of_subgaussian μ X w sigma delta hn hp hsigma
    hdelta hdelta1 hwmeas hindep hsubg hcol
  have hsqrt_combine : Real.sqrt (s : ℝ) * Real.sqrt a =
      Real.sqrt (2 * s * Real.log (2 * p / delta) / n) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg s)]
    congr 1
    dsimp [a]
    ring
  have hlam_sq : lam ^ 2 = 4 * sigma ^ 2 * a := by
    dsimp [lam]
    rw [mul_pow, mul_pow, Real.sq_sqrt ha.le]
    ring
  refine ⟨βhat, hβhatMeas, ?_, ?_⟩
  · intro ω
    simpa [βhat, y, lam, a] using hβhatMin ω
  · refine hscore.trans (MeasureTheory.measureReal_mono ?_ (measure_ne_top μ _))
    intro ω hω
    have horacle := lasso_oracle_inequality X (y ω) (fun i => w i ω)
      βstar (βhat ω) S s lam kappa hn rfl hsupp hcard hlam (by simpa [lam, a] using hω)
      hkappa hRE (hβhatMin ω)
    rcases horacle with ⟨hl2, hl1, hpred⟩
    constructor
    · calc
        finiteL2Norm (βhat ω - βstar) ≤
            3 * Real.sqrt s * lam / kappa := hl2
        _ = 6 * sigma * Real.sqrt (2 * s * Real.log (2 * p / delta) / n) /
              kappa := by dsimp [lam]; rw [← hsqrt_combine]; ring
    constructor
    · calc
        l1penalty (βhat ω - βstar) ≤ 12 * s * lam / kappa := hl1
        _ = 24 * sigma * s * Real.sqrt (2 * Real.log (2 * p / delta) / n) /
              kappa := by simp only [lam, a]; ring
    · calc
        fixedDesignPredictionError X (βhat ω - βstar) ≤
            9 * s * lam ^ 2 / kappa := hpred
        _ = 36 * s * sigma ^ 2 * (2 * Real.log (2 * p / delta) / n) /
              kappa := by rw [hlam_sq]; dsimp [a]; ring

end Causalean.ML
