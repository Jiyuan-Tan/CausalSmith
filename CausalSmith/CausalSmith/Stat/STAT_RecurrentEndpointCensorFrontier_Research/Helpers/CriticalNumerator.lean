module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.GeneralSurvivalEnvelopes
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalPredictableComparison

/-!
# Critical endpoint numerator regularity

Roadmap (11): the survival times intensity has a law-independent modulus of
order min(beta, 1). At positive smoothness order the same one-sided
interpolation bounds used for upper risk supply the first derivative bound.
This controls the numerator contribution to the logarithmic expansion (13).
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The numerator in the critical oracle variance has the uniform modulus
in roadmap (11), including smoothness orders greater than one. -/
-- @node: critical_numerator_uniform_holder
lemma critical_numerator_uniform_holder (c : ClassConstants) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ P : SubjectLaw, ModelClass c P → ∀ a : Arm,
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |survival P a x * P.lam a x - survival P a y * P.lam a y| ≤
        K * |x - y| ^ (min c.beta 1) := by
  have hM : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have hD := derivativeEnvelope_nonneg c hM c.Llambda_pos.le
  have hH := derivativeEnvelope_nonneg c
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  by_cases hk : holderOrder c = 0
  · have hβ : c.beta ≤ 1 := by
      simpa [hk] using (holderOrder_remainder_exponent c).2
    refine ⟨productHolderEnvelope c, productHolderEnvelope_nonneg c, ?_⟩
    intro P hP a x hx y hy
    simpa [hk, min_eq_left hβ] using (survival_product_holder c P hP a).2 x hx y hy
  · have hkpos : 0 < holderOrder c := Nat.pos_of_ne_zero hk
    have hβ : 1 ≤ c.beta := by
      have hh := (holderOrder_remainder_exponent c).1
      have hcast : (1 : ℝ) ≤ holderOrder c := by exact_mod_cast hkpos
      linarith
    let D := derivativeEnvelope c c.lambdaMax c.Llambda
    let B := survivalDerivativeEnvelope c 1
    have hB : 0 ≤ B := survivalDerivativeEnvelope_nonneg c hH 1
    refine ⟨D + B * c.lambdaMax, add_nonneg hD (mul_nonneg hB hM), ?_⟩
    intro P hP a x hx y hy
    have hcL : ContDiffOn ℝ (1 : ℕ) (P.lam a) (Icc (0 : ℝ) 1) :=
      (hP.recurrenceHolder a).1.of_le (by exact_mod_cast hkpos)
    have hcS : ContDiffOn ℝ (1 : ℕ) (survival P a) (Icc (0 : ℝ) 1) :=
      (survival_modelClass_contDiffOn c P hP a).of_le (by
        exact_mod_cast (show 1 ≤ holderOrder c + 1 by omega))
    have hL := Causalean.Mathlib.Analysis.Calculus.HolderTaylor.lower_jet_holder_of_next_bound
      0 1 0 1 D (by norm_num) (by norm_num) (by norm_num) hD (P.lam a)
      (by simpa using hcL) (by
        intro t ht
        simpa using recurrence_jet_bound c P hP a (by simpa using ht) ⟨1, by omega⟩)
      x (by simpa using hx) y (by simpa using hy)
    have hS := Causalean.Mathlib.Analysis.Calculus.HolderTaylor.lower_jet_holder_of_next_bound
      0 1 0 1 B (by norm_num) (by norm_num) (by norm_num) hB (survival P a)
      (by simpa using hcS) (by
        intro t ht
        simpa using survival_jet_bound c P hP a (j := 1) (by omega) (by simpa using ht))
      x (by simpa using hx) y (by simpa using hy)
    simp only [iteratedDerivWithin_zero, sub_self, Real.rpow_zero, mul_one,
      Real.rpow_one, zero_add] at hL hS
    have hSy : |survival P a x| ≤ 1 := by
      rw [abs_of_pos (show 0 < survival P a x from Real.exp_pos _)]
      exact (survival_bounds_of_deathBounds c P hP.deathBounds a hx).2
    have hLy : |P.lam a y| ≤ c.lambdaMax := by
      rw [abs_of_nonneg (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a y hy).1)]
      exact (hP.recurrenceBounds a y hy).2
    rw [min_eq_right hβ, Real.rpow_one]
    calc
      _ = |survival P a x * (P.lam a x - P.lam a y) +
          (survival P a x - survival P a y) * P.lam a y| := by congr 1; ring
      _ ≤ |survival P a x| * |P.lam a x - P.lam a y| +
          |survival P a x - survival P a y| * |P.lam a y| := by
        simpa only [abs_mul] using abs_add_le
          (survival P a x * (P.lam a x - P.lam a y))
          ((survival P a x - survival P a y) * P.lam a y)
      _ ≤ 1 * (D * |x - y|) + (B * |x - y|) * c.lambdaMax := by
        gcongr
      _ = _ := by ring

/-- Subtracting the endpoint inverse-linear term from the full oracle density
leaves two integrable powers, from numerator smoothness and retention error. -/
-- @node: critical_oracle_terminal_remainder_uniform_le
lemma critical_oracle_terminal_remainder_uniform_le (c : ClassConstants)
    (hk : c.kappa = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ P : SubjectLaw, ModelClass c P → ∀ a : Arm,
      ∀ x : ℝ, 0 < x → x ≤ c.x0 →
      |survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x) -
        survival P a 1 * P.lam a 1 / (P.g a * x)| ≤
      K * x ^ (min c.beta 1 - 1) +
        (c.lambdaMax * (2 * c.LG / c.gMin)) * x ^ (c.rho - 1) := by
  obtain ⟨B, hB, hmod⟩ := critical_numerator_uniform_holder c
  refine ⟨2 * B / c.gMin, div_nonneg (mul_nonneg (by norm_num) hB) c.gMin_pos.le, ?_⟩
  intro P hP a x hx hx0
  have ht : 1 - x ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [c.x0_le]
  have he := hmod P hP a (1 - x) ht 1 (by norm_num)
  rw [show 1 - x - 1 = -x by ring, abs_neg, abs_of_pos hx] at he
  have hg : 0 < P.g a := c.gMin_pos.trans_le (hP.endpointCoefficientBounds a).1
  obtain ⟨hr, hr2⟩ := critical_endpoint_retention_relative_error_le c hk P hP a hx hx0
  have hratio : 1 / 2 ≤ retention P a (1 - x) / (P.g a * x) := by
    have := (abs_le.mp hr).1
    linarith
  have hG : c.gMin / 2 * x ≤ retention P a (1 - x) := by
    have hm := (le_div_iff₀ (mul_pos hg hx)).mp hratio
    have hgm := mul_le_mul_of_nonneg_right (hP.endpointCoefficientBounds a).1 hx.le
    nlinarith
  have hGpos : 0 < retention P a (1 - x) :=
    (mul_pos (div_pos c.gMin_pos (by norm_num)) hx).trans_le hG
  have hF : |survival P a 1 * P.lam a 1| ≤ c.lambdaMax := by
    rw [abs_mul, abs_of_pos (show 0 < survival P a 1 from Real.exp_pos _),
      abs_of_nonneg (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a 1 (by norm_num)).1)]
    exact (mul_le_mul (survival_bounds_of_deathBounds c P hP.deathBounds a
      (by norm_num)).2 (hP.recurrenceBounds a 1 (by norm_num)).2
      (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a 1 (by norm_num)).1)
      (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
  have hnum : |(survival P a (1 - x) * P.lam a (1 - x) -
      survival P a 1 * P.lam a 1) / retention P a (1 - x)| ≤
      (2 * B / c.gMin) * x ^ (min c.beta 1 - 1) := by
    rw [abs_div, abs_of_pos hGpos]
    calc
      _ ≤ (B * x ^ (min c.beta 1)) / (c.gMin / 2 * x) :=
        div_le_div₀ (mul_nonneg hB (Real.rpow_nonneg hx.le _)) he (mul_pos (div_pos c.gMin_pos (by norm_num)) hx) hG
      _ = _ := by rw [Real.rpow_sub hx, Real.rpow_one]; field_simp
  calc
    _ = |(survival P a (1 - x) * P.lam a (1 - x) -
        survival P a 1 * P.lam a 1) / retention P a (1 - x) +
        (survival P a 1 * P.lam a 1) *
          (1 / retention P a (1 - x) - 1 / (P.g a * x))| := by congr 1; ring
    _ ≤ |(survival P a (1 - x) * P.lam a (1 - x) -
        survival P a 1 * P.lam a 1) / retention P a (1 - x)| +
        |survival P a 1 * P.lam a 1| *
          |1 / retention P a (1 - x) - 1 / (P.g a * x)| := by
      simpa only [abs_mul] using abs_add_le
        ((survival P a (1 - x) * P.lam a (1 - x) -
          survival P a 1 * P.lam a 1) / retention P a (1 - x))
        ((survival P a 1 * P.lam a 1) *
          (1 / retention P a (1 - x) - 1 / (P.g a * x)))
    _ ≤ _ := add_le_add hnum (by
      have hr := critical_endpoint_inverse_retention_remainder_uniform_le c hk P hP a hx hx0
      calc
        _ ≤ c.lambdaMax * ((2 * c.LG / c.gMin) * x ^ (c.rho - 1)) := by
          exact mul_le_mul hF hr (abs_nonneg _)
            (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
        _ = _ := by ring)

/-- The terminal correction to the principal logarithmic density is integrable
at zero and has a law-independent bounded integral on every truncated region.
This supplies both power remainders in roadmap (13). -/
-- @node: critical_oracle_terminal_remainder_integral_uniform
lemma critical_oracle_terminal_remainder_integral_uniform (c : ClassConstants)
    (hk : c.kappa = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : SubjectLaw, ModelClass c P → ∀ a : Arm,
      IntervalIntegrable (fun x =>
        survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x) -
          survival P a 1 * P.lam a 1 / (P.g a * x)) volume 0 c.x0 ∧
      ∀ h : ℝ, 0 ≤ h → h ≤ c.x0 →
        |∫ x in h..c.x0,
          survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x) -
            survival P a 1 * P.lam a 1 / (P.g a * x)| ≤ C := by
  obtain ⟨K, hK, hb⟩ := critical_oracle_terminal_remainder_uniform_le c hk
  let η := min c.beta 1
  let R := c.lambdaMax * (2 * c.LG / c.gMin)
  have hη : 0 < η := lt_min c.beta_pos (by norm_num)
  have hR : 0 ≤ R := mul_nonneg (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
    (div_nonneg (mul_nonneg (by norm_num) c.LG_pos.le) c.gMin_pos.le)
  refine ⟨K * (c.x0 ^ η / η) + R * (c.x0 ^ c.rho / c.rho),
    add_nonneg (mul_nonneg hK (div_nonneg (Real.rpow_nonneg c.x0_pos.le _) hη.le))
      (mul_nonneg hR (div_nonneg (Real.rpow_nonneg c.x0_pos.le _) c.rho_pos.le)), ?_⟩
  intro P hP a
  let f := fun x => survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x) -
    survival P a 1 * P.lam a 1 / (P.g a * x)
  let g := fun x : ℝ => K * x ^ (η - 1) + R * x ^ (c.rho - 1)
  have hg : IntervalIntegrable g volume 0 c.x0 :=
    ((intervalIntegral.intervalIntegrable_rpow' (r := η - 1)
      (by linarith) (a := 0) (b := c.x0)).const_mul K).add
      ((intervalIntegral.intervalIntegrable_rpow' (r := c.rho - 1)
        (by linarith [c.rho_pos]) (a := 0) (b := c.x0)).const_mul R)
  have hf : IntervalIntegrable f volume 0 c.x0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le c.x0_pos.le] at hg ⊢
    apply hg.mono' ?_ ?_
    · have hcomp : ContinuousOn (fun x : ℝ => 1 - x) (Ioc 0 c.x0) := by fun_prop
      have hmaps : MapsTo (fun x : ℝ => 1 - x) (Ioc 0 c.x0) (Icc 0 1) := by
        intro x hx
        constructor <;> linarith [hx.1, hx.2, c.x0_le]
      have hc := ((modelClass_survival_continuousOn c P hP a).mul
        (hP.recurrenceHolder a).1.continuousOn).comp hcomp hmaps
      have hmG := (measurable_retention P a).comp
        (show Measurable (fun x : ℝ => 1 - x) by fun_prop)
      exact (((hc.aestronglyMeasurable measurableSet_Ioc).aemeasurable.div
        hmG.aemeasurable.restrict).sub
          (measurable_const.div (measurable_const.mul measurable_id)).aemeasurable.restrict).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      simpa only [f, g, η, R, Real.norm_eq_abs] using hb P hP a x hx.1 hx.2
  refine ⟨hf, ?_⟩
  intro h hh hh0
  have hsub : uIcc h c.x0 ⊆ uIcc 0 c.x0 := by
    rw [uIcc_of_le hh0, uIcc_of_le c.x0_pos.le]
    exact Icc_subset_Icc hh le_rfl
  have hfi := hf.mono_set hsub
  have hgi := hg.mono_set hsub
  calc
    _ ≤ ∫ x in h..c.x0, |f x| := intervalIntegral.abs_integral_le_integral_abs hh0
    _ ≤ ∫ x in h..c.x0, g x := by
      apply intervalIntegral.integral_mono_ae_restrict hh0 hfi.abs hgi
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        (volume.restrict (Icc h c.x0)).ae_ne (0 : ℝ)] with x hx hxne
      exact hb P hP a x (lt_of_le_of_ne (hh.trans hx.1) (Ne.symm hxne)) hx.2
    _ = K * ((c.x0 ^ η - h ^ η) / η) +
        R * ((c.x0 ^ c.rho - h ^ c.rho) / c.rho) := by
      have hiη := (intervalIntegral.intervalIntegrable_rpow' (r := η - 1)
        (by linarith) (a := h) (b := c.x0)).const_mul K
      have hiρ := (intervalIntegral.intervalIntegrable_rpow' (r := c.rho - 1)
        (by linarith [c.rho_pos]) (a := h) (b := c.x0)).const_mul R
      dsimp [g]
      rw [intervalIntegral.integral_add hiη hiρ, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < η - 1)),
        integral_rpow (Or.inl (by linarith [c.rho_pos] : -1 < c.rho - 1))]
      simp only [sub_add_cancel]
    _ ≤ _ := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hK
        apply div_le_div_of_nonneg_right _ hη.le
        linarith [Real.rpow_nonneg hh η]
      · apply mul_le_mul_of_nonneg_left _ hR
        apply div_le_div_of_nonneg_right _ c.rho_pos.le
        linarith [Real.rpow_nonneg hh c.rho]

/-- The unweighted terminal oracle integral has exactly the paper's endpoint
logarithmic coefficient, with a remainder bounded uniformly over model laws. -/
-- @node: critical_oracle_terminal_log_expansion_uniform
lemma critical_oracle_terminal_log_expansion_uniform (c : ClassConstants)
    (hk : c.kappa = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : SubjectLaw, ModelClass c P → ∀ a : Arm,
      ∀ h : ℝ, 0 < h → h ≤ c.x0 →
        |(∫ x in h..c.x0,
          survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x)) -
            (survival P a 1 * P.lam a 1 / P.g a) * Real.log (c.x0 / h)| ≤ C := by
  obtain ⟨C, hC, hb⟩ := critical_oracle_terminal_remainder_integral_uniform c hk
  refine ⟨C, hC, ?_⟩
  intro P hP a h hh hh0
  obtain ⟨hi, hbound⟩ := hb P hP a
  have hsub : uIcc h c.x0 ⊆ uIcc 0 c.x0 := by
    rw [uIcc_of_le hh0, uIcc_of_le c.x0_pos.le]
    exact Icc_subset_Icc hh.le le_rfl
  have hir := hi.mono_set hsub
  have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume h c.x0 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hh0
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx
    exact (hh.trans_le hx.1).ne'
  have heq : (fun x : ℝ => survival P a 1 * P.lam a 1 / (P.g a * x)) =
      (fun x => (survival P a 1 * P.lam a 1 / P.g a) * x⁻¹) := by
    funext x
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hip : IntervalIntegrable (fun x : ℝ => survival P a 1 * P.lam a 1 /
      (P.g a * x)) volume h c.x0 := by
    rw [heq]
    exact hinv.const_mul _
  have hif : IntervalIntegrable (fun x =>
      survival P a (1 - x) * P.lam a (1 - x) / retention P a (1 - x)) volume h c.x0 := by
    convert hir.add hip using 1
    ext x
    exact (sub_add_cancel _ _).symm
  have he : (∫ x in h..c.x0, survival P a 1 * P.lam a 1 / (P.g a * x)) =
      (survival P a 1 * P.lam a 1 / P.g a) * Real.log (c.x0 / h) := by
    rw [heq, intervalIntegral.integral_const_mul, integral_inv_of_pos hh c.x0_pos]
  have hb' := hbound h hh.le hh0
  rw [intervalIntegral.integral_sub hif hip, he] at hb'
  exact hb'

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
