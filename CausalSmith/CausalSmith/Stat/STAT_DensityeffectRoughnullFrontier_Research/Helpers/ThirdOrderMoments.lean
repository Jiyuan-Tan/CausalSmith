module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.SecondOrderCovariance

/-! Observed second moments for the third-order singleton and pair projections.
Cell contraction and the conditional outcome moment preserve the roadmap's constants. -/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The coefficient-error vector is integrable and has design energy at most 900. -/
-- @node: verr_coefficients_design_energy
lemma verr_coefficients_design_energy (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J : ℕ) (hJ : 0 < J) (a : Bool) :
    Integrable (fun x => coefficients J (verr P train mx my a x)) unitVolume ∧
    Integrable (fun x => ‖coefficients J (verr P train mx my a x)‖ ^ 2) unitVolume ∧
    (∫ x, ‖coefficients J (verr P train mx my a x)‖ ^ 2 ∂unitVolume) ≤ 900 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hv : Integrable (fun x => coefficients J (verr P train mx my a x)) unitVolume := by
    apply integrable_coefficients_design
    change Integrable (fun z : ℝ × ℝ => verr P train mx my a z.1 z.2) _
    simpa only [pow_zero, one_mul, Function.uncurry] using
      integrable_uerr_pow_mul_verr_joint P hModel train mx my a 0
  have hb : ∀ᵐ x ∂unitVolume, ‖coefficients J (verr P train mx my a x)‖ ^ 2 ≤ 900 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    nlinarith [verr_coefficients_norm_le P hModel train mx my J hJ a x hx,
      norm_nonneg (coefficients J (verr P train mx my a x))]
  have hv2 : Integrable (fun x => ‖coefficients J (verr P train mx my a x)‖ ^ 2)
      unitVolume := by
    apply (integrable_const (900 : ℝ)).mono' (hv.aestronglyMeasurable.norm.pow 2)
    filter_upwards [hb] with x hx
    change ‖‖coefficients J (verr P train mx my a x)‖ ^ 2‖ ≤ 900
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine ⟨hv, hv2, ?_⟩
  simpa using integral_mono_ae hv2 (integrable_const (900 : ℝ)) hb

/-- Each treatment singleton in (10) has the observed second-moment bound (11). -/
-- @node: observed_third_treatment_singleton_moment_le
lemma observed_third_treatment_singleton_moment_le (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (train : Fin m → Omega) (mx my J q : ℕ) (hJ : 0 < J) (hq : 0 < q)
    (a : Bool) (f : Hj J) :
    (∫ o, (Rres train mx a o * cellAverage q (uerr P train mx a) (X o) *
      inner ℝ (cellAverage q (fun z => coefficients J (verr P train mx my a z))
        (X o)) f) ^ 2 ∂P.law) ≤ 32400 * ‖f‖ ^ 2 := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  obtain ⟨hv, hv2, hE⟩ := verr_coefficients_design_energy P hModel train mx my J hJ a
  have h := integral_Rres_design_sq_le P hModel train mx a
    (fun x => cellAverage q (uerr P train mx a) x *
      inner ℝ (cellAverage q (fun z => coefficients J (verr P train mx my a z)) x) f)
    (by
      apply measurable_of_histogram_const q
      intro x z hxz
      simp only [cellAverage_eq_of_cell_eq q _ x z hxz]) (chain_finite_range_binary (finite_range_cellAverage q _)
      (chain_finite_range_comp (finite_range_cellAverage q _) (fun v => inner ℝ v f)) (· * ·))
  simp only [mul_pow] at h
  have hc := conditional_third_treatment_singleton_le P hModel train mx q hq a _ hv hv2 f
  simp_rw [mul_assoc] at hc
  rw [integral_const_mul] at hc
  calc
    _ ≤ _ := by simpa only [mul_assoc, mul_pow] using h
    _ ≤ 36 * (∫ x, ‖coefficients J (verr P train mx my a x)‖ ^ 2 ∂unitVolume) * ‖f‖ ^ 2 := by simpa only [mul_assoc] using hc
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hE (sq_nonneg ‖f‖)]

/-- The treatment pair in (12) has second moment at most 72900q times test energy. -/
-- @node: observed_third_treatment_pair_moment_le
lemma observed_third_treatment_pair_moment_le (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (train : Fin m → Omega) (mx my J q : ℕ) (hJ : 0 < J) (hq : 0 < q)
    (a : Bool) (f : Hj J) :
    (∫ o1, ∫ o2, (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * inner ℝ
        (cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o2)) f) ^ 2
      ∂P.law ∂P.law) ≤ 72900 * q * ‖f‖ ^ 2 := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  let g := fun x => inner ℝ
    (cellAverage q (fun z => coefficients J (verr P train mx my a z)) x) f
  have hg : Measurable g := by
    apply measurable_of_histogram_const q
    intro x z hxz
    dsimp [g]
    rw [cellAverage_eq_of_cell_eq q _ x z hxz]
  have hgf : (Set.range g).Finite := chain_finite_range_comp
    (finite_range_cellAverage q _) (fun v => inner ℝ v f)
  obtain ⟨hv, hv2, hE⟩ := verr_coefficients_design_energy P hModel train mx my J hJ a
  have hi : Integrable (fun z : Omega × Omega =>
      (Rres train mx a z.1 * covariateKernel q (X z.1) (X z.2) *
        Rres train mx a z.2 * g (X z.2)) ^ 2) (P.law.prod P.law) := by
    apply integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
    apply chain_finite_range_comp (g := fun r => r ^ 2)
    apply chain_finite_range_binary (op := (· * ·))
    · apply chain_finite_range_binary (op := (· * ·))
      · apply chain_finite_range_binary (op := (· * ·))
        · exact chain_finite_range_precomp (finite_range_Rres train mx a) Prod.fst
        · exact chain_finite_range_precomp (finite_range_covariateKernel q) (fun z : Omega × Omega => (X z.1, X z.2))
      · exact chain_finite_range_precomp (finite_range_Rres train mx a) Prod.snd
    · exact chain_finite_range_precomp hgf (fun z : Omega × Omega => X z.2)
  change (∫ o1, ∫ o2, (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
    Rres train mx a o2 * g (X o2)) ^ 2 ∂P.law ∂P.law) ≤ _
  rw [integral_integral_swap hi]
  have hr (o2 : Omega) :
      (∫ o1, (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
        Rres train mx a o2 * g (X o2)) ^ 2 ∂P.law) ≤
      (9 * q) * (Rres train mx a o2 * g (X o2)) ^ 2 := by
    have he (o1 : Omega) :
        (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
          Rres train mx a o2 * g (X o2)) ^ 2 =
        (Rres train mx a o1) ^ 2 * (covariateKernel q (X o2) (X o1)) ^ 2 *
          (Rres train mx a o2 * g (X o2)) ^ 2 := by
      rw [covariateKernel_symm q (X o1) (X o2)]
      ring
    simp_rw [he]
    calc
      _ ≤ ∫ o1, 9 * (covariateKernel q (X o2) (X o1)) ^ 2 *
          (Rres train mx a o2 * g (X o2)) ^ 2 ∂P.law := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun _ => by positivity)
        · exact (integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
            (chain_finite_range_comp (chain_finite_range_precomp
              (finite_range_covariateKernel q) (fun o1 => (X o2, X o1)))
              (fun r => 9 * r ^ 2 * (Rres train mx a o2 * g (X o2)) ^ 2)))
        · exact Filter.Eventually.of_forall (fun o1 => mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (Rres_sq_le_nine train mx a o1) (sq_nonneg _))
            (sq_nonneg _))
      _ = _ := by
        rw [integral_mul_const, integral_const_mul, integral_observed_covariateKernel_sq P hModel q hq]
  calc
    _ ≤ ∫ o2, (9 * q) * (Rres train mx a o2 * g (X o2)) ^ 2 ∂P.law := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      · exact (integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
          (chain_finite_range_comp (chain_finite_range_binary (finite_range_Rres train mx a)
            (chain_finite_range_precomp hgf X) (· * ·)) (fun r => r ^ 2))).const_mul _
      · exact Filter.Eventually.of_forall hr
    _ = (9 * q) * ∫ o2, (Rres train mx a o2 * g (X o2)) ^ 2 ∂P.law := integral_const_mul _ _
    _ ≤ (9 * q) * (9 * ∫ x, (g x) ^ 2 ∂unitVolume) :=
      mul_le_mul_of_nonneg_left (integral_Rres_design_sq_le P hModel train mx a g hg hgf) (by positivity)
    _ ≤ (81 * q) * ((∫ x, ‖coefficients J (verr P train mx my a x)‖ ^ 2 ∂unitVolume) * ‖f‖ ^ 2) := by
      have h := integral_cellAverage_inner_sq_le q hq _ hv hv2 f
      dsimp [g]
      nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 81 * q)]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hE (sq_nonneg ‖f‖)) (by positivity : (0 : ℝ) ≤ 81 * q)
      nlinarith


/-- Retaining a subset of three roles integrates exactly the complementary observations. -/
-- @node: partial_role_three_iterated
lemma partial_role_three_iterated {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (h : (Fin 3 → E) → ℝ)
    (hh : Measurable h) (hf : (Set.range h).Finite) (S : Finset (Fin 3)) (o : Fin 3 → E) :
    partialRoleKernel μ 3 S h o = ∫ x, ∫ y, ∫ z,
      h ![if 0 ∈ S then o 0 else x, if 1 ∈ S then o 1 else y,
        if 2 ∈ S then o 2 else z] ∂μ ∂μ ∂μ := by
  unfold partialRoleKernel
  rw [integral_three_roles_eq_iterated μ _
    (integrable_of_measurable_finite_range _ _ (by
      apply hh.comp
      apply measurable_pi_lambda
      intro r
      split_ifs <;> fun_prop) (chain_finite_range_precomp hf _))]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  funext z
  congr 1
  funext r
  fin_cases r <;> simp

/-- The scalar third-order kernel's pair {1,2} projection is (12) tested by f. -/
-- @node: third_score_pair12
lemma third_score_pair12 (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx my J q : ℕ) (a : Bool) (f : Hj J) (o1 o2 : Omega) :
    (∫ o3, Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
      inner ℝ (Vres train mx my J a o3) f ∂P.law) =
    Rres train mx a o1 * covariateKernel q (X o1) (X o2) * Rres train mx a o2 *
      inner ℝ (cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o2)) f := by
  simp_rw [mul_assoc (Rres train mx a o1 * covariateKernel q (X o1) (X o2) * Rres train mx a o2)]
  rw [integral_const_mul, integral_tested_Vres_covariateKernel]

/-- The scalar endpoint pair projection uses the exact middle-cell identity. -/
-- @node: third_score_pair13
lemma third_score_pair13 (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) (f : Hj J) (o1 o3 : Omega) :
    (∫ o2, Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
      inner ℝ (Vres train mx my J a o3) f ∂P.law) =
    Rres train mx a o1 * covariateKernel q (X o1) (X o3) *
      cellAverage q (uerr P train mx a) (X o1) * inner ℝ (Vres train mx my J a o3) f := by
  rw [integral_mul_const]
  have he (o2 : Omega) : Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3) =
      Rres train mx a o1 * (covariateKernel q (X o1) (X o2) *
        Rres train mx a o2 * covariateKernel q (X o2) (X o3)) := by ring
  simp_rw [he]
  rw [integral_const_mul, integral_middle_Rres_kernel P hModel]
  ring

/-- The scalar final pair projection integrates the first treatment role. -/
-- @node: third_score_pair23
lemma third_score_pair23 (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) (f : Hj J) (o2 o3 : Omega) :
    (∫ o1, Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
      inner ℝ (Vres train mx my J a o3) f ∂P.law) =
    Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
      cellAverage q (uerr P train mx a) (X o2) * inner ℝ (Vres train mx my J a o3) f := by
  simp_rw [integral_mul_const, integral_Rres_covariateKernel P hModel]
  ring

/-- A tested cell mean is constant along a matching-cell kernel. -/
-- @node: covariateKernel_mul_tested_cellAverage
lemma covariateKernel_mul_tested_cellAverage {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (q : ℕ) (v : ℝ → E) (f : E) (x z : ℝ) :
    covariateKernel q x z * inner ℝ (cellAverage q v z) f =
      covariateKernel q x z * inner ℝ (cellAverage q v x) f := by
  by_cases h : cell q x = cell q z
  · rw [cellAverage_eq_of_cell_eq q v x z h]
  · simp [covariateKernel, h]

/-- The first singleton equals the first tested vector projection in (10). -/
-- @node: third_score_singleton1
lemma third_score_singleton1 (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) (f : Hj J) (o1 : Omega) :
    (∫ o2, ∫ o3, Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
      inner ℝ (Vres train mx my J a o3) f ∂P.law ∂P.law) =
    Rres train mx a o1 * cellAverage q (uerr P train mx a) (X o1) *
      inner ℝ (cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o1)) f := by
  simp_rw [third_score_pair12]
  have he (o2 : Omega) :
      Rres train mx a o1 * covariateKernel q (X o1) (X o2) * Rres train mx a o2 *
        inner ℝ (cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o2)) f =
      Rres train mx a o1 * (Rres train mx a o2 * covariateKernel q (X o2) (X o1)) *
        inner ℝ (cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o1)) f := by
    calc
      _ = Rres train mx a o1 * Rres train mx a o2 *
          (covariateKernel q (X o1) (X o2) * inner ℝ
            (cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o2)) f) := by ring
      _ = _ := by
        rw [covariateKernel_mul_tested_cellAverage, covariateKernel_symm q (X o1) (X o2)]
        ring
  simp_rw [he]
  rw [integral_mul_const, integral_const_mul, integral_Rres_covariateKernel P hModel]

/-- The middle singleton equals the second tested vector projection in (10). -/
-- @node: third_score_singleton2
lemma third_score_singleton2 (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) (f : Hj J) (o2 : Omega) :
    (∫ o1, ∫ o3, Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
      inner ℝ (Vres train mx my J a o3) f ∂P.law ∂P.law) =
    Rres train mx a o2 * cellAverage q (uerr P train mx a) (X o2) *
      inner ℝ (cellAverage q (fun z => coefficients J (verr P train mx my a z)) (X o2)) f := by
  simp_rw [third_score_pair12, integral_mul_const, integral_Rres_covariateKernel P hModel]
  ring

/-- The outcome singleton equals the squared treatment-cell mean projection in (10). -/
-- @node: third_score_singleton3
lemma third_score_singleton3 (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (a : Bool) (f : Hj J) (o3 : Omega) :
    (∫ o1, ∫ o2, Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
      Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
      inner ℝ (Vres train mx my J a o3) f ∂P.law ∂P.law) =
    (cellAverage q (uerr P train mx a) (X o3)) ^ 2 * inner ℝ (Vres train mx my J a o3) f := by
  simp_rw [third_score_pair13 P hModel]
  have he (o1 : Omega) :
      Rres train mx a o1 * covariateKernel q (X o1) (X o3) *
        cellAverage q (uerr P train mx a) (X o1) =
      (Rres train mx a o1 * covariateKernel q (X o1) (X o3)) *
        cellAverage q (uerr P train mx a) (X o3) := by
    by_cases h : cell q (X o1) = cell q (X o3)
    · rw [cellAverage_eq_of_cell_eq q _ (X o1) (X o3) h]
    · simp [covariateKernel, h]
  simp_rw [he]
  rw [integral_mul_const, integral_mul_const, integral_Rres_covariateKernel P hModel]
  ring

/-- The sampled third-order coefficient obeys (15), including m = 1. -/
-- @node: variance_inner_Uthree_le
lemma variance_inner_Uthree_le (P : ObsLaw) (hModel : Model P) {m : ℕ} (hm : 1 ≤ m)
    (train : Fin m → Omega) (mx my J q : ℕ) (hJ : 0 < J) (hq : 0 < q) (hqm : q ≤ m)
    (b : Fin 2) (a : Bool) (f : Hj J) :
    variance (fun eval => inner ℝ (Uthree train mx my J q eval b a) f) (evalLaw P m) ≤
      (2 : ℝ) ^ 20 * (m : ℝ)⁻¹ * ‖f‖ ^ 2 := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  let h : (Fin 3 → Omega) → ℝ := fun o =>
    Rres train mx a (o 0) * covariateKernel q (X (o 0)) (X (o 1)) *
      Rres train mx a (o 1) * covariateKernel q (X (o 1)) (X (o 2)) *
      inner ℝ (Vres train mx my J a (o 2)) f
  have hh : Measurable h := by dsimp [h]; unfold X; fun_prop
  have hf : (Set.range h).Finite := finite_range_third_role_kernel train mx my J q a f
  have hL2 : MemLp h 2 (Measure.pi (fun _ : Fin 3 => P.law)) := by
    obtain ⟨C, hC⟩ := hf.isBounded.exists_norm_le
    exact MemLp.of_bound hh.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun o => hC _ ⟨o, rfl⟩))
  have hp (S : Finset (Fin 3)) (o : Fin 3 → Omega) :=
    partial_role_three_iterated P.law h hh hf S o
  have hi (S : Finset (Fin 3)) :=
    (partial_role_kernel_memLp P.law 3 S h hL2).integrable_sq
  rw [variance_inner_Uthree_eq_roleAverage]
  apply three_role_variance_le_of_projection_moments P.law m q hm hqm h hh hL2
    (‖f‖ ^ 2) (sq_nonneg _)
  · rw [integral_three_roles_eq_iterated P.law _ (hi {0})]
    simp_rw [hp]
    simp only [h, Finset.mem_singleton, Fin.reduceEq,
      if_true, if_false, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    simp_rw [third_score_singleton1 P hModel]
    simpa using observed_third_treatment_singleton_moment_le P hModel train mx my J q hJ hq a f
  · rw [integral_three_roles_eq_iterated P.law _ (hi {1})]
    simp_rw [hp]
    simp only [h, Finset.mem_singleton, Fin.reduceEq, if_true, if_false,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    simp_rw [third_score_singleton2 P hModel]
    simpa using observed_third_treatment_singleton_moment_le P hModel train mx my J q hJ hq a f
  · rw [integral_three_roles_eq_iterated P.law _ (hi {2})]
    simp_rw [hp]
    simp only [h, Finset.mem_singleton, Fin.reduceEq, if_true, if_false,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    simp_rw [third_score_singleton3 P hModel]
    simpa only [real_inner_smul_left, integral_const, probReal_univ,
      smul_eq_mul, one_mul] using
      observed_third_outcome_singleton_moment_le P hModel train mx my J q hJ hq a f
  · rw [integral_three_roles_eq_iterated P.law _ (hi {0, 1})]
    simp_rw [hp]
    simp only [h, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq,
      or_true, true_or, or_self, if_true, if_false,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ]
    simp_rw [third_score_pair12]
    simpa using observed_third_treatment_pair_moment_le P hModel train mx my J q hJ hq a f
  · rw [integral_three_roles_eq_iterated P.law _ (hi {0, 2})]
    simp_rw [hp]
    simp only [h, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq,
      or_true, true_or, or_self, if_true, if_false,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    simp_rw [third_score_pair13 P hModel]
    simpa using observed_third_outcome_pair_moment_le P hModel train mx my J q hJ hq a f
  · rw [integral_three_roles_eq_iterated P.law _ (hi {1, 2})]
    simp_rw [hp]
    simp only [h, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq,
      or_true, true_or, or_self, if_true, if_false,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    simp_rw [third_score_pair23 P hModel]
    simpa using observed_third_outcome_pair_moment_le P hModel train mx my J q hJ hq a f
  · simpa only [show ({0, 1, 2} : Finset (Fin 3)) = Finset.univ by decide,
      partial_role_univ, h] using
      third_role_kernel_second_moment_le P hModel train mx my J q hJ hq a f

end CausalSmith.Stat.DensityEffectRoughNull
