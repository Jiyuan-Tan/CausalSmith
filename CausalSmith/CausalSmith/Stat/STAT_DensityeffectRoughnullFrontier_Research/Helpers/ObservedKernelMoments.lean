module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ObservedSecondMoments

/-! Observed-law full-overlap moments for the multiband covariance proof.
The conditional residual estimate is applied before integrating the kernel rows,
so the bounds retain the exact rank weights even above the sample size. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Squaring the clipped treatment residual costs at most nine pointwise. -/
-- @node: Rres_sq_le_nine
lemma Rres_sq_le_nine {m : ℕ} (train : Fin m → Omega) (mx : ℕ)
    (a : Bool) (o : Omega) : (Rres train mx a o) ^ 2 ≤ 9 := by
  have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)).2
    (Rres_abs_le train mx a o)
  simpa only [sq_abs, show (3 : ℝ) ^ 2 = 9 by norm_num] using h

/-- Every measurable covariate test integrates against the known uniform design. -/
-- @node: integral_observed_design_test
lemma integral_observed_design_test (P : ObsLaw) (hModel : Model P)
    (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ o, g (X o) ∂P.law) = ∫ x, g x ∂unitVolume := by
  rw [← integral_map (show Measurable X from measurable_fst).aemeasurable
    hg.aestronglyMeasurable, hModel.design]

/-- A treatment residual times a finite-range design score has the squared envelope
used for singleton and full-overlap projections. -/
-- @node: integral_Rres_design_sq_le
lemma integral_Rres_design_sq_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx : ℕ) (a : Bool) (g : ℝ → ℝ)
    (hg : Measurable g) (hgf : (Set.range g).Finite) :
    (∫ o, (Rres train mx a o * g (X o)) ^ 2 ∂P.law) ≤
      9 * ∫ x, (g x) ^ 2 ∂unitVolume := by
  calc
    _ ≤ ∫ o, 9 * (g (X o)) ^ 2 ∂P.law := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
      · exact (integrable_of_measurable_finite_range P.law _
          (by unfold X; fun_prop)
          (chain_finite_range_comp (chain_finite_range_precomp hgf X)
            (fun r => r ^ 2))).const_mul 9
      · filter_upwards [] with o
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (Rres_sq_le_nine train mx a o) (sq_nonneg _)
    _ = _ := by
      rw [integral_const_mul,
        integral_observed_design_test P hModel (fun x => (g x) ^ 2) (by fun_prop)]

/-- The squared kernel row has mass equal to its rank under the actual observed law. -/
-- @node: integral_observed_covariateKernel_sq
lemma integral_observed_covariateKernel_sq (P : ObsLaw) (hModel : Model P)
    (q : ℕ) (hq : 0 < q) (x : ℝ) :
    (∫ o, (covariateKernel q x (X o)) ^ 2 ∂P.law) = q := by
  rw [integral_observed_design_test P hModel (fun z => (covariateKernel q x z) ^ 2) (by fun_prop),
    integral_covariateKernel_sq q hq]

/-- An outcome residual tested by a single kernel row costs 4096 times its rank. -/
-- @node: observed_kernel_outcome_row_moment_le
lemma observed_kernel_outcome_row_moment_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (hJ : 0 < J) (hq : 0 < q)
    (a : Bool) (f : Hj J) (x : ℝ) :
    (∫ o, (covariateKernel q x (X o) *
      inner ℝ (Vres train mx my J a o) f) ^ 2 ∂P.law) ≤
      4096 * q * ‖f‖ ^ 2 := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  have h := integral_observed_inner_Vres_test_sq_le P hModel train mx my J hJ a
    (fun z => covariateKernel q x z • f) (by fun_prop)
    (chain_finite_range_comp
      (chain_finite_range_precomp (finite_range_covariateKernel q) (fun z => (x, z)))
      (fun r => r • f))
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  rw [integral_mul_const, integral_covariateKernel_sq q hq] at h
  simpa only [mul_pow, mul_assoc] using h

/-- A multiband outcome row has only the rank-weighted band energy, with no factor T. -/
-- @node: observed_multiband_outcome_row_moment_le
lemma observed_multiband_outcome_row_moment_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t) (a : Bool)
    (f : Hj (2 ^ T * L)) (x : ℝ) :
    (∫ o, (inner ℝ (Vres train mx my (2 ^ T * L) a o)
      (∑ t ∈ Finset.range (T + 1),
        covariateKernel (kt t) x (X o) • Qband L (2 ^ T * L) t f)) ^ 2 ∂P.law) ≤
      4096 * ∑ t ∈ Finset.range (T + 1),
        (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
  let : MeasurableSpace (Hj (2 ^ T * L)) := borel _
  let : BorelSpace (Hj (2 ^ T * L)) := ⟨rfl⟩
  have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
  have hJ : 0 < 2 ^ T * L := by positivity
  have h := integral_observed_inner_Vres_test_sq_le P hModel train mx my _ hJ a
    (fun z => ∑ t ∈ Finset.range (T + 1),
      covariateKernel (kt t) x z • Qband L (2 ^ T * L) t f) (by fun_prop)
    (chain_finite_range_sum _ _ (fun t _ => chain_finite_range_comp
      (chain_finite_range_precomp (finite_range_covariateKernel (kt t)) (fun z => (x, z)))
      (fun r => r • Qband L (2 ^ T * L) t f)))
  have he (z : ℝ) :
      ‖∑ t ∈ Finset.range (T + 1),
        covariateKernel (kt t) x z • Qband L (2 ^ T * L) t f‖ ^ 2 =
      ∑ t ∈ Finset.range (T + 1), (covariateKernel (kt t) x z) ^ 2 *
        ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
    simp_rw [← Qband_smul]
    rw [band_remainder_sum_norm_sq L T hL _
      (fun t ht => by have := Finset.mem_range.mp ht; omega)]
    simp only [Qband_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [he] at h
  rw [integral_finsetSum _ (fun t _ =>
    (integrable_covariateKernel_sq (kt t) x).mul_const _)] at h
  simp_rw [integral_mul_const] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [integral_covariateKernel_sq (kt t)
    (hkt t (by have := Finset.mem_range.mp ht; omega))]

/-- The actual independent two-role kernel satisfies the full-overlap bound (7).
The treatment square is bounded first and the band row is then integrated exactly. -/
-- @node: observed_multiband_full_overlap_moment_le
lemma observed_multiband_full_overlap_moment_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t) (a : Bool)
    (f : Hj (2 ^ T * L)) :
    (∫ o1, ∫ o2, (Rres train mx a o1 *
      inner ℝ (Vres train mx my (2 ^ T * L) a o2)
        (∑ t ∈ Finset.range (T + 1),
          covariateKernel (kt t) (X o1) (X o2) • Qband L (2 ^ T * L) t f)) ^ 2
      ∂P.law ∂P.law) ≤
      36864 * ∑ t ∈ Finset.range (T + 1),
        (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
  have hb (o1 : Omega) :
      (∫ o2, (Rres train mx a o1 *
        inner ℝ (Vres train mx my (2 ^ T * L) a o2)
          (∑ t ∈ Finset.range (T + 1),
            covariateKernel (kt t) (X o1) (X o2) • Qband L (2 ^ T * L) t f)) ^ 2
        ∂P.law) ≤
      36864 * ∑ t ∈ Finset.range (T + 1),
        (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    calc
      _ ≤ (Rres train mx a o1) ^ 2 * (4096 * ∑ t ∈ Finset.range (T + 1),
          (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (observed_multiband_outcome_row_moment_le P hModel train mx my L T hL
            kt hkt a f (X o1)) (sq_nonneg _)
      _ ≤ 9 * (4096 * ∑ t ∈ Finset.range (T + 1),
          (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (Rres_sq_le_nine train mx a o1) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ _ : Omega, 36864 * ∑ t ∈ Finset.range (T + 1),
        (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 ∂P.law := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      · exact integrable_const _
      · exact Filter.Eventually.of_forall hb
    _ = _ := by simp

/-- Both outcome-containing pair projections in (12) obey the actual-law 147456q budget. -/
-- @node: observed_third_outcome_pair_moment_le
lemma observed_third_outcome_pair_moment_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (hJ : 0 < J) (hq : 0 < q)
    (a : Bool) (f : Hj J) :
    (∫ o1, ∫ o3, (Rres train mx a o1 * covariateKernel q (X o1) (X o3) *
      cellAverage q (uerr P train mx a) (X o1) *
      inner ℝ (Vres train mx my J a o3) f) ^ 2 ∂P.law ∂P.law) ≤
      147456 * q * ‖f‖ ^ 2 := by
  have hu : ∀ᵐ x ∂unitVolume, |uerr P train mx a x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact uerr_abs_le P hModel train mx a x hx
  have hbar (x : ℝ) : (cellAverage q (uerr P train mx a) x) ^ 2 ≤ 4 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2
      (cellAverage_abs_le q hq _ 2 hu x)
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
  have hb (o1 : Omega) :
      (∫ o3, (Rres train mx a o1 * covariateKernel q (X o1) (X o3) *
        cellAverage q (uerr P train mx a) (X o1) *
        inner ℝ (Vres train mx my J a o3) f) ^ 2 ∂P.law) ≤
      147456 * q * ‖f‖ ^ 2 := by
    have he (o3 : Omega) :
        (Rres train mx a o1 * covariateKernel q (X o1) (X o3) *
          cellAverage q (uerr P train mx a) (X o1) *
          inner ℝ (Vres train mx my J a o3) f) ^ 2 =
        ((Rres train mx a o1) ^ 2 *
          (cellAverage q (uerr P train mx a) (X o1)) ^ 2) *
        (covariateKernel q (X o1) (X o3) *
          inner ℝ (Vres train mx my J a o3) f) ^ 2 := by ring
    simp_rw [he]
    rw [integral_const_mul]
    have hc : (Rres train mx a o1) ^ 2 *
        (cellAverage q (uerr P train mx a) (X o1)) ^ 2 ≤ 36 := by
      have h := mul_le_mul (Rres_sq_le_nine train mx a o1) (hbar (X o1))
        (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
      norm_num at h
      exact h
    calc
      _ ≤ ((Rres train mx a o1) ^ 2 *
          (cellAverage q (uerr P train mx a) (X o1)) ^ 2) *
          (4096 * q * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_left
        (observed_kernel_outcome_row_moment_le P hModel train mx my J q hJ hq a f
          (X o1)) (by positivity)
      _ ≤ 36 * (4096 * q * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ _ : Omega, 147456 * q * ‖f‖ ^ 2 ∂P.law := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      · exact integrable_const _
      · exact Filter.Eventually.of_forall hb
    _ = _ := by simp

/-- The full observable triple kernel has the q-squared budget (14), obtained by
integrating the outcome row and then the remaining design row. -/
-- @node: observed_third_full_overlap_moment_le
lemma observed_third_full_overlap_moment_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (hJ : 0 < J) (hq : 0 < q)
    (a : Bool) (f : Hj J) :
    (∫ o1, ∫ o2, ∫ o3,
      (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
        Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
        inner ℝ (Vres train mx my J a o3) f) ^ 2 ∂P.law ∂P.law ∂P.law) ≤
      331776 * (q : ℝ) ^ 2 * ‖f‖ ^ 2 := by
  have hb (o1 o2 : Omega) :
      (∫ o3,
        (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
          Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
          inner ℝ (Vres train mx my J a o3) f) ^ 2 ∂P.law) ≤
      (331776 * q * ‖f‖ ^ 2) * (covariateKernel q (X o1) (X o2)) ^ 2 := by
    have he (o3 : Omega) :
        (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
          Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
          inner ℝ (Vres train mx my J a o3) f) ^ 2 =
        ((Rres train mx a o1) ^ 2 * (Rres train mx a o2) ^ 2 *
          (covariateKernel q (X o1) (X o2)) ^ 2) *
        (covariateKernel q (X o2) (X o3) *
          inner ℝ (Vres train mx my J a o3) f) ^ 2 := by ring
    simp_rw [he]
    rw [integral_const_mul]
    have hc : (Rres train mx a o1) ^ 2 * (Rres train mx a o2) ^ 2 ≤ 81 := by
      have h := mul_le_mul (Rres_sq_le_nine train mx a o1)
        (Rres_sq_le_nine train mx a o2) (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
      norm_num at h
      exact h
    calc
      _ ≤ ((Rres train mx a o1) ^ 2 * (Rres train mx a o2) ^ 2 *
          (covariateKernel q (X o1) (X o2)) ^ 2) * (4096 * q * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (observed_kernel_outcome_row_moment_le P hModel train mx my J q hJ hq a f
            (X o2)) (by positivity)
      _ ≤ (81 * (covariateKernel q (X o1) (X o2)) ^ 2) *
          (4096 * q * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (by positivity)
      _ = _ := by ring
  have hinner (o1 : Omega) :
      (∫ o2, ∫ o3,
        (Rres train mx a o1 * covariateKernel q (X o1) (X o2) *
          Rres train mx a o2 * covariateKernel q (X o2) (X o3) *
          inner ℝ (Vres train mx my J a o3) f) ^ 2 ∂P.law ∂P.law) ≤
      331776 * (q : ℝ) ^ 2 * ‖f‖ ^ 2 := by
    calc
      _ ≤ ∫ o2, (331776 * q * ‖f‖ ^ 2) *
          (covariateKernel q (X o1) (X o2)) ^ 2 ∂P.law := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))
        · exact (integrable_of_measurable_finite_range P.law _ (by unfold X; fun_prop)
            (chain_finite_range_comp
              (chain_finite_range_precomp (finite_range_covariateKernel q)
                (fun o => (X o1, X o))) (fun r => r ^ 2))).const_mul _
        · exact Filter.Eventually.of_forall (hb o1)
      _ = _ := by
        rw [integral_const_mul, integral_observed_covariateKernel_sq P hModel q hq]
        ring
  calc
    _ ≤ ∫ _ : Omega, 331776 * (q : ℝ) ^ 2 * ‖f‖ ^ 2 ∂P.law := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ =>
          integral_nonneg (fun _ => sq_nonneg _)))
      · exact integrable_const _
      · exact Filter.Eventually.of_forall hinner
    _ = _ := by simp

/-- Two canonical roles integrate in their natural order under the product law. -/
-- @node: integral_two_roles_eq_iterated
lemma integral_two_roles_eq_iterated {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (g : (Fin 2 → E) → ℝ)
    (hg : Integrable g (Measure.pi (fun _ : Fin 2 => μ))) :
    (∫ o, g o ∂Measure.pi (fun _ : Fin 2 => μ)) =
      ∫ x, ∫ y, g ![x, y] ∂μ ∂μ := by
  let e2 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => E) 0
  have he2 := (measurePreserving_piFinSuccAbove (fun _ : Fin 2 => μ) 0).symm
  have hg2 : Integrable (g ∘ e2.symm) (μ.prod (Measure.pi (fun _ : Fin 1 => μ))) :=
    (he2.integrable_comp_emb e2.symm.measurableEmbedding).2 hg
  rw [← he2.integral_comp e2.symm.measurableEmbedding]
  change Integrable (fun z => g (e2.symm z))
    (μ.prod (Measure.pi (fun _ : Fin 1 => μ))) at hg2
  rw [integral_prod _ hg2]
  apply integral_congr_ae
  filter_upwards [] with x
  let e1 := MeasurableEquiv.piUnique (fun _ : Fin 1 => E)
  have he1 := (measurePreserving_piUnique (fun _ : Fin 1 => μ)).symm
  rw [← he1.integral_comp e1.symm.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Three canonical roles integrate in their natural order under the product law. -/
-- @node: integral_three_roles_eq_iterated
lemma integral_three_roles_eq_iterated {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (g : (Fin 3 → E) → ℝ)
    (hg : Integrable g (Measure.pi (fun _ : Fin 3 => μ))) :
    (∫ o, g o ∂Measure.pi (fun _ : Fin 3 => μ)) =
      ∫ x, ∫ y, ∫ z, g ![x, y, z] ∂μ ∂μ ∂μ := by
  let e3 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => E) 0
  have he3 := (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0).symm
  have hg3 : Integrable (g ∘ e3.symm) (μ.prod (Measure.pi (fun _ : Fin 2 => μ))) :=
    (he3.integrable_comp_emb e3.symm.measurableEmbedding).2 hg
  rw [← he3.integral_comp e3.symm.measurableEmbedding]
  change Integrable (fun z => g (e3.symm z))
    (μ.prod (Measure.pi (fun _ : Fin 2 => μ))) at hg3
  rw [integral_prod _ hg3]
  apply integral_congr_ae
  filter_upwards [hg3.prod_right_ae] with x hgx
  rw [integral_two_roles_eq_iterated μ _ hgx]
  apply integral_congr_ae
  filter_upwards [] with y
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The actual multiband scalar role kernel has finite range for fixed training. -/
-- @node: finite_range_multiband_role_kernel
lemma finite_range_multiband_role_kernel {m : ℕ} (train : Fin m → Omega)
    (mx my L T J : ℕ) (kt : ℕ → ℕ) (a : Bool) (f : Hj J) :
    (Set.range (fun o : Fin 2 → Omega => Rres train mx a (o 0) *
      inner ℝ (Vres train mx my J a (o 1))
        (∑ t ∈ Finset.range (T + 1),
          covariateKernel (kt t) (X (o 0)) (X (o 1)) • Qband L J t f))).Finite := by
  apply chain_finite_range_binary (op := (· * ·))
    (chain_finite_range_precomp (finite_range_Rres train mx a)
      (fun o : Fin 2 → Omega => o 0))
  apply chain_finite_range_binary (op := fun v w => inner ℝ v w)
    (chain_finite_range_precomp (finite_range_Vres train mx my J a)
      (fun o : Fin 2 → Omega => o 1))
  apply chain_finite_range_sum
  intro t _
  exact chain_finite_range_comp
    (chain_finite_range_precomp (finite_range_covariateKernel (kt t))
      (fun o : Fin 2 → Omega => (X (o 0), X (o 1)))) (fun r => r • Qband L J t f)

/-- The actual triple scalar role kernel has finite range for fixed training. -/
-- @node: finite_range_third_role_kernel
lemma finite_range_third_role_kernel {m : ℕ} (train : Fin m → Omega)
    (mx my J q : ℕ) (a : Bool) (f : Hj J) :
    (Set.range (fun o : Fin 3 → Omega =>
      Rres train mx a (o 0) * covariateKernel q (X (o 0)) (X (o 1)) *
      Rres train mx a (o 1) * covariateKernel q (X (o 1)) (X (o 2)) *
      inner ℝ (Vres train mx my J a (o 2)) f)).Finite := by
  apply chain_finite_range_binary (op := (· * ·))
  · apply chain_finite_range_binary (op := (· * ·))
    · apply chain_finite_range_binary (op := (· * ·))
      · apply chain_finite_range_binary (op := (· * ·))
        · exact chain_finite_range_precomp (finite_range_Rres train mx a)
            (fun o : Fin 3 → Omega => o 0)
        · exact chain_finite_range_precomp (finite_range_covariateKernel q)
            (fun o : Fin 3 → Omega => (X (o 0), X (o 1)))
      · exact chain_finite_range_precomp (finite_range_Rres train mx a)
          (fun o : Fin 3 → Omega => o 1)
    · exact chain_finite_range_precomp (finite_range_covariateKernel q)
        (fun o : Fin 3 → Omega => (X (o 1), X (o 2)))
  · exact chain_finite_range_comp
      (chain_finite_range_precomp (finite_range_Vres train mx my J a)
        (fun o : Fin 3 → Omega => o 2))
      (fun v => inner ℝ v f)

/-- Bound (7) is available directly on the canonical two-role product used by the
exact overlap identity, rather than only as an iterated integral. -/
-- @node: multiband_role_kernel_second_moment_le
lemma multiband_role_kernel_second_moment_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t) (a : Bool)
    (f : Hj (2 ^ T * L)) :
    (∫ o : Fin 2 → Omega, (Rres train mx a (o 0) *
      inner ℝ (Vres train mx my (2 ^ T * L) a (o 1))
        (∑ t ∈ Finset.range (T + 1),
          covariateKernel (kt t) (X (o 0)) (X (o 1)) •
            Qband L (2 ^ T * L) t f)) ^ 2 ∂Measure.pi (fun _ => P.law)) ≤
      36864 * ∑ t ∈ Finset.range (T + 1),
        (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
  let : MeasurableSpace (Hj (2 ^ T * L)) := borel _
  let : BorelSpace (Hj (2 ^ T * L)) := ⟨rfl⟩
  rw [integral_two_roles_eq_iterated P.law _
    (integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
      (chain_finite_range_comp
        (finite_range_multiband_role_kernel train mx my L T (2 ^ T * L) kt a f)
        (fun r => r ^ 2)))]
  exact observed_multiband_full_overlap_moment_le P hModel train mx my L T hL kt hkt a f

/-- Bound (14) is available directly on the canonical three-role product used by
all seven terms of the exact overlap identity. -/
-- @node: third_role_kernel_second_moment_le
lemma third_role_kernel_second_moment_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (hJ : 0 < J) (hq : 0 < q)
    (a : Bool) (f : Hj J) :
    (∫ o : Fin 3 → Omega,
      (Rres train mx a (o 0) * covariateKernel q (X (o 0)) (X (o 1)) *
        Rres train mx a (o 1) * covariateKernel q (X (o 1)) (X (o 2)) *
        inner ℝ (Vres train mx my J a (o 2)) f) ^ 2
      ∂Measure.pi (fun _ => P.law)) ≤ 331776 * (q : ℝ) ^ 2 * ‖f‖ ^ 2 := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  rw [integral_three_roles_eq_iterated P.law _
    (integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
      (chain_finite_range_comp (finite_range_third_role_kernel train mx my J q a f)
        (fun r => r ^ 2)))]
  exact observed_third_full_overlap_moment_le P hModel train mx my J q hJ hq a f

end CausalSmith.Stat.DensityEffectRoughNull
