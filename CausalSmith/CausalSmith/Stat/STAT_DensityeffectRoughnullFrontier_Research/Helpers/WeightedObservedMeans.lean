module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.KernelDesignMeans
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.MeanRemainderAssembly
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ObservedDesignMeans

/-! Covariate-tested observed outcome means for the pair and triple role calculations
in equation (21). Histogram test functions have finite range, so their integrability
requires no additional assumptions on the law or on training. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Testing an inverse-weighted outcome coordinate transports its conditional bin mean. -/
-- @node: integral_observed_tested_phi_coordinate
lemma integral_observed_tested_phi_coordinate (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx J : ℕ) (a : Bool) (i : Fin J) (c : ℝ → ℝ) (hc : Measurable c) :
    (∫ o in {o | A o = a},
      (pilotPi train mx a (X o))⁻¹ * c (X o) * phiCoefficients J (Y o) i ∂P.law) =
      ∫ x, c x * (1 + uerr P train mx a x) * coefficients J (P.eta a x) i ∂unitVolume := by
  let D : Set ℝ := {y | cell J y = i.val + 1}
  have hD : MeasurableSet D :=
    (measurable_histogram_cell J) (measurableSet_singleton _)
  have hY : Measurable Y := measurable_snd.comp measurable_snd
  have heq : (fun o : Omega => (pilotPi train mx a (X o))⁻¹ * c (X o) *
      phiCoefficients J (Y o) i) =
      (Y ⁻¹' D).indicator (fun o => (pilotPi train mx a (X o))⁻¹ * (Real.sqrt J * c (X o))) := by
    funext o
    by_cases hy : Y o ∈ D <;> simp [phiCoefficients, D, Set.indicator, hy] at * <;> ring
  rw [heq, integral_indicator (hD.preimage hY)]
  have hset : Y ⁻¹' D ∩ {o : Omega | A o = a} = {o | A o = a ∧ Y o ∈ D} := by
    ext o
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    exact and_comm
  rw [Measure.restrict_restrict (hD.preimage hY), hset]
  rw [show (∫ o in {o | A o = a ∧ Y o ∈ D},
      (pilotPi train mx a (X o))⁻¹ * (Real.sqrt J * c (X o)) ∂P.law) =
      ∫ x, ((1 + uerr P train mx a x) *
        ∫ y in D, P.eta a x y ∂unitVolume) * (Real.sqrt J * c x) ∂unitVolume from
    integral_observed_weighted_outcome_bin P train mx a D hD
      (fun x => Real.sqrt J * c x) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hbin : (∫ y in D, P.eta a x y ∂unitVolume) =
      ∫ y in histogramCell J (i.val + 1), P.eta a x y ∂unitVolume := by
    apply setIntegral_congr_set
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    apply propext
    change (cell J y = i.val + 1) ↔ (y ∈ Set.Icc 0 1 ∧ cell J y = i.val + 1)
    simp only [hy, true_and]
  rw [hbin]
  change _ = c x * (1 + uerr P train mx a x) *
    (Real.sqrt J * ∫ y in histogramCell J (i.val + 1), P.eta a x y ∂unitVolume)
  ring


/-- A measurable finite-range scalar test preserves vector integrability. -/
-- @node: integrable_finite_range_test_smul
lemma integrable_finite_range_test_smul {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (c : α → ℝ) (hc : Measurable c) (hcf : (Set.range c).Finite)
    (f : α → E) (hf : Integrable f μ) : Integrable (fun x => c x • f x) μ := by
  obtain ⟨C, hC⟩ := hcf.isBounded.exists_norm_le
  exact hf.bdd_smul C hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => hC (c x) ⟨x, rfl⟩))

/-- A finite-range covariate test transports the entire weighted outcome vector. -/
-- @node: integral_observed_tested_phi_vector
lemma integral_observed_tested_phi_vector (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx J : ℕ) (a : Bool)
    (c : ℝ → ℝ) (hc : Measurable c) (hcf : (Set.range c).Finite) :
    (∫ o in {o | A o = a},
      (c (X o) * (pilotPi train mx a (X o))⁻¹) • phiCoefficients J (Y o) ∂P.law) =
      ∫ x, (c x * (1 + uerr P train mx a x)) • coefficients J (P.eta a x)
        ∂unitVolume := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  have hi0 : Integrable (fun o : Omega =>
      (pilotPi train mx a (X o))⁻¹ • phiCoefficients J (Y o)) P.law := by
    apply integrable_of_measurable_finite_range _ _ (by unfold X Y; fun_prop)
    exact chain_finite_range_binary
      (chain_finite_range_comp (chain_finite_range_precomp
        (finite_range_pilotPi train mx a) X) (g := fun r : ℝ => r⁻¹))
      (chain_finite_range_precomp (finite_range_phiCoefficients J) Y) (· • ·)
  have hi := integrable_finite_range_test_smul P.law (fun o => c (X o))
    (by unfold X; fun_prop) (chain_finite_range_precomp hcf X) _ hi0
  have hj := integrable_finite_range_test_smul unitVolume c hc hcf _
    (integrable_weighted_eta_coefficients_design P train mx J a)
  simp only [smul_smul] at hi hj
  ext i
  rw [eval_integral_piLp (fun j => hi.integrableOn.eval_piLp j),
    eval_integral_piLp (fun j => hj.eval_piLp j)]
  simpa only [PiLp.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    integral_observed_tested_phi_coordinate P train mx J a i c hc

/-- Testing the observable outcome residual gives the tested design density-error mean. -/
-- @node: integral_Vres_covariate_test
lemma integral_Vres_covariate_test (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my J : ℕ) (a : Bool)
    (c : ℝ → ℝ) (hc : Measurable c) (hcf : (Set.range c).Finite) :
    (∫ o, c (X o) • Vres train mx my J a o ∂P.law) =
      ∫ x, c x • coefficients J (verr P train mx my a x) ∂unitVolume := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let S : Set Omega := {o | A o = a}
  have hS : MeasurableSet S := by
    exact (measurableSet_singleton a).preimage (show Measurable A by unfold A; fun_prop)
  let f : Omega → Hj J := fun o =>
    (c (X o) * (pilotPi train mx a (X o))⁻¹) • phiCoefficients J (Y o)
  let g : ℝ → Hj J := fun x =>
    (c x * (pilotPi train mx a x)⁻¹) • pilotCoefficients train mx my J a x
  have hgf : (Set.range g).Finite :=
    chain_finite_range_binary
      (chain_finite_range_binary hcf
        (chain_finite_range_comp (finite_range_pilotPi train mx a)
          (g := fun r : ℝ => r⁻¹)) (· * ·))
      (finite_range_pilotCoefficients train mx my J a) (· • ·)
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hgi : Integrable (fun o => g (X o)) P.law :=
    integrable_of_measurable_finite_range _ _ (hgm.comp measurable_fst)
      (chain_finite_range_precomp hgf X)
  have hfi : Integrable f P.law := by
    apply integrable_of_measurable_finite_range _ _ (by dsimp [f]; unfold X Y; fun_prop)
    exact chain_finite_range_binary
      (chain_finite_range_binary (chain_finite_range_precomp hcf X)
        (chain_finite_range_comp (chain_finite_range_precomp
          (finite_range_pilotPi train mx a) X) (g := fun r : ℝ => r⁻¹)) (· * ·))
      (chain_finite_range_precomp (finite_range_phiCoefficients J) Y) (· • ·)
  have he : (fun o => c (X o) • Vres train mx my J a o) = S.indicator f -
      S.indicator (fun o => g (X o)) := by
    funext o
    by_cases ha : A o = a <;>
      simp [Vres, S, Set.indicator, ha, f, g, smul_sub, one_div, smul_smul, mul_comm]
  rw [he]
  change (∫ o, S.indicator f o - S.indicator (fun o => g (X o)) o ∂P.law) = _
  rw [integral_sub (hfi.indicator hS) (hgi.indicator hS),
    integral_indicator hS, integral_indicator hS,
    integral_observed_tested_phi_vector P train mx J a c hc hcf,
    integral_observed_arm_covariate P a g hgm]
  obtain ⟨C, hC⟩ := hgf.isBounded.exists_norm_le
  have hpi : Integrable (fun x => pi P a x • g x) unitVolume := by
    apply Integrable.of_bound (by fun_prop) C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have heRange := P.e_range x hx
    have hp : |pi P a x| ≤ 1 := by
      cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte] <;>
        exact abs_le.mpr ⟨by linarith [heRange.1, heRange.2], by linarith [heRange.1, heRange.2]⟩
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
      (by simpa using hC (g x) ⟨x, rfl⟩)
  have hj := integrable_finite_range_test_smul unitVolume c hc hcf _
    (integrable_weighted_eta_coefficients_design P train mx J a)
  simp only [smul_smul] at hj
  rw [← integral_sub hj hpi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hp : pilotPi train mx a x ≠ 0 := by
    linarith [(pilotPi_mem_Icc train mx a x).1]
  have hu : 1 + uerr P train mx a x = pi P a x * (pilotPi train mx a x)⁻¹ := by
    unfold uerr
    field_simp
    ring
  change _ = c x • coefficients J (fun y => (1 + uerr P train mx a x) *
    (P.eta a x y - densityPilot train mx my a x y))
  rw [coefficients_const_mul_sub J _ _ _ (P.eta_integrable a x hx)
    (densityPilot_integrable train mx my a x)]
  simp only [smul_sub, smul_smul]
  dsimp [g, pilotCoefficients]
  rw [hu]
  simp only [smul_smul, mul_comm, mul_left_comm, mul_assoc]


/-- Correction-cell averages have finite range even when the input does not. -/
lemma finite_range_cellAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (f : ℝ → E) : (Set.range (cellAverage k f)).Finite := by
  exact chain_finite_range_of_factors (finite_range_cell k)
    (fun x z h => cellAverage_eq_of_cell_eq k f x z h)

/-- The unprojected observable pair kernel is integrable by finite histogram range. -/
-- @node: integrable_second_role_kernel
lemma integrable_second_role_kernel (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my J k : ℕ) (a : Bool) :
    Integrable (fun o : Omega × Omega =>
      (Rres train mx a o.1 * covariateKernel k (X o.1) (X o.2)) •
        Vres train mx my J a o.2) (P.law.prod P.law) := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  apply integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
  apply chain_finite_range_binary (op := fun r v => r • v)
  · apply chain_finite_range_binary (op := (· * ·))
    · exact chain_finite_range_precomp (finite_range_Rres train mx a) Prod.fst
    · exact chain_finite_range_precomp (finite_range_covariateKernel k)
        (fun o : Omega × Omega => (X o.1, X o.2))
  · exact chain_finite_range_precomp (finite_range_Vres train mx my J a) Prod.snd

/-- Integrating the independent treatment role, then the tested outcome role, gives
one scalar correction-cell mean times the outcome-error coefficient vector. -/
-- @node: integral_observed_pair_kernel
lemma integral_observed_pair_kernel (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J k : ℕ) (a : Bool) :
    (∫ o : Omega × Omega,
      (Rres train mx a o.1 * covariateKernel k (X o.1) (X o.2)) •
        Vres train mx my J a o.2 ∂P.law.prod P.law) =
      ∫ x, cellAverage k (uerr P train mx a) x •
        coefficients J (verr P train mx my a x) ∂unitVolume := by
  rw [integral_prod_symm _ (integrable_second_role_kernel P train mx my J k a)]
  simp_rw [integral_smul_const, integral_Rres_covariateKernel P hModel train mx k a]
  exact integral_Vres_covariate_test P train mx my J a
    (cellAverage k (uerr P train mx a)) (by fun_prop) (finite_range_cellAverage k _)

/-- The projected observable pair kernel gives exactly the bandwise design mean in (21). -/
-- @node: integral_observed_projected_pair_kernel
lemma integral_observed_projected_pair_kernel (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my L J t k : ℕ) (hk : 0 < k) (a : Bool) :
    (∫ o : Omega × Omega, Qband L J t
      ((Rres train mx a o.1 * covariateKernel k (X o.1) (X o.2)) •
        Vres train mx my J a o.2) ∂P.law.prod P.law) =
      Qband L J t (∫ x, cellAverage k (uerr P train mx a) x •
        cellAverage k (fun z => coefficients J (verr P train mx my a z)) x
          ∂unitVolume) := by
  rw [← Qband_integral _ L J t _ (integrable_second_role_kernel P train mx my J k a),
    integral_observed_pair_kernel P hModel train mx my J k a]
  congr 1
  apply integral_cellwise_smul_eq_cellAverage k hk
  · exact fun x z h => cellAverage_eq_of_cell_eq k _ x z h
  · apply integrable_coefficients_design
    change Integrable (fun z : ℝ × ℝ => verr P train mx my a z.1 z.2) _
    simpa only [pow_zero, one_mul] using
      integrable_uerr_pow_mul_verr_joint P hModel train mx my a 0

/-- Every positive-size second-role average has its exact bandwise cell-product expectation. -/
-- @node: integral_Utwo_eq_design_mean
lemma integral_Utwo_eq_design_mean (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (hm : 0 < m) (train : Fin m → Omega) (mx my L T J : ℕ) (kt : ℕ → ℕ)
    (hkt : ∀ t, t ≤ T → 0 < kt t) (b : Fin 2) (a : Bool) :
    (∫ eval, Utwo train mx my L T J kt eval b a ∂evalLaw P m) =
      ∑ t ∈ Finset.range (T + 1), Qband L J t
        (∫ x, cellAverage (kt t) (uerr P train mx a) x •
          cellAverage (kt t) (fun z => coefficients J (verr P train mx my a z)) x
            ∂unitVolume) := by
  rw [integral_Utwo_eq_sum_product_integral P hm]
  apply Finset.sum_congr rfl
  intro t ht
  exact integral_observed_projected_pair_kernel P hModel train mx my L J t (kt t)
    (hkt t (by simp only [Finset.mem_range] at ht; omega)) a

/-- The same-cell design kernel is symmetric in its two covariate arguments. -/
-- @node: covariateKernel_symm
lemma covariateKernel_symm (k : ℕ) (x z : ℝ) :
    covariateKernel k x z = covariateKernel k z x := by
  simp only [covariateKernel, eq_comm]

/-- A finite-range covariate test in a treatment kernel transports to its tested cell mean. -/
-- @node: integral_tested_Rres_covariateKernel
lemma integral_tested_Rres_covariateKernel (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx k : ℕ) (a : Bool) (w : ℝ)
    (c : ℝ → ℝ) (hc : Measurable c) (hcf : (Set.range c).Finite) :
    (∫ o, c (X o) * Rres train mx a o * covariateKernel k (X o) w ∂P.law) =
      cellAverage k (fun x => c x * uerr P train mx a x) w := by
  obtain ⟨C, hC⟩ := hcf.isBounded.exists_norm_le
  have hCn : 0 ≤ C := (norm_nonneg (c 0)).trans (hC (c 0) ⟨0, rfl⟩)
  have hb : ∀ x, ‖c x * covariateKernel k x w‖ ≤ C * k := by
    intro x
    have hK : ‖covariateKernel k x w‖ ≤ (k : ℝ) := by
      unfold covariateKernel
      split_ifs <;> simp
    rw [norm_mul]
    exact mul_le_mul (hC (c x) ⟨x, rfl⟩) hK (norm_nonneg _) hCn
  have h := integral_Rres_covariate_test P hModel train mx a
    (fun x => c x * covariateKernel k x w) (by fun_prop) (C * k) hb
  simpa only [cellAverage, covariateKernel_symm k w, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- The two treatment roles in the triple kernel have an integrable scalar product. -/
-- @node: integrable_treatment_pair_kernel
lemma integrable_treatment_pair_kernel (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx k : ℕ) (a : Bool) (w : ℝ) :
    Integrable (fun o : Omega × Omega =>
      Rres train mx a o.1 * covariateKernel k (X o.1) (X o.2) *
        Rres train mx a o.2 * covariateKernel k (X o.2) w) (P.law.prod P.law) := by
  apply integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
  apply chain_finite_range_binary (op := (· * ·))
  · apply chain_finite_range_binary (op := (· * ·))
    · apply chain_finite_range_binary (op := (· * ·))
      · exact chain_finite_range_precomp (finite_range_Rres train mx a) Prod.fst
      · exact chain_finite_range_precomp (finite_range_covariateKernel k)
          (fun o : Omega × Omega => (X o.1, X o.2))
    · exact chain_finite_range_precomp (finite_range_Rres train mx a) Prod.snd
  · exact chain_finite_range_precomp (finite_range_covariateKernel k)
      (fun o : Omega × Omega => (X o.2, w))

/-- Two independent treatment roles in a common correction cell give the squared
relative-error cell mean, as required for the triple expectation in (21). -/
-- @node: integral_treatment_pair_kernel
lemma integral_treatment_pair_kernel (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx k : ℕ) (hk : 0 < k) (a : Bool) (w : ℝ) :
    (∫ o : Omega × Omega,
      Rres train mx a o.1 * covariateKernel k (X o.1) (X o.2) *
        Rres train mx a o.2 * covariateKernel k (X o.2) w ∂P.law.prod P.law) =
      (cellAverage k (uerr P train mx a) w) ^ 2 := by
  rw [integral_prod_symm _ (integrable_treatment_pair_kernel P train mx k a w)]
  simp_rw [integral_mul_const, integral_Rres_covariateKernel P hModel train mx k a]
  rw [integral_tested_Rres_covariateKernel P hModel train mx k a w
    (cellAverage k (uerr P train mx a)) (by fun_prop) (finite_range_cellAverage k _)]
  have h := cellAverage_cellwise_smul k hk (cellAverage k (uerr P train mx a))
    (uerr P train mx a) (fun x z hc => cellAverage_eq_of_cell_eq k _ x z hc) w
  simpa only [smul_eq_mul, pow_two] using h

/-- The observable independent triple kernel gives the squared scalar cell mean
multiplied by the outcome-error coefficient vector. -/
-- @node: integral_observed_triple_kernel
lemma integral_observed_triple_kernel (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (hq : 0 < q) (a : Bool) :
    (∫ o : (Omega × Omega) × Omega,
      (Rres train mx a o.1.1 * covariateKernel q (X o.1.1) (X o.1.2) *
        Rres train mx a o.1.2 * covariateKernel q (X o.1.2) (X o.2)) •
        Vres train mx my J a o.2 ∂(P.law.prod P.law).prod P.law) =
      ∫ x, (cellAverage q (uerr P train mx a) x) ^ 2 •
        cellAverage q (fun z => coefficients J (verr P train mx my a z)) x
          ∂unitVolume := by
  rw [integral_prod_symm _ (integrable_third_role_kernel P train mx my J q a)]
  simp_rw [integral_smul_const, integral_treatment_pair_kernel P hModel train mx q hq a]
  rw [integral_Vres_covariate_test P train mx my J a
    (fun x => (cellAverage q (uerr P train mx a) x) ^ 2) (by fun_prop)
    (chain_finite_range_comp (finite_range_cellAverage q _) (fun r : ℝ => r ^ 2))]
  apply integral_cellwise_smul_eq_cellAverage q hq
  · intro x z hc
    rw [cellAverage_eq_of_cell_eq q _ x z hc]
  · apply integrable_coefficients_design
    change Integrable (fun z : ℝ × ℝ => verr P train mx my a z.1 z.2) _
    simpa only [pow_zero, one_mul] using
      integrable_uerr_pow_mul_verr_joint P hModel train mx my a 0

/-- Every positive-size third-role average has the exact squared-cell-mean expectation (21). -/
-- @node: integral_Uthree_eq_design_mean
lemma integral_Uthree_eq_design_mean (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (hm : 0 < m) (train : Fin m → Omega) (mx my J q : ℕ) (hq : 0 < q)
    (b : Fin 2) (a : Bool) :
    (∫ eval, Uthree train mx my J q eval b a ∂evalLaw P m) =
      ∫ x, (cellAverage q (uerr P train mx a) x) ^ 2 •
        cellAverage q (fun z => coefficients J (verr P train mx my a z)) x
          ∂unitVolume := by
  rw [integral_Uthree_eq_triple_product_integral P hm]
  exact integral_observed_triple_kernel P hModel train mx my J q hq a

/-- The observed coefficient chain has exactly the three design expectations (21). -/
-- @node: contrastMean_design_role_identity
lemma contrastMean_design_role_identity (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (hm : 0 < m) (train : Fin m → Omega) (mx my L T J q : ℕ) (kt : ℕ → ℕ)
    (hq : 0 < q) (hkt : ∀ t, t ≤ T → 0 < kt t) :
    contrastMean P train mx my L T J q kt =
      ∑ a : Bool, (if a then (1 : ℝ) else -1) •
        ((∫ x, pilotCoefficients train mx my J a x ∂unitVolume) +
          (∫ x, coefficients J (verr P train mx my a x) ∂unitVolume) -
          (∑ t ∈ Finset.range (T + 1), Qband L J t
            (∫ x, cellAverage (kt t) (uerr P train mx a) x •
              cellAverage (kt t) (fun z => coefficients J (verr P train mx my a z)) x
                ∂unitVolume)) +
          (∫ x, (cellAverage q (uerr P train mx a) x) ^ 2 •
            cellAverage q (fun z => coefficients J (verr P train mx my a z)) x
              ∂unitVolume)) := by
  rw [contrastMean_role_decomposition]
  simp_rw [integral_Uone_eq_integral_verr_coefficients P hm train mx my J,
    integral_Utwo_eq_design_mean P hModel hm train mx my L T J kt hkt,
    integral_Uthree_eq_design_mean P hModel hm train mx my J q hq]

/-- Observed role transport followed by the exact polynomial and band cancellation
proves the identity half of the corrected-mean lemma for every trained realization. -/
-- @node: contrastMean_eq_meanRemainder
lemma contrastMean_eq_meanRemainder (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (hm : 0 < m) (train : Fin m → Omega) (mx my L T J q : ℕ) (kt : ℕ → ℕ)
    (hJ : J = 2 ^ T * L) (hq : 0 < q) (hkt : ∀ t, t ≤ T → 0 < kt t) :
    contrastMean P train mx my L T J q kt - coefficients J (delta P) =
      meanRemainder P train mx my L T J q kt := by
  subst J
  rw [contrastMean_design_role_identity P hModel hm train mx my L T (2 ^ T * L) q kt hq hkt]
  exact corrected_mean_projected_contrast_identity P hModel train mx my L T q kt hq hkt

end CausalSmith.Stat.DensityEffectRoughNull
