module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperExpectation
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TwoBlock

/-! Second-moment certificates for the actual treatment-only denominator. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- Independence makes the variance of a coordinate average the one-record variance
 divided by its block size. -/
-- @node: upper_coordinate_average_variance
lemma upper_coordinate_average_variance {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (S : Finset (Fin n))
    (hS : S.Nonempty) (f : Ω → ℝ) (hf : MemLp f 2 P) (c : ℝ) :
    variance (fun o : Fin n → Ω => c * ∑ i ∈ S, f (o i))
      (Measure.pi (fun _ => P)) = c^2 * S.card * variance f P := by
  classical
  have hm (i : Fin n) := measurePreserving_eval (fun _ : Fin n => P) i
  have hi (i : Fin n) := hf.comp_measurePreserving (hm i)
  have hs : variance (fun o : Fin n → Ω => ∑ i ∈ S, f (o i))
      (Measure.pi (fun _ => P)) = (S.card : ℝ) * variance f P := by
    have he := IndepFun.variance_sum (s := S) (fun i _ => hi i)
      (fun i _ j _ hij =>
        (iIndepFun_pi (μ := fun _ : Fin n => P)
          (X := fun _ => f) (fun _ => hf.aemeasurable)).indepFun hij)
    have hv (i : Fin n) : variance (f ∘ Function.eval i)
        (Measure.pi (fun _ => P)) = variance f P := by
      change variance (f ∘ fun o : Fin n → Ω => o i) _ = _
      rw [← variance_map ((hm i).map_eq.symm ▸ hf.aemeasurable) (hm i).measurable.aemeasurable, (hm i).map_eq]
    have hfun : (∑ i ∈ S, f ∘ Function.eval i) =
        (fun o : Fin n → Ω => ∑ i ∈ S, f (o i)) := by funext o; simp
    rw [hfun] at he
    simpa only [hv, Finset.sum_const, nsmul_eq_mul] using he
  rw [variance_const_mul, hs]
  ring

/-- A bounded window-supported statistic has squared energy at most its bound
 squared times the known window mass. -/
-- @node: upper_window_second_moment
lemma upper_window_second_moment (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (f : O → ℝ) (hf : MemLp f 2 law.P)
    (hb : ∀ o, |f o| ≤ h⁻¹ * (if X o ∈ window h then 1 else 0)) :
    (∫ o, (f o)^2 ∂law.P) ≤ h⁻¹ := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  let g : unitInterval → ℝ := (window h).indicator (fun _ => (h⁻¹)^2)
  have hg : Measurable g := measurable_const.indicator hw
  have hi : Integrable (fun o => g (X o)) law.P := by
    apply (MemLp.of_bound (hg.comp (by unfold X; fun_prop)).aestronglyMeasurable
      ((h⁻¹)^2) (Filter.Eventually.of_forall fun o => ?_) :
      MemLp (fun o => g (X o)) 2 law.P).integrable (by norm_num)
    by_cases hx : X o ∈ window h <;> simp [g, hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (h⁻¹))] <;> positivity
  calc
    _ ≤ ∫ o, g (X o) ∂law.P := by
      apply integral_mono hf.integrable_sq hi
      intro o
      have hb' := hb o
      by_cases hx : X o ∈ window h
      · simp only [hx, if_true, mul_one] at hb'
        simpa [g, hx, sq_abs] using (sq_le_sq₀ (abs_nonneg _) (inv_nonneg.mpr hh.1.le)).2 hb'
      · have hz : f o = 0 := abs_nonpos_iff.mp (by simpa [hx] using hb')
        simp [g, hx, hz]
    _ = ∫ x, g x ∂design := by
      rw [← hu]
      exact (integral_map (by unfold X; fun_prop) hg.aestronglyMeasurable).symm
    _ = h⁻¹ := by
      rw [integral_indicator hw]
      simp [integral_const, Measure.real, design_window h hh,
        ENNReal.toReal_ofReal hh.1.le]
      field_simp

/-- The two uncentered denominator projections retain the treatment mark and
 are both supported on the public window with absolute bound one over bandwidth. -/
-- @node: upper_denominator_projection_bounds
lemma upper_denominator_projection_bounds (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ) :
    let B := fun o z : O => h⁻¹ * (bit (A o)*bit (A z)*projKernel h J (X o) (X z))
    let F := fun o : O => h⁻¹ * (if X o ∈ window h then bit (A o) else 0)
    (∀ o, |∫ z, B o z ∂law.P| ≤ h⁻¹ * (if X o ∈ window h then 1 else 0)) ∧
    (∀ o, |F o - ∫ z, B z o ∂law.P| ≤ h⁻¹ * (if X o ∈ window h then 1 else 0)) := by
  dsimp only
  have hs (o : O) : (∫ z, h⁻¹ * (bit (A z)*bit (A o)*projKernel h J (X z) (X o)) ∂law.P) =
      h⁻¹ * bit (A o) * projOp h J law.e (X o) := by
    have he : (fun z : O => h⁻¹ * (bit (A z)*bit (A o)*projKernel h J (X z) (X o))) =
        (fun z => h⁻¹ * (bit (A o)*bit (A z)*projKernel h J (X o) (X z))) := by
      funext z
      rw [projKernel_symm h J (X z) (X o), mul_comm (bit (A z))]
    rw [he, upper_denominator_kernel_section law hu]
  have he := covariance_memLp_of_bound h law.e law.e_measurable 1
    (fun x => by rw [abs_of_nonneg (law.e_range x).1]; exact (law.e_range x).2)
  constructor <;> intro o
  all_goals
    first | rw [upper_denominator_kernel_section law hu] | rw [hs]
    by_cases hx : X o ∈ window h
    · have hp := covariance_projOp_range h hh J law.e he 0 1 law.e_range (X o) hx
      cases ha : A o <;> simp only [hx, if_true, bit, ha, Bool.false_eq_true, ↓reduceIte,
        mul_zero, zero_mul, mul_one, zero_sub, sub_zero, abs_zero]
      all_goals first
        | exact inv_nonneg.mpr hh.1.le
        | (rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hh.1.le), abs_of_nonneg hp.1]
           simpa only [mul_one] using mul_le_mul_of_nonneg_left hp.2 (inv_nonneg.mpr hh.1.le))
        | have hid : h⁻¹ - h⁻¹ * projOp h J law.e (X o) =
              h⁻¹ * (1-projOp h J law.e (X o)) := by ring
          rw [hid, abs_mul, abs_of_nonneg (inv_nonneg.mpr hh.1.le),
            abs_of_nonneg (sub_nonneg.mpr hp.2)]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (show 1-projOp h J law.e (X o) ≤ 1 by linarith [hp.1]) (inv_nonneg.mpr hh.1.le)
    · have hp : projOp h J law.e (X o) = 0 := by simp [projOp, projKernel, hx]
      simp [hx, hp]

/-- Removing the two binary marks bounds the denominator kernel by the exact
 histogram section energy, with the original uniform covariate marginal. -/
-- @node: upper_denominator_kernel_energy
lemma upper_denominator_kernel_energy (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ) :
    (∫ o, ∫ z, (h⁻¹ * (bit (A o)*bit (A z)*projKernel h J (X o) (X z)))^2
      ∂law.P ∂law.P) ≤ 1 / (h * cellLen h J) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  let H : O × O → ℝ := fun oz => h⁻¹ * projKernel h J (X oz.1) (X oz.2)
  have hH : MemLp H 2 (law.P.prod law.P) := by
    apply MemLp.of_bound (by
      have hm : Measurable H := by dsimp [H]; unfold X; fun_prop
      exact hm.aestronglyMeasurable)
      (|h⁻¹| * |(cellLen h J)⁻¹|)
    filter_upwards [] with oz
    simp only [H, Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    unfold projKernel
    split_ifs <;> simp
  have hi := (upper_denominator_kernel_memLp law h J).integrable_sq
  have hdrop : (∫ o, ∫ z, (h⁻¹ * (bit (A o)*bit (A z)*projKernel h J (X o) (X z)))^2
      ∂law.P ∂law.P) ≤ ∫ o, ∫ z, (H (o,z))^2 ∂law.P ∂law.P := by
    rw [← integral_prod _ hi, ← integral_prod _ hH.integrable_sq]
    apply integral_mono hi hH.integrable_sq
    intro oz
    cases ha : A oz.1 <;> cases hb : A oz.2 <;> simp [H, bit, ha, hb, sq_nonneg]
  have hsection (o : O) : (∫ z, (H (o,z))^2 ∂law.P) =
      (window h).indicator (fun _ => (h⁻¹)^2 * (cellLen h J)⁻¹) (X o) := by
    have hm : Measurable (fun x => (projKernel h J (X o) x)^2) := by fun_prop
    have he : (∫ z, (projKernel h J (X o) (X z))^2 ∂law.P) =
        ∫ x, (projKernel h J (X o) x)^2 ∂design := by
      rw [← hu]
      exact (integral_map (by unfold X; fun_prop) hm.aestronglyMeasurable).symm
    simp only [H, mul_pow, integral_const_mul, he]
    by_cases hx : X o ∈ window h
    · rw [show (fun x => (projKernel h J (X o) x)^2) =
        (window h).indicator (fun x => (projKernel h J (X o) x)^2) by
          funext x; by_cases hx' : x ∈ window h <;> simp [projKernel, hx'],
        integral_indicator hw]
      have hs := projKernel_sq_integral h hh J (X o) hx
      simp_rw [projKernel_symm h J (X o)]
      rw [hs]
      simp [hx]
    · simp [projKernel, hx]
  simp_rw [hsection] at hdrop
  have hm : Measurable ((window h).indicator (fun _ : unitInterval => (h⁻¹)^2 * (cellLen h J)⁻¹)) :=
    measurable_const.indicator hw
  have he := (integral_map (φ := X) (by unfold X; fun_prop) hm.aestronglyMeasurable (μ := law.P)).symm
  rw [hu, integral_indicator hw] at he
  rw [he] at hdrop
  have hc : 0 < cellLen h J := by unfold cellLen; exact div_pos hh.1 (by positivity)
  have hval : (∫ _x in window h, (h⁻¹)^2 * (cellLen h J)⁻¹ ∂design) =
      1/(h * cellLen h J) := by
    simp [integral_const, Measure.real, design_window h hh, ENNReal.toReal_ofReal hh.1.le]
    field_simp
  rwa [hval] at hdrop

/-- The actual two-block denominator has the three standard-deviation bounds
 dictated by its supported projections and centered histogram kernel. -/
-- @node: upper_denominator_deviation_unscaled
lemma upper_denominator_deviation_unscaled (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (law : ObservedLaw) (hm : InModel κ law) :
    (∫ o, |denominatorHat κ n o-localDenominator law (upperH κ n) (upperJ κ n)|
      ∂Measure.pi (fun _ : Fin n => law.P)) ≤
      Real.sqrt (1 / ((treatmentBlock n).card * upperH κ n)) +
      Real.sqrt (1 / ((outcomeBlock n).card * upperH κ n)) +
      Real.sqrt (1 / ((treatmentBlock n).card * (outcomeBlock n).card *
        upperH κ n * cellLen (upperH κ n) (upperJ κ n))) := by
  let h := upperH κ n
  let J := upperJ κ n
  let B := fun o z : O => h⁻¹ * (bit (A o)*bit (A z)*projKernel h J (X o) (X z))
  let F := fun o : O => h⁻¹ * (if X o ∈ window h then bit (A o) else 0)
  have hh := (upper_tuning κ hκ n hn).1
  obtain ⟨ht, hy, hd⟩ := upper_blocks_nonempty_disjoint n hn
  have hF : MemLp F 2 law.P := by
    apply MemLp.of_bound (by
      have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
      exact ((Measurable.ite (hw.preimage (by unfold X; fun_prop))
        (by unfold A; fun_prop) measurable_const).const_mul _).aestronglyMeasurable) |h⁻¹|
    filter_upwards [] with o
    by_cases hx : X o ∈ window h <;> cases ha : A o <;> simp [F, hx, bit, ha, Real.norm_eq_abs]
  have hB := upper_denominator_kernel_memLp law h J
  have hr := centeredKernel_row_mean_memLp law.P B hB
  have hswap : MemLp (fun oz : O × O => B oz.2 oz.1) 2 (law.P.prod law.P) :=
    (memLp_two_iff_integrable_sq hB.aestronglyMeasurable.prod_swap).2 hB.integrable_sq.swap
  have hc := centeredKernel_row_mean_memLp law.P (fun o z => B z o) hswap
  have hb := upper_denominator_projection_bounds law hm.uniform h hh J
  have hrow := (variance_le_expectation_sq hr.aestronglyMeasurable).trans
    (upper_window_second_moment law hm.uniform h hh _ hr hb.1)
  have hcol := (variance_le_expectation_sq (hF.sub hc).aestronglyMeasurable).trans
    (upper_window_second_moment law hm.uniform h hh _ (hF.sub hc) hb.2)
  have htc : 0 < ((treatmentBlock n).card : ℝ) := by exact_mod_cast ht.card_pos
  have hyc : 0 < ((outcomeBlock n).card : ℝ) := by exact_mod_cast hy.card_pos
  have hvT : variance (treatmentTerm law.P (treatmentBlock n) B)
      (Measure.pi (fun _ : Fin n => law.P)) ≤ 1 / ((treatmentBlock n).card*h) := by
    unfold treatmentTerm
    rw [upper_coordinate_average_variance law.P _ ht
      (fun o => (∫ z, B o z ∂law.P) - ∫ v, ∫ w, B v w ∂law.P ∂law.P)
      (hr.sub (memLp_const _)), variance_sub_const hr.aestronglyMeasurable]
    have he : ((treatmentBlock n).card : ℝ) * (((treatmentBlock n).card : ℝ)⁻¹)^2 =
        ((treatmentBlock n).card : ℝ)⁻¹ := by field_simp; <;> ring
    rw [he]
    convert mul_le_mul_of_nonneg_left hrow (inv_nonneg.mpr htc.le) using 1 <;> first | rfl | simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  have hvY : variance (outcomeTerm law.P (outcomeBlock n) F B)
      (Measure.pi (fun _ : Fin n => law.P)) ≤ 1 / ((outcomeBlock n).card*h) := by
    unfold outcomeTerm
    rw [upper_coordinate_average_variance law.P _ hy
      (fun o => F o - (∫ v, B v o ∂law.P) - ∫ z, F z - (∫ v, B v z ∂law.P) ∂law.P)
      ((hF.sub hc).sub (memLp_const _))]
    have hv := variance_sub_const (hF.sub hc).aestronglyMeasurable
      (∫ z, F z - (∫ v, B v z ∂law.P) ∂law.P)
    change variance (fun o => F o - (∫ v, B v o ∂law.P) -
      ∫ z, F z - (∫ v, B v z ∂law.P) ∂law.P) law.P = _ at hv
    rw [hv]
    have he : ((outcomeBlock n).card : ℝ) * (((outcomeBlock n).card : ℝ)⁻¹)^2 =
        ((outcomeBlock n).card : ℝ)⁻¹ := by field_simp; <;> ring
    rw [he]
    convert mul_le_mul_of_nonneg_left hcol (inv_nonneg.mpr hyc.le) using 1 <;> first | rfl | simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  have hvC : variance (degenerateTerm law.P (treatmentBlock n) (outcomeBlock n) B)
      (Measure.pi (fun _ : Fin n => law.P)) ≤
      1 / ((treatmentBlock n).card * (outcomeBlock n).card * h * cellLen h J) := by
    rw [twoBlock_degenerate_variance law.P _ _ hd ht hy B hB]
    have he := (centeredKernel_energy_contraction law.P B hB).trans
      (upper_denominator_kernel_energy law hm.uniform h hh J)
    have hdiv := div_le_div_of_nonneg_right he (mul_nonneg htc.le hyc.le)
    convert hdiv using 1 <;> first | rfl | simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  have hdev := twoBlock_deviation_bound law.P _ _ hd ht hy F B hF hB
  have hex := twoBlock_expectation law.P _ _ hd ht hy F B hF hB
  rw [← upper_denominator_twoBlock κ n] at hex hdev
  rw [← hex, upper_denominator_expectation κ hκ n hn law hm] at hdev
  exact hdev.trans (add_le_add (add_le_add (Real.sqrt_le_sqrt hvT) (Real.sqrt_le_sqrt hvY))
    (Real.sqrt_le_sqrt hvC))

/-- Both fixed blocks contain at least a third of the sample, including odd n. -/
-- @node: upper_block_card_bounds
lemma upper_block_card_bounds (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ)/3 ≤ (treatmentBlock n).card ∧
    (n : ℝ)/3 ≤ (outcomeBlock n).card := by
  classical
  have ht : (treatmentBlock n).card = n/2 := by
    unfold treatmentBlock
    rw [Fin.card_filter_val_lt]
    exact min_eq_right (Nat.div_le_self _ _)
  have hy : (outcomeBlock n).card = n-n/2 := by
    have he : outcomeBlock n = Finset.univ \ treatmentBlock n := by
      ext i; simp [outcomeBlock, treatmentBlock]
    rw [he, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, ht]
  have ht' : n ≤ 3*(treatmentBlock n).card := by rw [ht]; omega
  have hy' : n ≤ 3*(outcomeBlock n).card := by rw [hy]; omega
  constructor <;> apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).2
  · rw [mul_comm]; exact_mod_cast ht'
  · rw [mul_comm]; exact_mod_cast hy'

/-- The public bandwidth budget controls the squared single-record noise scale. -/
-- @node: upper_inverse_bandwidth_budget
lemma upper_inverse_bandwidth_budget (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    1/((n : ℝ)*upperH κ n) ≤ (rate κ n)^2 := by
  have ht := upper_tuning κ hκ n hn
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hκ.1.1) hp
  have hqle : qExp κ ≤ 1/2 := by
    unfold qExp
    apply (div_le_iff₀ hp).2
    linarith [hκ.1.2]
  have hx : 0 < (n : ℝ)*upperH κ n := lt_of_lt_of_le (by norm_num) ht.2.1
  have hr : 0 ≤ rate κ n := le_trans (Real.rpow_pos_of_pos hx _).le ht.2.2.1
  have hs := (sq_le_sq₀ (Real.rpow_pos_of_pos hx (-qExp κ)).le hr).2 ht.2.2.1
  have he : (((n : ℝ)*upperH κ n)^(-qExp κ))^2 =
      ((n : ℝ)*upperH κ n)^(-2*qExp κ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx.le]
    congr 1; ring
  rw [he] at hs
  have hpow := Real.rpow_le_rpow_of_exponent_le ht.2.1
    (show (-1 : ℝ) ≤ -2*qExp κ by linarith)
  rw [Real.rpow_neg_one] at hpow
  simpa only [one_div] using hpow.trans hs

/-- The finest-mesh budget and rounding control the degenerate squared noise
 scale. The zero-resolution case instead uses the bandwidth budget. -/
-- @node: upper_inverse_mesh_budget
lemma upper_inverse_mesh_budget (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    1/((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) (upperJ κ n)) ≤
      16*(rate κ n)^2 := by
  let h := upperH κ n
  let δ := cellLen h (upperJ κ n)
  have ht := upper_tuning κ hκ n hn
  have hh : 0 < h := ht.1.1
  have hδ : 0 < δ := by dsimp [δ]; unfold cellLen; exact div_pos hh (by positivity)
  have hδle : δ ≤ 1 := by
    have hd : δ ≤ h := by
      dsimp [δ]; unfold cellLen
      exact div_le_self hh.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    exact hd.trans ht.1.2
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hκ.1.1) hp
  have hqle : qExp κ ≤ 1/2 := by
    unfold qExp; apply (div_le_iff₀ hp).2; linarith [hκ.1.2]
  have hr : 0 ≤ rate κ n := le_trans (Real.rpow_pos_of_pos
    (lt_of_lt_of_le (by norm_num) ht.2.1) _).le ht.2.2.1
  by_cases hJ : upperJ κ n = 0
  · have he : (n : ℝ)^2*h*δ = ((n : ℝ)*h)^2 := by
      dsimp [δ]; rw [hJ]; simp [cellLen]; ring
    have hx : 1 ≤ (n : ℝ)*h := ht.2.1
    have hi : 1/(((n : ℝ)*h)^2) ≤ 1/((n : ℝ)*h) := by
      apply one_div_le_one_div_of_le (lt_of_lt_of_le (by norm_num) hx)
      nlinarith
    change 1/((n : ℝ)^2*h*δ) ≤ _
    rw [he]
    have hb := upper_inverse_bandwidth_budget κ hκ n hn
    exact (hi.trans hb).trans (by nlinarith [sq_nonneg (rate κ n)])
  · have hb := upper_finest_budget κ hκ n hn (Nat.pos_of_ne_zero hJ)
    have he : 2*effectiveS κ ≤ 2*effectiveA κ + κ.β/qExp κ := by
      have hd : 2*κ.β ≤ κ.β/qExp κ := (le_div_iff₀ hq).2 (by nlinarith [hκ.2.2.1.1])
      unfold effectiveS
      linarith
    have hpow := Real.rpow_le_rpow_of_exponent_ge hδ hδle
      (show 1+2*effectiveS κ ≤ 1+2*effectiveA κ+κ.β/qExp κ by linarith)
    have hbudget : 1 ≤ (n : ℝ)^2*h*δ^(1+2*effectiveS κ) :=
      hb.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    rw [Real.rpow_add hδ, Real.rpow_one] at hbudget
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hdpos : 0 < (n : ℝ)^2*h*δ := by positivity
    have hi : 1/((n : ℝ)^2*h*δ) ≤ δ^(2*effectiveS κ) :=
      (div_le_iff₀ hdpos).2 (by nlinarith only [hbudget])
    have hs := (sq_le_sq₀ (Real.rpow_pos_of_pos hδ _).le (by positivity : 0 ≤ 4*rate κ n)).2
      ht.2.2.2.2.1
    have hid : (δ^effectiveS κ)^2 = δ^(2*effectiveS κ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hδ.le]; congr 1; ring
    rw [hid] at hs
    exact hi.trans (by nlinarith only [hs])

/-- The denominator of the stated estimator attains the roadmap's public
 deviation certificate, without any outcome moment or nuisance premise added. -/
-- @node: upper_denominator_deviation
lemma upper_denominator_deviation (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (law : ObservedLaw) (hm : InModel κ law) :
    (∫ o, |denominatorHat κ n o-localDenominator law (upperH κ n) (upperJ κ n)|
      ∂Measure.pi (fun _ : Fin n => law.P)) ≤ 20*rate κ n := by
  let h := upperH κ n
  let δ := cellLen h (upperJ κ n)
  let r := rate κ n
  have ht := upper_tuning κ hκ n hn
  have hh : 0 < h := ht.1.1
  have hδ : 0 < δ := by dsimp [δ]; unfold cellLen; exact div_pos hh (by positivity)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 ≤ r := le_trans (Real.rpow_pos_of_pos (mul_pos hnpos hh) _).le ht.2.2.1
  obtain ⟨hT, hY⟩ := upper_block_card_bounds n hn
  have htc : 0 < ((treatmentBlock n).card : ℝ) := lt_of_lt_of_le (by positivity) hT
  have hyc : 0 < ((outcomeBlock n).card : ℝ) := lt_of_lt_of_le (by positivity) hY
  have hb := upper_inverse_bandwidth_budget κ hκ n hn
  have hc := upper_inverse_mesh_budget κ hκ n hn
  have hsingle (k : ℝ) (hk : (n : ℝ)/3 ≤ k) : Real.sqrt (1/(k*h)) ≤ 2*r := by
    have hkpos : 0 < k := lt_of_lt_of_le (by positivity) hk
    have hi : 1/(k*h) ≤ 3/((n : ℝ)*h) := by
      have he := one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ)/3*h)
        (mul_le_mul_of_nonneg_right hk hh.le)
      convert he using 1 <;> first | rfl | field_simp <;> ring
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    have hb' : 3/((n : ℝ)*h) ≤ 3*r^2 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 3)
    exact (hi.trans hb').trans (by nlinarith [sq_nonneg r])
  have hcross : Real.sqrt (1/((treatmentBlock n).card*(outcomeBlock n).card*h*δ)) ≤ 12*r := by
    have hprod : (n : ℝ)^2/9 ≤ (treatmentBlock n).card*(outcomeBlock n).card := by
      have he := mul_le_mul hT hY (by positivity) htc.le
      nlinarith only [he]
    have hi : 1/((treatmentBlock n).card*(outcomeBlock n).card*h*δ) ≤
        9/((n : ℝ)^2*h*δ) := by
      have he := one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ)^2/9*h*δ)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod hh.le) hδ.le)
      convert he using 1 <;> first | rfl | field_simp <;> ring
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    have hc' : 9/((n : ℝ)^2*h*δ) ≤ 144*r^2 := by
      have he := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 9)
      dsimp only [δ, h, r] at ⊢
      simpa only [mul_one_div, ← mul_assoc, show (9 : ℝ)*16 = 144 by norm_num] using he
    exact (hi.trans hc').trans (by ring_nf; rfl)
  have hd := upper_denominator_deviation_unscaled κ hκ n hn law hm
  have hs := add_le_add (add_le_add (hsingle _ hT) (hsingle _ hY)) hcross
  exact hd.trans (hs.trans (by dsimp [r]; nlinarith only [hr]))

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
