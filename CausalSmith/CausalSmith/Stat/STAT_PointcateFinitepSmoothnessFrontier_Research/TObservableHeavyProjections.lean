module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.Completion
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.ProjectionFieldBounds
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TruncationMoments
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TwoBlock

/-! Finite-moment point-CATE frontier: TObservableHeavyProjections. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- Public moment-only projection constant. -/
def constantG (p : ℝ) : ℝ := 3 * (10 : ℝ)^(2/p)
/-- The public projection constant is uniformly bounded on the moment domain. -/
-- @node: constantG_le
lemma constantG_le (p : ℝ) (hp : 1 < p) : constantG p ≤ 300 := by
  have hp0 : 0 < p := by linarith
  have he : 2/p ≤ 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hr := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 10) he
  norm_num at hr
  unfold constantG
  linarith

/-- Histogram kernel sections have a finite deterministic absolute bound. -/
-- @node: projKernel_abs_bound
lemma projKernel_abs_bound (h : ℝ) (j : ℕ) (x z : unitInterval) :
    |projKernel h j x z| ≤ |(cellLen h j)⁻¹| := by
  unfold projKernel
  split_ifs <;> simp

/-- Truncation bounds the response for every nonnegative public threshold. -/
-- @node: trunc_abs_bound
lemma trunc_abs_bound (t y : ℝ) (ht : 0 ≤ t) : |trunc t y| ≤ t := by
  unfold trunc
  split_ifs with hy
  · exact hy
  · simpa using ht

/-- Every finite heavy kernel is square integrable under the original product law.
This uses finite clipping bounds, before any sharp energy or centering argument. -/
-- @node: heavyKernel_memLp
lemma heavyKernel_memLp (law : ObservedLaw) (h : ℝ) (J : ℕ)
    (T : Fin (J+1) → ℝ) (hT : ∀ j, 0 ≤ T j) :
    MemLp (fun z : O × O => heavyKernel h J T z.1 z.2) 2 (law.P.prod law.P) := by
  let C := |(cellLen h 0)⁻¹| * T 0 +
    ∑ j : Fin J, (|(cellLen h (j.val+1))⁻¹| + |(cellLen h j.val)⁻¹|) * T j.succ
  have hb (j : Fin J) (x z : unitInterval) :
      |bandKernel h (j.val+1) x z| ≤
        |(cellLen h (j.val+1))⁻¹| + |(cellLen h j.val)⁻¹| := by
    unfold bandKernel
    simp only [Nat.add_sub_cancel]
    exact (abs_sub _ _).trans (add_le_add
      (projKernel_abs_bound h _ x z) (projKernel_abs_bound h _ x z))
  apply MemLp.of_bound (by fun_prop) (|h⁻¹| * C)
  apply Filter.Eventually.of_forall
  intro oz
  rw [Real.norm_eq_abs]
  unfold heavyKernel
  rw [abs_mul]
  have hleg : |(if A oz.1 then (1 : ℝ) else 0) / h| ≤ |h⁻¹| := by
    cases A oz.1 <;> simp [div_eq_mul_inv]
  apply mul_le_mul hleg _ (abs_nonneg _) (abs_nonneg _)
  calc
    _ ≤ |projKernel h 0 (X oz.1) (X oz.2) * trunc (T 0) (Y oz.2)| +
        ∑ j : Fin J, |bandKernel h (j.val+1) (X oz.1) (X oz.2) * trunc (T j.succ) (Y oz.2)| :=
      (abs_add_le _ _).trans (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)
    _ ≤ C := by
      dsimp [C]
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul (projKernel_abs_bound h _ _ _)
          (trunc_abs_bound _ _ (hT 0)) (abs_nonneg _) (abs_nonneg _)
      · apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hb j _ _) (trunc_abs_bound _ _ (hT j.succ))
          (abs_nonneg _) (by positivity)

/-- Product-law centering contracts the finite clipped kernel's squared energy. -/
-- @node: heavyCentered_energy_contraction
lemma heavyCentered_energy_contraction (law : ObservedLaw) (h : ℝ) (J : ℕ)
    (T : Fin (J+1) → ℝ) (hT : ∀ j, 0 ≤ T j) :
    (∫ o, ∫ z, (heavyCentered law h J T o z)^2 ∂law.P ∂law.P) ≤
      (∫ o, ∫ z, (heavyKernel h J T o z)^2 ∂law.P ∂law.P) := by
  exact centeredKernel_energy_contraction law.P (heavyKernel h J T)
    (heavyKernel_memLp law h J T hT)

/-- Orthogonal histogram sections give an exact energy identity for arbitrary donor coefficients.
The coefficients are scalars here and may depend on one common outcome record. -/
-- @node: heavy_section_energy
lemma heavy_section_energy (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ)
    (c : Fin (J+1) → ℝ) (z : unitInterval) (hz : z ∈ window h) :
    (∫ x in window h, (projKernel h 0 x z * c 0 +
      ∑ j : Fin J, bandKernel h (j.val+1) x z * c j.succ)^2 ∂design) =
      h⁻¹ * ((c 0)^2 + ∑ j : Fin J, (2 : ℝ)^j.val * (c j.succ)^2) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let f : Fin (J+1) → unitInterval → ℝ := fun j x =>
    (if j.val = 0 then projKernel h 0 x z else bandKernel h j.val x z) * c j
  have hp (j : ℕ) : MemLp (fun x => projKernel h j x z) 2 (design.restrict (window h)) := by
    apply MemLp.of_bound (by fun_prop) |(cellLen h j)⁻¹|
    exact Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs]
      exact projKernel_abs_bound h j x z
  have hb (j : ℕ) : MemLp (fun x => bandKernel h j x z) 2 (design.restrict (window h)) := by
    exact (hp j).sub (hp (j-1))
  have hf (j : Fin (J+1)) : MemLp (f j) 2 (design.restrict (window h)) := by
    dsimp [f]
    split_ifs
    · exact (hp 0).mul_const (c j)
    · exact (hb j.val).mul_const (c j)
  have ho (i j : Fin (J+1)) (hne : i ≠ j) :
      (∫ x in window h, f i x * f j x ∂design) = 0 := by
    have hv : i.val ≠ j.val := fun he => hne (Fin.ext he)
    have he : (fun x => f i x * f j x) = (fun x => (c i * c j) *
      ((if i.val = 0 then projKernel h 0 x z else bandKernel h i.val x z) *
       (if j.val = 0 then projKernel h 0 x z else bandKernel h j.val x z))) := by
      funext x; dsimp [f]; ring
    rw [he, integral_const_mul]
    by_cases hi : i.val = 0
    · have hj : j.val ≠ 0 := by omega
      simp only [if_pos hi, if_neg hj]
      rw [projKernel_zero_bandKernel_orthogonal h hh j.val z hz, mul_zero]
    · by_cases hj : j.val = 0
      · simp only [if_neg hi, if_pos hj]
        simp_rw [mul_comm (bandKernel h i.val _ z)]
        rw [projKernel_zero_bandKernel_orthogonal h hh i.val z hz, mul_zero]
      · simp only [if_neg hi, if_neg hj]
        rw [bandKernel_sections_orthogonal h hh i.val j.val (by omega) (by omega) hv z hz,
          mul_zero]
  have he := integral_sq_orthogonal_sum (design.restrict (window h)) Finset.univ f
    (fun j _ => hf j) (fun i _ j _ hn => ho i j hn)
  have hsum (x) : (∑ j, f j x) = projKernel h 0 x z * c 0 +
      ∑ j : Fin J, bandKernel h (j.val+1) x z * c j.succ := by
    rw [Fin.sum_univ_succ]
    simp [f]
  simp_rw [hsum] at he
  rw [he, Fin.sum_univ_succ]
  have hsq (j : Fin (J+1)) : (fun x => (f j x)^2) =
      (fun x => (c j)^2 * (if j.val = 0 then (projKernel h 0 x z)^2
        else (bandKernel h j.val x z)^2)) := by
    funext x; dsimp [f]; split_ifs <;> ring
  simp_rw [hsq, integral_const_mul]
  simp only [Fin.val_zero, if_pos rfl, Fin.val_succ, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, if_false, if_true]
  rw [projKernel_zero_sq_integral h hh z hz]
  have hband (k : ℕ) : (∫ x in window h, (bandKernel h (k+1) x z)^2 ∂design) =
      (2 : ℝ)^k * h⁻¹ := by
    simpa only [Nat.add_sub_cancel] using bandKernel_sq_integral h hh (k+1) (by omega) z hz
  simp_rw [hband]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

/-- A clipped measurable response is in L2 under every finite measure. -/
-- @node: trunc_comp_memLp
lemma trunc_comp_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f) (T : ℝ) (hT : 0 ≤ T) :
    MemLp (fun x => trunc T (f x)) 2 μ := by
  apply MemLp.of_bound (by
    first | fun_prop | exact ((measurable_trunc T).comp hf).aestronglyMeasurable) T
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using trunc_abs_bound T (f x) hT

/-- Conditional record integration retains the Bernoulli weights of both clipped arm moments. -/
-- @node: record_trunc_square_integral
lemma record_trunc_square_integral (law : ObservedLaw) (x : unitInterval)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ r : Bool × ℝ, (trunc T r.2)^2 ∂recordMeasure law.e law.Q x) =
      law.e x * (∫ y, (trunc T y)^2 ∂law.Q true x) +
        (1-law.e x) * (∫ y, (trunc T y)^2 ∂law.Q false x) := by
  have hi (a : Bool) : Integrable (fun r : Bool × ℝ => (trunc T r.2)^2)
      ((Measure.dirac a).prod (law.Q a x)) :=
    (trunc_comp_memLp _ Prod.snd (by fun_prop) T hT).integrable_sq
  have he (a : Bool) : (∫ r : Bool × ℝ, (trunc T r.2)^2
      ∂((Measure.dirac a).prod (law.Q a x))) = ∫ y, (trunc T y)^2 ∂law.Q a x := by
    rw [Measure.dirac_prod, integral_map (by fun_prop) (by
      first | fun_prop | exact ((measurable_trunc T).comp measurable_snd).pow_const 2 |>.aestronglyMeasurable)]
  unfold recordMeasure
  rw [integral_add_measure ((hi true).smul_measure ENNReal.ofReal_ne_top)
    ((hi false).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, smul_eq_mul, he,
    ENNReal.toReal_ofReal (law.e_range x).1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (law.e_range x).2)]

/-- The original-law localized clipped second moment follows from the two arm envelopes. -/
-- @node: localized_trunc_square_bound
lemma localized_trunc_square_bound (κ : Params) (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (T : ℝ) (hT : 1 ≤ T) :
    (∫ o, (window h).indicator (fun _ => (trunc T (Y o))^2) (X o) ∂law.P) ≤
      10 * h * T^(2-κ.p) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let := completion_record_kernel_markov law
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have ht : 0 ≤ T := (by norm_num : (0 : ℝ) ≤ 1).trans hT
  have hi : Integrable (fun o => (window h).indicator
      (fun _ => (trunc T (Y o))^2) (X o)) law.P := by
    apply ((trunc_comp_memLp law.P Y (by unfold Y; fun_prop) T ht).integrable_sq.indicator
      (hw.preimage (show Measurable X by unfold X; fun_prop))).congr
    exact Filter.Eventually.of_forall fun o => by
      by_cases hx : X o ∈ window h <;> simp [hx]
  have hv : law.P = design ⊗ₘ recordKernel law.e law.e_measurable law.Q :=
    law.record_version.trans (by rw [hm.uniform])
  rw [hv] at hi ⊢
  rw [Measure.integral_compProd hi]
  have he : (fun x => ∫ r : Bool × ℝ,
      (window h).indicator (fun _ => (trunc T (Y (x,r)))^2) (X (x,r))
        ∂recordKernel law.e law.e_measurable law.Q x) =
      (window h).indicator (fun x => law.e x * (∫ y, (trunc T y)^2 ∂law.Q true x) +
        (1-law.e x) * (∫ y, (trunc T y)^2 ∂law.Q false x)) := by
    funext x
    by_cases hx : x ∈ window h
    · simp only [X, Y, Set.indicator_of_mem hx, recordKernel]
      exact record_trunc_square_integral law x T ht
    · simp [X, hx]
  rw [he, integral_indicator hw]
  have hi' : IntegrableOn (fun x => law.e x * (∫ y, (trunc T y)^2 ∂law.Q true x) +
      (1-law.e x) * (∫ y, (trunc T y)^2 ∂law.Q false x)) (window h) design := by
    have hint := hi.integral_compProd
    simp only [Kernel.prodMkLeft_apply, Kernel.const_apply] at hint
    rw [he] at hint
    exact (integrable_indicator_iff hw).mp hint
  calc
    _ ≤ ∫ _x in window h, 10 * T^(2-κ.p) ∂design := by
      apply integral_mono_ae hi' (integrable_const _)
      filter_upwards [ae_restrict_of_ae hm.conditionalMoment] with x hx
      have h0 := (truncation_moment_bounds κ.p T hκ.1 hT (law.Q false x) (hx false)).2.2.2
      have h1 := (truncation_moment_bounds κ.p T hκ.1 hT (law.Q true x) (hx true)).2.2.2
      have ha := mul_le_mul_of_nonneg_left h1 (law.e_range x).1
      have hb := mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr (law.e_range x).2)
      nlinarith
    _ = _ := by
      simp [integral_const, Measure.real, design_window h hh, ENNReal.toReal_ofReal hh.1.le]
      ring

/-- Finite linear combinations of histogram sections are square integrable after any
measurable covariate map under a finite measure. -/
-- @node: heavy_location_memLp
lemma heavy_location_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f : Ω → unitInterval) (hf : Measurable f)
    (h : ℝ) (J : ℕ) (c : Fin (J+1) → ℝ) (z : unitInterval) :
    MemLp (fun o => projKernel h 0 (f o) z * c 0 +
      ∑ j : Fin J, bandKernel h (j.val+1) (f o) z * c j.succ) 2 μ := by
  have hp (j : ℕ) : MemLp (fun o => projKernel h j (f o) z) 2 μ := by
    apply MemLp.of_bound (by
      first | fun_prop | exact ((measurable_projKernel h j).comp
        (hf.prodMk measurable_const)).aestronglyMeasurable) |(cellLen h j)⁻¹|
    exact Filter.Eventually.of_forall fun o => by
      simpa only [Real.norm_eq_abs] using projKernel_abs_bound h j (f o) z
  apply ((hp 0).mul_const (c 0)).add
  apply memLp_finsetSum
  intro j _
  exact ((hp (j.val+1)).sub (hp j.val)).mul_const (c j.succ)

/-- Dropping the binary treatment leg precedes Lebesgue orthogonality; the resulting
bound is supported on the donor window. -/
-- @node: heavy_treatment_section_bound
lemma heavy_treatment_section_bound (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ) (T : Fin (J+1) → ℝ) (z : O) :
    (∫ o, (heavyKernel h J T o z)^2 ∂law.P) ≤
      (h⁻¹)^3 * (window h).indicator (fun _ => (trunc (T 0) (Y z))^2 +
        ∑ j : Fin J, (2 : ℝ)^j.val * (trunc (T j.succ) (Y z))^2) (X z) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let c : Fin (J+1) → ℝ := fun j => trunc (T j) (Y z)
  let H : unitInterval → ℝ := fun x => projKernel h 0 x (X z) * c 0 +
    ∑ j : Fin J, bandKernel h (j.val+1) x (X z) * c j.succ
  have hi := (heavy_location_memLp law.P X (by unfold X; fun_prop) h J c (X z)).integrable_sq
  have hmH : Measurable H := by dsimp [H]; fun_prop
  have hdrop : (∫ o, (heavyKernel h J T o z)^2 ∂law.P) ≤
      (h⁻¹)^2 * ∫ o, (H (X o))^2 ∂law.P := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun o => sq_nonneg _)
      (hi.const_mul _) (Filter.Eventually.of_forall ?_)
    intro o
    change (((if A o then (1 : ℝ) else 0) / h) * H (X o))^2 ≤ _
    cases ha : A o
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, zero_div, zero_mul, zero_pow (by decide : 2 ≠ 0)]
      positivity
    · simp [ha, one_div, mul_pow, H]
  have hmap : (∫ o, (H (X o))^2 ∂law.P) = ∫ x, (H x)^2 ∂design := by
    rw [← hu]
    exact (integral_map (by unfold X; fun_prop) (hmH.pow_const 2).aestronglyMeasurable).symm
  rw [hmap] at hdrop
  by_cases hz : X z ∈ window h
  · have hs : (window h).indicator (fun x => (H x)^2) = fun x => (H x)^2 := by
      funext x
      by_cases hx : x ∈ window h
      · simp [hx]
      · simp [H, bandKernel, projKernel, hx]
    have he : (∫ x, (H x)^2 ∂design) =
        h⁻¹ * ((c 0)^2 + ∑ j : Fin J, (2 : ℝ)^j.val * (c j.succ)^2) := by
      rw [← hs, integral_indicator (show MeasurableSet (window h) from
        measurable_subtype_coe measurableSet_Icc)]
      exact heavy_section_energy h hh J c (X z) hz
    rw [he] at hdrop
    simp only [Set.indicator_of_mem hz]
    dsimp [c] at hdrop
    convert hdrop using 1 <;> ring
  · have hs : H = 0 := by
      funext x
      simp [H, bandKernel, projKernel, hz]
    simp only [hs, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), integral_zero, mul_zero] at hdrop
    simpa only [Set.indicator_of_notMem hz, mul_zero] using hdrop

/-- Integrating the donor-section bound gives the sharp multiscale product-law energy. -/
-- @node: heavyKernel_energy_bound
lemma heavyKernel_energy_bound (κ : Params) (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ)
    (T : Fin (J+1) → ℝ) (hT : ∀ j, 1 ≤ T j) :
    (∫ o, ∫ z, (heavyKernel h J T o z)^2 ∂law.P ∂law.P) ≤
      (10/h^2) * (T 0 ^ (2-κ.p) + ∑ j : Fin J, (2 : ℝ)^j.val * T j.succ ^ (2-κ.p)) := by
  have ht : ∀ j, 0 ≤ T j := fun j => (by norm_num : (0 : ℝ) ≤ 1).trans (hT j)
  have hi := (heavyKernel_memLp law h J T ht).integrable_sq
  rw [integral_integral_swap hi]
  let F : Fin (J+1) → O → ℝ := fun j z =>
    (window h).indicator (fun _ => (trunc (T j) (Y z))^2) (X z)
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have hF (j) : Integrable (F j) law.P := by
    apply ((trunc_comp_memLp law.P Y (by unfold Y; fun_prop) (T j) (ht j)).integrable_sq.indicator
      (hw.preimage (show Measurable X by unfold X; fun_prop))).congr
    exact Filter.Eventually.of_forall fun z => by
      by_cases hz : X z ∈ window h <;> simp [F, hz]
  have he (z : O) : (window h).indicator (fun _ => (trunc (T 0) (Y z))^2 +
      ∑ j : Fin J, (2 : ℝ)^j.val * (trunc (T j.succ) (Y z))^2) (X z) =
      F 0 z + ∑ j : Fin J, (2 : ℝ)^j.val * F j.succ z := by
    by_cases hz : X z ∈ window h <;> simp [F, hz]
  calc
    _ ≤ ∫ z, (h⁻¹)^3 * (F 0 z + ∑ j : Fin J, (2 : ℝ)^j.val * F j.succ z) ∂law.P := by
      apply integral_mono_ae hi.integral_prod_right
        (((hF 0).add (integrable_finset_sum _ (fun j _ => (hF j.succ).const_mul _))).const_mul _)
      exact Filter.Eventually.of_forall fun z => by
        dsimp only [Pi.add_apply]
        rw [← he z]
        exact heavy_treatment_section_bound law hm.uniform h hh J T z
    _ = (h⁻¹)^3 * ((∫ z, F 0 z ∂law.P) +
        ∑ j : Fin J, (2 : ℝ)^j.val * ∫ z, F j.succ z ∂law.P) := by
      integral_linearity
    _ ≤ (h⁻¹)^3 * (10 * h * T 0^(2-κ.p) +
        ∑ j : Fin J, (2 : ℝ)^j.val * (10 * h * T j.succ^(2-κ.p))) := by
      gcongr
      · exact pow_nonneg (inv_nonneg.mpr hh.1.le) 3
      · exact localized_trunc_square_bound κ hκ law hm h hh (T 0) (hT 0)
      · exact localized_trunc_square_bound κ hκ law hm h hh _ (hT _)
    _ = _ := by
      have hsum : (∑ j : Fin J, (2 : ℝ)^j.val * (10*h*T j.succ^(2-κ.p))) =
          10*h * ∑ j : Fin J, (2 : ℝ)^j.val * T j.succ^(2-κ.p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _; ring
      rw [hsum]
      field_simp [hh.1.ne']
      <;> ring

-- @node: lem:observable-heavy-projections
/-- The field and product-law heavy kernel have the observable multiscale L2 bounds without
conditional-tail smoothness or independent outcome records at different levels. -/
lemma observable_heavy_projections (κ : Params) (hκ : κ.Valid) (law : ObservedLaw) (hm : InModel κ law)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ) (T : Fin (J+1) → ℝ)
    (hT : ∀ j, 1 ≤ T j) -- @realizes T(public thresholds ≥1)
    (j0 : ℕ) (hj0 : j0 ≤ J) (hcap : ∀ j, j.val ≤ j0 → T j = T 0) :
  constantG κ.p ≤ 300 ∧
  h⁻¹ * (∫ x in window h, (projectionField law h J T x)^2 ∂design) ≤
    constantG κ.p + 200 * (∑ j : Fin J, if j0 < j.val+1 then T j.succ ^ (-2*(κ.p-1)) else 0) ∧
  MemLp (fun z : O × O => heavyKernel h J T z.1 z.2) 2 (law.P.prod law.P) ∧
  (∫ o, ∫ z, (heavyCentered law h J T o z)^2 ∂law.P ∂law.P) ≤
    (∫ o, ∫ z, (heavyKernel h J T o z)^2 ∂law.P ∂law.P) ∧
  (∫ o, ∫ z, (heavyKernel h J T o z)^2 ∂law.P ∂law.P) ≤
    (10/h^2) * (T 0 ^ (2-κ.p) + ∑ j : Fin J, (2 : ℝ)^j.val * T j.succ ^ (2-κ.p)) := by
  have hT0 : ∀ j, 0 ≤ T j := fun j => (by norm_num : (0 : ℝ) ≤ 1).trans (hT j)
  refine ⟨constantG_le κ.p hκ.1.1, ?_, heavyKernel_memLp law h J T hT0,
    heavyCentered_energy_contraction law h J T hT0, ?_⟩
  · exact projectionField_energy_bound κ hκ law hm h hh J T hT j0 hj0 hcap
  · exact heavyKernel_energy_bound κ hκ law hm h hh J T hT

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
