module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PositiveRatio
public import Mathlib.Probability.Moments.Variance

/-! Tonelli and the weak-design envelope supply the public second moments for
both signed inverse-weight sample marks. Product sampling then gives unbiased block
averages, variance and absolute-error bounds, and independence of disjoint blocks. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]

/-- A nonnegative stratum mark is its conditional integral multiplied by stratum mass. [Under the stated conditions](hyp:hoverlap,f). [This is the stated conclusion](goal). -/
-- @node: stratum_indicator_lintegral
lemma stratum_indicator_lintegral (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hoverlap : StratumPositive P) (x : Bool)
    (f : StructSpace S → ℝ≥0∞) :
    (∫⁻ w, (if sX w = x then f w else 0) ∂P) =
      P {w | sX w = x} * ∫⁻ w, f w ∂stratumLaw P x := by
  have hx : MeasurableSet {w : StructSpace S | sX w = x} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hp : P {w | sX w = x} ≠ 0 := by
    intro h
    have := strataProb_pos P hoverlap x
    simp [strataProb, Measure.real, h] at this
  rw [stratumLaw, lintegral_smul_measure]
  rw [smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hp (measure_ne_top P _), one_mul]
  simpa only [Set.indicator_apply, Set.mem_setOf_eq] using lintegral_indicator hx f

/-- Error independence factors the conditional inverse-weight square by Tonelli. [Under the stated conditions](hyp:hoverlap,herr,hgauss,hell). [This is the stated conclusion](goal). -/
-- @node: inverse_square_stratum_lintegral
lemma inverse_square_stratum_lintegral (sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (hoverlap : StratumPositive P) (herr : ErrorIndependence P)
    (hgauss : GaussianChannel P) (x : Bool) (ell : ℝ → ℝ) (hell : Measurable ell) :
    (∫⁻ w, ENNReal.ofReal ((ell (observedCentered sigma w))^2) ∂stratumLaw P x) =
      ∫⁻ t, ∫⁻ z, ENNReal.ofReal ((ell (t+sigma*z))^2) ∂gaussianReal 0 1
        ∂(stratumLaw P x).map latentCentered := by
  haveI := stratumLaw_probability P hoverlap x
  have hT : Measurable (latentCentered (S := S)) := by unfold latentCentered; fun_prop
  have hZT : Measurable (fun w : StructSpace S => (sZ w, latentCentered w)) := by fun_prop
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal ((ell (p.2+sigma*p.1))^2)
  have hF : Measurable F := by fun_prop
  have hprod : (stratumLaw P x).map (fun w => (sZ w, latentCentered w)) =
      (gaussianReal 0 1).prod ((stratumLaw P x).map latentCentered) := by
    rw [error_centered_product_stratum P hoverlap herr x, hgauss]
  calc
    _ = ∫⁻ w, F (sZ w, latentCentered w) ∂stratumLaw P x := by
      apply lintegral_congr
      intro w
      dsimp [F, observedCentered, contaminatedDose, latentCentered]
      congr 3
      ring
    _ = ∫⁻ p, F p ∂(gaussianReal 0 1).prod ((stratumLaw P x).map latentCentered) := by
      rw [← hprod, lintegral_map hF hZT]
    _ = _ := lintegral_prod_symm _ hF.aemeasurable

/-- The upper density envelope bounds each conditional inverse-weight second moment. [Under the stated conditions](hyp:hP,hell). [This is the stated conclusion](goal). -/
-- @node: inverse_square_stratum_le_VqENN
lemma inverse_square_stratum_le_VqENN (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (x : Bool) (ell : ℝ → ℝ) (hell : Measurable ell) :
    (∫⁻ w, ENNReal.ofReal ((ell (observedCentered sigma w))^2) ∂stratumLaw P x) ≤
      pubVqENN K kappa sigma ell := by
  obtain ⟨g, hg, hlaw, henv⟩ := hP.weakDesign
  rw [inverse_square_stratum_lintegral sigma P hP.strataPos
    hP.errorIndependence hP.gaussianChannel x ell hell, hlaw x,
    lintegral_withDensity_eq_lintegral_mul _ (hg x).ennreal_ofReal (by fun_prop)]
  have hchi16 : 0 ≤ K.chi / 16 := div_nonneg (K.clo_pos.le.trans K.clo_le_chi) (by norm_num)
  unfold pubVqENN VqENN
  rw [← lintegral_const_mul' _ _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [henv x] with t ht
  dsimp only [Pi.mul_apply]
  have hupper : ENNReal.ofReal (g x t) ≤
      ENNReal.ofReal (K.chi / 16) * (16 * ENNReal.ofReal (|t|^kappa)) := by
    calc
      _ ≤ ENNReal.ofReal (K.chi / 16 * (16 * |t|^kappa)) :=
        ENNReal.ofReal_le_ofReal (by linarith [ht.2])
      _ = _ := by
        rw [ENNReal.ofReal_mul hchi16, ENNReal.ofReal_mul (by norm_num)]
        norm_num
  calc
    _ ≤ (ENNReal.ofReal (K.chi / 16) * (16 * ENNReal.ofReal (|t|^kappa))) *
        (∫⁻ z, ENNReal.ofReal ((ell (t+sigma*z))^2) ∂gaussianReal 0 1) :=
      by gcongr
    _ = _ := by ring

/-- The unmarked structural stratum mark has second moment at most the public envelope. [Under the stated conditions](hyp:hP,hell). [This is the stated conclusion](goal). -/
-- @node: denominator_square_lintegral_le
lemma denominator_square_lintegral_le (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (x : Bool) (q : WeightPair) (hell : Measurable q.ell) :
    (∫⁻ w, ENNReal.ofReal ((if sX w = x then q.ell (observedCentered sigma w) else 0)^2) ∂P) ≤
      pubVqENN K kappa sigma q.ell := by
  have heq (w : StructSpace S) :
      ENNReal.ofReal ((if sX w = x then q.ell (observedCentered sigma w) else 0)^2) =
        if sX w = x then ENNReal.ofReal ((q.ell (observedCentered sigma w))^2) else 0 := by
    split_ifs <;> simp
  simp_rw [heq]
  rw [stratum_indicator_lintegral P hP.strataPos]
  calc
    _ ≤ 1 * ∫⁻ w, ENNReal.ofReal ((q.ell (observedCentered sigma w))^2) ∂stratumLaw P x :=
      by gcongr; exact prob_le_one
    _ ≤ _ := by
      rw [one_mul]
      exact inverse_square_stratum_le_VqENN E beta kappa sigma P hP x q.ell hell

/-- Bounded realized outcomes make the marked square no larger than the unmarked square. [Under the stated conditions](hyp:hP,hell). [This is the stated conclusion](goal). -/
-- @node: numerator_square_lintegral_le
lemma numerator_square_lintegral_le (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (x : Bool) (q : WeightPair) (hell : Measurable q.ell) :
    (∫⁻ w, ENNReal.ofReal ((if sX w = x then sY w*q.ell (observedCentered sigma w) else 0)^2) ∂P) ≤
      pubVqENN K kappa sigma q.ell := by
  apply le_trans _ (denominator_square_lintegral_le E beta kappa sigma P hP x q hell)
  apply lintegral_mono_ae
  filter_upwards [realized_outcome_mem_Icc E P hP.strataPos
    hP.scheduleUnconfoundedness hP.latentSupport hP.boundedPO hP.consistency] with w hw
  apply ENNReal.ofReal_le_ofReal
  by_cases hx : sX w = x
  · simp only [if_pos hx, mul_pow]
    have hs : (sY w)^2 ≤ 1 := by nlinarith [hw.1, hw.2]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs
      (sq_nonneg (q.ell (observedCentered sigma w)))
  · simp only [if_neg hx, le_refl]

/-- A finite extended second-moment envelope gives genuine square-integrability and a real bound. [Under the stated conditions](hyp:f,hf,hV,V,hbound). [This is the stated conclusion](goal). -/
-- @node: square_integrable_and_integral_le
lemma square_integrable_and_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (V : ℝ≥0∞)
    (hV : V < ⊤) (hbound : (∫⁻ w, ENNReal.ofReal ((f w)^2) ∂μ) ≤ V) :
    MemLp f 2 μ ∧ (∫ w, (f w)^2 ∂μ) ≤ V.toReal := by
  have hn : 0 ≤ᵐ[μ] (fun w => (f w)^2) := ae_of_all _ (fun w => sq_nonneg _)
  have hi : Integrable (fun w => (f w)^2) μ :=
    ⟨(hf.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).mpr (hbound.trans_lt hV)⟩
  refine ⟨(memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable]
  exact ENNReal.toReal_mono hV.ne hbound

/-- The observed denominator mark has a finite square and its public second-moment bound. [Under the stated conditions](hyp:hP,hell,hV). [This is the stated conclusion](goal). -/
-- @node: observed_denominator_second_moment
lemma observed_denominator_second_moment (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (x : Bool) (q : WeightPair) (hell : Measurable q.ell)
    (hV : VqENN kappa sigma q.ell < ⊤) :
    MemLp (fun o : Obs => if o.1 = x then q.ell (o.2.1-a0) else 0) 2 (obsLaw sigma P) ∧
    (∫ o : Obs, (if o.1 = x then q.ell (o.2.1-a0) else 0)^2 ∂obsLaw sigma P) ≤
      pubVq K kappa sigma q.ell := by
  have hm : Measurable (fun o : Obs => if o.1 = x then q.ell (o.2.1-a0) else 0) := by
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      (by fun_prop) measurable_const
  apply square_integrable_and_integral_le _ _ hm _ (pubVqENN_lt_top K kappa sigma _ hV)
  rw [obsLaw, lintegral_map (hm.pow_const 2).ennreal_ofReal (by
    unfold obsMap contaminatedDose; fun_prop)]
  exact denominator_square_lintegral_le E beta kappa sigma P hP x q hell

/-- The observed outcome-marked weight has a finite square and the same public bound. [Under the stated conditions](hyp:hP,hell,hV). [This is the stated conclusion](goal). -/
-- @node: observed_numerator_second_moment
lemma observed_numerator_second_moment (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (x : Bool) (q : WeightPair) (hell : Measurable q.ell)
    (hV : VqENN kappa sigma q.ell < ⊤) :
    MemLp (fun o : Obs => if o.1 = x then o.2.2*q.ell (o.2.1-a0) else 0) 2 (obsLaw sigma P) ∧
    (∫ o : Obs, (if o.1 = x then o.2.2*q.ell (o.2.1-a0) else 0)^2 ∂obsLaw sigma P) ≤
      pubVq K kappa sigma q.ell := by
  have hm : Measurable (fun o : Obs => if o.1 = x then o.2.2*q.ell (o.2.1-a0) else 0) := by
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      (by fun_prop) measurable_const
  apply square_integrable_and_integral_le _ _ hm _ (pubVqENN_lt_top K kappa sigma _ hV)
  rw [obsLaw, lintegral_map (hm.pow_const 2).ennreal_ofReal (by
    unfold obsMap contaminatedDose; fun_prop)]
  exact numerator_square_lintegral_le E beta kappa sigma P hP x q hell

/-- Both observed marks have variance at most the public inverse-weight moment. [Under the stated conditions](hyp:hP,hell,hV). [This is the stated conclusion](goal). -/
-- @node: observed_marks_variance_le
lemma observed_marks_variance_le (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (x : Bool) (q : WeightPair) (hell : Measurable q.ell)
    (hV : VqENN kappa sigma q.ell < ⊤) :
    variance (fun o : Obs => if o.1 = x then q.ell (o.2.1-a0) else 0) (obsLaw sigma P) ≤
      pubVq K kappa sigma q.ell ∧
    variance (fun o : Obs => if o.1 = x then o.2.2*q.ell (o.2.1-a0) else 0) (obsLaw sigma P) ≤
      pubVq K kappa sigma q.ell := by
  have hm : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose; fun_prop
  haveI : IsProbabilityMeasure (obsLaw sigma P) := Measure.isProbabilityMeasure_map hm.aemeasurable
  obtain ⟨hD, hDsq⟩ := observed_denominator_second_moment E beta kappa sigma P hP x q hell hV
  obtain ⟨hM, hMsq⟩ := observed_numerator_second_moment E beta kappa sigma P hP x q hell hV
  exact ⟨(variance_le_expectation_sq hD.aestronglyMeasurable).trans hDsq,
    (variance_le_expectation_sq hM.aestronglyMeasurable).trans hMsq⟩

/-- Averages over disjoint deterministic blocks are independent, even for different marks. [Under the stated conditions](hyp:hbc,f,g,hf,hg). [This is the stated conclusion](goal). -/
-- @node: iid_disjoint_block_averages_indep
lemma iid_disjoint_block_averages_indep {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (b c : Finset (Fin n))
    (hbc : Disjoint b c) (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun data : Fin n → Ω => (∑ i ∈ b, f (data i)) / (b.card : ℝ))
      (fun data : Fin n → Ω => (∑ i ∈ c, g (data i)) / (c.card : ℝ))
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hind : iIndepFun (fun i (data : Fin n → Ω) => data i)
      (Measure.pi (fun _ : Fin n => μ)) := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have h := iIndepFun.indepFun_finset b c hbc hind (fun _ => by fun_prop)
  let F := fun z : b → Ω => (∑ i : b, f (z i)) / (b.card : ℝ)
  let G := fun z : c → Ω => (∑ i : c, g (z i)) / (c.card : ℝ)
  have hF : Measurable F := by fun_prop
  have hG : Measurable G := by fun_prop
  have hcomp := h.comp hF hG
  have heqF : F ∘ (fun data (i : b) => data i) =
      (fun data : Fin n → Ω => (∑ i ∈ b, f (data i)) / (b.card : ℝ)) := by
    funext data
    dsimp [F, Function.comp_def]
    congr 1
    exact Finset.sum_coe_sort b (fun i => f (data i))
  have heqG : G ∘ (fun data (i : c) => data i) =
      (fun data : Fin n → Ω => (∑ i ∈ c, g (data i)) / (c.card : ℝ)) := by
    funext data
    dsimp [G, Function.comp_def]
    congr 1
    exact Finset.sum_coe_sort c (fun i => g (data i))
  rw [heqF, heqG] at hcomp
  exact hcomp

/-- A nonempty deterministic average of square-integrable iid marks is unbiased,
and its variance is the single-mark variance divided by the block size. [Under the stated conditions](hyp:hb,f,hf). [This is the stated conclusion](goal). -/
-- @node: iid_block_average_moments
lemma iid_block_average_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (b : Finset (Fin n))
    (hb : b.Nonempty) (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    let A := fun data : Fin n → Ω => (∑ i ∈ b, f (data i)) / (b.card : ℝ)
    MemLp A 2 (Measure.pi (fun _ : Fin n => μ)) ∧
    (∫ data, A data ∂Measure.pi (fun _ : Fin n => μ)) = ∫ o, f o ∂μ ∧
    variance A (Measure.pi (fun _ : Fin n => μ)) = variance f μ / (b.card : ℝ) := by
  let Q := Measure.pi (fun _ : Fin n => μ)
  let X : Fin n → (Fin n → Ω) → ℝ := fun i data => f (data i)
  have hX (i : Fin n) : MemLp (X i) 2 Q :=
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i)
  have hc : (b.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hb
  have hmean (i : Fin n) : (∫ data, X i data ∂Q) = ∫ o, f o ∂μ := by
    have hp := measurePreserving_eval (fun _ : Fin n => μ) i
    rw [← hp.map_eq, integral_map hp.measurable.aemeasurable]
    simpa only [hp.map_eq] using hf.aestronglyMeasurable
  have hvar (i : Fin n) : variance (X i) Q = variance f μ := by
    have hp := measurePreserving_eval (fun _ : Fin n => μ) i
    rw [← hp.map_eq, variance_map (by simpa only [hp.map_eq] using hf.aemeasurable)
      hp.measurable.aemeasurable]
    rfl
  have hsum : MemLp (fun data => ∑ i ∈ b, X i data) 2 Q :=
    memLp_finsetSum b (fun i _ => hX i)
  have hind : iIndepFun X Q := iIndepFun_pi (fun _ => hf.aemeasurable)
  have hvs : variance (fun data => ∑ i ∈ b, X i data) Q =
      (b.card : ℝ) * variance f μ := by
    have h := IndepFun.variance_sum (s := b) (fun i _ => hX i)
      (fun i hi j hj hij => hind.indepFun hij)
    simp only [hvar, Finset.sum_const, nsmul_eq_mul] at h
    convert h using 1
    congr 1
    funext data
    simp only [Finset.sum_apply]
  refine ⟨by simpa only [div_eq_mul_inv, mul_comm] using hsum.const_mul ((b.card : ℝ)⁻¹), ?_, ?_⟩
  · rw [integral_div, integral_finsetSum b (fun i _ => (hX i).integrable (by norm_num))]
    simp only [hmean, Finset.sum_const, nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ hc
  · simp only [div_eq_mul_inv]
    rw [variance_mul_const, hvs]
    field_simp

/-- Cauchy--Schwarz bounds expected absolute deviation by the square root of variance. [Under the stated conditions](hyp:f,hf). [This is the stated conclusion](goal). -/
-- @node: expected_abs_deviation_le_sqrt_variance
lemma expected_abs_deviation_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    (∫ w, |f w - ∫ o, f o ∂μ| ∂μ) ≤ Real.sqrt (variance f μ) := by
  let g := fun w => |f w - ∫ o, f o ∂μ|
  have hdiff : MemLp (fun w => f w - ∫ o, f o ∂μ) 2 μ :=
    hf.sub (memLp_const _)
  have hg : MemLp g 2 μ := by
    simpa only [Real.norm_eq_abs] using hdiff.norm
  have hid : (∫ w, (g w)^2 ∂μ) = variance f μ := by
    rw [variance_eq_integral hf.aemeasurable]
    simp only [g, sq_abs]
  have hsq : (∫ w, g w ∂μ)^2 ≤ variance f μ := by
    have h := variance_nonneg g μ
    rw [variance_eq_sub hg] at h
    simp only [Pi.pow_apply] at h
    rw [hid] at h
    linarith
  have hn : 0 ≤ ∫ w, g w ∂μ := integral_nonneg (fun _ => abs_nonneg _)
  have hs := Real.sq_sqrt (variance_nonneg f μ)
  have hp := Real.sqrt_nonneg (variance f μ)
  change (∫ w, g w ∂μ) ≤ _
  nlinarith

/-- The denominator block is unbiased and has variance at most Vq divided by its size. [Under the stated conditions](hyp:hP,hell,hV,hb). [This is the stated conclusion](goal). -/
-- @node: Dhat_population_moments
lemma Dhat_population_moments (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (n : ℕ) (hb : (splitBlock n 1).Nonempty) (x : Bool) (q : WeightPair)
    (hell : Measurable q.ell) (hV : VqENN kappa sigma q.ell < ⊤) :
    MemLp (fun data => Dhat n data x q) 2 (experiment n sigma P) ∧
    (∫ data, Dhat n data x q ∂experiment n sigma P) = populationD sigma P x q ∧
    variance (fun data => Dhat n data x q) (experiment n sigma P) ≤
      pubVq K kappa sigma q.ell / (splitBlock n 1).card := by
  have hm : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose; fun_prop
  haveI : IsProbabilityMeasure (obsLaw sigma P) := Measure.isProbabilityMeasure_map hm.aemeasurable
  obtain ⟨hmem, hsq⟩ := observed_denominator_second_moment E beta kappa sigma P hP x q hell hV
  obtain ⟨hA, hmean, hvar⟩ := iid_block_average_moments (obsLaw sigma P) n
    (splitBlock n 1) hb _ hmem
  refine ⟨hA, ?_, ?_⟩
  · dsimp only [Dhat, Mhat, experiment]
    rw [hmean, obsLaw, integral_map hm.aemeasurable hmem.aestronglyMeasurable]
    rfl
  · dsimp only [Dhat, Mhat, experiment]
    rw [hvar]
    exact div_le_div_of_nonneg_right
      ((variance_le_expectation_sq hmem.aestronglyMeasurable).trans hsq) (Nat.cast_nonneg _)

/-- The outcome-marked block is unbiased and obeys the same variance envelope. [Under the stated conditions](hyp:hP,hell,hV,hb). [This is the stated conclusion](goal). -/
-- @node: Mhat_population_moments
lemma Mhat_population_moments (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (n : ℕ) (hb : (splitBlock n 2).Nonempty) (x : Bool) (q : WeightPair)
    (hell : Measurable q.ell) (hV : VqENN kappa sigma q.ell < ⊤) :
    MemLp (fun data => Mhat n data x q) 2 (experiment n sigma P) ∧
    (∫ data, Mhat n data x q ∂experiment n sigma P) = populationM sigma P x q ∧
    variance (fun data => Mhat n data x q) (experiment n sigma P) ≤
      pubVq K kappa sigma q.ell / (splitBlock n 2).card := by
  have hm : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose; fun_prop
  haveI : IsProbabilityMeasure (obsLaw sigma P) := Measure.isProbabilityMeasure_map hm.aemeasurable
  obtain ⟨hmem, hsq⟩ := observed_numerator_second_moment E beta kappa sigma P hP x q hell hV
  obtain ⟨hA, hmean, hvar⟩ := iid_block_average_moments (obsLaw sigma P) n
    (splitBlock n 2) hb _ hmem
  refine ⟨hA, ?_, ?_⟩
  · dsimp only [Dhat, Mhat, experiment]
    rw [hmean, obsLaw, integral_map hm.aemeasurable hmem.aestronglyMeasurable]
    rfl
  · dsimp only [Dhat, Mhat, experiment]
    rw [hvar]
    exact div_le_div_of_nonneg_right
      ((variance_le_expectation_sq hmem.aestronglyMeasurable).trans hsq) (Nat.cast_nonneg _)

/-- Absolute error of each empirical inverse moment is bounded by its public standard deviation. [Under the stated conditions](hyp:hP,hell,hV,hb1,hb2). [This is the stated conclusion](goal). -/
-- @node: inverse_moments_expected_abs_error
lemma inverse_moments_expected_abs_error (E : PathSpace S) (beta kappa sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (n : ℕ) (hb1 : (splitBlock n 1).Nonempty) (hb2 : (splitBlock n 2).Nonempty)
    (x : Bool) (q : WeightPair) (hell : Measurable q.ell)
    (hV : VqENN kappa sigma q.ell < ⊤) :
    (∫ data, |Dhat n data x q - populationD sigma P x q| ∂experiment n sigma P) ≤
      Real.sqrt (pubVq K kappa sigma q.ell / (splitBlock n 1).card) ∧
    (∫ data, |Mhat n data x q - populationM sigma P x q| ∂experiment n sigma P) ≤
      Real.sqrt (pubVq K kappa sigma q.ell / (splitBlock n 2).card) := by
  have hm : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose; fun_prop
  haveI : IsProbabilityMeasure (obsLaw sigma P) := Measure.isProbabilityMeasure_map hm.aemeasurable
  haveI : IsProbabilityMeasure (experiment n sigma P) := by unfold experiment; infer_instance
  obtain ⟨hD, hDmean, hDv⟩ := Dhat_population_moments E beta kappa sigma P hP n hb1 x q hell hV
  obtain ⟨hM, hMmean, hMv⟩ := Mhat_population_moments E beta kappa sigma P hP n hb2 x q hell hV
  constructor
  · have h := expected_abs_deviation_le_sqrt_variance _ _ hD
    rw [hDmean] at h
    exact h.trans (Real.sqrt_le_sqrt hDv)
  · have h := expected_abs_deviation_le_sqrt_variance _ _ hM
    rw [hMmean] at h
    exact h.trans (Real.sqrt_le_sqrt hMv)

/-- Empirical stratum frequency is unbiased with the Bernoulli variance bound. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hb). -/
-- @node: phat_population_moments
lemma phat_population_moments (sigma : ℝ) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (n : ℕ) (hb : (splitBlock n 0).Nonempty) (x : Bool) :
    MemLp (fun data => phat n data x) 2 (experiment n sigma P) ∧
    (∫ data, phat n data x ∂experiment n sigma P) = strataProb P x ∧
    variance (fun data => phat n data x) (experiment n sigma P) ≤
      (1/4 : ℝ) / (splitBlock n 0).card := by
  have hm : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose; fun_prop
  haveI : IsProbabilityMeasure (obsLaw sigma P) := Measure.isProbabilityMeasure_map hm.aemeasurable
  let f : Obs → ℝ := fun o => if o.1 = x then 1 else 0
  have hf : Measurable f := Measurable.ite
    (measurableSet_eq_fun (by fun_prop) measurable_const) measurable_const measurable_const
  have hr : ∀ o, f o ∈ Icc (0 : ℝ) 1 := by intro o; dsimp [f]; split_ifs <;> norm_num
  have hmem : MemLp f 2 (obsLaw sigma P) := memLp_of_bounded (ae_of_all _ hr) hf.aestronglyMeasurable 2
  have hv : variance f (obsLaw sigma P) ≤ 1/4 := by
    have h := variance_le_sq_of_bounded (μ := obsLaw sigma P) (ae_of_all _ hr) hf.aemeasurable
    norm_num at h
    exact h
  have hmean : (∫ o, f o ∂obsLaw sigma P) = strataProb P x := by
    rw [obsLaw, integral_map hm.aemeasurable hf.aestronglyMeasurable]
    change (∫ w, (if sX w = x then (1 : ℝ) else 0) ∂P) = _
    have hx : MeasurableSet {w : StructSpace S | sX w = x} :=
      measurableSet_eq_fun (by fun_prop) measurable_const
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, setIntegral_const, smul_eq_mul, mul_one, strataProb]
      using integral_indicator_const (μ := P) (1 : ℝ) hx
  obtain ⟨hA, hAmean, hAv⟩ := iid_block_average_moments (obsLaw sigma P) n (splitBlock n 0) hb f hmem
  refine ⟨hA, ?_, ?_⟩
  · dsimp only [phat, experiment]
    exact hAmean.trans hmean
  · dsimp only [phat, experiment]
    rw [hAv]
    exact div_le_div_of_nonneg_right hv (Nat.cast_nonneg _)

end CausalSmith.Stat.NoisydoseWeakdesignTransition
