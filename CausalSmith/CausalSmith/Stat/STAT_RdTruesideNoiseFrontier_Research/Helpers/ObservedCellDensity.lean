module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.MarkedCells
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.MarkedDomination
public import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# Observed-cell densities for the cancellation witnesses

This file derives the treated observed-cell law from the concrete Bernoulli
product witness and the independent Gaussian error.  The resulting density is
the convolution already used by the marked-likelihood estimates.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Given [the displayed inputs and assumptions](hyp:p,y), [this definition specifies the stated object](goal). -/
def treatedLatentCell (p : ℝ → ℝ) (y : Bool) : Measure ℝ :=
  (uniformScore.restrict (Ici 0)).withDensity
    (fun x => ENNReal.ofReal (if y then p x else 1 - p x))

/-- Given [the displayed inputs and assumptions](hyp:p,y,x), [this definition specifies the stated object](goal). -/
def treatedCellBaseDensity (p : ℝ → ℝ) (y : Bool) (x : ℝ) : ℝ≥0∞ :=
  (Icc (0 : ℝ) 1).indicator (fun x =>
    ENNReal.ofReal (1/2 : ℝ) * ENNReal.ofReal (if y then p x else 1-p x)) x

/-- Given [the displayed inputs and assumptions](hyp:sigma,w), [this definition specifies the stated object](goal). -/
def proxyNoiseDensity (sigma w : ℝ) : ℝ≥0∞ := ENNReal.ofReal (phi sigma w)

/-- Given [the displayed inputs and assumptions](hyp:sigma,hsigma), [the stated mathematical conclusion holds](goal). -/
lemma scaledGaussian_eq_withDensity (sigma : ℝ) (hsigma : 0 < sigma) :
    (gaussianReal 0 1).map (fun z => sigma * z) =
      volume.withDensity (proxyNoiseDensity sigma) := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  have hv : NNReal.mk (sigma^2) (sq_nonneg sigma) ≠ 0 := by
    rw [ne_eq, ← NNReal.coe_eq_zero]
    simp [hsigma.ne']
  rw [gaussianReal_of_var_ne_zero 0 hv]
  congr 2
  funext w
  rw [gaussianPDF_def]
  exact congrArg ENNReal.ofReal (phi_eq_gaussianPDFReal sigma w).symm

/-- Given [the displayed inputs and assumptions](hyp:p,hp,hb,sigma,y,w), [the stated mathematical conclusion holds](goal). -/
lemma treated_lconvolution_eq_witness
    (p : ℝ → ℝ) (hp : Continuous p)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1)
    (sigma : ℝ) (y : Bool) (w : ℝ) :
    (treatedCellBaseDensity p y ⋆ₗ[volume] proxyNoiseDensity sigma) w =
      ENNReal.ofReal ((1/2 : ℝ) * ∫ x in (0 : ℝ)..1,
        (if y then p x else 1-p x) * phi sigma (w-x)) := by
  rw [MeasureTheory.lconvolution_def]
  simp only [treatedCellBaseDensity, proxyNoiseDensity]
  have hind : (fun x : ℝ =>
      (Icc (0 : ℝ) 1).indicator (fun x =>
        ENNReal.ofReal (1/2 : ℝ) * ENNReal.ofReal (if y then p x else 1-p x)) x *
          ENNReal.ofReal (phi sigma (-x+w))) =
      (Icc (0 : ℝ) 1).indicator (fun x =>
        (ENNReal.ofReal (1/2 : ℝ) * ENNReal.ofReal (if y then p x else 1-p x)) *
          ENNReal.ofReal (phi sigma (-x+w))) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [Set.indicator, hx]
  rw [hind]
  rw [lintegral_indicator measurableSet_Icc]
  let q : ℝ → ℝ := fun x => if y then p x else 1-p x
  let f : ℝ → ℝ := fun x => (1/2 : ℝ) * q x * phi sigma (-x+w)
  have hq_cont : Continuous q := by
    cases y
    · change Continuous (fun x => 1-p x)
      fun_prop
    · simpa [q] using hp
  have hf_cont : Continuous f := by
    unfold f
    fun_prop
  have hf_int : IntegrableOn f (Icc (0 : ℝ) 1) := hf_cont.integrableOn_Icc
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hq0 : 0 ≤ q x := by
      cases y
      · simpa [q] using sub_nonneg.mpr (hb x hx).2
      · simpa [q] using (hb x hx).1
    exact mul_nonneg (mul_nonneg (by norm_num) hq0) (phi_nonneg sigma _)
  have heq : (fun x =>
      ENNReal.ofReal (1/2 : ℝ) * ENNReal.ofReal (q x) *
        ENNReal.ofReal (phi sigma (-x+w))) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      fun x => ENNReal.ofReal (f x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hq0 : 0 ≤ q x := by
      cases y
      · simpa [q] using sub_nonneg.mpr (hb x hx).2
      · simpa [q] using (hb x hx).1
    unfold f
    rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1/2 : ℝ)),
      ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hq0)]
  change (∫⁻ x in Icc (0 : ℝ) 1,
    ENNReal.ofReal (1/2 : ℝ) * ENNReal.ofReal (q x) *
      ENNReal.ofReal (phi sigma (-x+w))) = _
  rw [lintegral_congr_ae heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hf_int hf_nonneg]
  apply congrArg ENNReal.ofReal
  unfold f q
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have harg : -x+w = w-x := by ring
  rw [harg]
  ring

/-- Given [the displayed inputs and assumptions](hyp:p,y,hp), [the stated mathematical conclusion holds](goal). -/
lemma treatedLatentCell_eq_withDensity (p : ℝ → ℝ) (y : Bool) (hp : Measurable p) :
    treatedLatentCell p y = volume.withDensity (treatedCellBaseDensity p y) := by
  have hq : Measurable (fun x : ℝ => ENNReal.ofReal (if y then p x else 1-p x)) := by
    cases y
    · simpa using (measurable_const.sub hp).ennreal_ofReal
    · simpa using hp.ennreal_ofReal
  have hrestrict : uniformScore.restrict (Ici 0) =
      ENNReal.ofReal (1/2 : ℝ) • volume.restrict (Icc 0 1) := by
    unfold uniformScore
    rw [Measure.restrict_smul, Measure.restrict_restrict measurableSet_Ici]
    congr 2
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨hx0, _hxneg, hx1⟩
      exact ⟨hx0, hx1⟩
    · rintro ⟨hx0, hx1⟩
      exact ⟨hx0, by linarith, hx1⟩
  unfold treatedLatentCell
  rw [hrestrict, withDensity_smul_measure]
  rw [← withDensity_smul _ hq]
  rw [← withDensity_indicator measurableSet_Icc]
  congr 2

/-- Given [the displayed inputs and assumptions](hyp:L,sigma,d,y), [this definition specifies the stated object](goal). -/
def observedCellMeasure (L : LatentLaw) (sigma : ℝ) (d y : Bool) : Measure ℝ :=
  ((Pobs L sigma).restrict {o | o.2.1 = d ∧ o.2.2 = y}).map Prod.fst

/-- Given [the displayed inputs and assumptions](hyp:d,y), [the stated mathematical conclusion holds](goal). -/
lemma measurableSet_observedCell (d y : Bool) :
    MeasurableSet {o : Obs | o.2.1 = d ∧ o.2.2 = y} := by
  exact ((measurableSet_singleton d).preimage (measurable_fst.comp measurable_snd)).inter
    ((measurableSet_singleton y).preimage (measurable_snd.comp measurable_snd))

/-- Given [the displayed inputs and assumptions](hyp:p,y,hp), [the stated mathematical conclusion holds](goal). -/
lemma schedule_treated_cell_eq (p : ℝ → ℝ) (y : Bool) (hp : Measurable p) :
    let M₀ := uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2)
    let M₁ := M₀ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun z : ℝ × Bool => p z.1)
    (M₁.restrict {z | 0 ≤ z.1.1 ∧ z.2 = y}).map (fun z => z.1.1) = treatedLatentCell p y := by
  dsimp only
  letI := uniformScore_probability
  let M₀ := uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2)
  have hM₀ : M₀.map Prod.fst = uniformScore :=
    bernoulli_compProd_fst uniformScore _ measurable_const (by
      filter_upwards [] with x
      norm_num)
  ext A hA
  rw [Measure.map_apply (by fun_prop) hA]
  rw [Measure.restrict_apply]
  swap
  · exact hA.preimage (measurable_fst.comp measurable_fst)
  have hpre : (fun z : (ℝ × Bool) × Bool => z.1.1) ⁻¹' A ∩
      {z | 0 ≤ z.1.1 ∧ z.2 = y} =
      (Prod.fst ⁻¹' (A ∩ Ici 0)) ×ˢ ({y} : Set Bool) := by
    ext z
    simp [and_left_comm, and_comm]
  rw [hpre, Measure.compProd_apply_prod
    ((hA.inter measurableSet_Ici).preimage measurable_fst) (measurableSet_singleton y)]
  cases y
  · simp_rw [Causalean.Mathlib.Probability.bernoulliMarkKernel_apply_false
      (fun z : ℝ × Bool => p z.1) (hp.comp measurable_fst)]
    change (∫⁻ z in Prod.fst ⁻¹' (A ∩ Ici 0), ENNReal.ofReal (1 - p z.1) ∂M₀) = _
    have hmap := MeasureTheory.setLIntegral_map (f := fun x : ℝ => ENNReal.ofReal (1-p x))
      (g := Prod.fst) (hA.inter (measurableSet_Ici : MeasurableSet (Ici (0 : ℝ))))
      (measurable_const.sub hp).ennreal_ofReal measurable_fst (μ := M₀)
    rw [hM₀] at hmap
    rw [← hmap]
    unfold treatedLatentCell
    rw [withDensity_apply _ hA]
    simp only [Bool.false_eq_true, if_false]
    rw [Measure.restrict_restrict hA]
  · simp_rw [Causalean.Mathlib.Probability.bernoulliMarkKernel_apply_true
      (fun z : ℝ × Bool => p z.1) (hp.comp measurable_fst)]
    change (∫⁻ z in Prod.fst ⁻¹' (A ∩ Ici 0), ENNReal.ofReal (p z.1) ∂M₀) = _
    have hmap := MeasureTheory.setLIntegral_map (f := fun x : ℝ => ENNReal.ofReal (p x))
      (g := Prod.fst) (hA.inter (measurableSet_Ici : MeasurableSet (Ici (0 : ℝ))))
      hp.ennreal_ofReal measurable_fst (μ := M₀)
    rw [hM₀] at hmap
    rw [← hmap]
    unfold treatedLatentCell
    rw [withDensity_apply _ hA]
    simp only [if_true]
    rw [Measure.restrict_restrict hA]

/-- Given [the displayed inputs and assumptions](hyp:p,hp,hc,hb,sigma,y), [the stated mathematical conclusion holds](goal). -/
lemma witness_observed_treated_cell_eq_conv
    (p : ℝ → ℝ) (hp : Measurable p) (hc : ContinuousOn p (Icc (-1) 1))
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1) (sigma : ℝ) (y : Bool) :
    observedCellMeasure (bernoulliWitness p hp hc hb) sigma true y =
      treatedLatentCell p y ∗ (gaussianReal 0 1).map (fun z => sigma * z) := by
  letI := uniformScore_probability
  let M₀ := uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2)
  let M₁ := M₀ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel (fun z : ℝ × Bool => p z.1)
  let pack : ((ℝ × Bool) × Bool) × ℝ → Latent :=
    fun z => (z.1.1.1, z.1.1.2, z.1.2, z.2)
  let cell : Set Obs := {o | o.2.1 = true ∧ o.2.2 = y}
  let schedCell : Set ((ℝ × Bool) × Bool) := {z | 0 ≤ z.1.1 ∧ z.2 = y}
  have hcell : MeasurableSet cell := measurableSet_observedCell true y
  have hsched : MeasurableSet schedCell := by
    exact ((measurableSet_Ici.preimage (measurable_fst.comp measurable_fst)).inter
      ((measurableSet_singleton y).preimage measurable_snd))
  have hpre : pack ⁻¹' (obs sigma ⁻¹' cell) = schedCell ×ˢ (univ : Set ℝ) := by
    ext z
    simp only [pack, obs, cell, schedCell, Set.mem_preimage, Set.mem_ofPred_eq,
      Set.mem_prod, Set.mem_univ, and_true, side, score, outcome]
    by_cases hx : 0 ≤ z.1.1.1
    · simp [hx]
    · simp [hx]
  unfold observedCellMeasure Pobs
  change Measure.map Prod.fst
    ((Measure.map (obs sigma) (witnessMeasure p)).restrict cell) = _
  rw [Measure.restrict_map (obs_measurable sigma) hcell]
  rw [Measure.map_map measurable_fst (obs_measurable sigma)]
  unfold witnessMeasure
  rw [Measure.restrict_map (by fun_prop) (hcell.preimage (obs_measurable sigma))]
  rw [Measure.map_map ((measurable_fst.comp (obs_measurable sigma))) (by fun_prop)]
  change Measure.map _ ((M₁.prod (gaussianReal 0 1)).restrict
      (pack ⁻¹' (obs sigma ⁻¹' cell))) = _
  rw [hpre, ← Measure.restrict_prod_eq_prod_univ]
  rw [← schedule_treated_cell_eq p y hp]
  change Measure.map _ ((M₁.restrict schedCell).prod (gaussianReal 0 1)) =
    Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
      ((Measure.map (fun z => z.1.1) (M₁.restrict schedCell)).prod
        (Measure.map (fun z => sigma * z) (gaussianReal 0 1)))
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [] with z
  rfl

/-- Given [the displayed inputs and assumptions](hyp:hleg,beta,b,sigma,m,s,y,hbeta,hb,hm,hsigma), [the stated mathematical conclusion holds](goal). -/
lemma altLaw_observed_treated_cell_density
    (hleg : ClassicalLegendreFacts) (beta b sigma : ℝ) (m : ℕ) (s y : Bool)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsigma : 0 < sigma) :
    observedCellMeasure (altLaw hleg beta b m s hbeta hb hm) sigma true y =
      volume.withDensity (fun w => ENNReal.ofReal
        (witnessTreatedCellConvolution beta b sigma m s y w)) := by
  let p := altProbability beta b m s
  have hprops := altProbability_properties hleg beta b m s hbeta hb hm
  have hpcont : Continuous p := altProbability_continuous beta b m s hb.1
  have hbase : Measurable (treatedCellBaseDensity p y) := by
    unfold treatedCellBaseDensity
    apply Measurable.indicator
    · have hq : Measurable (fun x => ENNReal.ofReal (if y then p x else 1-p x)) := by
        cases y
        · simpa using (measurable_const.sub hprops.1).ennreal_ofReal
        · simpa using hprops.1.ennreal_ofReal
      exact measurable_const.mul hq
    · exact measurableSet_Icc
  have hnoise : Measurable (proxyNoiseDensity sigma) := by
    exact (phi_continuous sigma).measurable.ennreal_ofReal
  unfold altLaw
  rw [witness_observed_treated_cell_eq_conv p hprops.1 hprops.2.1 hprops.2.2]
  rw [treatedLatentCell_eq_withDensity p y hprops.1]
  rw [scaledGaussian_eq_withDensity sigma hsigma]
  rw [MeasureTheory.conv_withDensity_eq_lconvolution hbase hnoise]
  congr 2
  funext w
  simpa only [p, witnessTreatedCellConvolution] using
    treated_lconvolution_eq_witness p hpcont (fun x hx => hprops.2.2 x
      ⟨by linarith [hx.1], hx.2⟩) sigma y w

/-- The negative-score, fair-outcome latent cell, independent of the treated mark. Given the displayed inputs, [this definition specifies the stated object](goal). -/
def controlLatentCell : Measure ℝ :=
  (uniformScore.restrict (Iio 0)).withDensity (fun _ => ENNReal.ofReal (1/2 : ℝ))

/-- Common observed density of either untreated outcome cell. Given [the displayed inputs and assumptions](hyp:sigma,w), [this definition specifies the stated object](goal). -/
def witnessControlCellConvolution (sigma w : ℝ) : ℝ :=
  (1/4 : ℝ) * ∫ x in (-1 : ℝ)..0, phi sigma (w-x)

/-- Given [the displayed inputs and assumptions](hyp:x), [this definition specifies the stated object](goal). -/
def controlCellBaseDensity (x : ℝ) : ℝ≥0∞ :=
  (Ico (-1 : ℝ) 0).indicator (fun _ => ENNReal.ofReal (1/4 : ℝ)) x

/-- Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
lemma controlLatentCell_eq_withDensity :
    controlLatentCell = volume.withDensity controlCellBaseDensity := by
  have hrestrict : uniformScore.restrict (Iio 0) =
      ENNReal.ofReal (1/2 : ℝ) • volume.restrict (Ico (-1) 0) := by
    unfold uniformScore
    rw [Measure.restrict_smul, Measure.restrict_restrict measurableSet_Iio]
    congr 2
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨hx0, hxneg, _hx1⟩
      exact ⟨hxneg, hx0⟩
    · rintro ⟨hxneg, hx0⟩
      exact ⟨hx0, hxneg, by linarith⟩
  unfold controlLatentCell
  rw [hrestrict, withDensity_smul_measure]
  rw [← withDensity_smul _ measurable_const]
  rw [← withDensity_indicator measurableSet_Ico]
  congr 2
  funext x
  simp only [controlCellBaseDensity, Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1/2 : ℝ))]
  norm_num

/-- Given [the displayed inputs and assumptions](hyp:sigma,w), [the stated mathematical conclusion holds](goal). -/
lemma control_lconvolution_eq (sigma w : ℝ) :
    (controlCellBaseDensity ⋆ₗ[volume] proxyNoiseDensity sigma) w =
      ENNReal.ofReal (witnessControlCellConvolution sigma w) := by
  rw [MeasureTheory.lconvolution_def]
  simp only [controlCellBaseDensity, proxyNoiseDensity]
  have hind : (fun x : ℝ =>
      (Ico (-1 : ℝ) 0).indicator (fun _ => ENNReal.ofReal (1/4 : ℝ)) x *
        ENNReal.ofReal (phi sigma (-x+w))) =
      (Ico (-1 : ℝ) 0).indicator (fun x =>
        ENNReal.ofReal (1/4 : ℝ) * ENNReal.ofReal (phi sigma (-x+w))) := by
    funext x
    by_cases hx : x ∈ Ico (-1 : ℝ) 0 <;> simp [Set.indicator, hx]
  rw [hind, lintegral_indicator measurableSet_Ico]
  let f : ℝ → ℝ := fun x => (1/4 : ℝ) * phi sigma (-x+w)
  have hf_cont : Continuous f := by
    unfold f
    fun_prop
  have hf_int : IntegrableOn f (Ico (-1 : ℝ) 0) :=
    hf_cont.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Ico (-1 : ℝ) 0)] f := by
    filter_upwards [] with x
    exact mul_nonneg (by norm_num) (phi_nonneg sigma _)
  have heq : (fun x => ENNReal.ofReal (1/4 : ℝ) *
      ENNReal.ofReal (phi sigma (-x+w))) =ᵐ[volume.restrict (Ico (-1 : ℝ) 0)]
      fun x => ENNReal.ofReal (f x) := by
    filter_upwards [] with x
    unfold f
    rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1/4 : ℝ))]
  rw [lintegral_congr_ae heq, ← ofReal_integral_eq_lintegral_ofReal hf_int hf_nonneg]
  apply congrArg ENNReal.ofReal
  unfold witnessControlCellConvolution f
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0),
    integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have harg : -x+w = w-x := by ring
  rw [harg]

/-- Given [the displayed inputs and assumptions](hyp:p,hp,hb,y), [the stated mathematical conclusion holds](goal). -/
lemma schedule_control_cell_eq
    (p : ℝ → ℝ) (hp : Measurable p)
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1) (y : Bool) :
    let M₀ := uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel
      (fun _ : ℝ => 1/2)
    let M₁ := M₀ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel
      (fun z : ℝ × Bool => p z.1)
    (M₁.restrict {z | z.1.1 < 0 ∧ z.1.2 = y}).map (fun z => z.1.1) =
      controlLatentCell := by
  dsimp only
  letI := uniformScore_probability
  let M₀ := uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel
    (fun _ : ℝ => 1/2)
  let M₁ := M₀ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel
    (fun z : ℝ × Bool => p z.1)
  have hpM₀ : ∀ᵐ z ∂M₀, 0 ≤ p z.1 ∧ p z.1 ≤ 1 := by
    apply Measure.ae_compProd_of_ae_fst
      (Causalean.Mathlib.Probability.bernoulliMarkKernel (fun _ : ℝ => 1/2))
      ((measurableSet_le measurable_const hp).inter (measurableSet_le hp measurable_const))
    filter_upwards [uniformScore_support] with x hx using hb x hx
  have hM₁ : M₁.map Prod.fst = M₀ :=
    bernoulli_compProd_fst M₀ _ (hp.comp measurable_fst) hpM₀
  have hM₀ : M₀.map Prod.fst = uniformScore :=
    bernoulli_compProd_fst uniformScore _ measurable_const (by
      filter_upwards [] with x
      norm_num)
  ext A hA
  rw [Measure.map_apply (by fun_prop) hA]
  rw [Measure.restrict_apply]
  swap
  · exact hA.preimage (measurable_fst.comp measurable_fst)
  have hpre : (fun z : (ℝ × Bool) × Bool => z.1.1) ⁻¹' A ∩
      {z | z.1.1 < 0 ∧ z.1.2 = y} =
      Prod.fst ⁻¹' {z : ℝ × Bool | z.1 ∈ A ∩ Iio 0 ∧ z.2 = y} := by
    ext z
    simp [and_left_comm, and_comm]
  rw [hpre]
  change M₁ (Prod.fst ⁻¹' ((A ∩ Iio 0) ×ˢ ({y} : Set Bool))) = _
  rw [← Measure.map_apply measurable_fst
    ((hA.inter measurableSet_Iio).prod (measurableSet_singleton y)), hM₁]
  change M₀ ((A ∩ Iio 0) ×ˢ ({y} : Set Bool)) = controlLatentCell A
  rw [Measure.compProd_apply_prod (hA.inter measurableSet_Iio)
    (measurableSet_singleton y)]
  cases y
  · simp_rw [Causalean.Mathlib.Probability.bernoulliMarkKernel_apply_false
      (fun _ : ℝ => 1/2) measurable_const]
    unfold controlLatentCell
    rw [withDensity_apply _ hA, Measure.restrict_restrict hA]
    norm_num
  · simp_rw [Causalean.Mathlib.Probability.bernoulliMarkKernel_apply_true
      (fun _ : ℝ => 1/2) measurable_const]
    change (∫⁻ _x in A ∩ Iio 0, ENNReal.ofReal (1/2 : ℝ) ∂uniformScore) = _
    unfold controlLatentCell
    rw [withDensity_apply _ hA, Measure.restrict_restrict hA]

/-- Given [the displayed inputs and assumptions](hyp:p,hp,hc,hb,sigma,y), [the stated mathematical conclusion holds](goal). -/
lemma witness_observed_control_cell_eq_conv
    (p : ℝ → ℝ) (hp : Measurable p) (hc : ContinuousOn p (Icc (-1) 1))
    (hb : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ p x ∧ p x ≤ 1)
    (sigma : ℝ) (y : Bool) :
    observedCellMeasure (bernoulliWitness p hp hc hb) sigma false y =
      controlLatentCell ∗ (gaussianReal 0 1).map (fun z => sigma * z) := by
  letI := uniformScore_probability
  let M₀ := uniformScore ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel
    (fun _ : ℝ => 1/2)
  let M₁ := M₀ ⊗ₘ Causalean.Mathlib.Probability.bernoulliMarkKernel
    (fun z : ℝ × Bool => p z.1)
  let pack : ((ℝ × Bool) × Bool) × ℝ → Latent :=
    fun z => (z.1.1.1, z.1.1.2, z.1.2, z.2)
  let cell : Set Obs := {o | o.2.1 = false ∧ o.2.2 = y}
  let schedCell : Set ((ℝ × Bool) × Bool) := {z | z.1.1 < 0 ∧ z.1.2 = y}
  have hcell : MeasurableSet cell := measurableSet_observedCell false y
  have hsched : MeasurableSet schedCell := by
    exact ((measurableSet_Iio.preimage (measurable_fst.comp measurable_fst)).inter
      ((measurableSet_singleton y).preimage (measurable_snd.comp measurable_fst)))
  have hpre : pack ⁻¹' (obs sigma ⁻¹' cell) = schedCell ×ˢ (univ : Set ℝ) := by
    ext z
    simp only [pack, obs, cell, schedCell, Set.mem_preimage, Set.mem_ofPred_eq,
      Set.mem_prod, Set.mem_univ, and_true, side, score, outcome]
    by_cases hx : 0 ≤ z.1.1.1
    · simp [hx]
    · simp [hx, lt_of_not_ge hx]
  unfold observedCellMeasure Pobs
  change Measure.map Prod.fst
    ((Measure.map (obs sigma) (witnessMeasure p)).restrict cell) = _
  rw [Measure.restrict_map (obs_measurable sigma) hcell]
  rw [Measure.map_map measurable_fst (obs_measurable sigma)]
  unfold witnessMeasure
  rw [Measure.restrict_map (by fun_prop) (hcell.preimage (obs_measurable sigma))]
  rw [Measure.map_map (measurable_fst.comp (obs_measurable sigma)) (by fun_prop)]
  change Measure.map _ ((M₁.prod (gaussianReal 0 1)).restrict
      (pack ⁻¹' (obs sigma ⁻¹' cell))) = _
  rw [hpre, ← Measure.restrict_prod_eq_prod_univ]
  rw [← schedule_control_cell_eq p hp hb y]
  change Measure.map _ ((M₁.restrict schedCell).prod (gaussianReal 0 1)) =
    Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
      ((Measure.map (fun z => z.1.1) (M₁.restrict schedCell)).prod
        (Measure.map (fun z => sigma * z) (gaussianReal 0 1)))
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [] with z
  rfl

/-- Given [the displayed inputs and assumptions](hyp:hleg,beta,b,sigma,m,s,y,hbeta,hb,hm,hsigma), [the stated mathematical conclusion holds](goal). -/
lemma altLaw_observed_control_cell_density
    (hleg : ClassicalLegendreFacts) (beta b sigma : ℝ) (m : ℕ) (s y : Bool)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsigma : 0 < sigma) :
    observedCellMeasure (altLaw hleg beta b m s hbeta hb hm) sigma false y =
      volume.withDensity (fun w => ENNReal.ofReal
        (witnessControlCellConvolution sigma w)) := by
  let p := altProbability beta b m s
  have hprops := altProbability_properties hleg beta b m s hbeta hb hm
  have hbase : Measurable controlCellBaseDensity := by
    unfold controlCellBaseDensity
    exact measurable_const.indicator measurableSet_Ico
  have hnoise : Measurable (proxyNoiseDensity sigma) :=
    (phi_continuous sigma).measurable.ennreal_ofReal
  unfold altLaw
  rw [witness_observed_control_cell_eq_conv p hprops.1 hprops.2.1 hprops.2.2]
  rw [controlLatentCell_eq_withDensity]
  rw [scaledGaussian_eq_withDensity sigma hsigma]
  rw [MeasureTheory.conv_withDensity_eq_lconvolution hbase hnoise]
  congr 2
  funext w
  exact control_lconvolution_eq sigma w

/-- Given [the displayed inputs and assumptions](hyp:d,y), [this definition specifies the stated object](goal). -/
def observedCell (d y : Bool) : Set Obs :=
  {o | o.2.1 = d ∧ o.2.2 = y}

/-- Given [the displayed inputs and assumptions](hyp:d,y,w), [this definition specifies the stated object](goal). -/
def observedCellEmbed (d y : Bool) (w : ℝ) : Obs := (w, d, y)

/-- Given [the displayed inputs and assumptions](hyp:L,sigma,d,y,A,hA), [the stated mathematical conclusion holds](goal). -/
lemma observedCellMeasure_apply_preimage
    (L : LatentLaw) (sigma : ℝ) (d y : Bool) (A : Set Obs) (hA : MeasurableSet A) :
    observedCellMeasure L sigma d y (observedCellEmbed d y ⁻¹' A) =
      (Pobs L sigma).restrict (observedCell d y) A := by
  have hembed : Measurable (observedCellEmbed d y) :=
    measurable_id.prodMk (measurable_const.prodMk measurable_const)
  unfold observedCellMeasure
  rw [Measure.map_apply measurable_fst (hA.preimage hembed)]
  rw [Measure.restrict_apply]
  swap
  · exact (hA.preimage hembed).preimage measurable_fst
  rw [Measure.restrict_apply hA]
  congr 1
  ext o
  rcases o with ⟨w, d', y'⟩
  simp only [observedCellEmbed, observedCell, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_ofPred_eq, Prod.fst]
  aesop

/-- Given [the displayed inputs and assumptions](hyp:mu), [the stated mathematical conclusion holds](goal). -/
lemma measure_eq_sum_observed_cells (mu : Measure Obs) :
    mu = Measure.sum (fun i : Bool × Bool => mu.restrict (observedCell i.1 i.2)) := by
  have hs : ∀ i : Bool × Bool, MeasurableSet (observedCell i.1 i.2) := by
    intro i
    exact measurableSet_observedCell i.1 i.2
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun i : Bool × Bool => observedCell i.1 i.2)) := by
    rintro ⟨d, y⟩ ⟨d', y'⟩ hne
    unfold Function.onFun
    rw [Set.disjoint_left]
    intro o ho ho'
    apply hne
    ext <;> simp_all [observedCell]
  have hcover : (⋃ i : Bool × Bool, observedCell i.1 i.2) = Set.univ := by
    ext o
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨(o.2.1, o.2.2), rfl, rfl⟩
  have h := Measure.restrict_iUnion (μ := mu)
    (s := fun i : Bool × Bool => observedCell i.1 i.2) hdisj hs
  rw [hcover, Measure.restrict_univ] at h
  exact h

/-- Given [the displayed inputs and assumptions](hyp:L,sigma,A,hA), [the stated mathematical conclusion holds](goal). -/
lemma measure_apply_eq_sum_observedCellMeasure
    (L : LatentLaw) (sigma : ℝ) (A : Set Obs) (hA : MeasurableSet A) :
    Pobs L sigma A = ∑ i : Bool × Bool,
      observedCellMeasure L sigma i.1 i.2 (observedCellEmbed i.1 i.2 ⁻¹' A) := by
  conv_lhs => rw [measure_eq_sum_observed_cells (Pobs L sigma)]
  rw [Measure.sum_apply _ hA, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact (observedCellMeasure_apply_preimage L sigma i.1 i.2 A hA).symm

/-- Given the displayed inputs, [this definition specifies the stated object](goal). -/
def observedReference : Measure Obs :=
  volume.prod (Measure.count : Measure (Bool × Bool))

/-- Given [the displayed inputs and assumptions](hyp:beta,b,sigma,m,s,o), [this definition specifies the stated object](goal). -/
def altObservedDensity (beta b sigma : ℝ) (m : ℕ) (s : Bool) (o : Obs) : ℝ :=
  if o.2.1 then witnessTreatedCellConvolution beta b sigma m s o.2.2 o.1
  else witnessControlCellConvolution sigma o.1

/-- Given [the displayed inputs and assumptions](hyp:sigma), [the stated mathematical conclusion holds](goal). -/
lemma witnessControlCellConvolution_continuous (sigma : ℝ) :
    Continuous (witnessControlCellConvolution sigma) := by
  unfold witnessControlCellConvolution
  fun_prop

/-- Given [the displayed inputs and assumptions](hyp:beta,b,sigma,m,s,y,hb), [the stated mathematical conclusion holds](goal). -/
lemma witnessTreatedCellConvolution_measurable
    (beta b sigma : ℝ) (m : ℕ) (s y : Bool) (hb : b ∈ Ioc (0 : ℝ) 1) :
    Measurable (witnessTreatedCellConvolution beta b sigma m s y) := by
  rw [show witnessTreatedCellConvolution beta b sigma m s y = fun w =>
      treatedConvolution sigma w/4 +
        witnessSign y * witnessSign s * kappa * (b/(m : ℝ)^2)^beta *
          markedConvolution b m sigma w/2 by
    funext w
    exact witnessTreatedCellConvolution_eq beta b sigma m s y hb w]
  apply StronglyMeasurable.measurable
  fun_prop

/-- Given [the displayed inputs and assumptions](hyp:beta,b,sigma,m,s,hb), [the stated mathematical conclusion holds](goal). -/
lemma altObservedDensity_measurable
    (beta b sigma : ℝ) (m : ℕ) (s : Bool) (hb : b ∈ Ioc (0 : ℝ) 1) :
    Measurable (altObservedDensity beta b sigma m s) := by
  apply Measurable.ite
  · exact (measurableSet_singleton true).preimage
      (measurable_fst.comp measurable_snd)
  · rw [show (fun x : Obs => witnessTreatedCellConvolution beta b sigma m s x.2.2 x.1) =
        fun x => if x.2.2 then witnessTreatedCellConvolution beta b sigma m s true x.1
          else witnessTreatedCellConvolution beta b sigma m s false x.1 by
      funext x
      cases x.2.2 <;> rfl]
    apply Measurable.ite
    · exact (measurableSet_singleton true).preimage
        (measurable_snd.comp measurable_snd)
    · exact (witnessTreatedCellConvolution_measurable beta b sigma m s true hb).comp
        measurable_fst
    · exact (witnessTreatedCellConvolution_measurable beta b sigma m s false hb).comp
        measurable_fst
  · exact (witnessControlCellConvolution_continuous sigma).measurable.comp measurable_fst

/-- Given [the displayed inputs and assumptions](hyp:hleg,beta,b,sigma,m,s,hbeta,hb,hm,hsigma), [the stated mathematical conclusion holds](goal). -/
lemma altLaw_observed_density
    (hleg : ClassicalLegendreFacts) (beta b sigma : ℝ) (m : ℕ) (s : Bool)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsigma : 0 < sigma) :
    Pobs (altLaw hleg beta b m s hbeta hb hm) sigma =
      observedReference.withDensity (fun o => ENNReal.ofReal
        (altObservedDensity beta b sigma m s o)) := by
  let L := altLaw hleg beta b m s hbeta hb hm
  have hdens : Measurable (fun o : Obs => ENNReal.ofReal
      (altObservedDensity beta b sigma m s o)) :=
    (altObservedDensity_measurable beta b sigma m s hb).ennreal_ofReal
  ext A hA
  rw [measure_apply_eq_sum_observedCellMeasure L sigma A hA]
  unfold observedReference
  rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  rw [lintegral_prod _ (hdens.indicator hA).aemeasurable]
  simp_rw [lintegral_count, tsum_fintype]
  rw [lintegral_finset_sum]
  swap
  · intro i _
    exact ((hdens.comp (measurable_id.prodMk measurable_const)).indicator
      (hA.preimage (measurable_id.prodMk measurable_const)))
  apply Finset.sum_congr rfl
  intro i _
  change observedCellMeasure L sigma i.1 i.2 (observedCellEmbed i.1 i.2 ⁻¹' A) = _
  rcases i with ⟨d, y⟩
  change observedCellMeasure L sigma d y (observedCellEmbed d y ⁻¹' A) =
    ∫⁻ w : ℝ, (observedCellEmbed d y ⁻¹' A).indicator
      (fun w => ENNReal.ofReal (altObservedDensity beta b sigma m s
        (observedCellEmbed d y w))) w
  have hcellA : MeasurableSet (observedCellEmbed d y ⁻¹' A) :=
    hA.preimage (measurable_id.prodMk (measurable_const.prodMk measurable_const))
  rw [lintegral_indicator hcellA]
  cases d
  · rw [altLaw_observed_control_cell_density hleg beta b sigma m s y hbeta hb hm hsigma]
    rw [withDensity_apply]
    · rfl
    · exact hA.preimage
        (measurable_id.prodMk (measurable_const.prodMk measurable_const))
  · rw [altLaw_observed_treated_cell_density hleg beta b sigma m s y hbeta hb hm hsigma]
    rw [withDensity_apply]
    · rfl
    · exact hA.preimage
        (measurable_id.prodMk (measurable_const.prodMk measurable_const))

/-- Given [the displayed inputs and assumptions](hyp:beta,b,sigma,m,o), [this definition specifies the stated object](goal). -/
def altObservedLikelihoodRatio
    (beta b sigma : ℝ) (m : ℕ) (o : Obs) : ℝ :=
  if o.2.1 then
    altObservedDensity beta b sigma m true o /
      altObservedDensity beta b sigma m false o
  else 1

/-- Given [the displayed inputs and assumptions](hyp:beta,b,sigma,m,hb), [the stated mathematical conclusion holds](goal). -/
lemma altObservedLikelihoodRatio_measurable
    (beta b sigma : ℝ) (m : ℕ) (hb : b ∈ Ioc (0 : ℝ) 1) :
    Measurable (altObservedLikelihoodRatio beta b sigma m) := by
  unfold altObservedLikelihoodRatio
  apply Measurable.ite
  · exact (measurableSet_singleton true).preimage
      (measurable_fst.comp measurable_snd)
  · exact (altObservedDensity_measurable beta b sigma m true hb).div
      (altObservedDensity_measurable beta b sigma m false hb)
  · fun_prop

/-- Given [the displayed inputs and assumptions](hyp:hleg,beta,b,sigma,m,s,hbeta,hb,hm,hsigma,o), [the stated mathematical conclusion holds](goal). -/
lemma altObservedDensity_nonneg
    (hleg : ClassicalLegendreFacts) (beta b sigma : ℝ) (m : ℕ) (s : Bool)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsigma : 0 < sigma) (o : Obs) :
    0 ≤ altObservedDensity beta b sigma m s o := by
  unfold altObservedDensity
  split
  · exact (le_trans (div_nonneg (treatedConvolution_pos sigma o.1 hsigma).le (by norm_num))
      (witnessTreatedCellConvolution_lower hleg beta b sigma m s o.2.2
        hbeta hb hm hsigma o.1))
  · unfold witnessControlCellConvolution
    exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ => phi_nonneg sigma (o.1 - x)))

/-- Given [the displayed inputs and assumptions](hyp:hleg,beta,b,sigma,m,hbeta,hb,hm,hsigma,o,ho), [the stated mathematical conclusion holds](goal). -/
lemma altObservedDensity_false_pos_on_treated
    (hleg : ClassicalLegendreFacts) (beta b sigma : ℝ) (m : ℕ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsigma : 0 < sigma) (o : Obs) (ho : o.2.1 = true) :
    0 < altObservedDensity beta b sigma m false o := by
  rw [altObservedDensity, if_pos ho]
  have hlower := witnessTreatedCellConvolution_lower hleg beta b sigma m false o.2.2
    hbeta hb hm hsigma o.1
  exact lt_of_lt_of_le (div_pos (treatedConvolution_pos sigma o.1 hsigma) (by norm_num)) hlower

/-- Given [the displayed inputs and assumptions](hyp:hleg,beta,b,sigma,m,hbeta,hb,hm,hsigma,o), [the stated mathematical conclusion holds](goal). -/
lemma altObservedDensity_mul_likelihoodRatio
    (hleg : ClassicalLegendreFacts) (beta b sigma : ℝ) (m : ℕ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsigma : 0 < sigma) (o : Obs) :
    ENNReal.ofReal (altObservedDensity beta b sigma m false o) *
        ENNReal.ofReal (altObservedLikelihoodRatio beta b sigma m o) =
      ENNReal.ofReal (altObservedDensity beta b sigma m true o) := by
  by_cases hd : o.2.1 = true
  · rw [altObservedLikelihoodRatio, if_pos hd]
    rw [ENNReal.ofReal_div_of_pos (altObservedDensity_false_pos_on_treated hleg beta b sigma m
      hbeta hb hm hsigma o hd)]
    exact ENNReal.mul_div_cancel
      (by simp [altObservedDensity_false_pos_on_treated hleg beta b sigma m
        hbeta hb hm hsigma o hd]) ENNReal.ofReal_ne_top
  · have hd' : o.2.1 = false := Bool.eq_false_of_not_eq_true hd
    rw [altObservedLikelihoodRatio, if_neg hd]
    simp only [ENNReal.ofReal_one, mul_one]
    unfold altObservedDensity
    rw [if_neg hd, if_neg hd]

/-- Given [the displayed inputs and assumptions](hyp:hleg,beta,b,sigma,m,hbeta,hb,hm,hsigma), [the stated mathematical conclusion holds](goal). -/
lemma altLaw_plus_eq_minus_withDensity
    (hleg : ClassicalLegendreFacts) (beta b sigma : ℝ) (m : ℕ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsigma : 0 < sigma) :
    Pobs (altLaw hleg beta b m true hbeta hb hm) sigma =
      (Pobs (altLaw hleg beta b m false hbeta hb hm) sigma).withDensity
        (fun o => ENNReal.ofReal (altObservedLikelihoodRatio beta b sigma m o)) := by
  rw [altLaw_observed_density hleg beta b sigma m true hbeta hb hm hsigma]
  rw [altLaw_observed_density hleg beta b sigma m false hbeta hb hm hsigma]
  rw [← withDensity_mul]
  · congr 1
    funext o
    exact (altObservedDensity_mul_likelihoodRatio hleg beta b sigma m
      hbeta hb hm hsigma o).symm
  · exact (altObservedDensity_measurable beta b sigma m false hb).ennreal_ofReal
  · exact (altObservedLikelihoodRatio_measurable beta b sigma m hb).ennreal_ofReal

/-- Given [the displayed inputs and assumptions](hyp:hleg,beta,b,sigma,m,hbeta,hb,hm,hsigma), [the stated mathematical conclusion holds](goal). -/
lemma altLaw_observed_rnDeriv
    (hleg : ClassicalLegendreFacts) (beta b sigma : ℝ) (m : ℕ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsigma : 0 < sigma) :
    (fun o => ((Pobs (altLaw hleg beta b m true hbeta hb hm) sigma).rnDeriv
      (Pobs (altLaw hleg beta b m false hbeta hb hm) sigma) o).toReal) =ᵐ[
        Pobs (altLaw hleg beta b m false hbeta hb hm) sigma]
      altObservedLikelihoodRatio beta b sigma m := by
  letI := (altLaw hleg beta b m false hbeta hb hm).prob
  letI : IsProbabilityMeasure
      (Pobs (altLaw hleg beta b m false hbeta hb hm) sigma) :=
    Measure.isProbabilityMeasure_map (obs_measurable sigma).aemeasurable
  rw [altLaw_plus_eq_minus_withDensity hleg beta b sigma m hbeta hb hm hsigma]
  filter_upwards [Measure.rnDeriv_withDensity
    (Pobs (altLaw hleg beta b m false hbeta hb hm) sigma)
    (altObservedLikelihoodRatio_measurable beta b sigma m hb).ennreal_ofReal] with o ho
  rw [ho, ENNReal.toReal_ofReal]
  by_cases hd : o.2.1 = true
  · rw [altObservedLikelihoodRatio, if_pos hd]
    exact div_nonneg
      (altObservedDensity_nonneg hleg beta b sigma m true hbeta hb hm hsigma o)
      (altObservedDensity_nonneg hleg beta b sigma m false hbeta hb hm hsigma o)
  · simp [altObservedLikelihoodRatio, hd]

/-- Given [the displayed inputs and assumptions](hyp:beta,b,sigma,m,o), [this definition specifies the stated object](goal). -/
def altChiSqReferenceIntegrand (beta b sigma : ℝ) (m : ℕ) (o : Obs) : ℝ :=
  altObservedDensity beta b sigma m false o *
    (altObservedLikelihoodRatio beta b sigma m o - 1)^2

/-- Given [the displayed inputs and assumptions](hyp:beta,b,sigma,m,hb), [the stated mathematical conclusion holds](goal). -/
lemma altChiSqReferenceIntegrand_measurable
    (beta b sigma : ℝ) (m : ℕ) (hb : b ∈ Ioc (0 : ℝ) 1) :
    Measurable (altChiSqReferenceIntegrand beta b sigma m) := by
  unfold altChiSqReferenceIntegrand
  exact (altObservedDensity_measurable beta b sigma m false hb).mul
    (((altObservedLikelihoodRatio_measurable beta b sigma m hb).sub measurable_const).pow_const 2)

/-- Given [the displayed inputs and assumptions](hyp:hleg,beta,b,sigma,m,hbeta,hb,hm,hsigma,w,d,y), [the stated mathematical conclusion holds](goal). -/
lemma altChiSqReferenceIntegrand_cell
    (hleg : ClassicalLegendreFacts) (beta b sigma : ℝ) (m : ℕ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsigma : 0 < sigma) (w : ℝ) (d y : Bool) :
    altChiSqReferenceIntegrand beta b sigma m (w, d, y) =
      if d then
        (witnessTreatedCellConvolution beta b sigma m true y w -
          witnessTreatedCellConvolution beta b sigma m false y w)^2 /
            witnessTreatedCellConvolution beta b sigma m false y w
      else 0 := by
  cases d
  · simp [altChiSqReferenceIntegrand, altObservedLikelihoodRatio, altObservedDensity]
  · have hq := altObservedDensity_false_pos_on_treated hleg beta b sigma m
      hbeta hb hm hsigma (w, true, y) rfl
    have hq' : 0 < witnessTreatedCellConvolution beta b sigma m false y w := by
      simpa [altObservedDensity] using hq
    simp only [if_true]
    change witnessTreatedCellConvolution beta b sigma m false y w *
      (witnessTreatedCellConvolution beta b sigma m true y w /
        witnessTreatedCellConvolution beta b sigma m false y w - 1)^2 = _
    field_simp [hq'.ne']

/-- Given [the displayed inputs and assumptions](hyp:hleg,beta,b,sigma,m,hbeta,hb,hm,hsigma), [the stated mathematical conclusion holds](goal). -/
lemma altChiSqReferenceIntegrand_integrable
    (hleg : ClassicalLegendreFacts) (beta b sigma : ℝ) (m : ℕ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsigma : 0 < sigma) :
    Integrable (altChiSqReferenceIntegrand beta b sigma m) observedReference := by
  unfold observedReference
  refine (integrable_prod_iff
    (altChiSqReferenceIntegrand_measurable beta b sigma m hb).aestronglyMeasurable).2
    ⟨Filter.Eventually.of_forall (fun w => Integrable.of_finite), ?_⟩
  have hint := witnessTreatedCellConvolution_square_difference_integrable hleg
    beta b sigma m hbeta hb hm hsigma
  apply hint.congr
  filter_upwards [] with w
  have hden0 : 0 ≤ witnessTreatedCellConvolution beta b sigma m false false w :=
    le_trans (div_nonneg (treatedConvolution_pos sigma w hsigma).le (by norm_num))
      (witnessTreatedCellConvolution_lower hleg beta b sigma m false false
        hbeta hb hm hsigma w)
  have hden1 : 0 ≤ witnessTreatedCellConvolution beta b sigma m false true w :=
    le_trans (div_nonneg (treatedConvolution_pos sigma w hsigma).le (by norm_num))
      (witnessTreatedCellConvolution_lower hleg beta b sigma m false true
        hbeta hb hm hsigma w)
  rw [integral_count]
  simp only [Real.norm_eq_abs, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [altChiSqReferenceIntegrand_cell hleg beta b sigma m hbeta hb hm hsigma w false false,
    altChiSqReferenceIntegrand_cell hleg beta b sigma m hbeta hb hm hsigma w false true,
    altChiSqReferenceIntegrand_cell hleg beta b sigma m hbeta hb hm hsigma w true false,
    altChiSqReferenceIntegrand_cell hleg beta b sigma m hbeta hb hm hsigma w true true]
  simp only [Bool.false_eq_true, if_false, if_true, abs_zero, zero_add]
  rw [abs_of_nonneg, abs_of_nonneg]
  · ring
  · exact div_nonneg (sq_nonneg _) hden0
  · exact div_nonneg (sq_nonneg _) hden1

/-- Given [the displayed inputs and assumptions](hyp:hleg,beta,b,sigma,m,hbeta,hb,hm,hsigma), [the stated mathematical conclusion holds](goal). -/
lemma altLikelihoodRatio_sq_integral_eq
    (hleg : ClassicalLegendreFacts) (beta b sigma : ℝ) (m : ℕ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m)
    (hsigma : 0 < sigma) :
    (∫ o, (altObservedLikelihoodRatio beta b sigma m o - 1)^2 ∂
      Pobs (altLaw hleg beta b m false hbeta hb hm) sigma) =
      ∫ w : ℝ, ∑ y : Bool,
        (witnessTreatedCellConvolution beta b sigma m true y w -
          witnessTreatedCellConvolution beta b sigma m false y w)^2 /
            witnessTreatedCellConvolution beta b sigma m false y w := by
  rw [altLaw_observed_density hleg beta b sigma m false hbeta hb hm hsigma]
  rw [integral_withDensity_eq_integral_toReal_smul
    (altObservedDensity_measurable beta b sigma m false hb).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hnonneg : ∀ o, 0 ≤ altObservedDensity beta b sigma m false o :=
    altObservedDensity_nonneg hleg beta b sigma m false hbeta hb hm hsigma
  simp_rw [ENNReal.toReal_ofReal (hnonneg _)]
  simp only [smul_eq_mul]
  change (∫ o, altChiSqReferenceIntegrand beta b sigma m o ∂observedReference) = _
  unfold observedReference
  rw [integral_prod _ (altChiSqReferenceIntegrand_integrable hleg beta b sigma m
    hbeta hb hm hsigma)]
  apply integral_congr_ae
  filter_upwards [] with w
  rw [integral_count]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [altChiSqReferenceIntegrand_cell hleg beta b sigma m hbeta hb hm hsigma w false false,
    altChiSqReferenceIntegrand_cell hleg beta b sigma m hbeta hb hm hsigma w false true,
    altChiSqReferenceIntegrand_cell hleg beta b sigma m hbeta hb hm hsigma w true false,
    altChiSqReferenceIntegrand_cell hleg beta b sigma m hbeta hb hm hsigma w true true]
  simp [Fintype.sum_bool]


end CausalSmith.Stat.RdTruesideNoiseFrontier
