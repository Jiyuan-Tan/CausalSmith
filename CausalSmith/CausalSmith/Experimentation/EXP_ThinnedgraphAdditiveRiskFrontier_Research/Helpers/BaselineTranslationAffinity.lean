module
public import Causalean.Stat.Minimax.SharpHellinger
public import Causalean.Stat.Minimax.TotalVariation
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BaselineTranslationEnergy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Translation affinity and common-marginal averaging
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The unhalved squared Hellinger energy of two real densities against a common reference
measure. -/
def hellingerEnergy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) : ℝ :=
  ∫ x, (Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 ∂μ

/-- The joint mixing-coordinate and response law for a common marginal and conditional density. -/
def densityJoint {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (ν : Measure Ξ) (μ : Measure Ω) (v : Ξ → Ω → ℝ) : Measure (Ξ × Ω) :=
  ν.bind (fun ξ => (μ.withDensity (fun x => ENNReal.ofReal (v ξ x))).map (Prod.mk ξ))

/-- The response mixture after integrating out the common mixing coordinate. -/
def densityMixture {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (ν : Measure Ξ) (μ : Measure Ω) (v : Ξ → Ω → ℝ) : Measure Ω :=
  ν.bind (fun ξ => μ.withDensity (fun x => ENNReal.ofReal (v ξ x)))

/-- A measurable nonnegative density defining a probability law is integrable and
has integral one; these side conditions are consequences of normalization.  [For the stated data and conditions](hyp:Ω,μ,f,hf,hf0), [the stated conclusion holds](goal). -/
-- @node: probability_density_integrable_normalized
lemma probability_density_integrable_normalized {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    Integrable f μ ∧ (∫ x, f x ∂μ) = 1 := by
  have hn : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = 1 := by
    have h := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (f x)))
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have hnn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hf0
  have hi : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnn).mp
      (by rw [hn]; exact ENNReal.one_ne_top)
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi hnn
  rw [hn] at he
  have hp : 0 ≤ ∫ x, f x ∂μ := integral_nonneg hf0
  exact_mod_cast (ENNReal.ofReal_eq_ofReal_iff hp (by norm_num : (0 : ℝ) ≤ 1)).mp
    (by simpa using he)

/-- Cauchy–Schwarz bounds total variation by the square root of the unhalved
Hellinger energy of two probability densities.  [For the stated data and conditions](hyp:Ω,μ,f,g,hf,hg,hf0,hg0), [the stated conclusion holds](goal). -/
-- @node: density_tv_le_sqrt_hellingerEnergy
lemma density_tv_le_sqrt_hellingerEnergy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))]
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (g x)))] :
    Causalean.Stat.tvDist (μ.withDensity (fun x => ENNReal.ofReal (f x)))
      (μ.withDensity (fun x => ENNReal.ofReal (g x))) ≤
        Real.sqrt (hellingerEnergy μ f g) := by
  obtain ⟨hfi, hf1⟩ := probability_density_integrable_normalized μ f hf hf0
  obtain ⟨hgi, hg1⟩ := probability_density_integrable_normalized μ g hg hg0
  have htv := Causalean.Stat.tvDist_le_sqrt_two_mul_one_sub_affinity
    μ f g hfi hgi hf0 hg0 hf1 hg1
  rw [← Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity
    μ f g hfi hgi hf0 hg0 hf1 hg1] at htv
  exact htv

/-- The baseline density is nonnegative.  [For the stated data and conditions](hyp:w), [the stated conclusion holds](goal). -/
-- @node: cosSqDensity_nonneg
lemma cosSqDensity_nonneg (w : ℝ) : 0 ≤ cosSqDensity w := by
  unfold cosSqDensity
  split <;> positivity

/-- The compactly supported cosine density is integrable and normalized.  [the stated conclusion holds](goal). -/
-- @node: cosSqDensity_integrable_normalized
lemma cosSqDensity_integrable_normalized :
    Integrable cosSqDensity ∧ (∫ w, cosSqDensity w) = 1 := by
  have he : cosSqDensity = Set.indicator (Set.Icc (-1 / 4 : ℝ) (1 / 4))
      (fun w => 4 * Real.cos (2 * Real.pi * w) ^ 2) := by
    funext w
    simp only [cosSqDensity, Set.indicator, Set.mem_Icc]
    congr 1
    exact propext (by
      constructor
      · intro h
        exact ⟨by linarith [(abs_le.mp h).1], (abs_le.mp h).2⟩
      · intro h
        exact abs_le.mpr ⟨by linarith [h.1], h.2⟩)
  have hc : Continuous (fun w : ℝ => 4 * Real.cos (2 * Real.pi * w) ^ 2) := by
    fun_prop
  rw [he]
  refine ⟨(integrable_indicator_iff measurableSet_Icc).mpr hc.continuousOn.integrableOn_Icc, ?_⟩
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 1 / 4),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2)
      (by positivity : 2 * Real.pi ≠ 0), integral_cos_sq]
  have hl : 2 * Real.pi * (-1 / 4 : ℝ) = -(Real.pi / 2) := by ring
  have hu : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
  simp only [hl, hu, Real.cos_neg, Real.cos_pi_div_two, zero_mul, sub_zero,
    smul_eq_mul]
  field_simp
  ring

/-- Translation preserves integrability and normalization of the baseline density.  [For the stated data and conditions](hyp:s), [the stated conclusion holds](goal). -/
-- @node: translated_cosSqDensity_integrable_normalized
lemma translated_cosSqDensity_integrable_normalized (s : ℝ) :
    Integrable (fun w => cosSqDensity (w - s)) ∧
      (∫ w, cosSqDensity (w - s)) = 1 := by
  refine ⟨cosSqDensity_integrable_normalized.1.comp_sub_right s, ?_⟩
  rw [integral_sub_right_eq_self]
  exact cosSqDensity_integrable_normalized.2

/-- Tensorized affinity and the product-defect bound give subadditivity of
squared Hellinger energy for normalized nonnegative coordinate densities.  [For the stated data and conditions](hyp:ι,f,g,hf,hg,hf0,hg0,hf1,hg1), [the stated conclusion holds](goal). -/
-- @node: hellingerEnergy_pi_le_sum
lemma hellingerEnergy_pi_le_sum {ι : Type*} [Fintype ι]
    (f g : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) (hg : ∀ i, Integrable (g i))
    (hf0 : ∀ i x, 0 ≤ f i x) (hg0 : ∀ i x, 0 ≤ g i x)
    (hf1 : ∀ i, (∫ x, f i x) = 1) (hg1 : ∀ i, (∫ x, g i x) = 1) :
    hellingerEnergy volume (fun x : ι → ℝ => ∏ i, f i (x i))
      (fun x => ∏ i, g i (x i)) ≤ ∑ i, hellingerEnergy volume (f i) (g i) := by
  have hFp : Integrable (fun x : ι → ℝ => ∏ i, f i (x i)) :=
    Integrable.fintype_prod hf
  have hGp : Integrable (fun x : ι → ℝ => ∏ i, g i (x i)) :=
    Integrable.fintype_prod hg
  have hF0 : ∀ x : ι → ℝ, 0 ≤ ∏ i, f i (x i) :=
    fun x => Finset.prod_nonneg (fun i _ => hf0 i (x i))
  have hG0 : ∀ x : ι → ℝ, 0 ≤ ∏ i, g i (x i) :=
    fun x => Finset.prod_nonneg (fun i _ => hg0 i (x i))
  have hF1 : (∫ x : ι → ℝ, ∏ i, f i (x i)) = 1 := by
    change (∫ x : ι → ℝ, ∏ i, f i (x i) ∂Measure.pi (fun _ => volume)) = 1
    rw [integral_fintype_prod_eq_prod]; simp [hf1]
  have hG1 : (∫ x : ι → ℝ, ∏ i, g i (x i)) = 1 := by
    change (∫ x : ι → ℝ, ∏ i, g i (x i) ∂Measure.pi (fun _ => volume)) = 1
    rw [integral_fintype_prod_eq_prod]; simp [hg1]
  have hE (i : ι) : hellingerEnergy volume (f i) (g i) =
      2 * (1 - Causalean.Stat.densityAffinity volume (f i) (g i)) :=
    Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity
      volume (f i) (g i) (hf i) (hg i) (hf0 i) (hg0 i) (hf1 i) (hg1 i)
  have ha0 (i : ι) : 0 ≤ Causalean.Stat.densityAffinity volume (f i) (g i) :=
    integral_nonneg (fun _ => Real.sqrt_nonneg _)
  have ha1 (i : ι) : Causalean.Stat.densityAffinity volume (f i) (g i) ≤ 1 := by
    have hn : 0 ≤ hellingerEnergy volume (f i) (g i) :=
      integral_nonneg (fun _ => sq_nonneg _)
    rw [hE i] at hn
    linarith
  change Causalean.Stat.hellingerSqDensity volume
    (fun x : ι → ℝ => ∏ i, f i (x i)) (fun x => ∏ i, g i (x i)) ≤ _
  rw [Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity
    volume _ _ hFp hGp hF0 hG0 hF1 hG1]
  change 2 * (1 - Causalean.Stat.densityAffinity (Measure.pi (fun _ : ι => volume))
    (fun x => ∏ i, f i (x i)) (fun x => ∏ i, g i (x i))) ≤ _
  rw [Causalean.Stat.densityAffinity_pi (fun _ : ι => (volume : Measure ℝ)) f g hf0 hg0]
  simp_rw [hE]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (Causalean.Stat.one_sub_prod_le_sum _ ha0 ha1)
    (by norm_num)

/-- [Joint measurability of the conditional densities](hyp:hv) gives [a measurable family of joint fibers](goal). -/
-- @node: measurable_densityJoint_fiber
@[fun_prop] lemma measurable_densityJoint_fiber {Ξ Ω : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (v : Ξ → Ω → ℝ) (hv : Measurable (fun p : Ξ × Ω => v p.1 p.2)) :
    Measurable (fun ξ => (μ.withDensity (fun x => ENNReal.ofReal (v ξ x))).map
      (Prod.mk ξ)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [Measure.map_apply measurable_prodMk_left hs,
    withDensity_apply _ (measurable_prodMk_left hs),
    ← lintegral_indicator (measurable_prodMk_left hs)]
  have hm : Measurable (s.indicator (fun p : Ξ × Ω => ENNReal.ofReal (v p.1 p.2))) :=
    (ENNReal.measurable_ofReal.comp hv).indicator hs
  simpa only [Set.indicator_apply, Set.mem_preimage] using hm.lintegral_prod_right'

/-- The conditional-density joint law is the density-weighted product reference law.  [For the stated data and conditions](hyp:Ξ,Ω,ν,μ,v,hv), [the stated conclusion holds](goal). -/
-- @node: densityJoint_eq_withDensity
lemma densityJoint_eq_withDensity {Ξ Ω : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Ω] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (μ : Measure Ω) [SigmaFinite μ] (v : Ξ → Ω → ℝ)
    (hv : Measurable (fun p : Ξ × Ω => v p.1 p.2)) :
    densityJoint ν μ v = (ν.prod μ).withDensity
      (fun p => ENNReal.ofReal (v p.1 p.2)) := by
  ext s hs
  rw [densityJoint, Measure.bind_apply hs
    (measurable_densityJoint_fiber μ v hv).aemeasurable,
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro ξ
  rw [Measure.map_apply measurable_prodMk_left hs,
    withDensity_apply _ (measurable_prodMk_left hs),
    ← lintegral_indicator (measurable_prodMk_left hs)]
  rfl

/-- Normalized conditional fibers give a probability joint law.  [For the stated data and conditions](hyp:Ξ,Ω,ν,μ,v,hv,hp), [the stated conclusion holds](goal). -/
-- @node: densityJoint_probability
lemma densityJoint_probability {Ξ Ω : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Ω] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (μ : Measure Ω) [SigmaFinite μ] (v : Ξ → Ω → ℝ)
    (hv : Measurable (fun p : Ξ × Ω => v p.1 p.2))
    (hp : ∀ ξ, IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (v ξ x)))) :
    IsProbabilityMeasure (densityJoint ν μ v) := by
  constructor
  rw [densityJoint, Measure.bind_apply MeasurableSet.univ
    (measurable_densityJoint_fiber μ v hv).aemeasurable]
  have he : ∀ ξ, (Measure.map (Prod.mk ξ)
      (μ.withDensity (fun x => ENNReal.ofReal (v ξ x)))) Set.univ = 1 := by
    intro ξ
    let _ := hp ξ
    rw [Measure.map_apply measurable_prodMk_left MeasurableSet.univ]
    simp
  simp_rw [he]
  simp

/-- The sum-reference Hellinger definition agrees with a sigma-finite density reference.  [For the stated data and conditions](hyp:Ω,μ,f,g,hf,hg,hf0,hg0), [the stated conclusion holds](goal). -/
-- @node: hellingerSqMeasure_eq_density
lemma hellingerSqMeasure_eq_density {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))]
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (g x)))] :
    Causalean.Stat.Minimax.hellingerSqMeasure
      (μ.withDensity (fun x => ENNReal.ofReal (f x)))
      (μ.withDensity (fun x => ENNReal.ofReal (g x))) = hellingerEnergy μ f g := by
  let B := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let C := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have hb : B ≪ μ := withDensity_absolutelyContinuous μ _
  have hc : C ≪ μ := withDensity_absolutelyContinuous μ _
  have hbs : B ≪ B + C := Measure.AbsolutelyContinuous.rfl.add_right C
  have hcs : C ≪ B + C := Measure.AbsolutelyContinuous.rfl.add_right' B
  have hbr := Measure.rnDeriv_mul_rnDeriv (κ := μ) hbs
  have hcr := Measure.rnDeriv_mul_rnDeriv (κ := μ) hcs
  have hbf : B.rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (f x) :=
    Measure.rnDeriv_withDensity μ (by fun_prop)
  have hcg : C.rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (g x) :=
    Measure.rnDeriv_withDensity μ (by fun_prop)
  change (∫ x, (Real.sqrt ((B.rnDeriv (B + C) x).toReal) -
    Real.sqrt ((C.rnDeriv (B + C) x).toReal)) ^ 2 ∂(B + C)) = _
  rw [← integral_toReal_rnDeriv_mul (hb.add_left hc)]
  apply integral_congr_ae
  filter_upwards [hbr, hcr, hbf, hcg] with x hxB hxC hxF hxG
  have hF : f x = (B.rnDeriv (B + C) x).toReal * ((B + C).rnDeriv μ x).toReal := by
    rw [← ENNReal.toReal_ofReal (hf0 x), ← hxF, ← hxB, Pi.mul_apply,
      ENNReal.toReal_mul]
  have hG : g x = (C.rnDeriv (B + C) x).toReal * ((B + C).rnDeriv μ x).toReal := by
    rw [← ENNReal.toReal_ofReal (hg0 x), ← hxG, ← hxC, Pi.mul_apply,
      ENNReal.toReal_mul]
  change _ = (Real.sqrt (f x) - Real.sqrt (g x)) ^ 2
  rw [hF, hG, Real.sqrt_mul ENNReal.toReal_nonneg,
    Real.sqrt_mul ENNReal.toReal_nonneg, ← sub_mul, mul_pow,
    Real.sq_sqrt ENNReal.toReal_nonneg]
  ring

/-- Marginalizing the joint law recovers its response mixture.  [For the stated data and conditions](hyp:Ξ,Ω,ν,μ,v,hv), [the stated conclusion holds](goal). -/
-- @node: densityJoint_map_snd
lemma densityJoint_map_snd {Ξ Ω : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Ω] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (μ : Measure Ω) [SigmaFinite μ] (v : Ξ → Ω → ℝ)
    (hv : Measurable (fun p : Ξ × Ω => v p.1 p.2)) :
    (densityJoint ν μ v).map Prod.snd = densityMixture ν μ v := by
  have hm : Measurable (fun ξ => μ.withDensity (fun x => ENNReal.ofReal (v ξ x))) := by
    apply measurable_withDensity
    exact ENNReal.measurable_ofReal.comp hv
  ext s hs
  rw [Measure.map_apply measurable_snd hs, densityJoint, densityMixture,
    Measure.bind_apply (measurable_snd hs) (measurable_densityJoint_fiber μ v hv).aemeasurable,
    Measure.bind_apply hs hm.aemeasurable]
  apply lintegral_congr
  intro ξ
  rw [Measure.map_apply measurable_prodMk_left (measurable_snd hs)]
  rfl

/-- Averaging conditional Hellinger energy over the actual common marginal gives
joint Hellinger energy and bounds the response-mixture total variation.  [For the stated data and conditions](hyp:Ξ,Ω,ν,μ,f,g,hf,hg,hf0,hg0,hfp,hgp), [the stated conclusion holds](goal). -/
-- @node: common_marginal_hellinger_averaging
lemma common_marginal_hellinger_averaging {Ξ Ω : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Ω] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (μ : Measure Ω) [SigmaFinite μ] (f g : Ξ → Ω → ℝ)
    (hf : Measurable (fun p : Ξ × Ω => f p.1 p.2))
    (hg : Measurable (fun p : Ξ × Ω => g p.1 p.2))
    (hf0 : ∀ ξ x, 0 ≤ f ξ x) (hg0 : ∀ ξ x, 0 ≤ g ξ x)
    (hfp : ∀ ξ, IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f ξ x))))
    (hgp : ∀ ξ, IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (g ξ x)))) :
    Causalean.Stat.Minimax.hellingerSqMeasure (densityJoint ν μ f) (densityJoint ν μ g) =
      (∫ ξ, hellingerEnergy μ (f ξ) (g ξ) ∂ν) ∧
    Causalean.Stat.tvDist (densityMixture ν μ f) (densityMixture ν μ g) ≤
      Real.sqrt (∫ ξ, hellingerEnergy μ (f ξ) (g ξ) ∂ν) := by
  let _ := densityJoint_probability ν μ f hf hfp
  let _ := densityJoint_probability ν μ g hg hgp
  have hpf : IsProbabilityMeasure ((ν.prod μ).withDensity
      (fun p => ENNReal.ofReal (f p.1 p.2))) := by
    rw [← densityJoint_eq_withDensity ν μ f hf]
    infer_instance
  have hpg : IsProbabilityMeasure ((ν.prod μ).withDensity
      (fun p => ENNReal.ofReal (g p.1 p.2))) := by
    rw [← densityJoint_eq_withDensity ν μ g hg]
    infer_instance
  let _ := hpf
  let _ := hpg
  have hfi := (probability_density_integrable_normalized (ν.prod μ)
    (fun p => f p.1 p.2) hf (fun p => hf0 p.1 p.2)).1
  have hgi := (probability_density_integrable_normalized (ν.prod μ)
    (fun p => g p.1 p.2) hg (fun p => hg0 p.1 p.2)).1
  have he : hellingerEnergy (ν.prod μ) (fun p => f p.1 p.2) (fun p => g p.1 p.2) =
      (∫ ξ, hellingerEnergy μ (f ξ) (g ξ) ∂ν) := by
    exact integral_prod _ (Causalean.Stat.Minimax.integrable_sqrt_sum_sub_sq
      (ν.prod μ) _ _ hfi hgi (fun p => hf0 p.1 p.2) (fun p => hg0 p.1 p.2)).2
  refine ⟨?_, ?_⟩
  · rw [densityJoint_eq_withDensity ν μ f hf, densityJoint_eq_withDensity ν μ g hg,
      hellingerSqMeasure_eq_density (ν.prod μ) _ _ hf hg
        (fun p => hf0 p.1 p.2) (fun p => hg0 p.1 p.2), he]
  · have htv : Causalean.Stat.tvDist (densityJoint ν μ f) (densityJoint ν μ g) ≤
        Real.sqrt (∫ ξ, hellingerEnergy μ (f ξ) (g ξ) ∂ν) := by
      rw [densityJoint_eq_withDensity ν μ f hf, densityJoint_eq_withDensity ν μ g hg,
        ← he]
      exact density_tv_le_sqrt_hellingerEnergy (ν.prod μ) _ _ hf hg
        (fun p => hf0 p.1 p.2) (fun p => hg0 p.1 p.2)
    rw [← densityJoint_map_snd ν μ f hf, ← densityJoint_map_snd ν μ g hg]
    apply le_trans ?_ htv
    unfold Causalean.Stat.tvDist
    apply ciSup_le
    rintro ⟨s, hs⟩
    rw [map_measureReal_apply_of_aemeasurable measurable_snd.aemeasurable hs,
      map_measureReal_apply_of_aemeasurable measurable_snd.aemeasurable hs]
    exact Causalean.Stat.abs_measureReal_sub_le_tvDist (measurable_snd hs)

/-- The pointwise derivative of the square-root baseline away from its two support
boundaries, with the arbitrary boundary values fixed to zero. -/
-- @node: baselineSqrtDerivAt
def baselineSqrtDerivAt (w : ℝ) : ℝ :=
  if |w| < (1 / 4 : ℝ) then -4 * Real.pi * Real.sin (2 * Real.pi * w) else 0

/-- Away from the two support boundaries, the square-root baseline has the
explicit supported sine derivative.  [For the stated data and conditions](hyp:w,hneg,hpos), [the stated conclusion holds](goal). -/
-- @node: sqrt_cosSqDensity_hasDerivAt
lemma sqrt_cosSqDensity_hasDerivAt (w : ℝ)
    (hneg : w ≠ -(1 / 4 : ℝ)) (hpos : w ≠ (1 / 4 : ℝ)) :
    HasDerivAt (fun x => Real.sqrt (cosSqDensity x)) (baselineSqrtDerivAt w) w := by
  rcases lt_trichotomy w (-(1 / 4 : ℝ)) with hw | hw | hw
  · have habs : ¬ |w| < (1 / 4 : ℝ) := by
      rw [not_lt]
      exact (le_of_lt (lt_neg.mpr hw)).trans (neg_le_abs w)
    have heq : (fun x => Real.sqrt (cosSqDensity x)) =ᶠ[nhds w]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.eventually_mem hw] with x hx
      have hxabs : ¬ |x| ≤ (1 / 4 : ℝ) := by
        rw [not_le]
        exact (lt_neg.mpr hx).trans_le (neg_le_abs x)
      rw [cosSqDensity, if_neg hxabs, Real.sqrt_zero]
    rw [baselineSqrtDerivAt, if_neg habs]
    exact (hasDerivAt_const (x := w) (c := (0 : ℝ))).congr_of_eventuallyEq heq
  · exact (hneg hw).elim
  · rcases lt_trichotomy w (1 / 4 : ℝ) with hwin | hw | hw
    · have habs : |w| < (1 / 4 : ℝ) := abs_lt.mpr ⟨hw, hwin⟩
      have heq : (fun x => Real.sqrt (cosSqDensity x)) =ᶠ[nhds w]
          (fun x => 2 * Real.cos (2 * Real.pi * x)) := by
        filter_upwards [isOpen_Ioo.eventually_mem ⟨hw, hwin⟩] with x hx
        rw [sqrt_cosSqDensity_eq_clamped_cos, min_eq_right hx.2.le,
          max_eq_right (by linarith [hx.1])]
      have hderiv : HasDerivAt (fun x => 2 * Real.cos (2 * Real.pi * x))
          (-4 * Real.pi * Real.sin (2 * Real.pi * w)) w := by
        convert ((Real.hasDerivAt_cos (2 * Real.pi * w)).comp w
          ((hasDerivAt_id w).const_mul (2 * Real.pi))).const_mul 2 using 1 <;>
          first | rfl | ring
      rw [baselineSqrtDerivAt, if_pos habs]
      exact hderiv.congr_of_eventuallyEq heq
    · exact (hpos hw).elim
    · have habs : ¬ |w| < (1 / 4 : ℝ) := by
        rw [not_lt]
        exact (le_of_lt hw).trans (le_abs_self w)
      have heq : (fun x => Real.sqrt (cosSqDensity x)) =ᶠ[nhds w]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioi.eventually_mem hw] with x hx
        have hxabs : ¬ |x| ≤ (1 / 4 : ℝ) := by
          rw [not_le]
          exact hx.trans_le (le_abs_self x)
        rw [cosSqDensity, if_neg hxabs, Real.sqrt_zero]
      rw [baselineSqrtDerivAt, if_neg habs]
      exact (hasDerivAt_const (x := w) (c := (0 : ℝ))).congr_of_eventuallyEq heq

/-- The explicitly tied square-root derivative has total squared energy four pi
squared.  [the stated conclusion holds](goal). -/
-- @node: baselineSqrtDerivAt_energy
lemma baselineSqrtDerivAt_energy :
    (∫ w, baselineSqrtDerivAt w ^ 2) = 4 * Real.pi ^ 2 := by
  have he : (fun w => baselineSqrtDerivAt w ^ 2) =
      (Set.Ioo (-1 / 4 : ℝ) (1 / 4)).indicator
        (fun w => (-4 * Real.pi * Real.sin (2 * Real.pi * w)) ^ 2) := by
    funext w
    by_cases hw : |w| < (1 / 4 : ℝ)
    · have hmem : w ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4) := by
        constructor <;> linarith [(abs_lt.mp hw).1, (abs_lt.mp hw).2]
      rw [baselineSqrtDerivAt, if_pos hw, Set.indicator_of_mem hmem]
    · have hmem : w ∉ Set.Ioo (-1 / 4 : ℝ) (1 / 4) := by
        intro hmem
        apply hw
        exact abs_lt.mpr ⟨by linarith [hmem.1], hmem.2⟩
      rw [baselineSqrtDerivAt, if_neg hw, Set.indicator_of_notMem hmem]
      norm_num
  rw [he, integral_indicator measurableSet_Ioo, ← integral_Icc_eq_integral_Ioo]
  have hsquare : (fun w : ℝ => (-4 * Real.pi * Real.sin (2 * Real.pi * w)) ^ 2) =
      (fun w => (4 * Real.pi * Real.sin (2 * Real.pi * w)) ^ 2) := by
    funext w
    ring
  rw [hsquare]
  exact baseline_derivative_energy

/-- Lipschitz and derivative energy, translation and product bounds, and common-marginal
Hellinger averaging.  [the stated conclusion holds](goal). -/
-- @node: lem:baseline-translation-affinity
lemma baseline_translation_affinity :
    LipschitzWith ((4 * Real.pi).toNNReal) (fun w => Real.sqrt (cosSqDensity w)) ∧
    (∫ w in Set.Icc (-1 / 4 : ℝ) (1 / 4), (4 * Real.pi * Real.sin (2 * Real.pi * w)) ^ 2) =
      4 * Real.pi ^ 2 ∧
    (∀ s t : ℝ, (∫ w, (Real.sqrt (cosSqDensity (w - s)) -
      Real.sqrt (cosSqDensity (w - t))) ^ 2) ≤ 4 * Real.pi ^ 2 * (s - t) ^ 2) ∧
    (∀ (B : ℕ) (s t : Fin B → ℝ),
      (∫ y : Fin B → ℝ, (Real.sqrt (∏ ℓ, cosSqDensity (y ℓ - s ℓ)) -
        Real.sqrt (∏ ℓ, cosSqDensity (y ℓ - t ℓ))) ^ 2) ≤
          ∑ ℓ, 4 * Real.pi ^ 2 * (s ℓ - t ℓ) ^ 2) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
      (vPlus vMinus : Ω → ℝ), Measurable vPlus → Measurable vMinus →
      (∀ x, 0 ≤ vPlus x) → (∀ x, 0 ≤ vMinus x) →
      IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (vPlus x))) →
      IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (vMinus x))) →
      Causalean.Stat.tvDist (μ.withDensity (fun x => ENNReal.ofReal (vPlus x)))
        (μ.withDensity (fun x => ENNReal.ofReal (vMinus x))) ≤
          Real.sqrt (hellingerEnergy μ vPlus vMinus)) ∧
    (∀ (Ξ Ω : Type) [MeasurableSpace Ξ] [MeasurableSpace Ω]
      (ν : Measure Ξ) [IsProbabilityMeasure ν] (μ : Measure Ω) [SigmaFinite μ]
      (vPlus vMinus : Ξ → Ω → ℝ),
      Measurable (fun x : Ξ × Ω => vPlus x.1 x.2) →
      Measurable (fun x : Ξ × Ω => vMinus x.1 x.2) →
      (∀ ξ x, 0 ≤ vPlus ξ x) → (∀ ξ x, 0 ≤ vMinus ξ x) →
      (∀ ξ, IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (vPlus ξ x)))) →
      (∀ ξ, IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (vMinus ξ x)))) →
      Causalean.Stat.Minimax.hellingerSqMeasure (densityJoint ν μ vPlus) (densityJoint ν μ vMinus) =
        (∫ ξ, hellingerEnergy μ (vPlus ξ) (vMinus ξ) ∂ν) ∧
      Causalean.Stat.tvDist (densityMixture ν μ vPlus) (densityMixture ν μ vMinus) ≤
        Real.sqrt (∫ ξ, hellingerEnergy μ (vPlus ξ) (vMinus ξ) ∂ν)) ∧
    (∀ w : ℝ, w ≠ -(1 / 4 : ℝ) → w ≠ (1 / 4 : ℝ) →
      HasDerivAt (fun x => Real.sqrt (cosSqDensity x)) (baselineSqrtDerivAt w) w) ∧
    (∫ w, baselineSqrtDerivAt w ^ 2) = 4 * Real.pi ^ 2 := by
  refine ⟨baseline_sqrt_lipschitz, baseline_derivative_energy, ?_⟩
  have htrans : ∀ s t : ℝ, (∫ w, (Real.sqrt (cosSqDensity (w - s)) -
      Real.sqrt (cosSqDensity (w - t))) ^ 2) ≤ 4 * Real.pi ^ 2 * (s - t) ^ 2 := by
    exact baseline_translation_energy
  refine ⟨htrans, ?_, ?_, ?_, ?_, baselineSqrtDerivAt_energy⟩
  · intro B s t
    have hp := hellingerEnergy_pi_le_sum
      (fun i w => cosSqDensity (w - s i)) (fun i w => cosSqDensity (w - t i))
      (fun i => (translated_cosSqDensity_integrable_normalized (s i)).1)
      (fun i => (translated_cosSqDensity_integrable_normalized (t i)).1)
      (fun _ _ => cosSqDensity_nonneg _) (fun _ _ => cosSqDensity_nonneg _)
      (fun i => (translated_cosSqDensity_integrable_normalized (s i)).2)
      (fun i => (translated_cosSqDensity_integrable_normalized (t i)).2)
    exact hp.trans (Finset.sum_le_sum (fun i _ => htrans (s i) (t i)))
  · intro Ω _ μ _ f g hf hg hf0 hg0 hfp hgp
    let _ := hfp
    let _ := hgp
    exact density_tv_le_sqrt_hellingerEnergy μ f g hf hg hf0 hg0
  · intro Ξ Ω _ _ ν _ μ _ f g hf hg hf0 hg0 hfp hgp
    exact common_marginal_hellinger_averaging ν μ f g hf hg hf0 hg0 hfp hgp
  · exact fun w hneg hpos => sqrt_cosSqDensity_hasDerivAt w hneg hpos

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
