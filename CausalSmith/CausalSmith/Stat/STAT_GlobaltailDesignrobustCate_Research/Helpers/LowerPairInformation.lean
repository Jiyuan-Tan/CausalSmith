module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairFiberMeans
public import Causalean.Mathlib.InformationTheory.KLBind

/-! # Conditional information in the observed binary experiment

The common control channel contributes zero divergence. Recording treatment
and covariates cannot increase the propensity-weighted treated-channel KL.
These lemmas implement the conditional-information step of equation (24) of
the lower-pair membership roadmap.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-- Finiteness of the proved quadratic bound gives absolute continuity of the
two treated channels, including points where the bump vanishes. -/
-- @node: treatedBinary_absolutelyContinuous
lemma treatedBinary_absolutelyContinuous (d : ℕ) (β δ h M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (x : Fin d → ℝ) (hx : x ∈ cube d) :
    binaryMeasure M (treatedPlusProbability d β δ h M true x) ≪
      binaryMeasure M (treatedPlusProbability d β δ h M false x) := by
  have hk := treatedBinary_klDiv_le_mean_sq d β δ h M
    hβ hδ hh hh1 hM hsmall x hx
  exact (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hk)).1

/-- For a shared Bernoulli treatment draw, the common control outcome contributes
zero KL; adding the fixed covariate coordinate is a measurable observation. -/
-- @node: binaryObservedFiber_klDiv_le
lemma binaryObservedFiber_klDiv_le (d : ℕ) (M e p r : ℝ)
    (he : e ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hac : binaryMeasure M p ≪ binaryMeasure M r) (x : Fin d → ℝ) :
    klDiv
      (ENNReal.ofReal e • (binaryMeasure M p).map (fun y => (x, true, y)) +
        ENNReal.ofReal (1 - e) • (binaryMeasure M (1 / 2)).map (fun y => (x, false, y)))
      (ENNReal.ofReal e • (binaryMeasure M r).map (fun y => (x, true, y)) +
        ENNReal.ofReal (1 - e) • (binaryMeasure M (1 / 2)).map (fun y => (x, false, y))) ≤
      ENNReal.ofReal e * klDiv (binaryMeasure M p) (binaryMeasure M r) := by
  let κ : Kernel Bool ℝ := ⟨fun a => binaryMeasure M (if a then p else 1 / 2),
    measurable_of_countable _⟩
  let η : Kernel Bool ℝ := ⟨fun a => binaryMeasure M (if a then r else 1 / 2),
    measurable_of_countable _⟩
  have : IsMarkovKernel κ := ⟨fun a => by
    cases a <;> exact binaryMeasure_isProbabilityMeasure M _ (by first | exact hp | norm_num)⟩
  have : IsMarkovKernel η := ⟨fun a => by
    cases a <;> exact binaryMeasure_isProbabilityMeasure M _ (by first | exact hr | norm_num)⟩
  have := treatmentMeasure_isProbabilityMeasure e he
  have := binaryMeasure_isProbabilityMeasure M (1 / 2) (by norm_num)
  have hchain := Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_right_of_forall_ac
    (μ := treatmentMeasure e) (κ := κ) (η := η)
    (Filter.Eventually.of_forall (fun a => by
      cases a
      · exact Measure.AbsolutelyContinuous.rfl
      · exact hac))
  have hvalue : (∫⁻ a, klDiv (κ a) (η a) ∂treatmentMeasure e) =
      ENNReal.ofReal e * klDiv (binaryMeasure M p) (binaryMeasure M r) := by
    have := binaryMeasure_isProbabilityMeasure M (2 : ℝ)⁻¹ (by norm_num)
    simp [treatmentMeasure, κ, η, lintegral_add_measure, lintegral_smul_measure]
  have hmap (k : Kernel Bool ℝ) [IsSFiniteKernel k] :
      ((treatmentMeasure e) ⊗ₘ k).map (fun z => (x, z.1, z.2)) =
        ENNReal.ofReal e • (k true).map (fun y => (x, true, y)) +
        ENNReal.ofReal (1 - e) • (k false).map (fun y => (x, false, y)) := by
    have hdir (a : Bool) : Measure.dirac a ⊗ₘ k = (k a).map (Prod.mk a) := by
      ext s hs
      rw [Measure.dirac_compProd_apply hs, Measure.map_apply (by fun_prop) hs]
    rw [treatmentMeasure, Measure.compProd_add_left, Measure.compProd_smul_left,
      Measure.compProd_smul_left, Measure.map_add _ _ (by fun_prop),
      Measure.map_smul, Measure.map_smul, hdir, hdir,
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hdp := InformationTheory.klDiv_map_le
    ((treatmentMeasure e) ⊗ₘ κ) ((treatmentMeasure e) ⊗ₘ η)
    (show Measurable (fun z : Bool × ℝ => (x, z.1, z.2)) from by fun_prop)
  rw [hmap κ, hmap η, hchain, hvalue] at hdp
  exact hdp

/-- The actual observed fiber obeys the propensity-weighted treated KL bound.
This removes the latent control draw before applying the information bound. -/
-- @node: lowerPair_observedFiber_klDiv_le
lemma lowerPair_observedFiber_klDiv_le (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (x : Fin d → ℝ) (hx : x ∈ cube d) :
    klDiv
      (((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
        (binaryMeasure M (1 / 2)).bind (fun y0 =>
          (binaryMeasure M (treatedPlusProbability d β δ h M true x)).map
            (fun y1 => (x, a, y0, y1))))).map observe)
      (((treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
        (binaryMeasure M (1 / 2)).bind (fun y0 =>
          (binaryMeasure M (treatedPlusProbability d β δ h M false x)).map
            (fun y1 => (x, a, y0, y1))))).map observe) ≤
      ENNReal.ofReal (baselinePropensity d q x) *
        klDiv (binaryMeasure M (treatedPlusProbability d β δ h M true x))
          (binaryMeasure M (treatedPlusProbability d β δ h M false x)) := by
  rw [lowerPair_observedFiber d β q h δ M hβ hδ hh hh1 hM hsmall true x hx,
    lowerPair_observedFiber d β q h δ M hβ hδ hh hh1 hM hsmall false x hx]
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall true x hx
  have hr := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall false x hx
  exact binaryObservedFiber_klDiv_le d M (baselinePropensity d q x) _ _
    (baselinePropensity_unit_interval d q hd hq x hx)
    ⟨by linarith [hp.1], by linarith [hp.2]⟩
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
    (treatedBinary_absolutelyContinuous d β δ h M hβ hδ hh hh1 hM hsmall x hx) x

/-- Averaging the observed-fiber divergence has the localized exponent `2β + D`.
The remaining global-law step is the shared-base bind chain rule. -/
-- @node: lowerPair_integrated_observedFiber_klDiv_le
lemma lowerPair_integrated_observedFiber_klDiv_le (d : ℕ) (β γ h δ M : ℝ)
    (hd : 1 ≤ d) (hγ : 1 < γ) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4) :
    (∫⁻ x in cube d, klDiv
      (((treatmentMeasure (baselinePropensity d (tailExponent γ) x)).bind (fun a =>
        (binaryMeasure M (1 / 2)).bind (fun y0 =>
          (binaryMeasure M (treatedPlusProbability d β δ h M true x)).map
            (fun y1 => (x, a, y0, y1))))).map observe)
      (((treatmentMeasure (baselinePropensity d (tailExponent γ) x)).bind (fun a =>
        (binaryMeasure M (1 / 2)).bind (fun y0 =>
          (binaryMeasure M (treatedPlusProbability d β δ h M false x)).map
            (fun y1 => (x, a, y0, y1))))).map observe)) ≤
      ENNReal.ofReal (16 * δ ^ 2 / M ^ 2 * h ^ (2 * β + effectiveDimension d γ)) := by
  have hq : 0 < tailExponent γ := by unfold tailExponent; linarith
  apply le_trans _ (treatedBinary_integrated_klDiv_le d β γ δ h M
    hd hβ hγ hδ hh hh1 hM hsmall)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact lowerPair_observedFiber_klDiv_le d β (tailExponent γ) h δ M
    hd hq hβ hδ hh hh1 hM hsmall x hx

/-- The shared-base bind chain rule transfers the localized conditional
information bound to the actual one-observation experiment. -/
-- @node: lowerPair_obs_klDiv_le
lemma lowerPair_obs_klDiv_le (d : ℕ) (β γ h δ M : ℝ)
    (hd : 1 ≤ d) (hγ : 1 < γ) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4) :
    klDiv (lowerPair d β (tailExponent γ) h δ M true).obs
      (lowerPair d β (tailExponent γ) h δ M false).obs ≤
      ENNReal.ofReal (16 * δ ^ 2 / M ^ 2 * h ^ (2 * β + effectiveDimension d γ)) := by
  classical
  have hq : 0 < tailExponent γ := by unfold tailExponent; linarith
  let F (s : Bool) (x : Fin d → ℝ) : Measure (Obs d) :=
    ENNReal.ofReal (baselinePropensity d (tailExponent γ) x) •
      (binaryMeasure M (treatedPlusProbability d β δ h M s x)).map
        (fun y => (x, true, y)) +
    ENNReal.ofReal (1 - baselinePropensity d (tailExponent γ) x) •
      (binaryMeasure M (1 / 2)).map (fun y => (x, false, y))
  have hF (s : Bool) : Measurable (F s) := by
    apply weightedChannels_measurable
    · have ht (x : Fin d → ℝ) : Measurable (fun y : ℝ => (x, true, y)) := by fun_prop
      simp_rw [binaryMeasure, Measure.map_add _ _ (ht _), Measure.map_smul,
        Measure.map_dirac' (ht _)]
      fun_prop
    · have ht (x : Fin d → ℝ) : Measurable (fun y : ℝ => (x, false, y)) := by fun_prop
      simp_rw [binaryMeasure, Measure.map_add _ _ (ht _), Measure.map_smul,
        Measure.map_dirac' (ht _)]
      fun_prop
    · exact (baselinePropensity_measurable d (tailExponent γ) hq).ennreal_ofReal
    · exact (measurable_const.sub
        (baselinePropensity_measurable d (tailExponent γ) hq)).ennreal_ofReal
  have hc : MeasurableSet (cube d) := by simp [cube]
  let K (s : Bool) : Kernel (Fin d → ℝ) (Obs d) :=
    ⟨fun x => if x ∈ cube d then F s x else 0, (hF s).ite hc measurable_const⟩
  have hprob (s : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
      IsProbabilityMeasure (F s x) := by
    have hp := treatedPlusProbability_quarter_bounds d β δ h M
      hβ hδ hh hh1 hM hsmall s x hx
    have := binaryMeasure_isProbabilityMeasure M _
      (show treatedPlusProbability d β δ h M s x ∈ Set.Icc (0 : ℝ) 1 from
        ⟨by linarith [hp.1], by linarith [hp.2]⟩)
    have := binaryMeasure_isProbabilityMeasure M (1 / 2) (by norm_num)
    have he := baselinePropensity_unit_interval d (tailExponent γ) hd hq x hx
    apply isProbabilityMeasure_iff.mpr
    dsimp [F]
    simp only [Measure.map_apply (show Measurable (fun y : ℝ => (x, true, y)) from by fun_prop)
        MeasurableSet.univ,
      Measure.map_apply (show Measurable (fun y : ℝ => (x, false, y)) from by fun_prop)
        MeasurableSet.univ, Set.preimage_univ, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add he.1 (sub_nonneg.mpr he.2)]
    simp
  have (s : Bool) : IsFiniteKernel (K s) := by
    refine ⟨⟨1, by simp, ?_⟩⟩
    intro x
    by_cases hx : x ∈ cube d
    · have := hprob s x hx
      simp [K, hx, measure_univ]
    · simp [K, hx]
  have heq (s : Bool) : (lowerPair d β (tailExponent γ) h δ M s).obs =
      (volume.restrict (cube d)).bind (K s) := by
    rw [lowerPair_obs_eq_bind_binary d β (tailExponent γ) h δ M
      hq hβ hδ hh hh1 hM hsmall s]
    apply Measure.bind_congr_right
    filter_upwards [ae_restrict_mem hc] with x hx
    simp [K, hx, F]
  have hsupp (s : Bool) : ∀ᵐ x ∂volume.restrict (cube d),
      (K s x) {z | z.1 = x}ᶜ = 0 := by
    filter_upwards [ae_restrict_mem hc] with x hx
    simp only [K, Kernel.coe_mk, if_pos hx, F, Measure.add_apply, Measure.smul_apply]
    rw [Measure.map_apply (by fun_prop) (by measurability),
      Measure.map_apply (by fun_prop) (by measurability)]
    simp
  have hac : ∀ᵐ x ∂volume.restrict (cube d), K true x ≪ K false x := by
    filter_upwards [ae_restrict_mem hc] with x hx
    simp only [K, Kernel.coe_mk, if_pos hx, F]
    exact ((treatedBinary_absolutelyContinuous d β δ h M
      hβ hδ hh hh1 hM hsmall x hx).map (by fun_prop)).smul _ |>.add
        (Measure.AbsolutelyContinuous.rfl.smul _)
  have : IsProbabilityMeasure (volume.restrict (cube d)) := by
    apply isProbabilityMeasure_iff.mpr
    simp [cube, Real.volume_Icc_pi]
  rw [heq true, heq false,
    Causalean.Mathlib.InformationTheory.Measure.klDiv_bind_eq_of_base_recording
      _ _ _ Prod.fst (by fun_prop) (by measurability) (hsupp true) (hsupp false) hac]
  apply le_trans _ (treatedBinary_integrated_klDiv_le d β γ δ h M
    hd hβ hγ hδ hh hh1 hM hsmall)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hc] with x hx
  simp only [K, Kernel.coe_mk, if_pos hx, F]
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall true x hx
  have hr := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall false x hx
  exact binaryObservedFiber_klDiv_le d M (baselinePropensity d (tailExponent γ) x) _ _
    (baselinePropensity_unit_interval d (tailExponent γ) hd hq x hx)
    ⟨by linarith [hp.1], by linarith [hp.2]⟩
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
    (treatedBinary_absolutelyContinuous d β δ h M hβ hδ hh hh1 hM hsmall x hx) x

/-- Observation preserves the normalized probability law of either witness. -/
-- @node: lowerPair_obs_isProbabilityMeasure
lemma lowerPair_obs_isProbabilityMeasure (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) : IsProbabilityMeasure (lowerPair d β q h δ M sign).obs := by
  have := lowerPair_isProbabilityMeasure d β q h δ M
    hd hq hβ hδ hh hh1 hM hsmall sign
  rw [(lowerPair_consistency d β q h δ M sign).2]
  apply Measure.isProbabilityMeasure_map
  change AEMeasurable (observe (d := d)) _
  apply Measurable.aemeasurable
  unfold observe
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.ite _ (by fun_prop) (by fun_prop)
  exact (measurableSet_singleton true).preimage (by fun_prop)

/-- Independent replication multiplies the localized information bound by the
sample size. Finiteness supplies absolute continuity and log-ratio integrability
rather than adding either as an assumption. -/
-- @node: lowerPair_product_klDiv_le
lemma lowerPair_product_klDiv_le (d n : ℕ) (β γ h δ M : ℝ)
    (hd : 1 ≤ d) (hγ : 1 < γ) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4) :
    klDiv (Measure.pi (fun _ : Fin n => (lowerPair d β (tailExponent γ) h δ M true).obs))
      (Measure.pi (fun _ : Fin n => (lowerPair d β (tailExponent γ) h δ M false).obs)) ≤
      ENNReal.ofReal (16 * δ ^ 2 / M ^ 2 * (n : ℝ) *
        h ^ (2 * β + effectiveDimension d γ)) := by
  have hq : 0 < tailExponent γ := by unfold tailExponent; linarith
  have := lowerPair_obs_isProbabilityMeasure d β (tailExponent γ) h δ M
    hd hq hβ hδ hh hh1 hM hsmall true
  have := lowerPair_obs_isProbabilityMeasure d β (tailExponent γ) h δ M
    hd hq hβ hδ hh hh1 hM hsmall false
  have hb := lowerPair_obs_klDiv_le d β γ h δ M hd hγ hβ hδ hh hh1 hM hsmall
  have hf := klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  have ht := Causalean.Mathlib.InformationTheory.productKL_tensorization n
    (lowerPair d β (tailExponent γ) h δ M true).obs
    (lowerPair d β (tailExponent γ) h δ M false).obs hf.1 hf.2
  apply (ENNReal.toReal_le_toReal ht.1 ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  calc
    _ ≤ (n : ℝ) * (klDiv (lowerPair d β (tailExponent γ) h δ M true).obs
        (lowerPair d β (tailExponent γ) h δ M false).obs).toReal := ht.2.2
    _ ≤ (n : ℝ) * (16 * δ ^ 2 / M ^ 2 * h ^ (2 * β + effectiveDimension d γ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      have hre := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      rw [ENNReal.toReal_ofReal (show 0 ≤ 16 * δ ^ 2 / M ^ 2 *
        h ^ (2 * β + effectiveDimension d γ) from by positivity)] at hre
      exact hre
    _ = _ := by ring

/-- The prescribed small-amplitude condition gives a KL constant uniform over
all admitted amplitudes, as required by the membership theorem's quantifiers. -/
-- @node: lowerPair_product_klDiv_le_unit
lemma lowerPair_product_klDiv_le_unit (d n : ℕ) (β γ h δ M : ℝ)
    (hd : 1 ≤ d) (hγ : 1 < γ) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4) :
    klDiv (Measure.pi (fun _ : Fin n => (lowerPair d β (tailExponent γ) h δ M true).obs))
      (Measure.pi (fun _ : Fin n => (lowerPair d β (tailExponent γ) h δ M false).obs)) ≤
      ENNReal.ofReal ((n : ℝ) * h ^ (2 * β + effectiveDimension d γ)) := by
  apply (lowerPair_product_klDiv_le d n β γ h δ M
    hd hγ hβ hδ hh hh1 hM hsmall).trans
  apply ENNReal.ofReal_le_ofReal
  have hcoef : 16 * δ ^ 2 / M ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
    have hscaled : 4 * δ ≤ M := by linarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ M - 4 * δ)
      (by positivity : 0 ≤ M + 4 * δ)]
  calc
    _ ≤ 1 * (n : ℝ) * h ^ (2 * β + effectiveDimension d γ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n)) (by positivity)
    _ = _ := by ring

end CausalSmith.Stat.GlobalTailDesignRobustCate
