module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionBudgetTransport
public import Causalean.Mathlib.Analysis.Fourier

/-! # Zero-order reflection endpoint

Angular Plancherel and restriction to the unit cube prove the zero-order
reflection contraction for every admissible whole-space extension. Taking the
extension infimum also bounds cube L² energy by each nonnegative Sobolev norm.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Euclidean coordinates preserve the restricted unit-cube measure.](goal) -/
-- @node: euclideanCube_coordinates_measurePreserving
lemma euclideanCube_coordinates_measurePreserving (p : ℕ) :
    MeasurePreserving (fun u : EuclideanSpace ℝ (Fin p) => (fun j => u j))
      (volume.restrict (euclideanCube p)) (cubeMeasure p) := by
  have h :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin p)).restrict_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin p → ℝ)).symm.measurableEmbedding
    (Set.univ.pi (fun _ : Fin p => Icc (0 : ℝ) 1))
  simpa only [cubeMeasure, volume_pi, Measure.restrict_pi_pi, euclideanCube,
    Set.preimage, Set.mem_pi, Set.mem_univ, forall_const] using! h

/-- Restricted Euclidean and product-cube nonnegative integrals agree, including infinite values. Under [the stated conditions](hyp:f), [the asserted mathematical result follows](goal). -/
-- @node: cube_lintegral_euclidean_coordinates
lemma cube_lintegral_euclidean_coordinates (p : ℕ) (f : Cube p → ℝ≥0∞) :
    (∫⁻ u, f (fun j => u j) ∂volume.restrict (euclideanCube p)) =
      ∫⁻ x, f x ∂cubeMeasure p := by
  exact (euclideanCube_coordinates_measurePreserving p).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin p → ℝ)).symm.measurableEmbedding f

/-- [ Every admissible extension has at least the cube's squared L² energy.](goal) Under [the stated conditions](hyp:hG). -/
-- @node: cube_l2Energy_le_extension_l2Energy
lemma cube_l2Energy_le_extension_l2Energy {p : ℕ} (g : Cube p → ℝ)
    (G : EuclideanSpace ℝ (Fin p) → ℂ)
    (hG : G =ᵐ[volume.restrict (euclideanCube p)] fun u => (g (fun j => u j) : ℂ)) :
    (∫⁻ x, ENNReal.ofReal |g x| ^ 2 ∂cubeMeasure p) ≤
      ∫⁻ u, ENNReal.ofReal (‖G u‖ ^ 2) := by
  rw [← cube_lintegral_euclidean_coordinates p]
  calc
    _ = ∫⁻ u, ENNReal.ofReal (‖G u‖ ^ 2) ∂volume.restrict (euclideanCube p) := by
      apply lintegral_congr_ae
      filter_upwards [hG] with u hu
      rw [hu, Complex.norm_real, Real.norm_eq_abs, ENNReal.ofReal_pow (abs_nonneg _)]
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl

/-- [ Angular Plancherel gives the exact norm-one zero-order reflection endpoint.](goal) Under [the stated conditions](hyp:hp,hg,hLp,hG1,hG2,hG). -/
-- @node: componentFourierBudget_zero_le_extension
lemma componentFourierBudget_zero_le_extension {p : ℕ} (hp : 0 < p)
    (g : Cube p → ℝ) (hg : Measurable g) (hLp : MemLp g 2 (cubeMeasure p))
    (G : EuclideanSpace ℝ (Fin p) → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hG : G =ᵐ[volume.restrict (euclideanCube p)] fun u => (g (fun j => u j) : ℂ)) :
    componentFourierBudget p 0 g ≤ ∫⁻ ω, ENNReal.ofReal (‖Fourier G ω‖ ^ 2) := by
  rw [componentFourierBudget_zero hp g hg hLp]
  change _ ≤ ∫⁻ ω, ENNReal.ofReal (‖Causalean.Mathlib.Analysis.Fourier.angularFourier G ω‖ ^ 2)
  rw [Causalean.Mathlib.Analysis.Fourier.angular_plancherel_integral G hG1 hG2]
  exact cube_l2Energy_le_extension_l2Energy g G hG

/-- [ Nonnegative Sobolev weights dominate the cube energy for every extension;
therefore the same bound survives taking the extension infimum.](goal) Under [the stated conditions](hyp:hs). -/
-- @node: cube_l2Energy_le_sobolevNormSq
lemma cube_l2Energy_le_sobolevNormSq {p : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (g : Cube p → ℝ) :
    (∫⁻ x, ENNReal.ofReal |g x| ^ 2 ∂cubeMeasure p) ≤ sobolevNormSq p s g := by
  unfold sobolevNormSq
  refine le_iInf fun G => le_iInf fun hG => ?_
  have he := cube_l2Energy_le_extension_l2Energy g G hG.2.2
  have hp := Causalean.Mathlib.Analysis.Fourier.angular_plancherel_integral G hG.1 hG.2.1
  change (∫⁻ ω, ENNReal.ofReal (‖Fourier G ω‖ ^ 2)) = _ at hp
  rw [← hp] at he
  refine he.trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_)
  have hw : 1 ≤ (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s :=
    Real.one_le_rpow (by
      have hn : 0 ≤ ‖ω‖ ^ 2 / (p : ℝ) := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
      linarith) hs
  exact le_mul_of_one_le_right (sq_nonneg _) hw

/-- [ The zero-order reflected Fourier mass is bounded by the restriction norm
at every nonnegative exponent, with constant one and no attainment assumption.](goal) Under [the stated conditions](hyp:hp,hs,hg,hLp). -/
-- @node: componentFourierBudget_zero_le_sobolevNormSq
lemma componentFourierBudget_zero_le_sobolevNormSq {p : ℕ} (hp : 0 < p)
    {s : ℝ} (hs : 0 ≤ s) (g : Cube p → ℝ) (hg : Measurable g)
    (hLp : MemLp g 2 (cubeMeasure p)) :
    componentFourierBudget p 0 g ≤ sobolevNormSq p s g := by
  rw [componentFourierBudget_zero hp g hg hLp]
  exact cube_l2Energy_le_sobolevNormSq hs g

/-- Folding into Euclidean coordinates preserves normalized cube measure. [The asserted mathematical result follows](goal). -/
-- @node: foldEuclidean_measurePreserving
lemma foldEuclidean_measurePreserving (p : ℕ) :
    MeasurePreserving (fun y : Torus p => WithLp.toLp 2 (fold y))
      (torusMeasure p) (volume.restrict (euclideanCube p)) := by
  have he : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin p → ℝ)).symm
      (volume.restrict (euclideanCube p)) (cubeMeasure p) := by
    exact euclideanCube_coordinates_measurePreserving p
  exact (he.symm (MeasurableEquiv.toLp 2 (Fin p → ℝ)).symm).comp (fold_measurePreserving p)

/-- [ Restriction of whole-space L² equivalence classes to the cube as a linear map. -/
-- @node: euclideanCubeRestrictionLinear
def euclideanCubeRestrictionLinear (p : ℕ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))) →ₗ[ℝ]
      Lp ℂ 2 (volume.restrict (euclideanCube p)) where
  toFun f := ((MeasureTheory.Lp.memLp f).restrict (euclideanCube p)).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [((MeasureTheory.Lp.memLp f).restrict (euclideanCube p)).coeFn_toLp,
      ((MeasureTheory.Lp.memLp g).restrict (euclideanCube p)).coeFn_toLp,
      ((MeasureTheory.Lp.memLp (f + g)).restrict (euclideanCube p)).coeFn_toLp,
      (ae_restrict_of_ae (Lp.coeFn_add f g)),
      Lp.coeFn_add (((MeasureTheory.Lp.memLp f).restrict (euclideanCube p)).toLp f)
        (((MeasureTheory.Lp.memLp g).restrict (euclideanCube p)).toLp g)]
        with x hf hg hfg hadd hradd
    simp only [hfg, hradd, hf, hg, hadd, Pi.add_apply]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [((MeasureTheory.Lp.memLp f).restrict (euclideanCube p)).coeFn_toLp,
      ((MeasureTheory.Lp.memLp (c • f)).restrict (euclideanCube p)).coeFn_toLp,
      (ae_restrict_of_ae (Lp.coeFn_smul c f)),
      Lp.coeFn_smul c (((MeasureTheory.Lp.memLp f).restrict (euclideanCube p)).toLp f)]
        with x hf hcf hsmul hrsmul
    simp only [RingHom.id_apply, hcf, hrsmul, hf, hsmul, Pi.smul_apply]

/-- The restriction map has norm at most one.](goal) This uses [the stated conclusion](goal). -/
-- @node: euclideanCubeRestrictionLinear_norm_le
lemma euclideanCubeRestrictionLinear_norm_le (p : ℕ)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    ‖euclideanCubeRestrictionLinear p f‖ ≤ ‖f‖ := by
  change ‖((MeasureTheory.Lp.memLp f).restrict (euclideanCube p)).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (MeasureTheory.Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_measure f Measure.restrict_le_self)

/-- [ The common even-reflection operator on whole-space L² equivalence classes.
Restriction is a contraction and the subsequent folded pullback is an isometry. -/
-- @node: reflectionL2Operator
def reflectionL2Operator (p : ℕ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))) →L[ℝ]
      Lp ℂ 2 (torusMeasure p) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun y : Torus p => WithLp.toLp 2 (fold y))
    (foldEuclidean_measurePreserving p)).toContinuousLinearMap.comp
    ((euclideanCubeRestrictionLinear p).mkContinuous 1 (by
      intro f
      simpa using euclideanCubeRestrictionLinear_norm_le p f))

/-- The actual even-reflection L² operator has endpoint norm at most one.](goal) This uses [the stated conclusion](goal). -/
-- @node: reflectionL2Operator_norm_le
lemma reflectionL2Operator_norm_le (p : ℕ) : ‖reflectionL2Operator p‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound (reflectionL2Operator p) (by norm_num) ?_
  intro f
  simp only [reflectionL2Operator, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearMap.mkContinuous_apply]
  change ‖Lp.compMeasurePreserving _ (foldEuclidean_measurePreserving p)
    (euclideanCubeRestrictionLinear p f)‖ ≤ 1 * ‖f‖
  rw [Lp.norm_compMeasurePreserving, one_mul]
  exact euclideanCubeRestrictionLinear_norm_le p f

/-- [ The L² operator is the genuine folded pullback, independently of representatives.](goal) -/
-- @node: reflectionL2Operator_coeFn
lemma reflectionL2Operator_coeFn (p : ℕ)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    reflectionL2Operator p f =ᵐ[torusMeasure p]
      fun y => f (WithLp.toLp 2 (fold y)) := by
  have h := Lp.coeFn_compMeasurePreserving
    (euclideanCubeRestrictionLinear p f) (foldEuclidean_measurePreserving p)
  have hr := (foldEuclidean_measurePreserving p).quasiMeasurePreserving.ae
    ((MeasureTheory.Lp.memLp f).restrict (euclideanCube p)).coeFn_toLp
  exact h.trans hr

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
