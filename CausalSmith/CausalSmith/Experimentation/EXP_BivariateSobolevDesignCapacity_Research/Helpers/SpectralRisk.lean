module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionTransfer

/-! # Fourier representation of the spectral seed-image design

The torus kernel averages only the fresh rounding seeds. Reflection and the common
shift are then transported by the proved reflection identity.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Joint measurability of rounding on the torus feature rows. This uses [the stated conclusion](goal). -/
-- @node: torusRounding_measurable
@[fun_prop] lemma torusRounding_measurable (n d : ℕ) :
    Measurable (fun p : (Fin n → Torus d) × RoundingSeeds n =>
      orderedBoundaryRounding n (spectralRows p.1) p.2) := by
  have hround := (ordered_prefix_rounding n (fun _ _ => 0) 0
    (by intros; simp)).1
  have hfeatures (h : ℕ) : Measurable (features d h) := by
    unfold features ek
    split <;> fun_prop
  have hrows : Measurable (fun w : Fin n → Torus d => spectralRows w) := by
    apply measurable_pi_lambda
    intro h
    apply measurable_pi_lambda
    intro i
    exact (hfeatures (h.val + 1)).comp (measurable_pi_apply i)
  exact hround.comp ((hrows.comp measurable_fst).prodMk measurable_snd)

/-- The fresh-seed kernel on torus samples. -/
-- @node: torusRoundingKernel
def torusRoundingKernel (n d : ℕ) : Kernel (Fin n → Torus d) (Signs n) :=
  ⟨fun w => (roundingSeedLaw n).map (orderedBoundaryRounding n (spectralRows w)), by
    letI : IsProbabilityMeasure (roundingSeedLaw n) := by
      unfold roundingSeedLaw
      infer_instance
    have h := (Measure.measurable_map _ (torusRounding_measurable n d)).comp
      (Measurable.map_prodMk_left (ν := roundingSeedLaw n)
        (α := Fin n → Torus d))
    simpa only [Function.comp_def, Measure.map_map (torusRounding_measurable n d)
      measurable_prodMk_left] using h⟩

/-- Rounding seed images are probability measures. -/
-- @node: torusRoundingKernel_markov
instance torusRoundingKernel_markov (n d : ℕ) :
    IsMarkovKernel (torusRoundingKernel n d) := by
  letI : IsProbabilityMeasure (roundingSeedLaw n) := by
    unfold roundingSeedLaw
    infer_instance
  constructor
  intro w
  exact Measure.isProbabilityMeasure_map
    (((torusRounding_measurable n d).comp
      (measurable_const.prodMk measurable_id)).aemeasurable)

/-- Integrating the torus kernel is exactly integrating the fresh rounding seeds.](goal) Under [the stated conditions](hyp:f,hf). This uses [the stated conclusion](goal). -/
-- @node: torusRoundingKernel_lintegral
lemma torusRoundingKernel_lintegral (n d : ℕ) (w : Fin n → Torus d)
    (f : Signs n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂torusRoundingKernel n d w) =
      ∫⁻ seeds, f (orderedBoundaryRounding n (spectralRows w) seeds)
        ∂roundingSeedLaw n := by
  change (∫⁻ z, f z ∂(roundingSeedLaw n).map
    (orderedBoundaryRounding n (spectralRows w))) = _
  have hg : Measurable (orderedBoundaryRounding n (spectralRows w)) :=
    (orderedBoundaryRounding_measurable n).comp
      (measurable_const.prodMk measurable_id)
  exact lintegral_map hf hg

/-- [ The original-sample kernel averages the torus kernel over reflection and shift.](goal) Under [the stated conditions](hyp:f,hf). -/
-- @node: spectralRoundingKernel_lintegral
lemma spectralRoundingKernel_lintegral (n d : ℕ) (x : Covariates n d)
    (f : Signs n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂spectralRoundingKernel n d x) =
      ∫⁻ η, ∫⁻ t, ∫⁻ z, f z ∂torusRoundingKernel n d (shiftedSample x η t)
        ∂torusMeasure d ∂reflectionLaw n d := by
  letI : IsProbabilityMeasure (roundingSeedLaw n) := by
    unfold roundingSeedLaw; infer_instance
  have hm : Measurable (spectralSigns x) := by fun_prop
  change (∫⁻ z, f z ∂(spectralSeedLaw n d).map (spectralSigns x)) = _
  rw [lintegral_map hf hm]
  unfold spectralSeedLaw
  rw [lintegral_prod]
  rotate_left
  · exact (hf.comp hm).aemeasurable
  apply lintegral_congr
  intro η
  rw [lintegral_prod]
  rotate_left
  · exact ((hf.comp hm).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
  apply lintegral_congr
  intro t
  exact (torusRoundingKernel_lintegral n d (shiftedSample x η t) f hf).symm

/-- [ Exact Fourier loss representation for the spectral branch of the design.](goal) Under [the stated conditions](hyp:hd). -/
-- @node: spectralRounding_loss_fourier
lemma spectralRounding_loss_fourier (n d : ℕ) (hd : 0 < d)
    (m : CenteredL2Fn d) :
    loss ⟨spectralRoundingKernel n d, spectralRoundingKernel_markov n d⟩ m.val =
      ENNReal.ofReal (4 / (n : ℝ)) *
        ∑' k : Fin d → ℤ, ENNReal.ofReal ‖Fhat m.val k‖ ^ 2 *
          ∫⁻ w, ∫⁻ seeds, ENNReal.ofReal ‖∑ i,
            (sgn (orderedBoundaryRounding n (spectralRows w) seeds i) : ℂ) *
              ek k (w i)‖ ^ 2 ∂roundingSeedLaw n
            ∂Measure.pi (fun _ : Fin n => torusMeasure d) := by
  unfold loss
  congr 1
  have hpoint (x : Covariates n d) := spectralRoundingKernel_lintegral n d x
    (fun z => ENNReal.ofReal ((∑ i, sgn (z i) * m.val (x i)) ^ 2)) (by fun_prop)
  simp_rw [hpoint]
  have hm : Measurable (fun p : (Covariates n d ×
      (ReflectionCoins n d × Torus d)) × Signs n =>
      ENNReal.ofReal |∑ i, sgn (p.2 i) * m.val (p.1.1 i)| ^ 2) := by
    have := m.property.1
    fun_prop
  have hshift : Measurable (fun p : Covariates n d ×
      (ReflectionCoins n d × Torus d) => shiftedSample p.1 p.2.1 p.2.2) := by
    unfold shiftedSample lift
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    have hcoin : Measurable (fun p : Covariates n d ×
        (ReflectionCoins n d × Torus d) => p.2.1 i j) := by fun_prop
    exact ((AddCircle.continuous_mk' (1 : ℝ)).measurable.comp
      (Measurable.ite (hcoin (measurableSet_singleton true))
        (by fun_prop) (by fun_prop))).add (by fun_prop)
  let ρ := (torusRoundingKernel n d).comap
    (fun p : Covariates n d × (ReflectionCoins n d × Torus d) =>
      shiftedSample p.1 p.2.1 p.2.2) hshift
  have hint : Measurable (fun p : Covariates n d ×
      (ReflectionCoins n d × Torus d) =>
      ∫⁻ z, ENNReal.ofReal |∑ i, sgn (z i) * m.val (p.1 i)| ^ 2
        ∂torusRoundingKernel n d (shiftedSample p.1 p.2.1 p.2.2)) :=
    hm.lintegral_kernel_prod_right' (κ := ρ)
  have hX : UniformDraw (covLaw n d) (id : Covariates n d → Covariates n d) :=
    ⟨measurable_id, Measure.map_id⟩
  have h := reflection_kernel_fourier_identity hd m (Covariates n d)
    (covLaw n d) id hX (torusRoundingKernel n d)
  simp only [id_eq] at h
  rw [lintegral_prod _ hint.aemeasurable] at h
  have hη (x : Covariates n d) := hint.comp (measurable_prodMk_left (x := x))
  dsimp only [Function.comp_def] at hη
  have hassoc : (∫⁻ x, ∫⁻ η, ∫⁻ t, ∫⁻ z,
      ENNReal.ofReal ((∑ i, sgn (z i) * m.val (x i)) ^ 2)
        ∂torusRoundingKernel n d (shiftedSample x η t)
        ∂torusMeasure d ∂reflectionLaw n d ∂covLaw n d) =
      ∫⁻ x, ∫⁻ p : ReflectionCoins n d × Torus d, ∫⁻ z,
        ENNReal.ofReal |∑ i, sgn (z i) * m.val (x i)| ^ 2
          ∂torusRoundingKernel n d (shiftedSample x p.1 p.2)
          ∂(reflectionLaw n d).prod (torusMeasure d) ∂covLaw n d := by
    apply lintegral_congr
    intro x
    rw [lintegral_prod]
    · simp only [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
    · exact (hη x).aemeasurable
  rw [hassoc, h]
  apply tsum_congr
  intro k
  congr 1
  apply lintegral_congr
  intro w
  exact torusRoundingKernel_lintegral n d w _ (by fun_prop)

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
