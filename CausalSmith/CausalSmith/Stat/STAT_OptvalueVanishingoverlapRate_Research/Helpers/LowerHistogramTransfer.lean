module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerDenseFullCounts
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparseFullCounts
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerTransfer
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperRaoBlackwell
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Fibre
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.Reconstruction
public import Causalean.Stat.Minimax.MarkovKernelTransport

/-! # Fixed-sample estimators in the lower Poisson count experiment

The ordered-prefix law pays only the short-count probability. Uniform histogram
reconstruction and kernel averaging then give a deterministic, parameter-free
count estimator with the same risk bound, including parameter-dependent rates.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer
open Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram


-- @node: lowerPrefixEstimator
/-- Read a fixed prefix and project the fixed-sample estimator to the unit interval. For the displayed parameters, lowerPrefixEstimator is the object specified by this definition. -/
 noncomputable def lowerPrefixEstimator {n d : ℕ} (est : Estimator n d) (fallback : Fin n → Obs d) (s : FiniteSample (Obs d)) : ℝ := projectUnit (est.1 (orderedPrefix fallback s)) -- @node: lowerPrefixEstimator_risk_le 
/-- The exact prefix pushforward bounds its risk by fixed risk plus shortage. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:lam), the [stated conclusion](goal) holds. -/
lemma lowerPrefixEstimator_risk_le {n d : ℕ} {ε : ℝ}
    (P : ModelLaw d ε) (est : Estimator n d) (fallback : Fin n → Obs d)
    (lam : ℝ≥0) :
    Causalean.Stat.sqRisk (finitePoissonSampleLaw P.1.pmf.toMeasure lam)
      (lowerPrefixEstimator est fallback) (observedValue P.1) ≤
      observedRisk n est P + (poissonMeasure lam).real {k : ℕ | k < n} := by
  letI : IsProbabilityMeasure (productLaw P.1 n) := by
    unfold productLaw
    infer_instance
  let T : (Fin n → Obs d) → ℝ := fun o => projectUnit (est.1 o)
  let loss := fun o => (T o - observedValue P.1) ^ 2
  have hm : Measurable T := by dsimp [T]; unfold projectUnit; fun_prop
  have hl : Integrable loss (productLaw P.1 n) := Integrable.of_finite
  have hdir : Integrable loss (Measure.dirac fallback) := Integrable.of_finite
  have hgood : (poissonMeasure lam (Set.Ici n)).toReal ≤ 1 :=
    measureReal_le_one
  have hfb : loss fallback ≤ 1 := by
    have hp := projectUnit_mem_unitInterval (est.1 fallback)
    have hv := observedValue_mem_unitInterval P.1
    dsimp [loss, T]
    nlinarith [hp.1, hp.2, hv.1, hv.2]
  have hmap := map_orderedPrefix_finitePoissonSampleLaw P.1.pmf.toMeasure lam fallback
  unfold Causalean.Stat.sqRisk lowerPrefixEstimator
  change (∫ s, loss (orderedPrefix fallback s) ∂finitePoissonSampleLaw P.1.pmf.toMeasure lam) ≤ _
  rw [← integral_map (measurable_orderedPrefix fallback).aemeasurable
    (show AEStronglyMeasurable loss
      (Measure.map (orderedPrefix fallback) (finitePoissonSampleLaw P.1.pmf.toMeasure lam)) from
      (by dsimp [loss]; fun_prop)), hmap]
  change (∫ o, loss o ∂((poissonMeasure lam (Set.Ici n)) • productLaw P.1 n +
    (poissonMeasure lam (Set.Iio n)) • Measure.dirac fallback)) ≤ _
  rw [integral_add_measure (hl.smul_measure (measure_ne_top _ _))
    (hdir.smul_measure (measure_ne_top _ _)),
    integral_smul_measure, integral_smul_measure, integral_dirac]
  have hnonneg : 0 ≤ ∫ o, loss o ∂productLaw P.1 n :=
    integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ ≤ (∫ o, loss o ∂productLaw P.1 n) +
        (poissonMeasure lam (Set.Iio n)).toReal := by
      apply add_le_add
      · exact mul_le_of_le_one_left hnonneg hgood
      · exact (mul_le_mul_of_nonneg_left hfb ENNReal.toReal_nonneg).trans_eq (mul_one _)
    _ ≤ _ := add_le_add (observedRisk_projectUnit_le est P) le_rfl


-- @node: lowerHistogramEstimator
/-- Average the reconstructed prefix over all orderings of a histogram.
This estimator depends on the fixed estimator and fallback only.

For [the displayed parameters](hyp:n,d,est,fallback), [lowerHistogramEstimator](goal) is the object specified by this definition. -/
noncomputable def lowerHistogramEstimator {n d : ℕ} (est : Estimator n d)
    (fallback : Fin n → Obs d) : (Obs d → ℕ) → ℝ :=
  Causalean.Stat.kernelMean (histogramReconstructionKernel (Obs d))
    (lowerPrefixEstimator est fallback)

-- @node: measurable_lowerHistogramEstimator
/-- The deterministic count estimator is measurable on the observed histogram space. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
@[fun_prop]
lemma measurable_lowerHistogramEstimator {n d : ℕ} (est : Estimator n d)
    (fallback : Fin n → Obs d) :
    Measurable (lowerHistogramEstimator est fallback) := by
  have hprefix := measurable_orderedPrefix fallback
  unfold lowerHistogramEstimator
  apply Causalean.Stat.measurable_kernelMean
  unfold lowerPrefixEstimator projectUnit
  fun_prop


-- @node: lowerHistogramEstimator_risk_le
/-- Reconstruction followed by Jensen transfers the risk to all observed counts. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:lam), the [stated conclusion](goal) holds. -/
lemma lowerHistogramEstimator_risk_le {n d : ℕ} {ε : ℝ}
    (P : ModelLaw d ε) (est : Estimator n d) (fallback : Fin n → Obs d)
    (lam : ℝ≥0) :
    Causalean.Stat.sqRisk (independentPoissonCountLaw P.1.pmf.toMeasure lam)
      (lowerHistogramEstimator est fallback) (observedValue P.1) ≤
      observedRisk n est P + (poissonMeasure lam).real {k : ℕ | k < n} := by
  have hm : Measurable (lowerPrefixEstimator est fallback) := by
    have hprefix := measurable_orderedPrefix fallback
    unfold lowerPrefixEstimator projectUnit
    fun_prop
  have hb : Causalean.Stat.UniformlyBounded (lowerPrefixEstimator est fallback) := by
    refine ⟨1, by norm_num, fun s => ?_⟩
    have hp := projectUnit_mem_unitInterval (est.1 (orderedPrefix fallback s))
    unfold lowerPrefixEstimator
    exact (abs_le.mpr ⟨by linarith [hp.1], hp.2⟩)
  have h := Causalean.Stat.sqRisk_kernelMean_le_comp
    (independentPoissonCountLaw P.1.pmf.toMeasure lam) (histogramReconstructionKernel (Obs d))
    hm hb (observedValue P.1)
  rw [independentPoissonCountLaw_comp_reconstruction] at h
  exact h.trans (lowerPrefixEstimator_risk_le P est fallback lam)


-- @node: lowerHistogramEstimator_poisson_risk_le
/-- A mean at least Bn/2 gives the uniform shortage penalty from roadmap (49). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:lam,hn,hB,hmean), the [stated conclusion](goal) holds. -/
lemma lowerHistogramEstimator_poisson_risk_le {n d : ℕ} {ε B : ℝ}
    (P : ModelLaw d ε) (est : Estimator n d) (fallback : Fin n → Obs d)
    (lam : ℝ≥0) (hn : 1 ≤ n) (hB : 2 < B)
    (hmean : B * (n : ℝ) / 2 ≤ lam) :
    Causalean.Stat.sqRisk (independentPoissonCountLaw P.1.pmf.toMeasure lam)
      (lowerHistogramEstimator est fallback) (observedValue P.1) ≤
      observedRisk n est P + Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) := by
  exact (lowerHistogramEstimator_risk_le P est fallback lam).trans
    (add_le_add_right (poisson_shortage_uniform_le lam hn hB hmean) _)


-- @node: observed_independentPoissonCountLaw_eq
/-- Independent count rates agree with the four observed atom masses. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:lam), the [stated conclusion](goal) holds. -/
lemma observed_independentPoissonCountLaw_eq {d : ℕ} (P : DiscreteLaw d)
    (lam : ℝ≥0) :
    independentPoissonCountLaw P.pmf.toMeasure lam =
      Measure.pi fun o : Obs d => poissonMeasure (Real.toNNReal
        ((lam : ℝ) * jointMass P o.1 o.2.1 o.2.2)) := by
  unfold independentPoissonCountLaw
  congr 1
  funext o
  congr 1
  apply NNReal.eq
  simp [jointMass, PMF.toMeasure_apply_singleton, ENNReal.coe_toNNReal,
    Real.toNNReal_of_nonneg (mul_nonneg lam.coe_nonneg ENNReal.toReal_nonneg),
    NNReal.coe_mul]
  exact Or.inl rfl


-- @node: denseHistogram_fixedSample_risk_le
/-- The same parameter-free count estimator transfers every dense fibre. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi,hn,hB,hθ), the [stated conclusion](goal) holds. -/
lemma denseHistogram_fixedSample_risk_le {n d : ℕ} (hd : 0 < d)
    {ε a B : ℝ} (hε : 0 < ε) (hεhi : ε ≤ 1 / 2)
    (ha : 0 ≤ a) (hahi : a ≤ 1 / 2) (hn : 1 ≤ n) (hB : 2 < B)
    (θ : Fin d → ℝ) (hθ : ∀ x, |θ x| ≤ 1)
    (est : Estimator n d) (fallback : Fin n → Obs d) :
    Causalean.Stat.sqRisk
      (denseFullObservedPoissonKernel d (B * n * ε / d) a
        (B * n * (1 - ε) / (2 * d)) θ)
      (lowerHistogramEstimator est fallback)
      (observedValue (denseObservedLaw hd ε a hε hεhi ha hahi θ hθ)) ≤
    observedRisk n est
      ⟨denseObservedLaw hd ε a hε hεhi ha hahi θ hθ,
        (denseObservedLaw_parameters hd ε a hε hεhi ha hahi θ hθ).1⟩ +
      Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) := by
  let P : ModelLaw d ε :=
    ⟨denseObservedLaw hd ε a hε hεhi ha hahi θ hθ,
      (denseObservedLaw_parameters hd ε a hε hεhi ha hahi θ hθ).1⟩
  have hmean : 0 ≤ B * (n : ℝ) := by positivity
  have h := lowerHistogramEstimator_poisson_risk_le P est fallback
    (Real.toNNReal (B * n)) hn hB (by rw [Real.coe_toNNReal _ hmean]; nlinarith)
  rw [observed_independentPoissonCountLaw_eq,
    Real.coe_toNNReal _ hmean] at h
  rw [denseFullObservedPoissonKernel_eq hd ε a B n hε hεhi ha hahi θ hθ]
  exact h

/-- The transfer also allows the sparse total rate to depend on its normalizer. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,hM,hn,hB,hz), the [stated conclusion](goal) holds. -/
lemma sparseHistogram_fixedSample_risk_le {n d : ℕ} (hd : 2 ≤ d)
    {ε M B : ℝ} (hε : 0 < ε) (hεhi : ε ≤ 1 / 2)
    (hM : 2 ≤ M) (hn : 1 ≤ n) (hB : 2 < B)
    (θ : Fin d → ℝ) (hz : ∀ x, θ x + sparseReference (_hMpaper := hM) M ∈ Set.Icc 0 M)
    (est : Estimator n d) (fallback : Fin n → Obs d) :
    Causalean.Stat.sqRisk (sparseFullObservedPoissonKernel (hMpaper := hM) B n d ε M θ)
      (lowerHistogramEstimator est fallback)
      (observedValue (sparseLaw (by omega) ε M ⟨hε, hεhi⟩
        (fun x => θ x + sparseReference (_hMpaper := hM) M) hz)) ≤
    observedRisk n est
      ⟨sparseLaw (by omega) ε M ⟨hε, hεhi⟩
        (fun x => θ x + sparseReference (_hMpaper := hM) M) hz,
        (sparse_likelihood n d ε M B (fun x => θ x + sparseReference (_hMpaper := hM) M)
          hn hd hε hεhi hM hB hz).1⟩ +
      Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) := by
  let P : ModelLaw d ε :=
    ⟨sparseLaw (by omega) ε M ⟨hε, hεhi⟩
      (fun x => θ x + sparseReference (_hMpaper := hM) M) hz,
      (sparse_likelihood n d ε M B (fun x => θ x + sparseReference (_hMpaper := hM) M)
        hn hd hε hεhi hM hB hz).1⟩
  let S := sparseNormalizerFormula d ε M (fun x => θ x + sparseReference (_hMpaper := hM) M) hz
  have hS : 1 / 2 ≤ S := sparseNormalizer_ge_half hε.le hεhi _ hz
  have hmean : 0 ≤ B * (n : ℝ) * S := by positivity
  have h := lowerHistogramEstimator_poisson_risk_le P est fallback
    (Real.toNNReal (B * n * S)) hn hB (by
      rw [Real.coe_toNNReal _ hmean]
      nlinarith [mul_nonneg (show 0 ≤ B by linarith) (Nat.cast_nonneg n)])
  rw [observed_independentPoissonCountLaw_eq,
    Real.coe_toNNReal _ hmean] at h
  rw [sparseFullObservedPoissonKernel_eq (hMpaper := hM) (by omega) ε M B n hε hεhi θ hz]
  exact h

end CausalSmith.Stat.OptvalueVanishingoverlapRate
