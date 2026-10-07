module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerDense
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparseCalibration

/-! # Dense target concentration and fuzzy testing

The target in (46) is the average positive part of the symmetric prior
parameters. Its variance is at most a²/d, giving the dense testing step (48).
The extension below clips only outside the legal prior support.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.Minimax.FuzzyHypotheses
open scoped BigOperators

-- @node: densePositivePart
/-- For [the displayed parameters](hyp:t), [densePositivePart](goal) is the object specified by this definition. -/
noncomputable def densePositivePart (t : ℝ) : ℝ := min 1 (max t 0)

-- @node: densePriorTarget
/-- For [the displayed parameters](hyp:d,a), [densePriorTarget](goal) is the object specified by this definition. -/
noncomputable def densePriorTarget (d : ℕ) (a : ℝ) (θ : Fin d → ℝ) : ℝ :=
  1 / 2 + a * ((∑ x, densePositivePart (θ x)) / d)

-- @node: measurable_densePositivePart
/-- The positive-part extension is measurable. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
@[fun_prop]
lemma measurable_densePositivePart : Measurable densePositivePart := by
  unfold densePositivePart
  fun_prop

-- @node: measurable_densePriorTarget
/-- The extended dense target is measurable. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
@[fun_prop]
lemma measurable_densePriorTarget (d : ℕ) (a : ℝ) : Measurable (densePriorTarget d a) := by
  unfold densePriorTarget
  fun_prop

-- @node: densePositivePart_eq
/-- On the legal support the extension gives exactly the summand in (46). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:ht), the [stated conclusion](goal) holds. -/
lemma densePositivePart_eq {t : ℝ} (ht : |t| ≤ 1) :
    densePositivePart t = (|t| + t) / 2 := by
  rw [densePositivePart, min_eq_right (max_le (le_trans (le_abs_self t) ht) (by norm_num))]
  by_cases h : 0 ≤ t
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right (le_of_not_ge h), abs_of_nonpos (le_of_not_ge h)]; ring

-- @node: densePositivePart_integral
/-- Symmetry identifies the positive-part expectation with half the absolute moment. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hsupp,hsym), the [stated conclusion](goal) holds. -/
lemma densePositivePart_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : IsSupportedOnUnitInterval ν) (hsym : IsSymmetric ν) :
    (∫ t, densePositivePart t ∂ν) = (∫ t, |t| ∂ν) / 2 := by
  have hs : ∀ᵐ t ∂ν, |t| ≤ 1 :=
    (mem_ae_iff_prob_eq_one (measurableSet_le (by fun_prop) measurable_const)).2
      (dense_prior_support_radius_one ν hsupp)
  have hi : MemLp (fun t : ℝ => t) 2 ν :=
    MemLp.of_bound (by fun_prop) 1 (hs.mono fun t ht => by simpa using ht)
  have ha : Integrable (fun t : ℝ => |t|) ν := (hi.integrable (by norm_num)).abs
  calc
    _ = ∫ t, (|t| + t) / 2 ∂ν := integral_congr_ae (hs.mono fun t ht => densePositivePart_eq ht)
    _ = (∫ t, |t| ∂ν) / 2 := by
      rw [integral_div, integral_add ha (hi.integrable (by norm_num)),
        dense_symmetric_integral_id_zero ν hsym, add_zero]

-- @node: dense_product_prior_target_integral_sq_le
/-- Independent dense prior coordinates concentrate the target around its symmetric scalar center, with no assumed concentration inequality. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hsupp,hsym), the [stated conclusion](goal) holds. -/
lemma dense_product_prior_target_integral_sq_le {d : ℕ} (hd : 0 < d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsupp : IsSupportedOnUnitInterval ν)
    (hsym : IsSymmetric ν) (a : ℝ) :
    (∫ θ, (densePriorTarget d a θ - (1 / 2 + a * (∫ t, |t| ∂ν) / 2)) ^ 2
      ∂productPrior d ν) ≤ a ^ 2 / d := by
  let μ := productPrior d ν
  let : IsProbabilityMeasure μ := by dsimp [μ, productPrior]; infer_instance
  let Z : Fin d → (Fin d → ℝ) → ℝ := fun x θ => densePositivePart (θ x)
  have hm (x : Fin d) : Measurable (Z x) := by dsimp [Z]; fun_prop
  have hb (x : Fin d) (θ : Fin d → ℝ) : Z x θ ∈ Set.Icc 0 1 :=
    ⟨le_min (by norm_num) (le_max_right _ _), min_le_left _ _⟩
  have hLp (x : Fin d) : MemLp (Z x) 2 μ :=
    MemLp.of_bound (hm x).aestronglyMeasurable 1 (ae_of_all _ fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb x θ).1]; exact (hb x θ).2)
  have hv (x : Fin d) : variance (Z x) μ ≤ 1 := by
    apply (variance_le_sq_of_bounded (ae_of_all _ (hb x)) (hm x).aemeasurable).trans
    norm_num
  have hind : iIndepFun Z μ := iIndepFun_pi (fun _ => measurable_densePositivePart.aemeasurable)
  let H := fun θ : Fin d → ℝ => (∑ x, Z x θ) / d
  have hHi : Integrable H μ :=
    (integrable_finsetSum _ (fun x _ => (hLp x).integrable (by norm_num))).div_const _
  have hHe : (∫ θ, H θ ∂μ) = (∫ t, |t| ∂ν) / 2 := by
    dsimp [H]
    rw [integral_div, integral_finsetSum _ (fun x _ => (hLp x).integrable (by norm_num))]
    have he (x : Fin d) : (∫ θ, Z x θ ∂μ) = (∫ t, |t| ∂ν) / 2 := by
      exact ((measurePreserving_eval (fun _ : Fin d => ν) x).hasLaw.integral_comp
        measurable_densePositivePart.aestronglyMeasurable).trans
          (densePositivePart_integral ν hsupp hsym)
    simp_rw [he]
    simp [ne_of_gt (Nat.cast_pos.mpr hd : (0 : ℝ) < d)]
  have hTm : Measurable (fun θ => 1 / 2 + a * H θ) := by dsimp [H, Z]; fun_prop
  have hTe : (∫ θ, (1 / 2 + a * H θ) ∂μ) = 1 / 2 + a * (∫ t, |t| ∂ν) / 2 := by
    rw [integral_add (integrable_const _) (hHi.const_mul _), integral_const_mul, hHe]
    simp; ring
  have hvar := sparse_independent_average_variance_le μ hd Z 1 hLp hind hv
  have heq : variance (fun θ => 1 / 2 + a * H θ) μ =
      ∫ θ, (densePriorTarget d a θ - (1 / 2 + a * (∫ t, |t| ∂ν) / 2)) ^ 2 ∂μ := by
    rw [variance_eq_integral hTm.aemeasurable, hTe]
    rfl
  change _ ≤ a ^ 2 / d
  rw [← heq, variance_const_add (hHi.aestronglyMeasurable.const_mul a), variance_const_mul]
  exact (mul_le_mul_of_nonneg_left hvar (sq_nonneg a)).trans_eq (by ring)

-- @node: dense_product_prior_target_tail_le
/-- Chebyshev supplies the dense prior target-deviation probabilities. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hsupp,hsym,hr), the [stated conclusion](goal) holds. -/
lemma dense_product_prior_target_tail_le {d : ℕ} (hd : 0 < d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsupp : IsSupportedOnUnitInterval ν)
    (hsym : IsSymmetric ν) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (productPrior d ν).real
      {θ | r < |densePriorTarget d a θ - (1 / 2 + a * (∫ t, |t| ∂ν) / 2)|} ≤
      a ^ 2 / (d * r ^ 2) := by
  let μ := productPrior d ν
  let : IsProbabilityMeasure μ := by dsimp [μ, productPrior]; infer_instance
  let center := 1 / 2 + a * (∫ t, |t| ∂ν) / 2
  have hcoord (x : Fin d) : MemLp (fun θ : Fin d → ℝ => densePositivePart (θ x)) 2 μ :=
    MemLp.of_bound (measurable_densePositivePart.comp (measurable_pi_apply x)).aestronglyMeasurable 1 (ae_of_all μ fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) (le_max_right _ _))]
      exact min_le_left _ _)
  have hsum : MemLp (fun θ : Fin d → ℝ => (∑ x, densePositivePart (θ x)) / d) 2 μ := by
    simpa only [div_eq_mul_inv] using
      (memLp_finsetSum Finset.univ (fun x _ => hcoord x)).mul_const (d : ℝ)⁻¹
  have hc : MemLp (fun _ : Fin d → ℝ => (1 / 2 : ℝ)) 2 μ := memLp_const _
  have hLp : MemLp (densePriorTarget d a) 2 μ := hc.add (hsum.const_mul a)
  have hint := (hLp.sub (memLp_const center)).integrable_sq
  have hsub : {θ | r < |densePriorTarget d a θ - center|} ⊆
      {θ | r ^ 2 ≤ (densePriorTarget d a θ - center) ^ 2} := by
    intro θ hθ
    change r < |densePriorTarget d a θ - center| at hθ
    change r ^ 2 ≤ (densePriorTarget d a θ - center) ^ 2
    nlinarith [sq_abs (densePriorTarget d a θ - center), abs_nonneg (densePriorTarget d a θ - center)]
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun θ => sq_nonneg (densePriorTarget d a θ - center)) hint (r ^ 2)
  have hb : r ^ 2 * μ.real {θ | r < |densePriorTarget d a θ - center|} ≤ a ^ 2 / d :=
    ((mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg r)).trans hmark).trans
      (dense_product_prior_target_integral_sq_le hd ν hsupp hsym a)
  change μ.real {θ | r < |densePriorTarget d a θ - center|} ≤ _
  calc
    _ ≤ (a ^ 2 / d) / r ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hr)).2 (by simpa only [mul_comm] using hb)
    _ = _ := by ring

-- @node: denseProductPoissonKernel
/-- For [the displayed parameters](hyp:d,r,a), [denseProductPoissonKernel](goal) is the object specified by this definition. -/
noncomputable def denseProductPoissonKernel (d : ℕ) (r a : ℝ) :
    Kernel (Fin d → ℝ) (Fin d → (Fin 2 → ℕ)) where
  toFun θ := Measure.pi fun x => denseTreatedKernel r a (θ x)
  measurable' := by
    let (t : ℝ) : IsProbabilityMeasure (denseTreatedKernel r a t) := by
      change IsProbabilityMeasure (denseTreatedLaw r a t)
      unfold denseTreatedLaw; infer_instance
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hatom (N : Fin d → (Fin 2 → ℕ)) :
        Measurable (fun θ : Fin d → ℝ =>
          (Measure.pi fun x => denseTreatedKernel r a (θ x)) {N}) := by
      simp only [Measure.pi_singleton]
      apply Finset.measurable_prod
      intro x _
      exact ((denseTreatedKernel r a).measurable_coe
        (measurableSet_singleton _)).comp (measurable_pi_apply x)
    simp_rw [← Measure.tsum_indicator_apply_singleton _ s hs]
    apply Measurable.tsum
    intro N
    by_cases hN : N ∈ s
    · simpa [Set.indicator_of_mem hN] using hatom N
    · simp [Set.indicator_of_notMem hN]

-- @node: denseProductPoissonKernel_probability
/-- The product kernel has probability fibres. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma denseProductPoissonKernel_probability (d : ℕ) (r a : ℝ) (θ : Fin d → ℝ) :
    IsProbabilityMeasure (denseProductPoissonKernel d r a θ) := by
  change IsProbabilityMeasure (Measure.pi fun x => denseTreatedLaw r a (θ x))
  unfold denseTreatedLaw; infer_instance

-- @node: dense_product_prior_predictive_eq
/-- Mixing the product kernel gives the predictive law of the proved TV bound. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma dense_product_prior_predictive_eq (d : ℕ) (r a : ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    priorPredictive (productPrior d ν) (denseProductPoissonKernel d r a) =
      productPriorPredictive d ν (denseTreatedKernel r a) := by
  apply priorPredictive_productPrior_eq_productPriorPredictive
  · intro t
    change IsProbabilityMeasure (denseTreatedLaw r a t)
    unfold denseTreatedLaw; infer_instance
  · intro θ; rfl

-- @node: dense_product_prior_bayesRisk_lower
/-- The dense fuzzy-testing step (48): concentration and likelihood TV are both derived; the alphabet condition makes target deviations negligible. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma dense_product_prior_bayesRisk_lower :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (K d : ℕ) (P : AbsMomentMatchedPriors K) (r a : ℝ),
        2 ≤ d → 0 < r → 0 < a → a ≤ 1 / 2 →
        C * logAlphabet d ≤ K → r * a ^ 2 ≤ η * K →
        let Delta := a * ((∫ t, |t| ∂P.ν₁) - (∫ t, |t| ∂P.ν₀)) / 2
        128 * a ^ 2 ≤ d * Delta ^ 2 → 0 < Delta →
        ∀ est : (Fin d → (Fin 2 → ℕ)) → ℝ, Measurable est →
          ENNReal.ofReal (5 * Delta ^ 2 / 256) ≤
            max (bayesSquaredRisk (productPrior d P.ν₀)
                  (denseProductPoissonKernel d r a) (densePriorTarget d a) est)
                (bayesSquaredRisk (productPrior d P.ν₁)
                  (denseProductPoissonKernel d r a) (densePriorTarget d a) est) := by
  obtain ⟨η, C, hη, hC, htvbound⟩ := dense_product_mixture_tv_le_one_eighth
  refine ⟨η, C, hη, hC, ?_⟩
  intro K d P r a hd hr ha hahi hK hband
  dsimp only
  intro hsize hDelta est hest
  let := P.probability₀
  let := P.probability₁
  let : IsProbabilityMeasure (productPrior d P.ν₀) := by unfold productPrior; infer_instance
  let : IsProbabilityMeasure (productPrior d P.ν₁) := by unfold productPrior; infer_instance
  let Delta := a * ((∫ t, |t| ∂P.ν₁) - (∫ t, |t| ∂P.ν₀)) / 2
  have ht (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (hsupp : IsSupportedOnUnitInterval ν) (hsym : IsSymmetric ν) :
      (productPrior d ν).real
        {θ | Delta / 4 < |densePriorTarget d a θ - (1 / 2 + a * (∫ t, |t| ∂ν) / 2)|} ≤ 1 / 8 := by
    apply (dense_product_prior_target_tail_le (by omega) ν hsupp hsym a
      (show 0 < Delta / 4 by positivity)).trans
    apply (div_le_iff₀ (by positivity : 0 < (d : ℝ) * (Delta / 4) ^ 2)).2
    have hsize' : 128 * a ^ 2 ≤ d * Delta ^ 2 := hsize
    nlinarith only [hsize']
  have htv : Causalean.Stat.tvDist
      (priorPredictive (productPrior d P.ν₀) (denseProductPoissonKernel d r a))
      (priorPredictive (productPrior d P.ν₁) (denseProductPoissonKernel d r a)) ≤ 1 / 8 := by
    rw [dense_product_prior_predictive_eq, dense_product_prior_predictive_eq]
    exact htvbound K d P r a hd hr ha.le hahi hK hband
  have hb := twoFuzzyHypotheses_bayesRisk_lower (productPrior d P.ν₀) (productPrior d P.ν₁)
    (denseProductPoissonKernel d r a) (densePriorTarget d a)
    (denseProductPoissonKernel_probability d r a) est hest (measurable_densePriorTarget d a)
    (1 / 2 + a * (∫ t, |t| ∂P.ν₀) / 2) (1 / 2 + a * (∫ t, |t| ∂P.ν₁) / 2)
    Delta (Delta / 4) (1 / 8) (1 / 8) (1 / 8)
    (by dsimp [Delta] at *; linarith)
    (by dsimp [Delta]; linarith)
    (ht P.ν₀ P.supported₀ P.symmetric₀) (ht P.ν₁ P.supported₁ P.symmetric₁) htv
  convert hb using 1
  congr 1
  ring

-- @node: dense_symmetric_bayesRisk_lower
/-- The Fejér symmetric priors attain the dense risk order a²/K². The separation is proved by the approximation certificate, never assumed. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma dense_symmetric_bayesRisk_lower :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (K d : ℕ) (r a : ℝ),
        0 < K → 2 ≤ d → 0 < r → 0 < a → a ≤ 1 / 2 →
        C * logAlphabet d ≤ K → r * a ^ 2 ≤ η * K →
        1280000 * (K : ℝ) ^ 2 ≤ d →
        ∃ P : AbsMomentMatchedPriors K,
          ∀ est : (Fin d → (Fin 2 → ℕ)) → ℝ, Measurable est →
            ENNReal.ofReal ((5 / 2560000 : ℝ) * a ^ 2 / (K : ℝ) ^ 2) ≤
              max (bayesSquaredRisk (productPrior d P.ν₀)
                    (denseProductPoissonKernel d r a) (densePriorTarget d a) est)
                  (bayesSquaredRisk (productPrior d P.ν₁)
                    (denseProductPoissonKernel d r a) (densePriorTarget d a) est) := by
  obtain ⟨η, C, hη, hC, hrisk⟩ := dense_product_prior_bayesRisk_lower
  refine ⟨η, C, hη, hC, ?_⟩
  intro K d r a hK hd hr ha hahi hlog hband hsize
  obtain ⟨P, hgap⟩ := dense_symmetric_priors_absGap_lower K hK
  refine ⟨P, ?_⟩
  intro est hest
  let Delta := a * ((∫ t, |t| ∂P.ν₁) - (∫ t, |t| ∂P.ν₀)) / 2
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hlo : a / (100 * K) ≤ Delta := by
    have hh := mul_le_mul_of_nonneg_left hgap ha.le
    dsimp [Delta]
    calc
      _ = a * ((1 / 50 : ℝ) / K) / 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hh (by norm_num)
  have hD : 0 < Delta := (by positivity : 0 < a / (100 * K)).trans_le hlo
  have hsq : a ^ 2 / (10000 * (K : ℝ) ^ 2) ≤ Delta ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ a / (100 * K)) hlo 2
    convert h using 1 <;> first | ring | rfl
  have hsize' : 128 * a ^ 2 ≤ d * Delta ^ 2 := by
    have hb : 128 * a ^ 2 ≤ (d : ℝ) * (a ^ 2 / (10000 * (K : ℝ) ^ 2)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : 0 < 10000 * (K : ℝ) ^ 2)).2
      nlinarith only [mul_le_mul_of_nonneg_right hsize (sq_nonneg a)]
    exact hb.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg d))
  have hb := hrisk K d P r a hd hr ha hahi hlog hband hsize' hD est hest
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hb
  calc
    _ = (5 / 256 : ℝ) * (a ^ 2 / (10000 * (K : ℝ) ^ 2)) := by ring
    _ ≤ (5 / 256 : ℝ) * Delta ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = _ := by ring

-- @node: dense_logDegree_bayesRisk_lower
/-- Above a universal alphabet cutoff the logarithmic dense experiment has risk at least a universal multiple of a²/K_d², with concentration derived. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma dense_logDegree_bayesRisk_lower :
    ∃ (η C : ℝ) (D : ℕ), 0 < η ∧ 2 ≤ C ∧ 2 ≤ D ∧
      ∀ (d : ℕ) (r a : ℝ), D ≤ d → 0 < r → 0 < a → a ≤ 1 / 2 →
        r * a ^ 2 ≤ η * lowerLogDegree C d →
        ∃ P : AbsMomentMatchedPriors (lowerLogDegree C d),
          ∀ est : (Fin d → (Fin 2 → ℕ)) → ℝ, Measurable est →
            ENNReal.ofReal ((5 / 2560000 : ℝ) * a ^ 2 /
              (lowerLogDegree C d : ℝ) ^ 2) ≤
              max (bayesSquaredRisk (productPrior d P.ν₀)
                    (denseProductPoissonKernel d r a) (densePriorTarget d a) est)
                  (bayesSquaredRisk (productPrior d P.ν₁)
                    (denseProductPoissonKernel d r a) (densePriorTarget d a) est) := by
  obtain ⟨η, C₀, hη, hC₀, hrisk⟩ := dense_symmetric_bayesRisk_lower
  let C := max C₀ 2
  have hC : 2 ≤ C := le_max_right _ _
  obtain ⟨D, hD, hcut⟩ := sparse_packet_alphabet_cutoff
    (cp := (1 / 100 : ℝ)) (by norm_num) hC
  refine ⟨η, C, D, hη, hC, hD, ?_⟩
  intro d r a hd hr ha hahi hband
  have hd2 := hD.trans hd
  obtain ⟨hK, hlog, _⟩ := lowerLogDegree_bounds hC hd2
  have hsmall := hcut d hd 2 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hsmall
  have hsize : 1280000 * (lowerLogDegree C d : ℝ) ^ 2 ≤ d := by linarith
  have hL : 0 ≤ logAlphabet d := by
    unfold logAlphabet
    apply Real.log_nonneg
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  exact hrisk (lowerLogDegree C d) d r a (by omega) hd2 hr ha hahi
    ((mul_le_mul_of_nonneg_right (le_max_left C₀ 2) hL).trans hlog) hband hsize

end CausalSmith.Stat.OptvalueVanishingoverlapRate
