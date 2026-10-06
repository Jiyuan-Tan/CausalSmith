module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparseMoments
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparseTV
public import Causalean.Mathlib.Analysis.Duality.MomentPrior
public import Causalean.Stat.Minimax.FuzzyHypotheses

/-! # Dense boundary-propensity lower experiment

The absolute-value Fejér certificate supplies symmetric, supported,
moment-matched priors with an inverse-degree gap, as required by (43)--(44).
The two treated Poisson coordinates have the exact Gram identity (47);
the untreated coordinates are common to both hypotheses and contribute one.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality
open Causalean.Stat.Minimax.MomentMatchedMixture
open scoped BigOperators

-- @node: dense_symmetric_priors_absGap_lower
/-- The Fejér inverse approximation bound and the symmetric dual-prior construction give the inverse-degree absolute-value gap in (44). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK), the [stated conclusion](goal) holds. -/
lemma dense_symmetric_priors_absGap_lower (K : ℕ) (hK : 0 < K) :
    ∃ P : AbsMomentMatchedPriors K,
      (1 / 50 : ℝ) / K ≤ (∫ t, |t| ∂P.ν₁) - (∫ t, |t| ∂P.ν₀) := by
  obtain ⟨P⟩ := exists_symmetric_momentMatched_absGap_for_degree K
  refine ⟨P, ?_⟩
  rw [P.abs_gap]
  have h := mul_le_mul_of_nonneg_left (bestUniformApproxErrorAbs_lower K hK)
    (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1 <;> first | ring | rfl

-- @node: dense_symmetric_integral_id_zero
/-- Symmetry cancels the signed first moment, so only the absolute-value moment contributes to the centers of the target in (46). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hsym), the [stated conclusion](goal) holds. -/
lemma dense_symmetric_integral_id_zero (ν : Measure ℝ) (hsym : IsSymmetric ν) :
    (∫ t, t ∂ν) = 0 := by
  have h : (∫ t, t ∂Measure.map (fun t : ℝ => -t) ν) = -(∫ t, t ∂ν) := by
    rw [integral_map (by fun_prop) (by fun_prop), integral_neg]
  rw [hsym] at h
  linarith

-- @node: denseTreatedMean
/-- For [the displayed parameters](hyp:r,a,t,j), [denseTreatedMean](goal) is the object specified by this definition. -/
noncomputable def denseTreatedMean (r a t : ℝ) (j : Fin 2) : ℝ :=
  r * (1 / 2 + if j = 0 then -(a * t) else a * t)

-- @node: denseTreatedLaw
/-- For [the displayed parameters](hyp:r,a,t), [denseTreatedLaw](goal) is the object specified by this definition. -/
noncomputable def denseTreatedLaw (r a t : ℝ) : Measure (Fin 2 → ℕ) :=
  Measure.pi (fun j => poissonMeasure (Real.toNNReal (denseTreatedMean r a t j)))

-- @node: denseTreatedLikelihood
/-- For [the displayed parameters](hyp:r,a,t,N), [denseTreatedLikelihood](goal) is the object specified by this definition. -/
noncomputable def denseTreatedLikelihood (r a t : ℝ) (N : Fin 2 → ℕ) : ℝ :=
  ∏ j, Real.exp (denseTreatedMean r a 0 j - denseTreatedMean r a t j) *
    (denseTreatedMean r a t j / denseTreatedMean r a 0 j) ^ N j

-- @node: denseTreatedMean_nonneg
/-- Legal amplitudes and supported prior parameters yield legal Poisson means. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hr,ha,hahi,ht), the [stated conclusion](goal) holds. -/
lemma denseTreatedMean_nonneg {r a t : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hahi : a ≤ 1 / 2) (ht : |t| ≤ 1) (j : Fin 2) :
    0 ≤ denseTreatedMean r a t j := by
  have hat : |a * t| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left ht ha).trans (by simpa using hahi)
  rw [abs_le] at hat
  unfold denseTreatedMean
  split_ifs <;> apply mul_nonneg hr <;> linarith [hat.1, hat.2]

-- @node: denseTreatedLikelihood_gram
/-- Equation (47): both treated outcomes contribute, giving exactly 4 r a². The calculation is valid at support endpoints, including zero alternative means. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hr), the [stated conclusion](goal) holds. -/
lemma denseTreatedLikelihood_gram {r : ℝ} (hr : 0 < r) (a t s : ℝ) :
    (∫ N, denseTreatedLikelihood r a t N * denseTreatedLikelihood r a s N
      ∂denseTreatedLaw r a 0) = Real.exp (4 * r * a ^ 2 * t * s) := by
  have hstar (j : Fin 2) : 0 < denseTreatedMean r a 0 j := by
    simp [denseTreatedMean]
    positivity
  have hfun (N : Fin 2 → ℕ) :
      denseTreatedLikelihood r a t N * denseTreatedLikelihood r a s N =
      ∏ j, (Real.exp (denseTreatedMean r a 0 j - denseTreatedMean r a t j) *
        (denseTreatedMean r a t j / denseTreatedMean r a 0 j) ^ N j) *
        (Real.exp (denseTreatedMean r a 0 j - denseTreatedMean r a s j) *
        (denseTreatedMean r a s j / denseTreatedMean r a 0 j) ^ N j) := by
    unfold denseTreatedLikelihood
    rw [← Finset.prod_mul_distrib]
  simp_rw [hfun]
  unfold denseTreatedLaw
  rw [integral_fintype_prod_eq_prod (fun j : Fin 2 => fun k : ℕ =>
    (Real.exp (denseTreatedMean r a 0 j - denseTreatedMean r a t j) *
      (denseTreatedMean r a t j / denseTreatedMean r a 0 j) ^ k) *
    (Real.exp (denseTreatedMean r a 0 j - denseTreatedMean r a s j) *
      (denseTreatedMean r a s j / denseTreatedMean r a 0 j) ^ k))]
  simp_rw [poisson_likelihood_gram_scalar _ _ _ (hstar _)]
  rw [← Real.exp_sum]
  congr 1
  simp [Fin.sum_univ_two, denseTreatedMean]
  field_simp
  ring

-- @node: measurable_denseTreatedLikelihood
/-- The dense likelihood is jointly measurable in parameter and counts. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
@[fun_prop]
lemma measurable_denseTreatedLikelihood (r a : ℝ) :
    Measurable (fun p : ℝ × (Fin 2 → ℕ) => denseTreatedLikelihood r a p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro N
  unfold denseTreatedLikelihood denseTreatedMean
  apply Finset.measurable_prod
  intro j _
  split_ifs <;> fun_prop

-- @node: denseTreatedLikelihood_nonneg
/-- A supported parameter yields a nonnegative genuine likelihood. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hr,ha,hahi,ht), the [stated conclusion](goal) holds. -/
lemma denseTreatedLikelihood_nonneg {r a t : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hahi : a ≤ 1 / 2) (ht : |t| ≤ 1) (N : Fin 2 → ℕ) :
    0 ≤ denseTreatedLikelihood r a t N := by
  apply Finset.prod_nonneg
  intro j _
  exact mul_nonneg (Real.exp_nonneg _) (pow_nonneg
    (div_nonneg (denseTreatedMean_nonneg hr ha hahi ht j)
      (denseTreatedMean_nonneg hr ha hahi (by norm_num) j)) _)

-- @node: denseTreatedLaw_eq_withDensity
/-- The two-coordinate likelihood recovers the actual Poisson law, even when a supported endpoint makes one alternative intensity zero. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hr,ha,hahi,ht), the [stated conclusion](goal) holds. -/
lemma denseTreatedLaw_eq_withDensity {r a t : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (hahi : a ≤ 1 / 2) (ht : |t| ≤ 1) :
    denseTreatedLaw r a t = (denseTreatedLaw r a 0).withDensity
      (fun N => ENNReal.ofReal (denseTreatedLikelihood r a t N)) := by
  have hstar (j : Fin 2) : 0 < denseTreatedMean r a 0 j := by
    simp [denseTreatedMean]
    positivity
  have hmean (j : Fin 2) := denseTreatedMean_nonneg hr.le ha hahi ht j
  apply Measure.ext_of_singleton
  intro N
  rw [withDensity_apply _ (measurableSet_singleton N), lintegral_singleton]
  simp only [denseTreatedLaw, Measure.pi_singleton]
  have hatom (j : Fin 2) := sparse_poisson_likelihood_atom (hmean j) (hstar j) (N j)
  simp_rw [hatom]
  rw [Finset.prod_mul_distrib]
  congr 1
  unfold denseTreatedLikelihood
  exact (ENNReal.ofReal_prod_of_nonneg (fun j _ =>
    mul_nonneg (Real.exp_nonneg _) (pow_nonneg
      (div_nonneg (hmean j) (hstar j).le) _))).symm

-- @node: measurable_denseTreatedLaw
/-- The dense treated counts form a measurable probability experiment. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
@[fun_prop]
lemma measurable_denseTreatedLaw (r a : ℝ) : Measurable (denseTreatedLaw r a) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hatom (N : Fin 2 → ℕ) : Measurable (fun t => denseTreatedLaw r a t {N}) := by
    simp only [denseTreatedLaw, Measure.pi_singleton, poissonMeasure_singleton]
    apply Finset.measurable_prod
    intro j _
    have hm : Measurable (fun t => denseTreatedMean r a t j) := by
      unfold denseTreatedMean
      split_ifs <;> fun_prop
    fun_prop
  simp_rw [← Measure.tsum_indicator_apply_singleton _ s hs]
  apply Measurable.tsum
  intro N
  by_cases hN : N ∈ s
  · simpa [Set.indicator_of_mem hN] using hatom N
  · simp [Set.indicator_of_notMem hN]

-- @node: denseTreatedKernel
/-- For [the displayed parameters](hyp:r,a), [denseTreatedKernel](goal) is the object specified by this definition. -/
noncomputable def denseTreatedKernel (r a : ℝ) : Kernel ℝ (Fin 2 → ℕ) where
  toFun t := denseTreatedLaw r a t
  measurable' := measurable_denseTreatedLaw r a

-- @node: dense_prior_support_radius_one
/-- The symmetric priors are concentrated on the radius-one support used in the exponential-Gram mixture theorem. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hsupp), the [stated conclusion](goal) holds. -/
lemma dense_prior_support_radius_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : IsSupportedOnUnitInterval ν) : ν {t | |t| ≤ 1} = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_le (by fun_prop) measurable_const)).1
  filter_upwards [(ae_iff).2 hsupp] with t ht
  simpa only [symmUnitInterval, Set.mem_Icc, abs_le, neg_le_neg_iff] using ht

-- @node: dense_product_mixture_tv_le_sqrt_tail
/-- Moment annihilation through K removes all lower terms in (47). The product-mixture testing distance is at most d times the square root of the remaining exponential tail, exactly as in the dense splice. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hr,ha,hahi), the [stated conclusion](goal) holds. -/
lemma dense_product_mixture_tv_le_sqrt_tail {K d : ℕ} (P : AbsMomentMatchedPriors K)
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2) :
    Causalean.Stat.tvDist
      (productPriorPredictive d P.ν₀ (denseTreatedKernel r a))
      (productPriorPredictive d P.ν₁ (denseTreatedKernel r a)) ≤
      d * Real.sqrt (exponentialSeriesTail K (4 * r * a ^ 2)) := by
  let : IsProbabilityMeasure P.ν₀ := P.probability₀
  let : IsProbabilityMeasure P.ν₁ := P.probability₁
  let : IsProbabilityMeasure (denseTreatedLaw r a 0) := by
    unfold denseTreatedLaw
    infer_instance
  have h := momentMatchedProductMixture_tv_le_of_supported
    d P.ν₀ P.ν₁ (denseTreatedKernel r a) (denseTreatedLaw r a 0)
    (denseTreatedLikelihood r a)
    (fun t => by change IsProbabilityMeasure (denseTreatedLaw r a t)
                 unfold denseTreatedLaw; infer_instance)
    (4 * r * a ^ 2) 1 K (by positivity) (by norm_num)
    (measurable_denseTreatedLikelihood r a)
    (fun t ht N => denseTreatedLikelihood_nonneg hr.le ha hahi ht N)
    (fun t ht => denseTreatedLaw_eq_withDensity hr ha hahi ht)
    (fun t _ s _ => denseTreatedLikelihood_gram hr a t s)
    (dense_prior_support_radius_one P.ν₀ P.supported₀)
    (dense_prior_support_radius_one P.ν₁ P.supported₁) P.moments_eq
  simpa using h

-- @node: dense_product_mixture_tv_le_one_eighth
/-- Universal choices of the amplitude coefficient and logarithmic degree make the dense product mixture TV at most 1/8. The calibration condition r a² ≤ η K is provided by the amplitude choice (45). In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma dense_product_mixture_tv_le_one_eighth :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (K d : ℕ) (P : AbsMomentMatchedPriors K) (r a : ℝ),
        2 ≤ d → 0 < r → 0 ≤ a → a ≤ 1 / 2 →
        C * logAlphabet d ≤ K → r * a ^ 2 ≤ η * K →
        Causalean.Stat.tvDist
          (productPriorPredictive d P.ν₀ (denseTreatedKernel r a))
          (productPriorPredictive d P.ν₁ (denseTreatedKernel r a)) ≤ 1 / 8 := by
  obtain ⟨b, D, ρ, hb, hD, hρ, htail⟩ :=
    FiniteSignedMomentMarkedPoissonMixture.exists_geometric_sqrt_exponentialSeriesTail_bound
      1 (by norm_num)
  obtain ⟨C, hC, hcal⟩ := sparse_geometric_degree_calibration hD hρ
  refine ⟨b / 4, C, by positivity, hC, ?_⟩
  intro K d P r a hd hr ha hahi hK hband
  have hsmall : 4 * r * a ^ 2 ≤ b * K := by nlinarith
  have hdecay : Real.sqrt (exponentialSeriesTail K (4 * r * a ^ 2)) ≤ D * ρ ^ K := by
    simpa only [one_mul] using htail K (4 * r * a ^ 2) (by positivity) hsmall
  calc
    _ ≤ d * Real.sqrt (exponentialSeriesTail K (4 * r * a ^ 2)) :=
      dense_product_mixture_tv_le_sqrt_tail P hr ha hahi
    _ ≤ d * (D * ρ ^ K) := mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg d)
    _ ≤ 1 / 8 := hcal d K hd hK

end CausalSmith.Stat.OptvalueVanishingoverlapRate
