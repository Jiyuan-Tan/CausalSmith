module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerDenseObserved
public import Mathlib.Probability.Kernel.Composition.Prod

/-! # Dense lower bounds with all observed Poisson counts

The untreated counts have a common law. Mixing the full experiment factors
this law out of each predictive mixture, so the treated-count TV bound and
the target concentration prove the same lower bound for full-count estimators.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.Minimax.FuzzyHypotheses
open scoped BigOperators ENNReal

/-- The two untreated outcomes in every cell are independent Poisson counts
with the common intensity q = B n (1 - ε)/(2 d). -/
-- @node: denseUntreatedPoissonLaw
noncomputable def denseUntreatedPoissonLaw (d : ℕ) (q : ℝ) :
    Measure (Fin d → (Fin 2 → ℕ)) :=
  Measure.pi fun _ => Measure.pi fun _ : Fin 2 => poissonMeasure (Real.toNNReal q)

/-- Full counts, arranged as treated counts followed by untreated counts. -/
-- @node: denseFullPoissonKernel
noncomputable def denseFullPoissonKernel (d : ℕ) (r a q : ℝ) :
    Kernel (Fin d → ℝ) ((Fin d → (Fin 2 → ℕ)) × (Fin d → (Fin 2 → ℕ))) := by
  letI : IsMarkovKernel (denseProductPoissonKernel d r a) :=
    ⟨denseProductPoissonKernel_probability d r a⟩
  exact (denseProductPoissonKernel d r a).prod
    (Kernel.const _ (denseUntreatedPoissonLaw d q))

/-- The full-count fibre is the product of the treated experiment and its parameter-independent untreated law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: denseFullPoissonKernel_apply
lemma denseFullPoissonKernel_apply (d : ℕ) (r a q : ℝ) (θ : Fin d → ℝ) :
    denseFullPoissonKernel d r a q θ =
      (denseProductPoissonKernel d r a θ).prod (denseUntreatedPoissonLaw d q) := by
  letI : IsMarkovKernel (denseProductPoissonKernel d r a) :=
    ⟨denseProductPoissonKernel_probability d r a⟩
  letI : IsProbabilityMeasure (denseUntreatedPoissonLaw d q) := by
    unfold denseUntreatedPoissonLaw; infer_instance
  exact Kernel.prod_apply _ _ _

/-- The full count experiment has probability fibres. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: denseFullPoissonKernel_probability
lemma denseFullPoissonKernel_probability (d : ℕ) (r a q : ℝ) (θ : Fin d → ℝ) :
    IsProbabilityMeasure (denseFullPoissonKernel d r a q θ) := by
  rw [denseFullPoissonKernel_apply]
  letI := denseProductPoissonKernel_probability d r a θ
  unfold denseUntreatedPoissonLaw
  infer_instance

/-- The untreated law factors out of the prior-predictive mixture. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: dense_full_prior_predictive_eq
lemma dense_full_prior_predictive_eq (d : ℕ) (r a q : ℝ)
    (π : Measure (Fin d → ℝ)) :
    priorPredictive π (denseFullPoissonKernel d r a q) =
      (priorPredictive π (denseProductPoissonKernel d r a)).prod
        (denseUntreatedPoissonLaw d q) := by
  letI : IsProbabilityMeasure (denseUntreatedPoissonLaw d q) := by
    unfold denseUntreatedPoissonLaw; infer_instance
  apply Measure.ext_of_singleton
  rintro ⟨T, U⟩
  rw [← Set.singleton_prod_singleton, priorPredictive_apply _ _ ((measurableSet_singleton T).prod (measurableSet_singleton U)),
    Measure.prod_prod, priorPredictive_apply _ _ (measurableSet_singleton _)]
  simp_rw [denseFullPoissonKernel_apply, Measure.prod_prod]
  exact lintegral_mul_const _ ((denseProductPoissonKernel d r a).measurable_coe
    (measurableSet_singleton _))

/-- Adding all untreated counts cannot increase the predictive TV bound. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: dense_full_prior_predictive_tv_le
lemma dense_full_prior_predictive_tv_le (d : ℕ) (r a q : ℝ)
    (π₀ π₁ : Measure (Fin d → ℝ)) [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁] :
    Causalean.Stat.tvDist (priorPredictive π₀ (denseFullPoissonKernel d r a q))
      (priorPredictive π₁ (denseFullPoissonKernel d r a q)) ≤
    Causalean.Stat.tvDist (priorPredictive π₀ (denseProductPoissonKernel d r a))
      (priorPredictive π₁ (denseProductPoissonKernel d r a)) := by
  letI : IsProbabilityMeasure (denseUntreatedPoissonLaw d q) := by
    unfold denseUntreatedPoissonLaw; infer_instance
  letI := priorPredictive_isProbability π₀ (denseProductPoissonKernel d r a)
    (denseProductPoissonKernel_probability d r a)
  letI := priorPredictive_isProbability π₁ (denseProductPoissonKernel d r a)
    (denseProductPoissonKernel_probability d r a)
  rw [dense_full_prior_predictive_eq, dense_full_prior_predictive_eq]
  simpa [Causalean.Stat.tvDist] using tvDist_prod_le_add
    (priorPredictive π₀ (denseProductPoissonKernel d r a))
    (priorPredictive π₁ (denseProductPoissonKernel d r a))
    (denseUntreatedPoissonLaw d q) (denseUntreatedPoissonLaw d q)

/-- Reorder all four observed counts into treated and untreated blocks,
with outcome false at index zero and outcome true at index one. -/
-- @node: denseCountEquiv
noncomputable def denseCountEquiv (d : ℕ) :
    (Obs d → ℕ) ≃ᵐ ((Fin d → (Fin 2 → ℕ)) × (Fin d → (Fin 2 → ℕ))) where
  toFun N := (fun x j => N (x, true, j = 1), fun x j => N (x, false, j = 1))
  invFun N := fun o => if o.2.1 then N.1 o.1 (if o.2.2 then 1 else 0)
    else N.2 o.1 (if o.2.2 then 1 else 0)
  left_inv N := by
    funext o
    rcases o with ⟨x, b, y⟩
    cases b <;> cases y <;> rfl
  right_inv N := by
    apply Prod.ext <;> funext x j <;> fin_cases j <;> rfl
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

/-- The full dense kernel is exactly the independent Poisson counts of the legal observed law, after a reversible reordering of all four coordinates. No coordinate of the observed experiment is discarded. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi,hθ), the [stated conclusion](goal) holds. -/
-- @node: denseFullPoissonKernel_eq_observedCounts
lemma denseFullPoissonKernel_eq_observedCounts {d : ℕ} (hd : 0 < d)
    (ε a B : ℝ) (n : ℕ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 2)
    (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (θ : Fin d → ℝ) (hθ : ∀ x, |θ x| ≤ 1) :
    Measure.map (denseCountEquiv d)
      (Measure.pi fun o : Obs d => poissonMeasure (Real.toNNReal
        (B * n * jointMass (denseObservedLaw hd ε a hε hεhi ha hahi θ hθ)
          o.1 o.2.1 o.2.2))) =
      denseFullPoissonKernel d (B * n * ε / d) a (B * n * (1 - ε) / (2 * d)) θ := by
  apply Measure.ext_of_singleton
  rintro ⟨T, U⟩
  rw [Measure.map_apply (denseCountEquiv d).measurable (measurableSet_singleton _),
    denseFullPoissonKernel_apply]
  have hpre : (denseCountEquiv d) ⁻¹' {(T, U)} =
      {(denseCountEquiv d).symm (T, U)} := by
    ext N
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (denseCountEquiv d).apply_eq_iff_eq_symm_apply
  rw [hpre, Measure.pi_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod]
  change (∏ o : Obs d, _) =
    (Measure.pi (fun x => denseTreatedLaw (B * n * ε / d) a (θ x))) {T} *
      (denseUntreatedPoissonLaw d (B * n * (1 - ε) / (2 * d))) {U}
  simp only [denseUntreatedPoissonLaw, denseTreatedLaw, Measure.pi_singleton]
  simp only [Obs, Fintype.prod_prod_type]
  have hmean := denseObservedLaw_poissonMeans hd ε a B n hε hεhi ha hahi θ hθ
  simp only [Fintype.prod_bool]
  dsimp only [denseCountEquiv, MeasurableEquiv.symm, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  simp_rw [(hmean _ _).1, (hmean _ _).2]
  simp [Fin.prod_univ_two, denseTreatedMean]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x _
  ring

/-- The dense fuzzy-testing step (48): concentration and likelihood TV are both derived; the alphabet condition makes target deviations negligible. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: dense_full_product_prior_bayesRisk_lower
lemma dense_full_product_prior_bayesRisk_lower :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (K d : ℕ) (P : AbsMomentMatchedPriors K) (r a q : ℝ),
        2 ≤ d → 0 < r → 0 < a → a ≤ 1 / 2 →
        C * logAlphabet d ≤ K → r * a ^ 2 ≤ η * K →
        let Delta := a * ((∫ t, |t| ∂P.ν₁) - (∫ t, |t| ∂P.ν₀)) / 2
        128 * a ^ 2 ≤ d * Delta ^ 2 → 0 < Delta →
        ∀ est : ((Fin d → (Fin 2 → ℕ)) × (Fin d → (Fin 2 → ℕ))) → ℝ, Measurable est →
          ENNReal.ofReal (5 * Delta ^ 2 / 256) ≤
            max (bayesSquaredRisk (productPrior d P.ν₀)
                  (denseFullPoissonKernel d r a q) (densePriorTarget d a) est)
                (bayesSquaredRisk (productPrior d P.ν₁)
                  (denseFullPoissonKernel d r a q) (densePriorTarget d a) est) := by
  obtain ⟨η, C, hη, hC, htvbound⟩ := dense_product_mixture_tv_le_one_eighth
  refine ⟨η, C, hη, hC, ?_⟩
  intro K d P r a q hd hr ha hahi hK hband
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
      (priorPredictive (productPrior d P.ν₀) (denseFullPoissonKernel d r a q))
      (priorPredictive (productPrior d P.ν₁) (denseFullPoissonKernel d r a q)) ≤ 1 / 8 := by
    apply (dense_full_prior_predictive_tv_le d r a q _ _).trans
    rw [dense_product_prior_predictive_eq, dense_product_prior_predictive_eq]
    exact htvbound K d P r a hd hr ha.le hahi hK hband
  have hb := twoFuzzyHypotheses_bayesRisk_lower (productPrior d P.ν₀) (productPrior d P.ν₁)
    (denseFullPoissonKernel d r a q) (densePriorTarget d a)
    (denseFullPoissonKernel_probability d r a q) est hest (measurable_densePriorTarget d a)
    (1 / 2 + a * (∫ t, |t| ∂P.ν₀) / 2) (1 / 2 + a * (∫ t, |t| ∂P.ν₁) / 2)
    Delta (Delta / 4) (1 / 8) (1 / 8) (1 / 8)
    hDelta.le (by positivity) (by dsimp [Delta] at *; linarith)
    (by dsimp [Delta]; linarith) (by norm_num) (by norm_num) (by norm_num)
    (ht P.ν₀ P.supported₀ P.symmetric₀) (ht P.ν₁ P.supported₁ P.symmetric₁) htv
  convert hb using 1
  congr 1
  ring

/-- The Fejér symmetric priors attain the dense risk order a²/K². The separation is proved by the approximation certificate, never assumed. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: dense_full_symmetric_bayesRisk_lower
lemma dense_full_symmetric_bayesRisk_lower :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (K d : ℕ) (r a q : ℝ),
        0 < K → 2 ≤ d → 0 < r → 0 < a → a ≤ 1 / 2 →
        C * logAlphabet d ≤ K → r * a ^ 2 ≤ η * K →
        1280000 * (K : ℝ) ^ 2 ≤ d →
        ∃ P : AbsMomentMatchedPriors K,
          ∀ est : ((Fin d → (Fin 2 → ℕ)) × (Fin d → (Fin 2 → ℕ))) → ℝ, Measurable est →
            ENNReal.ofReal ((5 / 2560000 : ℝ) * a ^ 2 / (K : ℝ) ^ 2) ≤
              max (bayesSquaredRisk (productPrior d P.ν₀)
                    (denseFullPoissonKernel d r a q) (densePriorTarget d a) est)
                  (bayesSquaredRisk (productPrior d P.ν₁)
                    (denseFullPoissonKernel d r a q) (densePriorTarget d a) est) := by
  obtain ⟨η, C, hη, hC, hrisk⟩ := dense_full_product_prior_bayesRisk_lower
  refine ⟨η, C, hη, hC, ?_⟩
  intro K d r a q hK hd hr ha hahi hlog hband hsize
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
  have hb := hrisk K d P r a q hd hr ha hahi hlog hband hsize' hD est hest
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hb
  calc
    _ = (5 / 256 : ℝ) * (a ^ 2 / (10000 * (K : ℝ) ^ 2)) := by ring
    _ ≤ (5 / 256 : ℝ) * Delta ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = _ := by ring

/-- Above a universal alphabet cutoff the logarithmic dense experiment has risk at least a universal multiple of a²/K_d², with concentration derived. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: dense_full_logDegree_bayesRisk_lower
lemma dense_full_logDegree_bayesRisk_lower :
    ∃ (η C : ℝ) (D : ℕ), 0 < η ∧ 2 ≤ C ∧ 2 ≤ D ∧
      ∀ (d : ℕ) (r a q : ℝ), D ≤ d → 0 < r → 0 < a → a ≤ 1 / 2 →
        r * a ^ 2 ≤ η * lowerLogDegree C d →
        ∃ P : AbsMomentMatchedPriors (lowerLogDegree C d),
          ∀ est : ((Fin d → (Fin 2 → ℕ)) × (Fin d → (Fin 2 → ℕ))) → ℝ, Measurable est →
            ENNReal.ofReal ((5 / 2560000 : ℝ) * a ^ 2 /
              (lowerLogDegree C d : ℝ) ^ 2) ≤
              max (bayesSquaredRisk (productPrior d P.ν₀)
                    (denseFullPoissonKernel d r a q) (densePriorTarget d a) est)
                  (bayesSquaredRisk (productPrior d P.ν₁)
                    (denseFullPoissonKernel d r a q) (densePriorTarget d a) est) := by
  obtain ⟨η, C₀, hη, hC₀, hrisk⟩ := dense_full_symmetric_bayesRisk_lower
  let C := max C₀ 2
  have hC : 2 ≤ C := le_max_right _ _
  obtain ⟨D, hD, hcut⟩ := sparse_packet_alphabet_cutoff
    (cp := (1 / 100 : ℝ)) (by norm_num) hC
  refine ⟨η, C, D, hη, hC, hD, ?_⟩
  intro d r a q hd hr ha hahi hband
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
  exact hrisk (lowerLogDegree C d) d r a q (by omega) hd2 hr ha hahi
    ((mul_le_mul_of_nonneg_right (le_max_left C₀ 2) hL).trans hlog) hband hsize

/-- Return the full Poisson experiment to the usual observed histogram
alphabet, using the inverse of the count reordering. -/
-- @node: denseFullObservedPoissonKernel
noncomputable def denseFullObservedPoissonKernel (d : ℕ) (r a q : ℝ) :
    Kernel (Fin d → ℝ) (Obs d → ℕ) :=
  (denseFullPoissonKernel d r a q).map (denseCountEquiv d).symm

/-- On the prior support the full histogram kernel is precisely the independent four-cell observed Poisson experiment. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi,hθ), the [stated conclusion](goal) holds. -/
-- @node: denseFullObservedPoissonKernel_eq
lemma denseFullObservedPoissonKernel_eq {d : ℕ} (hd : 0 < d)
    (ε a B : ℝ) (n : ℕ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 2)
    (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (θ : Fin d → ℝ) (hθ : ∀ x, |θ x| ≤ 1) :
    denseFullObservedPoissonKernel d (B * n * ε / d) a
        (B * n * (1 - ε) / (2 * d)) θ =
      Measure.pi fun o : Obs d => poissonMeasure (Real.toNNReal
        (B * n * jointMass (denseObservedLaw hd ε a hε hεhi ha hahi θ hθ)
          o.1 o.2.1 o.2.2)) := by
  rw [denseFullObservedPoissonKernel,
    Kernel.map_apply _ (denseCountEquiv d).symm.measurable]
  rw [← denseFullPoissonKernel_eq_observedCounts hd ε a B n hε hεhi ha hahi θ hθ]
  rw [Measure.map_map (denseCountEquiv d).symm.measurable (denseCountEquiv d).measurable]
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply, Measure.map_id']

/-- Reordering all observed counts preserves the squared Bayes risk exactly. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hest), the [stated conclusion](goal) holds. -/
-- @node: dense_full_observed_bayesRisk_eq
lemma dense_full_observed_bayesRisk_eq (d : ℕ) (r a q : ℝ)
    (π : Measure (Fin d → ℝ)) (target : (Fin d → ℝ) → ℝ)
    (est : (Obs d → ℕ) → ℝ) (hest : Measurable est) :
    bayesSquaredRisk π (denseFullObservedPoissonKernel d r a q) target est =
      bayesSquaredRisk π (denseFullPoissonKernel d r a q) target
        (fun N => est ((denseCountEquiv d).symm N)) := by
  unfold bayesSquaredRisk squaredRisk
  apply lintegral_congr
  intro θ
  rw [denseFullObservedPoissonKernel,
    Kernel.map_apply _ (denseCountEquiv d).symm.measurable]
  exact lintegral_map (by fun_prop) (denseCountEquiv d).symm.measurable

/-- The dense lower bound holds for arbitrary estimators using every observed histogram count, with the legal observed value as its target. The priors, gap, concentration and full-likelihood TV bound are proved. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: dense_full_observed_logDegree_bayesRisk_lower
lemma dense_full_observed_logDegree_bayesRisk_lower :
    ∃ (η C : ℝ) (D : ℕ), 0 < η ∧ 2 ≤ C ∧ 2 ≤ D ∧
      ∀ (d : ℕ) (r a q ε : ℝ) (hd : 0 < d)
        (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2),
        D ≤ d → 0 < r → 0 < a →
        r * a ^ 2 ≤ η * lowerLogDegree C d →
        ∃ P : AbsMomentMatchedPriors (lowerLogDegree C d),
          ∀ est : (Obs d → ℕ) → ℝ, Measurable est →
            ENNReal.ofReal ((5 / 2560000 : ℝ) * a ^ 2 /
              (lowerLogDegree C d : ℝ) ^ 2) ≤
              max (bayesSquaredRisk (productPrior d P.ν₀)
                    (denseFullObservedPoissonKernel d r a q)
                    (fun θ => observedValue (denseObservedModel hd ε a hε hεhi ha hahi θ).1) est)
                  (bayesSquaredRisk (productPrior d P.ν₁)
                    (denseFullObservedPoissonKernel d r a q)
                    (fun θ => observedValue (denseObservedModel hd ε a hε hεhi ha hahi θ).1) est) := by
  obtain ⟨η, C, D, hη, hC, hD, hbound⟩ := dense_full_logDegree_bayesRisk_lower
  refine ⟨η, C, D, hη, hC, hD, ?_⟩
  intro d r a q ε hd hε hεhi ha hahi hcut hr hapos hband
  obtain ⟨P, hP⟩ := hbound d r a q hcut hr hapos hahi hband
  refine ⟨P, ?_⟩
  intro est hest
  simp_rw [denseObservedModel_value]
  rw [dense_full_observed_bayesRisk_eq d r a q _ _ est hest,
    dense_full_observed_bayesRisk_eq d r a q _ _ est hest]
  exact hP _ (hest.comp (denseCountEquiv d).symm.measurable)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
