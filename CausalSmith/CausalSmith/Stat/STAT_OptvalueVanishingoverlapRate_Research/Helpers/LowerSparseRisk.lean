module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparseMoments
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparseTV
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketResponseLower
public import Causalean.Stat.Minimax.FuzzyHypotheses

/-! # Sparse prior testing risk

The supported, mean-one product priors concentrate the normalized target
around their scalar functional centers. Chebyshev and the full sparse
product-mixture TV bound then give the auxiliary squared-risk lower bound
in roadmap (40), before the fixed-sample transfer.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.Minimax.FuzzyHypotheses
open scoped BigOperators

/-- Extend a centered sparse intensity to the legal support by clipping. On either supported centered prior this equals the original intensity. For the displayed parameters, sparseClippedIntensity is the object specified by this definition. -/
 noncomputable def sparseClippedIntensity (M θ : ℝ) (hMpaper : 2 ≤ M) : ℝ := min M (max 0 (θ + sparseReference (_hMpaper := hMpaper) M)) 
/-- The normalized sparse value, extended measurably to all centered vectors. The extension agrees with the actual sparse observed value on legal vectors. For the displayed parameters, sparsePriorTarget is the object specified by this definition. -/
 noncomputable def sparsePriorTarget (d : ℕ) (ε M : ℝ) (θ : Fin d → ℝ) (hMpaper : 2 ≤ M) : ℝ := 1 / 2 + ((∑ x, phiEpsFormula ε (sparseClippedIntensity (hMpaper := hMpaper) M (θ x))) / d) / (2 * (1 - ε + ε * ((∑ x, sparseClippedIntensity (hMpaper := hMpaper) M (θ x)) / d))) 
/-- Clipping puts every extended intensity in the legal interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM,hMpaper), the [stated conclusion](goal) holds. -/
lemma sparseClippedIntensity_mem {M : ℝ} (hM : 0 ≤ M) (θ : ℝ) (hMpaper : 2 ≤ M) :
    sparseClippedIntensity (hMpaper := hMpaper) M θ ∈ Set.Icc 0 M := by
  exact ⟨le_min hM (le_max_left _ _), min_le_left _ _⟩

/-- On the supported prior, translation followed by clipping is the identity. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hz,hMpaper), the [stated conclusion](goal) holds. -/
lemma sparseClippedIntensity_sub_reference {M z : ℝ} (hz : z ∈ Set.Icc 0 M) (hMpaper : 2 ≤ M) :
    sparseClippedIntensity (hMpaper := hMpaper) M (z - sparseReference (_hMpaper := hMpaper) M) = z := by
  simp [sparseClippedIntensity, max_eq_right hz.1, min_eq_right hz.2]

/-- The full independent sparse Poisson experiment as a parameter kernel.
For the displayed parameters, sparseProductPoissonKernel is the object specified by this definition. -/
noncomputable def sparseProductPoissonKernel (B : ℝ) (n d : ℕ) (ε M : ℝ)
    (hMpaper : 2 ≤ M) : Kernel (Fin d → ℝ) (Fin d → (Fin 4 → ℕ)) where
  toFun θ := Measure.pi fun x =>
    sparseCenteredPoissonKernel (hMpaper := hMpaper) B n d ε M (θ x)
  measurable' := by
    let (θ : ℝ) : IsProbabilityMeasure
        (sparseCenteredPoissonKernel (hMpaper := hMpaper) B n d ε M θ) := by
      change IsProbabilityMeasure
        (poissonCellLaw B n d ε (θ + sparseReference (_hMpaper := hMpaper) M))
      unfold poissonCellLaw
      infer_instance
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hatom (N : Fin d → (Fin 4 → ℕ)) :
        Measurable (fun θ : Fin d → ℝ =>
          (Measure.pi fun x =>
            sparseCenteredPoissonKernel (hMpaper := hMpaper) B n d ε M (θ x)) {N}) := by
      simp only [Measure.pi_singleton]
      apply Finset.measurable_prod
      intro x _
      exact ((sparseCenteredPoissonKernel (hMpaper := hMpaper) B n d ε M).measurable_coe
        (measurableSet_singleton _)).comp (measurable_pi_apply x)
    simp_rw [← Measure.tsum_indicator_apply_singleton _ s hs]
    apply Measurable.tsum
    intro N
    by_cases hN : N ∈ s
    · simpa [Set.indicator_of_mem hN] using hatom N
    · simp [Set.indicator_of_notMem hN]
/-- Clipping is measurable, including the endpoints of the intensity support. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hMpaper), the [stated conclusion](goal) holds. -/
@[fun_prop]
lemma measurable_sparseClippedIntensity (M : ℝ) (hMpaper : 2 ≤ M) :
    Measurable (sparseClippedIntensity (hMpaper := hMpaper) M) := by
  unfold sparseClippedIntensity
  fun_prop

/-- The extended target is a measurable function of the centered vector. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hMpaper), the [stated conclusion](goal) holds. -/
@[fun_prop]
lemma measurable_sparsePriorTarget (d : ℕ) (ε M : ℝ) (hMpaper : 2 ≤ M) :
    Measurable (sparsePriorTarget (hMpaper := hMpaper) d ε M) := by
  unfold sparsePriorTarget phiEpsFormula
  fun_prop

/-- Translation and clipping preserve every measurable prior integral on the support. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hsupp,hf,hMpaper), the [stated conclusion](goal) holds. -/
lemma sparse_centered_clipped_integral (ν : Measure ℝ) {M : ℝ}
    (hsupp : ν (Set.Icc 0 M)ᶜ = 0) (f : ℝ → ℝ) (hf : Measurable f) (hMpaper : 2 ≤ M) :
    (∫ θ, f (sparseClippedIntensity (hMpaper := hMpaper) M θ)
      ∂Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) ν) = ∫ z, f z ∂ν := by
  rw [integral_map (by fun_prop)
    (show AEStronglyMeasurable (fun θ => f (sparseClippedIntensity (hMpaper := hMpaper) M θ)) _ from
      (by fun_prop : Measurable (fun θ => f (sparseClippedIntensity (hMpaper := hMpaper) M θ))).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [show ∀ᵐ z ∂ν, z ∈ Set.Icc 0 M from (ae_iff).2 hsupp] with z hz
  rw [sparseClippedIntensity_sub_reference (hMpaper := hMpaper) hz]

/-- The extended sparse target stays in the unit interval at every vector. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhalf,hM,hMpaper), the [stated conclusion](goal) holds. -/
lemma sparsePriorTarget_mem_unit {d : ℕ} (hd : 0 < d) {ε M : ℝ}
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) (hM : 0 ≤ M) (θ : Fin d → ℝ) (hMpaper : 2 ≤ M) :
    sparsePriorTarget (hMpaper := hMpaper) d ε M θ ∈ Set.Icc 0 1 := by
  let z := fun x => sparseClippedIntensity (hMpaper := hMpaper) M (θ x)
  have hz (x : Fin d) := sparseClippedIntensity_mem (hMpaper := hMpaper) hM (θ x)
  have hs := sparseNormalizer_ge_half hε hεhalf z hz
  obtain ⟨hlo, hhi⟩ := sparse_average_phi_bounds hd hε hεhalf z hz
  let H := (∑ x, phiEpsFormula ε (z x)) / d
  let S := 1 - ε + ε * ((∑ x, z x) / d)
  have he : sparseNormalizerFormula d ε M z hz = S := by
    dsimp [sparseNormalizerFormula, S]
    ring
  rw [he] at hs hhi
  have hS : 0 < S := by linarith
  have hq : 0 ≤ H / (2 * S) := div_nonneg hlo (by positivity)
  have hqhi : H / (2 * S) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * S)).2
    dsimp [H]
    linarith
  change 0 ≤ 1 / 2 + H / (2 * S) ∧ 1 / 2 + H / (2 * S) ≤ 1
  constructor <;> linarith

/-- Product copies of a supported mean-one prior satisfy the normalized target second-moment estimate (39), with the center expressed as a scalar prior integral. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hsupp,hmean,hε,hεhalf,hM,hMpaper), the [stated conclusion](goal) holds. -/
lemma sparse_product_prior_target_integral_sq_le {d : ℕ} (hd : 0 < d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {ε M : ℝ}
    (hsupp : ν (Set.Icc 0 M)ᶜ = 0) (hmean : (∫ z, z ∂ν) = 1)
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) (hM : 0 ≤ M) (hMpaper : 2 ≤ M) :
    (∫ θ, (sparsePriorTarget (hMpaper := hMpaper) d ε M θ -
      (1 / 2 + (∫ z, phiEpsFormula ε z ∂ν) / 2)) ^ 2
      ∂productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) ν)) ≤
        (2 + 3 * ε ^ 2 * M) / (2 * d) := by
  let π := Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) ν
  let : IsProbabilityMeasure π := Measure.isProbabilityMeasure_map (by fun_prop)
  let μ := productPrior d π
  let : IsProbabilityMeasure μ := by dsimp [μ, productPrior]; infer_instance
  let Z : Fin d → (Fin d → ℝ) → ℝ := fun x θ => sparseClippedIntensity (hMpaper := hMpaper) M (θ x)
  have hZ (x : Fin d) : Measurable (Z x) := by dsimp [Z]; fun_prop
  have hz (x : Fin d) (θ : Fin d → ℝ) := sparseClippedIntensity_mem (hMpaper := hMpaper) hM (θ x)
  have hscalar : (∫ θ, sparseClippedIntensity (hMpaper := hMpaper) M θ ∂π) = 1 := by
    simpa only [π, id_eq] using
      (sparse_centered_clipped_integral (hMpaper := hMpaper) ν hsupp id measurable_id).trans hmean
  have hzm (x : Fin d) : (∫ θ, Z x θ ∂μ) = 1 := by
    change (∫ θ, sparseClippedIntensity (hMpaper := hMpaper) M (θ x) ∂Measure.pi (fun _ : Fin d => π)) = 1
    simpa only [Function.comp_apply, Function.eval] using
      ((measurePreserving_eval (fun _ : Fin d => π) x).hasLaw.integral_comp
        (measurable_sparseClippedIntensity (hMpaper := hMpaper) M).aestronglyMeasurable).trans hscalar
  have hind : iIndepFun Z μ := by
    exact iIndepFun_pi (fun _ => (measurable_sparseClippedIntensity (hMpaper := hMpaper) M).aemeasurable)
  have hphi : Measurable (phiEpsFormula ε) := by unfold phiEpsFormula; fun_prop
  have hpi (x : Fin d) : Integrable (fun θ => phiEpsFormula ε (Z x θ)) μ :=
    (sparse_phi_memLp_variance_le μ (Z x) M ε (hZ x) (hz x) (hzm x)
      hε hεhalf).1.integrable (by norm_num)
  have hcenter : (∫ θ, (∑ x, phiEpsFormula ε (Z x θ)) / d ∂μ) =
      ∫ z, phiEpsFormula ε z ∂ν := by
    rw [integral_div, integral_finsetSum _ (fun x _ => hpi x)]
    have hi (x : Fin d) : (∫ θ, phiEpsFormula ε (Z x θ) ∂μ) = ∫ z, phiEpsFormula ε z ∂ν := by
      change (∫ θ, phiEpsFormula ε (sparseClippedIntensity (hMpaper := hMpaper) M (θ x))
        ∂Measure.pi (fun _ : Fin d => π)) = _
      simpa only [Function.comp_apply, Function.eval] using
        ((measurePreserving_eval (fun _ : Fin d => π) x).hasLaw.integral_comp
          (show AEStronglyMeasurable (fun θ => phiEpsFormula ε (sparseClippedIntensity (hMpaper := hMpaper) M θ)) π from
            (by fun_prop : Measurable
              (fun θ => phiEpsFormula ε (sparseClippedIntensity (hMpaper := hMpaper) M θ))).aestronglyMeasurable)).trans
          (sparse_centered_clipped_integral (hMpaper := hMpaper) ν hsupp _ hphi)
    simp_rw [hi]
    simp [ne_of_gt (Nat.cast_pos.mpr hd : (0 : ℝ) < d)]
  have hb := sparse_prior_target_integral_sq_le μ hd Z M ε hZ hz hzm hind hε hεhalf
  dsimp only at hb
  rw [hcenter] at hb
  exact hb

/-- Chebyshev converts the derived sparse target second moment into the prior-tail bound used by fuzzy testing; no target concentration is assumed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hsupp,hmean,hε,hεhalf,hM,hr,hMpaper), the [stated conclusion](goal) holds. -/
lemma sparse_product_prior_target_tail_le {d : ℕ} (hd : 0 < d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {ε M r : ℝ}
    (hsupp : ν (Set.Icc 0 M)ᶜ = 0) (hmean : (∫ z, z ∂ν) = 1)
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) (hM : 0 ≤ M) (hr : 0 < r) (hMpaper : 2 ≤ M) :
    (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) ν)).real
      {θ | r < |sparsePriorTarget (hMpaper := hMpaper) d ε M θ -
        (1 / 2 + (∫ z, phiEpsFormula ε z ∂ν) / 2)|} ≤
      (2 + 3 * ε ^ 2 * M) / (2 * d * r ^ 2) := by
  let π := Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) ν
  let : IsProbabilityMeasure π := Measure.isProbabilityMeasure_map (by fun_prop)
  let μ := productPrior d π
  let : IsProbabilityMeasure μ := by dsimp [μ, productPrior]; infer_instance
  let center := 1 / 2 + (∫ z, phiEpsFormula ε z ∂ν) / 2
  have hLp : MemLp (sparsePriorTarget (hMpaper := hMpaper) d ε M) 2 μ :=
    MemLp.of_bound (measurable_sparsePriorTarget (hMpaper := hMpaper) d ε M).aestronglyMeasurable 1
      (ae_of_all _ fun θ => by
        have hb := sparsePriorTarget_mem_unit (hMpaper := hMpaper) hd hε hεhalf hM θ
        rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
        exact hb.2)
  have hint : Integrable (fun θ => (sparsePriorTarget (hMpaper := hMpaper) d ε M θ - center) ^ 2) μ :=
    (hLp.sub (memLp_const center)).integrable_sq
  have hsub : {θ | r < |sparsePriorTarget (hMpaper := hMpaper) d ε M θ - center|} ⊆
      {θ | r ^ 2 ≤ (sparsePriorTarget (hMpaper := hMpaper) d ε M θ - center) ^ 2} := by
    intro θ hθ
    change r < |sparsePriorTarget (hMpaper := hMpaper) d ε M θ - center| at hθ
    change r ^ 2 ≤ (sparsePriorTarget (hMpaper := hMpaper) d ε M θ - center) ^ 2
    have ha := abs_nonneg (sparsePriorTarget (hMpaper := hMpaper) d ε M θ - center)
    nlinarith [sq_abs (sparsePriorTarget (hMpaper := hMpaper) d ε M θ - center)]
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun θ => sq_nonneg (sparsePriorTarget (hMpaper := hMpaper) d ε M θ - center)) hint (r ^ 2)
  have hmoment := sparse_product_prior_target_integral_sq_le (hMpaper := hMpaper) hd ν hsupp hmean hε hεhalf hM
  have hbound : r ^ 2 * μ.real {θ | r < |sparsePriorTarget (hMpaper := hMpaper) d ε M θ - center|} ≤
      (2 + 3 * ε ^ 2 * M) / (2 * d) := by
    exact ((mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg r)).trans
      hmark).trans hmoment
  change μ.real {θ | r < |sparsePriorTarget (hMpaper := hMpaper) d ε M θ - center|} ≤ _
  calc
    _ ≤ ((2 + 3 * ε ^ 2 * M) / (2 * d)) / r ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hr)).2 (by simpa only [mul_comm] using hbound)
    _ = _ := by ring

/-- The product sparse experiment has probability fibres at every centered vector. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hMpaper), the [stated conclusion](goal) holds. -/
lemma sparseProductPoissonKernel_probability (B : ℝ) (n d : ℕ) (ε M : ℝ)
    (θ : Fin d → ℝ) (hMpaper : 2 ≤ M) : IsProbabilityMeasure (sparseProductPoissonKernel (hMpaper := hMpaper) B n d ε M θ) := by
  change IsProbabilityMeasure
    (Measure.pi fun x => poissonCellLaw B n d ε (θ x + sparseReference (_hMpaper := hMpaper) M))
  unfold poissonCellLaw
  infer_instance

/-- Mixing the full sparse product kernel against the centered product prior is exactly the product predictive law bounded in (36). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hMpaper), the [stated conclusion](goal) holds. -/
lemma sparse_product_prior_predictive_eq (B : ℝ) (n d : ℕ) (ε M : ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hMpaper : 2 ≤ M) :
    priorPredictive
      (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) ν))
      (sparseProductPoissonKernel (hMpaper := hMpaper) B n d ε M) =
      productPriorPredictive d (Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) ν)
        (sparseCenteredPoissonKernel (hMpaper := hMpaper) B n d ε M) := by
  let : IsProbabilityMeasure (Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) ν) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply priorPredictive_productPrior_eq_productPriorPredictive
  · intro θ
    change IsProbabilityMeasure (poissonCellLaw B n d ε (θ + sparseReference (_hMpaper := hMpaper) M))
    unfold poissonCellLaw
    infer_instance
  · intro θ
    rfl

/-- Equations (36)--(40), before fixed-sample transfer: the exact supported priors and their derived concentration give an estimator-wise Bayes-risk lower bound. The numerical alphabet condition is (39); the likelihood closeness is proved by the sparse full-likelihood theorem, not assumed. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma sparse_product_prior_bayesRisk_lower :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (K n d : ℕ) (ε M B : ℝ) (P : ConstrainedPriorPair K M),
        1 ≤ n → 2 ≤ d → 0 < ε → ε ≤ 1 / 2 → ∀ hM : 2 ≤ M,
        2 < B → C * logAlphabet d ≤ K →
        M ≤ η * d * K / (B * n * ε) →
        let Delta := |(∫ z, phiEpsFormula ε z ∂P.ν₁) - (∫ z, phiEpsFormula ε z ∂P.ν₀)| / 2
        64 * (2 + 3 * ε ^ 2 * M) ≤ d * Delta ^ 2 →
        ∀ est : (Fin d → (Fin 4 → ℕ)) → ℝ, Measurable est →
          ENNReal.ofReal (5 * Delta ^ 2 / 256) ≤
            max
              (bayesSquaredRisk
                (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₀))
                (sparseProductPoissonKernel (hMpaper := hM) B n d ε M) (sparsePriorTarget (hMpaper := hM) d ε M) est)
              (bayesSquaredRisk
                (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₁))
                (sparseProductPoissonKernel (hMpaper := hM) B n d ε M) (sparsePriorTarget (hMpaper := hM) d ε M) est) := by
  obtain ⟨η, C, hη, hC, htvbound⟩ := sparse_product_mixture_tv_le_one_eighth
  refine ⟨η, C, hη, hC, ?_⟩
  intro K n d ε M B P hn hd hε hεhalf hM hB hK hband
  dsimp only
  intro hsize est hest
  let := P.prob₀
  let := P.prob₁
  let π₀ := productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₀)
  let π₁ := productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₁)
  let : IsProbabilityMeasure (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₀) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₁) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure π₀ := by dsimp [π₀, productPrior]; infer_instance
  let : IsProbabilityMeasure π₁ := by dsimp [π₁, productPrior]; infer_instance
  let a := ∫ z, phiEpsFormula ε z ∂P.ν₀
  let b := ∫ z, phiEpsFormula ε z ∂P.ν₁
  let Delta := |b - a| / 2
  have hM0 : 0 ≤ M := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsize' : 64 * (2 + 3 * ε ^ 2 * M) ≤ d * Delta ^ 2 := hsize
  have hDelta : 0 < Delta := by
    have hnonneg : 0 ≤ Delta := by dsimp [Delta]; positivity
    have hprod : 0 ≤ ε ^ 2 * M := by positivity
    by_contra hnpos
    have hz : Delta = 0 := le_antisymm (le_of_not_gt hnpos) hnonneg
    rw [hz] at hsize'
    nlinarith
  have htail (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (hsupp : ν (Set.Icc 0 M)ᶜ = 0) (hmean : (∫ z, z ∂ν) = 1) :
      (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) ν)).real
        {θ | Delta / 4 < |sparsePriorTarget (hMpaper := hM) d ε M θ -
          (1 / 2 + (∫ z, phiEpsFormula ε z ∂ν) / 2)|} ≤ 1 / 8 := by
    apply (sparse_product_prior_target_tail_le (hMpaper := hM) (by omega) ν hsupp hmean
      hε.le hεhalf hM0 (by positivity : 0 < Delta / 4)).trans
    apply (div_le_iff₀ (by positivity : 0 < 2 * (d : ℝ) * (Delta / 4) ^ 2)).2
    nlinarith [hsize']
  have ht0 := htail P.ν₀ P.supp₀ P.mean₀
  have ht1 := htail P.ν₁ P.supp₁ P.mean₁
  have htv : Causalean.Stat.tvDist
      (priorPredictive π₀ (sparseProductPoissonKernel (hMpaper := hM) B n d ε M))
      (priorPredictive π₁ (sparseProductPoissonKernel (hMpaper := hM) B n d ε M)) ≤ 1 / 8 := by
    rw [sparse_product_prior_predictive_eq, sparse_product_prior_predictive_eq]
    exact htvbound K n d ε M B P hn hd hε hεhalf hM hB hK hband
  have hnum : ((Delta / 2 - Delta / 4) ^ 2 *
      (1 - (1 / 8 : ℝ) - 1 / 8 - 1 / 8)) / 2 = 5 * Delta ^ 2 / 256 := by ring
  by_cases hab : a ≤ b
  · have hsep : Delta ≤ (1 / 2 + b / 2) - (1 / 2 + a / 2) := by
      dsimp [Delta]
      rw [abs_of_nonneg (by linarith : 0 ≤ b - a)]
      linarith
    have hb := twoFuzzyHypotheses_bayesRisk_lower π₀ π₁
      (sparseProductPoissonKernel (hMpaper := hM) B n d ε M) (sparsePriorTarget (hMpaper := hM) d ε M)
      (sparseProductPoissonKernel_probability (hMpaper := hM) B n d ε M) est hest
      (measurable_sparsePriorTarget (hMpaper := hM) d ε M)
      (1 / 2 + a / 2) (1 / 2 + b / 2) Delta (Delta / 4) (1 / 8) (1 / 8) (1 / 8)
      hDelta.le (by positivity) (by linarith) hsep
      (by norm_num) (by norm_num) (by norm_num) ht0 ht1 htv
    rw [hnum] at hb
    exact hb
  · have hsep : Delta ≤ (1 / 2 + a / 2) - (1 / 2 + b / 2) := by
      dsimp [Delta]
      rw [abs_of_nonpos (by linarith : b - a ≤ 0)]
      linarith
    have htv' : Causalean.Stat.tvDist
        (priorPredictive π₁ (sparseProductPoissonKernel (hMpaper := hM) B n d ε M))
        (priorPredictive π₀ (sparseProductPoissonKernel (hMpaper := hM) B n d ε M)) ≤ 1 / 8 := by
      rw [Causalean.Stat.tvDist_symm]
      exact htv
    have hb := twoFuzzyHypotheses_bayesRisk_lower π₁ π₀
      (sparseProductPoissonKernel (hMpaper := hM) B n d ε M) (sparsePriorTarget (hMpaper := hM) d ε M)
      (sparseProductPoissonKernel_probability (hMpaper := hM) B n d ε M) est hest
      (measurable_sparsePriorTarget (hMpaper := hM) d ε M)
      (1 / 2 + b / 2) (1 / 2 + a / 2) Delta (Delta / 4) (1 / 8) (1 / 8) (1 / 8)
      hDelta.le (by positivity) (by linarith) hsep
      (by norm_num) (by norm_num) (by norm_num) ht1 ht0 htv'
    rw [hnum, max_comm] at hb
    exact hb

/-- The explicit Jackson-packet witness attains the auxiliary sparse testing lower order M/K². Both its expectation gap and its mixture TV bound are proved, and (39) is exposed as a numerical alphabet condition to be calibrated in the final sparse/dense assembly. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma sparse_packet_bayesRisk_lower :
    ∃ (c cp η C : ℝ) (A : ℕ),
      0 < c ∧ 0 < cp ∧ 0 < η ∧ 0 < C ∧ 1 ≤ A ∧
      ∀ (K n d : ℕ) (ε M B : ℝ),
        2 ≤ K → 1 ≤ n → 2 ≤ d → 0 < ε → ε ≤ 1 / 2 →
        ∀ hM : 2 ≤ M, M ≤ (K : ℝ) ^ 2 → 2 < B → C * logAlphabet d ≤ K →
        M ≤ η * d * K / (B * n * ε) →
        256 * (2 + 3 * ε ^ 2 * M) * (K : ℝ) ^ 2 ≤ cp ^ 2 * M * d →
        ∃ (P : ConstrainedPriorPair K M),
          ∃ hdom : CommonAtomDomain (packetPositive A K M) (packetNegative A K M),
            commonAtomCompletion (packetPositive A K M) (packetNegative A K M) hdom =
              (P.ν₀, P.ν₁) ∧
            ∀ est : (Fin d → (Fin 4 → ℕ)) → ℝ, Measurable est →
              ENNReal.ofReal (c * M / (K : ℝ) ^ 2) ≤
                max
                  (bayesSquaredRisk
                    (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₀))
                    (sparseProductPoissonKernel (hMpaper := hM) B n d ε M) (sparsePriorTarget (hMpaper := hM) d ε M) est)
                  (bayesSquaredRisk
                    (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₁))
                    (sparseProductPoissonKernel (hMpaper := hM) B n d ε M) (sparsePriorTarget (hMpaper := hM) d ε M) est) := by
  obtain ⟨cp, A, hcp, hA, hpacket⟩ := packetCompletion_separation_lower
  obtain ⟨η, C, hη, hC, hrisk⟩ := sparse_product_prior_bayesRisk_lower
  refine ⟨5 * cp ^ 2 / 1024, cp, η, C, A, by positivity, hcp, hη, hC, hA, ?_⟩
  intro K n d ε M B hK hn hd hε hεhalf hM hMhi hB hlog hband hsize
  obtain ⟨P, hdom, _, _, _, hcompletion, hgap⟩ :=
    hpacket K M ε hK hM hMhi hε.le hεhalf
  refine ⟨P, hdom, hcompletion, ?_⟩
  intro est hest
  let Delta := |(∫ z, phiEpsFormula ε z ∂P.ν₁) - (∫ z, phiEpsFormula ε z ∂P.ν₀)| / 2
  have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hM0 : 0 ≤ M := by linarith
  have hlower : cp ^ 2 * M / (4 * (K : ℝ) ^ 2) ≤ Delta ^ 2 := by
    have hhalf : cp * Real.sqrt M / (2 * K) ≤ Delta := by
      dsimp [Delta]
      simpa only [div_div, mul_comm] using
        div_le_div_of_nonneg_right hgap (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg : 0 ≤ cp * Real.sqrt M / (2 * K) := by positivity
    have hs := pow_le_pow_left₀ hnonneg hhalf 2
    have he : (cp * Real.sqrt M / (2 * K)) ^ 2 = cp ^ 2 * M / (4 * (K : ℝ) ^ 2) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hM0]
      ring
    rwa [he] at hs
  have hsize' : 64 * (2 + 3 * ε ^ 2 * M) ≤ d * Delta ^ 2 := by
    have hscaled : 64 * (2 + 3 * ε ^ 2 * M) ≤
        d * (cp ^ 2 * M / (4 * (K : ℝ) ^ 2)) := by
      calc
        _ ≤ ((d : ℝ) * cp ^ 2 * M) / (4 * (K : ℝ) ^ 2) := by
          apply (le_div_iff₀ (by positivity : 0 < 4 * (K : ℝ) ^ 2)).2
          nlinarith only [hsize]
        _ = _ := by ring
    exact hscaled.trans (mul_le_mul_of_nonneg_left hlower hdR.le)
  have hb := hrisk K n d ε M B P hn hd hε hεhalf hM hB hlog hband hsize' est hest
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hb
  calc
    (5 * cp ^ 2 / 1024) * M / (K : ℝ) ^ 2 =
        5 / 256 * (cp ^ 2 * M / (4 * (K : ℝ) ^ 2)) := by ring
    _ ≤ 5 / 256 * Delta ^ 2 := mul_le_mul_of_nonneg_left hlower (by norm_num)
    _ = 5 * Delta ^ 2 / 256 := by ring

/-- The centered product priors put all their mass on legal sparse vectors. Thus the extensions used in testing do not introduce illegal prior parameters. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hsupp,hMpaper), the [stated conclusion](goal) holds. -/
lemma sparse_product_prior_ae_legal {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {M : ℝ} (hsupp : ν (Set.Icc 0 M)ᶜ = 0) (hMpaper : 2 ≤ M) :
    ∀ᵐ θ ∂productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) ν),
      ∀ x, θ x + sparseReference (_hMpaper := hMpaper) M ∈ Set.Icc 0 M := by
  let π := Measure.map (fun z => z - sparseReference (_hMpaper := hMpaper) M) ν
  let : IsProbabilityMeasure π := Measure.isProbabilityMeasure_map (by fun_prop)
  have hmeas : MeasurableSet {θ : ℝ | θ + sparseReference (_hMpaper := hMpaper) M ∈ Set.Icc 0 M} :=
    measurableSet_Icc.preimage (by fun_prop)
  have hscalar : ∀ᵐ θ ∂π, θ + sparseReference (_hMpaper := hMpaper) M ∈ Set.Icc 0 M := by
    rw [ae_map_iff (by fun_prop) hmeas]
    simpa only [sub_add_cancel] using (show ∀ᵐ z ∂ν, z ∈ Set.Icc 0 M from (ae_iff).2 hsupp)
  rw [Filter.eventually_all]
  intro x
  exact ((measurePreserving_eval (fun _ : Fin d => π) x).hasLaw.ae_iff
    (measurableSet_setOfPred.mp hmeas)).2 hscalar

/-- On every legal vector the testing target is exactly the value of the normalized sparse observed law in the paper, by the full likelihood identity. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhalf,hM,hz), the [stated conclusion](goal) holds. -/
lemma sparsePriorTarget_eq_observedValue {d : ℕ} (hd : 2 ≤ d) {ε M : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hM : 2 ≤ M) (θ : Fin d → ℝ)
    (hz : ∀ x, θ x + sparseReference (_hMpaper := hM) M ∈ Set.Icc 0 M) :
    sparsePriorTarget (hMpaper := hM) d ε M θ =
      observedValue (sparseLaw (by omega : 0 < d) ε M ⟨hε, hεhalf⟩
        (fun x => θ x + sparseReference (_hMpaper := hM) M) hz) := by
  have hval := (sparse_likelihood 1 d ε M 4 (fun x => θ x + sparseReference (_hMpaper := hM) M)
    (by norm_num) hd hε hεhalf hM (by norm_num) hz).2.2.1
  rw [hval]
  have hclip (x : Fin d) : sparseClippedIntensity (hMpaper := hM) M (θ x) = θ x + sparseReference (_hMpaper := hM) M := by
    simpa only [add_sub_cancel_right] using sparseClippedIntensity_sub_reference (hMpaper := hM) (hz x)
  unfold sparsePriorTarget
  simp_rw [hclip]
  have he : 1 - ε + ε * ((∑ x, (θ x + sparseReference (_hMpaper := hM) M)) / d) =
      sparseNormalizerFormula d ε M (fun x => θ x + sparseReference (_hMpaper := hM) M) hz := by
    unfold sparseNormalizerFormula
    ring
  rw [he]
  ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
