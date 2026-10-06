module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparseTesting
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.AggregatePoisson

/-! # Total variation for the sparse product-Poisson mixtures

The four-coordinate Poisson laws form a measurable probability kernel.
The supported moment-matching API converts their exact Gram formula into
the product total-variation estimate in roadmap equation (36).
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Minimax.MomentMatchedMixture
open scoped BigOperators

-- @node: measurable_poissonCellLaw
/-- The sparse Poisson experiment is measurable as a function of intensity. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
@[fun_prop]
lemma measurable_poissonCellLaw (B : ℝ) (n d : ℕ) (ε : ℝ) :
    Measurable (poissonCellLaw B n d ε) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hatom (N : Fin 4 → ℕ) :
      Measurable (fun z => poissonCellLaw B n d ε z {N}) := by
    simp only [poissonCellLaw, Measure.pi_singleton, poissonMeasure_singleton]
    apply Finset.measurable_prod
    intro j _
    have hm : Measurable (fun z => poissonCellMean B n d ε z j) := by
      unfold poissonCellMean
      split_ifs <;> fun_prop
    fun_prop
  simp_rw [← Measure.tsum_indicator_apply_singleton _ s hs]
  apply Measurable.tsum
  intro N
  by_cases hN : N ∈ s
  · simpa [Set.indicator_of_mem hN] using hatom N
  · simp [Set.indicator_of_notMem hN]

/-- The centered sparse experiment, with probability fibres at every real parameter.
For the displayed parameters, sparseCenteredPoissonKernel is the object specified by this definition. -/
noncomputable def sparseCenteredPoissonKernel (B : ℝ) (n d : ℕ) (ε M : ℝ)
    (hMpaper : 2 ≤ M) : Kernel ℝ (Fin 4 → ℕ) where
  toFun θ := poissonCellLaw B n d ε (θ + sparseReference (_hMpaper := hMpaper) M)
  measurable' := (measurable_poissonCellLaw B n d ε).comp (by fun_prop)
/-- Moment-matched packet priors have product-mixture TV bounded by the alphabet size times the square root of the tail from equation (34). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hε,hεhalf,hM,hB), the [stated conclusion](goal) holds. -/
lemma sparse_product_mixture_tv_le_sqrt_tail {K n d : ℕ} {ε M B : ℝ}
    (P : ConstrainedPriorPair K M) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hM : 2 ≤ M) (hB : 2 < B) :
    Causalean.Stat.tvDist
      (productPriorPredictive d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₀)
        (sparseCenteredPoissonKernel (hMpaper := hM) B n d ε M))
      (productPriorPredictive d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₁)
        (sparseCenteredPoissonKernel (hMpaper := hM) B n d ε M)) ≤
      d * Real.sqrt (exponentialSeriesTail K
        (sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM * M ^ 2 / 4)) := by
  let := P.prob₀
  let := P.prob₁
  let π₀ := Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₀
  let π₁ := Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₁
  let Q := poissonCellLaw B n d ε (sparseReference (_hMpaper := hM) M)
  let L := fun θ N => oneCellLikelihood (hMpaper := hM) B n d ε M (θ + sparseReference (_hMpaper := hM) M) N
  have hcenter : Measurable (fun z => z - sparseReference (_hMpaper := hM) M) := by fun_prop
  let : IsProbabilityMeasure π₀ := Measure.isProbabilityMeasure_map hcenter.aemeasurable
  let : IsProbabilityMeasure π₁ := Measure.isProbabilityMeasure_map hcenter.aemeasurable
  let : IsProbabilityMeasure Q := by dsimp [Q, poissonCellLaw]; infer_instance
  have hα : 0 ≤ sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM := by
    have hB0 : 0 ≤ B := by linarith
    have hbase : 0 ≤ 1 - ε := by linarith
    have hM0 : 0 ≤ M := by linarith
    unfold sparseGramCoefficient sparseReference
    positivity
  have hlegal (θ : ℝ) (hθ : |θ| ≤ M / 2) :
      θ + sparseReference (_hMpaper := hM) M ∈ Set.Icc 0 M := by
    rw [abs_le] at hθ
    dsimp [sparseReference]
    constructor <;> linarith [hθ.1, hθ.2]
  have hmeas : Measurable (fun p : ℝ × (Fin 4 → ℕ) => L p.1 p.2) := by
    change Measurable (fun p : ℝ × (Fin 4 → ℕ) =>
      oneCellLikelihood (hMpaper := hM) B n d ε M (p.1 + sparseReference (_hMpaper := hM) M) p.2)
    have ht : Measurable (fun p : ℝ × (Fin 4 → ℕ) =>
      (p.1 + sparseReference (_hMpaper := hM) M, p.2)) := by fun_prop
    exact Measurable.comp
      (g := fun p : ℝ × (Fin 4 → ℕ) => oneCellLikelihood (hMpaper := hM) B n d ε M p.1 p.2)
      (f := fun p : ℝ × (Fin 4 → ℕ) => (p.1 + sparseReference (_hMpaper := hM) M, p.2))
      (measurable_oneCellLikelihood (hMpaper := hM) B n d ε M) ht
  have hgram := (sparse_likelihood n d ε M B (fun _ => 0) hn hd hε hεhalf hM hB
    (fun _ => ⟨le_rfl, by linarith⟩)).2.2.2.1
  have hinner : ∀ θ, |θ| ≤ M / 2 → ∀ θ', |θ'| ≤ M / 2 →
      (∫ N, L θ N * L θ' N ∂Q) =
        Real.exp (sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM * θ * θ') := by
    intro θ hθ θ' hθ'
    simpa [L, Q] using hgram _ _ (hlegal θ hθ) (hlegal θ' hθ')
  have hdensity : ∀ θ, |θ| ≤ M / 2 →
      sparseCenteredPoissonKernel (hMpaper := hM) B n d ε M θ =
        Q.withDensity (fun N => ENNReal.ofReal (L θ N)) := by
    intro θ hθ
    exact poissonCellLaw_eq_withDensity_oneCellLikelihood
      hB hn hd hε hεhalf hM (hlegal θ hθ)
  have hbound := momentMatchedProductMixture_tv_le_of_supported
    d π₀ π₁ (sparseCenteredPoissonKernel (hMpaper := hM) B n d ε M) Q L
    (fun θ => by
      change IsProbabilityMeasure (poissonCellLaw B n d ε (θ + sparseReference (_hMpaper := hM) M))
      unfold poissonCellLaw
      infer_instance)
    (sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM) (M / 2) K hα (by linarith)
    hmeas (fun θ hθ N => oneCellLikelihood_nonneg hB hε hεhalf hM (hlegal θ hθ) N)
    hdensity hinner (sparse_centered_prior_support (hMpaper := hM) P.ν₀ P.supp₀)
    (sparse_centered_prior_support (hMpaper := hM) P.ν₁ P.supp₁)
    (constrainedPriorPair_centered_moments (hMpaper := hM) P)
  simpa only [π₀, π₁, show (M / 2) ^ 2 = M ^ 2 / 4 by ring,
    mul_div_assoc] using hbound


-- @node: sparse_geometric_degree_calibration
/-- A geometric one-cell error becomes at most 1/8 after tensorization when the degree exceeds a universal multiple of log(ed). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hD,hρ), the [stated conclusion](goal) holds. -/
lemma sparse_geometric_degree_calibration {D ρ : ℝ}
    (hD : 0 < D) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 2 ≤ d →
      C * logAlphabet d ≤ K → (d : ℝ) * (D * ρ ^ K) ≤ 1 / 8 := by
  let a := -Real.log ρ
  have ha : 0 < a := neg_pos.mpr (Real.log_neg hρ.1 hρ.2)
  let C := (|Real.log (8 * D)| + 2) / a
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro d K hd hK
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hd1
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd1
  have hL : logAlphabet d = 1 + Real.log d := by
    rw [logAlphabet, Real.log_mul (Real.exp_pos _).ne' hd0.ne', Real.log_exp]
  have hKa : (|Real.log (8 * D)| + 2) * (1 + Real.log d) ≤ a * K := by
    rw [hL] at hK
    have := (mul_le_mul_of_nonneg_left hK ha.le)
    dsimp [C] at this
    field_simp at this
    nlinarith
  have hlog : Real.log (8 * D * d) ≤ a * K := by
    rw [Real.log_mul (by positivity) hd0.ne']
    nlinarith [le_abs_self (Real.log (8 * D)), abs_nonneg (Real.log (8 * D)),
      mul_nonneg (abs_nonneg (Real.log (8 * D))) hld]
  have hp : ρ ^ K = Real.exp (-a * K) := by
    rw [← Real.exp_log (pow_pos hρ.1 K), Real.log_pow]
    congr 1
    dsimp [a]
    ring
  calc
    (d : ℝ) * (D * ρ ^ K) = (d * D) * Real.exp (-a * K) := by rw [hp]; ring
    _ ≤ (d * D) * Real.exp (-Real.log (8 * D * d)) := by
      gcongr
      linarith
    _ = 1 / 8 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
      <;> ring

/-- Roadmap (34)--(36): one universal small support scale and one universal logarithmic degree scale make the full sparse product experiments indistinguishable. The support constraint is precisely the second branch of (33). In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma sparse_product_mixture_tv_le_one_eighth :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (K n d : ℕ) (ε M B : ℝ) (P : ConstrainedPriorPair K M),
        1 ≤ n → 2 ≤ d → 0 < ε → ε ≤ 1 / 2 → ∀ hM : 2 ≤ M,
        ∀ hB : 2 < B, C * logAlphabet d ≤ K →
        M ≤ η * d * K / (B * n * ε) →
        Causalean.Stat.tvDist
          (productPriorPredictive d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₀)
            (sparseCenteredPoissonKernel (hMpaper := hM) B n d ε M))
          (productPriorPredictive d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₁)
            (sparseCenteredPoissonKernel (hMpaper := hM) B n d ε M)) ≤ 1 / 8 := by
  obtain ⟨b, D, ρ, hb, hD, hρ, htail⟩ :=
    FiniteSignedMomentMarkedPoissonMixture.exists_geometric_sqrt_exponentialSeriesTail_bound
      1 (by norm_num)
  obtain ⟨C, hC, hcal⟩ := sparse_geometric_degree_calibration hD hρ
  refine ⟨2 * b, C, by positivity, hC, ?_⟩
  intro K n d ε M B P hn hd hε hεhalf hM hB hK hband
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hB0 : 0 < B := by linarith
  have hden : 0 < B * n * ε := by positivity
  have hsmall : B * n * ε * M / (2 * d) ≤ b * K := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)).2
    have h := (le_div_iff₀ hden).1 hband
    nlinarith
  let t := sparseGramCoefficient B hB n d ε M ⟨hε, hεhalf⟩ hM * M ^ 2 / 4
  have ht0 : 0 ≤ t := by
    have hbase : 0 ≤ 1 - ε := by linarith
    have hM0 : 0 ≤ M := by linarith
    dsimp [t, sparseGramCoefficient, sparseReference]
    positivity
  have ht : t ≤ b * K :=
    (sparse_mixture_series_argument_le hn hd hε hεhalf hM hB).trans hsmall
  have hdecay : Real.sqrt (exponentialSeriesTail K t) ≤ D * ρ ^ K := by
    simpa only [one_mul] using htail K t ht0 ht
  calc
    _ ≤ d * Real.sqrt (exponentialSeriesTail K t) :=
      sparse_product_mixture_tv_le_sqrt_tail P hn hd hε hεhalf hM hB
    _ ≤ d * (D * ρ ^ K) := mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg d)
    _ ≤ 1 / 8 := hcal d K hd hK

end CausalSmith.Stat.OptvalueVanishingoverlapRate
