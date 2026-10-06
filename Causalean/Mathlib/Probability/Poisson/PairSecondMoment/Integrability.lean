module
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Basic
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.CountEnvelope
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.FixedCount
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Mixture
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Moments

/-!
# Measurability and count envelopes for a Poisson pair sum

The squared bilinear statistic is bounded on each fixed-count fibre by the
count product squared times the one-pair squared-kernel moment. This provides
the summable nonnegative envelope for the two independent Poisson counts.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace Causalean.Mathlib.Probability.Poisson.PairSecondMoment

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Given [a real kernel](hyp:K) with [a measurable uncurried form](hyp:hK),
[its bilinear sum over pairs of finite samples is measurable](goal). -/
@[fun_prop] theorem measurable_pairSum (K : X → Y → ℝ)
    (hK : Measurable (Function.uncurry K)) :
    Measurable (fun p : FiniteSample X × FiniteSample Y => pairSum K p.1 p.2) := by
  -- Use the sigma-type measurable-space constructor: on each pair of count
  -- fibres this is a finite sum of measurable coordinate evaluations.
  classical
  have hEmbedX (k : ℕ) :
      MeasurableEmbedding (fixedSizeEmbed (X := X) k) := by
    refine ⟨?_, measurable_fixedSizeEmbed k, ?_⟩
    · intro x y h
      simpa [fixedSizeEmbed] using h
    · intro s hs
      change MeasurableSet[⨅ a, MeasurableSpace.map
          (@Sigma.mk ℕ (fun r => Fin r → X) a) inferInstance]
        (@Sigma.mk ℕ (fun r => Fin r → X) k '' s)
      simp only [MeasurableSpace.measurableSet_iInf]
      intro a
      change MeasurableSet
        ((@Sigma.mk ℕ (fun r => Fin r → X) a) ⁻¹'
          (@Sigma.mk ℕ (fun r => Fin r → X) k '' s))
      by_cases h : a = k
      · subst a
        have hinj : Function.Injective
            (@Sigma.mk ℕ (fun r => Fin r → X) k) := by
          intro x y hxy
          simpa using hxy
        rw [hinj.preimage_image]
        exact hs
      · rw [Set.preimage_image_sigmaMk_of_ne h]
        exact MeasurableSet.empty
  have hEmbedY (k : ℕ) :
      MeasurableEmbedding (fixedSizeEmbed (X := Y) k) := by
    refine ⟨?_, measurable_fixedSizeEmbed k, ?_⟩
    · intro x y h
      simpa [fixedSizeEmbed] using h
    · intro s hs
      change MeasurableSet[⨅ a, MeasurableSpace.map
          (@Sigma.mk ℕ (fun r => Fin r → Y) a) inferInstance]
        (@Sigma.mk ℕ (fun r => Fin r → Y) k '' s)
      simp only [MeasurableSpace.measurableSet_iInf]
      intro a
      change MeasurableSet
        ((@Sigma.mk ℕ (fun r => Fin r → Y) a) ⁻¹'
          (@Sigma.mk ℕ (fun r => Fin r → Y) k '' s))
      by_cases h : a = k
      · subst a
        have hinj : Function.Injective
            (@Sigma.mk ℕ (fun r => Fin r → Y) k) := by
          intro x y hxy
          simpa using hxy
        rw [hinj.preimage_image]
        exact hs
      · rw [Set.preimage_image_sigmaMk_of_ne h]
        exact MeasurableSet.empty
  have hfiber (m n : ℕ) : Measurable
      (fun p : (Fin m → X) × (Fin n → Y) =>
        ∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j)) := by
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    have hpair : Measurable
        (fun p : (Fin m → X) × (Fin n → Y) => (p.1 i, p.2 j)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd)
    simpa only [Function.comp_def, Function.uncurry] using hK.comp hpair
  intro s hs
  have hpre :
      (fun p : FiniteSample X × FiniteSample Y => pairSum K p.1 p.2) ⁻¹' s =
        ⋃ m : ℕ, ⋃ n : ℕ,
          (Prod.map (fixedSizeEmbed (X := X) m) (fixedSizeEmbed (X := Y) n)) ''
            ((fun p : (Fin m → X) × (Fin n → Y) =>
              ∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j)) ⁻¹' s) := by
    ext p
    rcases p with ⟨⟨m, x⟩, ⟨n, y⟩⟩
    constructor
    · intro hp
      refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨n, ?_⟩⟩
      refine ⟨(x, y), ?_, ?_⟩
      · simpa [pairSum] using hp
      · rfl
    · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage] at *
      rintro ⟨m', n', q, hq, heq⟩
      change (fun p : FiniteSample X × FiniteSample Y => pairSum K p.1 p.2)
        (⟨m, x⟩, ⟨n, y⟩) ∈ s
      rw [← heq]
      change (∑ i : Fin m', ∑ j : Fin n', K (q.1 i) (q.2 j)) ∈ s
      exact hq
  rw [hpre]
  exact MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun n =>
    ((hEmbedX m).prodMap (hEmbedY n)).measurableSet_image.mpr ((hfiber m n) hs)

/-- Given [two probability laws](hyp:P,Q), [a measurable real kernel](hyp:K,hK),
[an integrable kernel square](hyp:hK2), and [two fixed array lengths](hyp:m,n),
[the expected squared bilinear sum is bounded by the squared length product
times the one-pair squared-kernel moment](goal). -/
theorem integral_fixedCount_pairSum_sq_le
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (K : X → Y → ℝ) (m n : ℕ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q)) :
    (∫ p : (Fin m → X) × (Fin n → Y),
      (∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j)) ^ 2
      ∂((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q))) ≤
      (m : ℝ) ^ 2 * (n : ℝ) ^ 2 *
        (∫ x, ∫ y, K x y ^ 2 ∂Q ∂P) := by
  -- Integrate `pairSum_sq_le_count_mul_sum_sq`, using
  -- `integrable_fixedCount_pairSum_sq` and the termwise integrability from
  -- `integral_fixedCount_sum_kernel_sq`; then evaluate the finite sum.
  classical
  let μ := (Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q)
  have hsum : Integrable
      (fun p : (Fin m → X) × (Fin n → Y) =>
        ∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j) ^ 2) μ := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    simpa only [pow_two] using
      (integrable_fixedCount_kernelProduct P Q K m n hK hK2 i i j j)
  have hle := integral_mono
    (integrable_fixedCount_pairSum_sq P Q K m n hK hK2)
    (hsum.const_mul ((m : ℝ) * (n : ℝ)))
    (fun p => pairSum_sq_le_count_mul_sum_sq K ⟨m, p.1⟩ ⟨n, p.2⟩)
  change (∫ p, (∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j)) ^ 2 ∂μ) ≤ _ at hle ⊢
  rw [integral_const_mul, integral_fixedCount_sum_kernel_sq P Q K m n hK hK2] at hle
  nlinarith [hle]

/-- Given [two probability laws](hyp:P,Q), [a measurable real kernel](hyp:K,hK),
[an integrable kernel square](hyp:hK2), and [two fixed array lengths](hyp:m,n),
[the nonnegative squared-sum integral is bounded by the two squared counts
times the one-pair squared-kernel integral](goal). -/
theorem lintegral_fixedCount_pairSum_sq_le
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (K : X → Y → ℝ) (m n : ℕ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q)) :
    (∫⁻ p : (Fin m → X) × (Fin n → Y),
      ENNReal.ofReal
        ((∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j)) ^ 2)
      ∂((Measure.pi fun _ : Fin m => P).prod
        (Measure.pi fun _ : Fin n => Q))) ≤
      (m : ℝ≥0∞) ^ 2 * (n : ℝ≥0∞) ^ 2 *
        (∫⁻ p : X × Y, ENNReal.ofReal (K p.1 p.2 ^ 2) ∂(P.prod Q)) := by
  -- Convert both nonnegative lintegrals to real integrals with
  -- `ofReal_integral_eq_lintegral_ofReal`; use the proved fixed-count real
  -- bound, `integral_prod`, and nonnegativity of each square. Reassociate
  -- `ENNReal.ofReal` products using nonnegative factors.
  classical
  let μ := (Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q)
  have hfixed := ofReal_integral_eq_lintegral_ofReal
    (integrable_fixedCount_pairSum_sq P Q K m n hK hK2)
    (Filter.Eventually.of_forall fun p => sq_nonneg
      (∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j)))
  have hpair := ofReal_integral_eq_lintegral_ofReal hK2
    (Filter.Eventually.of_forall fun p => sq_nonneg (K p.1 p.2))
  have hbound := integral_fixedCount_pairSum_sq_le P Q K m n hK hK2
  rw [← integral_prod _ hK2] at hbound
  change (∫ p, (∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j)) ^ 2 ∂μ) ≤ _ at hbound
  change (∫⁻ p, ENNReal.ofReal
    ((∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j)) ^ 2) ∂μ) ≤ _
  rw [← hfixed, ← hpair]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_pow, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (m : ℝ) ^ 2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (m : ℝ) ^ 2 * (n : ℝ) ^ 2)]
  all_goals first | exact ENNReal.ofReal_le_ofReal hbound | positivity

/-- Given [two probability laws](hyp:P,Q), [their nonnegative Poisson
rates](hyp:rateA,rateB), [a measurable real kernel](hyp:K,hK), and [an
integrable kernel square](hyp:hK2), [the nonnegative integral of the squared
bilinear sample sum is finite](goal). -/
theorem lintegral_pairSum_sq_lt_top
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (rateA rateB : ℝ≥0) (K : X → Y → ℝ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q)) :
    (∫⁻ p : FiniteSample X × FiniteSample Y,
      ENNReal.ofReal (pairSum K p.1 p.2 ^ 2)
      ∂((finitePoissonSampleLaw P rateA).prod
        (finitePoissonSampleLaw Q rateB))) < ⊤ := by
  -- Expand by `lintegral_pair_count_mixture`. Apply
  -- `lintegral_fixedCount_pairSum_sq_le` termwise, factor the constant
  -- one-pair lintegral out of the double series, and apply
  -- `poisson_pair_count_sq_series_lt_top`. Measurability of the ENNReal
  -- integrand follows from `measurable_pairSum K hK`, `Measurable.pow_const`,
  -- and `ENNReal.measurable_ofReal`. The one-pair lintegral is finite by
  -- `hK2.lintegral_lt_top`; handle a zero value before cancelling or
  -- reassociating an infinite ENNReal factor.
  let C : ℝ≥0∞ := ∫⁻ p : X × Y, ENNReal.ofReal (K p.1 p.2 ^ 2) ∂(P.prod Q)
  have hC : C < ⊤ := by
    have h := hK2.lintegral_lt_top
    exact h
  have hmeas : Measurable (fun p : FiniteSample X × FiniteSample Y =>
      ENNReal.ofReal (pairSum K p.1 p.2 ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((measurable_pairSum K hK).pow_const 2)
  rw [lintegral_pair_count_mixture P Q rateA rateB _ hmeas]
  have hbound (m n : ℕ) :
      (poissonMeasure rateA) ({m} : Set ℕ) *
        (poissonMeasure rateB) ({n} : Set ℕ) *
          (∫⁻ p : (Fin m → X) × (Fin n → Y),
            ENNReal.ofReal (pairSum K ⟨m, p.1⟩ ⟨n, p.2⟩ ^ 2)
            ∂((Measure.pi fun _ : Fin m => P).prod
              (Measure.pi fun _ : Fin n => Q))) ≤
      ((poissonMeasure rateA) ({m} : Set ℕ) *
        (poissonMeasure rateB) ({n} : Set ℕ) *
          ((m : ℝ≥0∞) ^ 2 * (n : ℝ≥0∞) ^ 2)) * C := by
    have h := lintegral_fixedCount_pairSum_sq_le P Q K m n hK hK2
    dsimp only [pairSum]
    calc
      _ ≤ (poissonMeasure rateA) ({m} : Set ℕ) *
        (poissonMeasure rateB) ({n} : Set ℕ) *
          ((m : ℝ≥0∞) ^ 2 * (n : ℝ≥0∞) ^ 2 * C) := by
            gcongr
      _ = _ := by ac_rfl
  have hsum := poisson_pair_count_sq_series_lt_top rateA rateB
  have hle :
      (∑' m : ℕ, ∑' n : ℕ,
        (poissonMeasure rateA) ({m} : Set ℕ) *
          (poissonMeasure rateB) ({n} : Set ℕ) *
            (∫⁻ p : (Fin m → X) × (Fin n → Y),
              ENNReal.ofReal (pairSum K ⟨m, p.1⟩ ⟨n, p.2⟩ ^ 2)
              ∂((Measure.pi fun _ : Fin m => P).prod
                (Measure.pi fun _ : Fin n => Q)))) ≤
      (∑' m : ℕ, ∑' n : ℕ,
        (poissonMeasure rateA) ({m} : Set ℕ) *
          (poissonMeasure rateB) ({n} : Set ℕ) *
            ((m : ℝ≥0∞) ^ 2 * (n : ℝ≥0∞) ^ 2)) * C := by
    calc
      _ ≤ ∑' m : ℕ, ∑' n : ℕ,
          ((poissonMeasure rateA) ({m} : Set ℕ) *
            (poissonMeasure rateB) ({n} : Set ℕ) *
              ((m : ℝ≥0∞) ^ 2 * (n : ℝ≥0∞) ^ 2)) * C := by
              exact ENNReal.tsum_le_tsum fun m => ENNReal.tsum_le_tsum fun n => hbound m n
      _ = _ := by simp_rw [ENNReal.tsum_mul_right]
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top hsum hC)

end Causalean.Mathlib.Probability.Poisson.PairSecondMoment
