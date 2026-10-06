module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.OrderedRounding
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionDefinitions

/-! # Spectral design and capacity handle

One smoothness-free kernel uses the ordered cosine/sine features of the reflected and
commonly shifted original sample. Its seed measure and exact arithmetic map are explicit.
Feature prefixes are obtained by finite box sorting, with no well-founded enumeration.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
attribute [local instance] Classical.propDecidable
variable {n d : ℕ}

/-- [ One representative of each {k,-k}, taking the first nonzero coordinate positive. -/
def IsFrequencyRepresentative (k : Fin d → ℤ) : Prop :=
  1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2 ∧
    ∃ j : Fin d, 0 < k j ∧ ∀ l : Fin d, l < j → k l = 0
/-- Lexicographic tie-breaking in the original coordinate order. -/
def frequencyBefore (k l : Fin d → ℤ) : Bool :=
  decide (frequencyComplexity k < frequencyComplexity l ∨
    (frequencyComplexity k = frequencyComplexity l ∧
      List.Lex (· < ·) ((List.finRange d).map k) ((List.finRange d).map l)))
/-- Finite frequency enumeration for a requested prefix. -/
def orderedFrequencyBox (d J : ℕ) : List (Fin d → ℤ) :=
  (((frequencyBox d J).toList.filter (fun k => decide (IsFrequencyRepresentative k))).mergeSort
    frequencyBefore)
/-- The index-th frequency in the prescribed ordering; a box of radius index+1 suffices. -/
def featureFrequency (d index : ℕ) : Fin d → ℤ :=
  (orderedFrequencyBox d (index + 1)).getD index 0
/-- Consecutive real cosine/sine pairs, with row numbering starting at one. -/
def features (d h : ℕ) (y : Torus d) : ℝ :=
  let k := featureFrequency d ((h - 1) / 2)
  if (h - 1) % 2 = 0 then Real.sqrt 2 * (ek k y).re else Real.sqrt 2 * (ek k y).im
  -- @realizes features(ordered √2 cosine/sine pairs by complexity then lexicographic order)
/-- Independent fair reflection coins for every original unit and coordinate. -/
abbrev ReflectionCoins (n d : ℕ) := Fin n → Fin d → Bool
  -- @realizes reflection(independent fair coin array)
/-- Uniform law of the reflection coins. -/
def reflectionLaw (n d : ℕ) : Measure (ReflectionCoins n d) :=
  (PMF.uniformOfFintype (ReflectionCoins n d)).toMeasure
/-- The reflected covariates, encoded by half of the period-two coordinate. -/
def lift (x : Covariates n d) (η : ReflectionCoins n d) : Fin n → Torus d :=
  fun i j => ((if η i j then (2 - x i j) / 2 else x i j / 2 : ℝ) : UnitAddCircle)
  -- @realizes lift(X or 2-X, interpreted in period-two torus)
/-- Shift the lifted sample by one independent common Haar torus element. -/
def shiftedSample (x : Covariates n d) (η : ReflectionCoins n d) (T : Torus d) :
    Fin n → Torus d := fun i => lift x η i + T
  -- @realizes W(lift_i+T mod 2)
  -- @realizes T(common independent Haar shift; law via spectralSeedLaw)
/-- Reflection coins, common shift, and independent uniform rounding seeds. -/
abbrev SpectralSeeds (n d : ℕ) := ReflectionCoins n d × Torus d × RoundingSeeds n
/-- Independent spectral seed law. -/
def spectralSeedLaw (n d : ℕ) : Measure (SpectralSeeds n d) :=
  (reflectionLaw n d).prod ((torusMeasure d).prod (roundingSeedLaw n))
  -- @realizes reflection(independent uniform reflection law)
  -- @realizes T(Haar-uniform and independent of all other seeds)
/-- Evaluate the first floor(n/4) prescribed real rows at the randomized sample. -/
def spectralRows (w : Fin n → Torus d) : Fin (n / 4) → Fin n → ℝ :=
  fun h i => features d (h.val + 1) (w i)
/-- The prescribed exact-real signing map. -/
def spectralSigns (x : Covariates n d) (seed : SpectralSeeds n d) : Signs n :=
  orderedBoundaryRounding n (spectralRows (shiftedSample x seed.1 seed.2.1)) seed.2.2
/-- Joint Borel measurability of the exact spectral signing map. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: spectralSigns_measurable
lemma spectralSigns_measurable (n d : ℕ) :
    Measurable (fun xs : Covariates n d × SpectralSeeds n d => spectralSigns xs.1 xs.2) := by
  have hround := (ordered_prefix_rounding n (fun _ _ => 0) 0
    (by intros; simp)).1
  have hfeatures (h : ℕ) : Measurable (features d h) := by
    unfold features ek
    split <;> fun_prop
  have hlift : Measurable (fun xs : Covariates n d × SpectralSeeds n d =>
      shiftedSample xs.1 xs.2.1 xs.2.2.1) := by
    unfold shiftedSample lift
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    have hcoin : Measurable (fun xs : Covariates n d × SpectralSeeds n d =>
        xs.2.1 i j) := by fun_prop
    have hcoord : Measurable (fun xs : Covariates n d × SpectralSeeds n d =>
        if xs.2.1 i j = true then (2 - xs.1 i j) / 2 else xs.1 i j / 2) :=
      Measurable.ite (hcoin (measurableSet_singleton true)) (by fun_prop) (by fun_prop)
    exact ((AddCircle.continuous_mk' (1 : ℝ)).measurable.comp hcoord).add (by fun_prop)
  have hrows : Measurable (fun xs : Covariates n d × SpectralSeeds n d =>
      spectralRows (shiftedSample xs.1 xs.2.1 xs.2.2.1)) := by
    apply measurable_pi_lambda
    intro h
    apply measurable_pi_lambda
    intro i
    exact (hfeatures (h.val + 1)).comp ((measurable_pi_apply i).comp hlift)
  exact hround.comp (hrows.prodMk (by fun_prop))
/-- Measurability of the seed-image kernel. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: spectralMeasure_measurable
lemma spectralMeasure_measurable (n d : ℕ) :
    Measurable (fun x : Covariates n d => (spectralSeedLaw n d).map (spectralSigns x)) := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (spectralSeedLaw n d) := by
    unfold spectralSeedLaw reflectionLaw roundingSeedLaw cubeMeasure
    infer_instance
  have hjoint := spectralSigns_measurable n d
  have h := (Measure.measurable_map _ hjoint).comp
    (Measurable.map_prodMk_left (ν := spectralSeedLaw n d) (α := Covariates n d))
  simpa only [Function.comp_def, Measure.map_map hjoint measurable_prodMk_left] using h
/-- Seed image of the prescribed procedure. -/
def spectralRoundingKernel (n d : ℕ) : Kernel (Covariates n d) (Signs n) :=
  ⟨fun x => (spectralSeedLaw n d).map (spectralSigns x), spectralMeasure_measurable n d⟩
/-- The spectral seed-image kernel has total mass one.](goal) This uses [the stated conclusion](goal). -/
-- @node: spectralRoundingKernel_markov
lemma spectralRoundingKernel_markov (n d : ℕ) :
    IsMarkovKernel (spectralRoundingKernel n d) := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (spectralSeedLaw n d) := by
    unfold spectralSeedLaw reflectionLaw roundingSeedLaw cubeMeasure
    infer_instance
  constructor
  intro x
  have hsigns : Measurable (spectralSigns x) := by
    fun_prop
  exact Measure.isProbabilityMeasure_map hsigns.aemeasurable
/-- [ Every prescribed real Fourier row has the common envelope √2.](goal) -/
-- @node: features_abs_le
lemma features_abs_le (d h : ℕ) (y : Torus d) : |features d h y| ≤ Real.sqrt 2 := by
  have hn : ‖ek (featureFrequency d ((h - 1) / 2)) y‖ ≤ 1 := by
    simpa only [ek, UnitAddTorus.mFourier_norm] using
      (UnitAddTorus.mFourier (featureFrequency d ((h - 1) / 2))).norm_coe_le_norm y
  unfold features
  split
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hn)
      (Real.sqrt_nonneg _)).trans_eq (mul_one _)
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans hn)
      (Real.sqrt_nonneg _)).trans_eq (mul_one _)

/-- [ One attaining design for every smoothness: independent signs when B≥n. -/
def piStar (n d : ℕ) : Design n d :=
  if n ≤ pairCount d then fairSignKernel n d
  else ⟨spectralRoundingKernel n d, spectralRoundingKernel_markov n d⟩
  -- @realizes pi_star(s-free independent-sign or spectral-rounding kernel)
/-- The concrete attaining construction has pointwise zero sign means, a stronger
internal property than the public class's almost-everywhere fairness requirement.](goal) This uses [the stated conclusion](goal). -/
-- @node: piStar_pointwise_fair
lemma piStar_pointwise_fair (n d : ℕ) : PointwiseFairKernel (piStar n d).val := by
  intro x i
  by_cases hbranch : n ≤ pairCount d
  · simpa only [piStar, if_pos hbranch, fairSignKernel, Kernel.const_apply] using
      fairSigns_mean_zero n i
  · simp only [piStar, if_neg hbranch]
    change ∫ z, sgn (z i) ∂(spectralSeedLaw n d).map (spectralSigns x) = 0
    have hm : Measurable (spectralSigns x) := by fun_prop
    have hz : Measurable (fun z : Signs n => sgn (z i)) := by fun_prop
    rw [integral_map hm.aemeasurable hz.aestronglyMeasurable]
    letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨by simp [Real.volume_Icc]⟩
    letI : IsProbabilityMeasure (reflectionLaw n d) := by
      unfold reflectionLaw; infer_instance
    letI : IsProbabilityMeasure (roundingSeedLaw n) := by
      unfold roundingSeedLaw cubeMeasure; infer_instance
    letI : IsProbabilityMeasure (spectralSeedLaw n d) := by
      unfold spectralSeedLaw; infer_instance
    let f : SpectralSeeds n d → ℝ := fun seed => sgn (spectralSigns x seed i)
    have hf : Measurable f := by fun_prop
    have hbound : ∀ seed, ‖f seed‖ ≤ 1 := by
      intro seed
      dsimp [f]
      cases spectralSigns x seed i <;> norm_num [sgn]
    have hi : Integrable f (spectralSeedLaw n d) :=
      Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)
    change ∫ seed, f seed ∂spectralSeedLaw n d = 0
    rw [spectralSeedLaw, integral_prod _ hi]
    have hinner (η : ReflectionCoins n d) :
        ∫ ts, f (η, ts) ∂(torusMeasure d).prod (roundingSeedLaw n) = 0 := by
      have hfi : Integrable (fun ts => f (η, ts))
          ((torusMeasure d).prod (roundingSeedLaw n)) :=
        Integrable.of_bound (hf.comp measurable_prodMk_left).aestronglyMeasurable 1
          (Filter.Eventually.of_forall (fun ts => hbound (η, ts)))
      rw [integral_prod _ hfi]
      have hround (T : Torus d) :
          ∫ seeds, f (η, T, seeds) ∂roundingSeedLaw n = 0 := by
        exact (ordered_prefix_rounding n
          (fun h j => features d h (shiftedSample x η T j)) (Real.sqrt 2)
          (fun h j _ => features_abs_le d h _)).2.2.1 i
      simp_rw [hround]
      simp
    simp_rw [hinner]
    simp
/-- Explicit comparison scale. -/
def aScale (n d : ℕ) (s : ℝ) : ℝ := min 1 (((pairCount d : ℝ) / n) ^ s)
  -- @realizes a_s(min 1 (B/n)^s)

-- @node: def:capacity-handle
/-- The comparison scale, single original-sample design, and independent finite prior. -/
def capacityHandle (n d : ℕ) (s : ℝ) :
    ℝ × Design n d × PMF (PairIdx d (priorCutoff n d) → Bool) :=
  (aScale n d s, piStar n d, cosinePrior n d s)

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
