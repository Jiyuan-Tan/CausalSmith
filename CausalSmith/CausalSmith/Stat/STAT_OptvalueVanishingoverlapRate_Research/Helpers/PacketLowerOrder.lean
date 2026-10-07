module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.WeightedDuality
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TrigExtraction
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.JacksonPacket
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Concrete Jackson packet measures

The positive and negative packet parts are finite measures supported on `[0,M]`,
with every polynomial moment integrable. These construction properties implement
roadmap (30). Exact pushforward, signed-pairing, and absolute-density formulas
recover the circle packet and its weighted normalization when the weight is
positive. The Fourier support argument proves matching of every moment through
degree K. Strict positivity and the kink-response lower bound remain open.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory

/-- The cosine coordinate in the Jackson-packet lower construction. -/
noncomputable def packetIntensity (M t : ℝ) : ℝ :=
  M / 2 * (1 + Real.cos t)

/-- The two translated, high-frequency Jackson waves centered at the kink. -/
noncomputable def packetWave (A₀ K : ℕ) (M t : ℝ) : ℝ :=
  let N := A₀ * K
  let θ := Real.arccos (2 / M - 1)
  packetOscillation N (t - θ) + packetOscillation N (t + θ)

/-- The exact weighted variation used to normalize the signed packet. -/
noncomputable def packetWeight (A₀ K : ℕ) (M : ℝ) : ℝ :=
  ∫ t in Set.Icc (-Real.pi) Real.pi,
    (1 + packetIntensity M t) * |packetWave A₀ K M t| / (2 * Real.pi)

/-- Positive Jordan part of the normalized Jackson packet, pushed to `[0,M]`. -/
noncomputable def packetPositive (A₀ K : ℕ) (M : ℝ) : Measure ℝ :=
  Measure.map (packetIntensity M)
    ((volume.restrict (Set.Icc (-Real.pi) Real.pi)).withDensity
      (fun t => ENNReal.ofReal
        (max (packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi)) 0)))

/-- Negative Jordan part of the same signed packet, pushed to `[0,M]`. -/
noncomputable def packetNegative (A₀ K : ℕ) (M : ℝ) : Measure ℝ :=
  Measure.map (packetIntensity M)
    ((volume.restrict (Set.Icc (-Real.pi) Real.pi)).withDensity
      (fun t => ENNReal.ofReal
        (max (-(packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi))) 0)))

/-- The cosine coordinate is continuous on the entire circle parameter line. The [stated conclusion](goal) holds. -/
-- @node: continuous_packetIntensity
@[fun_prop] lemma continuous_packetIntensity (M : ℝ) :
    Continuous (packetIntensity M) := by
  unfold packetIntensity
  fun_prop

/-- Nonnegative endpoints put every cosine intensity in the desired support. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
-- @node: packetIntensity_mem_Icc
lemma packetIntensity_mem_Icc {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    packetIntensity M t ∈ Set.Icc 0 M := by
  have hlo := Real.neg_one_le_cos t
  have hhi := Real.cos_le_one t
  unfold packetIntensity
  constructor
  · exact mul_nonneg (by positivity) (by linarith)
  · nlinarith

/-- Pushing any measure through the cosine coordinate concentrates it on `[0,M]`; in particular no Jordan-part mass escapes the paper's interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
-- @node: packetIntensity_map_support
lemma packetIntensity_map_support {M : ℝ} (hM : 0 ≤ M) (μ : Measure ℝ) :
    (Measure.map (packetIntensity M) μ) (Set.Icc 0 M)ᶜ = 0 := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
  have he : packetIntensity M ⁻¹' (Set.Icc 0 M)ᶜ = ∅ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
      iff_false, not_not]
    exact packetIntensity_mem_Icc hM t
  rw [he, measure_empty]

/-- The concrete positive packet is supported on the constrained-prior interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
-- @node: packetPositive_support
lemma packetPositive_support (A₀ K : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    packetPositive A₀ K M (Set.Icc 0 M)ᶜ = 0 := by
  unfold packetPositive
  exact packetIntensity_map_support hM _

/-- The concrete negative packet has the same constrained-prior support. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
-- @node: packetNegative_support
lemma packetNegative_support (A₀ K : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    packetNegative A₀ K M (Set.Icc 0 M)ᶜ = 0 := by
  unfold packetNegative
  exact packetIntensity_map_support hM _

/-- The translated packet wave is continuous, including zero degree. The [stated conclusion](goal) holds. -/
-- @node: continuous_packetWave
@[fun_prop] lemma continuous_packetWave (A₀ K : ℕ) (M : ℝ) :
    Continuous (packetWave A₀ K M) := by
  unfold packetWave packetOscillation packetKernel
  fun_prop (disch := exact
    Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)

/-- Either Jordan density is integrable on the compact circle interval, even before positivity of the normalization weight is proved. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: packetDensity_integrable
lemma packetDensity_integrable (A₀ K : ℕ) (M sign : ℝ) :
    Integrable (fun t => max
      (sign * (packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi))) 0)
      (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
  apply ContinuousOn.integrableOn_compact (K := Set.Icc (-Real.pi) Real.pi)
    (μ := volume) isCompact_Icc
  fun_prop

/-- The compactly supported positive density defines a finite measure. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: packetPositive_finite
lemma packetPositive_finite (A₀ K : ℕ) (M : ℝ) :
    IsFiniteMeasure (packetPositive A₀ K M) := by
  have hi := packetDensity_integrable A₀ K M 1
  simp only [one_mul] at hi
  let hm := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => le_max_right _ _)).mpr hi)
  unfold packetPositive
  infer_instance

/-- The compactly supported negative density also defines a finite measure. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: packetNegative_finite
lemma packetNegative_finite (A₀ K : ℕ) (M : ℝ) :
    IsFiniteMeasure (packetNegative A₀ K M) := by
  have hi := packetDensity_integrable A₀ K M (-1)
  simp only [neg_one_mul] at hi
  let hm := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => le_max_right _ _)).mpr hi)
  unfold packetNegative
  infer_instance

/-- Compact support makes every polynomial moment of both concrete packet parts integrable; no moment regularity premise is necessary. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
-- @node: packetParts_integrable_moments
lemma packetParts_integrable_moments (A₀ K : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (j : ℕ) :
    Integrable (fun z => z ^ j) (packetPositive A₀ K M) ∧
      Integrable (fun z => z ^ j) (packetNegative A₀ K M) := by
  let := packetPositive_finite A₀ K M
  let := packetNegative_finite A₀ K M
  exact ⟨integrable_of_supported_Icc _ M (packetPositive_support A₀ K hM)
      _ (by fun_prop),
    integrable_of_supported_Icc _ M (packetNegative_support A₀ K hM)
      _ (by fun_prop)⟩

/-- The only remaining common-atom domain obligation for these concrete packet parts is the positive part's strict mass bound. Finiteness and first-moment integrability follow from the construction. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
-- @node: packetParts_commonAtomDomain_iff
lemma packetParts_commonAtomDomain_iff (A₀ K : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    CommonAtomDomain (packetPositive A₀ K M) (packetNegative A₀ K M) ↔
      packetPositive A₀ K M Set.univ < 1 := by
  constructor
  · intro h
    exact h.2.2.2.2
  · intro hmass
    have hi := packetParts_integrable_moments A₀ K hM 1
    simp only [pow_one] at hi
    exact ⟨packetPositive_finite A₀ K M, packetNegative_finite A₀ K M,
      hi.1, hi.2, hmass⟩


/-- Change of variables and the real density formula recover either packet part exactly, without a positivity assumption on the normalization weight. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hf), the [stated conclusion](goal) holds. -/
-- @node: packetPart_integral
lemma packetPart_integral (A₀ K : ℕ) (M sign : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) :
    (∫ z, f z ∂Measure.map (packetIntensity M)
      ((volume.restrict (Set.Icc (-Real.pi) Real.pi)).withDensity
        (fun t => ENNReal.ofReal (max
          (sign * (packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi))) 0)))) =
    ∫ t in Set.Icc (-Real.pi) Real.pi,
      max (sign * (packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi))) 0 *
        f (packetIntensity M t) := by
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul]

/-- The signed difference of the pushed-forward packet parts is exactly the normalized circle pairing, as used in roadmap (30). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hf,hfc), the [stated conclusion](goal) holds. -/
-- @node: packetParts_integral_sub
lemma packetParts_integral_sub (A₀ K : ℕ) (M : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f)
    (hfc : ContinuousOn (fun t => f (packetIntensity M t))
      (Set.Icc (-Real.pi) Real.pi)) :
    (∫ z, f z ∂packetPositive A₀ K M) -
      (∫ z, f z ∂packetNegative A₀ K M) =
    ∫ t in Set.Icc (-Real.pi) Real.pi,
      (packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi)) *
        f (packetIntensity M t) := by
  have hpformula := packetPart_integral A₀ K M 1 f hf
  have hmformula := packetPart_integral A₀ K M (-1) f hf
  simp only [one_mul, neg_one_mul] at hpformula hmformula
  rw [packetPositive, packetNegative, hpformula, hmformula]
  have hp : Integrable (fun t => max
      (packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi)) 0 *
        f (packetIntensity M t)) (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (by fun_prop : ContinuousOn _ (Set.Icc (-Real.pi) Real.pi)).mul hfc
  have hm : Integrable (fun t => max
      (-(packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi))) 0 *
        f (packetIntensity M t)) (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (by fun_prop : ContinuousOn _ (Set.Icc (-Real.pi) Real.pi)).mul hfc
  rw [← integral_sub hp hm]
  apply integral_congr_ae
  filter_upwards with t
  by_cases h : 0 ≤ packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi)
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

/-- The sum of the two packet-part integrals is the absolute-density pairing; there is no loss of variation in the explicit positive/negative construction. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hf,hfc), the [stated conclusion](goal) holds. -/
-- @node: packetParts_integral_add
lemma packetParts_integral_add (A₀ K : ℕ) (M : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f)
    (hfc : ContinuousOn (fun t => f (packetIntensity M t))
      (Set.Icc (-Real.pi) Real.pi)) :
    (∫ z, f z ∂packetPositive A₀ K M) +
      (∫ z, f z ∂packetNegative A₀ K M) =
    ∫ t in Set.Icc (-Real.pi) Real.pi,
      |packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi)| *
        f (packetIntensity M t) := by
  have hpformula := packetPart_integral A₀ K M 1 f hf
  have hmformula := packetPart_integral A₀ K M (-1) f hf
  simp only [one_mul, neg_one_mul] at hpformula hmformula
  rw [packetPositive, packetNegative, hpformula, hmformula]
  have hp : Integrable (fun t => max
      (packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi)) 0 *
        f (packetIntensity M t)) (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (by fun_prop : ContinuousOn _ (Set.Icc (-Real.pi) Real.pi)).mul hfc
  have hm : Integrable (fun t => max
      (-(packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi))) 0 *
        f (packetIntensity M t)) (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (by fun_prop : ContinuousOn _ (Set.Icc (-Real.pi) Real.pi)).mul hfc
  rw [← integral_add hp hm]
  apply integral_congr_ae
  filter_upwards with t
  by_cases h : 0 ≤ packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi)
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
    ring
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith),
      abs_of_neg (lt_of_not_ge h)]
    ring


/-- The circle normalization weight is nonnegative for the paper's support range. Its strict positivity is a separate Fourier/kink-response obligation. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
-- @node: packetWeight_nonneg
lemma packetWeight_nonneg (A₀ K : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ packetWeight A₀ K M := by
  apply integral_nonneg
  intro t
  have hz := (packetIntensity_mem_Icc hM t).1
  exact div_nonneg (mul_nonneg (by linarith) (abs_nonneg _)) (by positivity)

/-- With positive normalization weight, the two explicit packet parts have combined weighted mass exactly one, the normalization in roadmap (30). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hW), the [stated conclusion](goal) holds. -/
-- @node: packetParts_weighted_normalization
lemma packetParts_weighted_normalization (A₀ K : ℕ) (M : ℝ)
    (hW : 0 < packetWeight A₀ K M) :
    (∫ z, (1 + z) ∂packetPositive A₀ K M) +
      (∫ z, (1 + z) ∂packetNegative A₀ K M) = 1 := by
  rw [packetParts_integral_add A₀ K M (fun z => 1 + z) (by fun_prop) (by fun_prop)]
  have hpi : 0 < (2 * Real.pi : ℝ) := by positivity
  calc
    _ = ∫ t in Set.Icc (-Real.pi) Real.pi,
        ((1 + packetIntensity M t) * |packetWave A₀ K M t| /
          (2 * Real.pi)) / packetWeight A₀ K M := by
      apply integral_congr_ae
      filter_upwards with t
      rw [abs_div, abs_div, abs_of_pos hW, abs_of_pos hpi]
      ring
    _ = packetWeight A₀ K M / packetWeight A₀ K M := by
      rw [integral_div]
      rfl
    _ = 1 := div_self (ne_of_gt hW)

/-- The normalization can be read directly as the sum of the two masses and first moments, ready for the degree-zero/one annihilation identities. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM,hW), the [stated conclusion](goal) holds. -/
-- @node: packetParts_mass_add_moment
lemma packetParts_mass_add_moment (A₀ K : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hW : 0 < packetWeight A₀ K M) :
    ((packetPositive A₀ K M) Set.univ).toReal +
      (∫ z, z ∂packetPositive A₀ K M) +
      (((packetNegative A₀ K M) Set.univ).toReal +
        (∫ z, z ∂packetNegative A₀ K M)) = 1 := by
  let := packetPositive_finite A₀ K M
  let := packetNegative_finite A₀ K M
  have hi := packetParts_integrable_moments A₀ K hM 1
  simp only [pow_one] at hi
  have hnorm := packetParts_weighted_normalization A₀ K M hW
  rw [integral_add (integrable_const 1) hi.1,
    integral_add (integrable_const 1) hi.2] at hnorm
  simpa only [integral_const, smul_eq_mul, mul_one, Measure.real] using hnorm


/-- The actual kink objective has the exact signed-packet response, despite its irrelevant singular encoding outside the nonnegative supporting interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma packetParts_phiEps_sub (A₀ K : ℕ) {M : ℝ} (hM : 0 ≤ M) (ε : ℝ) :
    (∫ z, phiEpsFormula ε z ∂packetPositive A₀ K M) -
      (∫ z, phiEpsFormula ε z ∂packetNegative A₀ K M) =
    ∫ t in Set.Icc (-Real.pi) Real.pi,
      (packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi)) *
        phiEpsFormula ε (packetIntensity M t) := by
  apply packetParts_integral_sub
  · unfold phiEpsFormula
    fun_prop
  · unfold phiEpsFormula
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      have hz := (packetIntensity_mem_Icc hM t).1
      linarith


/-- Integer cosine modes are unchanged after a full circle turn. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: packet_cos_periodic
lemma packet_cos_periodic (r : ℤ) :
    Function.Periodic (fun t : ℝ => Real.cos ((r : ℝ) * t)) (2 * Real.pi) := by
  intro t
  change Real.cos ((r : ℝ) * (t + 2 * Real.pi)) = Real.cos ((r : ℝ) * t)
  rw [mul_add]
  exact Real.cos_add_int_mul_two_pi _ r

/-- Fourier reconstruction makes the packet periodic before translation. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN), the [stated conclusion](goal) holds. -/
-- @node: packetOscillation_periodic
lemma packetOscillation_periodic {N : ℕ} (hN : 0 < N) :
    Function.Periodic (packetOscillation N) (2 * Real.pi) := by
  intro t
  change Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.kernel N
      (t + 2 * Real.pi) * Real.cos (4 * (N : ℝ) * (t + 2 * Real.pi)) =
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.kernel N t *
      Real.cos (4 * (N : ℝ) * t)
  rw [Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.kernel_fourier
      N hN (t + 2 * Real.pi),
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.kernel_fourier
      N hN t]
  have hsum : (∑ j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ),
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.normalizedCoeff N j *
        Real.cos ((j : ℝ) * (t + 2 * Real.pi))) =
      ∑ j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ),
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.normalizedCoeff N j *
        Real.cos ((j : ℝ) * t) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun x =>
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.normalizedCoeff N j * x)
      (packet_cos_periodic j t)
  rw [hsum]
  congr 1
  convert packet_cos_periodic (4 * (N : ℤ)) t using 1 <;> push_cast <;> rfl

/-- Translation preserves the integral of a periodic function over one turn. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hf), the [stated conclusion](goal) holds. -/
-- @node: packet_periodic_integral_translate
lemma packet_periodic_integral_translate (f : ℝ → ℝ)
    (hf : Function.Periodic f (2 * Real.pi)) (θ : ℝ) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, f (t - θ)) =
      ∫ t in Set.Icc (-Real.pi) Real.pi, f t := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    intervalIntegral.integral_comp_sub_right]
  convert hf.intervalIntegral_add_eq (-Real.pi - θ) (-Real.pi) using 1 <;>
    congr 1 <;> ring

/-- A translated high-frequency packet annihilates every low-frequency real trigonometric polynomial. This is the Fourier-support argument in (16). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN,hKN,hf), the [stated conclusion](goal) holds. -/
-- @node: packetOscillation_trig_annihilation
lemma packetOscillation_trig_annihilation {N K : ℕ} (hN : 2 ≤ N)
    (hKN : K < 2 * N + 2) (f : ℝ → ℝ)
    (hf : Causalean.Mathlib.Analysis.JacksonApproximation.IsTrigPolyLE K f)
    (θ : ℝ) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, packetOscillation N (t - θ) * f t) = 0 := by
  obtain ⟨a, b, hab⟩ := hf
  have hshift (t : ℝ) : f (t + θ) =
      ∑ r ∈ Finset.range (K + 1),
        ((a r * Real.cos ((r : ℝ) * θ) + b r * Real.sin ((r : ℝ) * θ)) *
            Real.cos ((r : ℝ) * t) +
         (b r * Real.cos ((r : ℝ) * θ) - a r * Real.sin ((r : ℝ) * θ)) *
            Real.sin ((r : ℝ) * t)) := by
    rw [hab]
    apply Finset.sum_congr rfl
    intro r hr
    rw [mul_add, Real.cos_add, Real.sin_add]
    ring
  have hperiod : Function.Periodic (fun t => packetOscillation N t * f (t + θ))
      (2 * Real.pi) := by
    intro t
    change packetOscillation N (t + 2 * Real.pi) * f (t + 2 * Real.pi + θ) =
      packetOscillation N t * f (t + θ)
    rw [packetOscillation_periodic (N := N) (by omega) t]
    congr 1
    rw [hab, hab]
    apply Finset.sum_congr rfl
    intro r hr
    have hc := packet_cos_periodic (r : ℤ) (t + θ)
    have hs : Real.sin ((r : ℝ) * ((t + θ) + 2 * Real.pi)) =
        Real.sin ((r : ℝ) * (t + θ)) := by
      rw [mul_add]
      exact Real.sin_add_int_mul_two_pi _ (r : ℤ)
    convert congrArg₂ (fun x y => a r * x + b r * y) hc hs using 1 <;>
      congr 2 <;> push_cast <;> ring
  calc
    _ = ∫ t in Set.Icc (-Real.pi) Real.pi, packetOscillation N t * f (t + θ) := by
      convert packet_periodic_integral_translate _ hperiod θ using 1
      simp only [sub_add_cancel]
    _ = 0 := by
      simp_rw [hshift, Finset.mul_sum]
      rw [integral_finsetSum _ (fun r hr =>
        (show Continuous (fun t => packetOscillation N t *
          ((a r * Real.cos ((r : ℝ) * θ) + b r * Real.sin ((r : ℝ) * θ)) *
              Real.cos ((r : ℝ) * t) +
           (b r * Real.cos ((r : ℝ) * θ) - a r * Real.sin ((r : ℝ) * θ)) *
              Real.sin ((r : ℝ) * t))) by
          unfold packetOscillation packetKernel
          fun_prop (disch := exact
            Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)
        ).continuousOn.integrableOn_compact isCompact_Icc)]
      apply Finset.sum_eq_zero
      intro r hr
      have hrK : r ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      have hz := Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packet_shifted_support
        N hN (r : ℤ) (Or.inl (by
          rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ r)]
          exact_mod_cast (lt_of_le_of_lt hrK hKN)))
      change (∫ t in Set.Icc (-Real.pi) Real.pi,
        packetOscillation N t * Real.cos ((r : ℝ) * t)) = 0 ∧
        (∫ t in Set.Icc (-Real.pi) Real.pi,
        packetOscillation N t * Real.sin ((r : ℝ) * t)) = 0 at hz
      simp_rw [mul_add, mul_left_comm (packetOscillation N _) _]
      rw [integral_add, integral_const_mul, integral_const_mul, hz.1, hz.2]
      · ring
      all_goals
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        unfold packetOscillation packetKernel
        fun_prop (disch := exact
          Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)


/-- Every degree-at-most-K polynomial in the intensity has zero circle pairing with the explicit two-center packet, exactly as in roadmap (16). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hK,hp), the [stated conclusion](goal) holds. -/
-- @node: packetWave_polynomial_annihilation
lemma packetWave_polynomial_annihilation {A₀ K : ℕ} (hA : 1 ≤ A₀)
    (hK : 2 ≤ K) (M : ℝ) (p : Polynomial ℝ) (hp : p.natDegree ≤ K) :
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      packetWave A₀ K M t * p.eval (packetIntensity M t)) = 0 := by
  let q : Polynomial ℝ := p.comp (Polynomial.C (M / 2) * (1 + Polynomial.X))
  have hlin : (Polynomial.C (M / 2) * (1 + Polynomial.X)).natDegree ≤ 1 := by
    calc
      _ ≤ (Polynomial.C (M / 2)).natDegree + (1 + Polynomial.X).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 := by
        simp only [Polynomial.natDegree_C, zero_add]
        exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have hq : q.natDegree ≤ K := by
    exact Polynomial.natDegree_comp_le.trans
      ((Nat.mul_le_mul_right _ hp).trans (by simpa using Nat.mul_le_mul_left K hlin))
  have heval (t : ℝ) : q.eval (Real.cos t) = p.eval (packetIntensity M t) := by
    simp [q, Polynomial.eval_comp, packetIntensity]
  have ht := (Causalean.Mathlib.Analysis.JacksonApproximation.polynomial_cos_is_even_trigPoly
    q hq).1
  have hN : 2 ≤ A₀ * K := by nlinarith
  have hKN : K < 2 * (A₀ * K) + 2 := by nlinarith
  have hplus := packetOscillation_trig_annihilation hN hKN _ ht
    (Real.arccos (2 / M - 1))
  have hminus := packetOscillation_trig_annihilation hN hKN _ ht
    (-Real.arccos (2 / M - 1))
  simp_rw [heval] at hplus hminus
  simp only [sub_neg_eq_add] at hminus
  unfold packetWave
  simp only [add_mul]
  rw [integral_add, hplus, hminus, add_zero]
  all_goals
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    unfold packetOscillation packetKernel
    fun_prop (disch := exact
      Causalean.Mathlib.Analysis.JacksonApproximation.continuous_jackson _)

/-- The actual pushed-forward positive and negative packets match every moment through degree K; no positivity or moment-matching premise is assumed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hK,hj), the [stated conclusion](goal) holds. -/
-- @node: packetParts_moments_match
lemma packetParts_moments_match {A₀ K : ℕ} (hA : 1 ≤ A₀) (hK : 2 ≤ K)
    (M : ℝ) {j : ℕ} (hj : j ≤ K) :
    (∫ z, z ^ j ∂packetPositive A₀ K M) =
      ∫ z, z ^ j ∂packetNegative A₀ K M := by
  apply sub_eq_zero.mp
  rw [packetParts_integral_sub A₀ K M (fun z => z ^ j) (by fun_prop) (by fun_prop)]
  have hz := packetWave_polynomial_annihilation hA hK M
    (Polynomial.X ^ j) (by simpa using hj)
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at hz
  calc
    _ = (∫ t in Set.Icc (-Real.pi) Real.pi,
        packetWave A₀ K M t * packetIntensity M t ^ j) /
          packetWeight A₀ K M / (2 * Real.pi) := by
      rw [← integral_div, ← integral_div]
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = 0 := by rw [hz]; simp

end CausalSmith.Stat.OptvalueVanishingoverlapRate
