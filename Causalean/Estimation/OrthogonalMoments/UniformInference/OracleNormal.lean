module
public import Causalean.Estimation.OrthogonalMoments.UniformInference.Basic
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenCore
public import Causalean.Stat.Sample.PiTransport

/-! # Uniform Gaussian approximation for bounded oracle scores

The oracle score has mean zero, a uniform positive variance floor, and a
uniform third absolute moment bound. A quantitative scalar Berry–Esseen
bound gives a normal approximation uniformly over a changing class of laws.
The bounded score assumption also supplies the fourth moment needed for
variance estimation downstream.
-/

@[expose] public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat Causalean.Stat.CLT.BerryEsseen

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

/-- Oracle regularity means that the mean-zero score is measurable and
uniformly bounded, its variance stays above `vmin > 0`, and its third
absolute moment stays below `M3` over every current law class. -/
structure OracleConditions (B vmin M3 : ℝ) : Prop where
  B_nonneg : 0 ≤ B
  vmin_pos : 0 < vmin
  M3_nonneg : 0 ≤ M3
  measurable : ∀ p, Measurable (F.oracle p)
  mean_zero : ∀ n p, p ∈ F.lawClass n →
    ∫ z, F.oracle p z ∂F.laws p = 0
  bounded : ∀ n p, p ∈ F.lawClass n → ∀ z,
    |F.oracle p z| ≤ B
  variance_lower : ∀ n p, p ∈ F.lawClass n →
    vmin ≤ F.oracleVar p
  third_moment : ∀ n p, p ∈ F.lawClass n →
    ∫ z, |F.oracle p z| ^ 3 ∂F.laws p ≤ M3

namespace Family

/-- The standardized oracle sum divides the normalized empirical influence
score by its law-specific population standard deviation. -/
noncomputable def standardizedOracle (n : ℕ) (p : ι) (ω : Ω) : ℝ :=
  F.oracleSum n p ω / Real.sqrt (F.oracleVar p)

/-- A bounded third absolute moment and positive variance floor give a
uniform scalar Berry–Esseen distribution-function bound for each positive
sample size. The constant one is a conservative universal constant. -/
theorem oracle_berry_esseen
    {B vmin M3 : ℝ} (O : OracleConditions F B vmin M3)
    (n : ℕ) (hn : 0 < n) (p : ι) (hp : p ∈ F.lawClass n) (x : ℝ) :
    |(F.sampleLaw p {ω | F.standardizedOracle n p ω ≤ x}).toReal -
      ((gaussianReal 0 1) (Set.Iic x)).toReal| ≤
      M3 / ((Real.sqrt vmin) ^ 3 * Real.sqrt (n : ℝ)) := by
  let μ : Measure ℝ := (F.laws p).map (F.oracle p)
  haveI : IsProbabilityMeasure (F.sampleLaw p) := (F.sample p).indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure (F.laws p) := by
    rw [← (F.sample p).map_eq 0]
    exact Measure.isProbabilityMeasure_map ((F.sample p).meas 0).aemeasurable
  have hm : Measurable (F.oracle p) := O.measurable p
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hm.aemeasurable
  have hv : 0 < F.oracleVar p := lt_of_lt_of_le O.vmin_pos (O.variance_lower n p hp)
  have hmean_int : Integrable (F.oracle p) (F.laws p) := by
    apply Integrable.of_bound hm.aestronglyMeasurable B
    filter_upwards [] with z
    simpa using O.bounded n p hp z
  have hvar_int : Integrable (fun z => (F.oracle p z) ^ 2) (F.laws p) := by
    apply Integrable.of_bound (by fun_prop) (B ^ 2)
    filter_upwards [] with z
    have hz := O.bounded n p hp z
    simpa only [Real.norm_eq_abs, abs_pow, abs_sq] using (pow_le_pow_left₀ (abs_nonneg _) hz 2)
  have hthird_int : Integrable (fun z => |F.oracle p z| ^ 3) (F.laws p) := by
    apply Integrable.of_bound (by fun_prop) (B ^ 3)
    filter_upwards [] with z
    have hz := O.bounded n p hp z
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using (pow_le_pow_left₀ (abs_nonneg _) hz 3)
  have hmean_map : Integrable (fun y : ℝ => y) μ :=
    (integrable_map_measure (by fun_prop) hm.aemeasurable).2 (by exact hmean_int)
  have hvar_map : Integrable (fun y : ℝ => y ^ 2) μ :=
    (integrable_map_measure (by fun_prop) hm.aemeasurable).2 (by exact hvar_int)
  have hthird_map : Integrable (fun y : ℝ => |y| ^ 3) μ :=
    (integrable_map_measure (by fun_prop) hm.aemeasurable).2 (by exact hthird_int)
  have hmean : ∫ y : ℝ, y ∂μ = 0 := by
    rw [show (∫ y : ℝ, y ∂μ) = ∫ z, F.oracle p z ∂F.laws p from
      integral_map hm.aemeasurable (by fun_prop)]
    exact O.mean_zero n p hp
  have hvar : ∫ y : ℝ, y ^ 2 ∂μ = F.oracleVar p := by
    rw [show (∫ y : ℝ, y ^ 2 ∂μ) = ∫ z, (F.oracle p z) ^ 2 ∂F.laws p from
      integral_map hm.aemeasurable (by fun_prop)]
    rfl
  have hthird : ∫ y : ℝ, |y| ^ 3 ∂μ ≤ M3 := by
    rw [show (∫ y : ℝ, |y| ^ 3 ∂μ) = ∫ z, |F.oracle p z| ^ 3 ∂F.laws p from
      integral_map hm.aemeasurable (by fun_prop)]
    exact O.third_moment n p hp
  let T : Ω → Fin n → ℝ := fun ω i => F.oracle p ((F.sample p).Z i ω)
  have hTmeas : Measurable T := by
    apply measurable_pi_lambda
    intro i
    exact hm.comp ((F.sample p).meas i)
  have hTlaw : (F.sampleLaw p).map T = Measure.pi (fun _ : Fin n => μ) := by
    calc
      (F.sampleLaw p).map T =
          (Measure.pi (fun _ : Fin n => F.laws p)).map
            (fun v i => F.oracle p (v i)) := by
        rw [← Causalean.Stat.iidSample_finN_pushforward (F.sample p) n]
        rw [Measure.map_map (Causalean.Stat.measurable_finCoordinatewise n hm)
          (Causalean.Stat.iidSample_finN_measurable (F.sample p) n)]
        rfl
      _ = Measure.pi (fun _ : Fin n => μ) :=
        Causalean.Stat.map_pi_finCoordinatewise n (F.laws p) hm
  have hE : MeasurableSet
      {v : Fin n → ℝ | (∑ i : Fin n, v i) /
        (Real.sqrt (n : ℝ) * Real.sqrt (F.oracleVar p)) ≤ x} := by
    exact measurableSet_le (by fun_prop) measurable_const
  have hevent :
      F.sampleLaw p {ω | F.standardizedOracle n p ω ≤ x} =
      (Measure.pi (fun _ : Fin n => μ))
        {v : Fin n → ℝ | (∑ i : Fin n, v i) /
          (Real.sqrt (n : ℝ) * Real.sqrt (F.oracleVar p)) ≤ x} := by
    rw [← hTlaw, Measure.map_apply hTmeas hE]
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, T, standardizedOracle, oracleSum]
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ => F.oracle p ((F.sample p).Z j ω)) n]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring_nf
  rw [hevent]
  calc
    _ ≤ M3 / ((Real.sqrt (F.oracleVar p)) ^ 3 * Real.sqrt (n : ℝ)) :=
      iid_real_berry_esseen μ (F.oracleVar p) M3 hv hmean_map hmean
        hvar_map hvar hthird_map hthird n hn x
    _ ≤ M3 / ((Real.sqrt vmin) ^ 3 * Real.sqrt (n : ℝ)) := by
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
      have hden : 0 < (Real.sqrt vmin) ^ 3 * Real.sqrt (n : ℝ) := by
        exact mul_pos (pow_pos (Real.sqrt_pos.2 O.vmin_pos) _) (Real.sqrt_pos.2 hnreal)
      apply div_le_div_of_nonneg_left O.M3_nonneg hden
      gcongr
      exact O.variance_lower n p hp

/-- For [a cross-fitting family](hyp:F) satisfying [the oracle-score conditions — a bounded,
mean-zero oracle score with a uniform variance floor and third-moment bound](hyp:O),
[the standardized oracle sum converges to the standard Gaussian in Kolmogorov distance uniformly
over the possibly sample-size-dependent law class](goal). -/
theorem standardizedOracle_uniformGaussian
    {B vmin M3 : ℝ} (O : OracleConditions F B vmin M3) :
    F.UniformGaussian F.standardizedOracle := by
  have hv : 0 < Real.sqrt vmin := Real.sqrt_pos.2 O.vmin_pos
  have hrate : Tendsto
      (fun n : ℕ => ENNReal.ofReal
        (M3 / ((Real.sqrt vmin) ^ 3 * Real.sqrt (n : ℝ))))
      atTop (𝓝 0) := by
    have hroot : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hroot
    have hreal : Tendsto
        (fun n : ℕ => M3 / ((Real.sqrt vmin) ^ 3 * Real.sqrt (n : ℝ)))
        atTop (𝓝 0) := by
      convert hinv.const_mul (M3 / (Real.sqrt vmin) ^ 3) using 1
      · funext n
        rw [div_mul_eq_mul_div, div_eq_mul_inv]
        ring
      · simp
    simpa using ENNReal.tendsto_ofReal hreal
  rw [UniformGaussian]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    refine iSup_le fun p => iSup_le fun hp => iSup_le fun x => ?_
    exact ENNReal.ofReal_le_ofReal (F.oracle_berry_esseen O n hn p hp x)

end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference
