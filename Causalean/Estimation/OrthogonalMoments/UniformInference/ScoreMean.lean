module
public import Causalean.Estimation.OrthogonalMoments.UniformInference.FoldRates
public import Causalean.Estimation.OrthogonalMoments.UniformInference.OracleNormal
public import Causalean.Stat.Concentration.TailBounds.Hoeffding

/-! # Uniform cross-fitted score mean

The mean-zero oracle score and foldwise approximation rates imply that
the empirical held-out score mean vanishes uniformly in probability.
-/

public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped ENNReal

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

namespace Family

/-- For [a cross-fitting family](hyp:F) satisfying [the foldwise rate conditions on score
approximation and drift](hyp:R) and [the oracle-score conditions, including a mean-zero oracle
score](hyp:O), [the empirical mean of the held-out estimated scores vanishes in probability
uniformly over the law class](goal). -/
theorem scoreMean_uniformOP
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    {B vmin M3 : ℝ}
    (R : RateConditions F r a b C δ) (O : OracleConditions F B vmin M3) :
    F.UniformOP F.scoreMean := by
  have hOracle : F.UniformOP (fun n p ω =>
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        F.oracle p ((F.sample p).Z i ω)) := by
    intro ε hε
    let b : ℝ := 2 * B + 1
    have hb : 0 < b := by dsimp [b]; linarith [O.B_nonneg]
    have hrate : Tendsto (fun n : ℕ =>
        ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * ε ^ 2 / b ^ 2)))
        atTop (𝓝 0) := by
      have hc : 0 < 2 * ε ^ 2 / b ^ 2 := by positivity
      have ht : Tendsto (fun n : ℕ => (n : ℝ) * (2 * ε ^ 2 / b ^ 2))
          atTop atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hc
      have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul 2
      have hr (n : ℕ) :
          -2 * (n : ℝ) * ε ^ 2 / b ^ 2 =
            -((n : ℝ) * (2 * ε ^ 2 / b ^ 2)) := by ring
      have hreal : Tendsto (fun n : ℕ =>
          2 * Real.exp (-2 * (n : ℝ) * ε ^ 2 / b ^ 2)) atTop (𝓝 0) := by
        simpa only [Function.comp_apply, hr, mul_zero] using he
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal
    rw [ENNReal.tendsto_nhds_zero]
    intro ζ hζ
    have he := (ENNReal.tendsto_nhds_zero.mp hrate) ζ hζ
    filter_upwards [eventually_gt_atTop (0 : ℕ), he] with n hn htail
    apply le_trans _ htail
    refine iSup_le fun p => iSup_le fun hp => ?_
    haveI : IsProbabilityMeasure (F.sampleLaw p) :=
      (F.sample p).indep.isProbabilityMeasure
    haveI : IsProbabilityMeasure (F.laws p) := by
      rw [← (F.sample p).law]
      exact Measure.isProbabilityMeasure_map ((F.sample p).meas 0).aemeasurable
    have hbound : ∀ᵐ z ∂F.laws p,
        F.oracle p z ∈ Set.Icc (-B) (B + 1) := by
      filter_upwards with z
      have hz := O.bounded n p hp z
      constructor <;> linarith [neg_abs_le (F.oracle p z), le_abs_self (F.oracle p z)]
    have hh := Causalean.Stat.Concentration.hoeffding_abs_ge
      (F.sample p) (O.measurable p) (a := -B) (b := B + 1)
      (by linarith [O.B_nonneg]) hbound n hn hε.le
    have heq : ∀ ω,
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          F.oracle p ((F.sample p).Z i ω) =
        (F.sample p).sampleMean (F.oracle p) n ω -
          ∫ z, F.oracle p z ∂F.laws p := by
      intro ω
      simp only [IIDSample.sampleMean, O.mean_zero n p hp, sub_zero]
    have htail' : (F.sampleLaw p).real
        {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          F.oracle p ((F.sample p).Z i ω)|} ≤
        2 * Real.exp (-2 * (n : ℝ) * ε ^ 2 / b ^ 2) := by
      convert hh using 1 <;> simp only [heq, b] <;> ring
    have hfinite : F.sampleLaw p
        {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          F.oracle p ((F.sample p).Z i ω)|} ≠ ⊤ := by
      exact ne_top_of_le_ne_top (by simp)
        (measure_mono (Set.subset_univ _))
    exact (ENNReal.ofReal_toReal hfinite).symm ▸
      ENNReal.ofReal_le_ofReal htail'
  have hLinear := F.uniform_asymptotic_linearity R
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  have hsum : Tendsto (fun n =>
      (⨆ (p : ι) (_hp : p ∈ F.lawClass n),
        F.sampleLaw p {ω | ε / 2 ≤
          |Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) -
            F.oracleSum n p ω|}) +
      (⨆ (p : ι) (_hp : p ∈ F.lawClass n),
        F.sampleLaw p {ω | ε / 2 ≤
          |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            F.oracle p ((F.sample p).Z i ω)|})) atTop (𝓝 0) := by
    convert (hLinear (ε / 2) hhalf).add (hOracle (ε / 2) hhalf) using 1 <;> simp
  rw [ENNReal.tendsto_nhds_zero] at hsum ⊢
  intro ζ hζ
  filter_upwards [hsum ζ hζ, eventually_gt_atTop (0 : ℕ)] with n htail hn
  apply le_trans _ htail
  refine iSup_le fun p => iSup_le fun hp => ?_
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by
    exact (Real.one_le_sqrt).2 (by exact_mod_cast hn)
  have hscale : (fun ω => (Real.sqrt (n : ℝ))⁻¹ * F.oracleSum n p ω) =
      fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        F.oracle p ((F.sample p).Z i ω) := by
    funext ω
    simp only [oracleSum]
    have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    calc
      (Real.sqrt (n : ℝ))⁻¹ *
          ((Real.sqrt (n : ℝ))⁻¹ *
            ∑ i ∈ Finset.range n, F.oracle p ((F.sample p).Z i ω)) =
          ((Real.sqrt (n : ℝ))⁻¹ ^ 2) *
            ∑ i ∈ Finset.range n, F.oracle p ((F.sample p).Z i ω) := by ring
      _ = _ := by rw [inv_pow, hsq]
  have hpoint (ω : Ω) :
      ε ≤ |F.scoreMean n p ω| →
      ε / 2 ≤ |Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) -
          F.oracleSum n p ω| ∨
      ε / 2 ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          F.oracle p ((F.sample p).Z i ω)| := by
    intro hω
    have hid : F.scoreMean n p ω =
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) -
            F.oracleSum n p ω) +
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          F.oracle p ((F.sample p).Z i ω) := by
      have he : F.estimate n p ω - F.target p = F.scoreMean n p ω := by
        simp [estimate, scoreMean]
      rw [← congrFun hscale ω, ← he]
      have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hsqrt)
      field_simp
      ring
    rw [hid] at hω
    have hi : (Real.sqrt (n : ℝ))⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 hsqrt
    have hi0 : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := by positivity
    have ht := abs_add_le
      ((Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) - F.oracleSum n p ω))
      ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        F.oracle p ((F.sample p).Z i ω))
    rw [abs_mul, abs_of_nonneg hi0] at ht
    have hbnd := mul_le_mul_of_nonneg_right hi
      (abs_nonneg (Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) - F.oracleSum n p ω))
    by_contra hh
    push_neg at hh
    nlinarith
  have hfirst : F.sampleLaw p {ω | ε / 2 ≤
      |Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) -
        F.oracleSum n p ω|} ≤
      ⨆ (q : ι) (_hq : q ∈ F.lawClass n),
        F.sampleLaw q {ω | ε / 2 ≤
          |Real.sqrt (n : ℝ) * (F.estimate n q ω - F.target q) -
            F.oracleSum n q ω|} :=
    le_iSup_of_le p (le_iSup_of_le hp le_rfl)
  have hsecond : F.sampleLaw p {ω | ε / 2 ≤
      |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        F.oracle p ((F.sample p).Z i ω)|} ≤
      ⨆ (q : ι) (_hq : q ∈ F.lawClass n),
        F.sampleLaw q {ω | ε / 2 ≤
          |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            F.oracle q ((F.sample q).Z i ω)|} :=
    le_iSup_of_le p (le_iSup_of_le hp le_rfl)
  calc
    F.sampleLaw p {ω | ε ≤ |F.scoreMean n p ω|} ≤
        F.sampleLaw p
          ({ω | ε / 2 ≤ |Real.sqrt (n : ℝ) *
            (F.estimate n p ω - F.target p) - F.oracleSum n p ω|} ∪
           {ω | ε / 2 ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
             F.oracle p ((F.sample p).Z i ω)|}) :=
        measure_mono (fun ω hω => hpoint ω hω)
    _ ≤ F.sampleLaw p {ω | ε / 2 ≤ |Real.sqrt (n : ℝ) *
              (F.estimate n p ω - F.target p) - F.oracleSum n p ω|} +
            F.sampleLaw p {ω | ε / 2 ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
              F.oracle p ((F.sample p).Z i ω)|} := measure_union_le _ _
    _ ≤ _ := add_le_add hfirst hsecond


end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference
