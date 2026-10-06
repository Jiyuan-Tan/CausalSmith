module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperJacksonOscillation
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperLogAbsorption
public import Mathlib.Probability.Moments.Variance

/-! # Independent-cell risk assembly

Roadmap equations (29)–(34) add the independent cell variances and square the
sum of their biases. The rate assembly below consumes cellwise estimates;
it does not assume the risk bound for the estimator.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators


-- @node: cellStatistic_sqRisk_eq_variance_add_bias
/-- Squared loss decomposes into variance and squared bias for an L² statistic. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hT), the [stated conclusion](goal) holds. -/
lemma cellStatistic_sqRisk_eq_variance_add_bias {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → ℝ) (t : ℝ)
    (hT : MemLp T 2 μ) :
    Causalean.Stat.sqRisk μ T t = variance T μ + ((∫ ω, T ω ∂μ) - t) ^ 2 := by
  have hInt := hT.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hCross : Integrable (fun ω => (2 * t) * T ω) μ := hInt.const_mul (2 * t)
  have hDiff : Integrable (fun ω => T ω ^ 2 - (2 * t) * T ω) μ :=
    hT.integrable_sq.sub hCross
  have he : (fun ω => (T ω - t) ^ 2) =
      (fun ω => T ω ^ 2 - (2 * t) * T ω + t ^ 2) := by
    funext ω
    ring
  unfold Causalean.Stat.sqRisk
  rw [he, integral_add hDiff (integrable_const (t ^ 2)),
    integral_sub hT.integrable_sq hCross, integral_const_mul,
    integral_const, probReal_univ, one_smul, variance_eq_sub hT]
  simp only [Pi.pow_apply]
  ring


-- @node: independentCell_sum_sqRisk_eq
/-- Independent cell variances add, while their biases add before squaring, as required in the passage to equation (29). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hT,hind), the [stated conclusion](goal) holds. -/
lemma independentCell_sum_sqRisk_eq {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ι → Ω → ℝ) (t : ι → ℝ)
    (hT : ∀ i, MemLp (T i) 2 μ) (hind : iIndepFun T μ) :
    Causalean.Stat.sqRisk μ (fun ω => ∑ i, T i ω) (∑ i, t i) =
      (∑ i, variance (T i) μ) + (∑ i, ((∫ ω, T i ω ∂μ) - t i)) ^ 2 := by
  have hsum : MemLp (fun ω => ∑ i, T i ω) 2 μ := by
    exact memLp_finsetSum Finset.univ (fun i _ => hT i)
  have hvar : variance (fun ω => ∑ i, T i ω) μ = ∑ i, variance (T i) μ := by
    have hfun : (∑ i, T i) = (fun ω => ∑ i, T i ω) := by funext ω; simp
    rw [← hfun]
    exact IndepFun.variance_sum (X := T) (s := Finset.univ)
      (fun i _ => hT i) (fun i _ j _ hij => hind.indepFun hij)
  rw [cellStatistic_sqRisk_eq_variance_add_bias μ _ _ hsum, hvar,
    integral_finsetSum _ (fun i _ => (hT i).integrable (by norm_num)),
    Finset.sum_sub_distrib]


-- @node: independentCell_sum_sqRisk_le
/-- Cellwise variance envelopes and absolute bias envelopes give a sum-risk bound. The squared bias is kept intact, avoiding a spurious factor of the alphabet size. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hT,hind,hv,hb), the [stated conclusion](goal) holds. -/
lemma independentCell_sum_sqRisk_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ι → Ω → ℝ) (t v b : ι → ℝ)
    (hT : ∀ i, MemLp (T i) 2 μ) (hind : iIndepFun T μ)
    (hv : ∀ i, variance (T i) μ ≤ v i)
    (hb : ∀ i, |(∫ ω, T i ω ∂μ) - t i| ≤ b i) :
    Causalean.Stat.sqRisk μ (fun ω => ∑ i, T i ω) (∑ i, t i) ≤
      (∑ i, v i) + (∑ i, b i) ^ 2 := by
  rw [independentCell_sum_sqRisk_eq μ T t hT hind]
  apply add_le_add (Finset.sum_le_sum fun i _ => hv i)
  have hab : |∑ i, ((∫ ω, T i ω ∂μ) - t i)| ≤ ∑ i, b i :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hb i)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2


-- @node: activeBranch_combined_bias_rate_le
/-- Equations (32)–(33) absorb the entire summed bias, including the clipping displacement. The only random-scale input is the cellwise pilot moment estimate (19). In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma activeBranch_combined_bias_rate_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (P : DiscreteLaw d) (S : Fin d → Ω → ℝ) (Cs Cb a : ℝ),
      0 ≤ Cs → 0 < a → (d : ℝ) ≤ 8 * a * logAlphabet d →
      (∀ x, Integrable (S x) μ) →
      (∀ x, Integrable (fun ω => (S x ω) ^ 2) μ) →
      (∀ x, (∫ ω, (S x ω) ^ 2 ∂μ) ≤
        Cs * (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) →
      (∑ x : Fin d, Cb * (Real.sqrt (cellMass P x / (a * logAlphabet d)) +
        1 / (a * logAlphabet d) + (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ ω, S x ω ∂μ))) ^ 2 ≤
        2 * Cb ^ 2 * (18 + Cs * A) * ((d : ℝ) / (a * logAlphabet d)) := by
  obtain ⟨A, hA, hclip⟩ := activeBranch_clipping_bias_rate_le
  refine ⟨A, hA, ?_⟩
  intro Ω _ μ _ d hd P S Cs Cb a hCs ha hactive hS hS₂ hmom
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hL := logAlphabet_pos hd
  have hR : (d : ℝ) / (a * logAlphabet d) ≤ 8 :=
    (div_le_iff₀ (mul_pos ha hL)).2 (by nlinarith)
  have hbase := activeBranch_total_bias_sq_le P (a * logAlphabet d) (mul_pos ha hL) hR
  have htail := hclip μ hd P S Cs a hCs ha hactive hS hS₂ hmom
  have hpow : ((d : ℝ) ^ (-(3 / 16 : ℝ))) ^ 2 = (d : ℝ) ^ (-(3 / 8 : ℝ)) := by
    rw [← Real.rpow_mul_natCast hd0.le]
    norm_num
  have hid : (∑ x : Fin d, Cb * (Real.sqrt (cellMass P x / (a * logAlphabet d)) +
      1 / (a * logAlphabet d) + (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ ω, S x ω ∂μ))) =
      Cb * (((∑ x : Fin d, Real.sqrt (cellMass P x / (a * logAlphabet d))) +
        (d : ℝ) / (a * logAlphabet d)) +
        (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∑ x : Fin d, ∫ ω, S x ω ∂μ)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hid, mul_pow]
  have htwo (u v : ℝ) : (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
    nlinarith [sq_nonneg (u - v)]
  calc
    _ ≤ Cb ^ 2 * (2 * (((∑ x : Fin d, Real.sqrt (cellMass P x / (a * logAlphabet d))) +
          (d : ℝ) / (a * logAlphabet d)) ^ 2) +
        2 * ((d : ℝ) ^ (-(3 / 16 : ℝ)) * (∑ x : Fin d, ∫ ω, S x ω ∂μ)) ^ 2) :=
      mul_le_mul_of_nonneg_left (htwo _ _) (sq_nonneg _)
    _ ≤ Cb ^ 2 * (2 * (18 * ((d : ℝ) / (a * logAlphabet d))) +
        2 * (Cs * A * ((d : ℝ) / (a * logAlphabet d)))) := by
      gcongr
      simpa only [mul_pow, hpow] using htail
    _ = _ := by ring


-- @node: activeBranch_independentCell_sqRisk_rate_le
/-- Equations (29)–(34): independent cell statistics obey the active-branch rate once their integrated variance and bias estimates and the pilot second moments have been proved. The constant is uniform in the alphabet and the intensity. These are intermediate cell estimates, not a premise asserting estimator risk. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hCs,hCv), the [stated conclusion](goal) holds. -/
lemma activeBranch_independentCell_sqRisk_rate_le (Cs Cv Cb : ℝ)
    (hCs : 0 ≤ Cs) (hCv : 0 ≤ Cv) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (P : DiscreteLaw d) (T S : Fin d → Ω → ℝ) (t : Fin d → ℝ) (a : ℝ),
      0 < a → (d : ℝ) ≤ 8 * a * logAlphabet d →
      (∀ x, MemLp (T x) 2 μ) → iIndepFun T μ →
      (∀ x, Integrable (S x) μ) →
      (∀ x, Integrable (fun ω => (S x ω) ^ 2) μ) →
      (∀ x, (∫ ω, (S x ω) ^ 2 ∂μ) ≤
        Cs * (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) →
      (∀ x, variance (T x) μ ≤
        Cv * (d : ℝ) ^ (1 / 16 : ℝ) * (∫ ω, (S x ω) ^ 2 ∂μ)) →
      (∀ x, |(∫ ω, T x ω ∂μ) - t x| ≤
        Cb * (Real.sqrt (cellMass P x / (a * logAlphabet d)) +
          1 / (a * logAlphabet d) + (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ ω, S x ω ∂μ))) →
      Causalean.Stat.sqRisk μ (fun ω => ∑ x, T x ω) (∑ x, t x) ≤
        C * ((d : ℝ) / (a * logAlphabet d)) := by
  obtain ⟨Av, hAv, hvariance⟩ := activeBranch_variance_scale_rate_le
  obtain ⟨Ab, hAb, hbias⟩ := activeBranch_combined_bias_rate_le
  let C := Cv * Cs * Av + 2 * Cb ^ 2 * (18 + Cs * Ab) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ d hd P T S t a ha hactive hT hind hS hS₂ hmom hv hb
  have hR : 0 ≤ (d : ℝ) / (a * logAlphabet d) :=
    div_nonneg (Nat.cast_nonneg _) (mul_pos ha (logAlphabet_pos hd)).le
  have hvs := hvariance hd P (fun x => ∫ ω, (S x ω) ^ 2 ∂μ)
    Cs a hCs ha hactive hmom
  have hbs := hbias μ hd P S Cs Cb a hCs ha hactive hS hS₂ hmom
  have hsum := independentCell_sum_sqRisk_le μ T t
    (fun x => Cv * (d : ℝ) ^ (1 / 16 : ℝ) * (∫ ω, (S x ω) ^ 2 ∂μ))
    (fun x => Cb * (Real.sqrt (cellMass P x / (a * logAlphabet d)) +
      1 / (a * logAlphabet d) + (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ ω, S x ω ∂μ)))
    hT hind hv hb
  rw [← Finset.mul_sum] at hsum
  have hvs' := mul_le_mul_of_nonneg_left hvs hCv
  dsimp [C]
  nlinarith

/-- Projection to the unit interval is continuous, including at both endpoints. The [stated conclusion](goal) holds. -/
-- @node: projectUnit_continuous
@[fun_prop] lemma projectUnit_continuous : Continuous projectUnit := by
  unfold projectUnit
  fun_prop


-- @node: projectUnit_sqRisk_le
/-- The final projection in equation (34) preserves any risk bound assembled for the unprojected sum. Its squared-loss integrability follows from the original L² statistic and pointwise contraction, so no extra regularity premise is needed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hT,ht), the [stated conclusion](goal) holds. -/
lemma projectUnit_sqRisk_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → ℝ) (t : ℝ)
    (hT : MemLp T 2 μ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.sqRisk μ (fun ω => projectUnit (T ω)) t ≤
      Causalean.Stat.sqRisk μ T t := by
  have hc : Continuous (fun z : ℝ => (projectUnit z - t) ^ 2) := by
    fun_prop
  have hs : AEStronglyMeasurable (fun ω => (projectUnit (T ω) - t) ^ 2) μ :=
    hc.comp_aestronglyMeasurable hT.aestronglyMeasurable
  have hraw : Integrable (fun ω => (T ω - t) ^ 2) μ :=
    (hT.sub (memLp_const t)).integrable_sq
  have hproj : Integrable (fun ω => (projectUnit (T ω) - t) ^ 2) μ :=
    hraw.mono' hs (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact projectUnit_sq_error_le ht)
  exact integral_mono hproj hraw (fun ω => projectUnit_sq_error_le ht)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
