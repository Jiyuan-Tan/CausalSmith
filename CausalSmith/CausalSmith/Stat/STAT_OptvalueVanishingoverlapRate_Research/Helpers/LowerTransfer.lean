module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerDense
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperEmpiricalRatio
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.TIdentification
public import Causalean.Mathlib.Probability.Poisson.FinitePartition
public import Causalean.Stat.Concentration.Poisson.SelfNormalized.Chernoff

/-! # Lower Transfer scaffold

Identification and causal completion preserve the attained risks, their
worst-case supremum, and the all-estimator minimax value. The remaining
Poisson shortage estimate in roadmap (49) is proved uniformly over the sparse
normalizer. Projection and the first-label risk transfer below implement the loss comparison
after (49); constructing the label map from the count experiment remains open. -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open scoped NNReal


-- @node: causalRisk_eq_observedRisk
/-- Identification makes the causal risk equal the risk at the observed margin. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhalf), the [stated conclusion](goal) holds. -/
lemma causalRisk_eq_observedRisk {n d : ℕ} {ε : ℝ}
    (hd : 2 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (est : Estimator n d) (Q : CausalModelLaw d ε) :
    causalRisk n est Q =
      observedRisk n est ⟨observedMarginal Q.1, ⟨Q.2.overlap⟩⟩ := by
  unfold causalRisk observedRisk
  rw [identification.2.1 d ε Q.1 hd hε hεhalf Q.2]


-- @node: causalRisk_range_eq_observedRisk_range
/-- Every risk attained in either model class is attained in the other: observed margins give one inclusion and causal completion gives the reverse. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhalf), the [stated conclusion](goal) holds. -/
lemma causalRisk_range_eq_observedRisk_range {n d : ℕ} {ε : ℝ}
    (hd : 2 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (est : Estimator n d) :
    Set.range (causalRisk n (ε := ε) est) =
      Set.range (observedRisk n (ε := ε) est) := by
  ext r
  constructor
  · rintro ⟨Q, rfl⟩
    exact ⟨⟨observedMarginal Q.1, ⟨Q.2.overlap⟩⟩,
      (causalRisk_eq_observedRisk hd hε hεhalf est Q).symm⟩
  · rintro ⟨P, rfl⟩
    obtain ⟨Q, hQ, hmargin⟩ := identification.1 d ε P.1 hd hε hεhalf P.2
    refine ⟨⟨Q, hQ⟩, ?_⟩
    rw [causalRisk_eq_observedRisk hd hε hεhalf]
    change Causalean.Stat.sqRisk (productLaw (observedMarginal Q) n) est.1
      (observedValue (observedMarginal Q)) =
      Causalean.Stat.sqRisk (productLaw P.1 n) est.1 (observedValue P.1)
    rw [hmargin]


-- @node: causalWorstRisk_eq_observedWorstRisk
/-- Each estimator has the same worst-case risk for the observed and causal targets. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhalf), the [stated conclusion](goal) holds. -/
lemma causalWorstRisk_eq_observedWorstRisk {n d : ℕ} {ε : ℝ}
    (hd : 2 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (est : Estimator n d) :
    Causalean.Stat.worstCaseRiskReal (causalRisk n (ε := ε)) est =
      Causalean.Stat.worstCaseRiskReal (observedRisk n (ε := ε)) est := by
  rw [Causalean.Stat.worstCaseRisk_eq_sSup_range,
    Causalean.Stat.worstCaseRisk_eq_sSup_range,
    causalRisk_range_eq_observedRisk_range hd hε hεhalf est]

/-- Identification and completion preserve the armwise estimator's worst-case risk. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀,hd,hε,hεhalf), the [stated conclusion](goal) holds. -/
lemma causalArmwiseWorstRisk_eq_armwiseWorstRisk (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    (n d : ℕ) (ε : ℝ) (hd : 2 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    causalArmwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε =
      armwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε := by
  exact causalWorstRisk_eq_observedWorstRisk hd hε hεhalf
    (armwiseEstimatorWitness H₀ κ D₀ hH₀ hκ hD₀ n d ε)


-- @node: causalMinimaxRisk_eq_minimaxRisk
/-- Taking the infimum over the shared estimator class preserves the exact risk equality. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhalf), the [stated conclusion](goal) holds. -/
lemma causalMinimaxRisk_eq_minimaxRisk {n d : ℕ} {ε : ℝ}
    (hd : 2 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    causalMinimaxRisk n d ε = minimaxRisk n d ε := by
  unfold causalMinimaxRisk minimaxRisk Causalean.Stat.minimaxValueReal
  congr 1
  funext est
  exact causalWorstRisk_eq_observedWorstRisk hd hε hεhalf est


-- @node: causalMinimaxRisk_bounds_of_observed
/-- A two-sided observed minimax bound transfers unchanged to the causal target. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhalf,hlower,hupper), the [stated conclusion](goal) holds. -/
lemma causalMinimaxRisk_bounds_of_observed {n d : ℕ} {ε c C : ℝ}
    (hd : 2 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hlower : c * rateScale n d ε ≤ minimaxRisk n d ε)
    (hupper : minimaxRisk n d ε ≤ C * rateScale n d ε) :
    c * rateScale n d ε ≤ causalMinimaxRisk n d ε ∧
      causalMinimaxRisk n d ε ≤ C * rateScale n d ε := by
  rw [causalMinimaxRisk_eq_minimaxRisk hd hε hεhalf]
  exact ⟨hlower, hupper⟩


-- @node: observedRisk_nonneg
/-- Squared observed risk is nonnegative for every estimator and observed law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma observedRisk_nonneg {n d : ℕ} {ε : ℝ}
    (est : Estimator n d) (P : ModelLaw d ε) :
    0 ≤ observedRisk n est P := by
  exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _


-- @node: minimaxRisk_le_armwiseWorstRisk
/-- The admissible deterministic armwise estimator upper-bounds the minimax infimum. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀), the [stated conclusion](goal) holds. -/
lemma minimaxRisk_le_armwiseWorstRisk (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    (n d : ℕ) (ε : ℝ) :
    minimaxRisk n d ε ≤ armwiseWorstRisk H₀ κ D₀ hH₀ hκ hD₀ n d ε := by
  exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    (fun est P => observedRisk_nonneg est P)
    (armwiseEstimatorWitness H₀ κ D₀ hH₀ hκ hD₀ n d ε)



-- @node: poisson_shortage_prob_le
/-- The lower Gaussian Poisson tail gives the exact shortage exponent before uniformizing over the normalizer in roadmap (49). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:lam,hlam), the [stated conclusion](goal) holds. -/
lemma poisson_shortage_prob_le (lam : ℝ≥0) (n : ℕ)
    (hlam : (n : ℝ) < lam) :
    (poissonMeasure lam).real {k : ℕ | k < n} ≤
      Real.exp (-((lam : ℝ) - n) ^ 2 / (2 * lam)) := by
  have hlampos : 0 < (lam : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg n) hlam
  have hs : 0 ≤ (lam : ℝ) - n := by linarith
  have hsqrt : Real.sqrt (2 * (lam : ℝ) * (((lam : ℝ) - n) ^ 2 / (2 * lam))) =
      (lam : ℝ) - n := by
    rw [mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) hlampos)),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
  have hsub : {k : ℕ | k < n} ⊆
      {k : ℕ | (lam : ℝ) - k >
        Real.sqrt (2 * (lam : ℝ) * (((lam : ℝ) - n) ^ 2 / (2 * lam)))} := by
    intro k hk
    change (lam : ℝ) - (k : ℝ) > _
    rw [hsqrt]
    have hkR : (k : ℝ) < n := by exact_mod_cast hk
    linarith
  have ht := Causalean.Stat.Concentration.PoissonSelfNormalized.poisson_lower_bernstein lam
    (z := ((lam : ℝ) - n) ^ 2 / (2 * lam)) (by positivity)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans ht)
  simpa only [Measure.real_def, ENNReal.toReal_ofReal (Real.exp_nonneg _), neg_div] using h


-- @node: shortage_exponent_ge
/-- The shortage exponent increases above n. Evaluating it at Bn/2 gives exactly the exponent in roadmap (49). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hr,hB,hlam), the [stated conclusion](goal) holds. -/
lemma shortage_exponent_ge {lam B r : ℝ} (hr : 0 < r) (hB : 2 < B)
    (hlam : B * r / 2 ≤ lam) :
    r * (B - 2) ^ 2 / (4 * B) ≤ (lam - r) ^ 2 / (2 * lam) := by
  have hBpos : 0 < B := by linarith
  have ha : 0 < B * r / 2 := by positivity
  have hlampos : 0 < lam := ha.trans_le hlam
  have hmono : (B * r / 2 - r) ^ 2 / (2 * (B * r / 2)) ≤
      (lam - r) ^ 2 / (2 * lam) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hprod : 0 ≤ (lam - B * r / 2) * (lam * (B * r / 2) - r ^ 2) := by
      apply mul_nonneg (by linarith)
      have hfirst := mul_le_mul_of_nonneg_right hlam ha.le
      have hbase : r ≤ B * r / 2 := by nlinarith
      have hsq := pow_le_pow_left₀ hr.le hbase 2
      nlinarith
    nlinarith
  calc
    _ = (B * r / 2 - r) ^ 2 / (2 * (B * r / 2)) := by field_simp; ring
    _ ≤ _ := hmono


-- @node: poisson_shortage_uniform_le
/-- Any Poisson experiment with total mean at least Bn/2 satisfies the uniform shortage probability in roadmap (49). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:lam,hn,hB,hlam), the [stated conclusion](goal) holds. -/
lemma poisson_shortage_uniform_le (lam : ℝ≥0) {n : ℕ} {B : ℝ}
    (hn : 1 ≤ n) (hB : 2 < B) (hlam : B * (n : ℝ) / 2 ≤ lam) :
    (poissonMeasure lam).real {k : ℕ | k < n} ≤
      Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlamn : (n : ℝ) < lam := by nlinarith
  apply (poisson_shortage_prob_le lam n hlamn).trans
  apply Real.exp_le_exp.mpr
  have he := neg_le_neg (shortage_exponent_ge hnpos hB hlam)
  simpa only [neg_div, neg_mul] using he

/-- The sparse normalizer is at least one half, so the conditional total count of every legal sparse experiment obeys the same shortage bound. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hε,hεhalf,hB,hz,lam,hmean), the [stated conclusion](goal) holds. -/
lemma sparse_poisson_shortage_le {n d : ℕ} {ε M B : ℝ}
    (hn : 1 ≤ n) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) (hB : 2 < B)
    (z : Fin d → ℝ) (hz : ∀ x, z x ∈ Set.Icc 0 M)
    (lam : ℝ≥0) (hmean : (lam : ℝ) = B * n * sparseNormalizerFormula d ε M z hz) :
    (poissonMeasure lam).real {k : ℕ | k < n} ≤
      Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) := by
  apply poisson_shortage_uniform_le lam hn hB
  rw [hmean]
  have hs := mul_le_mul_of_nonneg_left (sparseNormalizer_ge_half hε hεhalf z hz)
    (show 0 ≤ B * (n : ℝ) by positivity)
  nlinarith



-- @node: poissonCount_shortage_uniform_le
/-- The uniform shortage estimate applies to a count on any probability space once its conditional Poisson law has been established. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:lam,hN,hn,hB,hmean), the [stated conclusion](goal) holds. -/
lemma poissonCount_shortage_uniform_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Ω → ℕ) (lam : ℝ≥0)
    (hN : HasLaw N (poissonMeasure lam) μ) {n : ℕ} {B : ℝ}
    (hn : 1 ≤ n) (hB : 2 < B) (hmean : B * (n : ℝ) / 2 ≤ lam) :
    μ.real {ω | N ω < n} ≤
      Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) := by
  rw [hN.measureReal_eq (show MeasurableSet {k : ℕ | k < n} from measurableSet_Iio)]
  exact poisson_shortage_uniform_le lam hn hB hmean


-- @node: shortageExponential_le_inverse_sample
/-- Exponential shortage can be made an arbitrarily small inverse-sample penalty by increasing its positive exponent coefficient. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hδ,hcoef), the [stated conclusion](goal) holds. -/
lemma shortageExponential_le_inverse_sample {a δ : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hδ : 0 < δ) (hcoef : 1 / δ ≤ a) :
    Real.exp (-a * (n : ℝ)) ≤ δ / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hexp : a * (n : ℝ) * Real.exp (-(a * n)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one (a * n)).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hδa : 1 ≤ δ * a := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hcoef
  have hb := mul_le_mul_of_nonneg_left hexp hδ.le
  have hsmall : (n : ℝ) * Real.exp (-(a * n)) ≤ δ := by
    have hm := mul_le_mul_of_nonneg_right hδa
      (show 0 ≤ (n : ℝ) * Real.exp (-(a * n)) by positivity)
    nlinarith
  apply (le_div_iff₀ hnpos).2
  rw [neg_mul, mul_comm]
  exact hsmall


-- @node: shortage_inflation_exists
/-- A single universal inflation B makes the shortage penalty smaller than any specified positive multiple of 1/n, uniformly over all sample sizes. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hδ), the [stated conclusion](goal) holds. -/
lemma shortage_inflation_exists {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 2 < B ∧ ∀ n : ℕ, 1 ≤ n →
      Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) ≤ δ / n := by
  let B : ℝ := 4 * (1 / δ + 2)
  have hq : 0 < 1 / δ := by positivity
  have hB : 2 < B := by dsimp [B]; linarith
  have hBpos : 0 < B := by linarith
  have hcoef : 1 / δ ≤ (B - 2) ^ 2 / (4 * B) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * B)).2
    have he : B = 4 * (1 / δ + 2) := rfl
    nlinarith
  refine ⟨B, hB, fun n hn => ?_⟩
  have ht := shortageExponential_le_inverse_sample hn hδ hcoef
  convert ht using 1
  congr 1
  ring


-- @node: observedRisk_projectUnit_le
/-- Every finite observed estimator can be projected without increasing its risk. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma observedRisk_projectUnit_le {n d : ℕ} {ε : ℝ}
    (est : Estimator n d) (P : ModelLaw d ε) :
    Causalean.Stat.sqRisk (productLaw P.1 n) (fun o => projectUnit (est.1 o))
      (observedValue P.1) ≤ observedRisk n est P := by
  let : IsProbabilityMeasure (productLaw P.1 n) := by
    unfold productLaw
    infer_instance
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro o
  exact projectUnit_sq_error_le (observedValue_mem_unitInterval P.1)


-- @node: firstLabels_shortage_sqRisk_le
/-- Use the first n labels on a sufficiently large count and zero on shortage. If the label block has the fixed-sample law, projection and an indicator bound transfer its risk with at most the shortage probability as an additive penalty. The label block may include unobserved continuation labels on shortage; the transferred statistic uses none of them there. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN,hX), the [stated conclusion](goal) holds. -/
lemma firstLabels_shortage_sqRisk_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n d : ℕ} {ε : ℝ}
    (P : ModelLaw d ε) (est : Estimator n d) (N : Ω → ℕ) (hN : Measurable N)
    (X : Ω → (Fin n → Obs d)) (hX : HasLaw X (productLaw P.1 n) μ) :
    Causalean.Stat.sqRisk μ
      (fun ω => if N ω < n then 0 else projectUnit (est.1 (X ω)))
      (observedValue P.1) ≤ observedRisk n est P + μ.real {ω | N ω < n} := by
  classical
  let loss : (Fin n → Obs d) → ℝ := fun o => (est.1 o - observedValue P.1) ^ 2
  have hloss : AEStronglyMeasurable loss (productLaw P.1 n) := by fun_prop
  have hsource : Integrable loss (Measure.map X μ) := by
    rw [hX.map_eq]
    let : IsProbabilityMeasure (productLaw P.1 n) := by
      unfold productLaw
      infer_instance
    exact Integrable.of_finite
  have hcomp : Integrable (fun ω => loss (X ω)) μ :=
    hsource.comp_aemeasurable hX.aemeasurable
  have hs : MeasurableSet {ω | N ω < n} := hN measurableSet_Iio
  have hi : Integrable ({ω | N ω < n}.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hs
  have ht := observedValue_mem_unitInterval P.1
  have hpoint (ω : Ω) :
      ((if N ω < n then 0 else projectUnit (est.1 (X ω))) - observedValue P.1) ^ 2 ≤
        loss (X ω) + {ω | N ω < n}.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases hshort : N ω < n
    · simp only [Set.indicator, Set.mem_ofPred_eq, hshort, ↓reduceIte, zero_sub, neg_sq]
      have hsq : (observedValue P.1) ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      exact hsq.trans (le_add_of_nonneg_left (sq_nonneg _))
    · simp only [Set.indicator, Set.mem_ofPred_eq, hshort, ↓reduceIte, add_zero]
      exact projectUnit_sq_error_le ht
  have hmeas : AEStronglyMeasurable
      (fun ω => ((if N ω < n then 0 else projectUnit (est.1 (X ω))) -
        observedValue P.1) ^ 2) μ := by
    have hv : AEStronglyMeasurable (fun ω => projectUnit (est.1 (X ω))) μ := by
      have hm : Measurable (fun o : Fin n → Obs d => projectUnit (est.1 o)) := by
        unfold projectUnit
        fun_prop
      exact (hm.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
    have he : AEStronglyMeasurable
        (fun ω => if N ω < n then 0 else projectUnit (est.1 (X ω))) μ := by
      apply (AEStronglyMeasurable.piecewise hs
        (aestronglyMeasurable_const (b := (0 : ℝ))) hv.restrict).congr
      exact Filter.Eventually.of_forall fun ω => by
        by_cases h : N ω < n <;> simp [Set.piecewise, h]
    fun_prop
  have hint : Integrable
      (fun ω => ((if N ω < n then 0 else projectUnit (est.1 (X ω))) -
        observedValue P.1) ^ 2) μ := by
    apply (hcomp.add hi).mono' hmeas
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint ω
  unfold Causalean.Stat.sqRisk
  calc
    _ ≤ ∫ ω, (loss (X ω) + {ω | N ω < n}.indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
      integral_mono hint (hcomp.add hi) hpoint
    _ = observedRisk n est P + μ.real {ω | N ω < n} := by
      rw [integral_add hcomp hi, integral_indicator_const 1 hs]
      rw [show (∫ ω, loss (X ω) ∂μ) = ∫ o, loss o ∂productLaw P.1 n from
        hX.integral_comp hloss]
      simp only [smul_eq_mul, mul_one]
      rfl


-- @node: firstLabels_poisson_sqRisk_le
/-- Combining the first-label transfer with (49) gives the uniform Poisson penalty used in both the sparse and dense lower experiments. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN,hX,lam,hlaw,hn,hB,hmean), the [stated conclusion](goal) holds. -/
lemma firstLabels_poisson_sqRisk_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n d : ℕ} {ε B : ℝ}
    (P : ModelLaw d ε) (est : Estimator n d) (N : Ω → ℕ) (hN : Measurable N)
    (X : Ω → (Fin n → Obs d)) (hX : HasLaw X (productLaw P.1 n) μ)
    (lam : ℝ≥0) (hlaw : HasLaw N (poissonMeasure lam) μ)
    (hn : 1 ≤ n) (hB : 2 < B) (hmean : B * (n : ℝ) / 2 ≤ lam) :
    Causalean.Stat.sqRisk μ
      (fun ω => if N ω < n then 0 else projectUnit (est.1 (X ω)))
      (observedValue P.1) ≤ observedRisk n est P +
        Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) := by
  exact (firstLabels_shortage_sqRisk_le μ P est N hN X hX).trans
    (add_le_add_right (poissonCount_shortage_uniform_le μ N lam hlaw hn hB hmean) _)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
