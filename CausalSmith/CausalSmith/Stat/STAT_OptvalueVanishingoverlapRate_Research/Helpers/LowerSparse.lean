module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketKinkSeparation
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.SparseFamily
public import Causalean.Stat.Minimax.Mixture.MomentMatched.SupportLocalized

/-! # Sparse target normalization

Pointwise envelope and normalization bounds used in equations (37)--(39)
of the weighted-separation proof roadmap. -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators

/-- The positive-part functional is nonnegative and bounded by its cell normalizer. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hεhalf,hz), the [stated conclusion](goal) holds. -/
lemma phiEps_nonneg_le_weight {ε z : ℝ} (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hz : 0 ≤ z) : 0 ≤ phiEpsFormula ε z ∧ phiEpsFormula ε z ≤ 1 - ε + ε * z := by
  have hbase : 0 ≤ 1 - ε := by linarith
  have hw : 0 ≤ 1 - ε + ε * z := add_nonneg hbase (mul_nonneg hε hz)
  have hd : 0 < 1 + z := by linarith
  have hp : max (z - 1) 0 ≤ 1 + z := max_le (by linarith) (by linarith)
  constructor
  · unfold phiEpsFormula
    exact div_nonneg (mul_nonneg hw (le_max_right _ _)) hd.le
  · unfold phiEpsFormula
    apply (div_le_iff₀ hd).2
    exact mul_le_mul_of_nonneg_left hp hw


-- @node: sparse_intensity_sq_le
/-- A bounded nonnegative intensity has second moment scale at most M times its mean. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hz), the [stated conclusion](goal) holds. -/
lemma sparse_intensity_sq_le {M z : ℝ} (hz : z ∈ Set.Icc 0 M) :
    z ^ 2 ≤ M * z := by
  have h := mul_le_mul_of_nonneg_right hz.2 hz.1
  nlinarith

/-- The scalar envelope gives the second-moment scale in roadmap equation (37). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hεhalf,hz), the [stated conclusion](goal) holds. -/
lemma phiEps_sq_le {ε M z : ℝ} (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hz : z ∈ Set.Icc 0 M) :
    (phiEpsFormula ε z) ^ 2 ≤ 2 * (1 + ε ^ 2 * M * z) := by
  obtain ⟨hlo, hhi⟩ := phiEps_nonneg_le_weight hε hεhalf hz.1
  have hsq : (phiEpsFormula ε z) ^ 2 ≤ (1 - ε + ε * z) ^ 2 := by
    nlinarith
  have hi := sparse_intensity_sq_le hz
  have hscaled := mul_le_mul_of_nonneg_left hi (sq_nonneg ε)
  have hbase : (1 - ε) ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (1 - ε - ε * z)]

/-- The sparse denominator stays above one half throughout the closed overlap range. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hεhalf,hz), the [stated conclusion](goal) holds. -/
lemma sparseNormalizer_ge_half {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hεhalf : ε ≤ 1 / 2) (z : Fin d → ℝ) (hz : ∀ x, z x ∈ Set.Icc 0 M) :
    1 / 2 ≤ sparseNormalizerFormula d ε M z hz := by
  have hs : 0 ≤ ∑ x : Fin d, z x := Finset.sum_nonneg (fun x _ => (hz x).1)
  have ht : 0 ≤ ε / (d : ℝ) * ∑ x : Fin d, z x := by positivity
  unfold sparseNormalizerFormula
  linarith

/-- The empirical average of the scalar functional is between zero and S_d. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhalf,hz), the [stated conclusion](goal) holds. -/
lemma sparse_average_phi_bounds {d : ℕ} (hd : 0 < d) {ε M : ℝ}
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (z : Fin d → ℝ) (hz : ∀ x, z x ∈ Set.Icc 0 M) :
    0 ≤ (∑ x : Fin d, phiEpsFormula ε (z x)) / d ∧
      (∑ x : Fin d, phiEpsFormula ε (z x)) / d ≤ sparseNormalizerFormula d ε M z hz := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hb (x : Fin d) := phiEps_nonneg_le_weight hε hεhalf (hz x).1
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun x _ => (hb x).1)) hdR.le
  · apply (div_le_iff₀ hdR).2
    calc
      _ ≤ ∑ x : Fin d, (1 - ε + ε * z x) :=
        Finset.sum_le_sum (fun x _ => (hb x).2)
      _ = sparseNormalizerFormula d ε M z hz * d := by
        simp [sparseNormalizerFormula, Finset.sum_add_distrib, ← Finset.mul_sum]
        field_simp


-- @node: sparse_ratio_normalization_le
/-- Normalization perturbs H_d by at most the denominator error, as in equation (38). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hS,hH,hHS), the [stated conclusion](goal) holds. -/
lemma sparse_ratio_normalization_le {H S : ℝ} (hS : 0 < S)
    (hH : 0 ≤ H) (hHS : H ≤ S) : |H / S - H| ≤ |1 - S| := by
  have hq : 0 ≤ H / S := div_nonneg hH hS.le
  have hq1 : H / S ≤ 1 := (div_le_one hS).2 hHS
  have hid : H / S - H = (H / S) * (1 - S) := by field_simp
  rw [hid, abs_mul, abs_of_nonneg hq]
  simpa using mul_le_mul_of_nonneg_right hq1 (abs_nonneg (1 - S))


-- @node: sparse_target_center_sq_le
/-- The normalized target is close to a deterministic prior center by two errors. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hS,hH,hHS), the [stated conclusion](goal) holds. -/
lemma sparse_target_center_sq_le {H S h : ℝ} (hS : 0 < S)
    (hH : 0 ≤ H) (hHS : H ≤ S) :
    (1 / 2 + H / (2 * S) - (1 / 2 + h / 2)) ^ 2 ≤
      ((S - 1) ^ 2 + (H - h) ^ 2) / 2 := by
  have hb := sparse_ratio_normalization_le hS hH hHS
  have hsq : (H / S - H) ^ 2 ≤ (S - 1) ^ 2 := by
    have hp := abs_nonneg (H / S - H)
    nlinarith [sq_abs (H / S - H), sq_abs (1 - S)]
  have hid : 1 / 2 + H / (2 * S) - (1 / 2 + h / 2) =
      ((H / S - H) + (H - h)) / 2 := by ring
  rw [hid]
  nlinarith [sq_nonneg ((H / S - H) - (H - h))]

/-- Applying the exact sparse likelihood identity gives the target-center estimate for the actual observed law, including arbitrary boundary intensities. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hε,hεhalf,hM,hB,hz), the [stated conclusion](goal) holds. -/
lemma sparseLaw_target_center_sq_le (n d : ℕ) (ε M B : ℝ)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hM : 2 ≤ M) (hB : B > 2) (z : Fin d → ℝ)
    (hz : ∀ x, z x ∈ Set.Icc 0 M) (h : ℝ) :
    (observedValue (sparseLaw (by omega : 0 < d) ε M ⟨hε, hεhalf⟩ z hz) -
      (1 / 2 + h / 2)) ^ 2 ≤
      ((sparseNormalizerFormula d ε M z hz - 1) ^ 2 +
        ((∑ x : Fin d, phiEpsFormula ε (z x)) / d - h) ^ 2) / 2 := by
  have hval := (sparse_likelihood n d ε M B z hn hd hε hεhalf hM hB hz).2.2.1
  rw [hval]
  have hs : 0 < sparseNormalizerFormula d ε M z hz :=
    lt_of_lt_of_le (by norm_num) (sparseNormalizer_ge_half hε.le hεhalf z hz)
  obtain ⟨hlo, hhi⟩ := sparse_average_phi_bounds (by omega : 0 < d)
    hε.le hεhalf z hz
  convert sparse_target_center_sq_le (h := h) hs hlo hhi using 1
  ring


-- @node: sparse_target_center_integral_sq_le
/-- Integrating the pointwise estimate reduces target concentration to the two second moments appearing in roadmap equations (37)--(39). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hS,hH,hHS,hSsecond,hHsecond), the [stated conclusion](goal) holds. -/
lemma sparse_target_center_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H S : Ω → ℝ) (h : ℝ)
    (hS : ∀ ω, 0 < S ω) (hH : ∀ ω, 0 ≤ H ω) (hHS : ∀ ω, H ω ≤ S ω)
    (hSsecond : Integrable (fun ω => (S ω - 1) ^ 2) μ)
    (hHsecond : Integrable (fun ω => (H ω - h) ^ 2) μ) :
    (∫ ω, (1 / 2 + H ω / (2 * S ω) - (1 / 2 + h / 2)) ^ 2 ∂μ) ≤
      ((∫ ω, (S ω - 1) ^ 2 ∂μ) + (∫ ω, (H ω - h) ^ 2 ∂μ)) / 2 := by
  calc
    _ ≤ ∫ ω, ((S ω - 1) ^ 2 + (H ω - h) ^ 2) / 2 ∂μ := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        ((hSsecond.add hHsecond).div_const 2)
      exact Filter.Eventually.of_forall fun ω =>
        sparse_target_center_sq_le (hS ω) (hH ω) (hHS ω)
    _ = _ := by rw [integral_div, integral_add hSsecond hHsecond]

end CausalSmith.Stat.OptvalueVanishingoverlapRate
