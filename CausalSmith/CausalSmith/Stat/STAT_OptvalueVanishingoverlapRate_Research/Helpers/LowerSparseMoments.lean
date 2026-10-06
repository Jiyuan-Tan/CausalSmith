module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparse
public import Mathlib.Probability.Moments.Variance

/-! # Sparse prior concentration

Roadmap equation (37) follows from bounded intensities with common first
moment one and independence across cells. Square integrability is derived
from the support envelope, rather than imposed as an extra premise.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators


-- @node: sparse_intensity_memLp_variance_le
/-- A supported intensity of mean one has variance at most its support endpoint. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hZ,hsupp,hmean), the [stated conclusion](goal) holds. -/
lemma sparse_intensity_memLp_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (M : ℝ)
    (hZ : Measurable Z) (hsupp : ∀ ω, Z ω ∈ Set.Icc 0 M)
    (hmean : (∫ ω, Z ω ∂μ) = 1) :
    MemLp Z 2 μ ∧ variance Z μ ≤ M := by
  have hLp : MemLp Z 2 μ := MemLp.of_bound hZ.aestronglyMeasurable M
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hsupp ω).1]
      exact (hsupp ω).2)
  refine ⟨hLp, (variance_le_expectation_sq hLp.aestronglyMeasurable).trans ?_⟩
  calc
    (∫ ω, Z ω ^ 2 ∂μ) ≤ ∫ ω, M * Z ω ∂μ :=
      integral_mono hLp.integrable_sq
        ((hLp.integrable (by norm_num)).const_mul M)
        (fun ω => sparse_intensity_sq_le (hsupp ω))
    _ = M := by rw [integral_const_mul, hmean, mul_one]

/-- The functional envelope yields the scalar variance bound in (37), uniformly including zero overlap and the upper boundary of the intensity support. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hZ,hsupp,hmean,hε,hεhalf), the [stated conclusion](goal) holds. -/
lemma sparse_phi_memLp_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (M ε : ℝ)
    (hZ : Measurable Z) (hsupp : ∀ ω, Z ω ∈ Set.Icc 0 M)
    (hmean : (∫ ω, Z ω ∂μ) = 1) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    MemLp (fun ω => phiEpsFormula ε (Z ω)) 2 μ ∧
      variance (fun ω => phiEpsFormula ε (Z ω)) μ ≤ 2 * (1 + ε ^ 2 * M) := by
  have hm : Measurable (fun ω => phiEpsFormula ε (Z ω)) := by
    unfold phiEpsFormula
    fun_prop
  have hLp : MemLp (fun ω => phiEpsFormula ε (Z ω)) 2 μ :=
    MemLp.of_bound hm.aestronglyMeasurable (1 - ε + ε * M)
      (ae_of_all _ fun ω => by
        have hb := phiEps_nonneg_le_weight hε hεhalf (hsupp ω).1
        rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
        exact hb.2.trans (by gcongr; exact (hsupp ω).2))
  have hZi := (sparse_intensity_memLp_variance_le μ Z M hZ hsupp hmean).1.integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  refine ⟨hLp, (variance_le_expectation_sq hLp.aestronglyMeasurable).trans ?_⟩
  calc
    (∫ ω, phiEpsFormula ε (Z ω) ^ 2 ∂μ) ≤
        ∫ ω, 2 * (1 + ε ^ 2 * M * Z ω) ∂μ :=
      integral_mono hLp.integrable_sq
        (((integrable_const 1).add (hZi.const_mul (ε ^ 2 * M))).const_mul 2)
        (fun ω => phiEps_sq_le hε hεhalf (hsupp ω))
    _ = 2 * (1 + ε ^ 2 * M) := by
      rw [integral_const_mul, integral_add (integrable_const 1)
        (hZi.const_mul _), integral_const_mul, hmean]
      simp


-- @node: sparse_independent_average_variance_le
/-- Independent cell variances give the inverse-alphabet concentration factor for their average; the cells need not have identical distributions. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hZ,hind,hv), the [stated conclusion](goal) holds. -/
lemma sparse_independent_average_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (hd : 0 < d)
    (Z : Fin d → Ω → ℝ) (v : ℝ) (hZ : ∀ x, MemLp (Z x) 2 μ)
    (hind : iIndepFun Z μ) (hv : ∀ x, variance (Z x) μ ≤ v) :
    variance (fun ω => (∑ x, Z x ω) / d) μ ≤ v / d := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have he : (∑ x, Z x) = (fun ω => ∑ x, Z x ω) := by funext ω; simp
  have hsum : variance (fun ω => ∑ x, Z x ω) μ = ∑ x, variance (Z x) μ := by
    rw [← he]
    exact IndepFun.variance_sum (fun x _ => hZ x)
      (fun x _ y _ hxy => hind.indepFun hxy)
  simp_rw [div_eq_mul_inv]
  rw [variance_mul_const, hsum]
  calc
    _ ≤ (∑ _x : Fin d, v) * (d : ℝ)⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun x _ => hv x) (sq_nonneg _)
    _ = _ := by simp; field_simp

/-- The empirical average of the positive-part functional has the H_d variance bound of (37), derived from the intensity support and first moments. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hZ,hsupp,hmean,hind,hε,hεhalf), the [stated conclusion](goal) holds. -/
lemma sparse_average_phi_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (hd : 0 < d)
    (Z : Fin d → Ω → ℝ) (M ε : ℝ) (hZ : ∀ x, Measurable (Z x))
    (hsupp : ∀ x ω, Z x ω ∈ Set.Icc 0 M)
    (hmean : ∀ x, (∫ ω, Z x ω ∂μ) = 1) (hind : iIndepFun Z μ)
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    variance (fun ω => (∑ x, phiEpsFormula ε (Z x ω)) / d) μ ≤
      2 * (1 + ε ^ 2 * M) / d := by
  have hphi : Measurable (phiEpsFormula ε) := by unfold phiEpsFormula; fun_prop
  have hb (x : Fin d) := sparse_phi_memLp_variance_le μ (Z x) M ε
    (hZ x) (hsupp x) (hmean x) hε hεhalf
  exact sparse_independent_average_variance_le μ hd
    (fun x ω => phiEpsFormula ε (Z x ω)) _ (fun x => (hb x).1)
    (hind.comp (fun _ => phiEpsFormula ε) (fun _ => hphi)) (fun x => (hb x).2)


-- @node: sparse_normalizer_integral_sq_le
/-- The sparse denominator has expectation one, so its squared error about one is its variance. This proves the S_d assertion of roadmap (37). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hZ,hsupp,hmean,hind), the [stated conclusion](goal) holds. -/
lemma sparse_normalizer_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (hd : 0 < d)
    (Z : Fin d → Ω → ℝ) (M ε : ℝ) (hZ : ∀ x, Measurable (Z x))
    (hsupp : ∀ x ω, Z x ω ∈ Set.Icc 0 M)
    (hmean : ∀ x, (∫ ω, Z x ω ∂μ) = 1) (hind : iIndepFun Z μ) :
    (∫ ω, (1 - ε + ε * ((∑ x, Z x ω) / d) - 1) ^ 2 ∂μ) ≤ ε ^ 2 * M / d := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hb (x : Fin d) := sparse_intensity_memLp_variance_le μ (Z x) M
    (hZ x) (hsupp x) (hmean x)
  let A : Ω → ℝ := fun ω => (∑ x, Z x ω) / d
  have hAm : Measurable A := by dsimp [A]; fun_prop
  have hAi : Integrable A μ :=
    (integrable_finsetSum _ (fun x _ => (hb x).1.integrable (by norm_num))).div_const _
  have hAe : (∫ ω, A ω ∂μ) = 1 := by
    dsimp [A]
    rw [integral_div, integral_finsetSum _
      (fun x _ => (hb x).1.integrable (by norm_num))]
    simp [hmean, ne_of_gt hdR]
  have hSm : Measurable (fun ω => ε * A ω + (1 - ε)) := by fun_prop
  have hSe : (∫ ω, ε * A ω + (1 - ε) ∂μ) = 1 := by
    rw [integral_add (hAi.const_mul _) (integrable_const _), integral_const_mul, hAe]
    simp
  have hv := sparse_independent_average_variance_le μ hd Z M
    (fun x => (hb x).1) hind (fun x => (hb x).2)
  have hid (ω : Ω) : 1 - ε + ε * A ω = ε * A ω + (1 - ε) := by ring
  have hvar : variance (fun ω => ε * A ω + (1 - ε)) μ =
      ∫ ω, (ε * A ω + (1 - ε) - 1) ^ 2 ∂μ := by
    rw [variance_eq_integral hSm.aemeasurable, hSe]
  change (∫ ω, (1 - ε + ε * A ω - 1) ^ 2 ∂μ) ≤ _
  simp_rw [hid]
  rw [← hvar, variance_add_const (hAm.aestronglyMeasurable.const_mul ε),
    variance_const_mul]
  exact (mul_le_mul_of_nonneg_left hv (sq_nonneg ε)).trans_eq (by ring)

/-- The H_d variance estimate is also its integrated squared deviation from its prior mean, the second assertion of (37) in precisely its roadmap form. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hZ,hsupp,hmean,hind,hε,hεhalf), the [stated conclusion](goal) holds. -/
lemma sparse_average_phi_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (hd : 0 < d)
    (Z : Fin d → Ω → ℝ) (M ε : ℝ) (hZ : ∀ x, Measurable (Z x))
    (hsupp : ∀ x ω, Z x ω ∈ Set.Icc 0 M)
    (hmean : ∀ x, (∫ ω, Z x ω ∂μ) = 1) (hind : iIndepFun Z μ)
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    let H := fun ω => (∑ x, phiEpsFormula ε (Z x ω)) / d
    (∫ ω, (H ω - (∫ η, H η ∂μ)) ^ 2 ∂μ) ≤
      2 * (1 + ε ^ 2 * M) / d := by
  dsimp only
  have hm : Measurable (fun ω => (∑ x, phiEpsFormula ε (Z x ω)) / d) := by
    unfold phiEpsFormula
    fun_prop
  rw [← variance_eq_integral hm.aemeasurable]
  exact sparse_average_phi_variance_le μ hd Z M ε hZ hsupp hmean hind hε hεhalf

/-- Equations (37)--(39) control the normalized sparse target around its nonrandom prior center. This retains both denominator and numerator errors. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hZ,hsupp,hmean,hind,hε,hεhalf), the [stated conclusion](goal) holds. -/
lemma sparse_prior_target_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (hd : 0 < d)
    (Z : Fin d → Ω → ℝ) (M ε : ℝ) (hZ : ∀ x, Measurable (Z x))
    (hsupp : ∀ x ω, Z x ω ∈ Set.Icc 0 M)
    (hmean : ∀ x, (∫ ω, Z x ω ∂μ) = 1) (hind : iIndepFun Z μ)
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) :
    let H := fun ω => (∑ x, phiEpsFormula ε (Z x ω)) / d
    let S := fun ω => 1 - ε + ε * ((∑ x, Z x ω) / d)
    (∫ ω, (1 / 2 + H ω / (2 * S ω) -
      (1 / 2 + (∫ η, H η ∂μ) / 2)) ^ 2 ∂μ) ≤
        (2 + 3 * ε ^ 2 * M) / (2 * d) := by
  dsimp only
  let H := fun ω => (∑ x, phiEpsFormula ε (Z x ω)) / d
  let S := fun ω => 1 - ε + ε * ((∑ x, Z x ω) / d)
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hA : MemLp (fun ω => (∑ x, Z x ω) / d) 2 μ := by
    simpa only [div_eq_mul_inv] using
      (memLp_finsetSum Finset.univ (fun x _ =>
        (sparse_intensity_memLp_variance_le μ (Z x) M (hZ x)
          (hsupp x) (hmean x)).1)).mul_const (d : ℝ)⁻¹
  have hS : MemLp S 2 μ := by
    exact (memLp_const (1 - ε)).add (hA.const_mul ε)
  have hH : MemLp H 2 μ := by
    simpa only [H, div_eq_mul_inv] using
      (memLp_finsetSum Finset.univ (fun x _ =>
        (sparse_phi_memLp_variance_le μ (Z x) M ε (hZ x)
          (hsupp x) (hmean x) hε hεhalf).1)).mul_const (d : ℝ)⁻¹
  have hSpos (ω : Ω) : 0 < S ω := by
    have hb := sparseNormalizer_ge_half hε hεhalf (fun x => Z x ω)
      (fun x => hsupp x ω)
    have he : sparseNormalizerFormula d ε M (fun x => Z x ω) (fun x => hsupp x ω) = S ω := by
      dsimp [sparseNormalizerFormula, S]
      ring
    rw [he] at hb
    linarith
  have hbounds (ω : Ω) : 0 ≤ H ω ∧ H ω ≤ S ω := by
    have hb := sparse_average_phi_bounds hd hε hεhalf (fun x => Z x ω)
      (fun x => hsupp x ω)
    have he : sparseNormalizerFormula d ε M (fun x => Z x ω) (fun x => hsupp x ω) = S ω := by
      dsimp [sparseNormalizerFormula, S]
      ring
    simpa only [H, he] using hb
  have hnorm := sparse_normalizer_integral_sq_le μ hd Z M ε hZ hsupp hmean hind
  have hnum := sparse_average_phi_integral_sq_le μ hd Z M ε hZ hsupp hmean hind hε hεhalf
  have htarget := sparse_target_center_integral_sq_le μ H S (∫ η, H η ∂μ)
    hSpos (fun ω => (hbounds ω).1) (fun ω => (hbounds ω).2)
    ((hS.sub (memLp_const 1)).integrable_sq)
    ((hH.sub (memLp_const _)).integrable_sq)
  apply htarget.trans
  calc
    _ ≤ (ε ^ 2 * M / d + 2 * (1 + ε ^ 2 * M) / d) / 2 := by
      exact div_le_div_of_nonneg_right (add_le_add hnorm hnum) (by norm_num)
    _ = _ := by ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
