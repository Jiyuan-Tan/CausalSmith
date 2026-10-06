module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperIndependentAggregation

/-! # Good- and bad-pilot risk assembly

Roadmap (29) splits each actual cell error into its disjoint good- and
bad-pilot parts. Independent cell variances add; the good bias is summed
before squaring, and the bad bias is controlled by its second moments.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- @node: pairwiseCell_sum_sqRisk_eq
/-- Pairwise independence suffices for (29): only distinct-cell covariances enter the variance of the sum. This matches the implemented marked experiment. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hT,hind), the [stated conclusion](goal) holds. -/
lemma pairwiseCell_sum_sqRisk_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (T : Fin d → Ω → ℝ) (t : Fin d → ℝ)
    (hT : ∀ x, MemLp (T x) 2 μ)
    (hind : Pairwise (fun x y => IndepFun (T x) (T y) μ)) :
    Causalean.Stat.sqRisk μ (fun ω => ∑ x, T x ω) (∑ x, t x) =
      (∑ x, variance (T x) μ) + (∑ x, ((∫ ω, T x ω ∂μ) - t x)) ^ 2 := by
  have hsum := memLp_finsetSum Finset.univ (fun x _ => hT x)
  have hfun : (∑ x, T x) = (fun ω => ∑ x, T x ω) := by funext ω; simp
  have hv := IndepFun.variance_sum (X := T) (s := Finset.univ)
    (fun x _ => hT x) (fun x _ y _ hxy => hind hxy)
  rw [hfun] at hv
  rw [cellStatistic_sqRisk_eq_variance_add_bias μ _ _ hsum, hv,
    integral_finsetSum _ (fun x _ => (hT x).integrable (by norm_num)),
    Finset.sum_sub_distrib]

-- @node: independentCell_good_bad_sqRisk_le
/-- Disjoint good and bad errors yield the independent-cell risk estimate in (29). Only the full cell statistics need be independent. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hT,hind,hG,hB,hsplit,hdisjoint), the [stated conclusion](goal) holds. -/
lemma independentCell_good_bad_sqRisk_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (T G B : Fin d → Ω → ℝ) (t : Fin d → ℝ)
    (hT : ∀ x, MemLp (T x) 2 μ) (hind : Pairwise (fun x y => IndepFun (T x) (T y) μ))
    (hG : ∀ x, MemLp (G x) 2 μ) (hB : ∀ x, MemLp (B x) 2 μ)
    (hsplit : ∀ x ω, T x ω - t x = G x ω + B x ω)
    (hdisjoint : ∀ x ω, G x ω * B x ω = 0) :
    Causalean.Stat.sqRisk μ (fun ω => ∑ x, T x ω) (∑ x, t x) ≤
      (∑ x, ∫ ω, (G x ω) ^ 2 ∂μ) +
      2 * (∑ x, ∫ ω, G x ω ∂μ) ^ 2 +
      (1 + 2 * (d : ℝ)) * (∑ x, ∫ ω, (B x ω) ^ 2 ∂μ) := by
  have hv (x : Fin d) : variance (T x) μ ≤
      (∫ ω, (G x ω) ^ 2 ∂μ) + (∫ ω, (B x ω) ^ 2 ∂μ) := by
    have hr := cellStatistic_sqRisk_eq_variance_add_bias μ (T x) (t x) (hT x)
    have he : Causalean.Stat.sqRisk μ (T x) (t x) =
        (∫ ω, (G x ω) ^ 2 ∂μ) + (∫ ω, (B x ω) ^ 2 ∂μ) := by
      unfold Causalean.Stat.sqRisk
      calc
        _ = ∫ ω, (G x ω) ^ 2 + (B x ω) ^ 2 ∂μ := integral_congr_ae (by
          filter_upwards [] with ω
          rw [hsplit x ω]
          nlinarith [hdisjoint x ω])
        _ = _ := integral_add (hG x).integrable_sq (hB x).integrable_sq
    rw [he] at hr
    linarith [sq_nonneg ((∫ ω, T x ω ∂μ) - t x)]
  have hb (x : Fin d) : (∫ ω, T x ω ∂μ) - t x =
      (∫ ω, G x ω ∂μ) + (∫ ω, B x ω ∂μ) := by
    rw [← integral_add ((hG x).integrable (by norm_num))
      ((hB x).integrable (by norm_num))]
    have he : (fun ω => G x ω + B x ω) = (fun ω => T x ω - t x) := by
      funext ω
      exact (hsplit x ω).symm
    rw [he, integral_sub ((hT x).integrable (by norm_num)) (integrable_const _)]
    simp
  have hbad := clippingScale_integral_sum_sq_le μ B
    (fun x => (hB x).integrable (by norm_num)) (fun x => (hB x).integrable_sq)
  rw [pairwiseCell_sum_sqRisk_eq μ T t hT hind]
  simp_rw [hb]
  rw [Finset.sum_add_distrib]
  have hvar := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hv x)
  rw [Finset.sum_add_distrib] at hvar
  nlinarith [sq_nonneg ((∑ x, ∫ ω, G x ω ∂μ) - (∑ x, ∫ ω, B x ω ∂μ))]

open Classical in
-- @node: independentCell_pilotEvent_sqRisk_le
/-- Measurable pilot events provide the disjoint error split automatically. Both pieces inherit L² regularity from the cell statistic, so this step introduces no extra moment assumption on the localized pieces. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hT,hind,hE), the [stated conclusion](goal) holds. -/
lemma independentCell_pilotEvent_sqRisk_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (T : Fin d → Ω → ℝ) (t : Fin d → ℝ) (E : Fin d → Set Ω)
    (hT : ∀ x, MemLp (T x) 2 μ) (hind : Pairwise (fun x y => IndepFun (T x) (T y) μ))
    (hE : ∀ x, MeasurableSet (E x)) :
    Causalean.Stat.sqRisk μ (fun ω => ∑ x, T x ω) (∑ x, t x) ≤
      (∑ x, ∫ ω, if ω ∈ E x then (T x ω - t x) ^ 2 else 0 ∂μ) +
      2 * (∑ x, ∫ ω, if ω ∈ E x then T x ω - t x else 0 ∂μ) ^ 2 +
      (1 + 2 * (d : ℝ)) *
        (∑ x, ∫ ω, if ω ∉ E x then (T x ω - t x) ^ 2 else 0 ∂μ) := by
  classical
  let G : Fin d → Ω → ℝ := fun x ω => if ω ∈ E x then T x ω - t x else 0
  let B : Fin d → Ω → ℝ := fun x ω => if ω ∉ E x then T x ω - t x else 0
  have hG (x : Fin d) : MemLp (G x) 2 μ := by
    change MemLp ((E x).indicator (fun ω => T x ω - t x)) 2 μ
    exact ((hT x).sub (memLp_const (t x))).indicator (hE x)
  have hB (x : Fin d) : MemLp (B x) 2 μ := by
    have he : B x = (E x)ᶜ.indicator (fun ω => T x ω - t x) := by
      funext ω
      simp only [B, Set.indicator_apply, Set.mem_compl_iff]
    rw [he]
    exact ((hT x).sub (memLp_const (t x))).indicator (hE x).compl
  have hs (x : Fin d) (ω : Ω) : T x ω - t x = G x ω + B x ω := by
    by_cases he : ω ∈ E x <;> simp [G, B, he]
  have hdj (x : Fin d) (ω : Ω) : G x ω * B x ω = 0 := by
    by_cases he : ω ∈ E x <;> simp [G, B, he]
  have h := independentCell_good_bad_sqRisk_le μ T G B t hT hind hG hB hs hdj
  simpa only [G, B, ite_pow, zero_pow (by norm_num : 2 ≠ 0)] using h

-- @node: activeBranch_good_bad_independentCell_sqRisk_rate_le
/-- The good-pilot estimates (19), (20), (28) and the bad-pilot squared cell estimate (22) imply the full independent-cell rate (34). The bad error retains its actual second moment; no unit-loss replacement is used. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hCs,hCv,hCd), the [stated conclusion](goal) holds. -/
lemma activeBranch_good_bad_independentCell_sqRisk_rate_le (Cs Cv Cb Cd : ℝ)
    (hCs : 0 ≤ Cs) (hCv : 0 ≤ Cv) (hCd : 0 ≤ Cd) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (P : DiscreteLaw d) (T G B S : Fin d → Ω → ℝ) (t : Fin d → ℝ) (a : ℝ),
      0 < a → (d : ℝ) ≤ 8 * a * logAlphabet d →
      (∀ x, MemLp (T x) 2 μ) → Pairwise (fun x y => IndepFun (T x) (T y) μ) →
      (∀ x, MemLp (G x) 2 μ) → (∀ x, MemLp (B x) 2 μ) →
      (∀ x ω, T x ω - t x = G x ω + B x ω) →
      (∀ x ω, G x ω * B x ω = 0) →
      (∀ x, Integrable (S x) μ) →
      (∀ x, Integrable (fun ω => (S x ω) ^ 2) μ) →
      (∀ x, (∫ ω, (S x ω) ^ 2 ∂μ) ≤
        Cs * (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) →
      (∀ x, (∫ ω, (G x ω) ^ 2 ∂μ) ≤
        Cv * (d : ℝ) ^ (1 / 16 : ℝ) * (∫ ω, (S x ω) ^ 2 ∂μ)) →
      (∀ x, |∫ ω, G x ω ∂μ| ≤
        Cb * (Real.sqrt (cellMass P x / (a * logAlphabet d)) +
          1 / (a * logAlphabet d) + (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ ω, S x ω ∂μ))) →
      (∀ x, (∫ ω, (B x ω) ^ 2 ∂μ) ≤
        Cd * (d : ℝ) ^ (-4 : ℝ) *
          (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) →
      Causalean.Stat.sqRisk μ (fun ω => ∑ x, T x ω) (∑ x, t x) ≤
        C * ((d : ℝ) / (a * logAlphabet d)) := by
  obtain ⟨Av, hAv, hvariance⟩ := activeBranch_variance_scale_rate_le
  obtain ⟨Ab, hAb, hbias⟩ := activeBranch_combined_bias_rate_le
  obtain ⟨Ad, hAd, hbadRate⟩ := activeBranch_pilot_moment_sum_rate_le 1 (by norm_num)
  let C := Cv * Cs * Av + 4 * Cb ^ 2 * (18 + Cs * Ab) + 3 * Cd * Ad + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Ω _ μ _ d hd P T G B S t a ha hactive hT hind hG hB hsplit hdisjoint
    hS hS₂ hmom hgood₂ hgood₁ hbad₂
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hR : 0 ≤ (d : ℝ) / (a * logAlphabet d) := by
    have hL := logAlphabet_pos hd
    positivity
  have hvs := hvariance hd P (fun x => ∫ ω, (S x ω) ^ 2 ∂μ)
    Cs a hCs ha hactive hmom
  have hg := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hgood₂ x)
  rw [← Finset.mul_sum] at hg
  have hvg : (∑ x, ∫ ω, (G x ω) ^ 2 ∂μ) ≤
      Cv * Cs * Av * ((d : ℝ) / (a * logAlphabet d)) := hg.trans (by
    have hh := mul_le_mul_of_nonneg_left hvs hCv
    nlinarith [hh])
  have hbs := hbias μ hd P S Cs Cb a hCs ha hactive hS hS₂ hmom
  have hgb : |∑ x, ∫ ω, G x ω ∂μ| ≤
      ∑ x : Fin d, Cb * (Real.sqrt (cellMass P x / (a * logAlphabet d)) +
        1 / (a * logAlphabet d) + (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ ω, S x ω ∂μ)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun x _ => hgood₁ x))
  have hgb₂ := pow_le_pow_left₀ (abs_nonneg _) hgb 2
  rw [sq_abs] at hgb₂
  have hdecay : (d : ℝ) * (d : ℝ) ^ (-4 : ℝ) ≤ 1 := by
    nth_rw 1 [← Real.rpow_one (d : ℝ)]
    rw [← Real.rpow_add hd0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hd1 (by norm_num)
  have hscaled (x : Fin d) : (d : ℝ) * (∫ ω, (B x ω) ^ 2 ∂μ) ≤
      Cd * (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2) := by
    have hp : 0 ≤ cellMass P x :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
    have hL := logAlphabet_pos hd
    have hs : 0 ≤ cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2 :=
      by positivity
    calc
      _ ≤ (d : ℝ) * (Cd * (d : ℝ) ^ (-4 : ℝ) *
          (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) :=
        mul_le_mul_of_nonneg_left (hbad₂ x) hd0.le
      _ = Cd * ((d : ℝ) * (d : ℝ) ^ (-4 : ℝ)) *
          (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2) := by ring
      _ ≤ _ := by
        simpa using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdecay hCd) hs
  have hbd := hbadRate hd P (fun x => (d : ℝ) * (∫ ω, (B x ω) ^ 2 ∂μ))
    Cd a hCd ha hactive hscaled
  norm_num only [sub_self, Real.rpow_zero, one_mul] at hbd
  rw [← Finset.mul_sum] at hbd
  have hb0 : 0 ≤ ∑ x, ∫ ω, (B x ω) ^ 2 ∂μ :=
    Finset.sum_nonneg (fun x _ => integral_nonneg (fun ω => sq_nonneg _))
  have htotal := independentCell_good_bad_sqRisk_le μ T G B t hT hind hG hB
    hsplit hdisjoint
  have hbadterm : (1 + 2 * (d : ℝ)) * (∑ x, ∫ ω, (B x ω) ^ 2 ∂μ) ≤
      3 * (Cd * Ad * ((d : ℝ) / (a * logAlphabet d))) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd1) hb0]
  dsimp [C]
  nlinarith

-- @node: activeBranch_approximation_sum_sq_rate_le
/-- The squared cellwise Jackson approximation envelopes sum to at most 18 times the active rate, including null cells. This retains the approximation term in (28) when passing from polynomial loss to loss around the cell target. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:ha,hactive), the [stated conclusion](goal) holds. -/
lemma activeBranch_approximation_sum_sq_rate_le {d : ℕ} (P : DiscreteLaw d)
    (a : ℝ) (ha : 0 < a) (hactive : (d : ℝ) / a ≤ 8) :
    (∑ x : Fin d, (Real.sqrt (cellMass P x / a) + 1 / a) ^ 2) ≤
      18 * ((d : ℝ) / a) := by
  have hsum := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun x : Fin d => Real.sqrt (cellMass P x / a) + 1 / a)
    (fun x _ => add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have htotal := activeBranch_total_bias_sq_le P a ha hactive
  have he : (∑ x : Fin d, (Real.sqrt (cellMass P x / a) + 1 / a)) =
      (∑ x : Fin d, Real.sqrt (cellMass P x / a)) + (d : ℝ) / a := by
    rw [Finset.sum_add_distrib]
    simp [div_eq_mul_inv]
  rw [he] at hsum
  exact hsum.trans htotal

-- @node: activeBranch_good_bad_approximation_sqRisk_rate_le
/-- The good-pilot target loss includes both the factorial fluctuation and the squared Jackson approximation error. Summing that extra error with (32) preserves (34); the bad-pilot contribution is still its actual second moment. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hCs,hCv,hCd,hCe), the [stated conclusion](goal) holds. -/
lemma activeBranch_good_bad_approximation_sqRisk_rate_le (Cs Cv Cb Cd Ce : ℝ)
    (hCs : 0 ≤ Cs) (hCv : 0 ≤ Cv) (hCd : 0 ≤ Cd) (hCe : 0 ≤ Ce) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (P : DiscreteLaw d) (T G B S : Fin d → Ω → ℝ) (t : Fin d → ℝ) (a : ℝ),
      0 < a → (d : ℝ) ≤ 8 * a * logAlphabet d →
      (∀ x, MemLp (T x) 2 μ) → Pairwise (fun x y => IndepFun (T x) (T y) μ) →
      (∀ x, MemLp (G x) 2 μ) → (∀ x, MemLp (B x) 2 μ) →
      (∀ x ω, T x ω - t x = G x ω + B x ω) →
      (∀ x ω, G x ω * B x ω = 0) →
      (∀ x, Integrable (S x) μ) →
      (∀ x, Integrable (fun ω => (S x ω) ^ 2) μ) →
      (∀ x, (∫ ω, (S x ω) ^ 2 ∂μ) ≤
        Cs * (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) →
      (∀ x, (∫ ω, (G x ω) ^ 2 ∂μ) ≤
        Cv * (d : ℝ) ^ (1 / 16 : ℝ) * (∫ ω, (S x ω) ^ 2 ∂μ) +
          Ce * (Real.sqrt (cellMass P x / (a * logAlphabet d)) +
            1 / (a * logAlphabet d)) ^ 2) →
      (∀ x, |∫ ω, G x ω ∂μ| ≤
        Cb * (Real.sqrt (cellMass P x / (a * logAlphabet d)) +
          1 / (a * logAlphabet d) + (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ ω, S x ω ∂μ))) →
      (∀ x, (∫ ω, (B x ω) ^ 2 ∂μ) ≤
        Cd * (d : ℝ) ^ (-4 : ℝ) *
          (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) →
      Causalean.Stat.sqRisk μ (fun ω => ∑ x, T x ω) (∑ x, t x) ≤
        C * ((d : ℝ) / (a * logAlphabet d)) := by
  obtain ⟨Av, hAv, hvariance⟩ := activeBranch_variance_scale_rate_le
  obtain ⟨Ab, hAb, hbias⟩ := activeBranch_combined_bias_rate_le
  obtain ⟨Ad, hAd, hbadRate⟩ := activeBranch_pilot_moment_sum_rate_le 1 (by norm_num)
  let C := Cv * Cs * Av + 4 * Cb ^ 2 * (18 + Cs * Ab) + 3 * Cd * Ad + 18 * Ce + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Ω _ μ _ d hd P T G B S t a ha hactive hT hind hG hB hsplit hdisjoint
    hS hS₂ hmom hgood₂ hgood₁ hbad₂
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hR : 0 ≤ (d : ℝ) / (a * logAlphabet d) := by
    have hL := logAlphabet_pos hd
    positivity
  have hvs := hvariance hd P (fun x => ∫ ω, (S x ω) ^ 2 ∂μ)
    Cs a hCs ha hactive hmom
  have hg := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hgood₂ x)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hg
  have happrox := activeBranch_approximation_sum_sq_rate_le P
    (a * logAlphabet d) (mul_pos ha (logAlphabet_pos hd))
    ((div_le_iff₀ (mul_pos ha (logAlphabet_pos hd))).2 (by nlinarith))
  have hvg : (∑ x, ∫ ω, (G x ω) ^ 2 ∂μ) ≤
      (Cv * Cs * Av + 18 * Ce) * ((d : ℝ) / (a * logAlphabet d)) := hg.trans (by
    have hh := mul_le_mul_of_nonneg_left hvs hCv
    nlinarith [hh, mul_le_mul_of_nonneg_left happrox hCe])
  have hbs := hbias μ hd P S Cs Cb a hCs ha hactive hS hS₂ hmom
  have hgb : |∑ x, ∫ ω, G x ω ∂μ| ≤
      ∑ x : Fin d, Cb * (Real.sqrt (cellMass P x / (a * logAlphabet d)) +
        1 / (a * logAlphabet d) + (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ ω, S x ω ∂μ)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun x _ => hgood₁ x))
  have hgb₂ := pow_le_pow_left₀ (abs_nonneg _) hgb 2
  rw [sq_abs] at hgb₂
  have hdecay : (d : ℝ) * (d : ℝ) ^ (-4 : ℝ) ≤ 1 := by
    nth_rw 1 [← Real.rpow_one (d : ℝ)]
    rw [← Real.rpow_add hd0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hd1 (by norm_num)
  have hscaled (x : Fin d) : (d : ℝ) * (∫ ω, (B x ω) ^ 2 ∂μ) ≤
      Cd * (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2) := by
    have hp : 0 ≤ cellMass P x :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
    have hL := logAlphabet_pos hd
    have hs : 0 ≤ cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2 :=
      by positivity
    calc
      _ ≤ (d : ℝ) * (Cd * (d : ℝ) ^ (-4 : ℝ) *
          (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) :=
        mul_le_mul_of_nonneg_left (hbad₂ x) hd0.le
      _ = Cd * ((d : ℝ) * (d : ℝ) ^ (-4 : ℝ)) *
          (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2) := by ring
      _ ≤ _ := by
        simpa using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdecay hCd) hs
  have hbd := hbadRate hd P (fun x => (d : ℝ) * (∫ ω, (B x ω) ^ 2 ∂μ))
    Cd a hCd ha hactive hscaled
  norm_num only [sub_self, Real.rpow_zero, one_mul] at hbd
  rw [← Finset.mul_sum] at hbd
  have hb0 : 0 ≤ ∑ x, ∫ ω, (B x ω) ^ 2 ∂μ :=
    Finset.sum_nonneg (fun x _ => integral_nonneg (fun ω => sq_nonneg _))
  have htotal := independentCell_good_bad_sqRisk_le μ T G B t hT hind hG hB
    hsplit hdisjoint
  have hbadterm : (1 + 2 * (d : ℝ)) * (∑ x, ∫ ω, (B x ω) ^ 2 ∂μ) ≤
      3 * (Cd * Ad * ((d : ℝ) / (a * logAlphabet d))) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd1) hb0]
  dsimp [C]
  nlinarith

open Classical in
-- @node: activeBranch_pilotEvent_approximation_sqRisk_rate_le
/-- Measurable good-pilot events turn the target-loss estimates of (20), (22), and (28) into the independent-cell rate. The Jackson squared error is retained, and the localized L² properties follow from the full cell statistics. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hCs,hCv,hCd,hCe), the [stated conclusion](goal) holds. -/
lemma activeBranch_pilotEvent_approximation_sqRisk_rate_le (Cs Cv Cb Cd Ce : ℝ)
    (hCs : 0 ≤ Cs) (hCv : 0 ≤ Cv) (hCd : 0 ≤ Cd) (hCe : 0 ≤ Ce) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (P : DiscreteLaw d) (T S : Fin d → Ω → ℝ) (t : Fin d → ℝ)
        (E : Fin d → Set Ω) (a : ℝ),
      0 < a → (d : ℝ) ≤ 8 * a * logAlphabet d →
      (∀ x, MemLp (T x) 2 μ) → Pairwise (fun x y => IndepFun (T x) (T y) μ) →
      (∀ x, MeasurableSet (E x)) →
      (∀ x, Integrable (S x) μ) →
      (∀ x, Integrable (fun ω => (S x ω) ^ 2) μ) →
      (∀ x, (∫ ω, (S x ω) ^ 2 ∂μ) ≤
        Cs * (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) →
      (∀ x, (∫ ω, if ω ∈ E x then (T x ω - t x) ^ 2 else 0 ∂μ) ≤
        Cv * (d : ℝ) ^ (1 / 16 : ℝ) * (∫ ω, (S x ω) ^ 2 ∂μ) +
          Ce * (Real.sqrt (cellMass P x / (a * logAlphabet d)) +
            1 / (a * logAlphabet d)) ^ 2) →
      (∀ x, |∫ ω, if ω ∈ E x then T x ω - t x else 0 ∂μ| ≤
        Cb * (Real.sqrt (cellMass P x / (a * logAlphabet d)) +
          1 / (a * logAlphabet d) + (d : ℝ) ^ (-(3 / 16 : ℝ)) * (∫ ω, S x ω ∂μ))) →
      (∀ x, (∫ ω, if ω ∉ E x then (T x ω - t x) ^ 2 else 0 ∂μ) ≤
        Cd * (d : ℝ) ^ (-4 : ℝ) *
          (cellMass P x * logAlphabet d / a + logAlphabet d ^ 2 / a ^ 2)) →
      Causalean.Stat.sqRisk μ (fun ω => ∑ x, T x ω) (∑ x, t x) ≤
        C * ((d : ℝ) / (a * logAlphabet d)) := by
  classical
  obtain ⟨C, hC, hrate⟩ := activeBranch_good_bad_approximation_sqRisk_rate_le
    Cs Cv Cb Cd Ce hCs hCv hCd hCe
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ d hd P T S t E a ha hactive hT hind hE hS hS₂ hmom hg₂ hg₁ hb₂
  let G : Fin d → Ω → ℝ := fun x ω => if ω ∈ E x then T x ω - t x else 0
  let B : Fin d → Ω → ℝ := fun x ω => if ω ∉ E x then T x ω - t x else 0
  have hG (x : Fin d) : MemLp (G x) 2 μ := by
    change MemLp ((E x).indicator (fun ω => T x ω - t x)) 2 μ
    exact ((hT x).sub (memLp_const (t x))).indicator (hE x)
  have hB (x : Fin d) : MemLp (B x) 2 μ := by
    have he : B x = (E x)ᶜ.indicator (fun ω => T x ω - t x) := by
      funext ω
      simp only [B, Set.indicator_apply, Set.mem_compl_iff]
    rw [he]
    exact ((hT x).sub (memLp_const (t x))).indicator (hE x).compl
  apply hrate μ hd P T G B S t a ha hactive hT hind hG hB
  · intro x ω
    by_cases he : ω ∈ E x <;> simp [G, B, he]
  · intro x ω
    by_cases he : ω ∈ E x <;> simp [G, B, he]
  · exact hS
  · exact hS₂
  · exact hmom
  · simpa only [G, ite_pow, zero_pow (by norm_num : 2 ≠ 0)] using hg₂
  · exact hg₁
  · simpa only [B, ite_pow, zero_pow (by norm_num : 2 ≠ 0)] using hb₂

end CausalSmith.Stat.OptvalueVanishingoverlapRate
