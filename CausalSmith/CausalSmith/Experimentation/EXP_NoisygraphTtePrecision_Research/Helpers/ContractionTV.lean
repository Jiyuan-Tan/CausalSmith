module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.LikelihoodDensity
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.LikelihoodExpansion
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.PosteriorEnergy
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Analytic
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The odd geometric series and full-record TV contraction

The bounded polynomial densities permit the L1–L2 comparison. The exact odd-order
expansion and planted posterior energy bound then sum to the stated geometric bound.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- [Every mark factor is Borel, including the zero-density branch.](goal) -/
-- @node: contraction_responseMark_measurable
@[fun_prop] lemma contraction_responseMark_measurable (δ : ℝ) :
    Measurable (responseMark δ) := by
  have hf (s : ℝ) : Measurable (fun y =>
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y-s)) := by
    unfold CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity
    apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    all_goals fun_prop
  have hb := (balancedDensity_probability δ).1
  unfold responseMark
  apply Measurable.ite (measurableSet_lt measurable_const hb)
  · exact ((hf δ).sub (by simpa using hf (-δ))).div (measurable_const.mul hb)
  · exact measurable_const

/-- Given [the stated assumptions](hyp:hfit), [Finite graph posteriors and Borel response marks give a Borel likelihood polynomial.](goal) -/
-- @node: contraction_likelihoodPoly_measurable
@[fun_prop] lemma contraction_likelihoodPoly_measurable (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (σ : Bool) : Measurable (likelihoodPoly n m hfit q r δ σ) := by
  unfold likelihoodPoly
  apply Finset.measurable_sum
  intro M _
  apply Measurable.mul
  · exact (Measurable.of_discrete : Measurable
      (fun H => matchingPosterior n m hfit q r H M)).comp measurable_fst
  · apply Finset.measurable_prod
    intro e _
    fun_prop

/-- Given [the stated assumptions](hyp:hfit,hqr), [Each likelihood factor is in [0,2], so averaging matching products costs at most 2^m.](goal) -/
-- @node: contraction_likelihoodPoly_le
lemma contraction_likelihoodPoly_le (n m : ℕ) (hfit : 2*m ≤ n) (q r δ : ℝ)
    (hqr : ChannelDomain q r) (σ : Bool) (o : Record (Fin n)) :
    likelihoodPoly n m hfit q r δ σ o ≤ (2 : ℝ)^m := by
  have hf (e : Fin m × Fin m) :
      0 ≤ 1 + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ *
        responseMark δ (o.2.2 (recipientOf n m hfit e.2)) *
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf (o.2.1 (donorOf n m hfit e.1)) ∧
      1 + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ *
        responseMark δ (o.2.2 (recipientOf n m hfit e.2)) *
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf (o.2.1 (donorOf n m hfit e.1)) ≤ 2 := by
    have hh := responseMark_mem_Icc δ (o.2.2 (recipientOf n m hfit e.2))
    cases σ <;> cases o.2.1 (donorOf n m hfit e.1) <;>
      simp only [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf,
        Bool.false_eq_true, ↓reduceIte] <;> constructor <;> nlinarith [hh.1, hh.2]
  calc
    likelihoodPoly n m hfit q r δ σ o ≤
        ∑ M : Matching m, matchingPosterior n m hfit q r o.1 M * (2 : ℝ)^m := by
      apply Finset.sum_le_sum
      intro M _
      apply mul_le_mul_of_nonneg_left _ (matchingPosterior_nonneg n m hfit q r hqr o.1 M)
      calc
        _ ≤ ∏ _e ∈ M.edges, (2 : ℝ) := Finset.prod_le_prod (fun e _ => (hf e).1)
          (fun e _ => (hf e).2)
        _ = (2 : ℝ)^M.size := by simp [Matching.size]
        _ ≤ (2 : ℝ)^m := pow_le_pow_right₀ (by norm_num) (matching_size_le m M)
    _ = (2 : ℝ)^m := by rw [← Finset.sum_mul, matchingPosterior_sum_one n m hfit q r hqr]; ring

/-- Given [the stated assumptions](hyp:hfit,hqr), [Bounded measurable likelihoods have an integrable squared sign difference.](goal) -/
-- @node: contraction_likelihood_difference_integrable
lemma contraction_likelihood_difference_integrable (n m : ℕ) (hfit : 2*m ≤ n)
    (q r δ : ℝ) (hqr : ChannelDomain q r) :
    Integrable (fun o => (likelihoodPoly n m hfit q r δ true o -
      likelihoodPoly n m hfit q r δ false o)^2) (referenceLaw n m hfit q r δ) := by
  let := referenceLaw_probability n m hfit q r δ hqr
  apply Integrable.of_bound (by fun_prop) (((2 : ℝ)^m)^2)
  apply Filter.Eventually.of_forall
  intro o
  have hp0 := likelihoodPoly_nonneg n m hfit q r δ hqr true o
  have hn0 := likelihoodPoly_nonneg n m hfit q r δ hqr false o
  have hp := contraction_likelihoodPoly_le n m hfit q r δ hqr true o
  have hn := contraction_likelihoodPoly_le n m hfit q r δ hqr false o
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [mul_nonneg hp0 hn0, mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hn)]

/-- Given [the stated assumptions](hyp:hx0,hx), [The odd powers in any finite range are bounded by the odd geometric series.](goal) -/
-- @node: contraction_odd_geometric_sum_le
lemma contraction_odd_geometric_sum_le (m : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 1) :
    (∑ k ∈ (Finset.Icc 1 m).filter Odd, x^k) ≤ x/(1-x^2) := by
  let S := (Finset.Icc 1 m).filter Odd
  have hid (k : ℕ) (hk : k ∈ S) : k = 2*(k/2)+1 := by
    have ho := Nat.odd_iff.mp (Finset.mem_filter.mp hk).2
    omega
  have hinj : Set.InjOn (fun k : ℕ => k/2) (S : Set ℕ) := by
    intro k hk l hl hkl
    dsimp only at hkl
    calc
      k = 2*(k/2)+1 := hid k hk
      _ = 2*(l/2)+1 := by rw [hkl]
      _ = l := (hid l hl).symm
  have hsub : S.image (fun k => k/2) ⊆ Finset.range (m+1) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have hkm := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
    simp only [Finset.mem_range]
    omega
  have hsq : x^2 < 1 := by nlinarith
  calc
    (∑ k ∈ S, x^k) = ∑ j ∈ S.image (fun k => k/2), x*(x^2)^j := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro k hk
      calc
        x^k = x^(2*(k/2)+1) := congrArg (fun j => x^j) (hid k hk)
        _ = x*(x^2)^(k/2) := by rw [pow_add, pow_mul]; ring
    _ ≤ ∑ j ∈ Finset.range (m+1), x*(x^2)^j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = x * ∑ j ∈ Finset.Ico 0 (m+1), (x^2)^j := by rw [Nat.Ico_zero_eq_range, Finset.mul_sum]
    _ ≤ x * (1/(1-x^2)) := by
      apply mul_le_mul_of_nonneg_left _ hx0
      simpa using geom_sum_Ico_le_of_lt_one (sq_nonneg x) hsq (m := 0) (n := m+1)
    _ = x/(1-x^2) := by ring

/-- Given [the stated assumptions](hyp:hm,hfit,hr,hrq,hq,hδ,hδu,ha,hH,hi,hregime,hx), [The L1–L2 step and all-order bounds sum the odd geometric series.](goal) -/
-- @node: contraction_tv
lemma contraction_tv (n m : ℕ) (hm : 1 ≤ m) (hfit : 2*m ≤ n) (q r δ : ℝ)
    (hr : 0 < r) (hrq : r ≤ q) (hq : q ≤ 1) (hδ : 0 < δ) (hδu : δ ≤ 1/12)
    (D : Design (Fin n)) (ha : AssignmentLaw D) (hH : AcquisitionLaw D q r)
    (hi : DesignIndependent D) (hregime : q/2 ≤ m*r)
    (hx : (9/64)*markEnergy δ*kappa q r < 1) :
    Causalean.Stat.tvDist (signLaw n m hfit D true δ) (signLaw n m hfit D false δ) ≤
      Real.sqrt (((9/64)*markEnergy δ*kappa q r)/(1-((9/64)*markEnergy δ*kappa q r)^2)) := by
  have hqr : ChannelDomain q r := ⟨hr.le, hrq, hq⟩
  let := referenceLaw_probability n m hfit q r δ hqr
  let := signLaw_probability n m hfit D q r δ hqr ha hH hi true
  let := signLaw_probability n m hfit D q r δ hqr ha hH hi false
  have hdens (σ : Bool) : signLaw n m hfit D σ δ =
      (referenceLaw n m hfit q r δ).withDensity
        (fun o => ENNReal.ofReal (likelihoodPoly n m hfit q r δ σ o)) := by
    let := signLaw_probability n m hfit D q r δ hqr ha hH hi σ
    obtain ⟨hac, hrn⟩ := likelihood_density n m hm hfit q r δ hr hrq hq hδ hδu D ha hH hi σ
    rw [← Measure.withDensity_rnDeriv_eq _ _ hac]
    exact withDensity_congr_ae hrn
  have htv := Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_le_half_sqrt_integral_sq_density_sub
    (signLaw n m hfit D true δ) (signLaw n m hfit D false δ)
    (referenceLaw n m hfit q r δ)
    (likelihoodPoly n m hfit q r δ true) (likelihoodPoly n m hfit q r δ false)
    (contraction_likelihoodPoly_measurable n m hfit q r δ true)
    (contraction_likelihoodPoly_measurable n m hfit q r δ false)
    (likelihoodPoly_nonneg n m hfit q r δ hqr true)
    (likelihoodPoly_nonneg n m hfit q r δ hqr false)
    (hdens true) (hdens false)
    (contraction_likelihood_difference_integrable n m hfit q r δ hqr)
  let x := (9/64)*markEnergy δ*kappa q r
  have hx0 : 0 ≤ x := mul_nonneg
    (mul_nonneg (by norm_num) (markEnergy_mem_Icc δ).1) (kappa_nonneg q r hqr)
  have henergy :
      (∫ o, (likelihoodPoly n m hfit q r δ true o - likelihoodPoly n m hfit q r δ false o)^2
        ∂referenceLaw n m hfit q r δ) ≤ 4 * (x/(1-x^2)) := by
    rw [likelihood_odd_energy n m hm hfit q r δ hr hrq hq hδ hδu]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      _ ≤ ∑ k ∈ (Finset.Icc 1 m).filter Odd, x^k := by
        apply Finset.sum_le_sum
        intro k hk
        have hkI := (Finset.mem_filter.mp hk).1
        calc
          _ ≤ markEnergy δ ^ k * (((9/64)*kappa q r)^k) :=
            mul_le_mul_of_nonneg_left
              (posterior_order_energy_le n m hm hfit q r hr hrq hq hregime k hkI)
              (pow_nonneg (markEnergy_mem_Icc δ).1 k)
          _ = x^k := by dsimp [x]; rw [← mul_pow]; congr 1; ring
      _ ≤ x/(1-x^2) := contraction_odd_geometric_sum_le m x hx0 hx
  calc
    _ ≤ (1/2 : ℝ) * Real.sqrt
        (∫ o, (likelihoodPoly n m hfit q r δ true o - likelihoodPoly n m hfit q r δ false o)^2
          ∂referenceLaw n m hfit q r δ) := htv
    _ ≤ (1/2 : ℝ) * Real.sqrt (4 * (x/(1-x^2))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt henergy) (by norm_num)
    _ = Real.sqrt (x/(1-x^2)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      ring


end CausalSmith.Experimentation.NoisygraphTtePrecision
