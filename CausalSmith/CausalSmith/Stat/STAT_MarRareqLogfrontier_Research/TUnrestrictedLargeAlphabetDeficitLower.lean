module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedNearCompleteArrivalEnvelope
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.LargeAlphabet.RiskAveraging
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.LargeAlphabet.SampleMatching
public import Causalean.Stat.Minimax.FuzzyHypotheses

/-! The uniform large-alphabet point-risk lower bound for all bounded estimator kernels. -/

public section
open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:q,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_center_separation
lemma largeAlphabet_center_separation (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    1 / 2 - q / (1 + q) = (1 - q) / (2 * (1 + q)) ∧
    (1 - q) / 4 ≤ 1 / 2 - q / (1 + q) ∧
    1 / 2 - q / (1 + q) ≤ (1 - q) / 2 := by
  have hp : 0 < 1 + q := by linarith
  have heq : 1 / 2 - q / (1 + q) = (1 - q) / (2 * (1 + q)) := by
    field_simp
    ring
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < 2 * (1 + q))).mpr
    nlinarith
  · rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + q))).mpr
    nlinarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,h,hn,hd,hq,hregime,hsep), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_prior_bad_probability
lemma largeAlphabet_prior_bad_probability (n d : ℕ) (q h : ℝ)
    (hn : 1 ≤ n) (hd : 1024 * n ^ 2 ≤ d) (hq : q ≤ 1)
    (hregime : (n : ℝ)⁻¹ ≤ (1 - q) ^ 2)
    (hsep : (1 - q) / 4 ≤ h) :
    (binaryCellPrior d).real {ξ | h / 4 < |cellPriorTarget ξ - 1 / 2|} ≤
      1 / 16 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdreal : 1024 * (n : ℝ) ^ 2 ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by nlinarith
  have hdNat : 1 ≤ d := by exact_mod_cast (show (1 : ℝ) ≤ d by nlinarith)
  have hdelta : 0 < 1 - q := by
    have hinv : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
    nlinarith
  have hh : 0 < h := by linarith
  have hsquare : (1 - q) ^ 2 ≤ 16 * h ^ 2 := by nlinarith
  have hndelta : 1 ≤ (n : ℝ) * (1 - q) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hregime hnpos.le
    simpa [ne_of_gt hnpos] using hm
  have hbudget : 64 ≤ (d : ℝ) * h ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ (n : ℝ) ^ 2)
    have h₂ := mul_le_mul_of_nonneg_right hdreal (sq_nonneg h)
    have h₃ := mul_le_mul_of_nonneg_left hndelta hnpos.le
    nlinarith
  refine (binaryCellPrior_target_concentration d hdNat (h / 4) (by positivity)).trans ?_
  apply (div_le_iff₀ (by positivity : 0 < 4 * (d : ℝ) * (h / 4) ^ 2)).mpr
  nlinarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hq1,hregime), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_center_prior_concentration
lemma largeAlphabet_center_prior_concentration (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1024 * n ^ 2 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1)
    (hregime : (n : ℝ)⁻¹ ≤ (1 - q) ^ 2) :
    (binaryCellPrior d).real
      {ξ | (1 / 2 - q / (1 + q)) / 4 < |cellPriorTarget ξ - 1 / 2|} ≤
      1 / 16 := by
  exact largeAlphabet_prior_bad_probability n d q (1 / 2 - q / (1 + q))
    hn hd hq1 hregime (largeAlphabet_center_separation q hq hq1).2.1

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hq1,hregime), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_deficit_minimax_lower
lemma largeAlphabet_deficit_minimax_lower
    (n d : ℕ) (q : ℝ) (hn : 1 ≤ n) (hd : 1024 * n ^ 2 ≤ d)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hregime : (n : ℝ)⁻¹ ≤ (1 - q) ^ 2) :
    (1 - q) ^ 2 / 1024 ≤ unrestrictedMinimaxRisk n d q := by
  have hdpos : 1 ≤ d := by nlinarith
  let T₀ : Estimator n d :=
    Estimator.ofMap (fun _ => 0) ⟨measurable_const, by intro s; norm_num⟩
  let : Nonempty (Estimator n d) := ⟨T₀⟩
  unfold unrestrictedMinimaxRisk
  apply Causalean.Stat.le_minimaxValue
  intro T
  let h : ℝ := 1 / 2 - q / (1 + q)
  have hsep := (largeAlphabet_center_separation q hq hq1).2.1
  have hh : 0 ≤ h := by dsimp [h]; linarith
  let P := largeAlphabetComparisonLaw d q hdpos hq hq1
  let := P.2
  let : IsProbabilityMeasure (P.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (sampleLaw n P) := by
    unfold sampleLaw
    infer_instance
  let E : Set ((Fin n → ObsRecord d) × ℝ) := {z | z.2 ≤ 1 / 2 - h / 2}
  have hE : MeasurableSet E := by measurability
  have havg := largeAlphabet_prior_test_risk n d q hdpos hq hq1 T (1 / 2) h hh
  have hcomp := largeAlphabet_comparison_test_risk (sampleLaw n P) T (1 / 2) h hh
  have htarget : 1 / 2 - h = ate P := by
    rw [show ate P = q / (1 + q) from
      largeAlphabetComparisonLaw_ate d q hdpos hq hq1]
    dsimp [h]
    ring
  rw [htarget] at hcomp
  change (h ^ 2 / 16) * (sampleLaw n P ⊗ₘ T.1).real Eᶜ ≤ squaredRisk T P at hcomp
  have htest := largeAlphabet_actual_collision_testing n d q hn hd hq hq1 T E hE
  have hbad := largeAlphabet_center_prior_concentration n d q hn hd hq hq1 hregime
  have hscaled := mul_le_mul_of_nonneg_left htest
    (by positivity : 0 ≤ h ^ 2 / 16)
  have hpenalty := mul_le_mul_of_nonneg_left hbad
    (by positivity : 0 ≤ h ^ 2 / 16)
  have hbayes : h ^ 2 / 32 ≤
      (∫ ξ, squaredRisk T (largeAlphabetLaw q ξ hdpos hq hq1) ∂binaryCellPrior d) +
        squaredRisk T P := by
    change (h ^ 2 / 16) * (1 - (1 / 8192 : ℝ)) ≤
      (h ^ 2 / 16) *
        ((largeAlphabetSampleMixture n d q hdpos hq hq1 ⊗ₘ T.1).real E +
          (sampleLaw n P ⊗ₘ T.1).real Eᶜ) at hscaled
    change (h ^ 2 / 16) * (binaryCellPrior d).real
      {ξ | h / 4 < |cellPriorTarget ξ - 1 / 2|} ≤ (h ^ 2 / 16) * (1 / 16) at hpenalty
    change (h ^ 2 / 16) *
      (largeAlphabetSampleMixture n d q hdpos hq hq1 ⊗ₘ T.1).real E ≤ _ at havg
    nlinarith only [hscaled, havg, hcomp, hpenalty, sq_nonneg h]
  have hbdd : BddAbove (Set.range (fun P : {P : FullLaw d //
      UnrestrictedArrivalModelClass n d q P} => squaredRisk T P.1)) := by
    refine ⟨4, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact (unrestricted_squaredRisk_bounds T P.1).2
  have hb₀ := largeAlphabet_prior_squaredRisk_le_worst n d q hn hdpos hq hq1 T
  have hb₁ := Causalean.Stat.le_worstCaseRisk
    (risk := fun (T : Estimator n d) (P : {P : FullLaw d //
      UnrestrictedArrivalModelClass n d q P}) => squaredRisk T P.1)
    (e := T) hbdd ⟨P, largeAlphabetComparisonLaw_model n d q hn hdpos hq hq1⟩
  have hsquare : (1 - q) ^ 2 ≤ 16 * h ^ 2 := by
    change (1 - q) / 4 ≤ h at hsep
    nlinarith [sq_nonneg (h - (1 - q) / 4)]
  nlinarith only [hbayes, hb₀, hb₁, hsquare]

-- @node: thm:unrestricted-large-alphabet-deficit-lower
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
theorem unrestricted_large_alphabet_deficit_lower
    (n d : ℕ) (q : ℝ) (hn : 1 ≤ n) (hd : 1024 * n ^ 2 ≤ d)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    max (1 / (256 * (n : ℝ))) ((1 - q) ^ 2 / 1024) ≤
      unrestrictedMinimaxRisk n d q ∧
    unrestrictedMinimaxRisk n d q ≤ 4 / (n : ℝ) + (1 - q) ^ 2 ∧
    (1 / 2048 : ℝ) * ((n : ℝ)⁻¹ + (1 - q) ^ 2) ≤ unrestrictedMinimaxRisk n d q ∧
    unrestrictedMinimaxRisk n d q ≤ 4 * ((n : ℝ)⁻¹ + (1 - q) ^ 2) := by
  have hdpos : 1 ≤ d := by nlinarith
  obtain ⟨C, hC, _, henvelope⟩ := unrestricted_near_complete_arrival_envelope
  obtain ⟨hfloor, hupper, _⟩ := henvelope n d q hn hdpos hq hq1
  have hupper' : unrestrictedMinimaxRisk n d q ≤ 4 / (n : ℝ) + (1 - q) ^ 2 :=
    hupper.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdeficit : (1 - q) ^ 2 / 1024 ≤ unrestrictedMinimaxRisk n d q := by
    by_cases hsmall : (1 - q) ^ 2 ≤ (n : ℝ)⁻¹
    · refine le_trans ?_ hfloor
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
      have heq : 1 / (256 * (n : ℝ)) = (n : ℝ)⁻¹ / 256 := by
        field_simp
      rw [heq]
      nlinarith [inv_nonneg.mpr hnpos.le, sq_nonneg (1 - q)]
    · have hregime : (n : ℝ)⁻¹ ≤ (1 - q) ^ 2 := (lt_of_not_ge hsmall).le
      exact largeAlphabet_deficit_minimax_lower n d q hn hd hq hq1 hregime
  have hmax := max_le hfloor hdeficit
  refine ⟨hmax, hupper', ?_, ?_⟩
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have heq : 1 / (256 * (n : ℝ)) = (n : ℝ)⁻¹ / 256 := by field_simp
    rw [heq] at hfloor
    linarith [inv_nonneg.mpr hnpos.le]
  · have heq : 4 / (n : ℝ) = 4 * (n : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    rw [heq] at hupper'
    nlinarith [sq_nonneg (1 - q)]

end CausalSmith.Stat.MarRareqLogfrontier
