module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.AffineTesting
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.CausalRealization
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.FinitePrefixTransfer
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridArmRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridUpper
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.T_RareLabelFloor

/-!
Uniform rare-overlap annotation frontier and existence and identification of causal extensions.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Universal four-index minimax comparison, attaining rule, and compatible causal
interpretation](goal).
-/
-- @node: thm:uniform-annotation-frontier
theorem uniform_annotation_frontier :
    (∃ c C : Real, 0 < c ∧ c ≤ C ∧
      -- @realizes c(positive lower constant independent of all public indices)
      -- @realizes C(finite upper constant at least c independent of all public indices)
      ∀ (n m d : Nat) (eps : Real), 1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
        Measurable (hybridEstimator n m d eps) ∧
        (∀ s, hybridEstimator n m d eps s ∈ Set.Icc (-1) 1) ∧
        c * frontierRate n m d eps ≤ minimaxRisk n m d eps ∧
        minimaxRisk n m d eps ≤ worstRisk (liftRule (hybridEstimator n m d eps)) eps ∧
        worstRisk (liftRule (hybridEstimator n m d eps)) eps ≤ C * frontierRate n m d eps) ∧
    (∀ (d : Nat) (eps : Real) (P : DiscreteLaw d),
      2 ≤ d → 0 < eps → eps ≤ 1 / 4 → ModelClass d eps P →
      (∃ H : PotentialLaw d, observedMarginal H = P ∧ Consistency H ∧ ConditionalExchangeability
        H) ∧
      ∀ H : PotentialLaw d, observedMarginal H = P → Consistency H →
        -- @realizes H(universal extension has observed marginal P and satisfies consistency)
        ConditionalExchangeability H → poContrast H = ateFunctional P) := by
  obtain ⟨clab, hclab, hlab⟩ := rare_label_floor.1
  obtain ⟨caff, hcaff, haff⟩ := normalized_affine_testing
  obtain ⟨Cup, hCup, hup⟩ := hybrid_upper
  let E : Real := Real.exp 4096
  have hE : 1 ≤ E := Real.one_le_exp (by norm_num)
  have hEpos : 0 < E := Real.exp_pos _
  let c : Real := min (clab / (2 * E)) (caff / 2)
  have hc : 0 < c := lt_min (div_pos hclab (by positivity)) (by positivity)
  have hcl : c ≤ clab / (2 * E) := min_le_left _ _
  have hca : c ≤ caff / 2 := min_le_right _ _
  have hcl2 : 2 * c ≤ clab := by
    have := (le_div_iff₀ (show 0 < 2 * E by positivity)).mp hcl
    nlinarith
  constructor
  · refine ⟨c, max Cup c, hc, le_max_right _ _, ?_⟩
    intro n m d eps hn hd heps heps'
    obtain ⟨hmeas, hrange, hupper⟩ := hup n m d eps hn hd heps heps'
    have hrate : 0 ≤ frontierRate n m d eps := (frontierRate_pos n m d eps hn heps).le
    have hminimax : minimaxRisk n m d eps ≤
        worstRisk (liftRule (hybridEstimator n m d eps)) eps := by
      have hmeasLift : Measurable (liftRule (hybridEstimator n m d eps)) := by
        exact hmeas.comp measurable_fst
      let T : Rule n m d := ⟨liftRule (hybridEstimator n m d eps), hmeasLift,
        fun z => hrange z.1⟩
      exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
        (risk := fun (T : Rule n m d) (P : ClassLaw d eps) => ruleRisk T.1 P.1)
        (fun T P => integral_nonneg (fun z => sq_nonneg _)) T
    refine ⟨hmeas, hrange, ?_, hminimax,
      hupper.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrate)⟩
    have hlabel := (hlab n m d eps hn hd heps heps').1
    let S : Real := (n : Real) * eps
    let x : Real := (d : Real) / (((n : Real) + m) * eps * logScale n eps)
    have hS : 0 < S := mul_pos (by exact_mod_cast hn) heps
    have hinv : 0 < 1 / S := one_div_pos.mpr hS
    have hrdef : frontierRate n m d eps = min 1 (1 / S + x ^ 2) := rfl
    have hbdef : labelBenchmark n eps = min 1 (1 / S) := by
      simp only [labelBenchmark, labelScale, one_div, S]
    by_cases hsmall : S < E
    · have hbinv : 1 / E ≤ 1 / S := one_div_le_one_div_of_le hS hsmall.le
      have hb : 1 / E ≤ labelBenchmark n eps := by
        rw [hbdef]
        exact le_min ((div_le_one hEpos).mpr hE) hbinv
      have hcE : c ≤ clab * (1 / E) := by
        have := (le_div_iff₀ (show 0 < 2 * E by positivity)).mp hcl
        have hdiv : (clab * (1 / E)) * E = clab := by field_simp
        nlinarith
      calc
        c * frontierRate n m d eps ≤ c * 1 :=
          mul_le_mul_of_nonneg_left (frontierRate_le_one n m d eps) hc.le
        _ ≤ clab * (1 / E) := by simpa using hcE
        _ ≤ clab * labelBenchmark n eps := mul_le_mul_of_nonneg_left hb hclab.le
        _ ≤ minimaxRisk n m d eps := hlabel
    · have hlarge : E ≤ S := le_of_not_gt hsmall
      have hSone : 1 ≤ S := hE.trans hlarge
      have hb : labelBenchmark n eps = 1 / S := by
        rw [hbdef, min_eq_right ((div_le_one hS).mpr hSone)]
      by_cases hx : x ^ 2 ≤ 1 / S
      · have hr : frontierRate n m d eps ≤ 2 * (1 / S) := by
          rw [hrdef]
          exact (min_le_right _ _).trans (by linarith)
        calc
          c * frontierRate n m d eps ≤ c * (2 * (1 / S)) :=
            mul_le_mul_of_nonneg_left hr hc.le
          _ ≤ clab * (1 / S) := by nlinarith [mul_le_mul_of_nonneg_right hcl2 hinv.le]
          _ ≤ minimaxRisk n m d eps := by simpa only [hb] using hlabel
      · have ha := (haff n m d eps hn hd heps heps' hlarge (lt_of_not_ge hx)).2.2
        change caff * min 1 (x ^ 2) ≤ minimaxRisk n m d eps at ha
        have hr : frontierRate n m d eps ≤ 2 * min 1 (x ^ 2) := by
          rw [hrdef]
          by_cases hxone : x ^ 2 ≤ 1
          · rw [min_eq_right hxone]
            exact (min_le_right _ _).trans (by linarith [lt_of_not_ge hx])
          · rw [min_eq_left (le_of_not_ge hxone)]
            exact (min_le_left _ _).trans (by norm_num)
        have hxmin : 0 ≤ min 1 (x ^ 2) := le_min (by norm_num) (sq_nonneg _)
        have hca2 : 2 * c ≤ caff := by linarith
        calc
          c * frontierRate n m d eps ≤ c * (2 * min 1 (x ^ 2)) :=
            mul_le_mul_of_nonneg_left hr hc.le
          _ ≤ caff * min 1 (x ^ 2) := by
            nlinarith [mul_le_mul_of_nonneg_right hca2 hxmin]
          _ ≤ minimaxRisk n m d eps := ha
  · intro d eps P hd heps heps' hP
    obtain ⟨hwitness, hidentify⟩ := causal_realization d eps P hd heps heps' hP
    exact ⟨⟨independentExtension P, hwitness⟩, hidentify⟩

end CausalSmith.Stat.AnnotationRarearmFrontier
