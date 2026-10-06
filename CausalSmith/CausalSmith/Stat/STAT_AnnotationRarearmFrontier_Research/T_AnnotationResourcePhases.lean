module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.OraclePhaseAlgebra
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.T_BenchmarkRecovery
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.T_UniformAnnotationFrontier

/-!
Exact resource phases for arbitrary sequences and universal saturation and oracle plateaus.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


open Filter Asymptotics

/-- [Under the stated inputs and conditions](hyp:eps,hd,heps,heps',n,m,d), The zero Borel rule gives a risk at most one on the full observable model class.  This gives [the stated result](goal).-/
-- @node: phase_minimaxRisk_le_one
lemma phase_minimaxRisk_le_one (n m d : Nat) (eps : Real)
    (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    minimaxRisk n m d eps ≤ 1 := by
  let P0 : ClassLaw d eps :=
    ⟨labelFloorLaw d eps (1 / 8) false hd labelFloorAmplitude_eighth,
      labelFloor_model d eps (1 / 8) false hd labelFloorAmplitude_eighth heps heps'⟩
  letI : Nonempty (ClassLaw d eps) := ⟨P0⟩
  let T : Rule n m d := ⟨fun _ => 0, measurable_const, by intro z; norm_num⟩
  apply (Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    (risk := fun (T : Rule n m d) (P : ClassLaw d eps) => ruleRisk T.1 P.1)
    (fun T P => integral_nonneg (fun z => sq_nonneg _)) T).trans
  apply ciSup_le
  intro P
  have htarget := ateFunctional_mem_Icc P.1
  have hsq : (ateFunctional P.1) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htarget.2) (by linarith [htarget.1] : 0 ≤ ateFunctional P.1 + 1)]
  haveI : IsProbabilityMeasure (obsLaw P.1) := by
    dsimp [obsLaw]
    infer_instance
  haveI : IsProbabilityMeasure (labeledProductLaw P.1 n) := by
    dsimp [labeledProductLaw]
    infer_instance
  haveI : IsProbabilityMeasure (auxProductLaw P.1 m) := by
    dsimp [auxProductLaw]
    infer_instance
  haveI : IsProbabilityMeasure (annotationLaw P.1 n m) := by
    dsimp [annotationLaw]
    infer_instance
  haveI : IsProbabilityMeasure seedLaw := by
    constructor
    simp [seedLaw]
  simpa [ruleRisk, T, integral_const] using hsq

/-- [Under the stated inputs and conditions](hyp:hc,hC,hA,hB,hX,hY,A,B,X,Y,c,C), Uniform positive comparisons transfer vanishing ratios in both directions.  This gives [the stated result](goal).-/
-- @node: phase_ratio_comparison_tendsto
lemma phase_ratio_comparison_tendsto (A B X Y : Nat → Real) (c C : Real)
    (hc : 0 < c) (hC : 0 < C) (hA : ∀ k, 0 < A k) (hB : ∀ k, 0 < B k)
    (hX : ∀ k, c * A k ≤ X k ∧ X k ≤ C * A k)
    (hY : ∀ k, c * B k ≤ Y k ∧ Y k ≤ C * B k) :
    Tendsto (fun k => X k / Y k) atTop (nhds 0) ↔
      Tendsto (fun k => A k / B k) atTop (nhds 0) := by
  have hXp (k) : 0 < X k := (mul_pos hc (hA k)).trans_le (hX k).1
  have hYp (k) : 0 < Y k := (mul_pos hc (hB k)).trans_le (hY k).1
  have hupper (k) : X k / Y k ≤ (C / c) * (A k / B k) := by
    have h := (div_le_div_iff₀ (hYp k) (mul_pos hc (hB k))).2
      (show X k * (c * B k) ≤ (C * A k) * Y k by
        nlinarith [mul_le_mul_of_nonneg_right (hX k).2 (mul_pos hc (hB k)).le,
          mul_le_mul_of_nonneg_left (hY k).1 (mul_pos hC (hA k)).le])
    calc
      X k / Y k ≤ (C * A k) / (c * B k) := h
      _ = (C / c) * (A k / B k) := by field_simp
  have hlower (k) : A k / B k ≤ (C / c) * (X k / Y k) := by
    have h := (div_le_div_iff₀ (mul_pos hC (hB k)) (hYp k)).2
      (show (c * A k) * Y k ≤ X k * (C * B k) by
        nlinarith [mul_le_mul_of_nonneg_left (hY k).2 (mul_pos hc (hA k)).le,
          mul_le_mul_of_nonneg_right (hX k).1 (mul_pos hC (hB k)).le])
    have h' := mul_le_mul_of_nonneg_left h (le_of_lt (div_pos hC hc))
    calc
      A k / B k = (C / c) * ((c * A k) / (C * B k)) := by field_simp
      _ ≤ (C / c) * (X k / Y k) := h'
  constructor
  · intro h
    exact squeeze_zero (fun k => (div_pos (hA k) (hB k)).le) hlower
      (by simpa using h.const_mul (C / c))
  · intro h
    exact squeeze_zero (fun k => (div_pos (hXp k) (hYp k)).le) hupper
      (by simpa using h.const_mul (C / c))

/-- [Under the stated inputs and conditions](hyp:hS,S,x), The supervised cap differs from the dimension-only cap by at most the inverse label scale.  This gives [the stated result](goal).-/
-- @node: phase_supervised_cap_bounds
lemma phase_supervised_cap_bounds (S x : Real) (hS : 0 < S) :
    min 1 (x ^ 2) ≤ min 1 (1 / S + x ^ 2) ∧
      min 1 (1 / S + x ^ 2) ≤ min 1 (x ^ 2) + 1 / S := by
  refine ⟨min_le_min_left _ (by linarith [one_div_pos.mpr hS]), ?_⟩
  by_cases hx : x ^ 2 ≤ 1
  · rw [min_eq_right hx]
    exact (min_le_right _ _).trans_eq (by ring)
  · rw [min_eq_left (le_of_not_ge hx)]
    exact (min_le_left _ _).trans (by linarith [one_div_pos.mpr hS])

/-- [Under the stated inputs and conditions](hyp:hx,hh,x,h), Normalizing the auxiliary dimension term by its cap gives the exact budget ratio square.  This gives [the stated result](goal).-/
-- @node: phase_improvement_budget_square
lemma phase_improvement_budget_square (x h : Real) (hx : 0 < x) (hh : 0 < h) :
    (x / h) ^ 2 / min 1 (x ^ 2) = (max 1 x / h) ^ 2 := by
  by_cases hsmall : x ≤ 1
  · have hsq : x ^ 2 ≤ 1 := by nlinarith
    rw [min_eq_right hsq, max_eq_left hsmall]
    field_simp
  · have hlarge : 1 ≤ x := le_of_not_ge hsmall
    have hsq : 1 ≤ x ^ 2 := by nlinarith
    rw [min_eq_left hsq, max_eq_right hlarge, div_one]

/-- [Under the stated hypotheses](hyp:hc,hC,hcmp), Strict improvement is exactly vanishing frontier ratio under the uniform comparison.  This gives [the stated result](goal). -/
-- @node: improvement_ratio_of_frontier_comparison
lemma improvement_ratio_of_frontier_comparison (v : ExperimentSeq) (c C : Real)
    (hc : 0 < c) (hC : 0 < C)
    (hcmp : ∀ (n m d : Nat) (eps : Real), 1 ≤ n → 2 ≤ d →
      0 < eps → eps ≤ 1 / 4 →
      c * frontierRate n m d eps ≤ minimaxRisk n m d eps ∧
        minimaxRisk n m d eps ≤ C * frontierRate n m d eps) :
    v ∈ improvementPhase ↔ Tendsto (fun k =>
      frontierRate (v k).n (v k).m (v k).d (v k).eps /
        frontierRate (v k).n 0 (v k).d (v k).eps) atTop (nhds 0) := by
  exact phase_ratio_comparison_tendsto _ _ _ _ c C hc hC
    (fun k => frontierRate_pos _ _ _ _ (v k).n_pos (v k).eps_pos)
    (fun k => frontierRate_pos _ _ _ _ (v k).n_pos (v k).eps_pos)
    (fun k => hcmp _ _ _ _ (v k).n_pos (v k).d_ge (v k).eps_pos (v k).eps_le)
    (fun k => hcmp _ _ _ _ (v k).n_pos (v k).d_ge (v k).eps_pos (v k).eps_le)

/-- [Under the stated inputs and conditions](hyp:v,h), A vanishing frontier ratio forces diverging label information, even on oscillating sequences.  This gives [the stated result](goal).-/
-- @node: phase_improvement_label_divergence
lemma phase_improvement_label_divergence (v : ExperimentSeq)
    (h : Tendsto (fun k =>
      frontierRate (v k).n (v k).m (v k).d (v k).eps /
        frontierRate (v k).n 0 (v k).d (v k).eps) atTop (nhds 0)) :
    Tendsto (fun k => labelScale (v k).n (v k).eps) atTop atTop := by
  have hrate : Tendsto (fun k => frontierRate (v k).n (v k).m (v k).d (v k).eps)
      atTop (nhds 0) := by
    apply squeeze_zero (fun k =>
      (frontierRate_pos _ _ _ _ (v k).n_pos (v k).eps_pos).le) (fun k => ?_) h
    apply (le_div_iff₀ (frontierRate_pos _ _ _ _ (v k).n_pos (v k).eps_pos)).mpr
    exact mul_le_of_le_one_right
      (frontierRate_pos _ _ _ _ (v k).n_pos (v k).eps_pos).le
      (frontierRate_le_one _ _ _ _)
  exact ((consistency_of_frontier_comparison v
    (fun k => frontierRate (v k).n (v k).m (v k).d (v k).eps)
    1 1 zero_lt_one zero_lt_one (fun k => by simp)).mp hrate).1

/-- [Under the stated inputs and conditions](hyp:hS,hx,hh,S,x,h), The capped frontier ratio is bounded by the three inverse information scales.  This gives [the stated result](goal).-/
-- @node: phase_improvement_ratio_bound
lemma phase_improvement_ratio_bound (S x h : Real)
    (hS : 0 < S) (hx : 0 < x) (hh : 0 < h) :
    min 1 (1 / S + (x / h) ^ 2) / min 1 (1 / S + x ^ 2) ≤
      S⁻¹ + ((Real.sqrt S * x)⁻¹) ^ 2 + ((h / max 1 x)⁻¹) ^ 2 := by
  let t := min 1 (x ^ 2)
  have ht : 0 < t := lt_min zero_lt_one (sq_pos_of_pos hx)
  have hB : t ≤ min 1 (1 / S + x ^ 2) :=
    (phase_supervised_cap_bounds S x hS).1
  have hlabel : (1 / S) / t ≤ S⁻¹ + ((Real.sqrt S * x)⁻¹) ^ 2 := by
    have hsqrt := Real.sq_sqrt hS.le
    have hsqrtpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
    have hid : (1 / S) / x ^ 2 = ((Real.sqrt S * x)⁻¹) ^ 2 := by
      rw [mul_inv, mul_pow, inv_pow, hsqrt]
      simp only [one_div, div_eq_mul_inv, inv_pow, one_mul]
    by_cases hsmall : x ^ 2 ≤ 1
    · dsimp [t]
      rw [min_eq_right hsmall, hid]
      exact le_add_of_nonneg_left (inv_nonneg.mpr hS.le)
    · dsimp [t]
      rw [min_eq_left (le_of_not_ge hsmall), div_one, one_div]
      exact le_add_of_nonneg_right (sq_nonneg _)
  have hbudget : (x / h) ^ 2 / t = ((h / max 1 x)⁻¹) ^ 2 := by
    rw [phase_improvement_budget_square x h hx hh, inv_div]
  calc
    _ ≤ (1 / S + (x / h) ^ 2) / t :=
      div_le_div₀ (by positivity) (min_le_right _ _) ht hB
    _ = (1 / S) / t + (x / h) ^ 2 / t := add_div _ _ _
    _ ≤ _ := by rw [hbudget]; exact add_le_add hlabel le_rfl

/-- [Under the stated inputs and conditions](hyp:hS,hx,hh,hSlim,hxdim,hbudget,S,x,h), Diverging label, relative-dimension, and marginal-budget scales imply strict improvement.  This gives [the stated result](goal).-/
-- @node: phase_improvement_ratio_sufficient
lemma phase_improvement_ratio_sufficient (S x h : Nat → Real)
    (hS : ∀ k, 0 < S k) (hx : ∀ k, 0 < x k) (hh : ∀ k, 0 < h k)
    (hSlim : Tendsto S atTop atTop)
    (hxdim : Tendsto (fun k => Real.sqrt (S k) * x k) atTop atTop)
    (hbudget : Tendsto (fun k => h k / max 1 (x k)) atTop atTop) :
    Tendsto (fun k => min 1 (1 / S k + (x k / h k) ^ 2) /
      min 1 (1 / S k + x k ^ 2)) atTop (nhds 0) := by
  have h1 := tendsto_inv_atTop_zero.comp hSlim
  have h2 := (tendsto_inv_atTop_zero.comp hxdim).pow 2
  have h3 := (tendsto_inv_atTop_zero.comp hbudget).pow 2
  apply squeeze_zero (fun k => by
    have hSk := hS k
    positivity)
    (fun k => phase_improvement_ratio_bound _ _ _ (hS k) (hx k) (hh k))
  simpa using (h1.add h2).add h3

/-- [Under the stated inputs and conditions](hyp:hS,hx,hh,hr,S,x,h), Once the label cap is inactive, a small frontier ratio controls both inverse scales.  This gives [the stated result](goal).-/
-- @node: phase_improvement_necessary_bounds
lemma phase_improvement_necessary_bounds (S x h : Real)
    (hS : 1 ≤ S) (hx : 0 < x) (hh : 0 < h)
    (hr : min 1 (1 / S + (x / h) ^ 2) / min 1 (1 / S + x ^ 2) ≤ 1 / 2) :
    ((Real.sqrt S * x)⁻¹) ^ 2 ≤
        2 * (min 1 (1 / S + (x / h) ^ 2) / min 1 (1 / S + x ^ 2)) ∧
      ((h / max 1 x)⁻¹) ^ 2 ≤
        2 * (min 1 (1 / S + (x / h) ^ 2) / min 1 (1 / S + x ^ 2)) := by
  let a := 1 / S
  let A := min 1 (a + (x / h) ^ 2)
  let B := min 1 (a + x ^ 2)
  let r := A / B
  let t := min 1 (x ^ 2)
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have ha : 0 < a := one_div_pos.mpr hSp
  have ha1 : a ≤ 1 := by simpa [a] using one_div_le_one_div_of_le zero_lt_one hS
  have hB : 0 < B := lt_min zero_lt_one (by positivity)
  have ht : 0 < t := lt_min zero_lt_one (sq_pos_of_pos hx)
  have hr0 : 0 ≤ r := div_nonneg (le_min (by norm_num) (by positivity)) hB.le
  have hrhalf : r ≤ 1 / 2 := hr
  have hAB : r * B = A := div_mul_cancel₀ A hB.ne'
  have hAhalf : A ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left (min_le_left 1 (a + x ^ 2)) hr0
    simp only [mul_one] at this
    change r * B ≤ r at this
    linarith
  have hcap : A = a + (x / h) ^ 2 := by
    apply min_eq_right
    have : min 1 (a + (x / h) ^ 2) < 1 := lt_of_le_of_lt hAhalf (by norm_num)
    exact le_of_lt (by
      simpa only [min_lt_iff, lt_self_iff_false, false_or] using this)
  have haA : a ≤ A := by rw [hcap]; exact le_add_of_nonneg_right (sq_nonneg _)
  have hBsum : B ≤ a + x ^ 2 := min_le_right _ _
  have har : a ≤ r * (a + x ^ 2) :=
    haA.trans (hAB ▸ mul_le_mul_of_nonneg_left hBsum hr0)
  have hax : a ≤ x ^ 2 := by
    have := mul_le_mul_of_nonneg_right hrhalf (by positivity : 0 ≤ a + x ^ 2)
    nlinarith
  have haz : a ≤ 2 * r * x ^ 2 := by
    have := mul_le_mul_of_nonneg_right hrhalf ha.le
    nlinarith
  have hid : ((Real.sqrt S * x)⁻¹) ^ 2 = a / x ^ 2 := by
    rw [mul_inv, mul_pow, inv_pow, Real.sq_sqrt hSp.le]
    simp only [a, div_eq_mul_inv, inv_pow, one_mul]
  refine ⟨?_, ?_⟩
  · rw [hid]
    exact (div_le_iff₀ (sq_pos_of_pos hx)).mpr haz
  · have hat : a ≤ t := le_min ha1 hax
    have hBt : B ≤ 2 * t := by
      have hb := (phase_supervised_cap_bounds S x hSp).2
      change B ≤ t + a at hb
      linarith
    have hnum : (x / h) ^ 2 ≤ r * (2 * t) := by
      have hb := mul_le_mul_of_nonneg_left hBt hr0
      rw [hAB, hcap] at hb
      linarith
    rw [inv_div, ← phase_improvement_budget_square x h hx hh]
    exact (div_le_iff₀ ht).mpr (by nlinarith [hnum])

/-- [Under the stated inputs and conditions](hyp:hS,hx,hh,hSlim,hratio,S,x,h), Vanishing capped frontier ratios force both dimension and marginal-budget divergence.  This gives [the stated result](goal).-/
-- @node: phase_improvement_ratio_necessary
lemma phase_improvement_ratio_necessary (S x h : Nat → Real)
    (hS : ∀ k, 0 < S k) (hx : ∀ k, 0 < x k) (hh : ∀ k, 0 < h k)
    (hSlim : Tendsto S atTop atTop)
    (hratio : Tendsto (fun k => min 1 (1 / S k + (x k / h k) ^ 2) /
      min 1 (1 / S k + x k ^ 2)) atTop (nhds 0)) :
    Tendsto (fun k => Real.sqrt (S k) * x k) atTop atTop ∧
      Tendsto (fun k => h k / max 1 (x k)) atTop atTop := by
  have hbounds : ∀ᶠ k in atTop,
      ((Real.sqrt (S k) * x k)⁻¹) ^ 2 ≤
        2 * (min 1 (1 / S k + (x k / h k) ^ 2) / min 1 (1 / S k + x k ^ 2)) ∧
      ((h k / max 1 (x k))⁻¹) ^ 2 ≤
        2 * (min 1 (1 / S k + (x k / h k) ^ 2) / min 1 (1 / S k + x k ^ 2)) := by
    filter_upwards [hSlim.eventually (eventually_ge_atTop 1),
      hratio.eventually_lt_const (by norm_num : (0 : Real) < 1 / 2)] with k hs hr
    exact phase_improvement_necessary_bounds _ _ _ hs (hx k) (hh k) hr.le
  have hzero : Tendsto (fun k =>
      2 * (min 1 (1 / S k + (x k / h k) ^ 2) / min 1 (1 / S k + x k ^ 2)))
      atTop (nhds 0) := by simpa using hratio.const_mul 2
  have hinvert (f : Nat → Real) (hp : ∀ k, 0 < f k)
      (hsq : Tendsto (fun k => (f k)⁻¹ ^ 2) atTop (nhds 0)) :
      Tendsto f atTop atTop := by
    have hi : Tendsto (fun k => (f k)⁻¹) atTop (nhds 0) := by
      have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
      simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs,
        abs_of_pos (inv_pos.mpr (hp _))] using ht
    have hip : Tendsto (fun k => (f k)⁻¹) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hi, Eventually.of_forall (fun k => inv_pos.mpr (hp k))⟩
    simpa only [Function.comp_def, inv_inv] using tendsto_inv_nhdsGT_zero.comp hip
  constructor
  · apply hinvert _ (fun k => mul_pos (Real.sqrt_pos.mpr (hS k)) (hx k))
    exact squeeze_zero' (Eventually.of_forall (fun k => sq_nonneg _))
      (hbounds.mono (fun k hk => hk.1)) hzero
  · apply hinvert _ (fun k => div_pos (hh k) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    exact squeeze_zero' (Eventually.of_forall (fun k => sq_nonneg _))
      (hbounds.mono (fun k hk => hk.2)) hzero

-- @node: thm:annotation-resource-phases
/--
[Exact consistency, oracle, and strict-improvement phases and the two finite-budget
elbows](goal).
-/
theorem annotation_resource_phases :
    (∀ v : ExperimentSeq,
      let S := fun k => labelScale (v k).n (v k).eps
      let Nn := fun k => ((v k).n : Real) + (v k).m
      let ell := fun k => logScale (v k).n (v k).eps
      let dd := fun k => ((v k).d : Real)
      (v ∈ consistencyPhase ↔ Tendsto S atTop atTop ∧
        dd =o[atTop] (fun k => Nn k * (v k).eps * ell k)) ∧
      (v ∈ oraclePhase ↔ Tendsto S atTop atTop ∧
        dd =O[atTop] (fun k => Nn k * (v k).eps * ell k / Real.sqrt (S k))) ∧
      (v ∈ improvementPhase ↔ Tendsto S atTop atTop ∧
        Tendsto (fun k => dd k / (Real.sqrt (S k) * ell k)) atTop atTop ∧
        Tendsto (fun k => (Nn k / (v k).n) / max 1 (dd k / (S k * ell k))) atTop atTop) ∧
      ((∀ k, (v k).m = 0) →
        (v ∈ consistencyPhase ↔ Tendsto S atTop atTop ∧ dd =o[atTop] (fun k => S k * ell k)) ∧
        (v ∈ oraclePhase ↔ Tendsto S atTop atTop ∧ dd =O[atTop] (fun k => Real.sqrt (S k) * ell
          k)) ∧
        v ∉ improvementPhase) ∧
      (Tendsto S atTop atTop → (v ∈ oraclePhase ↔
        (fun k => dd k * Real.sqrt (S k) / ((v k).eps * ell k)) =O[atTop] Nn)) ∧
      (v ∈ oraclePhase →
        (∃ c C : Real, 0 < c ∧ 0 < C ∧ ∀ᶠ k in atTop,
          c / S k ≤ (v k).risk ∧ (v k).risk ≤ C / S k) ∧
        ∃ c : Real, 0 < c ∧ ∀ᶠ k in atTop, ∀ m' : Nat,
          c / S k ≤ minimaxRisk (v k).n m' (v k).d (v k).eps)) ∧
    (∃ c : Real, 0 < c ∧ ∀ (n m d : Nat) (eps : Real),
      1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
      ((n : Real) + m) * eps * logScale n eps ≤ d →
        c ≤ minimaxRisk n m d eps ∧ minimaxRisk n m d eps ≤ 1) ∧
    (∃ c C : Real, 0 < c ∧ 0 < C ∧ ∀ (n m d : Nat) (eps : Real),
      1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
      (d : Real) * Real.sqrt ((n : Real) * eps) / (eps * logScale n eps) ≤ (n : Real) + m →
        c * labelBenchmark n eps ≤ minimaxRisk n m d eps ∧
        minimaxRisk n m d eps ≤ C * labelBenchmark n eps) := by
  obtain ⟨c, C, hc, hcC, hfront⟩ := uniform_annotation_frontier.1
  have hC : 0 < C := hc.trans_le hcC
  have hcmp (n m d : Nat) (eps : Real) (hn : 1 ≤ n) (hd : 2 ≤ d)
      (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
      c * frontierRate n m d eps ≤ minimaxRisk n m d eps ∧
      minimaxRisk n m d eps ≤ C * frontierRate n m d eps := by
    obtain ⟨_, _, hlo, hmid, hhi⟩ := hfront n m d eps hn hd heps heps'
    exact ⟨hlo, hmid.trans hhi⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v
    dsimp only
    have hcons : v ∈ consistencyPhase ↔
        Tendsto (fun k => labelScale (v k).n (v k).eps) atTop atTop ∧
        (fun k => ((v k).d : Real)) =o[atTop]
          (fun k => (((v k).n : Real) + (v k).m) * (v k).eps *
            logScale (v k).n (v k).eps) := by
      exact consistency_of_frontier_comparison v (fun k => (v k).risk) c C hc hC
        (fun k => hcmp _ _ _ _ (v k).n_pos (v k).d_ge (v k).eps_pos (v k).eps_le)
    have horacle : v ∈ oraclePhase ↔
        Tendsto (fun k => labelScale (v k).n (v k).eps) atTop atTop ∧
        (fun k => ((v k).d : Real)) =O[atTop]
          (fun k => (((v k).n : Real) + (v k).m) * (v k).eps *
            logScale (v k).n (v k).eps / Real.sqrt (labelScale (v k).n (v k).eps)) := by
      constructor
      · rintro ⟨hS, hbounded⟩
        exact ⟨hS, (oracle_of_frontier_comparison v (fun k => (v k).risk) c C hc hC
          (fun k => hcmp _ _ _ _ (v k).n_pos (v k).d_ge (v k).eps_pos (v k).eps_le)
          hS).mp hbounded⟩
      · rintro ⟨hS, hdim⟩
        exact ⟨hS, (oracle_of_frontier_comparison v (fun k => (v k).risk) c C hc hC
          (fun k => hcmp _ _ _ _ (v k).n_pos (v k).d_ge (v k).eps_pos (v k).eps_le)
          hS).mpr hdim⟩
    refine ⟨hcons, horacle, ?_, ?_, ?_, ?_⟩
    · rw [improvement_ratio_of_frontier_comparison v c C hc hC hcmp]
      constructor
      · intro hratio
        refine ⟨phase_improvement_label_divergence v hratio, ?_⟩
        let S := fun k => labelScale (v k).n (v k).eps
        let ell := fun k => logScale (v k).n (v k).eps
        let x := fun k => ((v k).d : Real) / (S k * ell k)
        let h := fun k => (((v k).n : Real) + (v k).m) / (v k).n
        have hS (k) : 0 < S k := mul_pos (by exact_mod_cast (v k).n_pos) (v k).eps_pos
        have hell (k) : 0 < ell k := phase_logScale_pos _ _ (v k).n_pos (v k).eps_pos
        have hx (k) : 0 < x k := div_pos
          (by exact_mod_cast (show 0 < (v k).d by have := (v k).d_ge; omega))
          (mul_pos (hS k) (hell k))
        have hn (k) : (0 : Real) < (v k).n := by exact_mod_cast (v k).n_pos
        have hh (k) : 0 < h k := div_pos
          (add_pos_of_pos_of_nonneg (hn k) (Nat.cast_nonneg _)) (hn k)
        have hrate (k) : frontierRate (v k).n (v k).m (v k).d (v k).eps =
            min 1 (1 / S k + (x k / h k) ^ 2) := by
          dsimp [frontierRate, x, h, S, labelScale, ell]
          congr 2
          field_simp [ne_of_gt (hn k)]
        have hsuper (k) : frontierRate (v k).n 0 (v k).d (v k).eps =
            min 1 (1 / S k + x k ^ 2) := by
          simp only [frontierRate, Nat.cast_zero, add_zero, x, S, labelScale, ell]
        have hnormalized : Tendsto (fun k => min 1 (1 / S k + (x k / h k) ^ 2) /
            min 1 (1 / S k + x k ^ 2)) atTop (nhds 0) := by
          simpa only [hrate, hsuper] using hratio
        obtain ⟨hdim, hbudget⟩ := phase_improvement_ratio_necessary S x h hS hx hh
          (phase_improvement_label_divergence v hratio) hnormalized
        refine ⟨?_, hbudget⟩
        convert hdim using 1
        funext k
        have hs := Real.sq_sqrt (hS k).le
        have hsp := Real.sqrt_pos.mpr (hS k)
        change ((v k).d : Real) / (Real.sqrt (S k) * ell k) =
          Real.sqrt (S k) * (((v k).d : Real) / (S k * ell k))
        field_simp [ne_of_gt (hS k), ne_of_gt (hell k), ne_of_gt hsp]
        nlinarith [hs]
      · intro hlimits
        let S := fun k => labelScale (v k).n (v k).eps
        let ell := fun k => logScale (v k).n (v k).eps
        let x := fun k => ((v k).d : Real) / (S k * ell k)
        let h := fun k => (((v k).n : Real) + (v k).m) / (v k).n
        have hS (k) : 0 < S k := mul_pos (by exact_mod_cast (v k).n_pos) (v k).eps_pos
        have hell (k) : 0 < ell k := phase_logScale_pos _ _ (v k).n_pos (v k).eps_pos
        have hx (k) : 0 < x k := div_pos
          (by exact_mod_cast (show 0 < (v k).d by have := (v k).d_ge; omega))
          (mul_pos (hS k) (hell k))
        have hn (k) : (0 : Real) < (v k).n := by exact_mod_cast (v k).n_pos
        have hh (k) : 0 < h k := div_pos
          (add_pos_of_pos_of_nonneg (hn k) (Nat.cast_nonneg _)) (hn k)
        have hdim : Tendsto (fun k => Real.sqrt (S k) * x k) atTop atTop := by
          convert hlimits.2.1 using 1
          funext k
          have hs := Real.sq_sqrt (hS k).le
          have hsp := Real.sqrt_pos.mpr (hS k)
          change Real.sqrt (S k) * (((v k).d : Real) / (S k * ell k)) =
            ((v k).d : Real) / (Real.sqrt (S k) * ell k)
          field_simp [ne_of_gt (hS k), ne_of_gt (hell k), ne_of_gt hsp]
          nlinarith [hs]
        have hrate (k) : frontierRate (v k).n (v k).m (v k).d (v k).eps =
            min 1 (1 / S k + (x k / h k) ^ 2) := by
          dsimp [frontierRate, x, h, S, labelScale, ell]
          congr 2
          field_simp [ne_of_gt (hn k)]
        have hsuper (k) : frontierRate (v k).n 0 (v k).d (v k).eps =
            min 1 (1 / S k + x k ^ 2) := by
          simp only [frontierRate, Nat.cast_zero, add_zero, x, S, labelScale, ell]
        simpa only [hrate, hsuper] using
          phase_improvement_ratio_sufficient S x h hS hx hh hlimits.1 hdim hlimits.2.2
    · intro hsupervised
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hsupervised, Nat.cast_zero, add_zero, labelScale] using hcons
      · have hscale :
            (fun k => (((v k).n : Real) + (v k).m) * (v k).eps *
              logScale (v k).n (v k).eps / Real.sqrt (labelScale (v k).n (v k).eps)) =
            (fun k => Real.sqrt (labelScale (v k).n (v k).eps) *
              logScale (v k).n (v k).eps) := by
          funext k
          simpa only [hsupervised, Nat.cast_zero, add_zero] using
            phase_supervised_oracle_scale _ _ (v k).n_pos (v k).eps_pos
        simpa only [hscale] using horacle
      · intro himprove
        have hpositive (k : Nat) : 0 < (v k).risk :=
          (mul_pos hc (frontierRate_pos _ _ _ _ (v k).n_pos (v k).eps_pos)).trans_le
            (hcmp _ _ _ _ (v k).n_pos (v k).d_ge (v k).eps_pos (v k).eps_le).1
        have hone : (fun k => (v k).risk / minimaxRisk (v k).n 0 (v k).d (v k).eps) =
            (fun _ : Nat => (1 : Real)) := by
          funext k
          have heq : minimaxRisk (v k).n 0 (v k).d (v k).eps = (v k).risk := by
            simp only [PublicIndex.risk, hsupervised]
          rw [heq, div_self (hpositive k).ne']
        change Tendsto (fun k => (v k).risk /
          minimaxRisk (v k).n 0 (v k).d (v k).eps) atTop (nhds 0) at himprove
        rw [hone] at himprove
        have hfalse : (1 : Real) = 0 := tendsto_nhds_unique tendsto_const_nhds himprove
        exact one_ne_zero hfalse
    · intro hS
      rw [horacle, and_iff_right hS]
      exact phase_dimension_budget_iff v
    · intro horacle
      obtain ⟨hS, hbounded⟩ := horacle
      obtain ⟨M, hM⟩ := hbounded.eventually_le
      have hlarge : ∀ᶠ k in atTop, 1 ≤ labelScale (v k).n (v k).eps :=
        hS.eventually (eventually_ge_atTop 1)
      have hbench : ∀ᶠ k in atTop,
          labelBenchmark (v k).n (v k).eps = 1 / labelScale (v k).n (v k).eps := by
        filter_upwards [hlarge] with k hk
        dsimp only [labelBenchmark]
        rw [min_eq_right (inv_le_one_of_one_le₀ hk), one_div]
      have hlower (k : Nat) (m' : Nat) :
          c * labelBenchmark (v k).n (v k).eps ≤
            minimaxRisk (v k).n m' (v k).d (v k).eps :=
        (mul_le_mul_of_nonneg_left
          (phase_labelBenchmark_le_frontier _ _ _ _) hc.le).trans
          (hcmp _ _ _ _ (v k).n_pos (v k).d_ge (v k).eps_pos (v k).eps_le).1
      refine ⟨⟨c, max M 1, hc, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩,
        c, hc, ?_⟩
      · filter_upwards [hbench, hM] with k hk hMk
        have hpos : 0 < labelScale (v k).n (v k).eps :=
          mul_pos (by exact_mod_cast (v k).n_pos) (v k).eps_pos
        have hupper := (div_le_iff₀ (one_div_pos.mpr hpos)).mp (by
          simpa only [hk] using hMk)
        constructor
        · simpa only [hk, mul_one_div, PublicIndex.risk] using hlower k (v k).m
        · calc
            (v k).risk ≤ M * (1 / labelScale (v k).n (v k).eps) := hupper
            _ ≤ max M 1 * (1 / labelScale (v k).n (v k).eps) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (one_div_pos.mpr hpos).le
            _ = max M 1 / labelScale (v k).n (v k).eps := by rw [mul_one_div]
      · filter_upwards [hbench] with k hk
        intro m'
        simpa only [hk, mul_one_div] using hlower k m' 
  · refine ⟨c, hc, ?_⟩
    intro n m d eps hn hd heps heps' hdim
    have hsat := phase_frontier_saturation n m d eps hn heps hdim
    exact ⟨by simpa only [hsat, mul_one] using
      (hcmp n m d eps hn hd heps heps').1,
      phase_minimaxRisk_le_one n m d eps hd heps heps'⟩
  · refine ⟨c, 2 * C, hc, by positivity, ?_⟩
    intro n m d eps hn hd heps heps' hbudget
    obtain ⟨hlo, hhi⟩ := hcmp n m d eps hn hd heps heps'
    constructor
    · exact (mul_le_mul_of_nonneg_left
        (phase_labelBenchmark_le_frontier n m d eps) hc.le).trans hlo
    · calc
        minimaxRisk n m d eps ≤ C * frontierRate n m d eps := hhi
        _ ≤ C * (2 * labelBenchmark n eps) := mul_le_mul_of_nonneg_left
          (phase_frontier_plateau n m d eps hn heps hbudget) hC.le
        _ = (2 * C) * labelBenchmark n eps := by ring

end CausalSmith.Stat.AnnotationRarearmFrontier
