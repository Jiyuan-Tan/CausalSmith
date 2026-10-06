module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.LabelFloorTesting
public import Mathlib.Analysis.Convex.Jensen

/-!
Conditional averaging of auxiliary samples for the exact-marginal experiment,
and the zero-rule cap on the original minimax risk.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- The iid auxiliary-array weight is a polynomial in the supplied table. -/
-- @node: comparisonArrayWeight
noncomputable def comparisonArrayWeight {m d : Nat} (v : AuxTable d)
    (V : Fin m → AuxObs d) : Real := ∏ i, v (V i)

/-- [Under the stated inputs and conditions](hyp:d,P,m,V), At the true table the polynomial weight is the probability of the auxiliary array.  This gives [the stated result](goal).-/
-- @node: comparisonArrayWeight_true
lemma comparisonArrayWeight_true {d : Nat} (P : DiscreteLaw d) (m : Nat)
    (V : Fin m → AuxObs d) :
    comparisonArrayWeight (auxTable P) V = (auxProductLaw P m).real {V} := by
  simp [comparisonArrayWeight, auxTable, auxProductLaw, measureReal_def,
    Measure.pi_singleton, ENNReal.toReal_prod, PMF.toMeasure_apply_singleton]

/-- [Under the stated inputs and conditions](hyp:d,P,m), Auxiliary-array weights at a population table sum to one, including the empty array.  This gives [the stated result](goal).-/
-- @node: comparisonArrayWeight_sum
lemma comparisonArrayWeight_sum {d : Nat} (P : DiscreteLaw d) (m : Nat) :
    ∑ V : Fin m → AuxObs d, comparisonArrayWeight (auxTable P) V = 1 := by
  letI : IsProbabilityMeasure (auxProductLaw P m) := by
    unfold auxProductLaw; infer_instance
  simp_rw [comparisonArrayWeight_true]
  simpa using (integral_fintype (μ := auxProductLaw P m)
    (integrable_const (1 : Real))).symm

/-- Averaging over auxiliary arrays retains the independent seed; clipping makes the rule
legal on every ambient table. -/
-- @node: comparisonAverageRule
noncomputable def comparisonAverageRule {n m d : Nat} (T : Rule n m d)
    (z : (Fin n → Obs d) × AuxTable d × Real) : Real :=
  max (-1) (min 1 (∑ V : Fin m → AuxObs d,
    comparisonArrayWeight z.2.1 V * T.1 ((z.1, V), z.2.2)))

/-- The averaged rule is Borel on the entire ambient table space. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: comparisonAverageRule_measurable
lemma comparisonAverageRule_measurable {n m d : Nat} (T : Rule n m d) :
    Measurable (comparisonAverageRule T) := by
  unfold comparisonAverageRule comparisonArrayWeight
  have hT := T.2.1
  fun_prop

/-- [Under the stated inputs and conditions](hyp:T,z,n,m,d), Clipping bounds the average even on tables that are not probability vectors.  This gives [the stated result](goal).-/
-- @node: comparisonAverageRule_mem_Icc
lemma comparisonAverageRule_mem_Icc {n m d : Nat} (T : Rule n m d)
    (z : (Fin n → Obs d) × AuxTable d × Real) :
    comparisonAverageRule T z ∈ Set.Icc (-1) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- [Under the stated inputs and conditions](hyp:T,P,L,u,n,m,d), On a true marginal table the convex average already lies in the action interval.  This gives [the stated result](goal).-/
-- @node: comparisonAverageRule_true
lemma comparisonAverageRule_true {n m d : Nat} (T : Rule n m d) (P : DiscreteLaw d)
    (L : Fin n → Obs d) (u : Real) :
    comparisonAverageRule T (L, auxTable P, u) =
      ∑ V : Fin m → AuxObs d, comparisonArrayWeight (auxTable P) V * T.1 ((L, V), u) := by
  have hw (V : Fin m → AuxObs d) : 0 ≤ comparisonArrayWeight (auxTable P) V := by
    rw [comparisonArrayWeight_true]; exact ENNReal.toReal_nonneg
  have hlo : -1 ≤ ∑ V : Fin m → AuxObs d,
      comparisonArrayWeight (auxTable P) V * T.1 ((L, V), u) := by
    calc
      -1 = ∑ V : Fin m → AuxObs d, comparisonArrayWeight (auxTable P) V * (-1) := by
        rw [← Finset.sum_mul, comparisonArrayWeight_sum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun V _ => mul_le_mul_of_nonneg_left (T.2.2 _).1 (hw V)
  have hhi : (∑ V : Fin m → AuxObs d,
      comparisonArrayWeight (auxTable P) V * T.1 ((L, V), u)) ≤ 1 := by
    calc
      _ ≤ ∑ V : Fin m → AuxObs d, comparisonArrayWeight (auxTable P) V * 1 :=
        Finset.sum_le_sum fun V _ => mul_le_mul_of_nonneg_left (T.2.2 _).2 (hw V)
      _ = 1 := by rw [← Finset.sum_mul, comparisonArrayWeight_sum, one_mul]
  unfold comparisonAverageRule
  rw [min_eq_right hhi, max_eq_right hlo]

/-- [Under the stated inputs and conditions](hyp:T,P,L,u,n,m,d), Jensen's inequality for the finite conditional average of a randomized rule.  This gives [the stated result](goal).-/
-- @node: comparisonAverageRule_loss_le
lemma comparisonAverageRule_loss_le {n m d : Nat} (T : Rule n m d) (P : DiscreteLaw d)
    (L : Fin n → Obs d) (u : Real) :
    (comparisonAverageRule T (L, auxTable P, u) - ateFunctional P) ^ 2 ≤
      ∑ V : Fin m → AuxObs d, comparisonArrayWeight (auxTable P) V *
        (T.1 ((L, V), u) - ateFunctional P) ^ 2 := by
  have hconvex : ConvexOn Real Set.univ (fun x : Real => (x - ateFunctional P) ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    dsimp
    have hid : a * (x - ateFunctional P) ^ 2 + b * (y - ateFunctional P) ^ 2 -
        (a * x + b * y - ateFunctional P) ^ 2 = a * b * (x - y) ^ 2 := by
      rw [show b = 1 - a by linarith]
      ring
    have hpos := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))
    linarith
  rw [comparisonAverageRule_true]
  simpa only [smul_eq_mul] using hconvex.map_sum_le
    (t := Finset.univ) (w := fun V : Fin m → AuxObs d => comparisonArrayWeight (auxTable P) V)
    (p := fun V => T.1 ((L, V), u))
    (fun V _ => by rw [comparisonArrayWeight_true]; exact ENNReal.toReal_nonneg)
    (comparisonArrayWeight_sum P m) (fun _ _ => Set.mem_univ _)

/-- [Under the stated inputs and conditions](hyp:T,P,n,m,d), Auxiliary conditional averaging cannot increase squared-error risk at any population.  This gives [the stated result](goal).-/
-- @node: comparisonAverageRule_risk_le
lemma comparisonAverageRule_risk_le {n m d : Nat} (T : Rule n m d) (P : DiscreteLaw d) :
    knownRuleRisk (comparisonAverageRule T) P ≤ ruleRisk T.1 P := by
  letI : IsProbabilityMeasure (obsLaw P) := by unfold obsLaw; infer_instance
  letI : IsProbabilityMeasure (labeledProductLaw P n) := by
    unfold labeledProductLaw; infer_instance
  letI : IsProbabilityMeasure (auxProductLaw P m) := by
    unfold auxProductLaw; infer_instance
  letI : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw; infer_instance
  letI : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  have hT := T.2.1
  have hsection (L : Fin n → Obs d) (V : Fin m → AuxObs d) :
      Integrable (fun u => (T.1 ((L, V), u) - ateFunctional P) ^ 2) seedLaw := by
    apply Causalean.Stat.mse_integrable_of_estimator_bound (M := 1)
      seedLaw (fun u => T.1 ((L, V), u)) (by fun_prop) (by norm_num)
    exact fun u => T.2.2 _
  have hfull : Integrable (fun z => (T.1 z - ateFunctional P) ^ 2)
      ((annotationLaw P n m).prod seedLaw) :=
    Causalean.Stat.mse_integrable_of_estimator_bound (M := 1) _ T.1 hT (by norm_num) T.2.2
  have havg : Integrable (fun z : (Fin n → Obs d) × Real =>
      (comparisonAverageRule T (z.1, auxTable P, z.2) - ateFunctional P) ^ 2)
      ((labeledProductLaw P n).prod seedLaw) := by
    have hm := comparisonAverageRule_measurable T
    exact Causalean.Stat.mse_integrable_of_estimator_bound (M := 1)
      ((labeledProductLaw P n).prod seedLaw)
      (fun z => comparisonAverageRule T (z.1, auxTable P, z.2))
      (hm.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
      (by norm_num) (fun z => comparisonAverageRule_mem_Icc T _)
  unfold knownRuleRisk ruleRisk
  rw [integral_prod _ havg, integral_prod _ hfull]
  change (∫ L, ∫ u, (comparisonAverageRule T (L, auxTable P, u) - ateFunctional P) ^ 2
      ∂seedLaw ∂labeledProductLaw P n) ≤
    ∫ LV, ∫ u, (T.1 (LV, u) - ateFunctional P) ^ 2 ∂seedLaw
      ∂((labeledProductLaw P n).prod (auxProductLaw P m))
  rw [integral_prod _ hfull.integral_prod_left]
  apply integral_mono havg.integral_prod_left
    hfull.integral_prod_left.integral_prod_left
  intro L
  calc
    (∫ u, (comparisonAverageRule T (L, auxTable P, u) - ateFunctional P) ^ 2 ∂seedLaw) ≤
        ∫ u, ∑ V : Fin m → AuxObs d, comparisonArrayWeight (auxTable P) V *
          (T.1 ((L, V), u) - ateFunctional P) ^ 2 ∂seedLaw := by
      apply integral_mono
      · apply Causalean.Stat.mse_integrable_of_estimator_bound (M := 1) _
          (fun u => comparisonAverageRule T (L, auxTable P, u))
          ((comparisonAverageRule_measurable T).comp
            (measurable_const.prodMk (measurable_const.prodMk measurable_id))) (by norm_num)
        exact fun u => comparisonAverageRule_mem_Icc T _
      · exact integrable_finsetSum _ fun V _ => (hsection L V).const_mul _
      · exact fun u => comparisonAverageRule_loss_le T P L u
    _ = ∑ V : Fin m → AuxObs d, comparisonArrayWeight (auxTable P) V *
        (∫ u, (T.1 ((L, V), u) - ateFunctional P) ^ 2 ∂seedLaw) := by
      rw [integral_finsetSum _ (fun V _ => (hsection L V).const_mul _)]
      simp only [integral_const_mul]
    _ = ∫ V, ∫ u, (T.1 ((L, V), u) - ateFunctional P) ^ 2
        ∂seedLaw ∂auxProductLaw P m := by
      rw [integral_fintype (by
        simpa using (IntegrableOn.of_finite (μ := auxProductLaw P m)
          (f := fun V => ∫ u, (T.1 ((L, V), u) - ateFunctional P) ^ 2 ∂seedLaw)
          (Set.finite_univ : (Set.univ : Set (Fin m → AuxObs d)).Finite)))]
      simp only [comparisonArrayWeight_true, smul_eq_mul]

/-- [Under the stated inputs and conditions](hyp:eps,hd,heps,heps',n,m,d), Conditional averaging proves that exact marginal information can only lower minimax risk.  This gives [the stated result](goal).-/
-- @node: comparison_known_le_minimax
lemma comparison_known_le_minimax (n m d : Nat) (eps : Real)
    (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    knownMarginalRisk n d eps ≤ minimaxRisk n m d eps := by
  let P0 : ClassLaw d eps :=
    ⟨labelFloorLaw d eps (1 / 8) false hd labelFloorAmplitude_eighth,
      labelFloor_model d eps (1 / 8) false hd labelFloorAmplitude_eighth heps heps'⟩
  letI : Nonempty (ClassLaw d eps) := ⟨P0⟩
  let T0 : Rule n m d := ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩
  letI : Nonempty (Rule n m d) := ⟨T0⟩
  change Causalean.Stat.minimaxValueReal
      (fun (T : KnownRule n d) (P : ClassLaw d eps) => knownRuleRisk T.1 P.1) ≤
    Causalean.Stat.minimaxValueReal
      (fun (T : Rule n m d) (P : ClassLaw d eps) => ruleRisk T.1 P.1)
  apply Causalean.Stat.minimaxValue_le_minimaxValue
    (Causalean.Stat.bddBelow_range_worstCaseRisk
      (fun T P => integral_nonneg (fun z => sq_nonneg _)))
  intro T
  let K : KnownRule n d := ⟨comparisonAverageRule T,
    comparisonAverageRule_measurable T, comparisonAverageRule_mem_Icc T⟩
  refine ⟨K, ?_⟩
  apply Causalean.Stat.worstCaseRisk_le
  intro P
  apply (comparisonAverageRule_risk_le T P.1).trans
  refine Causalean.Stat.le_worstCaseRisk
    (risk := fun (T : Rule n m d) (P : ClassLaw d eps) => ruleRisk T.1 P.1)
    (e := T) ?_ P
  refine ⟨4, ?_⟩
  rintro _ ⟨Q, rfl⟩
  letI : IsProbabilityMeasure (obsLaw Q.1) := by unfold obsLaw; infer_instance
  letI : IsProbabilityMeasure (annotationLaw Q.1 n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw; infer_instance
  letI : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  exact labelFloor_bounded_mse _ T.1 T.2.2 _ (ateFunctional_mem_Icc Q.1)

/-- [Under the stated inputs and conditions](hyp:eps,n,d), Squared loss makes the exact-marginal minimax value nonnegative.  This gives [the stated result](goal).-/
-- @node: comparison_known_nonneg
lemma comparison_known_nonneg (n d : Nat) (eps : Real) :
    0 ≤ knownMarginalRisk n d eps := by
  exact Causalean.Stat.minimaxValue_nonneg
    (fun (T : KnownRule n d) (P : ClassLaw d eps) => integral_nonneg (fun z => sq_nonneg _))

/-- [Under the stated inputs and conditions](hyp:eps,hd,heps,heps',n,m,d), The original zero rule gives the universal minimax cap of one.  This gives [the stated result](goal).-/
-- @node: comparison_minimax_le_one
lemma comparison_minimax_le_one (n m d : Nat) (eps : Real)
    (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    minimaxRisk n m d eps ≤ 1 := by
  let P0 : ClassLaw d eps :=
    ⟨labelFloorLaw d eps (1 / 8) false hd labelFloorAmplitude_eighth,
      labelFloor_model d eps (1 / 8) false hd labelFloorAmplitude_eighth heps heps'⟩
  letI : Nonempty (ClassLaw d eps) := ⟨P0⟩
  let T0 : Rule n m d := ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩
  apply (Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    (risk := fun (T : Rule n m d) (P : ClassLaw d eps) => ruleRisk T.1 P.1)
    (fun T P => integral_nonneg (fun z => sq_nonneg _)) T0).trans
  apply ciSup_le
  intro P
  letI : IsProbabilityMeasure (obsLaw P.1) := by unfold obsLaw; infer_instance
  letI : IsProbabilityMeasure (annotationLaw P.1 n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw; infer_instance
  letI : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  have ht := ateFunctional_mem_Icc P.1
  have hzero : ruleRisk T0.1 P.1 = (ateFunctional P.1) ^ 2 := by
    simp [ruleRisk, T0]
  change ruleRisk T0.1 P.1 ≤ 1
  rw [hzero]
  nlinarith [ht.1, ht.2]

/-- [Under the stated inputs and conditions](hyp:eps,hd,heps,heps',n,m,d), Both elementary endpoints of the experiment comparison hold for every auxiliary budget.  This gives [the stated result](goal).-/
-- @node: comparison_difference_bounds
lemma comparison_difference_bounds (n m d : Nat) (eps : Real)
    (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    0 ≤ minimaxRisk n m d eps - knownMarginalRisk n d eps ∧
      minimaxRisk n m d eps - knownMarginalRisk n d eps ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (comparison_known_le_minimax n m d eps hd heps heps')
  · have hcap := comparison_minimax_le_one n m d eps hd heps heps'
    have hnonneg := comparison_known_nonneg n d eps
    linarith

end CausalSmith.Stat.AnnotationRarearmFrontier
