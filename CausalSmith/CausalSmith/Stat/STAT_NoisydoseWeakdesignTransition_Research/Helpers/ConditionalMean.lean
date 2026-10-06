module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.IdentificationBasics
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.ScheduleFactorization
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-! Product integration of schedule evaluations and bounded regression tests. -/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]

/-- Normalized stratum integrals equal the corresponding indicator integrals divided by mass. [Under the stated conditions](hyp:f). [This is the stated conclusion](goal). -/
-- @node: stratumLaw_integral
lemma stratumLaw_integral (P : Measure (StructSpace S)) (x : Bool)
    (f : StructSpace S → ℝ) :
    (∫ w, f w ∂stratumLaw P x) =
      (∫ w, (if sX w = x then f w else 0) ∂P) / strataProb P x := by
  have hx : MeasurableSet {w : StructSpace S | sX w = x} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [stratumLaw, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  rw [← integral_indicator hx]
  simp only [strataProb, Measure.real, indicator_apply, mem_ofPred_eq, div_eq_mul_inv, mul_comm]

/-- The stratum coordinate is constant under its normalized stratum law. [This is the stated conclusion](goal). -/
-- @node: stratumLaw_ae_stratum
lemma stratumLaw_ae_stratum (P : Measure (StructSpace S)) (x : Bool) :
    ∀ᵐ w ∂stratumLaw P x, sX w = x := by
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (measurableSet_eq_fun (by fun_prop) measurable_const)

/-- Integrable population expectations split into the two normalized stratum expectations. [Under the stated conditions](hyp:hoverlap,f,hf). [This is the stated conclusion](goal). -/
-- @node: integral_eq_stratum_sum
lemma integral_eq_stratum_sum (P : Measure (StructSpace S))
    (hoverlap : StratumPositive P) (f : StructSpace S → ℝ) (hf : Integrable f P) :
    (∫ w, f w ∂P) = ∑ x : Bool, strataProb P x * ∫ w, f w ∂stratumLaw P x := by
  have hi (x : Bool) : Integrable (fun w => if sX w = x then f w else 0) P := by
    apply (hf.indicator (show MeasurableSet {w : StructSpace S | sX w = x} from
      measurableSet_eq_fun (by fun_prop) measurable_const)).congr
    filter_upwards [] with w
    by_cases hw : sX w = x <;> simp [hw]
  calc
    _ = ∫ w, ∑ x : Bool, if sX w = x then f w else 0 ∂P := by
      apply integral_congr_ae
      filter_upwards [] with w
      cases sX w <;> simp
    _ = ∑ x : Bool, ∫ w, (if sX w = x then f w else 0) ∂P :=
      integral_finsetSum _ (fun x _ => hi x)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [stratumLaw_integral, mul_div_cancel₀ _ (ne_of_gt (strataProb_pos P hoverlap x))]

/-- The projected potential mean is a globally measurable extension of its Holder version. -/
-- @node: projectedMean
def projectedMean (E : PathSpace S) (P : Measure (StructSpace S)) (a : ℝ) (x : Bool) : ℝ :=
  condPotMean E P x (Set.projIcc 0 1 zero_le_one a)

/-- Holder regularity makes the projected mean Borel in dose and stratum. [Under the stated conditions](hyp:hbeta,hholder). [This is the stated conclusion](goal). -/
-- @node: projectedMean_measurable
@[fun_prop] lemma projectedMean_measurable (E : PathSpace S) (P : Measure (StructSpace S))
    (beta : ℝ) (hbeta : 0 < beta) (hholder : HolderMean E beta P) :
    Measurable (fun p : ℝ × Bool => projectedMean E P p.1 p.2) := by
  have hc (x : Bool) : Continuous (fun a : ℝ => projectedMean E P a x) :=
    (condPotMean_continuousOn E beta P hbeta hholder x).comp_continuous
      ((continuous_projIcc (h := zero_le_one)).subtype_val) (fun a => (Set.projIcc 0 1 zero_le_one a).property)
  have heq : (fun p : ℝ × Bool => projectedMean E P p.1 p.2) =
      (fun p => if p.2 = false then projectedMean E P p.1 false else projectedMean E P p.1 true) := by
    funext p; cases p.2 <;> simp
  rw [heq]
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
    ((hc false).measurable.comp measurable_fst) ((hc true).measurable.comp measurable_fst)

/-- Projection preserves the public mean bound at every real input dose. [Under the stated conditions](hyp:hrange). [This is the stated conclusion](goal). -/
-- @node: projectedMean_mem_Icc
lemma projectedMean_mem_Icc (E : PathSpace S) (P : Measure (StructSpace S))
    (hrange : MeanRange E P) (a : ℝ) (x : Bool) : projectedMean E P a x ∈ Icc (0 : ℝ) 1 := by
  have h := hrange x _ (Set.projIcc 0 1 zero_le_one a).property
  constructor <;> dsimp [projectedMean] <;> linarith [h.1, h.2]

/-- Integrating a fixed schedule evaluation under its stratum marginal gives the potential mean. [This is the stated conclusion](goal). -/
-- @node: schedule_marginal_mean
lemma schedule_marginal_mean (E : PathSpace S) (P : Measure (StructSpace S))
    (x : Bool) (a : ℝ) :
    (∫ s, E.eval s (Set.projIcc 0 1 zero_le_one a) ∂(stratumLaw P x).map sSched) =
      projectedMean E P a x := by
  have hm : Measurable (fun s : S => E.eval s (Set.projIcc 0 1 zero_le_one a)) := by
    first | fun_prop | exact E.measurable_eval.comp (measurable_id.prodMk measurable_const)
  rw [integral_map (show Measurable (sSched (S := S)) by fun_prop).aemeasurable hm.aestronglyMeasurable,
    stratumLaw_integral]
  rfl

/-- Clipped joint evaluation is bounded everywhere and agrees with the schedule almost surely. -/
-- @node: boundedScheduleEval
def boundedScheduleEval (E : PathSpace S) (a : ℝ) (s : S) : ℝ :=
  max 0 (min 1 (E.eval s (Set.projIcc 0 1 zero_le_one a)))

/-- The clipped schedule evaluation is jointly Borel. [This is the stated conclusion](goal). -/
-- @node: boundedScheduleEval_measurable
@[fun_prop] lemma boundedScheduleEval_measurable (E : PathSpace S) :
    Measurable (fun p : ℝ × S => boundedScheduleEval E p.1 p.2) := by
  have hm : Measurable (fun p : ℝ × S => E.eval p.2 (Set.projIcc 0 1 zero_le_one p.1)) := by
    first
    | fun_prop
    | exact E.measurable_eval.comp
        (measurable_snd.prodMk ((continuous_projIcc (h := zero_le_one)).measurable.comp measurable_fst))
  exact measurable_const.max (measurable_const.min hm)

/-- Clipped schedule evaluations take values in the unit interval. [This is the stated conclusion](goal). -/
-- @node: boundedScheduleEval_mem_Icc
lemma boundedScheduleEval_mem_Icc (E : PathSpace S) (a : ℝ) (s : S) :
    boundedScheduleEval E a s ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Fixed-dose boundedness justifies replacing schedule evaluation by its clipped version. [Under the stated conditions](hyp:hbounded). [This is the stated conclusion](goal). -/
-- @node: boundedScheduleEval_marginal_mean
lemma boundedScheduleEval_marginal_mean (E : PathSpace S) (P : Measure (StructSpace S))
    (hbounded : BoundedPotentialOutcomes E P) (x : Bool) (a : ℝ) :
    (∫ s, boundedScheduleEval E a s ∂(stratumLaw P x).map sSched) =
      projectedMean E P a x := by
  rw [← schedule_marginal_mean]
  apply integral_congr_ae
  have hS : Measurable (sSched (S := S)) := by fun_prop
  have hm : Measurable (fun s : S => E.eval s (Set.projIcc 0 1 zero_le_one a)) := by
    first | fun_prop | exact E.measurable_eval.comp (measurable_id.prodMk measurable_const)
  have hb : ∀ᵐ s ∂(stratumLaw P x).map sSched,
      E.eval s (Set.projIcc 0 1 zero_le_one a) ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff hS.aemeasurable (hm measurableSet_Icc)).mpr
    exact ae_stratumLaw_of_ae P x (hbounded _ (Set.projIcc 0 1 zero_le_one a).property)
  filter_upwards [hb] with s hs
  dsimp [boundedScheduleEval]
  rw [min_eq_right hs.2, max_eq_right hs.1]

/-- Consistency and integrated fixed-dose bounds identify the clipped random evaluation with Y. [Under the stated conditions](hyp:hoverlap,hex,hsupport,hbounded,hcons). [This is the stated conclusion](goal). -/
-- @node: boundedScheduleEval_ae_outcome
lemma boundedScheduleEval_ae_outcome (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hoverlap : StratumPositive P)
    (hex : ScheduleUnconfoundedness P) (hsupport : LatentSupport P)
    (hbounded : BoundedPotentialOutcomes E P) (hcons : DoseConsistency E P) :
    (fun w => boundedScheduleEval E (sA w) (sSched w)) =ᵐ[P] sY := by
  filter_upwards [realized_potential_mem_Icc E P hoverlap hex hsupport hbounded,
    hsupport, hcons] with w hw ha hc
  dsimp [boundedScheduleEval]
  rw [Set.projIcc_of_mem zero_le_one ha, ← potentialOutcome,
    min_eq_right hw.2, max_eq_right hw.1, ← hc]

/-- Equation (3) follows by integrating the schedule coordinate in the conditional product law. [Under the stated conditions](hyp:hoverlap,hex,herr,hsupport,hbounded,hcons,hbeta,hholder,hrange,hF,hB). [This is the stated conclusion](goal). -/
-- @node: bounded_test_mean_stratum
lemma bounded_test_mean_stratum (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hoverlap : StratumPositive P)
    (hex : ScheduleUnconfoundedness P) (herr : ErrorIndependence P)
    (hsupport : LatentSupport P) (hbounded : BoundedPotentialOutcomes E P)
    (hcons : DoseConsistency E P) (beta : ℝ) (hbeta : 0 < beta)
    (hholder : HolderMean E beta P) (hrange : MeanRange E P) (x : Bool)
    (F : (ℝ × Bool × ℝ) → ℝ) (hF : Measurable F)
    (B : ℝ) (hB : ∀ p, |F p| ≤ B) :
    (∫ w, F (sA w, x, sZ w)*sY w ∂stratumLaw P x) =
      ∫ w, F (sA w, x, sZ w)*projectedMean E P (sA w) x ∂stratumLaw P x := by
  let R := stratumLaw P x
  let ζ := P.map sZ
  let γ := R.map sA
  let Λ := R.map sSched
  have : IsProbabilityMeasure R := stratumLaw_probability P hoverlap x
  have hZ : Measurable (sZ (S := S)) := by fun_prop
  have hA : Measurable (sA (S := S)) := by fun_prop
  have hS : Measurable (sSched (S := S)) := by fun_prop
  have : IsProbabilityMeasure ζ := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure γ := Measure.isProbabilityMeasure_map hA.aemeasurable
  have : IsProbabilityMeasure Λ := Measure.isProbabilityMeasure_map hS.aemeasurable
  let G : ℝ × ℝ × S → ℝ := fun p => F (p.2.1, x, p.1)*boundedScheduleEval E p.2.1 p.2.2
  have hG : Measurable G := by
    exact (hF.comp (by fun_prop)).mul
      ((boundedScheduleEval_measurable E).comp (by fun_prop))
  have hbound (p : ℝ × ℝ × S) : ‖G p‖ ≤ B := by
    have he := boundedScheduleEval_mem_Icc E p.2.1 p.2.2
    dsimp [G]
    rw [abs_mul, abs_of_nonneg he.1]
    exact (mul_le_mul_of_nonneg_left he.2 (abs_nonneg _)).trans (by simpa using hB (p.2.1, x, p.1))
  have hi : Integrable G (ζ.prod (γ.prod Λ)) := Integrable.of_bound hG.aestronglyMeasurable B (ae_of_all _ hbound)
  have hprod : R.map (fun w => (sZ w, sA w, sSched w)) = ζ.prod (γ.prod Λ) :=
    schedule_dose_error_product_stratum P hoverlap hex herr x
  have hleft : (∫ w, F (sA w, x, sZ w)*sY w ∂R) = ∫ p, G p ∂ζ.prod (γ.prod Λ) := by
    rw [← hprod, integral_map (hZ.prodMk (hA.prodMk hS)).aemeasurable hG.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [ae_stratumLaw_of_ae P x
      (boundedScheduleEval_ae_outcome E P hoverlap hex hsupport hbounded hcons)] with w hw
    dsimp [G]; rw [hw]
  rw [hleft, integral_prod _ hi]
  have hinner : ∀ᵐ z ∂ζ, Integrable (fun p : ℝ × S => G (z,p)) (γ.prod Λ) := hi.prod_right_ae
  have hreduce : (∫ z, ∫ p, G (z,p) ∂γ.prod Λ ∂ζ) =
      ∫ z, ∫ a, F (a,x,z)*projectedMean E P a x ∂γ ∂ζ := by
    apply integral_congr_ae
    filter_upwards [hinner] with z hz
    rw [integral_prod _ hz]
    apply integral_congr_ae
    filter_upwards [] with a
    dsimp [G]
    rw [integral_const_mul, boundedScheduleEval_marginal_mean E P hbounded x a]
  rw [hreduce]
  have hm : Measurable (fun p : ℝ × ℝ => F (p.2,x,p.1)*projectedMean E P p.2 x) := by
    exact (hF.comp (by fun_prop)).mul
      ((projectedMean_measurable E P beta hbeta hholder).comp
        (show Measurable (fun p : ℝ × ℝ => (p.2,x)) by fun_prop))
  have hmean : Integrable (fun p : ℝ × ℝ => F (p.2,x,p.1)*projectedMean E P p.2 x) (ζ.prod γ) := by
    apply Integrable.of_bound hm.aestronglyMeasurable B
    filter_upwards [] with p
    have he := projectedMean_mem_Icc E P hrange p.2 x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he.1]
    exact (mul_le_mul_of_nonneg_left he.2 (abs_nonneg _)).trans (by simpa using hB (p.2,x,p.1))
  rw [← integral_prod _ hmean]
  have hmap : R.map (fun w => (sZ w,sA w)) = ζ.prod γ := by
    have hh := congrArg (Measure.map (fun p : ℝ × ℝ × S => (p.1,p.2.1))) hprod
    rw [Measure.map_map (show Measurable (fun p : ℝ × ℝ × S => (p.1,p.2.1)) by fun_prop)
      (hZ.prodMk (hA.prodMk hS))] at hh
    change R.map (fun w => (sZ w,sA w)) =
      (ζ.prod (γ.prod Λ)).map (Prod.map id Prod.fst) at hh
    rw [← Measure.map_prod_map ζ (γ.prod Λ) measurable_id measurable_fst,
      Measure.map_id, Measure.map_fst_prod, measure_univ, one_smul] at hh
    exact hh
  rw [← hmap, integral_map (hZ.prodMk hA).aemeasurable (hm.aestronglyMeasurable)]

/-- The projected random-dose mean is measurable under the population law. [Under the stated conditions](hyp:hbeta,hholder). [This is the stated conclusion](goal). -/
-- @node: projectedMean_random_measurable
@[fun_prop] lemma projectedMean_random_measurable (E : PathSpace S)
    (P : Measure (StructSpace S)) (beta : ℝ) (hbeta : 0 < beta)
    (hholder : HolderMean E beta P) :
    Measurable (fun w : StructSpace S => projectedMean E P (sA w) (sX w)) := by
  fun_prop

/-- The globally projected mean is integrable by the public range bound. [Under the stated conditions](hyp:hbeta,hholder,hrange). [This is the stated conclusion](goal). -/
-- @node: projectedMean_random_integrable
lemma projectedMean_random_integrable (E : PathSpace S)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (beta : ℝ) (hbeta : 0 < beta) (hholder : HolderMean E beta P)
    (hrange : MeanRange E P) :
    Integrable (fun w => projectedMean E P (sA w) (sX w)) P := by
  apply Integrable.of_bound
    (by first | fun_prop | exact (projectedMean_random_measurable E P beta hbeta hholder).aestronglyMeasurable) 1
  filter_upwards [] with w
  have hm := projectedMean_mem_Icc E P hrange (sA w) (sX w)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hm.1] using hm.2

/-- Summing equation (3) over the two strata gives the bounded-test characterization. [Under the stated conditions](hyp:hbeta,hP,hF,hB). [This is the stated conclusion](goal). -/
-- @node: bounded_test_mean
lemma bounded_test_mean (E : PathSpace S) (beta kappa sigma : ℝ)
    (hbeta : 0 < beta) (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (F : (ℝ × Bool × ℝ) → ℝ) (hF : Measurable F)
    (B : ℝ) (hB : ∀ p, |F p| ≤ B) :
    (∫ w, F (sA w,sX w,sZ w)*sY w ∂P) =
      ∫ w, F (sA w,sX w,sZ w)*projectedMean E P (sA w) (sX w) ∂P := by
  have hfm : Measurable (fun w : StructSpace S => F (sA w,sX w,sZ w)) := by fun_prop
  have hiY : Integrable (fun w => F (sA w,sX w,sZ w)*sY w) P := by
    apply Integrable.of_bound (by fun_prop) B
    filter_upwards [realized_outcome_mem_Icc E P hP.strataPos
      hP.scheduleUnconfoundedness hP.latentSupport hP.boundedPO hP.consistency] with w hw
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1]
    exact (mul_le_mul_of_nonneg_left hw.2 (abs_nonneg _)).trans (by simpa using hB (sA w,sX w,sZ w))
  have hmeanm := projectedMean_random_measurable E P beta hbeta hP.holderMean
  have hiM : Integrable (fun w => F (sA w,sX w,sZ w)*projectedMean E P (sA w) (sX w)) P := by
    apply Integrable.of_bound (by fun_prop) B
    filter_upwards [] with w
    have hm := projectedMean_mem_Icc E P hP.meanRange (sA w) (sX w)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm.1]
    exact (mul_le_mul_of_nonneg_left hm.2 (abs_nonneg _)).trans (by simpa using hB (sA w,sX w,sZ w))
  rw [integral_eq_stratum_sum P hP.strataPos _ hiY,
    integral_eq_stratum_sum P hP.strataPos _ hiM]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  calc
    _ = ∫ w, F (sA w,x,sZ w)*sY w ∂stratumLaw P x := by
      apply integral_congr_ae
      filter_upwards [stratumLaw_ae_stratum P x] with w hw
      rw [hw]
    _ = ∫ w, F (sA w,x,sZ w)*projectedMean E P (sA w) x ∂stratumLaw P x :=
      bounded_test_mean_stratum E P hP.strataPos hP.scheduleUnconfoundedness
        hP.errorIndependence hP.latentSupport hP.boundedPO hP.consistency
        beta hbeta hP.holderMean hP.meanRange x F hF B hB
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [stratumLaw_ae_stratum P x] with w hw
      rw [hw]

/-- Bounded Borel tests characterize the conditional mean on a generated sigma algebra. [Under the stated conditions](hyp:H,hH,f,hf,g,hgm,hgi,htests). [This is the stated conclusion](goal). -/
-- @node: condExp_eq_of_bounded_tests
lemma condExp_eq_of_bounded_tests {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Ω → T) (hH : Measurable H)
    (f : Ω → ℝ) (hf : Integrable f P) (g : T → ℝ) (hgm : Measurable g)
    (hgi : Integrable (g ∘ H) P)
    (htests : ∀ F : T → ℝ, Measurable F → (∃ B : ℝ, ∀ z, |F z| ≤ B) →
      (∫ w, F (H w)*f w ∂P) = ∫ w, F (H w)*g (H w) ∂P) :
    P[f | MeasurableSpace.comap H inferInstance] =ᵐ[P] g ∘ H := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq hH.comap_le hf
    (fun _ _ _ => hgi.integrableOn) ?_
    ((hgm.comp (comap_measurable H)).aestronglyMeasurable)).symm
  intro s hs _
  obtain ⟨B,hB,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hb : ∃ C : ℝ, ∀ z, |B.indicator (fun _ => (1 : ℝ)) z| ≤ C := by
    refine ⟨1, ?_⟩
    intro z
    by_cases hz : z ∈ B <;> simp [hz]
  have ht := htests (B.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hB) hb
  have heq (u : Ω → ℝ) : (fun w => B.indicator (fun _ => (1 : ℝ)) (H w)*u w) =
      (H ⁻¹' B).indicator u := by
    funext w
    by_cases hw : H w ∈ B <;> simp [hw]
  rw [heq f, heq (fun w => g (H w)), integral_indicator (hH hB), integral_indicator (hH hB)] at ht
  exact ht.symm

end CausalSmith.Stat.NoisydoseWeakdesignTransition
