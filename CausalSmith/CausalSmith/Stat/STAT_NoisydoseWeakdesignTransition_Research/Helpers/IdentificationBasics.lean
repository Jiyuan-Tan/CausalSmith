module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.MetricSpace.Holder
/-! Observed stratum identification, continuous potential means, and target decomposition. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]

/-- Joint schedule evaluation gives measurability at every public fixed dose. [Under the stated conditions](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: potentialOutcome_measurable
@[fun_prop] lemma potentialOutcome_measurable (E : PathSpace S) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) : Measurable (fun w : StructSpace S => potentialOutcome E w a) := by
  first
  | fun_prop
  | exact E.measurable_eval.comp
      (show Measurable (fun w : StructSpace S => (sSched w, (⟨a, ha⟩ : Dose))) by fun_prop)

/-- Bounded fixed-dose potential outcomes are integrable without an added premise. [Under the stated conditions](hyp:hbounded,ha). [This is the stated conclusion](goal). -/
lemma potentialOutcome_integrable (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hbounded : BoundedPotentialOutcomes E P)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : Integrable (fun w => potentialOutcome E w a) P := by
  apply (integrable_const (1 : ℝ)).mono'
    (potentialOutcome_measurable E a ha).aestronglyMeasurable
  filter_upwards [hbounded a ha] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg hw.1]
  exact hw.2

/-- With [bounded potential outcomes](hyp:hbounded), the potential mean at a
[dose in the public interval](hyp:ha), conditional on a [positive-mass stratum](hyp:hpos),
[lies between zero and one](goal). -/
lemma condPotMean_mem_Icc (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hbounded : BoundedPotentialOutcomes E P)
    (x : Bool) (hpos : 0 < strataProb P x) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    condPotMean E P x a ∈ Icc (0 : ℝ) 1 := by
  have hs : MeasurableSet {w : StructSpace S | sX w = x} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hi := (potentialOutcome_integrable E P hbounded a ha).restrict
      (s := {w : StructSpace S | sX w = x})
  have hb := ae_restrict_of_ae (s := {w : StructSpace S | sX w = x}) (hbounded a ha)
  unfold condPotMean
  have heq : (∫ w, (if sX w = x then potentialOutcome E w a else 0) ∂P) =
      ∫ w in {w : StructSpace S | sX w = x}, potentialOutcome E w a ∂P := by
    simpa only [Set.indicator, Set.mem_ofPred_eq] using
      (integral_indicator (f := fun w => potentialOutcome E w a) hs)
  rw [heq]
  constructor
  · exact div_nonneg (integral_nonneg_of_ae (hb.mono fun _ hw => hw.1)) hpos.le
  · apply (div_le_one hpos).2
    calc
      _ ≤ ∫ _ in {w : StructSpace S | sX w = x}, (1 : ℝ) ∂P :=
        integral_mono_ae hi (integrable_const 1) (hb.mono fun _ hw => hw.2)
      _ = strataProb P x := by simp [strataProb]

/-- Overlap makes each finite-stratum normalization strictly positive. [Under the stated condition](hyp:hoverlap). [This is the stated conclusion](goal). -/
-- @node: strataProb_pos
lemma strataProb_pos (P : Measure (StructSpace S))
    (hoverlap : StratumPositive P) (x : Bool) :
    0 < strataProb P x := hoverlap x

/-- Partitioning the fixed-dose potential expectation into the two positive strata gives its target formula. [Under the stated conditions](hyp:hoverlap,hbounded). [This is the stated conclusion](goal). -/
-- @node: causalTarget_eq_stratum_sum
lemma causalTarget_eq_stratum_sum (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (hoverlap : StratumPositive P)
    (hbounded : BoundedPotentialOutcomes E P) :
    causalTarget E P = ∑ x : Bool, strataProb P x * condPotMean E P x a0 := by
  have ha : a0 ∈ Icc (0 : ℝ) 1 := by norm_num [a0]
  have hi := potentialOutcome_integrable E P hbounded a0 ha
  have his (x : Bool) : Integrable
      (fun w => if sX w = x then potentialOutcome E w a0 else 0) P := by
    apply (hi.indicator (show MeasurableSet {w : StructSpace S | sX w = x}
      from measurableSet_eq_fun (by fun_prop) measurable_const)).congr
    filter_upwards with w
    by_cases hw : sX w = x <;> simp [hw]
  have heq (w : StructSpace S) : potentialOutcome E w a0 =
      ∑ x : Bool, if sX w = x then potentialOutcome E w a0 else 0 := by
    cases sX w <;> simp
  calc
    causalTarget E P = ∫ w, ∑ x : Bool, if sX w = x then potentialOutcome E w a0 else 0 ∂P := by
      exact integral_congr_ae (Eventually.of_forall heq)
    _ = ∑ x : Bool, ∫ w, (if sX w = x then potentialOutcome E w a0 else 0) ∂P :=
      integral_finsetSum Finset.univ (fun x _ => his x)
    _ = ∑ x : Bool, strataProb P x * condPotMean E P x a0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [condPotMean, mul_div_cancel₀ _ (ne_of_gt (strataProb_pos P hoverlap x))]

/-- The observed stratum marginal has exactly the structural stratum mass. [This is the stated conclusion](goal). -/
-- @node: obsLaw_stratum_mass
lemma obsLaw_stratum_mass (sigma : ℝ) (P : Measure (StructSpace S)) (x : Bool) :
    (obsLaw sigma P).real {o : Obs | o.1 = x} = strataProb P x := by
  have hm : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose
    fun_prop
  unfold obsLaw strataProb Measure.real
  rw [Measure.map_apply hm (show MeasurableSet {o : Obs | o.1 = x}
    from measurableSet_eq_fun (by fun_prop) measurable_const)]
  rfl

/-- Observational equivalence identifies the overlap probabilities directly from the marginal. [Under the stated conditions](hyp:hobs). [This is the stated conclusion](goal). -/
-- @node: strataProb_eq_of_obsLaw_eq
lemma strataProb_eq_of_obsLaw_eq (sigma : ℝ) (P P' : Measure (StructSpace S))
    (hobs : obsLaw sigma P = obsLaw sigma P') (x : Bool) : strataProb P x = strataProb P' x := by
  rw [← obsLaw_stratum_mass sigma P x, hobs, obsLaw_stratum_mass sigma P' x]

/-- Positive Holder exponent supplies continuity of the potential mean, including at the endpoints. [Under the stated conditions](hyp:hbeta,hholder). [This is the stated conclusion](goal). -/
-- @node: condPotMean_continuousOn
@[fun_prop] lemma condPotMean_continuousOn (E : PathSpace S) (beta : ℝ)
    (P : Measure (StructSpace S)) (hbeta : 0 < beta)
    (hholder : HolderMean E beta P) (x : Bool) :
    ContinuousOn (condPotMean E P x) (Icc (0 : ℝ) 1) := by
  have hh : HolderOnWith 1 ⟨beta, hbeta.le⟩ (condPotMean E P x) (Icc (0 : ℝ) 1) := by
    intro a ha b hb
    simp only [edist_dist, ENNReal.coe_one, one_mul]
    change ENNReal.ofReal (dist (condPotMean E P x a) (condPotMean E P x b)) ≤
      ENNReal.ofReal (dist a b) ^ beta
    rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hbeta.le]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.dist_eq] using hholder x a ha b hb)
  exact hh.continuousOn (by exact_mod_cast hbeta)

/-- Lebesgue almost-everywhere agreement of the two Holder versions identifies every public dose. [Under the stated conditions](hyp:hbeta,hholder,hholder',hae). [This is the stated conclusion](goal). -/
-- @node: condPotMean_eqOn_of_ae_eq
lemma condPotMean_eqOn_of_ae_eq (E : PathSpace S) (beta : ℝ)
    (P P' : Measure (StructSpace S)) (hbeta : 0 < beta)
    (hholder : HolderMean E beta P) (hholder' : HolderMean E beta P') (x : Bool)
    (hae : condPotMean E P x =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] condPotMean E P' x) :
    EqOn (condPotMean E P x) (condPotMean E P' x) (Icc (0 : ℝ) 1) := by
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hae
    (condPotMean_continuousOn E beta P hbeta hholder x)
    (condPotMean_continuousOn E beta P' hbeta hholder' x)

end CausalSmith.Stat.NoisydoseWeakdesignTransition
