module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Estimators
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.ReferenceLaw
public import Causalean.Stat.Minimax.TotalVariation

/-!
# Separate risk and connected-length testing reductions

The two reductions retain the realized causal target and charge exceptional
prior mass explicitly. The independent seed preserves total variation.
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

section PriorTesting

variable {V Ξ : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace Ξ]

/-- [The common independent seed has unit mass.](goal) -/
-- @node: separated_seed_probability
lemma separated_seed_probability : IsProbabilityMeasure seedLaw := by
  constructor
  simp [seedLaw, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.seedLaw,
    Real.volume_Icc]

/-- Given [the stated assumptions](hyp:hqr), [The fixed-population seeded law is the product of the record law and seed.](goal) -/
-- @node: separated_recordLaw_eq_prod
lemma separated_recordLaw_eq_prod (q r : ℝ) (hqr : ChannelDomain q r) (η : Schedule V) :
    recordLaw (noisyDesign q r) η =
      ((noisyDesign q r η).map (recordOf η)).prod seedLaw := by
  let := noisyDesign_probability q r hqr η
  let := separated_seed_probability
  simpa only [Measure.map_id, recordLaw, Prod.map_def, id_eq] using
    (Measure.map_prod_map (noisyDesign q r η) seedLaw
      (recordOf_measurable η) measurable_id).symm

/-- Given [the stated assumptions](hyp:hqr,hm), [A measurable mixture of full-record probability channels has unit mass.](goal) -/
-- @node: separated_mixture_probability
lemma separated_mixture_probability (q r : ℝ) (hqr : ChannelDomain q r)
    (π : Measure Ξ) [IsProbabilityMeasure π] (s : Ξ → Schedule V)
    (hm : Measurable (fun ξ => (noisyDesign q r (s ξ)).map (recordOf (s ξ)))) :
    IsProbabilityMeasure (mixtureRecordLaw q r π s) := by
  unfold mixtureRecordLaw
  apply isProbabilityMeasure_bind hm.aemeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    let := noisyDesign_probability q r hqr (s ξ)
    exact Measure.isProbabilityMeasure_map (recordOf_measurable (s ξ)).aemeasurable

/-- Given [the stated assumptions](hyp:hqr,hf,f,hm), [Nonnegative seeded statistics average over the original fixed-population laws.](goal) -/
-- @node: separated_mixture_lintegral
lemma separated_mixture_lintegral (q r : ℝ) (hqr : ChannelDomain q r)
    (π : Measure Ξ) [IsProbabilityMeasure π] (s : Ξ → Schedule V)
    (hm : Measurable (fun ξ => (noisyDesign q r (s ξ)).map (recordOf (s ξ))))
    (f : Record V × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂(mixtureRecordLaw q r π s).prod seedLaw) =
      ∫⁻ ξ, ∫⁻ x, f x ∂recordLaw (noisyDesign q r) (s ξ) ∂π := by
  let := separated_seed_probability
  let := separated_mixture_probability q r hqr π s hm
  rw [lintegral_prod _ hf.aemeasurable]
  unfold mixtureRecordLaw
  rw [Measure.lintegral_bind hm.aemeasurable hf.lintegral_prod_right'.aemeasurable]
  apply lintegral_congr
  intro ξ
  rw [separated_recordLaw_eq_prod q r hqr]
  let := noisyDesign_probability q r hqr (s ξ)
  let : IsProbabilityMeasure ((noisyDesign q r (s ξ)).map (recordOf (s ξ))) :=
    Measure.isProbabilityMeasure_map (recordOf_measurable (s ξ)).aemeasurable
  exact (lintegral_prod _ hf.aemeasurable).symm

/-- Given [the stated assumptions](hyp:hqr,hE,hm), [Event probabilities in the seeded mixture average fixed-population probabilities.](goal) -/
-- @node: separated_mixture_apply
lemma separated_mixture_apply (q r : ℝ) (hqr : ChannelDomain q r)
    (π : Measure Ξ) [IsProbabilityMeasure π] (s : Ξ → Schedule V)
    (hm : Measurable (fun ξ => (noisyDesign q r (s ξ)).map (recordOf (s ξ))))
    (E : Set (Record V × ℝ)) (hE : MeasurableSet E) :
    ((mixtureRecordLaw q r π s).prod seedLaw) E =
      ∫⁻ ξ, recordLaw (noisyDesign q r) (s ξ) E ∂π := by
  simpa only [lintegral_indicator_const hE, one_mul] using
    separated_mixture_lintegral q r hqr π s hm (E.indicator (fun _ => 1))
      (measurable_const.indicator hE)

/-- Given [the stated assumptions](hyp:hqr,hE,hB,hc,hε,hbad,R,hm,hcost), [Averaging an event cost charges only its declared exceptional prior mass.](goal) -/
-- @node: separated_mixture_event_bound
lemma separated_mixture_event_bound (q r : ℝ) (hqr : ChannelDomain q r)
    (π : Measure Ξ) [IsProbabilityMeasure π] (s : Ξ → Schedule V)
    (hm : Measurable (fun ξ => (noisyDesign q r (s ξ)).map (recordOf (s ξ))))
    (E : Set (Record V × ℝ)) (hE : MeasurableSet E)
    (B : Set Ξ) (hB : MeasurableSet B) (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hbad : π.real B ≤ ε) (R : ℝ≥0∞)
    (hcost : ∀ᵐ ξ ∂π, ENNReal.ofReal c * recordLaw (noisyDesign q r) (s ξ) E ≤
      R + ENNReal.ofReal c * B.indicator (fun _ => (1 : ℝ≥0∞)) ξ) :
    ENNReal.ofReal c * ((mixtureRecordLaw q r π s).prod seedLaw) E ≤
      R + ENNReal.ofReal c * ENNReal.ofReal ε := by
  rw [separated_mixture_apply q r hqr π s hm E hE,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ∫⁻ ξ, R + ENNReal.ofReal c * B.indicator (fun _ => (1 : ℝ≥0∞)) ξ ∂π :=
      lintegral_mono_ae hcost
    _ = R + ENNReal.ofReal c * π B := by
      rw [lintegral_add_left measurable_const,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_const hB]
      simp
    _ ≤ _ := by
      gcongr
      exact (ofReal_measureReal (μ := π) (s := B)).symm.trans_le
        (ENNReal.ofReal_le_ofReal hbad)

/-- Given [the stated assumptions](hyp:hqr,ha), [On a nonexceptional target, a wrong sign costs at least the squared separation.](goal) -/
-- @node: separated_fixed_sign_cost
lemma separated_fixed_sign_cost (q r : ℝ) (hqr : ChannelDomain q r)
    (η : Schedule V) (T : Estimator V) (a : ℝ) (ha : 0 ≤ a) (σ : Bool) :
    ENNReal.ofReal (a^2) * recordLaw (noisyDesign q r) η
      (if σ then {x | T.1 x < 0} else {x | T.1 x < 0}ᶜ) ≤
    sqLoss (noisyDesign q r) η T + ENNReal.ofReal (a^2) *
      (if (if σ then
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η < a
        else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η)
      then 1 else 0) := by
  let θ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η
  let E : Set (Record V × ℝ) := if σ then {x | T.1 x < 0} else {x | T.1 x < 0}ᶜ
  have hE : MeasurableSet E := by
    have h : MeasurableSet {x | T.1 x < 0} := measurableSet_lt T.2.1 measurable_const
    cases σ
    · exact h.compl
    · exact h
  let := recordLaw_probability (noisyDesign q r) η (noisyDesign_probability q r hqr η)
  by_cases hb : (if σ then θ < a else -a < θ)
  · simp only [show (if σ then
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η < a
        else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η) from hb,
      ↓reduceIte, mul_one]
    exact (show ENNReal.ofReal (a^2) * recordLaw (noisyDesign q r) η E ≤
        ENNReal.ofReal (a^2) from by
      simpa using mul_le_mul' (le_refl (ENNReal.ofReal (a^2)))
        (prob_le_one (μ := recordLaw (noisyDesign q r) η))).trans
      (by simp)
  · have hpoint : ∀ x ∈ E, a^2 ≤ (T.1 x - θ)^2 := by
      intro x hx
      cases σ
      · have ht : 0 ≤ T.1 x := by simpa [E] using hx
        have hθ : θ ≤ -a := by simpa using hb
        nlinarith [sq_nonneg (T.1 x - θ - a)]
      · have ht : T.1 x < 0 := by simpa [E] using hx
        have hθ : a ≤ θ := by simpa using hb
        nlinarith [sq_nonneg (θ - T.1 x - a)]
    simp only [show ¬(if σ then
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η < a
        else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η) from hb,
      ↓reduceIte, mul_zero, add_zero]
    rw [← lintegral_indicator_const hE]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (hpoint x hx)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le

/-- Given [the stated assumptions](hyp:hqr,ha,hε,hm,ht,hclass,hbad), [Prior sign error is paid for by worst squared risk and exceptional target mass.](goal) -/
-- @node: separated_prior_sign_error
lemma separated_prior_sign_error (q r : ℝ) (hqr : ChannelDomain q r)
    (π : Measure Ξ) [IsProbabilityMeasure π] (s : Ξ → Schedule V)
    (hm : Measurable (fun ξ => (noisyDesign q r (s ξ)).map (recordOf (s ξ))))
    (ht : Measurable (fun ξ => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ)))
    (d : ℕ) (hclass : ∀ᵐ ξ ∂π, ScheduleClass (s ξ) d)
    (T : Estimator V) (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε) (σ : Bool)
    (hbad : π.real {ξ | if σ then
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ) < a
        else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ)} ≤ ε) :
    ENNReal.ofReal (a^2) * ((mixtureRecordLaw q r π s).prod seedLaw)
      (if σ then {x | T.1 x < 0} else {x | T.1 x < 0}ᶜ) ≤
      worstRisk (noisyDesign q r) d T + ENNReal.ofReal (a^2) * ENNReal.ofReal ε := by
  have hE : MeasurableSet {x | T.1 x < 0} := measurableSet_lt T.2.1 measurable_const
  have hB : MeasurableSet {ξ | if σ then
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ) < a
        else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ)} := by
    cases σ
    · exact measurableSet_lt measurable_const ht
    · exact measurableSet_lt ht measurable_const
  apply separated_mixture_event_bound q r hqr π s hm _
    (by
      cases σ
      · exact hE.compl
      · exact hE) _ hB (a^2) ε (sq_nonneg a) hε hbad
  filter_upwards [hclass] with ξ hξ
  have hcost := separated_fixed_sign_cost q r hqr (s ξ) T a ha σ
  have hsup : sqLoss (noisyDesign q r) (s ξ) T ≤ worstRisk (noisyDesign q r) d T :=
    le_iSup (fun η : {η : Schedule V // ScheduleClass η d} =>
      sqLoss (noisyDesign q r) η.1 T) ⟨s ξ, hξ⟩
  exact hcost.trans (add_le_add hsup (by
    by_cases h : (if σ then
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ) < a
      else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ))
    · simp [h]
    · simp [h]))

/-- Given [the stated assumptions](hyp:hE,hε,hτ,R,hP,hM), [Two sign errors and their explicit exceptional masses imply the squared-risk bound.](goal) -/
-- @node: separated_sign_testing_risk
lemma separated_sign_testing_risk {X : Type*} [MeasurableSpace X]
    (P M : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure M]
    (E : Set X) (hE : MeasurableSet E) (a ε τ : ℝ) (hε : 0 ≤ ε)
    (hτ : Causalean.Stat.tvDist P M ≤ τ) (R : ℝ≥0∞)
    (hP : ENNReal.ofReal (a^2) * P E ≤ R + ENNReal.ofReal (a^2) * ENNReal.ofReal ε)
    (hM : ENNReal.ofReal (a^2) * M Eᶜ ≤ R + ENNReal.ofReal (a^2) * ENNReal.ofReal ε) :
    ENNReal.ofReal (a^2/2*(1-τ-2*ε)) ≤ R := by
  by_cases hR : R = ⊤
  · simp [hR]
  have htest : ENNReal.ofReal (1-τ) ≤ P E + M Eᶜ := by
    have h := ENNReal.ofReal_le_ofReal
      ((sub_le_sub_left hτ 1).trans (Causalean.Stat.one_sub_tvDist_le_test hE))
    rwa [ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg,
      ofReal_measureReal, ofReal_measureReal] at h
  have hsum : ENNReal.ofReal (a^2) * ENNReal.ofReal (1-τ) ≤
      (R + ENNReal.ofReal (a^2) * ENNReal.ofReal ε) +
      (R + ENNReal.ofReal (a^2) * ENNReal.ofReal ε) := by
    calc
      _ ≤ ENNReal.ofReal (a^2) * (P E + M Eᶜ) := mul_le_mul' le_rfl htest
      _ ≤ _ := by rw [mul_add]; exact add_le_add hP hM
  have hfin : R + ENNReal.ofReal (a^2) * ENNReal.ofReal ε ≠ ⊤ := by finiteness
  have hreal := ENNReal.toReal_mono (by finiteness) hsum
  rw [ENNReal.toReal_add hfin hfin, ENNReal.toReal_add hR (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg a), ENNReal.toReal_ofReal hε] at hreal
  have hpos : 1-τ ≤ (ENNReal.ofReal (1-τ)).toReal := by
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  apply (ENNReal.ofReal_le_iff_le_toReal hR).mpr
  nlinarith [mul_le_mul_of_nonneg_left hpos (sq_nonneg a)]

/-- Given [the stated assumptions](hyp:hqr,ha,hε,hmP,hmM,htP,htM,hclassP,hclassM,hsepP,hsepM,hτ), [Exceptional-target priors give the full-record minimax squared-risk lower bound.](goal) -/
-- @node: separated_prior_risk
lemma separated_prior_risk
    {ΞP ΞM : Type*} [MeasurableSpace ΞP] [MeasurableSpace ΞM]
    (q r : ℝ) (hqr : ChannelDomain q r) (d : ℕ)
    (πP : Measure ΞP) (πM : Measure ΞM) [IsProbabilityMeasure πP] [IsProbabilityMeasure πM]
    (sP : ΞP → Schedule V) (sM : ΞM → Schedule V)
    (hmP : Measurable (fun ξ => (noisyDesign q r (sP ξ)).map (recordOf (sP ξ))))
    (hmM : Measurable (fun ξ => (noisyDesign q r (sM ξ)).map (recordOf (sM ξ))))
    (htP : Measurable (fun ξ => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sP ξ)))
    (htM : Measurable (fun ξ => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sM ξ)))
    (a ε τ : ℝ) (ha : 0 < a) (hε : 0 ≤ ε)
    (hclassP : ∀ᵐ ξ ∂πP, ScheduleClass (sP ξ) d)
    (hclassM : ∀ᵐ ξ ∂πM, ScheduleClass (sM ξ) d)
    (hsepP : πP.real {ξ | CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sP ξ) < a} ≤ ε)
    (hsepM : πM.real {ξ | -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sM ξ)} ≤ ε)
    (hτ : Causalean.Stat.tvDist (mixtureRecordLaw q r πP sP) (mixtureRecordLaw q r πM sM) ≤ τ) :
    ENNReal.ofReal (a^2/2*(1-τ-2*ε)) ≤ minimaxRisk (noisyDesign (V := V) q r) d := by
  let := separated_seed_probability
  let := separated_mixture_probability q r hqr πP sP hmP
  let := separated_mixture_probability q r hqr πM sM hmM
  have htv : Causalean.Stat.tvDist
      ((mixtureRecordLaw q r πP sP).prod seedLaw)
      ((mixtureRecordLaw q r πM sM).prod seedLaw) ≤ τ := by
    simpa using (Causalean.Stat.tvDist_compProd_eq
      (mixtureRecordLaw q r πP sP) (mixtureRecordLaw q r πM sM)
      (ProbabilityTheory.Kernel.const _ seedLaw)).trans_le hτ
  change _ ≤ ⨅ T : Estimator V, worstRisk (noisyDesign q r) d T
  apply le_iInf
  intro T
  have hP := separated_prior_sign_error q r hqr πP sP hmP htP d hclassP T a ε ha.le hε true hsepP
  have hM := separated_prior_sign_error q r hqr πM sM hmM htM d hclassM T a ε ha.le hε false hsepM
  exact separated_sign_testing_risk _ _ {x | T.1 x < 0}
    (measurableSet_lt T.2.1 measurable_const) a ε τ hε htv _ hP hM

/-- Given [the stated assumptions](hyp:hqr,hη,hI), [Honesty forces a separated target to be reached by the appropriate endpoint.](goal) -/
-- @node: separated_fixed_interval_miss
lemma separated_fixed_interval_miss (q r : ℝ) (hqr : ChannelDomain q r)
    (d : ℕ) (I : IntervalProc V) (hI : Honest (noisyDesign q r) d I)
    (η : Schedule V) (hη : ScheduleClass η d) (a : ℝ) (σ : Bool) :
    recordLaw (noisyDesign q r) η
      {x | if σ then a ≤ (I.1 x).2 else (I.1 x).1 ≤ -a}ᶜ ≤
      ENNReal.ofReal (1/10) +
      (if (if σ then CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η < a
        else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η)
        then 1 else 0) := by
  let θ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η
  let E : Set (Record V × ℝ) := {x | if σ then a ≤ (I.1 x).2 else (I.1 x).1 ≤ -a}
  have hE : MeasurableSet E := by
    cases σ
    · exact measurableSet_le I.2.1.fst measurable_const
    · exact measurableSet_le measurable_const I.2.1.snd
  let := recordLaw_probability (noisyDesign q r) η (noisyDesign_probability q r hqr η)
  by_cases hb : (if σ then θ < a else -a < θ)
  · simp only [show (if σ then CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η < a
        else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η) from hb,
      ↓reduceIte]
    exact (prob_le_one (μ := recordLaw (noisyDesign q r) η)).trans (by simp)
  · have hcover : ENNReal.ofReal (9/10) ≤ recordLaw (noisyDesign q r) η E := by
      apply (hI η hη).trans
      apply measure_mono
      intro x hx
      cases σ
      · have hθ : θ ≤ -a := by simpa using hb
        exact hx.1.trans hθ
      · have hθ : a ≤ θ := by simpa using hb
        exact hθ.trans hx.2
    simp only [show ¬(if σ then CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η < a
        else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η) from hb,
      ↓reduceIte, add_zero]
    rw [measure_compl hE (measure_ne_top _ _), measure_univ]
    apply tsub_le_iff_right.mpr
    calc
      (1 : ℝ≥0∞) = ENNReal.ofReal (1/10) + ENNReal.ofReal (9/10) := by
        rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1/10)
          (by norm_num : (0 : ℝ) ≤ 9/10)]
        norm_num
      _ ≤ _ := add_le_add le_rfl hcover

/-- Given [the stated assumptions](hyp:hqr,hε,hm,ht,hclass,hI,hbad), [Averaging population-wise honesty loses only the exceptional prior mass.](goal) -/
-- @node: separated_prior_interval_event
lemma separated_prior_interval_event (q r : ℝ) (hqr : ChannelDomain q r)
    (π : Measure Ξ) [IsProbabilityMeasure π] (s : Ξ → Schedule V)
    (hm : Measurable (fun ξ => (noisyDesign q r (s ξ)).map (recordOf (s ξ))))
    (ht : Measurable (fun ξ => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ)))
    (d : ℕ) (hclass : ∀ᵐ ξ ∂π, ScheduleClass (s ξ) d)
    (I : IntervalProc V) (hI : Honest (noisyDesign q r) d I)
    (a ε : ℝ) (hε : 0 ≤ ε) (σ : Bool)
    (hbad : π.real {ξ | if σ then
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ) < a
        else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ)} ≤ ε) :
    9/10-ε ≤ ((mixtureRecordLaw q r π s).prod seedLaw).real
      {x | if σ then a ≤ (I.1 x).2 else (I.1 x).1 ≤ -a} := by
  let E : Set (Record V × ℝ) := {x | if σ then a ≤ (I.1 x).2 else (I.1 x).1 ≤ -a}
  let B : Set Ξ := {ξ | if σ then
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ) < a
        else -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (s ξ)}
  have hE : MeasurableSet E := by
    cases σ
    · exact measurableSet_le I.2.1.fst measurable_const
    · exact measurableSet_le measurable_const I.2.1.snd
  have hB : MeasurableSet B := by
    cases σ
    · exact measurableSet_lt measurable_const ht
    · exact measurableSet_lt ht measurable_const
  have hcost : ∀ᵐ ξ ∂π, ENNReal.ofReal 1 * recordLaw (noisyDesign q r) (s ξ) Eᶜ ≤
      ENNReal.ofReal (1/10) + ENNReal.ofReal 1 * B.indicator (fun _ => (1 : ℝ≥0∞)) ξ := by
    filter_upwards [hclass] with ξ hξ
    have h := separated_fixed_interval_miss q r hqr d I hI (s ξ) hξ a σ
    simpa only [ENNReal.ofReal_one, one_mul, Set.indicator, E, B, Set.mem_ofPred_eq] using h
  have h := separated_mixture_event_bound q r hqr π s hm Eᶜ hE.compl B hB
    1 ε (by norm_num) hε hbad (ENNReal.ofReal (1/10)) hcost
  simp only [ENNReal.ofReal_one, one_mul] at h
  have hreal := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/10), ENNReal.toReal_ofReal hε] at hreal
  let := separated_seed_probability
  let := separated_mixture_probability q r hqr π s hm
  have hcomp := measureReal_compl (μ := (mixtureRecordLaw q r π s).prod seedLaw) hE
  simp only [probReal_univ] at hcomp
  change 9/10-ε ≤ ((mixtureRecordLaw q r π s).prod seedLaw).real E
  change ((mixtureRecordLaw q r π s).prod seedLaw).real Eᶜ ≤ 1/10+ε at hreal
  linarith

/-- Given [the stated assumptions](hyp:hqr,hm,hclass), [Prior averaging of connected length is bounded by its fixed-population supremum.](goal) -/
-- @node: separated_mixture_length_le_worst
lemma separated_mixture_length_le_worst (q r : ℝ) (hqr : ChannelDomain q r)
    (π : Measure Ξ) [IsProbabilityMeasure π] (s : Ξ → Schedule V)
    (hm : Measurable (fun ξ => (noisyDesign q r (s ξ)).map (recordOf (s ξ))))
    (d : ℕ) (hclass : ∀ᵐ ξ ∂π, ScheduleClass (s ξ) d) (I : IntervalProc V) :
    (∫⁻ x, ENNReal.ofReal ((I.1 x).2 - (I.1 x).1)
      ∂(mixtureRecordLaw q r π s).prod seedLaw) ≤ worstLength (noisyDesign q r) d I := by
  have hf : Measurable (fun x => ENNReal.ofReal ((I.1 x).2 - (I.1 x).1)) := by
    exact (I.2.1.snd.sub I.2.1.fst).ennreal_ofReal
  rw [separated_mixture_lintegral q r hqr π s hm _ hf]
  calc
    _ ≤ ∫⁻ _ξ, worstLength (noisyDesign q r) d I ∂π := by
      apply lintegral_mono_ae
      filter_upwards [hclass] with ξ hξ
      exact le_iSup (fun η : {η : Schedule V // ScheduleClass η d} =>
        expLength (noisyDesign q r) η.1 I) ⟨s ξ, hξ⟩
    _ = _ := by simp

omit [Fintype V] [DecidableEq V] in
/-- Given [the stated assumptions](hyp:ha,hτ,hP,hM), [Two likely endpoint events, transferred by TV, force connected interval length.](goal) -/
-- @node: separated_interval_testing_length
lemma separated_interval_testing_length (P M : Measure (Record V × ℝ))
    [IsProbabilityMeasure P] [IsProbabilityMeasure M] (I : IntervalProc V)
    (a ε τ : ℝ) (ha : 0 ≤ a)
    (hP : 9/10-ε ≤ P.real {x | a ≤ (I.1 x).2})
    (hM : 9/10-ε ≤ M.real {x | (I.1 x).1 ≤ -a})
    (hτ : Causalean.Stat.tvDist P M ≤ τ) :
    ENNReal.ofReal (2*a*((80/100 : ℝ)-τ-2*ε)) ≤
      ∫⁻ x, ENNReal.ofReal ((I.1 x).2 - (I.1 x).1) ∂P := by
  let E : Set (Record V × ℝ) := {x | a ≤ (I.1 x).2}
  let F : Set (Record V × ℝ) := {x | (I.1 x).1 ≤ -a}
  have hE : MeasurableSet E := measurableSet_le measurable_const I.2.1.snd
  have hF : MeasurableSet F := measurableSet_le I.2.1.fst measurable_const
  have htransfer := (Causalean.Stat.measureReal_sub_le_tvDist (μ := P) (ν := M) hF).trans hτ
  have hinter := measureReal_union_add_inter (μ := P) (s := E) hF
  have hunion : P.real (E ∪ F) ≤ 1 := measureReal_le_one
  have hprob : (80/100 : ℝ)-τ-2*ε ≤ P.real (E ∩ F) := by
    change 9/10-ε ≤ P.real E at hP
    change 9/10-ε ≤ M.real F at hM
    linarith
  calc
    _ ≤ ENNReal.ofReal (2*a) * P (E ∩ F) := by
      rw [← ofReal_measureReal, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) ha)]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hprob (mul_nonneg (by norm_num) ha)
    _ ≤ _ := by
      rw [← lintegral_indicator_const (hE.inter hF)]
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ E ∩ F
      · rw [Set.indicator_of_mem hx]
        apply ENNReal.ofReal_le_ofReal
        have hu : a ≤ (I.1 x).2 := hx.1
        have hl : (I.1 x).1 ≤ -a := hx.2
        linarith
      · rw [Set.indicator_of_notMem hx]
        exact zero_le

/-- Given [the stated assumptions](hyp:hqr,ha,hε,hmP,hmM,htP,htM,hclassP,hclassM,hsepP,hsepM,hτ), [Separated priors give a distinct lower bound for finite-honest connected length.](goal) -/
-- @node: separated_prior_length
lemma separated_prior_length
    {ΞP ΞM : Type*} [MeasurableSpace ΞP] [MeasurableSpace ΞM]
    (q r : ℝ) (hqr : ChannelDomain q r) (d : ℕ)
    (πP : Measure ΞP) (πM : Measure ΞM) [IsProbabilityMeasure πP] [IsProbabilityMeasure πM]
    (sP : ΞP → Schedule V) (sM : ΞM → Schedule V)
    (hmP : Measurable (fun ξ => (noisyDesign q r (sP ξ)).map (recordOf (sP ξ))))
    (hmM : Measurable (fun ξ => (noisyDesign q r (sM ξ)).map (recordOf (sM ξ))))
    (htP : Measurable (fun ξ => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sP ξ)))
    (htM : Measurable (fun ξ => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sM ξ)))
    (a ε τ : ℝ) (ha : 0 < a) (hε : 0 ≤ ε)
    (hclassP : ∀ᵐ ξ ∂πP, ScheduleClass (sP ξ) d)
    (hclassM : ∀ᵐ ξ ∂πM, ScheduleClass (sM ξ) d)
    (hsepP : πP.real {ξ | CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sP ξ) < a} ≤ ε)
    (hsepM : πM.real {ξ | -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sM ξ)} ≤ ε)
    (hτ : Causalean.Stat.tvDist (mixtureRecordLaw q r πP sP) (mixtureRecordLaw q r πM sM) ≤ τ) :
    ENNReal.ofReal (2*a*((80/100 : ℝ)-τ-2*ε)) ≤ minimaxLength (noisyDesign (V := V) q r) d := by
  let := separated_seed_probability
  let := separated_mixture_probability q r hqr πP sP hmP
  let := separated_mixture_probability q r hqr πM sM hmM
  have htv : Causalean.Stat.tvDist
      ((mixtureRecordLaw q r πP sP).prod seedLaw)
      ((mixtureRecordLaw q r πM sM).prod seedLaw) ≤ τ := by
    simpa using (Causalean.Stat.tvDist_compProd_eq
      (mixtureRecordLaw q r πP sP) (mixtureRecordLaw q r πM sM)
      (ProbabilityTheory.Kernel.const _ seedLaw)).trans_le hτ
  change _ ≤ ⨅ I : {I : IntervalProc V // Honest (noisyDesign q r) d I},
    worstLength (noisyDesign q r) d I.1
  apply le_iInf
  intro I
  have hP := separated_prior_interval_event q r hqr πP sP hmP htP d hclassP I.1 I.2 a ε hε true hsepP
  have hM := separated_prior_interval_event q r hqr πM sM hmM htM d hclassM I.1 I.2 a ε hε false hsepM
  exact (separated_interval_testing_length _ _ I.1 a ε τ ha.le hP hM htv).trans
    (separated_mixture_length_le_worst q r hqr πP sP hmP d hclassP I.1)

end PriorTesting

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr,ha,ha1,hmP,hmM,htP,htM,hε,hclassP,hclassM,hsepP,hsepM,hτ), [Two supported Borel priors with exceptional target-separation mass at most ε give
separate minimax MSE and honest connected-interval length bounds, including seeded procedures.](goal) -/
-- @node: lem:separated-prior-decisions
lemma separated_prior_decisions (n d : ℕ) (q r : ℝ) (hn : 4 ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) (hqr : ChannelDomain q r)
    {ΞP ΞM : Type*} [MeasurableSpace ΞP] [MeasurableSpace ΞM]
    (πP : Measure ΞP) (πM : Measure ΞM) [IsProbabilityMeasure πP] [IsProbabilityMeasure πM]
    (sP : ΞP → Schedule (Fin n)) (sM : ΞM → Schedule (Fin n))
    (hmP : Measurable (fun ξ => (noisyDesign q r (sP ξ)).map (recordOf (sP ξ))))
    (hmM : Measurable (fun ξ => (noisyDesign q r (sM ξ)).map (recordOf (sM ξ))))
    (htP : Measurable (fun ξ => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sP ξ)))
    (htM : Measurable (fun ξ => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sM ξ)))
    (a ε τ : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hclassP : ∀ᵐ ξ ∂πP, ScheduleClass (sP ξ) d) (hclassM : ∀ᵐ ξ ∂πM, ScheduleClass (sM ξ) d)
    (hsepP : πP.real {ξ | CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sP ξ) < a} ≤ ε)
    (hsepM : πM.real {ξ | -a < CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte (sM ξ)} ≤ ε)
    (hτ : Causalean.Stat.tvDist (mixtureRecordLaw q r πP sP) (mixtureRecordLaw q r πM sM) ≤ τ) :
    ENNReal.ofReal (a^2/2*(1-τ-2*ε)) ≤ minimaxRisk (noisyDesign (V := Fin n) q r) d ∧
    ENNReal.ofReal (2*a*((80/100 : ℝ)-τ-2*ε)) ≤ minimaxLength (noisyDesign (V := Fin n) q r) d := by
  constructor
  · exact separated_prior_risk q r hqr d πP πM sP sM hmP hmM htP htM
      a ε τ ha hε.1 hclassP hclassM hsepP hsepM hτ
  · exact separated_prior_length q r hqr d πP πM sP sM hmP hmM htP htM
      a ε τ ha hε.1 hclassP hclassM hsepP hsepM hτ

end CausalSmith.Experimentation.NoisygraphTtePrecision
