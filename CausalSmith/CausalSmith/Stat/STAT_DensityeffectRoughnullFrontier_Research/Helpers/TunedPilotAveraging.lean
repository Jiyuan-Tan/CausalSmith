module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.PilotConcentration
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RateAssembly
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.TunedSamplingTransfer

/-! Good/bad training averaging for the frozen reported interval. Bad pilots cost
at most sixteen; their outer probability suffices without any measurable-supremum premise. -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- A bounded observable costs its good-event budget plus the outer probability
of the exceptional event times the global envelope. -/
-- @node: integral_le_good_budget_add_bad_mass
lemma integral_le_good_budget_add_bad_mass {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Integrable f μ)
    (E : Set α) (b M : ℝ) (hb : 0 ≤ b) (_hM : 0 ≤ M)
    (hbound : ∀ x, f x ≤ M) (hgood : ∀ x, x ∉ E → f x ≤ b) :
    (∫ x, f x ∂μ) ≤ b + M * μ.real E := by
  classical
  let S := toMeasurable μ E
  have hS : MeasurableSet S := measurableSet_toMeasurable μ E
  have hi : Integrable (S.indicator (fun _ => M)) μ :=
    (integrable_const M).indicator hS
  have hle : ∀ x, f x ≤ b + S.indicator (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      exact (hbound x).trans (by linarith)
    · rw [Set.indicator_of_notMem hx, add_zero]
      exact hgood x (fun he => hx (subset_toMeasurable μ E he))
  have h := integral_mono hf ((integrable_const b).add hi) hle
  change (∫ x, f x ∂μ) ≤ (∫ x, b + S.indicator (fun _ => M) x ∂μ) at h
  rw [integral_add (integrable_const b) hi, integral_const, probReal_univ, one_smul,
    integral_indicator hS, setIntegral_const, smul_eq_mul] at h
  simpa only [S, measureReal_def, measure_toMeasurable, mul_comm] using h

/-- Average a bounded training observable using the public bad-pilot tail.
The training event can be arbitrary: only the observable must be measurable. -/
-- @node: pilot_training_integral_budget
lemma pilot_training_integral_budget (P : ObsLaw) (hModel : Model P)
    (m mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my)
    (g : Data (roleSize (13 * m)) → ℝ) (hg : Measurable g)
    (b M : ℝ) (hb : 0 ≤ b) (hM : 0 ≤ M) (hbound : ∀ train, g train ∈ Set.Icc 0 M)
    (hgood : ∀ train, GoodPilot P train (2 ^ 16) mx my → g train ≤ b) :
    (∫ train, g train ∂dataLaw P (roleSize (13 * m))) ≤
      b + M * zetaAllow m mx my := by
  let sel := fun ω : SampleSpace (13 * m) => foldData (13 * m) ω.1 0
  have hsel : Measurable sel := by unfold sel foldData; fun_prop
  have hi : Integrable (fun ω => g (sel ω)) (sampleLaw P (13 * m)) :=
    Integrable.of_bound (hg.comp hsel).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound _).1]
        exact (hbound _).2))
  have ht := integral_le_good_budget_add_bad_mass (sampleLaw P (13 * m))
    (fun ω => g (sel ω)) hi {ω | ¬GoodPilot P (sel ω) (2 ^ 16) mx my}
    b M hb hM (fun ω => (hbound _).2)
    (fun ω h => hgood _ (Classical.not_not.mp h))
  have hp := pilot_concentration_public_tail P hModel m mx my hm hmx hmy
    (sampleLaw P (13 * m)) rfl
  have he : (∫ ω, g (sel ω) ∂sampleLaw P (13 * m)) =
      ∫ train, g train ∂dataLaw P (roleSize (13 * m)) := by
    have hmap : (sampleLaw P (13 * m)).map sel = dataLaw P (roleSize (13 * m)) :=
      sampleLaw_foldData_map P (13 * m) 0
    rw [← hmap]
    exact (integral_map hsel.aemeasurable hg.aestronglyMeasurable).symm
  rw [he] at ht
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hM))

/-- The bounded reported quantity in the retained training/evaluation experiment. -/
-- @node: tunedReportedLength
def tunedReportedLength (n : ℕ) (z : Data (roleSize n) × EvalData (roleSize n)) : ℝ :=
  intervalLength (invSet (energy z.1 (tunedMx (roleSize n)) (tunedMy (roleSize n))
    (tunedL (roleSize n)) (tunedT (roleSize n)) (tunedJ (roleSize n))
    (tunedQ (roleSize n)) (tunedKt (roleSize n)) z.2)
    (aci (tunedB n) (tunedW n))
    (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))))

-- @node: measurable_tunedReportedLength
@[fun_prop] lemma measurable_tunedReportedLength (n : ℕ) :
    Measurable (tunedReportedLength n) := by
  let Z := fun z : Data (roleSize n) × EvalData (roleSize n) => energy z.1
    (tunedMx (roleSize n)) (tunedMy (roleSize n)) (tunedL (roleSize n))
    (tunedT (roleSize n)) (tunedJ (roleSize n)) (tunedQ (roleSize n))
    (tunedKt (roleSize n)) z.2
  have hZ : Measurable Z := by fun_prop
  have he : tunedReportedLength n = fun z =>
      invUpper (Z z) (aci (tunedB n) (tunedW n))
        (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))) -
      invLower (Z z) (aci (tunedB n) (tunedW n))
        (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))) := by
    funext z
    exact inversion_length_eq _ _ _ (tuned_inversion_nonneg n).1
  rw [he]
  exact ((inversion_endpoints_measurable _ _).2.comp hZ).sub
    ((inversion_endpoints_measurable _ _).1.comp hZ)

/-- The conditional reported length is bounded at every trained realization,
including bad pilots. -/
-- @node: tunedReportedLength_conditional_range
lemma tunedReportedLength_conditional_range (P : ObsLaw) (n : ℕ)
    (train : Data (roleSize n)) :
    (∫ eval, tunedReportedLength n (train, eval) ∂evalLaw P (roleSize n)) ∈
      Set.Icc (0 : ℝ) 16 := by
  let : IsProbabilityMeasure (evalLaw P (roleSize n)) := by
    unfold evalLaw; infer_instance
  have hr : ∀ eval, tunedReportedLength n (train, eval) ∈ Set.Icc (0 : ℝ) 16 :=
    fun eval => inversion_length_range _ _ _
  have hm : Measurable (fun eval => tunedReportedLength n (train, eval)) := by fun_prop
  have hi : Integrable (fun eval => tunedReportedLength n (train, eval))
      (evalLaw P (roleSize n)) := Integrable.of_bound hm.aestronglyMeasurable 16
    (Filter.Eventually.of_forall (fun eval => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hr eval).1]
      exact (hr eval).2))
  refine ⟨integral_nonneg (fun eval => (hr eval).1), ?_⟩
  have h := integral_mono hi (integrable_const (16 : ℝ)) (fun eval => (hr eval).2)
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- Averaging the good-pilot inversion length and the bounded bad-pilot cost
proves the uniform null expected-length budget in (58). -/
-- @node: starRule_null_expectedLength_budget
lemma starRule_null_expectedLength_budget (n : ℕ) (hbranch : reportingBranch n)
    (P : ObsLaw) (hNull : NullModel P) :
    expectedLength P n (starRule n) ≤ (aci (tunedB n) (tunedW n)) ^ 2 +
      4 * dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)) +
      16 * zetaAllow (roleSize n) (tunedMx (roleSize n)) (tunedMy (roleSize n)) := by
  let m := roleSize n
  let g := fun train : Data m =>
    ∫ eval, tunedReportedLength n (train, eval) ∂evalLaw P m
  let b := (aci (tunedB n) (tunedW n)) ^ 2 +
    4 * dci (tunedB n) (tunedW n) (tunedV n) (tunedJ m)
  let : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  have hg : Measurable g :=
    (measurable_tunedReportedLength n).stronglyMeasurable.integral_prod_right'.measurable
  have hb : 0 ≤ b := by
    dsimp [b]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (tuned_inversion_nonneg n).2)
  have hgood : ∀ train, GoodPilot P train (2 ^ 16) (tunedMx m) (tunedMy m) → g train ≤ b :=
    fun train h => tuned_null_conditional_length n hbranch P hNull train h
  have hmx : 0 < tunedMx m := by
    obtain ⟨k, hk⟩ := dyadicFloor_dyadic (((m : ℝ) / Real.log m) ^ (10 / 13 : ℝ))
    change 0 < dyadicFloor _
    rw [hk]
    positivity
  have hmy : 0 < tunedMy m := by
    obtain ⟨k, hk⟩ := dyadicFloor_dyadic (((m : ℝ) / Real.log m) ^ (1 / 13 : ℝ))
    change 0 < dyadicFloor _
    rw [hk]
    positivity
  have hbudget := pilot_training_integral_budget P hNull.1 m (tunedMx m) (tunedMy m)
    hbranch.1 hmx hmy
  have hrole : roleSize (13 * m) = m := by simp [roleSize]
  rw [hrole] at hbudget
  have h := hbudget g hg b 16 hb (by norm_num) (tunedReportedLength_conditional_range P n) hgood
  rw [starRule_expectedLength_iterated P n hbranch]
  exact h

/-- The uniform budget passes to the supremum over every equality density. -/
-- @node: starRule_worstNullLength_budget
lemma starRule_worstNullLength_budget (n : ℕ) (hbranch : reportingBranch n) :
    worstNullLength n (starRule n) ≤ (aci (tunedB n) (tunedW n)) ^ 2 +
      4 * dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)) +
      16 * zetaAllow (roleSize n) (tunedMx (roleSize n)) (tunedMy (roleSize n)) := by
  apply csSup_le
  · exact ⟨expectedLength (exampleLaw 0) n (starRule n),
      exampleLaw 0, nonflat_example.2.1, rfl⟩
  · rintro r ⟨P, hNull, rfl⟩
    exact starRule_null_expectedLength_budget n hbranch P hNull

/-- Equation (59), with no logarithmic factor, follows from the deterministic
allowance rates and the actual good/bad training average. -/
-- @node: starRule_worstNullLength_upper_rate
lemma starRule_worstNullLength_upper_rate :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n, n0 ≤ n →
      worstNullLength n (starRule n) ≤ C * frontierRate n := by
  obtain ⟨C, hC, n0, hrate⟩ := tuned_rate_arithmetic
  refine ⟨C, hC, n0, ?_⟩
  intro n hn
  obtain ⟨hbranch, _, _, _, hbudget⟩ := hrate n hn
  have hlength := starRule_worstNullLength_budget n hbranch
  have hs := sq_nonneg (aci (tunedB n) (tunedW n))
  linarith

/-- Coverage in the retained independent training/evaluation experiment. -/
-- @node: tunedCoverageEvent
def tunedCoverageEvent (P : ObsLaw) (n : ℕ) :
    Set (Data (roleSize n) × EvalData (roleSize n)) :=
  {z | Psi P ∈ invSet (energy z.1 (tunedMx (roleSize n)) (tunedMy (roleSize n))
    (tunedL (roleSize n)) (tunedT (roleSize n)) (tunedJ (roleSize n))
    (tunedQ (roleSize n)) (tunedKt (roleSize n)) z.2)
    (aci (tunedB n) (tunedW n))
    (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)))}

-- @node: measurableSet_tunedCoverageEvent
lemma measurableSet_tunedCoverageEvent (P : ObsLaw) (n : ℕ) :
    MeasurableSet (tunedCoverageEvent P n) := by
  let a := aci (tunedB n) (tunedW n)
  let d := dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))
  let Z := fun z : Data (roleSize n) × EvalData (roleSize n) => energy z.1
    (tunedMx (roleSize n)) (tunedMy (roleSize n)) (tunedL (roleSize n))
    (tunedT (roleSize n)) (tunedJ (roleSize n)) (tunedQ (roleSize n))
    (tunedKt (roleSize n)) z.2
  have hZ : Measurable Z := by fun_prop
  have he : tunedCoverageEvent P n =
      {z | invLower (Z z) a d ≤ Psi P ∧ Psi P ≤ invUpper (Z z) a d} := by
    ext z
    change Psi P ∈ invSet (Z z) a d ↔ _
    rw [invSet_eq_endpoint_interval _ _ _ (tuned_inversion_nonneg n).1]
    rfl
  rw [he]
  exact (measurableSet_le ((inversion_endpoints_measurable a d).1.comp hZ)
    measurable_const).inter (measurableSet_le measurable_const
      ((inversion_endpoints_measurable a d).2.comp hZ))

/-- Integrating conditional coverage over good and bad training proves
finite-sample honesty on the nontrivial reporting branch. -/
-- @node: starRule_isHonest_of_reportingBranch
lemma starRule_isHonest_of_reportingBranch (n : ℕ) (hbranch : reportingBranch n) :
    IsHonest n (starRule n) := by
  classical
  intro P hModel
  let m := roleSize n
  let E := tunedCoverageEvent P n
  let f : Data m × EvalData m → ℝ := Eᶜ.indicator (fun _ => 1)
  let g := fun train : Data m => ∫ eval, f (train, eval) ∂evalLaw P m
  have hE : MeasurableSet E := measurableSet_tunedCoverageEvent P n
  have hf : Measurable f := measurable_const.indicator hE.compl
  let : IsProbabilityMeasure (dataLaw P m) := by unfold dataLaw; infer_instance
  let : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  have hfr : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    by_cases hz : z ∈ Eᶜ <;> simp [f, hz]
  have hg : Measurable g := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hgr : ∀ train, g train ∈ Set.Icc (0 : ℝ) 1 := by
    intro train
    have hsec : Measurable (fun eval => f (train, eval)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    have hi : Integrable (fun eval => f (train, eval)) (evalLaw P m) :=
      Integrable.of_bound hsec.aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun eval => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hfr _).1]
          exact (hfr _).2))
    refine ⟨integral_nonneg (fun eval => (hfr _).1), ?_⟩
    have h := integral_mono hi (integrable_const (1 : ℝ)) (fun eval => (hfr _).2)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hgood : ∀ train, GoodPilot P train (2 ^ 16) (tunedMx m) (tunedMy m) →
      g train ≤ (1 / 20 : ℝ) := by
    intro train hGood
    let F : Set (EvalData m) := {eval | (train, eval) ∈ E}
    have hF : MeasurableSet F := hE.preimage (measurable_const.prodMk measurable_id)
    have he : g train = (evalLaw P m).real Fᶜ := by
      change (∫ eval, Fᶜ.indicator (fun _ => (1 : ℝ)) eval ∂evalLaw P m) = _
      exact integral_indicator_one hF.compl
    have hc := tuned_conditional_interval_coverage n hbranch P hModel train hGood
    change (19 / 20 : ℝ) ≤ (evalLaw P m).real F at hc
    rw [he, measureReal_compl hF, probReal_univ]
    linarith
  have hmx : 0 < tunedMx m := by
    obtain ⟨k, hk⟩ := dyadicFloor_dyadic (((m : ℝ) / Real.log m) ^ (10 / 13 : ℝ))
    change 0 < dyadicFloor _
    rw [hk]
    positivity
  have hmy : 0 < tunedMy m := by
    obtain ⟨k, hk⟩ := dyadicFloor_dyadic (((m : ℝ) / Real.log m) ^ (1 / 13 : ℝ))
    change 0 < dyadicFloor _
    rw [hk]
    positivity
  have hbudget := pilot_training_integral_budget P hModel m (tunedMx m) (tunedMy m)
    hbranch.1 hmx hmy
  have hrole : roleSize (13 * m) = m := by simp [roleSize]
  rw [hrole] at hbudget
  have hb := hbudget g hg (1 / 20) 1 (by norm_num) (by norm_num) hgr hgood
  have hi : Integrable f ((dataLaw P m).prod (evalLaw P m)) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfr _).1]
        exact (hfr _).2))
  have he : (∫ train, g train ∂dataLaw P m) =
      ((dataLaw P m).prod (evalLaw P m)).real Eᶜ := by
    rw [← integral_prod f hi]
    exact integral_indicator_one hE.compl
  rw [he, one_mul] at hb
  have hz := hbranch.2.2
  have hc := measureReal_compl (μ := (dataLaw P m).prod (evalLaw P m)) hE
  rw [probReal_univ] at hc
  rw [starRule_coverage_product P n hbranch]
  change (9 / 10 : ℝ) ≤ ((dataLaw P m).prod (evalLaw P m)).real E
  linarith

/-- The single frozen total rule is honest for every finite sample size. -/
-- @node: starRule_isHonest
lemma starRule_isHonest (n : ℕ) : IsHonest n (starRule n) := by
  by_cases hbranch : reportingBranch n
  · exact starRule_isHonest_of_reportingBranch n hbranch
  · exact starRule_isHonest_of_not_reportingBranch n hbranch

end CausalSmith.Stat.DensityEffectRoughNull
