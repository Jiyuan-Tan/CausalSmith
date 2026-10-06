module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerCertificate
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawMembership

/-! Center-score Bernoulli trial submodels for the lower certificate. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,hOverlap), [this definition](goal) introduces the corresponding object. -/
def trialCenterScore {ε : ℝ} (hOverlap : Overlap ε) : ScoreSpace ε :=
  ⟨1 / 2, by
    constructor
    · exact le_of_lt hOverlap.2
    · linarith [hOverlap.2]⟩
/-- [This definition](goal) introduces the corresponding mathematical object. -/
def trialZeroOutcome : OutcomeSpace := ⟨0, by norm_num⟩
/-- [This definition](goal) introduces the corresponding mathematical object. -/
def trialOneOutcome : OutcomeSpace := ⟨1, by norm_num⟩

/-- For [the specified mathematical inputs](hyp:ε,J,g,hOverlap,y,a), [this definition](goal) introduces the corresponding object. -/
def trialCenterRow {ε : ℝ} {J : ℕ} (g : ScoreSpace ε → LabelSpace J)
    (hOverlap : Overlap ε) (y : OutcomeSpace) (a : ArmSpace) : FullRow ε J :=
  (trialCenterScore hOverlap, trialZeroOutcome, y, a,
    if a then y else trialZeroOutcome, g (trialCenterScore hOverlap))
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenterRow_measurable {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε) :
    Measurable (fun ya : OutcomeSpace × ArmSpace =>
      trialCenterRow g hOverlap ya.1 ya.2) := by
  have hcond : MeasurableSet {ya : OutcomeSpace × ArmSpace | ya.2 = true} := by
    exact measurableSet_eq_fun measurable_snd measurable_const
  have hobs : Measurable (fun ya : OutcomeSpace × ArmSpace =>
      if ya.2 then ya.1 else trialZeroOutcome) :=
    Measurable.ite hcond measurable_fst measurable_const
  unfold trialCenterRow
  fun_prop (disch := assumption)

/-- For [the specified mathematical inputs](hyp:p), [this definition](goal) introduces the corresponding object. -/
def trialOutcomeLaw (p : ℝ) : Measure OutcomeSpace :=
  ENNReal.ofReal p • Measure.dirac trialOneOutcome +
    ENNReal.ofReal (1 - p) • Measure.dirac trialZeroOutcome
/-- Given [the stated mathematical inputs and assumptions](hyp:p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialOutcomeLaw_isProbabilityMeasure (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (trialOutcomeLaw p) := by
  rw [isProbabilityMeasure_iff]
  unfold trialOutcomeLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
  norm_num

/-- [This definition](goal) introduces the corresponding mathematical object. -/
def trialArmLaw : Measure ArmSpace :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true +
    (1 / 2 : ℝ≥0∞) • Measure.dirac false
/-- This result [establishes the stated mathematical conclusion](goal). -/
lemma trialArmLaw_isProbabilityMeasure : IsProbabilityMeasure trialArmLaw := by
  rw [isProbabilityMeasure_iff]
  unfold trialArmLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simpa only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one, one_div] using ENNReal.inv_two_add_inv_two
/-- This result [establishes the stated mathematical conclusion](goal). -/
lemma trialArmLaw_true_mass : trialArmLaw.real {true} = 1 / 2 := by
  unfold trialArmLaw
  rw [Measure.real_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  norm_num

/-- For [the specified mathematical inputs](hyp:ε,J,g,hOverlap,p), [this definition](goal) introduces the corresponding object. -/
def trialCenterFullLaw {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (p : ℝ) : Measure (FullRow ε J) :=
  ((trialOutcomeLaw p).prod trialArmLaw).map
    (fun ya => trialCenterRow g hOverlap ya.1 ya.2)
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenterFullLaw_isProbabilityMeasure {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (trialCenterFullLaw g hOverlap p) := by
  letI : IsProbabilityMeasure (trialOutcomeLaw p) :=
    trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
  letI : IsProbabilityMeasure trialArmLaw := trialArmLaw_isProbabilityMeasure
  unfold trialCenterFullLaw
  exact Measure.isProbabilityMeasure_map (trialCenterRow_measurable g hOverlap).aemeasurable

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenterFullLaw_scoreMarginal {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ScoreMarginal (trialCenterFullLaw g hOverlap p)
      (Measure.dirac (trialCenterScore hOverlap)) := by
  letI : IsProbabilityMeasure (trialOutcomeLaw p) :=
    trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
  letI : IsProbabilityMeasure trialArmLaw := trialArmLaw_isProbabilityMeasure
  have hrow := trialCenterRow_measurable g hOverlap
  unfold ScoreMarginal trialCenterFullLaw
  rw [Measure.map_map (by unfold score; fun_prop) hrow]
  change ((trialOutcomeLaw p).prod trialArmLaw).map
    (fun _ => trialCenterScore hOverlap) = _
  rw [Measure.map_const]
  simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,p), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenterFullLaw_consistency {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε) (p : ℝ) :
    Consistency (trialCenterFullLaw g hOverlap p) := by
  have hrow := trialCenterRow_measurable g hOverlap
  have hcond : MeasurableSet {ω : FullRow ε J | arm ω = true} :=
    measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const
  have hpot : Measurable (fun ω : FullRow ε J =>
      if arm ω then outcome1 ω else outcome0 ω) :=
    Measurable.ite hcond (by unfold outcome1; fun_prop)
      (by unfold outcome0; fun_prop)
  have hset : MeasurableSet {ω : FullRow ε J |
      observed ω = if arm ω then outcome1 ω else outcome0 ω} := by
    exact measurableSet_eq_fun (by unfold observed; fun_prop)
      hpot
  unfold Consistency trialCenterFullLaw
  rw [ae_map_iff hrow.aemeasurable hset]
  filter_upwards [] with ya
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,p,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenterFullLaw_deterministicRelease {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε) (p : ℝ)
    (hg : Measurable g) :
    DeterministicRelease g (trialCenterFullLaw g hOverlap p) := by
  have hrow := trialCenterRow_measurable g hOverlap
  have hset : MeasurableSet {ω : FullRow ε J | label ω = g (score ω)} := by
    exact measurableSet_eq_fun (by unfold label; fun_prop)
      (hg.comp (by unfold score; fun_prop))
  unfold DeterministicRelease trialCenterFullLaw
  rw [ae_map_iff hrow.aemeasurable hset]
  filter_upwards [] with ya
  rfl
/-- Given [the stated mathematical inputs and assumptions](hyp:p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialOutcomeLaw_mean (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ y : OutcomeSpace, (y : ℝ) ∂(trialOutcomeLaw p)) = p := by
  unfold trialOutcomeLaw
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp [trialOneOutcome, trialZeroOutcome, hp0, sub_nonneg.mpr hp1, smul_eq_mul]
  · exact Integrable.smul_measure (μ := Measure.dirac trialOneOutcome)
      (c := ENNReal.ofReal p)
      (integrable_dirac (f := fun y : OutcomeSpace => (y : ℝ))
        (a := trialOneOutcome) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac trialZeroOutcome)
      (c := ENNReal.ofReal (1 - p))
      (integrable_dirac (f := fun y : OutcomeSpace => (y : ℝ))
        (a := trialZeroOutcome) (by simp [enorm])) (by simp)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenterFullLaw_ate {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ate (trialCenterFullLaw g hOverlap p) = p := by
  letI : IsProbabilityMeasure (trialOutcomeLaw p) :=
    trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
  letI : IsProbabilityMeasure trialArmLaw := trialArmLaw_isProbabilityMeasure
  have hrow := trialCenterRow_measurable g hOverlap
  calc
    ate (trialCenterFullLaw g hOverlap p) =
        ∫ ya : OutcomeSpace × ArmSpace, (ya.1 : ℝ)
          ∂((trialOutcomeLaw p).prod trialArmLaw) := by
      unfold ate trialCenterFullLaw
      rw [integral_map hrow.aemeasurable (by
        unfold outcome0 outcome1
        fun_prop)]
      simp [trialCenterRow, outcome0, outcome1, trialZeroOutcome]
    _ = ∫ y : OutcomeSpace, (y : ℝ)
          ∂(((trialOutcomeLaw p).prod trialArmLaw).map Prod.fst) := by
      rw [integral_map measurable_fst.aemeasurable (by fun_prop)]
    _ = ∫ y : OutcomeSpace, (y : ℝ) ∂(trialOutcomeLaw p) := by
      rw [Measure.map_fst_prod]
      rw [show trialArmLaw Set.univ = 1 from isProbabilityMeasure_iff.mp inferInstance]
      simp
    _ = p := trialOutcomeLaw_mean p hp0 hp1

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenterFullLaw_randomizedAssignment {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    RandomizedAssignment (trialCenterFullLaw g hOverlap p) := by
  intro B hB
  let μ : Measure OutcomeSpace := trialOutcomeLaw p
  let ν : Measure ArmSpace := trialArmLaw
  let f : OutcomeSpace × ArmSpace → FullRow ε J :=
    fun ya => trialCenterRow g hOverlap ya.1 ya.2
  have hf : Measurable f := trialCenterRow_measurable g hOverlap
  let U : Set OutcomeSpace :=
    {y | (trialCenterScore hOverlap, trialZeroOutcome, y) ∈ B}
  have hU : MeasurableSet U := by
    have htriple : Measurable (fun y : OutcomeSpace =>
        (trialCenterScore hOverlap, trialZeroOutcome, y)) := by fun_prop
    exact hB.preimage htriple
  let S : Set (FullRow ε J) :=
    {ω | arm ω = true ∧ latentTriple ω ∈ B}
  let T : Set (FullRow ε J) := {ω | latentTriple ω ∈ B}
  have hlatent : Measurable (latentTriple (ε := ε) (J := J)) := by
    unfold latentTriple score outcome0 outcome1
    fun_prop
  have hS : MeasurableSet S :=
    (measurableSet_eq_fun (by unfold arm; fun_prop) measurable_const).inter
      (hB.preimage hlatent)
  have hT : MeasurableSet T := hB.preimage hlatent
  have hpreS : f ⁻¹' S = U ×ˢ {true} := by
    ext ya
    cases ha : ya.2 <;> simp [f, S, U, trialCenterRow, arm,
      latentTriple, score, outcome0, outcome1, ha]
  have hpreT : f ⁻¹' T = U ×ˢ Set.univ := by
    ext ya
    simp [f, T, U, trialCenterRow, latentTriple, score, outcome0, outcome1]
  have hνprob : IsProbabilityMeasure ν := trialArmLaw_isProbabilityMeasure
  have hνuniv : ν.real Set.univ = 1 := isProbabilityMeasure_iff_real.mp hνprob
  change (trialCenterFullLaw g hOverlap p).real S =
    ∫ ω in T, (score ω : ℝ) ∂(trialCenterFullLaw g hOverlap p)
  have hleft : (trialCenterFullLaw g hOverlap p).real S = μ.real U / 2 := by
    unfold trialCenterFullLaw
    rw [MeasureTheory.map_measureReal_apply hf hS, hpreS,
      measureReal_prod_prod]
    rw [show ν.real {true} = 1 / 2 from trialArmLaw_true_mass]
    ring
  have hright : (∫ ω in T, (score ω : ℝ)
        ∂(trialCenterFullLaw g hOverlap p)) = μ.real U / 2 := by
    unfold trialCenterFullLaw
    rw [MeasureTheory.setIntegral_map hT (by unfold score; fun_prop)
      hf.aemeasurable]
    rw [hpreT]
    change ∫ _ in U ×ˢ Set.univ, (1 / 2 : ℝ) ∂(μ.prod ν) = _
    rw [setIntegral_const, measureReal_prod_prod, hνuniv]
    simp only [smul_eq_mul, mul_one]
    ring
  exact hleft.trans hright.symm

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,hg,p,hp0,hp1), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenterFullLaw_externalScoreLaw {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (hg : Measurable g) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ExternalScoreLaw g (trialCenterFullLaw g hOverlap p)
      (Measure.dirac (trialCenterScore hOverlap)) where
  probabilityP := trialCenterFullLaw_isProbabilityMeasure g hOverlap p hp0 hp1
  probabilityH := inferInstance
  overlap := hOverlap
  measurableRelease := hg
  scoreMarginal := trialCenterFullLaw_scoreMarginal g hOverlap p hp0 hp1
  randomizedAssignment := trialCenterFullLaw_randomizedAssignment g hOverlap p hp0 hp1
  consistency := trialCenterFullLaw_consistency g hOverlap p
  deterministicRelease := trialCenterFullLaw_deterministicRelease g hOverlap p hg

end
end CausalSmith.PartialID.UnlinkedPropensityAte
