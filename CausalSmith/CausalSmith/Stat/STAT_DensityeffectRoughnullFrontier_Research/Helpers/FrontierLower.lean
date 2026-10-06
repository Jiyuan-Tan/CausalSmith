module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.EnergyProjection
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture

/-! Finite-prior randomized length transfer and the all-procedure frontier converse. -/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The fixed-sample finite mixture is a probability law. -/
-- @node: finiteSampleMixture_probability
instance finiteSampleMixture_probability (n : ℕ) (nu : FinitePrior) :
    IsProbabilityMeasure (finiteSampleMixture n nu) := by
  constructor
  simp only [finiteSampleMixture, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  have hdata (i : Fin nu.1) : dataLaw (priorLaw nu i) n Set.univ = 1 := by
    unfold dataLaw
    exact measure_univ
  simp only [hdata, mul_one]
  exact nu.2.2.2

/-- Independent public randomization of the finite observation mixture. -/
-- @node: finiteRandomizedMixture
def finiteRandomizedMixture (n : ℕ) (nu : FinitePrior) : Measure (SampleSpace n) :=
  (finiteSampleMixture n nu).prod unitVolume

/-- Public randomization preserves the finite mixture's normalization. -/
-- @node: finiteRandomizedMixture_probability
instance finiteRandomizedMixture_probability (n : ℕ) (nu : FinitePrior) :
    IsProbabilityMeasure (finiteRandomizedMixture n nu) := by
  unfold finiteRandomizedMixture
  infer_instance

/-- Mixing component sampling laws commutes with the common randomization law. -/
-- @node: finiteRandomizedMixture_eq_sum
lemma finiteRandomizedMixture_eq_sum (n : ℕ) (nu : FinitePrior) :
    finiteRandomizedMixture n nu =
      ∑ i : Fin nu.1, priorWeight nu i • sampleLaw (priorLaw nu i) n := by
  simp only [finiteRandomizedMixture, finiteSampleMixture, sampleLaw,
    ← Measure.sum_fintype, Measure.prod_sum_left, Measure.prod_smul_left]

/-- The finite prior's real weights sum to one. -/
-- @node: priorWeight_toReal_sum
lemma priorWeight_toReal_sum (nu : FinitePrior) :
    ∑ i : Fin nu.1, (priorWeight nu i).toReal = 1 := by
  rw [← ENNReal.toReal_sum]
  · change (∑ i : Fin nu.1, nu.2.2.1 i).toReal = 1
    rw [nu.2.2.2]
    rfl
  · intro i hi
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (show priorWeight nu i ≤ 1 from by
        rw [← nu.2.2.2]
        exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i))

/-- The randomized mixture event mass is its finite weighted average. -/
-- @node: finiteRandomizedMixture_real
lemma finiteRandomizedMixture_real (n : ℕ) (nu : FinitePrior)
    (E : Set (SampleSpace n)) (_hE : MeasurableSet E) :
    (finiteRandomizedMixture n nu).real E =
      ∑ i : Fin nu.1, (priorWeight nu i).toReal * (sampleLaw (priorLaw nu i) n).real E := by
  rw [measureReal_def, finiteRandomizedMixture_eq_sum,
    Measure.finsetSum_apply, ENNReal.toReal_sum]
  · simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, measureReal_def]
  · intro i hi
    have hw : priorWeight nu i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (by
      exact (Finset.single_le_sum (fun _ _ => zero_le) hi).trans_eq nu.2.2.2)
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top hw (measure_ne_top _ _)

/-- A uniform component coverage bound passes to the finite randomized mixture. -/
-- @node: finiteRandomizedMixture_event_lower
lemma finiteRandomizedMixture_event_lower (n : ℕ) (nu : FinitePrior)
    (E : Set (SampleSpace n)) (hE : MeasurableSet E) (c : ℝ)
    (hc : ∀ i, priorWeight nu i ≠ 0 → c ≤ (sampleLaw (priorLaw nu i) n).real E) :
    c ≤ (finiteRandomizedMixture n nu).real E := by
  rw [finiteRandomizedMixture_real n nu E hE]
  calc
    c = (∑ i : Fin nu.1, (priorWeight nu i).toReal) * c := by
      rw [priorWeight_toReal_sum, one_mul]
    _ = ∑ i : Fin nu.1, (priorWeight nu i).toReal * c := Finset.sum_mul ..
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hw : priorWeight nu i = 0
      · simp [hw]
      · exact mul_le_mul_of_nonneg_left (hc i hw) ENNReal.toReal_nonneg

/-- The finite randomized mixture is the image of the data mixture through the
same public randomization channel under both hypotheses. -/
-- @node: finiteRandomizedMixture_channel
lemma finiteRandomizedMixture_channel (n : ℕ) (nu : FinitePrior) :
    finiteRandomizedMixture n nu = publicRandomizationKernel n ∘ₘ finiteSampleMixture n nu := by
  rw [Measure.comp_eq_comp_const_apply]
  unfold publicRandomizationKernel
  rw [Kernel.prod_const_comp]
  simp only [Kernel.id_comp, Kernel.prod_const, Kernel.const_apply, finiteRandomizedMixture]

/-- Adding independent randomization cannot increase total variation. -/
-- @node: finiteRandomizedMixture_tv
lemma finiteRandomizedMixture_tv (n : ℕ) (nu0 nu1 : FinitePrior) :
    Causalean.Stat.tvDist (finiteRandomizedMixture n nu0) (finiteRandomizedMixture n nu1) ≤
      Causalean.Stat.tvDist (finiteSampleMixture n nu0) (finiteSampleMixture n nu1) := by
  rw [finiteRandomizedMixture_channel, finiteRandomizedMixture_channel]
  exact Causalean.Stat.tvDist_bind_le _ _ _

/-- Expected length under the finite mixture is the average of component lengths. -/
-- @node: finiteRandomizedMixture_expectedLength
lemma finiteRandomizedMixture_expectedLength (n : ℕ) (nu : FinitePrior)
    (I : IntervalRule n) (hRule : IsIntervalRule n I) :
    (∫ w, intervalLength (I w) ∂finiteRandomizedMixture n nu) =
      ∑ i : Fin nu.1, (priorWeight nu i).toReal * expectedLength (priorLaw nu i) n I := by
  have hLength := measurable_intervalLength n I hRule
  rw [finiteRandomizedMixture_eq_sum, integral_finsetSum_measure]
  · simp only [integral_smul_measure, smul_eq_mul, expectedLength]
  · intro i hi
    have hw : priorWeight nu i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (by
      exact (Finset.single_le_sum (fun _ _ => zero_le) hi).trans_eq nu.2.2.2)
    exact (intervalLength_integrable n I hRule hLength
      (sampleLaw (priorLaw nu i) n)).smul_measure hw

/-- The weighted average over equality laws cannot exceed the worst equality length. -/
-- @node: finiteRandomizedMixture_length_le_worst
lemma finiteRandomizedMixture_length_le_worst (n : ℕ) (nu : FinitePrior)
    (hnull : PriorSupported nu (fun P => NullModel P))
    (I : IntervalRule n) (hRule : IsIntervalRule n I) :
    (∫ w, intervalLength (I w) ∂finiteRandomizedMixture n nu) ≤ worstNullLength n I := by
  have hLength := measurable_intervalLength n I hRule
  have hb : BddAbove {r : ℝ | ∃ P : ObsLaw, NullModel P ∧ r = expectedLength P n I} := by
    refine ⟨16, ?_⟩
    rintro r ⟨P, hP, rfl⟩
    exact expectedLength_le_sixteen n I hRule hLength P
  rw [finiteRandomizedMixture_expectedLength n nu I hRule]
  calc
    _ ≤ ∑ i : Fin nu.1, (priorWeight nu i).toReal * worstNullLength n I := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hw : priorWeight nu i = 0
      · simp [hw]
      · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        exact le_csSup hb ⟨priorLaw nu i, hnull i hw, rfl⟩
    _ = worstNullLength n I := by rw [← Finset.sum_mul, priorWeight_toReal_sum, one_mul]

/-- Finite actual-law priors force every honest randomized interval to bridge the
null energy and the separated alternatives. This is the transfer used in (60). -/
-- @node: finite_mixture_length_transfer
lemma finite_mixture_length_transfer (n : ℕ) (nu0 nu1 : FinitePrior) (rho : ℝ)
    (hrho : rho ∈ Set.Ioc 0 16)
    (hnull : PriorSupported nu0 (fun P => NullModel P))
    (halt : PriorSupported nu1 (fun P => Model P ∧ rho ≤ Psi P))
    (htv : Causalean.Stat.tvDist (finiteSampleMixture n nu0)
      (finiteSampleMixture n nu1) ≤ 1 / 4)
    (I : IntervalRule n) (hRule : IsIntervalRule n I) (hHonest : IsHonest n I) :
    (11 / 20 : ℝ) * rho ≤ worstNullLength n I := by
  classical
  have hLength := measurable_intervalLength n I hRule
  let E : Set (SampleSpace n) := {w | rho ≤ intervalLength (I w)}
  let F : Set (SampleSpace n) := {w | 0 ∉ I w}
  have hE : MeasurableSet E := measurableSet_le measurable_const hLength
  have hzero : MeasurableSet {w : SampleSpace n | 0 ∈ I w} := by
    exact hRule.2.preimage (by fun_prop : Measurable (fun w : SampleSpace n => (w, (0 : ℝ))))
  have hF : MeasurableSet F := hzero.compl
  have hnullcov : (9 / 10 : ℝ) ≤ (finiteRandomizedMixture n nu0).real Fᶜ := by
    apply finiteRandomizedMixture_event_lower n nu0 Fᶜ hF.compl
    intro i hi
    have hP := hnull i hi
    have hh := hHonest (priorLaw nu0 i) hP.1
    simpa only [coverage, NullModel_Psi_zero _ hP, F, Set.compl_ofPred, not_not] using hh
  have haltcov : (9 / 10 : ℝ) ≤ (finiteRandomizedMixture n nu1).real (F ∪ E) := by
    apply finiteRandomizedMixture_event_lower n nu1 (F ∪ E) (hF.union hE)
    intro i hi
    have hP := halt i hi
    apply (hHonest (priorLaw nu1 i) hP.1).trans
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro w hw
    by_cases hz : 0 ∈ I w
    · exact Or.inr (hP.2.trans (intervalLength_ge_of_mem (I w) (hRule.1 w).2 hz
        (Psi (priorLaw nu1 i)) hw))
    · exact Or.inl hz
  have hgap := (Causalean.Stat.measureReal_sub_le_tvDist
    (μ := finiteRandomizedMixture n nu0) (ν := finiteRandomizedMixture n nu1)
    (hF.union hE)).trans ((finiteRandomizedMixture_tv n nu0 nu1).trans htv)
  have hFmass : (finiteRandomizedMixture n nu0).real F ≤ 1 / 10 := by
    have hc := measureReal_compl (μ := finiteRandomizedMixture n nu0) hF
    rw [probReal_univ] at hc
    linarith
  have hunion := measureReal_union_le (μ := finiteRandomizedMixture n nu0) F E
  have hEmass : (11 / 20 : ℝ) ≤ (finiteRandomizedMixture n nu0).real E := by
    linarith
  calc
    (11 / 20 : ℝ) * rho ≤ rho * (finiteRandomizedMixture n nu0).real E := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hEmass hrho.1.le
    _ ≤ ∫ w, intervalLength (I w) ∂finiteRandomizedMixture n nu0 :=
      intervalLength_integral_lower n I hRule hLength _ rho hrho.1.le
    _ ≤ worstNullLength n I := finiteRandomizedMixture_length_le_worst n nu0 hnull I hRule

/-- Equation (60): one public lower constant controls every fully honest randomized rule. -/
-- @node: honest_rule_frontier_lower_bound
lemma honest_rule_frontier_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, ∀ n, n0 ≤ n →
      ∀ I : IntervalRule n, IsIntervalRule n I → IsHonest n I →
        c * frontierRate n ≤ worstNullLength n I := by
  obtain ⟨c, hc, n0, h⟩ := rough_null_lower_mixture
  refine ⟨(11 / 20 : ℝ) * c, by positivity, n0, ?_⟩
  intro n hn I hRule hHonest
  obtain ⟨nu0, nu1, rho, hrho, hrate, hnull, halt, htv⟩ :=
    h n hn (fun P => sampleLaw P n) (fun _ => rfl)
  have htransfer := finite_mixture_length_transfer n nu0 nu1 rho hrho
    (fun i hi => (hnull i hi).1)
    (fun i hi => ⟨(halt i hi).1, (halt i hi).2.ge⟩) htv I hRule hHonest
  calc
    ((11 / 20 : ℝ) * c) * frontierRate n = (11 / 20 : ℝ) * (c * frontierRate n) := by ring
    _ ≤ (11 / 20 : ℝ) * rho := mul_le_mul_of_nonneg_left hrate (by norm_num)
    _ ≤ worstNullLength n I := htransfer

/-- Every model law has nonnegative marginal outcome densities bounded by four. -/
-- @node: model_marginalDensity_mem_Icc
lemma model_marginalDensity_mem_Icc (P : ObsLaw) (hModel : Model P)
    (a : Bool) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    marginalDensity P a y ∈ Set.Icc 0 4 := by
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact P.eta_nonneg a x y hx hy
  · exact (le_abs_self _).trans (model_marginalDensity_abs_le P hModel a y hy)

/-- The causal energy belongs to the public reporting range throughout the model. -/
-- @node: model_Psi_mem_Icc
lemma model_Psi_mem_Icc (P : ObsLaw) (hModel : Model P) : Psi P ∈ Set.Icc 0 16 := by
  constructor
  · exact integral_nonneg (fun _ => sq_nonneg _)
  · have hb : ∀ᵐ y ∂unitVolume, (delta P y) ^ 2 ≤ 16 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      have h0 := model_marginalDensity_mem_Icc P hModel false y hy
      have h1 := model_marginalDensity_mem_Icc P hModel true y hy
      have hd : |delta P y| ≤ 4 := by
        rw [delta, abs_le]
        constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
      nlinarith [sq_abs (delta P y), abs_nonneg (delta P y)]
    have h := integral_mono_ae (model_delta_integrable P hModel).2 (integrable_const (16 : ℝ)) hb
    simpa only [Psi, l2Squared, integral_const, probReal_univ, one_smul] using h

/-- The full reporting interval is a measurable connected rule at every sample size. -/
-- @node: fullInterval_isIntervalRule
lemma fullInterval_isIntervalRule (n : ℕ) :
    IsIntervalRule n (fun _ => Set.Icc 0 16) := by
  refine ⟨fun _ => ⟨Set.ordConnected_Icc, Set.Subset.rfl⟩, ?_⟩
  exact measurableSet_Icc.preimage measurable_snd

/-- The full reporting interval is honest for the original model at every sample size. -/
-- @node: fullInterval_isHonest
lemma fullInterval_isHonest (n : ℕ) : IsHonest n (fun _ => Set.Icc 0 16) := by
  intro P hP
  have htarget := model_Psi_mem_Icc P hP
  have hevent : {w : SampleSpace n | Psi P ∈ Set.Icc (0 : ℝ) 16} = Set.univ := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact htarget
  simp only [coverage, hevent, probReal_univ]
  norm_num

/-- The honest-rule optimization has a feasible value, including at small sample sizes. -/
-- @node: honest_frontier_feasible
lemma honest_frontier_feasible (n : ℕ) :
    {r : ℝ | ∃ I : IntervalRule n, IsIntervalRule n I ∧ IsHonest n I ∧
      r = worstNullLength n I}.Nonempty := by
  exact ⟨worstNullLength n (fun _ => Set.Icc 0 16), _,
    fullInterval_isIntervalRule n, fullInterval_isHonest n, rfl⟩

/-- Every admissible rule has nonnegative worst-null length, witnessed by the actual
non-flat equality law in the sanity construction. -/
-- @node: worstNullLength_nonneg
lemma worstNullLength_nonneg (n : ℕ) (I : IntervalRule n) (hRule : IsIntervalRule n I) :
    0 ≤ worstNullLength n I := by
  have hnull : NullModel (exampleLaw 0) := nonflat_example.2.1
  exact Real.sSup_nonneg' ⟨expectedLength (exampleLaw 0) n I,
    ⟨exampleLaw 0, hnull, rfl⟩, expectedLength_nonneg _ n I hRule⟩

/-- The optimization is bounded below by zero, so any honest rule bounds its infimum. -/
-- @node: honestLengthFrontier_le_rule
lemma honestLengthFrontier_le_rule (n : ℕ) (I : IntervalRule n)
    (hRule : IsIntervalRule n I) (hHonest : IsHonest n I) :
    honestLengthFrontier n ≤ worstNullLength n I := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨I', hRule', hHonest', rfl⟩
    exact worstNullLength_nonneg n I' hRule'
  · exact ⟨I, hRule, hHonest, rfl⟩

/-- Taking the infimum in (60) yields the sharp all-procedure minimax lower rate. -/
-- @node: honestLengthFrontier_lower_rate
lemma honestLengthFrontier_lower_rate :
    ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, ∀ n, n0 ≤ n →
      c * frontierRate n ≤ honestLengthFrontier n := by
  obtain ⟨c, hc, n0, h⟩ := honest_rule_frontier_lower_bound
  refine ⟨c, hc, n0, ?_⟩
  intro n hn
  apply le_csInf (honest_frontier_feasible n)
  rintro r ⟨I, hRule, hHonest, rfl⟩
  exact h n hn I hRule hHonest

end CausalSmith.Stat.DensityEffectRoughNull
