module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.Estimator

/-! # Uniform block experiments

The measurable four-coin construction and its probability, score marginal,
consistency, bounded-potential, and sampling properties, together with the
tested logger, treatment-effect, and conditional-exchangeability identities.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

/-- Four independent uniforms: score, assignment coin, and two potential-outcome coins. -/
noncomputable def fourUniform : Measure (((ℝ × ℝ) × ℝ) × ℝ) :=
  ((uniformRandomizer.prod uniformRandomizer).prod uniformRandomizer).prod uniformRandomizer

/-- Shared logger, weak on the score block. -/
noncomputable def blockLogger (m q x : ℝ) : ℝ :=
  if x ≤ m then q else 1/2

/-- Control mean for the two-point rows. -/
noncomputable def blockMeanZero (m x : ℝ) : ℝ :=
  if x ≤ m then 0 else -1/2

/-- Treated mean for the two-point rows. -/
noncomputable def blockMeanOne (m h : ℝ) (σ : Bool) (x : ℝ) : ℝ :=
  if x ≤ m then (if σ then h else -h) else 1/2

/-- A {-1,+1}-valued outcome with prescribed mean when the mean lies in [-1,1]. -/
noncomputable def binaryOutcome (μ u : ℝ) : ℝ :=
  if u ≤ (1+μ)/2 then 1 else -1

/-- Full row-law construction from four independent uniform variables. -/
noncomputable def blockFull (m q h : ℝ) (σ : Bool) : Measure FullRow :=
  fourUniform.map fun v =>
    let x := v.1.1.1
    let action := decide (v.1.1.2 ≤ blockLogger m q x)
    let y0 := binaryOutcome (blockMeanZero m x) v.1.2
    let y1 := binaryOutcome (blockMeanOne m h σ x) v.2
    ⟨x, action, if action then y1 else y0, y0, y1⟩

/-- Generic same-logger pair. -/
noncomputable def blockPair (m q h : ℝ) (σ : Bool) : RowLaw :=
  let μ := blockFull m q h σ
  { full := μ
    logger := blockLogger m q
    tau := fun x => blockMeanOne m h σ x - blockMeanZero m x
    samples := fun k => Measure.pi fun _ : Fin k =>
      μ.map fun o => (⟨o.X,o.A,o.Y⟩ : Observation) }

/-- The block logger is Borel at its cutoff, including the endpoint. -/
@[fun_prop]
-- @node: blockLogger_measurable
lemma blockLogger_measurable (m q : ℝ) : Measurable (blockLogger m q) := by
  unfold blockLogger
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

/-- The control mean is a Borel step function. -/
@[fun_prop]
-- @node: blockMeanZero_measurable
lemma blockMeanZero_measurable (m : ℝ) : Measurable (blockMeanZero m) := by
  unfold blockMeanZero
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

/-- Each sign's treated mean is a Borel step function. -/
@[fun_prop]
-- @node: blockMeanOne_measurable
lemma blockMeanOne_measurable (m h : ℝ) (σ : Bool) :
    Measurable (blockMeanOne m h σ) := by
  unfold blockMeanOne
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

/-- The four-coin construction of the full row is measurable. -/
-- @node: blockFull_map_measurable
lemma blockFull_map_measurable (m q h : ℝ) (σ : Bool) :
    Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) =>
      let x := v.1.1.1
      let action := decide (v.1.1.2 ≤ blockLogger m q x)
      let y0 := binaryOutcome (blockMeanZero m x) v.1.2
      let y1 := binaryOutcome (blockMeanOne m h σ x) v.2
      (⟨x, action, if action then y1 else y0, y0, y1⟩ : FullRow)) := by
  apply measurable_comap_iff.mpr
  have ha : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) =>
      decide (v.1.1.2 ≤ blockLogger m q v.1.1.1)) := by
    apply measurable_to_bool
    simpa [Set.preimage] using
      (measurableSet_le (by fun_prop : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) => v.1.1.2))
        ((blockLogger_measurable m q).comp
          (by fun_prop : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) => v.1.1.1))))
  have hy0 : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) =>
      binaryOutcome (blockMeanZero m v.1.1.1) v.1.2) := by
    unfold binaryOutcome
    apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) <;> fun_prop
  have hy1 : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) =>
      binaryOutcome (blockMeanOne m h σ v.1.1.1) v.2) := by
    unfold binaryOutcome
    apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) <;> fun_prop
  have hy : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) =>
      if decide (v.1.1.2 ≤ blockLogger m q v.1.1.1) then
        binaryOutcome (blockMeanOne m h σ v.1.1.1) v.2
      else binaryOutcome (blockMeanZero m v.1.1.1) v.1.2) :=
    Measurable.ite (ha (measurableSet_singleton true)) hy1 hy0
  exact (by fun_prop : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) => v.1.1.1)).prodMk
    (ha.prodMk (hy.prodMk (hy0.prodMk hy1)))

/-- The uniform randomizer has total mass one. -/
-- @node: uniformRandomizer_probability
lemma uniformRandomizer_probability : IsProbabilityMeasure uniformRandomizer := by
  constructor
  norm_num [uniformRandomizer, Measure.restrict_apply, Real.volume_Icc]

/-- The four-uniform pushforward is a probability law for either sign. -/
-- @node: blockPair_probability
lemma blockPair_probability (m q h : ℝ) (σ : Bool) :
    IsProbabilityMeasure (blockPair m q h σ).full := by
  haveI := uniformRandomizer_probability
  haveI : IsProbabilityMeasure fourUniform := by unfold fourUniform; infer_instance
  exact Measure.isProbabilityMeasure_map (blockFull_map_measurable m q h σ).aemeasurable

/-- The score marginal of each constructed block experiment is uniform. -/
-- @node: blockPair_score_uniform
lemma blockPair_score_uniform (m q h : ℝ) (σ : Bool) :
    (blockPair m q h σ).PX = uniformRandomizer := by
  haveI := uniformRandomizer_probability
  have hX : Measurable FullRow.X := (comap_measurable _).fst
  change (fourUniform.map _).map FullRow.X = _
  rw [Measure.map_map hX (blockFull_map_measurable m q h σ)]
  change fourUniform.map (fun v => v.1.1.1) = _
  have h1 : fourUniform.map Prod.fst =
      (uniformRandomizer.prod uniformRandomizer).prod uniformRandomizer := by
    simp [fourUniform]
  have h2 : ((uniformRandomizer.prod uniformRandomizer).prod
      uniformRandomizer).map Prod.fst = uniformRandomizer.prod uniformRandomizer := by simp
  have h3 : (uniformRandomizer.prod uniformRandomizer).map Prod.fst =
      uniformRandomizer := by simp
  calc
    fourUniform.map (fun v => v.1.1.1) =
        ((fourUniform.map Prod.fst).map Prod.fst).map Prod.fst := by
      rw [Measure.map_map measurable_fst measurable_fst,
        Measure.map_map (measurable_fst.comp measurable_fst) measurable_fst]
      rfl
    _ = uniformRandomizer := by rw [h1, h2, h3]

/-- The uniform score marginal is a probability supported on the public interval. -/
-- @node: blockPair_score_borel
lemma blockPair_score_borel (m q h : ℝ) (σ : Bool) :
    BorelScoreMarginal (blockPair m q h σ) := by
  rw [BorelScoreMarginal, blockPair_score_uniform]
  refine ⟨uniformRandomizer_probability, ?_⟩
  simp [uniformRandomizer, Measure.restrict_apply, measurableSet_Icc.compl]

/-- The observed outcome in the block construction is the assigned potential. -/
-- @node: blockPair_consistency
lemma blockPair_consistency (m q h : ℝ) (σ : Bool) :
    Consistency (blockPair m q h σ) := by
  unfold Consistency blockPair blockFull
  dsimp only
  apply ae_map_iff (blockFull_map_measurable m q h σ).aemeasurable ?_ |>.2
  · exact Filter.Eventually.of_forall (fun _ => rfl)
  · have hcoords : Measurable (fun o : FullRow => (o.X, o.A, o.Y, o.Y0, o.Y1)) :=
      comap_measurable _
    exact measurableSet_eq_fun hcoords.snd.snd.fst
      (Measurable.ite (hcoords.snd.fst (measurableSet_singleton true))
        hcoords.snd.snd.snd.snd hcoords.snd.snd.snd.fst)

/-- Binary potential outcomes lie in the public range for every coin realization. -/
-- @node: blockPair_bounded_potentials
lemma blockPair_bounded_potentials (m q h : ℝ) (σ : Bool) :
    BoundedPotentials (blockPair m q h σ) := by
  unfold BoundedPotentials blockPair blockFull
  dsimp only
  apply ae_map_iff (blockFull_map_measurable m q h σ).aemeasurable ?_ |>.2
  · apply Filter.Eventually.of_forall
    intro v
    dsimp
    simp only [binaryOutcome]
    split_ifs <;> norm_num
  · have hcoords : Measurable (fun o : FullRow => (o.X, o.A, o.Y, o.Y0, o.Y1)) :=
      comap_measurable _
    exact (hcoords.snd.snd.snd.fst measurableSet_Icc).inter
      (hcoords.snd.snd.snd.snd measurableSet_Icc)

/-- The block construction assigns the product observation law to its samples. -/
-- @node: blockPair_iid
lemma blockPair_iid (m q h : ℝ) (σ : Bool) (n : ℕ) :
    IIDRows (blockPair m q h σ) n := by
  rfl

/-- A thresholded uniform coin has success probability equal to its cutoff. -/
-- @node: uniformRandomizer_coin_integral
lemma uniformRandomizer_coin_integral (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ u, (if u ≤ q then (1:ℝ) else 0) ∂uniformRandomizer) = q := by
  change (∫ u, (Set.Iic q).indicator (fun _ => (1:ℝ)) u ∂uniformRandomizer) = q
  rw [integral_indicator measurableSet_Iic, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  rw [Measure.real_def]
  rw [uniformRandomizer, Measure.restrict_apply measurableSet_Iic]
  have hs : Set.Iic q ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 q := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · tauto
    · intro hu
      exact ⟨hu.2, hu.1, hu.2.trans hq1⟩
  rw [hs, Real.volume_Icc]
  simp [hq]

/-- The threshold representation of a binary outcome is jointly Borel in its mean and coin. -/
@[fun_prop]
-- @node: binaryOutcome_measurable
lemma binaryOutcome_measurable : Measurable (fun z : ℝ × ℝ => binaryOutcome z.1 z.2) := by
  unfold binaryOutcome
  apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) <;> fun_prop

/-- A binary outcome with a feasible mean has that mean under a uniform coin. -/
-- @node: binaryOutcome_uniform_mean
lemma binaryOutcome_uniform_mean (μ : ℝ) (hμ : -1 ≤ μ) (hμ1 : μ ≤ 1) :
    (∫ u, binaryOutcome μ u ∂uniformRandomizer) = μ := by
  have := uniformRandomizer_probability
  have hm : Measurable (fun u : ℝ => if u ≤ (1+μ)/2 then (1:ℝ) else 0) := by
    apply Measurable.ite (measurableSet_le measurable_id measurable_const) <;> fun_prop
  have hi : Integrable (fun u : ℝ => if u ≤ (1+μ)/2 then (1:ℝ) else 0)
      uniformRandomizer := by
    exact Integrable.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (by intro u; split_ifs <;> norm_num))
  calc
    _ = ∫ u, 2 * (if u ≤ (1+μ)/2 then (1:ℝ) else 0) - 1 ∂uniformRandomizer := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (by intro u; by_cases hu : u ≤ (1+μ)/2 <;> norm_num [binaryOutcome, hu])
    _ = 2 * ((1+μ)/2) - 1 := by
      rw [integral_sub (hi.const_mul 2) (integrable_const 1), integral_const_mul,
        uniformRandomizer_coin_integral _ (by linarith) (by linarith)]
      simp
    _ = μ := by ring

/-- The binary-coin mean identity remains valid after testing on any measurable outer event. -/
-- @node: independent_binary_test_integral
lemma independent_binary_test_integral {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (k : Ω → ℝ) (hk : Measurable k)
    (hklo : ∀ x, -1 ≤ k x) (hkhi : ∀ x, k x ≤ 1)
    (S : Set Ω) (hS : MeasurableSet S) :
    (∫ z : Ω × ℝ, S.indicator (fun x => binaryOutcome (k x) z.2) z.1
      ∂ν.prod uniformRandomizer) = ∫ x in S, k x ∂ν := by
  classical
  have := uniformRandomizer_probability
  have hf : Integrable (fun z : Ω × ℝ =>
      if z.1 ∈ S then binaryOutcome (k z.1) z.2 else 0)
      (ν.prod uniformRandomizer) := by
    have hm : Measurable (fun z : Ω × ℝ =>
        if z.1 ∈ S then binaryOutcome (k z.1) z.2 else 0) := by
      apply Measurable.ite (measurable_fst hS) <;> fun_prop
    exact Integrable.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (by intro z; unfold binaryOutcome; split_ifs <;> norm_num))
  simp only [Set.indicator]
  rw [integral_prod _ hf, ← integral_indicator hS]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ S
  · simp only [hx, ↓reduceIte, Set.indicator_of_mem]
    exact binaryOutcome_uniform_mean (k x) (hklo x) (hkhi x)
  · simp [hx]

/-- The treated potential has its prescribed score-dependent mean on every Borel score set. -/
-- @node: blockPair_treated_mean_identity
lemma blockPair_treated_mean_identity (m q h : ℝ) (σ : Bool)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (B : Set ℝ) (hB : MeasurableSet B) :
    ∫ o in {o | o.X ∈ B}, o.Y1 ∂(blockPair m q h σ).full =
      ∫ x in B, blockMeanOne m h σ x ∂uniformRandomizer := by
  classical
  have := uniformRandomizer_probability
  have hcoords : Measurable (fun o : FullRow => (o.X, o.A, o.Y, o.Y0, o.Y1)) :=
    comap_measurable _
  have hs : MeasurableSet {o : FullRow | o.X ∈ B} := hcoords.fst hB
  change (∫ (o : FullRow) in {o | o.X ∈ B}, o.Y1 ∂fourUniform.map _) = _
  rw [setIntegral_map hs hcoords.snd.snd.snd.snd.aestronglyMeasurable
    (blockFull_map_measurable m q h σ).aemeasurable,
    ← integral_indicator ((blockFull_map_measurable m q h σ) hs)]
  simp only [Set.indicator, Set.mem_preimage, Set.mem_ofPred_eq]
  change (∫ v, (if v.1.1.1 ∈ B then binaryOutcome (blockMeanOne m h σ v.1.1.1) v.2 else 0)
    ∂fourUniform) = _
  unfold fourUniform
  have hmean := independent_binary_test_integral ((uniformRandomizer.prod uniformRandomizer).prod uniformRandomizer)
    (fun v : (ℝ × ℝ) × ℝ => blockMeanOne m h σ v.1.1) (by fun_prop)
    (by intro v; unfold blockMeanOne; cases σ <;> split_ifs <;> linarith)
    (by intro v; unfold blockMeanOne; cases σ <;> split_ifs <;> linarith)
    {v : (ℝ × ℝ) × ℝ | v.1.1 ∈ B} ((measurable_fst.comp measurable_fst) hB)
  simp only [Set.indicator, Set.mem_ofPred_eq] at hmean
  rw [hmean]
  rw [← integral_indicator (show MeasurableSet {v : (ℝ × ℝ) × ℝ | v.1.1 ∈ B} from
    (measurable_fst.comp measurable_fst) hB)]
  simp only [Set.indicator, Set.mem_ofPred_eq]
  change (∫ v : (ℝ × ℝ) × ℝ, (if v.1.1 ∈ B then blockMeanOne m h σ v.1.1 else 0)
    ∂(uniformRandomizer.prod uniformRandomizer).prod uniformRandomizer) = _
  rw [integral_fun_fst (fun v : ℝ × ℝ => if v.1 ∈ B then blockMeanOne m h σ v.1 else 0),
    integral_fun_fst (fun x : ℝ => if x ∈ B then blockMeanOne m h σ x else 0)]
  simp only [probReal_univ, one_smul]
  exact integral_indicator hB

/-- The control potential has its prescribed score-dependent mean on every Borel score set. -/
-- @node: blockPair_control_mean_identity
lemma blockPair_control_mean_identity (m q h : ℝ) (σ : Bool)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∫ o in {o | o.X ∈ B}, o.Y0 ∂(blockPair m q h σ).full =
      ∫ x in B, blockMeanZero m x ∂uniformRandomizer := by
  classical
  have := uniformRandomizer_probability
  have hcoords : Measurable (fun o : FullRow => (o.X, o.A, o.Y, o.Y0, o.Y1)) :=
    comap_measurable _
  have hs : MeasurableSet {o : FullRow | o.X ∈ B} := hcoords.fst hB
  change (∫ (o : FullRow) in {o | o.X ∈ B}, o.Y0 ∂fourUniform.map _) = _
  rw [setIntegral_map hs hcoords.snd.snd.snd.fst.aestronglyMeasurable
    (blockFull_map_measurable m q h σ).aemeasurable,
    ← integral_indicator ((blockFull_map_measurable m q h σ) hs)]
  simp only [Set.indicator, Set.mem_preimage, Set.mem_ofPred_eq]
  change (∫ v, (if v.1.1.1 ∈ B then binaryOutcome (blockMeanZero m v.1.1.1) v.1.2 else 0)
    ∂fourUniform) = _
  unfold fourUniform
  rw [integral_fun_fst (fun v : (ℝ × ℝ) × ℝ => if v.1.1 ∈ B then
    binaryOutcome (blockMeanZero m v.1.1) v.2 else 0)]
  simp only [probReal_univ, one_smul]
  have hmean := independent_binary_test_integral (uniformRandomizer.prod uniformRandomizer)
    (fun v : ℝ × ℝ => blockMeanZero m v.1) (by fun_prop)
    (by intro v; unfold blockMeanZero; split_ifs <;> norm_num)
    (by intro v; unfold blockMeanZero; split_ifs <;> norm_num)
    {v : ℝ × ℝ | v.1 ∈ B} (measurable_fst hB)
  simp only [Set.indicator, Set.mem_ofPred_eq] at hmean
  rw [hmean]
  rw [← integral_indicator (show MeasurableSet {v : ℝ × ℝ | v.1 ∈ B} from
    measurable_fst hB)]
  simp only [Set.indicator, Set.mem_ofPred_eq]
  change (∫ v : ℝ × ℝ, (if v.1 ∈ B then blockMeanZero m v.1 else 0)
    ∂uniformRandomizer.prod uniformRandomizer) = _
  rw [integral_fun_fst (fun x : ℝ => if x ∈ B then blockMeanZero m x else 0)]
  simp only [probReal_univ, one_smul]
  exact integral_indicator hB

/-- Integrating both potential-outcome coins yields the declared conditional treatment effect. -/
-- @node: blockPair_effect_identity
lemma blockPair_effect_identity (m q h : ℝ) (σ : Bool)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (B : Set ℝ) (hB : MeasurableSet B) :
    ∫ o in {o | o.X ∈ B}, (o.Y1-o.Y0) ∂(blockPair m q h σ).full =
      ∫ x in B, (blockPair m q h σ).tau x ∂(blockPair m q h σ).PX := by
  have := uniformRandomizer_probability
  have := blockPair_probability m q h σ
  have hcoords : Measurable (fun o : FullRow => (o.X, o.A, o.Y, o.Y0, o.Y1)) :=
    comap_measurable _
  have hi0 : Integrable (fun o : FullRow => o.Y0) (blockPair m q h σ).full := by
    apply Integrable.of_bound hcoords.snd.snd.snd.fst.aestronglyMeasurable 1
    filter_upwards [blockPair_bounded_potentials m q h σ] with o ho
    exact abs_le.mpr ho.1
  have hi1 : Integrable (fun o : FullRow => o.Y1) (blockPair m q h σ).full := by
    apply Integrable.of_bound hcoords.snd.snd.snd.snd.aestronglyMeasurable 1
    filter_upwards [blockPair_bounded_potentials m q h σ] with o ho
    exact abs_le.mpr ho.2
  have hm0 : Integrable (blockMeanZero m) uniformRandomizer := by
    exact Integrable.of_bound (blockMeanZero_measurable m).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (by intro x; unfold blockMeanZero; split_ifs <;> norm_num))
  have hm1 : Integrable (blockMeanOne m h σ) uniformRandomizer := by
    apply Integrable.of_bound (blockMeanOne_measurable m h σ).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_le]
    unfold blockMeanOne
    cases σ <;> split_ifs <;> constructor <;> linarith
  rw [integral_sub hi1.integrableOn hi0.integrableOn,
    blockPair_treated_mean_identity m q h σ hh hh1 B hB,
    blockPair_control_mean_identity m q h σ B hB,
    ← integral_sub hm1.integrableOn hm0.integrableOn, blockPair_score_uniform]
  rfl

/-- Integrating the independent assignment coin recovers the block logger on every Borel set. -/
-- @node: blockPair_logger_identity
lemma blockPair_logger_identity (m q h : ℝ) (σ : Bool)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (B : Set ℝ) (hB : MeasurableSet B) :
    ∫ o in {o | o.X ∈ B}, (if o.A then (1:ℝ) else 0) ∂(blockPair m q h σ).full =
      ∫ x in B, (blockPair m q h σ).logger x ∂(blockPair m q h σ).PX := by
  classical
  have := uniformRandomizer_probability
  have hcoords : Measurable (fun o : FullRow => (o.X, o.A, o.Y, o.Y0, o.Y1)) :=
    comap_measurable _
  have hA : Measurable (fun o : FullRow => if o.A then (1:ℝ) else 0) := by
    apply Measurable.ite (hcoords.snd.fst (measurableSet_singleton true)) <;> fun_prop
  rw [blockPair_score_uniform]
  change (∫ (o : FullRow) in {o | o.X ∈ B}, (if o.A then (1:ℝ) else 0)
    ∂fourUniform.map _) = ∫ x in B, blockLogger m q x ∂uniformRandomizer
  have hs : MeasurableSet {o : FullRow | o.X ∈ B} := hcoords.fst hB
  rw [setIntegral_map hs hA.aestronglyMeasurable
    (blockFull_map_measurable m q h σ).aemeasurable]
  rw [← integral_indicator ((blockFull_map_measurable m q h σ) hs)]
  simp only [Set.indicator, Set.mem_preimage, Set.mem_ofPred_eq, decide_eq_true_eq]
  change (∫ v, (if v.1.1.1 ∈ B then
      (if v.1.1.2 ≤ blockLogger m q v.1.1.1 then (1:ℝ) else 0) else 0)
    ∂fourUniform) = _
  unfold fourUniform
  rw [integral_fun_fst (fun v : (ℝ × ℝ) × ℝ => if v.1.1 ∈ B then
    (if v.1.2 ≤ blockLogger m q v.1.1 then (1:ℝ) else 0) else 0),
    integral_fun_fst (fun v : ℝ × ℝ => if v.1 ∈ B then
      (if v.2 ≤ blockLogger m q v.1 then (1:ℝ) else 0) else 0)]
  simp only [probReal_univ, one_smul]
  have hf : Integrable (fun v : ℝ × ℝ => if v.1 ∈ B then
      (if v.2 ≤ blockLogger m q v.1 then (1:ℝ) else 0) else 0)
      (uniformRandomizer.prod uniformRandomizer) := by
    have hmeas : Measurable (fun v : ℝ × ℝ => if v.1 ∈ B then
        (if v.2 ≤ blockLogger m q v.1 then (1:ℝ) else 0) else 0) := by
      apply Measurable.ite (measurable_fst hB)
      · apply Measurable.ite (measurableSet_le measurable_snd (by fun_prop)) <;> fun_prop
      · fun_prop
    exact Integrable.of_bound hmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (by intro v; split_ifs <;> norm_num))
  rw [integral_prod _ hf, ← integral_indicator hB]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ B
  · simp only [hx, ↓reduceIte, Set.indicator_of_mem]
    apply uniformRandomizer_coin_integral
    · unfold blockLogger; split_ifs <;> linarith
    · unfold blockLogger; split_ifs <;> linarith
  · simp [hx]

/-- Bounded Borel four-coin integrals can put assignment last, leaving potentials fixed. -/
-- @node: fourUniform_integral_assignment_last
lemma fourUniform_integral_assignment_last
    (f : (((ℝ × ℝ) × ℝ) × ℝ) → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : ∀ v, ‖f v‖ ≤ M) :
    (∫ v, f v ∂fourUniform) = ∫ y1, ∫ y0, ∫ x, ∫ u,
      f (((x,u),y0),y1) ∂uniformRandomizer ∂uniformRandomizer
        ∂uniformRandomizer ∂uniformRandomizer := by
  have := uniformRandomizer_probability
  unfold fourUniform
  rw [integral_prod_symm _ (Integrable.of_bound hf.aestronglyMeasurable M
    (Filter.Eventually.of_forall hM))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y1
  dsimp only
  have hm1 : Measurable (fun v : (ℝ × ℝ) × ℝ => f (v,y1)) := by fun_prop
  rw [integral_prod_symm _ (Integrable.of_bound hm1.aestronglyMeasurable M
    (Filter.Eventually.of_forall (fun v => hM (v,y1))))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y0
  dsimp only
  have hm0 : Measurable (fun v : ℝ × ℝ => f ((v,y0),y1)) := by fun_prop
  exact integral_prod _ (Integrable.of_bound hm0.aestronglyMeasurable M
    (Filter.Eventually.of_forall (fun v => hM ((v,y0),y1))))

/-- Either assignment sign has its Bernoulli probability under a uniform coin. -/
-- @node: uniformRandomizer_assignment_integral
lemma uniformRandomizer_assignment_integral (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (a : Bool) :
    (∫ u, (if decide (u ≤ q) = a then (1:ℝ) else 0) ∂uniformRandomizer) =
      if a then q else 1-q := by
  have := uniformRandomizer_probability
  cases a
  · have hm : Measurable (fun u : ℝ => if u ≤ q then (1:ℝ) else 0) := by
      apply Measurable.ite (measurableSet_le measurable_id measurable_const) <;> fun_prop
    have hi : Integrable (fun u : ℝ => if u ≤ q then (1:ℝ) else 0) uniformRandomizer :=
      Integrable.of_bound hm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall (by intro u; split_ifs <;> norm_num))
    calc
      _ = ∫ u, 1 - (if u ≤ q then (1:ℝ) else 0) ∂uniformRandomizer := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (by intro u; by_cases hu : u ≤ q <;> simp [hu])
      _ = 1-q := by
        rw [integral_sub (integrable_const 1) hi, uniformRandomizer_coin_integral q hq hq1]
        simp
  · simpa using uniformRandomizer_coin_integral q hq hq1

/-- Assignment is conditionally independent of both potentials in the four-uniform construction. -/
-- @node: blockPair_exchangeability
lemma blockPair_exchangeability (m q h : ℝ) (σ : Bool)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) : Exchangeability (blockPair m q h σ) := by
  classical
  have := uniformRandomizer_probability
  intro B hB g hg hgBound a
  obtain ⟨M, hM⟩ := hgBound
  have hM0 : 0 ≤ M := (abs_nonneg (g (0,0))).trans (hM (0,0))
  have hp : ∀ x, 0 ≤ blockLogger m q x ∧ blockLogger m q x ≤ 1 := by
    intro x
    unfold blockLogger
    split_ifs <;> constructor <;> linarith
  have hw : ∀ x, |if a then blockLogger m q x else 1-blockLogger m q x| ≤ 1 := by
    intro x
    have := hp x
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rw [abs_le] <;> constructor <;> linarith
  have hcoords : Measurable (fun o : FullRow => (o.X, o.A, o.Y, o.Y0, o.Y1)) :=
    comap_measurable _
  have hpot : Measurable (fun o : FullRow => g (o.Y0,o.Y1)) :=
    hg.comp (hcoords.snd.snd.snd.fst.prodMk hcoords.snd.snd.snd.snd)
  have hr : Measurable (fun o : FullRow =>
      (if a then blockLogger m q o.X else 1-blockLogger m q o.X) * g (o.Y0,o.Y1)) := by
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact (measurable_const.sub ((blockLogger_measurable m q).comp hcoords.fst)).mul hpot
    · exact ((blockLogger_measurable m q).comp hcoords.fst).mul hpot
  have hsL : MeasurableSet {o : FullRow | o.X ∈ B ∧ o.A = a} :=
    (hcoords.fst hB).inter (hcoords.snd.fst (measurableSet_singleton a))
  have hsR : MeasurableSet {o : FullRow | o.X ∈ B} := hcoords.fst hB
  change (∫ (o : FullRow) in {o | o.X ∈ B ∧ o.A = a}, g (o.Y0,o.Y1) ∂fourUniform.map _) =
    ∫ (o : FullRow) in {o | o.X ∈ B},
      (if a then blockLogger m q o.X else 1-blockLogger m q o.X) * g (o.Y0,o.Y1)
        ∂fourUniform.map _
  rw [setIntegral_map hsL hpot.aestronglyMeasurable
    (blockFull_map_measurable m q h σ).aemeasurable,
    setIntegral_map hsR hr.aestronglyMeasurable
      (blockFull_map_measurable m q h σ).aemeasurable,
    ← integral_indicator ((blockFull_map_measurable m q h σ) hsL),
    ← integral_indicator ((blockFull_map_measurable m q h σ) hsR)]
  simp only [Set.indicator, Set.mem_preimage, Set.mem_ofPred_eq]
  let F := fun v : (((ℝ × ℝ) × ℝ) × ℝ) =>
    if v.1.1.1 ∈ B ∧ decide (v.1.1.2 ≤ blockLogger m q v.1.1.1) = a then
      g (binaryOutcome (blockMeanZero m v.1.1.1) v.1.2,
        binaryOutcome (blockMeanOne m h σ v.1.1.1) v.2) else 0
  let G := fun v : (((ℝ × ℝ) × ℝ) × ℝ) => if v.1.1.1 ∈ B then
    (if a then blockLogger m q v.1.1.1 else 1-blockLogger m q v.1.1.1) *
      g (binaryOutcome (blockMeanZero m v.1.1.1) v.1.2,
        binaryOutcome (blockMeanOne m h σ v.1.1.1) v.2) else 0
  change (∫ v, F v ∂fourUniform) = ∫ v, G v ∂fourUniform
  have hF : Measurable F := by
    unfold F
    apply Measurable.ite
    · apply MeasurableSet.inter
      · exact (by fun_prop : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) => v.1.1.1)) hB
      · have hd : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) =>
            decide (v.1.1.2 ≤ blockLogger m q v.1.1.1)) := by
          apply measurable_to_bool
          simpa only [Set.preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff, decide_eq_true_eq] using
            (measurableSet_le
              (by fun_prop : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) => v.1.1.2))
              (by fun_prop : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) => blockLogger m q v.1.1.1)))
        exact hd (measurableSet_singleton a)
    · fun_prop
    · fun_prop
  have hG : Measurable G := by
    unfold G
    apply Measurable.ite
    · exact (by fun_prop : Measurable (fun v : (((ℝ × ℝ) × ℝ) × ℝ) => v.1.1.1)) hB
    · cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
    · fun_prop
  have hFb : ∀ v, ‖F v‖ ≤ M := by
    intro v
    dsimp [F]
    split_ifs
    · exact hM _
    · simpa using hM0
  have hGb : ∀ v, ‖G v‖ ≤ M := by
    intro v
    dsimp [G]
    by_cases hx : v.1.1.1 ∈ B
    · simp only [hx, ↓reduceIte]
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hw _) (abs_nonneg _)).trans (by simpa using hM _)
    · simpa [hx] using hM0
  rw [fourUniform_integral_assignment_last F hF M hFb,
    fourUniform_integral_assignment_last G hG M hGb]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y0
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp [F, G]
  by_cases hx : x ∈ B
  · simp only [hx, true_and, ↓reduceIte]
    have heq : (fun u : ℝ => if decide (u ≤ blockLogger m q x) = a then
        g (binaryOutcome (blockMeanZero m x) y0, binaryOutcome (blockMeanOne m h σ x) y1)
          else 0) = fun u => (if decide (u ≤ blockLogger m q x) = a then (1:ℝ) else 0) *
        g (binaryOutcome (blockMeanZero m x) y0, binaryOutcome (blockMeanOne m h σ x) y1) := by
      funext u
      split_ifs <;> simp
    rw [heq, integral_mul_const, uniformRandomizer_assignment_integral _ (hp x).1 (hp x).2]
    simp
  · simp [hx]

end CausalSmith.Stat.ScorethresholdOverlapRegret
