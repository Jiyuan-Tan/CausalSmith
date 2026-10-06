module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentTransport
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Construction
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.CosineRegularity
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.DatasetMarginals
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.TreeGeometry
/-! The shared-threshold direct experiment coupling and its independent-record transport cost. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The localized bump has integrated mass at most the length of its macro support. The result uses [the stated assumptions](hyp:hL,hhL) and establishes [the displayed conclusion](goal). -/
-- @node: bump_lintegral_le_macro_length
lemma bump_lintegral_le_macro_length (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4) :
    (∫⁻ x : Covariate, ENNReal.ofReal (bump hL x)) ≤ ENNReal.ofReal (2*hL) := by
  classical
  let W : Set Covariate := {x | |(x : ℝ)-x0| < hL}
  have hW : MeasurableSet W := measurableSet_lt (by fun_prop) measurable_const
  calc
    _ ≤ ∫⁻ x : Covariate, W.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ W
      · simp only [Set.indicator_of_mem hx]
        exact (ENNReal.ofReal_le_ofReal (bump_range hL x).2).trans_eq (by simp)
      · have hg : envelope hL x = 0 :=
          envelope_zero_of_radius_le hL hhL x (le_of_not_gt hx)
        simp [Set.indicator_of_notMem hx, bump, hg]
    _ = (volume : Measure Covariate) W := by
      rw [lintegral_indicator_const hW]
      simp
    _ ≤ _ := volume_covariate_neighborhood_le x0 hL

/-- The crossing probability includes the fair treatment probability. -/
-- @node: directCrossingMass
def directCrossingMass (hL : ℝ) (x : Covariate) : ℝ := separation hL * bump hL x / 2

/-- The crossing mass fits within the fair treated-zero atom.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL,x). -/
-- @node: directCrossingMass_range
lemma directCrossingMass_range (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4) (x : Covariate) :
    0 ≤ directCrossingMass hL x ∧ directCrossingMass hL x ≤ 1/4 := by
  have ht := separation_le_sqrt hL hhL
  have hb := bump_range hL x
  have hs : separation hL ≤ 1/4 := by
    dsimp [separation, kappa]
    linarith [hhL.2]
  dsimp [directCrossingMass]
  constructor
  · exact div_nonneg (mul_nonneg ht.1 hb.1) (by norm_num)
  · nlinarith [mul_le_mul_of_nonneg_left hb.2 ht.1]

/-- Integrating the shared thresholds leaves four common atoms and one crossing atom. -/
-- @node: directConditionalCoupling
def directConditionalCoupling (hL : ℝ) (x : Covariate) : Measure (O × O) :=
  ENNReal.ofReal (1/4 : ℝ) • Measure.dirac ((x,false,false),(x,false,false)) +
  ENNReal.ofReal (1/4 : ℝ) • Measure.dirac ((x,false,true),(x,false,true)) +
  ENNReal.ofReal (1/4 - directCrossingMass hL x) •
    Measure.dirac ((x,true,false),(x,true,false)) +
  ENNReal.ofReal (1/4 : ℝ) • Measure.dirac ((x,true,true),(x,true,true)) +
  ENNReal.ofReal (directCrossingMass hL x) •
    Measure.dirac ((x,true,false),(x,true,true))

/-- The finite shared-threshold law is a measurable conditional measure. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: measurable_directConditionalCoupling
@[fun_prop] lemma measurable_directConditionalCoupling (hL : ℝ) :
    Measurable (directConditionalCoupling hL) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [directConditionalCoupling, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hE, smul_eq_mul]
  unfold directCrossingMass
  have hdir (a b c d : Bool) :
      Measurable (fun x : Covariate => E.indicator (1 : O × O → ℝ≥0∞)
        ((x,a,b),(x,c,d))) :=
    (measurable_const.indicator hE).comp (by fun_prop)
  fun_prop

/-- Conditional shared thresholds have total mass one.  [the theorem's stated inputs and assumptions](hyp:x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: directConditionalCoupling_probability
lemma directConditionalCoupling_probability (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4)
    (x : Covariate) : IsProbabilityMeasure (directConditionalCoupling hL x) := by
  constructor
  have hw := directCrossingMass_range hL hhL x
  simp only [directConditionalCoupling, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num : (0 : ℝ) ≤ 1/4),
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1/4+1/4) (sub_nonneg.mpr hw.2),
    ← ENNReal.ofReal_add (by linarith : 0 ≤ 1/4+1/4+(1/4-directCrossingMass hL x))
      (by norm_num : (0 : ℝ) ≤ 1/4),
    ← ENNReal.ofReal_add (by linarith : 0 ≤ 1/4+1/4+(1/4-directCrossingMass hL x)+1/4) hw.1]
  rw [show (1/4+1/4+(1/4-directCrossingMass hL x)+1/4+directCrossingMass hL x : ℝ) = 1 by ring]
  exact ENNReal.ofReal_one

/-- Only the crossing atom contributes to the conditional disagreement cost. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: directConditionalCoupling_cost
lemma directConditionalCoupling_cost (hL : ℝ) (x : Covariate) :
    (∫⁻ z : O × O, if z.1 = z.2 then (0 : ℝ≥0∞) else 1
      ∂directConditionalCoupling hL x) = ENNReal.ofReal (directCrossingMass hL x) := by
  have hm : Measurable (fun z : O × O => if z.1 = z.2 then (0 : ℝ≥0∞) else 1) := by
    exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd)
      measurable_const measurable_const
  simp [directConditionalCoupling, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac' _ hm]

/-- Integrate the conditional shared-threshold coupling over the common uniform covariate. -/
-- @node: directRecordCoupling
def directRecordCoupling (hL : ℝ) : Measure (O × O) :=
  (volume : Measure Covariate).bind (directConditionalCoupling hL)

/-- The common covariate and conditional shared thresholds give a probability coupling law.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: directRecordCoupling_probability
lemma directRecordCoupling_probability (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4) :
    IsProbabilityMeasure (directRecordCoupling hL) := by
  constructor
  rw [directRecordCoupling, Measure.bind_apply MeasurableSet.univ
    (measurable_directConditionalCoupling hL).aemeasurable]
  have hu (x : Covariate) : directConditionalCoupling hL x Set.univ = 1 := by
    let := directConditionalCoupling_probability hL hhL x
    exact measure_univ
  simp_rw [hu]
  simp

/-- The fair marginal of the shared-threshold conditional coupling.  [the theorem's stated inputs and assumptions](hyp:x,E,hE), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: directConditionalCoupling_fst
lemma directConditionalCoupling_fst (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4)
    (x : Covariate) (E : Set O) (hE : MeasurableSet E) :
    directConditionalCoupling hL x (Prod.fst ⁻¹' E) =
      ∑ z : Bool × Bool, ENNReal.ofReal (1/4 : ℝ) *
        E.indicator (1 : O → ℝ≥0∞) (x,z.1,z.2) := by
  have hw := directCrossingMass_range hL hhL x
  have ha : ENNReal.ofReal (1/4-directCrossingMass hL x) +
      ENNReal.ofReal (directCrossingMass hL x) = ENNReal.ofReal (1/4 : ℝ) := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hw.2) hw.1]
    congr 1
    ring
  have hind (z : O × O) : (Prod.fst ⁻¹' E).indicator (1 : O × O → ℝ≥0∞) z =
      E.indicator (1 : O → ℝ≥0∞) z.1 := by rfl
  simp only [directConditionalCoupling, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurable_fst hE), smul_eq_mul]
  simp_rw [hind]
  change _ = _
  simp only [Set.indicator_preimage, Function.comp_apply, Fintype.sum_prod_type,
    Fintype.sum_bool]
  calc
    _ = ENNReal.ofReal (1/4 : ℝ) * E.indicator 1 (x,false,false) +
        ENNReal.ofReal (1/4 : ℝ) * E.indicator 1 (x,false,true) +
        (ENNReal.ofReal (1/4-directCrossingMass hL x) +
          ENNReal.ofReal (directCrossingMass hL x)) * E.indicator 1 (x,true,false) +
        ENNReal.ofReal (1/4 : ℝ) * E.indicator 1 (x,true,true) := by
          simp only [Set.indicator, Set.preimage, Set.mem_setOf_eq, Pi.one_apply, Prod.fst, Prod.snd]
          ring
    _ = _ := by rw [ha]; ring

/-- The treated marginal of the shared-threshold conditional coupling.  [the theorem's stated inputs and assumptions](hyp:x,E,hE), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: directConditionalCoupling_snd
lemma directConditionalCoupling_snd (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4)
    (x : Covariate) (E : Set O) (hE : MeasurableSet E) :
    directConditionalCoupling hL x (Prod.snd ⁻¹' E) =
      ∑ z : Bool × Bool,
        ENNReal.ofReal (bernoulliMass (1/2) z.1 *
          bernoulliMass (if z.1 then directMu1 hL x else 1/2) z.2) *
        E.indicator (1 : O → ℝ≥0∞) (x,z.1,z.2) := by
  have hw := directCrossingMass_range hL hhL x
  have ha : ENNReal.ofReal (1/4 : ℝ) + ENNReal.ofReal (directCrossingMass hL x) =
      ENNReal.ofReal (1/4+directCrossingMass hL x) :=
    (ENNReal.ofReal_add (by norm_num) hw.1).symm
  have hind (z : O × O) : (Prod.snd ⁻¹' E).indicator (1 : O × O → ℝ≥0∞) z =
      E.indicator (1 : O → ℝ≥0∞) z.2 := by rfl
  simp only [directConditionalCoupling, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurable_snd hE), smul_eq_mul,
    Set.indicator_preimage, Function.comp_apply, Fintype.sum_prod_type,
    Fintype.sum_bool, bernoulliMass, Bool.false_eq_true, if_false, if_true]
  simp_rw [hind]
  have hplus : (1/2 : ℝ) * directMu1 hL x = 1/4 + directCrossingMass hL x := by
    dsimp [directMu1, directCrossingMass]; ring
  have hminus : (1/2 : ℝ) * (1-directMu1 hL x) = 1/4 - directCrossingMass hL x := by
    dsimp [directMu1, directCrossingMass]; ring
  norm_num only at *
  rw [hplus, hminus]
  calc
    _ = ENNReal.ofReal (1/4 : ℝ) * E.indicator 1 (x,false,false) +
        ENNReal.ofReal (1/4 : ℝ) * E.indicator 1 (x,false,true) +
        ENNReal.ofReal (1/4-directCrossingMass hL x) * E.indicator 1 (x,true,false) +
        (ENNReal.ofReal (1/4 : ℝ) + ENNReal.ofReal (directCrossingMass hL x)) *
          E.indicator 1 (x,true,true) := by
          simp only [Set.indicator, Set.preimage, Set.mem_setOf_eq, Pi.one_apply, Prod.fst, Prod.snd]
          ring
    _ = _ := by rw [ha]; ring

/-- The first integrated marginal is the observed fair null law.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: directRecordCoupling_map_fst
lemma directRecordCoupling_map_fst (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4) :
    (directRecordCoupling hL).map Prod.fst = Pobs fairNull := by
  ext E hE
  rw [Measure.map_apply measurable_fst hE, directRecordCoupling,
    Measure.bind_apply (measurable_fst hE) (measurable_directConditionalCoupling hL).aemeasurable]
  simp_rw [directConditionalCoupling_fst hL hhL _ E hE]
  rw [fairNull, binaryCausalLaw_observed_apply _ _ _ measurable_const measurable_const
    measurable_const fair_parameters_range E hE]
  apply lintegral_congr
  intro x
  apply Finset.sum_congr rfl
  intro z _
  cases z.1 <;> cases z.2 <;> norm_num [bernoulliMass, Set.indicator, Pi.one_apply]

/-- The second integrated marginal is the observed direct alternative law.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: directRecordCoupling_map_snd
lemma directRecordCoupling_map_snd (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4) :
    (directRecordCoupling hL).map Prod.snd = Pobs (directAlternative hL hhL) := by
  ext E hE
  rw [Measure.map_apply measurable_snd hE, directRecordCoupling,
    Measure.bind_apply (measurable_snd hE) (measurable_directConditionalCoupling hL).aemeasurable,
    directAlternative, binaryCausalLaw_observed_apply _ _ _ measurable_const measurable_const
      (measurable_directMu1 hL) (direct_parameters_range hL hhL) E hE]
  exact lintegral_congr (fun x => directConditionalCoupling_snd hL hhL x E hE)

/-- The integrated disagreement cost is bounded by the crossing probability and macro support. The result uses [the stated assumptions](hyp:hL,hhL) and establishes [the displayed conclusion](goal). -/
-- @node: directRecordCoupling_cost_le
lemma directRecordCoupling_cost_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4) :
    (∫⁻ z : O × O, if z.1 = z.2 then (0 : ℝ≥0∞) else 1
      ∂directRecordCoupling hL) ≤ ENNReal.ofReal (separation hL*hL) := by
  have hm : Measurable (fun z : O × O => if z.1 = z.2 then (0 : ℝ≥0∞) else 1) :=
    Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd)
      measurable_const measurable_const
  have ht := (separation_le_sqrt hL hhL).1
  rw [directRecordCoupling, Measure.lintegral_bind
    (measurable_directConditionalCoupling hL).aemeasurable hm.aemeasurable]
  simp_rw [directConditionalCoupling_cost, directCrossingMass,
    show ∀ x : Covariate, separation hL * bump hL x / 2 =
      (separation hL/2)*bump hL x by intro x; ring,
    ENNReal.ofReal_mul (show 0 ≤ separation hL/2 from div_nonneg ht (by norm_num))]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal (separation hL/2)*ENNReal.ofReal (2*hL) :=
      mul_le_mul' le_rfl (bump_lintegral_le_macro_length hL hhL)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (show 0 ≤ separation hL/2 from div_nonneg ht (by norm_num))]
      congr 1
      ring

/-- Independent copies of the shared-threshold record pair are regrouped into two datasets. -/
-- @node: directDatasetCoupling
def directDatasetCoupling (hL : ℝ) (n : ℕ) : Measure (Dataset n × Dataset n) :=
  (Measure.pi (fun _ : Fin n => directRecordCoupling hL)).map
    (fun z => (fun i => (z i).1, fun i => (z i).2))

/-- The independent-record construction has the two prescribed product marginals.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL,n). -/
-- @node: directDatasetCoupling_isCoupling
lemma directDatasetCoupling_isCoupling (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4) (n : ℕ) :
    Causalean.Stat.IsCoupling (directDatasetCoupling hL n)
      (dataLaw n fairNull) (dataLaw n (directAlternative hL hhL)) := by
  let := directRecordCoupling_probability hL hhL
  have hu : Measurable (fun z : Fin n → O × O =>
      (fun i => (z i).1, fun i => (z i).2)) := by fun_prop
  refine ⟨Measure.isProbabilityMeasure_map hu.aemeasurable, ?_, ?_⟩
  · rw [directDatasetCoupling, Measure.map_map measurable_fst hu]
    change (Measure.pi (fun _ : Fin n => directRecordCoupling hL)).map
      (fun z i => (z i).1) = _
    rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
    simp_rw [directRecordCoupling_map_fst hL hhL]
    rfl
  · rw [directDatasetCoupling, Measure.map_map measurable_snd hu]
    change (Measure.pi (fun _ : Fin n => directRecordCoupling hL)).map
      (fun z i => (z i).2) = _
    rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
    simp_rw [directRecordCoupling_map_snd hL hhL]
    rfl

/-- Hamming cost adds the identical one-record crossing costs over all independent records. The result uses [the stated assumptions](hyp:hL,hhL) and establishes [the displayed conclusion](goal). -/
-- @node: directDatasetCoupling_cost_le
lemma directDatasetCoupling_cost_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4) (n : ℕ) :
    (∫⁻ z, (dHam n z.1 z.2 : ℝ≥0∞) ∂directDatasetCoupling hL n) ≤
      ENNReal.ofReal ((n : ℝ)*separation hL*hL) := by
  classical
  let := directRecordCoupling_probability hL hhL
  have hm : Measurable (fun z : O × O => if z.1 = z.2 then (0 : ℝ≥0∞) else 1) :=
    Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd)
      measurable_const measurable_const
  rw [directDatasetCoupling, lintegral_map (measurable_datasetHammingCost n) (by fun_prop)]
  simp only [dHam, hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [lintegral_finsetSum _ (fun i _ => by
    simpa only [ite_not, Function.comp_def] using hm.comp (measurable_pi_apply i))]
  have hi (i : Fin n) :
      (∫⁻ z : Fin n → O × O, if (z i).1 ≠ (z i).2 then (1 : ℝ≥0∞) else 0
        ∂Measure.pi (fun _ : Fin n => directRecordCoupling hL)) =
      ∫⁻ z : O × O, if z.1 = z.2 then (0 : ℝ≥0∞) else 1 ∂directRecordCoupling hL := by
    simpa only [ite_not, Function.comp_def] using
      (measurePreserving_eval (fun _ : Fin n => directRecordCoupling hL) i).lintegral_comp hm
  simp_rw [hi]
  calc
    _ ≤ ∑ _ : Fin n, ENNReal.ofReal (separation hL*hL) :=
      Finset.sum_le_sum (fun _ _ => directRecordCoupling_cost_le hL hhL)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      ring

end CausalSmith.Stat.PrivateCateRoughdesign
