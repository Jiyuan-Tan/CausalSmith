module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.PilotSamplingLaw
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ObservedDesignMeans
public import Causalean.Stat.Concentration.TailBounds.BinomialCount
public import Causalean.Stat.Sample.PiTransport
/-!
Observed-law lower tails for all arm/covariate training counts. The model
overlap and uniform cell masses feed the library Chernoff bound; the finite
union and sampling transport discharge equation (17). The outcome tail
parameter is converted exactly to the public power budget.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.DensityEffectRoughNull
/-- Finite IID lower tail at half a lower bound on the mean. -/
-- @node: pilot_finite_count_half_tail_le
lemma pilot_finite_count_half_tail_le {E : Type*} [MeasurableSpace E]
    (Q : Measure E) [IsProbabilityMeasure Q] (f : E → ℝ)
    (hf : Measurable f) (h01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (m : ℕ) (p : ℝ) (hp : 0 ≤ p) (hmean : p ≤ ∫ x, f x ∂Q) :
    (Measure.pi (fun _ : Fin m => Q)).real
      {z | (∑ i : Fin m, f (z i)) ≤ (m : ℝ) * p / 2} ≤
        Real.exp (-((m : ℝ) * p) / 8) := by
  let S := Causalean.Stat.iidSample_infinitePi Q
  have hmeas : MeasurableSet {z : Fin m → E |
      (∑ i : Fin m, f (z i)) ≤ (m : ℝ) * p / 2} := by
    exact measurableSet_le (by fun_prop) measurable_const
  rw [← Causalean.Stat.iidSample_finN_pushforward S m, measureReal_def,
    Measure.map_apply (Causalean.Stat.iidSample_finN_measurable S m) hmeas]
  have heq : (fun ω : ℕ → E => ∑ i : Fin m, f (S.Z i ω)) =
      Causalean.Stat.Concentration.bernoulliCount S f m := by
    funext ω
    exact Fin.sum_univ_eq_sum_range (fun i => f (S.Z i ω)) m
  change (Measure.infinitePi (fun _ : ℕ => Q)).real
    {ω | (∑ i : Fin m, f (S.Z i ω)) ≤ (m : ℝ) * p / 2} ≤ _
  rw [show {ω : ℕ → E | (∑ i : Fin m, f (S.Z i ω)) ≤ (m : ℝ) * p / 2} =
    {ω | Causalean.Stat.Concentration.bernoulliCount S f m ω ≤ (m : ℝ) * p / 2}
    from congrArg (fun g => {ω | g ω ≤ (m : ℝ) * p / 2}) heq]
  apply (Causalean.Stat.Concentration.boundedCount_lower_tail_of_tilt S hf h01
    hmean m (-Real.log 2) (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith)).trans
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_two_lt_d9.trans (by norm_num : (0.6931471808 : ℝ) < 3 / 4)
  have hmp : 0 ≤ (m : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  nlinarith

/-- Every arm has at least a quarter of each uniform covariate cell's mass. -/
-- @node: pilot_arm_cell_mass_lower
lemma pilot_arm_cell_mass_lower (P : ObsLaw) (hModel : Model P)
    (mx : ℕ) (hmx : 0 < mx) (c : Fin mx) (a : Bool) :
    1 / (4 * (mx : ℝ)) ≤
      P.law.real {o | cell mx (X o) = c.val + 1 ∧ A o = a} := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let B : Set ℝ := {x | cell mx x = c.val + 1}
  have hB : MeasurableSet B := measurable_cell mx (measurableSet_singleton _)
  change 1 / (4 * (mx : ℝ)) ≤ P.law.real {o | X o ∈ B ∧ A o = a}
  rw [observed_arm_covariate_mass P a B hB]
  have hmass : unitVolume.real B = 1 / (mx : ℝ) := by
    have heq : unitVolume B = unitVolume (histogramCell mx (c.val + 1)) := by
      rw [unitVolume, Measure.restrict_apply hB,
        Measure.restrict_apply (measurableSet_histogramCell _ _)]
      congr 1
      ext x
      simp [B, histogramCell, and_comm, and_left_comm]
    rw [measureReal_def, heq, ← measureReal_def, histogramCell_mass_eq mx hmx c]
  calc
    _ = ∫ _x in B, (1 / 4 : ℝ) ∂unitVolume := by
      rw [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ, ← measureReal_def, hmass]
      ring
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) (integrable_pi_design P a).integrableOn
      filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with x hx
      exact (model_pi_mem_Icc P hModel a x hx).1

/-- The observed arm-cell count has the roadmap's single-cell exponential tail. -/
-- @node: pilot_arm_cell_count_tail_le
lemma pilot_arm_cell_count_tail_le (P : ObsLaw) (hModel : Model P)
    (m mx : ℕ) (hmx : 0 < mx) (a : Bool) (x : ℝ) :
    (dataLaw P m).real {train |
      (armCellCount train mx a x : ℝ) < (m : ℝ) / (8 * mx)} ≤
        Real.exp (-(m : ℝ) / (32 * mx)) := by
  let : IsProbabilityMeasure (dataLaw P m) := by unfold dataLaw; infer_instance
  let c : Fin mx := ⟨cell mx x - 1, by have := cell_index_mem mx hmx x; omega⟩
  have hc : c.val + 1 = cell mx x := by
    dsimp [c]
    have := cell_index_mem mx hmx x
    omega
  let E : Set Omega := {o | cell mx (X o) = c.val + 1 ∧ A o = a}
  have hE : MeasurableSet E := by
    apply MeasurableSet.inter
    · exact measurableSet_eq_fun ((measurable_cell mx).comp measurable_fst) measurable_const
    · exact measurableSet_eq_fun (by unfold A; fun_prop) measurable_const
  let f : Omega → ℝ := E.indicator (fun _ => 1)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have h01 : ∀ o, f o ∈ Set.Icc (0 : ℝ) 1 := by
    intro o
    by_cases h : o ∈ E <;> simp [f, h]
  have hmean : 1 / (4 * (mx : ℝ)) ≤ ∫ o, f o ∂P.law := by
    rw [show f = E.indicator (fun _ => (1 : ℝ)) from rfl,
      integral_indicator hE, integral_const, smul_eq_mul]
    simpa [measureReal_def, E] using pilot_arm_cell_mass_lower P hModel mx hmx c a
  have hid (train : Fin m → Omega) : (∑ i : Fin m, f (train i)) =
      (armCellCount train mx a x : ℝ) := by
    simp only [f, Set.indicator, Set.mem_setOf_eq, E, hc, armCellCount]
    exact Finset.sum_boole _ _
  have ht := pilot_finite_count_half_tail_le P.law f hf h01 m (1 / (4 * mx))
    (by positivity) hmean
  have hr : (m : ℝ) * (1 / (4 * mx)) / 2 = (m : ℝ) / (8 * mx) := by ring
  have he : -((m : ℝ) * (1 / (4 * mx))) / 8 = -(m : ℝ) / (32 * mx) := by ring
  rw [he] at ht
  apply le_trans (b := (dataLaw P m).real
    {train | (∑ i : Fin m, f (train i)) ≤ (m : ℝ) * (1 / (4 * mx)) / 2})
  · refine measureReal_mono ?_ (measure_ne_top _ _)
    intro train htrain
    change (∑ i : Fin m, f (train i)) ≤ _
    rw [hid, hr]
    exact le_of_lt htrain
  · exact ht

/-- A fixed midpoint represents each histogram cell, including its endpoints. -/
-- @node: pilot_cell_midpoint_mem
lemma pilot_cell_midpoint_mem (mx : ℕ) (hmx : 0 < mx) (c : Fin mx) :
    ((c.val : ℝ) + 1 / 2) / mx ∈ histogramCell mx (c.val + 1) := by
  apply bin_subset_histogramCell mx hmx c
  have hp : (0 : ℝ) < mx := by exact_mod_cast hmx
  constructor
  · apply (div_le_div_iff_of_pos_right hp).mpr
    linarith
  · apply (div_lt_div_iff_of_pos_right hp).mpr
    linarith

/-- The union over both arms and all cells gives exactly the count failure
budget in equation (17), without a dyadic or sample-size restriction. -/
-- @node: pilot_arm_counts_iid_tail_le
lemma pilot_arm_counts_iid_tail_le (P : ObsLaw) (hModel : Model P)
    (m mx : ℕ) (hmx : 0 < mx) :
    (dataLaw P m).real {train | ¬(∀ a x, x ∈ Set.Icc 0 1 →
      (m : ℝ) / (8 * mx) ≤ armCellCount train mx a x)} ≤
        2 * (mx : ℝ) * Real.exp (-(m : ℝ) / (32 * mx)) := by
  let : IsProbabilityMeasure (dataLaw P m) := by unfold dataLaw; infer_instance
  let midpoint (c : Fin mx) : ℝ := ((c.val : ℝ) + 1 / 2) / mx
  let E (c : Fin mx × Bool) : Set (Data m) :=
    {train | (armCellCount train mx c.2 (midpoint c.1) : ℝ) < (m : ℝ) / (8 * mx)}
  have hsub : {train : Data m | ¬(∀ a x, x ∈ Set.Icc 0 1 →
      (m : ℝ) / (8 * mx) ≤ armCellCount train mx a x)} ⊆ ⋃ c, E c := by
    intro train hbad
    change ¬(∀ a x, x ∈ Set.Icc 0 1 → _ ≤ _) at hbad
    push_neg at hbad
    obtain ⟨a, x, hx, hfail⟩ := hbad
    let c : Fin mx := ⟨cell mx x - 1, by have := cell_index_mem mx hmx x; omega⟩
    have hc : cell mx (midpoint c) = cell mx x := by
      have hm := (pilot_cell_midpoint_mem mx hmx c).2
      dsimp [midpoint, c] at *
      have := cell_index_mem mx hmx x
      omega
    apply Set.mem_iUnion.mpr
    refine ⟨(c, a), ?_⟩
    change (armCellCount train mx a (midpoint c) : ℝ) < _
    simpa only [armCellCount, hc] using hfail
  calc
    _ ≤ (dataLaw P m).real (⋃ c, E c) := measureReal_mono hsub
    _ ≤ ∑ c, (dataLaw P m).real (E c) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _c : Fin mx × Bool, Real.exp (-(m : ℝ) / (32 * mx)) := by
      apply Finset.sum_le_sum
      intro c _
      exact pilot_arm_cell_count_tail_le P hModel m mx hmx c.2 (midpoint c.1)
    _ = _ := by simp; ring

/-- The actual randomized sampling law satisfies the simultaneous count bound
for the training fold, with all remaining roles integrated out. -/
-- @node: pilot_arm_counts_sampling_tail_le
lemma pilot_arm_counts_sampling_tail_le (P : ObsLaw) (hModel : Model P)
    (m mx : ℕ) (hmx : 0 < mx)
    (ν : Measure (SampleSpace (13 * m))) (hSampling : SamplingLaw P (13 * m) ν) :
    ν.real {ω | ¬(∀ a x, x ∈ Set.Icc 0 1 →
      (m : ℝ) / (8 * mx) ≤ armCellCount (foldData (13 * m) ω.1 0) mx a x)} ≤
        2 * (mx : ℝ) * Real.exp (-(m : ℝ) / (32 * mx)) := by
  let E : Set (Data (roleSize (13 * m))) := {train | ¬(∀ a x,
    x ∈ Set.Icc 0 1 → (m : ℝ) / (8 * mx) ≤ armCellCount train mx a x)}
  exact (samplingLaw_foldData_real_le P (13 * m) ν hSampling 0 E).trans (by
    have hmrole : roleSize (13 * m) = m := by simp [roleSize]
    dsimp only [E]
    generalize roleSize (13 * m) = r at *
    subst r
    exact pilot_arm_counts_iid_tail_le P hModel m mx hmx)

/-- The Bernstein tail parameter is exactly the power used in the public
failure allowance, rather than an asymptotic substitute. -/
-- @node: pilot_exp_log_tail_eq_zpow
lemma pilot_exp_log_tail_eq_zpow (m : ℕ) (hm : 0 < m) :
    Real.exp (-(30 * Real.log m)) = (m : ℝ) ^ (-30 : ℤ) := by
  have hp : (0 : ℝ) < m := by exact_mod_cast hm
  conv_rhs => rw [← Real.exp_log (zpow_pos hp (-30))]
  rw [Real.log_zpow]
  congr 1
  norm_num

/-- Count and outcome contributions to pilot failure are discharged;
the propensity contribution retains the same count-good event. -/
-- @node: pilot_good_sampling_tail_le_count_budget
lemma pilot_good_sampling_tail_le_count_budget (P : ObsLaw) (hModel : Model P)
    (m mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my)
    (ν : Measure (SampleSpace (13 * m))) (hSampling : SamplingLaw P (13 * m) ν) :
    ν.real {ω | ¬GoodPilot P (foldData (13 * m) ω.1 0) (2 ^ 16) mx my} ≤
      2 * (mx : ℝ) * Real.exp (-(m : ℝ) / (32 * mx)) +
      ν.real {ω | (∀ a x, x ∈ Set.Icc 0 1 →
        (m : ℝ) / (8 * mx) ≤ armCellCount (foldData (13 * m) ω.1 0) mx a x) ∧
        ∃ a x, x ∈ Set.Icc 0 1 ∧ hAllow (2 ^ 16) m mx my <
        |pilotPi (foldData (13 * m) ω.1 0) mx a x - pi P a x|} +
      4 * (mx : ℝ) * my * (m : ℝ) ^ (-30 : ℤ) := by
  apply (pilot_good_sampling_tail_le P hModel m mx my hm hmx hmy ν hSampling).trans
  rw [pilot_exp_log_tail_eq_zpow m (by omega)]
  exact add_le_add
    (add_le_add (pilot_arm_counts_sampling_tail_le P hModel m mx hmx ν hSampling) le_rfl)
    le_rfl

end CausalSmith.Stat.DensityEffectRoughNull
