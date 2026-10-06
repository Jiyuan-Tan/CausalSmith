module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.PilotCountTail

/-!
Conditional treatment Bernstein bounds for the propensity histogram. Retaining
the exact supported covariates makes the treatment trials independent; the model
Hölder condition controls the bias of their cellwise conditional mean.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The covariate cell label used for treatment concentration. -/
-- @node: pilotCovariateKey
def pilotCovariateKey (mx : ℕ) (hmx : 0 < mx) (x : Set.Icc (0 : ℝ) 1) : Fin mx :=
  ⟨cell mx x.val - 1, by have := cell_index_mem mx hmx x.val; omega⟩

-- @node: pilotCovariateKey_eq_iff
lemma pilotCovariateKey_eq_iff (mx : ℕ) (hmx : 0 < mx)
    (x y : Set.Icc (0 : ℝ) 1) :
    pilotCovariateKey mx hmx x = pilotCovariateKey mx hmx y ↔
      cell mx x.val = cell mx y.val := by
  have := cell_index_mem mx hmx x.val
  have := cell_index_mem mx hmx y.val
  simp only [pilotCovariateKey, Fin.mk.injEq]
  omega

-- @node: measurableSet_pilotCovariateKey
lemma measurableSet_pilotCovariateKey (mx : ℕ) (hmx : 0 < mx) (c : Fin mx) :
    MeasurableSet {x | pilotCovariateKey mx hmx x = c} := by
  have hm : Measurable (fun x : Set.Icc (0 : ℝ) 1 => cell mx x.val - 1) :=
    ((measurable_cell mx).comp measurable_subtype_coe).sub measurable_const
  simpa only [pilotCovariateKey, Fin.ext_iff] using
    measurableSet_eq_fun hm (measurable_const (a := c.val))

/-- The treatment bin probability is the given propensity version. -/
-- @node: pilot_treatment_binProbability_eq
lemma pilot_treatment_binProbability_eq (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.Concentration.ConditionalBernstein.binProbability
      (causalTreatmentKernel P) {true} x = P.e x.val := by
  rw [Causalean.Stat.Concentration.ConditionalBernstein.binProbability,
    measureReal_def, causalTreatmentKernel_apply_singleton]
  simpa [pi, armProbability] using ENNReal.toReal_ofReal (P.e_range x.val x.property).1

/-- Equation (16), simultaneously over all covariate cells, conditional on
the retained covariates and then integrated over their IID law. -/
-- @node: pilot_treatment_iid_bernstein_tail_le
lemma pilot_treatment_iid_bernstein_tail_le (P : ObsLaw) (m mx : ℕ)
    (hmx : 0 < mx) (u : ℝ) (hu : 0 ≤ u) :
    (Measure.pi (fun _ : Fin m => pilotDesignLaw P)).real
      {z | ((fun i => (z i).1), (fun i => (z i).2)) ∈
        Causalean.Stat.Concentration.ConditionalBernstein.histogramBadEvent
        (pilotCovariateKey mx hmx) (causalTreatmentKernel P)
        (fun _ : Fin 1 => ({true} : Set Bool)) 1 u} ≤
      2 * (mx : ℝ) * Real.exp (-u) := by
  have h := Causalean.Stat.Concentration.ConditionalBernstein.iid_joint_simultaneous_tail_le
    (n := m) causalCovariateLaw (causalTreatmentKernel P) (pilotCovariateKey mx hmx)
    (fun _ : Fin 1 => ({true} : Set Bool))
    (measurableSet_pilotCovariateKey mx hmx) (fun _ => measurableSet_singleton true)
    (by norm_num : (0 : ℝ) ≤ 1) hu
    (Filter.Eventually.of_forall (fun x _c _j _hi => by
      rw [pilot_treatment_binProbability_eq]
      exact (P.e_range x.val x.property).2))
  simpa [pilotDesignLaw, Causalean.Stat.Concentration.ConditionalBernstein.histogramBadEvent] using h

/-- Reconstructing records with arbitrary outcomes leaves covariate counts unchanged. -/
-- @node: pilot_propensity_cellCount_eq
lemma pilot_propensity_cellCount_eq {m : ℕ} (mx : ℕ) (hmx : 0 < mx)
    (d : Fin m → PilotDesign) (v : Fin m → ℝ) (x : Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.Concentration.ConditionalBernstein.cellCount
      (pilotCovariateKey mx hmx) (pilotCovariateKey mx hmx x) (fun i => (d i).1) =
      cellCount (pilotTrainingRecords d v) mx x.val := by
  classical
  simp only [Causalean.Stat.Concentration.ConditionalBernstein.cellCount,
    cellCount, pilotTrainingRecords, X, pilotCovariateKey_eq_iff]
  exact (Finset.card_filter _ _).symm

/-- Treatment successes are exactly the true-arm training count. -/
-- @node: pilot_propensity_jointCount_eq
lemma pilot_propensity_jointCount_eq {m : ℕ} (mx : ℕ) (hmx : 0 < mx)
    (d : Fin m → PilotDesign) (v : Fin m → ℝ) (x : Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.Concentration.ConditionalBernstein.jointCount
      (pilotCovariateKey mx hmx) {true} (pilotCovariateKey mx hmx x)
      (fun i => (d i).1) (fun i => (d i).2) =
      armCellCount (pilotTrainingRecords d v) mx true x.val := by
  classical
  simp only [Causalean.Stat.Concentration.ConditionalBernstein.jointCount,
    armCellCount, pilotTrainingRecords, X, A, pilotCovariateKey_eq_iff, Set.mem_singleton_iff]
  exact (Finset.card_filter _ _).symm

/-- Averaging the exact conditional treatment means over a cell introduces
only the model's covariate Hölder bias, as in (18). -/
-- @node: pilot_propensity_conditional_bias_le
lemma pilot_propensity_conditional_bias_le (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (mx : ℕ) (hmx : 0 < mx) (d : Fin m → PilotDesign)
    (x : Set.Icc (0 : ℝ) 1)
    (hcount : 0 < Causalean.Stat.Concentration.ConditionalBernstein.cellCount
      (pilotCovariateKey mx hmx) (pilotCovariateKey mx hmx x) (fun i => (d i).1)) :
    |Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean
      (pilotCovariateKey mx hmx) (causalTreatmentKernel P) {true}
      (pilotCovariateKey mx hmx x) (fun i => (d i).1) /
      (Causalean.Stat.Concentration.ConditionalBernstein.cellCount
        (pilotCovariateKey mx hmx) (pilotCovariateKey mx hmx x)
        (fun i => (d i).1) : ℝ) - P.e x.val| ≤
      10 * (mx : ℝ) ^ (-1 / 10 : ℝ) := by
  classical
  let key := pilotCovariateKey mx hmx
  let c := key x
  let N := Causalean.Stat.Concentration.ConditionalBernstein.cellCount key c (fun i => (d i).1)
  let D := 10 * (mx : ℝ) ^ (-1 / 10 : ℝ)
  let M := Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean
    key (causalTreatmentKernel P) {true} c (fun i => (d i).1)
  have hN : (0 : ℝ) < N := by exact_mod_cast hcount
  have hsum : |∑ i : Fin m, if key (d i).1 = c then P.e (d i).1.val - P.e x.val else 0| ≤
      (N : ℝ) * D := by
    calc
      _ ≤ ∑ i : Fin m, |if key (d i).1 = c then P.e (d i).1.val - P.e x.val else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin m, (if key (d i).1 = c then (1 : ℝ) else 0) * D := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : key (d i).1 = c
        · have hc := (pilotCovariateKey_eq_iff mx hmx (d i).1 x).mp hi
          have hb := (hModel.propensity_holder (d i).1.val (d i).1.property x.val x.property).trans
            (mul_le_mul_of_nonneg_left
              (same_cell_holder_scale_le mx hmx _ _ (d i).1.property x.property hc) (by norm_num))
          simpa only [hi, if_pos, one_mul] using hb
        · simp [hi]
      _ = (N : ℝ) * D := by
        rw [← Finset.sum_mul]
        congr 1
        rw [Causalean.Stat.Concentration.ConditionalBernstein.cellCount_cast]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : key (d i).1 = c <;>
          simp [Causalean.Stat.Concentration.ConditionalBernstein.cellIndicator, hi]
  have hid : M - (N : ℝ) * P.e x.val =
      ∑ i : Fin m, if key (d i).1 = c then P.e (d i).1.val - P.e x.val else 0 := by
    dsimp [M]
    rw [Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean,
      Causalean.Stat.Concentration.ConditionalBernstein.cellCount_cast,
      Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [pilot_treatment_binProbability_eq]
    by_cases hi : key (d i).1 = c <;>
      simp [Causalean.Stat.Concentration.ConditionalBernstein.cellIndicator, hi]
  change |M / (N : ℝ) - P.e x.val| ≤ D
  rw [show M / (N : ℝ) - P.e x.val = (M - (N : ℝ) * P.e x.val) / N by field_simp,
    abs_div, abs_of_pos hN, hid]
  exact (div_le_iff₀ hN).2 (by simpa only [mul_comm] using hsum)

/-- Dropping the arm restriction only increases a covariate count. -/
-- @node: pilot_armCellCount_le_cellCount
lemma pilot_armCellCount_le_cellCount {m : ℕ} (train : Fin m → Omega)
    (mx : ℕ) (a : Bool) (x : ℝ) : armCellCount train mx a x ≤ cellCount train mx x := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [armCellCount, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simpa only [cellCount, Finset.mem_filter, Finset.mem_univ, true_and] using hi.1

/-- The outcome Bernstein allowance also bounds the treatment radius, with
ample slack at every positive outcome resolution. -/
-- @node: pilot_propensity_radius_le_hAllow
lemma pilot_propensity_radius_le_hAllow (m mx my N : ℕ)
    (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my)
    (hcount : (m : ℝ) / (8 * mx) ≤ N) :
    10 * (mx : ℝ) ^ (-1 / 10 : ℝ) +
      Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
        (N : ℝ) (30 * Real.log m) / N ≤ hAllow (2 ^ 16) m mx my := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmxpos : (0 : ℝ) < mx := by exact_mod_cast hmx
  have hmypos : (0 : ℝ) < my := by exact_mod_cast hmy
  have hmy1 : (1 : ℝ) ≤ my := by exact_mod_cast hmy
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hcount
  have hu : 0 ≤ 30 * Real.log m := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    positivity
  have hr : Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
      (N : ℝ) (30 * Real.log m) / N ≤
      (my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
        ((4 / my) * N) (30 * Real.log m) / N := by
    rw [pilot_density_bernsteinRadius_eq my N _ hmypos hNpos hu]
    unfold Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
    rw [add_div]
    apply add_le_add
    · have he : Real.sqrt (2 * (N : ℝ) * (30 * Real.log m)) / N =
          Real.sqrt (2 * (30 * Real.log m) / N) := by
        have hid : 2 * (30 * Real.log m) / N =
            (1 / (N : ℝ)) ^ 2 * (2 * (N : ℝ) * (30 * Real.log m)) := by
          field_simp
        rw [hid, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ 1 / (N : ℝ))]
        ring
      rw [he]
      apply Real.sqrt_le_sqrt
      apply (div_le_div_iff_of_pos_right hNpos).mpr
      nlinarith
    · exact (div_le_div_iff_of_pos_right hNpos).mpr (by nlinarith)
  have hb := pilot_density_bernstein_threshold_le_hAllow m mx my N hm hmx hmy hcount
  have hD : 0 ≤ 10 * (mx : ℝ) ^ (-1 / 10 : ℝ) := by positivity
  have hy : 0 ≤ 10 * (my : ℝ)⁻¹ := by positivity
  have hR : 0 ≤ (my : ℝ) *
      Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
        ((4 / my) * N) (30 * Real.log m) / N := by
    have := Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius_nonneg
      ((4 / my) * N) hu
    positivity
  linarith

/-- A good simultaneous treatment Bernstein event controls both clipped arm
propensities at every point, provided the arm-count event holds. -/
-- @node: pilot_propensity_public_error_of_not_badEvent
lemma pilot_propensity_public_error_of_not_badEvent (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my)
    (d : Fin m → PilotDesign) (v : Fin m → ℝ)
    (hcounts : ∀ a x, x ∈ Set.Icc 0 1 →
      (m : ℝ) / (8 * mx) ≤ armCellCount (pilotTrainingRecords d v) mx a x)
    (hgood : ((fun i => (d i).1), (fun i => (d i).2)) ∉
      Causalean.Stat.Concentration.ConditionalBernstein.histogramBadEvent
        (pilotCovariateKey mx hmx) (causalTreatmentKernel P)
        (fun _ : Fin 1 => ({true} : Set Bool)) 1 (30 * Real.log m)) :
    ∀ a x, x ∈ Set.Icc 0 1 →
      |pilotPi (pilotTrainingRecords d v) mx a x - pi P a x| ≤ hAllow (2 ^ 16) m mx my := by
  intro a x hx
  let e : Set.Icc (0 : ℝ) 1 := ⟨x, hx⟩
  let N := cellCount (pilotTrainingRecords d v) mx x
  have hfloor : (m : ℝ) / (8 * mx) ≤ N :=
    (hcounts true x hx).trans (by exact_mod_cast (pilot_armCellCount_le_cellCount
      (pilotTrainingRecords d v) mx true x))
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmxpos : (0 : ℝ) < mx := by exact_mod_cast hmx
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hfloor
  have hN : 0 < N := by exact_mod_cast hNpos
  have hc := pilot_propensity_cellCount_eq mx hmx d v e
  have hj := pilot_propensity_jointCount_eq mx hmx d v e
  have hcount : 0 < Causalean.Stat.Concentration.ConditionalBernstein.cellCount
      (pilotCovariateKey mx hmx) (pilotCovariateKey mx hmx e) (fun i => (d i).1) := by
    rwa [hc]
  have hdev :=
    Causalean.Stat.Concentration.ConditionalBernstein.simultaneous_deviation_of_not_mem_badEvent
      (p := ((fun i => (d i).1), (fun i => (d i).2))) hgood
        (pilotCovariateKey mx hmx e) (0 : Fin 1)
  have hn := Causalean.Stat.Concentration.ConditionalBernstein.normalized_deviation_le
    (pilotCovariateKey mx hmx) (causalTreatmentKernel P) {true} (pilotCovariateKey mx hmx e)
    (fun i => (d i).1) (fun i => (d i).2) 1 (30 * Real.log m) hcount hdev
  have hb := pilot_propensity_conditional_bias_le P hModel mx hmx d e hcount
  rw [hc, hj] at hn
  rw [hc] at hb
  have hraw : |(if N = 0 then (1 / 2 : ℝ) else
      (armCellCount (pilotTrainingRecords d v) mx true x : ℝ) / N) - P.e x| ≤
      10 * (mx : ℝ) ^ (-1 / 10 : ℝ) +
      Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
        (N : ℝ) (30 * Real.log m) / N := by
    rw [if_neg (Nat.ne_of_gt hN)]
    exact (abs_sub_le _ _ _).trans (by simpa only [one_mul, add_comm] using add_le_add hn hb)
  exact (pilotPi_error_le_of_raw P hModel (pilotTrainingRecords d v) mx a x _ hx hraw).trans
    (pilot_propensity_radius_le_hAllow m mx my N hm hmx hmy hfloor)

/-- Integrating out all outcome coordinates preserves the retained IID design law. -/
-- @node: pilot_iid_jointLaw_map_design
lemma pilot_iid_jointLaw_map_design (P : ObsLaw) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => pilotDesignLaw P ⊗ₘ pilotOutcomeKernel P)).map
      (fun z i => (z i).1) = Measure.pi (fun _ : Fin m => pilotDesignLaw P) := by
  rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
  have hf : (pilotDesignLaw P ⊗ₘ pilotOutcomeKernel P).map Prod.fst = pilotDesignLaw P := by
    change (pilotDesignLaw P ⊗ₘ pilotOutcomeKernel P).fst = _
    rw [Measure.fst_compProd]
  simp only [hf]

/-- The propensity deviation on the count-good event is bounded under the
actual observed IID law; outcomes are integrated out, with no independence
assumption between the count event and the deviation. -/
-- @node: pilot_propensity_actual_iid_tail_le
lemma pilot_propensity_actual_iid_tail_le (P : ObsLaw) (hModel : Model P)
    (m mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my) :
    (dataLaw P m).real {train |
      (∀ a x, x ∈ Set.Icc 0 1 → (m : ℝ) / (8 * mx) ≤ armCellCount train mx a x) ∧
      ∃ a x, x ∈ Set.Icc 0 1 ∧ hAllow (2 ^ 16) m mx my <
        |pilotPi train mx a x - pi P a x|} ≤
      2 * (mx : ℝ) * Real.exp (-(30 * Real.log m)) := by
  let bad : Set (Fin m → PilotDesign) := {d |
    ((fun i => (d i).1), (fun i => (d i).2)) ∈
      Causalean.Stat.Concentration.ConditionalBernstein.histogramBadEvent
        (pilotCovariateKey mx hmx) (causalTreatmentKernel P)
        (fun _ : Fin 1 => ({true} : Set Bool)) 1 (30 * Real.log m)}
  have hb : MeasurableSet bad :=
    (Causalean.Stat.Concentration.ConditionalBernstein.measurableSet_histogramBadEvent
      (pilotCovariateKey mx hmx) (causalTreatmentKernel P)
      (fun _ : Fin 1 => ({true} : Set Bool))
      (measurableSet_pilotCovariateKey mx hmx) (fun _ => measurableSet_singleton true)
      1 (30 * Real.log m)).preimage (by fun_prop)
  rw [← pilot_iid_jointLaw_map_record P m, measureReal_def,
    (measurableEmbedding_pilot_record_vector m).map_apply]
  apply le_trans (b := (Measure.pi (fun _ : Fin m =>
    pilotDesignLaw P ⊗ₘ pilotOutcomeKernel P)).real
      ((fun z i => (z i).1) ⁻¹' bad))
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    rintro z ⟨hc, a, x, hx, he⟩
    by_contra hg
    have hp := pilot_propensity_public_error_of_not_badEvent P hModel mx my hm hmx hmy
      (fun i => (z i).1) (fun i => (z i).2) hc hg a x hx
    exact (not_lt_of_ge hp) he
  · rw [measureReal_def, ← Measure.map_apply (by fun_prop) hb,
      pilot_iid_jointLaw_map_design P m, ← measureReal_def]
    apply pilot_treatment_iid_bernstein_tail_le P m mx hmx
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    positivity

/-- The same propensity budget holds for the actual training fold, including
integration over the other twelve roles and independent randomization. -/
-- @node: pilot_propensity_sampling_tail_le
lemma pilot_propensity_sampling_tail_le (P : ObsLaw) (hModel : Model P)
    (m mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my)
    (ν : Measure (SampleSpace (13 * m))) (hSampling : SamplingLaw P (13 * m) ν) :
    ν.real {ω |
      (∀ a x, x ∈ Set.Icc 0 1 → (m : ℝ) / (8 * mx) ≤
        armCellCount (foldData (13 * m) ω.1 0) mx a x) ∧
      ∃ a x, x ∈ Set.Icc 0 1 ∧ hAllow (2 ^ 16) m mx my <
        |pilotPi (foldData (13 * m) ω.1 0) mx a x - pi P a x|} ≤
      2 * (mx : ℝ) * (m : ℝ) ^ (-30 : ℤ) := by
  let E : Set (Data (roleSize (13 * m))) := {train |
    (∀ a x, x ∈ Set.Icc 0 1 → (m : ℝ) / (8 * mx) ≤ armCellCount train mx a x) ∧
    ∃ a x, x ∈ Set.Icc 0 1 ∧ hAllow (2 ^ 16) m mx my < |pilotPi train mx a x - pi P a x|}
  apply (samplingLaw_foldData_real_le P (13 * m) ν hSampling 0 E).trans
  have hr : roleSize (13 * m) = m := by simp [roleSize]
  dsimp only [E]
  generalize roleSize (13 * m) = r at *
  subst r
  rw [← pilot_exp_log_tail_eq_zpow m (by omega)]
  exact pilot_propensity_actual_iid_tail_le P hModel m mx my hm hmx hmy

end CausalSmith.Stat.DensityEffectRoughNull
