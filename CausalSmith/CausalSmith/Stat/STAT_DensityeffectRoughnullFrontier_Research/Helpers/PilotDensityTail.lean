module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.PilotDeterministic
/-!
Public-scale Bernstein bounds for normalized density pilots. The conditional and
IID retained-design tails use the roadmap's arm-cell count floor and the frozen
pilot constant, absorbing the library's full linear Bernstein term. Sampling-law
block extraction is recorded for the remaining actual-law assembly.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

-- @node: pilot_density_bernsteinRadius_eq
lemma pilot_density_bernsteinRadius_eq (b N u : ℝ) (hb : 0 < b) (hN : 0 < N)
    (_hu : 0 ≤ u) :
    b * Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
      ((4 / b) * N) u / N = Real.sqrt (8 * b * u / N) + b * u / N := by
  unfold Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
  have hs : b * Real.sqrt (2 * (4 / b * N) * u) / N =
      Real.sqrt (8 * b * u / N) := by
    have hid : 8 * b * u / N = (b / N) ^ 2 * (2 * (4 / b * N) * u) := by
      field_simp
      ring
    rw [hid, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ b / N)]
    ring
  rw [mul_add, add_div, hs]

-- @node: pilot_density_bernsteinRadius_le
lemma pilot_density_bernsteinRadius_le (m mx my N u : ℝ)
    (hm : 0 < m) (hmx : 0 < mx) (hmy : 0 < my) (hN : 0 < N) (hu : 0 ≤ u)
    (hcount : m / (8 * mx) ≤ N) :
    my * Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
      ((4 / my) * N) u / N ≤
      Real.sqrt (64 * mx * my * u / m) + 8 * mx * my * u / m := by
  rw [pilot_density_bernsteinRadius_eq my N u hmy hN hu]
  have hc : m ≤ N * (8 * mx) := (div_le_iff₀ (by positivity)).mp hcount
  have hr : my * u / N ≤ 8 * mx * my * u / m := by
    apply (le_div_iff₀ hm).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hN).mpr
    nlinarith [mul_le_mul_of_nonneg_right hc (mul_nonneg hmy.le hu)]
  apply add_le_add _ hr
  apply Real.sqrt_le_sqrt
  convert mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 8) using 1 <;> first | rfl | ring

/-- The library radius uses a full linear tail term. The fixed public pilot constant
also absorbs that term after normalization. -/
-- @node: normalized_pilot_bernstein_threshold_le
lemma normalized_pilot_bernstein_threshold_le (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) :
    40 * (10 * x + 10 * y + Real.sqrt (1920 * z) + 240 * z) ≤
      (2 : ℝ) ^ 16 * (x + y + Real.sqrt z + z) := by
  have hs : Real.sqrt (1920 * z) ≤ 44 * Real.sqrt z := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hz]
  have hs0 := Real.sqrt_nonneg z
  rw [show (2 : ℝ) ^ 16 = 65536 by norm_num]
  linarith

/-- A lower arm-cell count turns the conditional Bernstein radius into the public
resolution-scale error, uniformly over retained covariate and arm assignments. -/
-- @node: pilot_density_bernstein_threshold_le_hAllow
lemma pilot_density_bernstein_threshold_le_hAllow (m mx my N : ℕ)
    (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my)
    (hcount : (m : ℝ) / (8 * mx) ≤ N) :
    40 * (10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
      (my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
        ((4 / my) * N) (30 * Real.log m) / N) ≤ hAllow (2 ^ 16) m mx my := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmxpos : (0 : ℝ) < mx := by exact_mod_cast hmx
  have hmypos : (0 : ℝ) < my := by exact_mod_cast hmy
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hcount
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hlog := Real.log_nonneg hm1
  have hr := pilot_density_bernsteinRadius_le m mx my N (30 * Real.log m)
    hmpos hmxpos hmypos hNpos (by positivity) hcount
  have hid : 64 * (mx : ℝ) * my * (30 * Real.log m) / m =
      1920 * ((mx : ℝ) * my * Real.log m / m) := by ring
  have hil : 8 * (mx : ℝ) * my * (30 * Real.log m) / m =
      240 * ((mx : ℝ) * my * Real.log m / m) := by ring
  rw [hid, hil] at hr
  calc
    _ ≤ 40 * (10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
        Real.sqrt (1920 * ((mx : ℝ) * my * Real.log m / m)) +
        240 * ((mx : ℝ) * my * Real.log m / m)) := by linarith
    _ ≤ hAllow (2 ^ 16) m mx my := by
      rw [hAllow, if_neg (by omega)]
      exact normalized_pilot_bernstein_threshold_le _ _ _
        (by positivity) (by positivity) (by positivity)


/-- With the roadmap's arm-cell count floor, the normalized conditional density
pilot exceeds its public allowance on at most the simultaneous outcome-bin tail.
This is uniform in the complete retained design; no independence from the count
event is used. -/
-- @node: pilot_density_public_fibre_tail_le
lemma pilot_density_public_fibre_tail_le (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my)
    (d : Fin m → PilotDesign)
    (hcounts : ∀ e : PilotDesign, (m : ℝ) / (8 * mx) ≤
      Causalean.Stat.Concentration.ConditionalBernstein.cellCount
        (pilotDesignKey mx hmx) (pilotDesignKey mx hmx e) d) :
    (Causalean.Stat.finProductKernel m (pilotOutcomeKernel P) d).real
      {v | ∃ a x y, x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧
        hAllow (2 ^ 16) m mx my <
          |densityPilot (pilotTrainingRecords d v) mx my a x y - P.eta a x y|} ≤
      4 * (mx : ℝ) * my * Real.exp (-(30 * Real.log m)) := by
  let u := 30 * Real.log m
  have hu : 0 ≤ u := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    exact mul_nonneg (by norm_num) (Real.log_nonneg hm1)
  let bad : Set (Fin m → ℝ) := {v | ∃ e : PilotDesign, ∃ y : ℝ,
    y ∈ Set.Icc 0 1 ∧
    0 < armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val ∧
    10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
      (my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
        ((4 / my) * (armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val : ℝ)) u /
        armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val <
      |(my : ℝ) * outcomeCellCount (pilotTrainingRecords d v) mx my e.2 e.1.val y /
        armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val - P.eta e.2 e.1.val y|}
  apply le_trans (b := (Causalean.Stat.finProductKernel m (pilotOutcomeKernel P) d).real bad)
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    rintro v ⟨a, x, y, hx, hy, hfail⟩
    by_contra hgood
    let e : PilotDesign := (⟨x, hx⟩, a)
    let N := armCellCount (pilotTrainingRecords d v) mx a x
    have hfloor : (m : ℝ) / (8 * mx) ≤ N := by
      simpa only [pilot_bernstein_cellCount_eq mx hmx d v e] using hcounts e
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmxpos : (0 : ℝ) < mx := by exact_mod_cast hmx
    have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hfloor
    have hN : 0 < N := by exact_mod_cast hNpos
    let D := 10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
      (my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
        ((4 / my) * N) u / N
    have hD : 0 ≤ D := by
      have hr := Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius_nonneg
        ((4 / my) * N) hu
      dsimp [D]
      positivity
    have hraw : ∀ yp ∈ Set.Icc 0 1,
        |(if N = 0 then (1 : ℝ) else
          (my : ℝ) * outcomeCellCount (pilotTrainingRecords d v) mx my a x yp / N) -
          P.eta a x yp| ≤ D := by
      intro yp hyp
      rw [if_neg (Nat.ne_of_gt hN)]
      apply le_of_not_gt
      intro hbad
      exact hgood ⟨e, yp, hyp, hN, hbad⟩
    have herror := densityPilot_error_le_of_raw P hModel (pilotTrainingRecords d v)
      mx my a x y D hx hy hD hraw
    have hallow : 40 * D ≤ hAllow (2 ^ 16) m mx my :=
      pilot_density_bernstein_threshold_le_hAllow m mx my N hm hmx hmy hfloor
    exact (not_lt_of_ge (herror.trans hallow)) hfail
  · exact pilot_raw_density_fibre_tail_le P hModel mx my hmx hmy d u hu


/-- A simultaneous good Bernstein event and the arm-cell count floor imply the
public normalized density error bound at every covariate and outcome point. -/
-- @node: pilot_density_public_error_of_not_badEvent
lemma pilot_density_public_error_of_not_badEvent (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my)
    (d : Fin m → PilotDesign) (v : Fin m → ℝ) (hs : ∀ i, v i ∈ Set.Icc 0 1)
    (hcounts : ∀ e : PilotDesign, (m : ℝ) / (8 * mx) ≤
      Causalean.Stat.Concentration.ConditionalBernstein.cellCount
        (pilotDesignKey mx hmx) (pilotDesignKey mx hmx e) d)
    (hgood : (d, v) ∉
      Causalean.Stat.Concentration.ConditionalBernstein.histogramBadEvent
        (pilotDesignKey mx hmx) (pilotOutcomeKernel P)
        (fun j : Fin my => histogramCell my (j.val + 1)) (4 / my) (30 * Real.log m)) :
    ∀ a x y, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
      |densityPilot (pilotTrainingRecords d v) mx my a x y - P.eta a x y| ≤
        hAllow (2 ^ 16) m mx my := by
  intro a x y hx hy
  let e : PilotDesign := (⟨x, hx⟩, a)
  let N := armCellCount (pilotTrainingRecords d v) mx a x
  have hfloor : (m : ℝ) / (8 * mx) ≤ N := by
    simpa only [pilot_bernstein_cellCount_eq mx hmx d v e] using hcounts e
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmxpos : (0 : ℝ) < mx := by exact_mod_cast hmx
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hfloor
  have hN : 0 < N := by exact_mod_cast hNpos
  let D := 10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
    (my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
      ((4 / my) * N) (30 * Real.log m) / N
  have hu : 0 ≤ 30 * Real.log m := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    exact mul_nonneg (by norm_num) (Real.log_nonneg hm1)
  have hD : 0 ≤ D := by
    have hr := Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius_nonneg
      ((4 / my) * N) hu
    dsimp [D]
    positivity
  have hdev :=
    Causalean.Stat.Concentration.ConditionalBernstein.simultaneous_deviation_of_not_mem_badEvent
      (p := (d, v)) hgood
  have hraw : ∀ yp ∈ Set.Icc 0 1,
      |(if N = 0 then (1 : ℝ) else
        (my : ℝ) * outcomeCellCount (pilotTrainingRecords d v) mx my a x yp / N) -
        P.eta a x yp| ≤ D := by
    intro yp hyp
    rw [if_neg (Nat.ne_of_gt hN)]
    have hi := cell_index_mem my hmy yp
    let j : Fin my := ⟨cell my yp - 1, by omega⟩
    have hj : j.val + 1 = cell my yp := by dsimp [j]; omega
    have hd := hdev (pilotDesignKey mx hmx e) j
    rw [pilot_bernstein_cellCount_eq mx hmx d v e] at hd
    exact pilot_raw_density_error_of_bernstein P hModel mx my hmx hmy d v e j yp
      ⟨hyp, hj.symm⟩ hs _ hN hd
  exact (densityPilot_error_le_of_raw P hModel (pilotTrainingRecords d v)
    mx my a x y D hx hy hD hraw).trans
      (pilot_density_bernstein_threshold_le_hAllow m mx my N hm hmx hmy hfloor)

/-- Integrating arbitrary retained designs preserves the outcome-bin failure
budget on the count-good event. The count event need not be independent of the
histogram deviations. -/
-- @node: pilot_density_public_iid_tail_le
lemma pilot_density_public_iid_tail_le (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (Q : Measure PilotDesign) [IsProbabilityMeasure Q]
    (mx my : ℕ) (hm : 3 ≤ m) (hmx : 0 < mx) (hmy : 0 < my) :
    (Measure.pi (fun _ : Fin m => Q ⊗ₘ pilotOutcomeKernel P)).real
      {z | (∀ e : PilotDesign, (m : ℝ) / (8 * mx) ≤
        Causalean.Stat.Concentration.ConditionalBernstein.cellCount
          (pilotDesignKey mx hmx) (pilotDesignKey mx hmx e) (fun i => (z i).1)) ∧
        ∃ a x y, x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧
          hAllow (2 ^ 16) m mx my <
            |densityPilot (pilotTrainingRecords (fun i => (z i).1) (fun i => (z i).2))
              mx my a x y - P.eta a x y|} ≤
      4 * (mx : ℝ) * my * Real.exp (-(30 * Real.log m)) := by
  have hu : 0 ≤ 30 * Real.log m := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    exact mul_nonneg (by norm_num) (Real.log_nonneg hm1)
  have hp : ∀ᵐ z ∂Q ⊗ₘ pilotOutcomeKernel P, z.2 ∈ Set.Icc 0 1 := by
    rw [Measure.ae_compProd_iff (measurableSet_Icc.preimage measurable_snd)]
    exact Filter.Eventually.of_forall fun d => by
      rw [pilotOutcomeKernel_apply]
      exact conditionalOutcomeKernel_ae_mem P d.2 d.1
  have hs : ∀ᵐ z ∂Measure.pi (fun _ : Fin m => Q ⊗ₘ pilotOutcomeKernel P),
      ∀ i, (z i).2 ∈ Set.Icc 0 1 := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => Q ⊗ₘ pilotOutcomeKernel P)
      (i := i)).eventually hp
  apply le_trans (b := (Measure.pi (fun _ : Fin m => Q ⊗ₘ pilotOutcomeKernel P)).real
    {z | ∃ c : Fin mx × Bool, ∃ j : Fin my,
      Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
        ((4 / my) * (Causalean.Stat.Concentration.ConditionalBernstein.cellCount
          (pilotDesignKey mx hmx) c (fun i => (z i).1) : ℝ)) (30 * Real.log m) <
        |(Causalean.Stat.Concentration.ConditionalBernstein.jointCount
          (pilotDesignKey mx hmx) (histogramCell my (j.val + 1)) c
          (fun i => (z i).1) (fun i => (z i).2) : ℝ) -
          Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean
            (pilotDesignKey mx hmx) (pilotOutcomeKernel P) (histogramCell my (j.val + 1)) c
            (fun i => (z i).1)|})
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hs] with z hz
    rintro ⟨hcounts, a, x, y, hx, hy, hfail⟩
    by_contra hgood
    have he := pilot_density_public_error_of_not_badEvent P hModel mx my hm hmx hmy
      (fun i => (z i).1) (fun i => (z i).2) hz hcounts hgood a x y hx hy
    exact (not_lt_of_ge he) hfail
  · exact pilot_outcome_iid_tail_le P hModel Q mx my hmx hmy _ hu


/-- Extracting any of the thirteen blocks from the randomized sampling law gives
exactly its IID observation law; the public randomization is integrated out. -/
-- @node: sampleLaw_foldData_map
lemma sampleLaw_foldData_map (P : ObsLaw) (n : ℕ) (b : Fin 13) :
    (sampleLaw P n).map (fun ω => foldData n ω.1 b) =
      Measure.pi (fun _ : Fin (roleSize n) => P.law) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hinj : Function.Injective (foldIndex n b) := by
    intro i j hij
    have hpair : (b, i) = (b, j) := foldIndex_injective n hij
    exact congrArg Prod.snd hpair
  have hsel := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin n => P.law) hinj
  simp only [Measure.infinitePi_eq_pi] at hsel
  change ((dataLaw P n).prod unitVolume).map
    ((fun data => foldData n data b) ∘ Prod.fst) = _
  rw [← Measure.map_map (by unfold foldData; fun_prop : Measurable (fun data => foldData n data b))
    measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  exact hsel


/-- The full linear Bernstein propensity threshold is bounded by the outcome
threshold at any positive outcome rank. -/
-- @node: pilot_propensity_bernstein_threshold_le_density
lemma pilot_propensity_bernstein_threshold_le_density (m mx my : ℕ) (hm : 3 ≤ m)
    (hmy : 1 ≤ my) :
    10 * (mx : ℝ) ^ (-1 / 10 : ℝ) +
      Real.sqrt (240 * ((mx : ℝ) * Real.log m / m)) +
      120 * ((mx : ℝ) * Real.log m / m) ≤
    10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
      Real.sqrt (1920 * ((mx : ℝ) * my * Real.log m / m)) +
      240 * ((mx : ℝ) * my * Real.log m / m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hlog := Real.log_nonneg hm1
  have hmy1 : (1 : ℝ) ≤ my := by exact_mod_cast hmy
  have hz : 0 ≤ (mx : ℝ) * Real.log m / m := by positivity
  have hzz : (mx : ℝ) * Real.log m / m ≤ (mx : ℝ) * my * Real.log m / m := by
    calc
      _ ≤ ((mx : ℝ) * Real.log m / m) * my := le_mul_of_one_le_right hz hmy1
      _ = _ := by ring
  have hs : Real.sqrt (240 * ((mx : ℝ) * Real.log m / m)) ≤
      Real.sqrt (1920 * ((mx : ℝ) * my * Real.log m / m)) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hy : 0 ≤ (my : ℝ)⁻¹ := by positivity
  linarith

/-- Raw histogram bounds with the library Bernstein linear terms still imply
exactly the frozen good-pilot event, with no change to its public constant. -/
-- @node: goodPilot_of_raw_bernstein_histogram_bounds
lemma goodPilot_of_raw_bernstein_histogram_bounds {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (hm : 3 ≤ m) (hmy : 1 ≤ my)
    (hpi : ∀ x ∈ Set.Icc 0 1,
      |(if cellCount train mx x = 0 then (1 / 2 : ℝ) else
        (armCellCount train mx true x : ℝ) / cellCount train mx x) - P.e x| ≤
      10 * (mx : ℝ) ^ (-1 / 10 : ℝ) +
        Real.sqrt (240 * ((mx : ℝ) * Real.log m / m)) +
        120 * ((mx : ℝ) * Real.log m / m))
    (heta : ∀ a x y, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
      |(if armCellCount train mx a x = 0 then (1 : ℝ) else
        (my : ℝ) * outcomeCellCount train mx my a x y / armCellCount train mx a x) -
        P.eta a x y| ≤
      10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
        Real.sqrt (1920 * ((mx : ℝ) * my * Real.log m / m)) +
        240 * ((mx : ℝ) * my * Real.log m / m)) :
    GoodPilot P train (2 ^ 16) mx my := by
  let D := 10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
    Real.sqrt (1920 * ((mx : ℝ) * my * Real.log m / m)) +
    240 * ((mx : ℝ) * my * Real.log m / m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hlog := Real.log_nonneg hm1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hallow : 40 * D ≤ hAllow (2 ^ 16) m mx my := by
    rw [hAllow, if_neg (by omega)]
    exact normalized_pilot_bernstein_threshold_le _ _ _
      (by positivity) (by positivity) (by positivity)
  apply pilotError_le_of_pointwise
  · intro a x hx
    have hraw := (hpi x hx).trans
      (pilot_propensity_bernstein_threshold_le_density m mx my hm hmy)
    exact (pilotPi_error_le_of_raw P hModel train mx a x D hx hraw).trans
      ((by linarith : D ≤ 40 * D).trans hallow)
  · intro a x y hx hy
    exact (densityPilot_error_le_of_raw P hModel train mx my a x y D hx hy hD
      (fun yp hyp => heta a x yp hx hyp)).trans hallow

end CausalSmith.Stat.DensityEffectRoughNull
