module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CausalKernels
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CorrectedMean
public import Causalean.Stat.Concentration.ConditionalBernstein.Integrated

/-!
Variance-sensitive conditional Bernstein adapters for the paper's outcome histograms.
The design retains both the unit covariate and treatment assignment. All outcome-bin
probabilities are bounded by four divided by the outcome resolution; no count lower
bound is used for the tail event, so empty cells remain included.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Supported covariate and retained treatment assignment for conditional histogram tails. -/
-- @node: PilotDesign
abbrev PilotDesign := Set.Icc (0 : ℝ) 1 × Bool

/-- The actual conditional outcome density, selected by the retained treatment. -/
-- @node: pilotOutcomeKernel
def pilotOutcomeKernel (P : ObsLaw) : Kernel PilotDesign ℝ :=
  Kernel.piecewise (s := {d : PilotDesign | d.2 = true})
    (measurableSet_eq_fun measurable_snd measurable_const)
    ((conditionalOutcomeKernel P true).comap Prod.fst measurable_fst)
    ((conditionalOutcomeKernel P false).comap Prod.fst measurable_fst)

/-- Selection by treatment preserves the Markov property. -/
-- @node: pilotOutcomeKernel_isMarkov
instance pilotOutcomeKernel_isMarkov (P : ObsLaw) : IsMarkovKernel (pilotOutcomeKernel P) := by
  unfold pilotOutcomeKernel
  infer_instance

/-- Evaluating the retained-design kernel recovers the corresponding arm density law. -/
-- @node: pilotOutcomeKernel_apply
lemma pilotOutcomeKernel_apply (P : ObsLaw) (d : PilotDesign) :
    pilotOutcomeKernel P d = conditionalOutcomeKernel P d.2 d.1 := by
  rcases d with ⟨x, a⟩
  cases a <;> simp [pilotOutcomeKernel, Kernel.piecewise_apply, Kernel.comap_apply]

/-- Outcome-kernel event probabilities are the specified integrals of the density version. -/
-- @node: conditionalOutcomeKernel_real_eq
lemma conditionalOutcomeKernel_real_eq (P : ObsLaw) (a : Bool)
    (x : Set.Icc (0 : ℝ) 1) (D : Set ℝ) (hD : MeasurableSet D) :
    (conditionalOutcomeKernel P a x).real D = ∫ y in D, P.eta a x.val y ∂unitVolume := by
  have hn : 0 ≤ᵐ[unitVolume.restrict D] P.eta a x.val := by
    filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with y hy
    exact P.eta_nonneg a x.val y x.property hy
  rw [conditionalOutcomeKernel_apply, measureReal_def, withDensity_apply _ hD,
    ← ofReal_integral_eq_lintegral_ofReal (P.eta_integrable a x.val x.property).integrableOn hn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)]

/-- The model envelope supplies the Bernoulli variance scale four divided by the bin rank. -/
-- @node: pilotOutcomeKernel_binProbability_le
lemma pilotOutcomeKernel_binProbability_le (P : ObsLaw) (hModel : Model P)
    (my : ℕ) (hmy : 0 < my) (d : PilotDesign) (j : Fin my) :
    Causalean.Stat.Concentration.ConditionalBernstein.binProbability
      (pilotOutcomeKernel P) (histogramCell my (j.val + 1)) d ≤ 4 / (my : ℝ) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  rw [Causalean.Stat.Concentration.ConditionalBernstein.binProbability,
    pilotOutcomeKernel_apply, conditionalOutcomeKernel_real_eq P d.2 d.1 _
      (measurableSet_histogramCell _ _)]
  calc
    _ ≤ ∫ _y in histogramCell my (j.val + 1), (4 : ℝ) ∂unitVolume := by
      apply integral_mono_ae (P.eta_integrable d.2 d.1.val d.1.property).integrableOn
        (integrable_const 4)
      filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with y hy
      exact (hModel.density_envelope d.2 d.1.val y d.1.property hy).2
    _ = 4 * unitVolume.real (histogramCell my (j.val + 1)) := by
      rw [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
      change unitVolume.real _ * 4 = 4 * unitVolume.real _
      ring
    _ ≤ 4 * (1 / (my : ℝ)) :=
      mul_le_mul_of_nonneg_left (histogramCell_mass_le my hmy j) (by norm_num)
    _ = _ := by ring

/-- Zero-based finite cell label paired with the retained arm. -/
-- @node: pilotDesignKey
def pilotDesignKey (mx : ℕ) (hmx : 0 < mx) (d : PilotDesign) : Fin mx × Bool :=
  (⟨cell mx d.1.val - 1, by have h := cell_index_mem mx hmx d.1.val; omega⟩, d.2)

/-- Equality of finite design keys is exactly equality of covariate cells and arms. -/
-- @node: pilotDesignKey_eq_iff
lemma pilotDesignKey_eq_iff (mx : ℕ) (hmx : 0 < mx) (d e : PilotDesign) :
    pilotDesignKey mx hmx d = pilotDesignKey mx hmx e ↔
      cell mx d.1.val = cell mx e.1.val ∧ d.2 = e.2 := by
  have hd := cell_index_mem mx hmx d.1.val
  have he := cell_index_mem mx hmx e.1.val
  simp only [pilotDesignKey, Prod.mk.injEq, Fin.mk.injEq]
  constructor
  · rintro ⟨h, ha⟩
    exact ⟨by omega, ha⟩
  · rintro ⟨h, ha⟩
    exact ⟨congrArg (fun n : ℕ => n - 1) h, ha⟩

/-- Finite design-key fibres are measurable, as required for integrated Bernstein. -/
-- @node: measurableSet_pilotDesignKey
lemma measurableSet_pilotDesignKey (mx : ℕ) (hmx : 0 < mx) (c : Fin mx × Bool) :
    MeasurableSet {d : PilotDesign | pilotDesignKey mx hmx d = c} := by
  have hm : Measurable (fun d : PilotDesign => cell mx d.1.val - 1) :=
    ((measurable_cell mx).comp (measurable_subtype_coe.comp measurable_fst)).sub measurable_const
  have hs := (measurableSet_eq_fun hm (measurable_const (a := c.1.val))).inter
    (measurableSet_eq_fun measurable_snd (measurable_const (a := c.2)))
  rcases c with ⟨c, a⟩
  simpa only [pilotDesignKey, Prod.mk.injEq, Fin.ext_iff, Set.ofPred_and] using hs

/-- Every assignment fibre obeys the simultaneous variance-sensitive outcome-bin tail;
the bound is valid even when some arm cells have count zero. -/
-- @node: pilot_outcome_fibre_tail_le
lemma pilot_outcome_fibre_tail_le (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (mx my : ℕ) (hmx : 0 < mx) (hmy : 0 < my)
    (d : Fin m → PilotDesign) (u : ℝ) (hu : 0 ≤ u) :
    (Causalean.Stat.finProductKernel m (pilotOutcomeKernel P) d).real
      (Prod.mk d ⁻¹' Causalean.Stat.Concentration.ConditionalBernstein.histogramBadEvent
        (pilotDesignKey mx hmx) (pilotOutcomeKernel P)
        (fun j : Fin my => histogramCell my (j.val + 1)) (4 / my) u) ≤
      4 * (mx : ℝ) * my * Real.exp (-u) := by
  have h := Causalean.Stat.Concentration.ConditionalBernstein.fibre_simultaneous_tail_le
    (pilotDesignKey mx hmx) (pilotOutcomeKernel P)
    (fun j : Fin my => histogramCell my (j.val + 1))
    (fun j => measurableSet_histogramCell _ _) d (by positivity : (0 : ℝ) ≤ 4 / my) hu
    (fun _c j i _hi => pilotOutcomeKernel_binProbability_le P hModel my hmy (d i) j)
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_ofNat, show (2 : ℝ) * (mx * 2) * my = 4 * mx * my by ring] using h

/-- Integrating all retained-design assignments preserves the exact variance-sensitive tail. -/
-- @node: pilot_outcome_iid_tail_le
lemma pilot_outcome_iid_tail_le (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (Q : Measure PilotDesign) [IsProbabilityMeasure Q]
    (mx my : ℕ) (hmx : 0 < mx) (hmy : 0 < my) (u : ℝ) (hu : 0 ≤ u) :
    (Measure.pi (fun _ : Fin m => Q ⊗ₘ pilotOutcomeKernel P)).real
      {z | ∃ c : Fin mx × Bool, ∃ j : Fin my,
        Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
          ((4 / my) * (Causalean.Stat.Concentration.ConditionalBernstein.cellCount
            (pilotDesignKey mx hmx) c (fun i => (z i).1) : ℝ)) u <
        |(Causalean.Stat.Concentration.ConditionalBernstein.jointCount
            (pilotDesignKey mx hmx) (histogramCell my (j.val + 1)) c
            (fun i => (z i).1) (fun i => (z i).2) : ℝ) -
          Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean
            (pilotDesignKey mx hmx) (pilotOutcomeKernel P) (histogramCell my (j.val + 1)) c
            (fun i => (z i).1)|} ≤
      4 * (mx : ℝ) * my * Real.exp (-u) := by
  have h := Causalean.Stat.Concentration.ConditionalBernstein.iid_joint_simultaneous_tail_le
    (n := m) Q (pilotOutcomeKernel P) (pilotDesignKey mx hmx)
    (fun j : Fin my => histogramCell my (j.val + 1))
    (measurableSet_pilotDesignKey mx hmx) (fun j => measurableSet_histogramCell _ _)
    (by positivity : (0 : ℝ) ≤ 4 / my) hu
    (Filter.Eventually.of_forall (fun d _c j _hi =>
      pilotOutcomeKernel_binProbability_le P hModel my hmy d j))
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_ofNat, show (2 : ℝ) * (mx * 2) * my = 4 * mx * my by ring] using h

/-- Within a pilot covariate cell, a conditional bin height approximates every
true density value in the matching outcome bin with the roadmap's two bias terms. -/
-- @node: pilot_conditional_bin_height_error_le
lemma pilot_conditional_bin_height_error_le (P : ObsLaw) (hModel : Model P)
    (mx my : ℕ) (hmx : 0 < mx) (hmy : 0 < my) (d e : PilotDesign)
    (hd : pilotDesignKey mx hmx d = pilotDesignKey mx hmx e)
    (j : Fin my) (y : ℝ) (hy : y ∈ histogramCell my (j.val + 1)) :
    |(my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.binProbability
      (pilotOutcomeKernel P) (histogramCell my (j.val + 1)) d - P.eta e.2 e.1.val y| ≤
      10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ := by
  obtain ⟨hc, ha⟩ := (pilotDesignKey_eq_iff mx hmx d e).1 hd
  rw [Causalean.Stat.Concentration.ConditionalBernstein.binProbability,
    pilotOutcomeKernel_apply, conditionalOutcomeKernel_real_eq P d.2 d.1 _
      (measurableSet_histogramCell _ _), ha]
  have hp := model_outcomeProjection_error_le P hModel my hmy e.2 d.1.val y
    d.1.property hy.1
  have hb : |P.eta e.2 d.1.val y - P.eta e.2 e.1.val y| ≤
      10 * (mx : ℝ) ^ (-1 / 10 : ℝ) :=
    (hModel.density_covariate_holder e.2 y hy.1 d.1.val d.1.property
      e.1.val e.1.property).trans
      (mul_le_mul_of_nonneg_left
        (same_cell_holder_scale_le mx hmx _ _ d.1.property e.1.property hc) (by norm_num))
  have he : (my : ℝ) * (∫ yp in histogramCell my (j.val + 1),
      P.eta e.2 d.1.val yp ∂unitVolume) = outcomeProjection my (P.eta e.2 d.1.val) y := by
    simp only [outcomeProjection, hy.2]
  rw [he]
  calc
    _ ≤ |outcomeProjection my (P.eta e.2 d.1.val) y - P.eta e.2 d.1.val y| +
        |P.eta e.2 d.1.val y - P.eta e.2 e.1.val y| := abs_sub_le _ _ _
    _ ≤ 10 / (my : ℝ) + 10 * (mx : ℝ) ^ (-1 / 10 : ℝ) := add_le_add hp hb
    _ = _ := by ring

/-- Retaining the supported design and outcome coordinates produces the paper's record. -/
-- @node: pilotTrainingRecords
def pilotTrainingRecords {m : ℕ} (d : Fin m → PilotDesign) (y : Fin m → ℝ) : Fin m → Omega :=
  fun i => (d i |>.1.val, (d i).2, y i)

/-- Bernstein's cell count is exactly the paper's arm/covariate training count. -/
-- @node: pilot_bernstein_cellCount_eq
lemma pilot_bernstein_cellCount_eq {m : ℕ} (mx : ℕ) (hmx : 0 < mx)
    (d : Fin m → PilotDesign) (y : Fin m → ℝ) (e : PilotDesign) :
    Causalean.Stat.Concentration.ConditionalBernstein.cellCount
      (pilotDesignKey mx hmx) (pilotDesignKey mx hmx e) d =
      armCellCount (pilotTrainingRecords d y) mx e.2 e.1.val := by
  classical
  simp only [Causalean.Stat.Concentration.ConditionalBernstein.cellCount,
    armCellCount, pilotTrainingRecords, X, A, pilotDesignKey_eq_iff]
  exact (Finset.card_filter _ _).symm

/-- On unit-supported outcomes, the Bernstein joint count is the raw histogram bin count. -/
-- @node: pilot_bernstein_jointCount_eq
lemma pilot_bernstein_jointCount_eq {m : ℕ} (mx my : ℕ) (hmx : 0 < mx)
    (d : Fin m → PilotDesign) (v : Fin m → ℝ) (e : PilotDesign)
    (y : ℝ)
    (hs : ∀ i, v i ∈ Set.Icc 0 1) :
    Causalean.Stat.Concentration.ConditionalBernstein.jointCount
      (pilotDesignKey mx hmx) (histogramCell my (cell my y))
      (pilotDesignKey mx hmx e) d v =
      outcomeCellCount (pilotTrainingRecords d v) mx my e.2 e.1.val y := by
  classical
  rw [outcomeCellCount, Finset.card_filter]
  simp only [Causalean.Stat.Concentration.ConditionalBernstein.jointCount, pilotTrainingRecords, X, A, Y, pilotDesignKey_eq_iff,
    histogramCell, Set.mem_ofPred_eq, hs, true_and]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact propext and_assoc

/-- Averaging the conditional bin means introduces only the two histogram bias terms. -/
-- @node: pilot_conditional_density_bias_le
lemma pilot_conditional_density_bias_le (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (mx my : ℕ) (hmx : 0 < mx) (hmy : 0 < my)
    (d : Fin m → PilotDesign) (e : PilotDesign) (j : Fin my)
    (y : ℝ) (hy : y ∈ histogramCell my (j.val + 1))
    (hcount : 0 < Causalean.Stat.Concentration.ConditionalBernstein.cellCount
      (pilotDesignKey mx hmx) (pilotDesignKey mx hmx e) d) :
    |(my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean
      (pilotDesignKey mx hmx) (pilotOutcomeKernel P) (histogramCell my (j.val + 1))
      (pilotDesignKey mx hmx e) d /
      (Causalean.Stat.Concentration.ConditionalBernstein.cellCount
        (pilotDesignKey mx hmx) (pilotDesignKey mx hmx e) d : ℝ) - P.eta e.2 e.1.val y| ≤
      10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ := by
  classical
  let key := pilotDesignKey mx hmx
  let c := key e
  let N := Causalean.Stat.Concentration.ConditionalBernstein.cellCount key c d
  let p := Causalean.Stat.Concentration.ConditionalBernstein.binProbability
    (pilotOutcomeKernel P) (histogramCell my (j.val + 1))
  let eta := P.eta e.2 e.1.val y
  let D := 10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹
  have hN : (0 : ℝ) < N := by exact_mod_cast hcount
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsum : |∑ i : Fin m, if key (d i) = c then (my : ℝ) * p (d i) - eta else 0| ≤
      (N : ℝ) * D := by
    calc
      _ ≤ ∑ i : Fin m, |if key (d i) = c then (my : ℝ) * p (d i) - eta else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin m, (if key (d i) = c then (1 : ℝ) else 0) * D := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : key (d i) = c
        · simpa only [hi, if_pos, one_mul] using
            pilot_conditional_bin_height_error_le P hModel mx my hmx hmy (d i) e hi j y hy
        · simp [hi]
      _ = (N : ℝ) * D := by
        rw [← Finset.sum_mul]
        congr 1
        rw [Causalean.Stat.Concentration.ConditionalBernstein.cellCount_cast]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : key (d i) = c <;>
          simp [Causalean.Stat.Concentration.ConditionalBernstein.cellIndicator, hi]
  have hid : (my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean
      key (pilotOutcomeKernel P) (histogramCell my (j.val + 1)) c d - (N : ℝ) * eta =
      ∑ i : Fin m, if key (d i) = c then (my : ℝ) * p (d i) - eta else 0 := by
    rw [Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean,
      Causalean.Stat.Concentration.ConditionalBernstein.cellCount_cast,
      Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : key (d i) = c <;>
      simp [Causalean.Stat.Concentration.ConditionalBernstein.cellIndicator, hi, p]
  change |(my : ℝ) * _ / (N : ℝ) - eta| ≤ D
  rw [show (my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean
      key (pilotOutcomeKernel P) (histogramCell my (j.val + 1)) c d / (N : ℝ) - eta =
      ((my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean
      key (pilotOutcomeKernel P) (histogramCell my (j.val + 1)) c d - (N : ℝ) * eta) / N by
        field_simp, abs_div, abs_of_pos hN, hid]
  exact (div_le_iff₀ hN).2 (by simpa only [mul_comm] using hsum)

/-- A positive-count raw histogram satisfies the bias-plus-Bernstein bound before
clipping or normalization, with no loss of the inverse-bin variance factor. -/
-- @node: pilot_raw_density_error_of_bernstein
lemma pilot_raw_density_error_of_bernstein (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (mx my : ℕ) (hmx : 0 < mx) (hmy : 0 < my)
    (d : Fin m → PilotDesign) (v : Fin m → ℝ) (e : PilotDesign)
    (j : Fin my) (y : ℝ) (hy : y ∈ histogramCell my (j.val + 1))
    (hs : ∀ i, v i ∈ Set.Icc 0 1) (u : ℝ)
    (hcount : 0 < armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val)
    (hdev : |(Causalean.Stat.Concentration.ConditionalBernstein.jointCount
        (pilotDesignKey mx hmx) (histogramCell my (j.val + 1))
        (pilotDesignKey mx hmx e) d v : ℝ) -
      Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean
        (pilotDesignKey mx hmx) (pilotOutcomeKernel P) (histogramCell my (j.val + 1))
        (pilotDesignKey mx hmx e) d| ≤
      Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
        ((4 / my) * (armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val : ℝ)) u) :
    |(my : ℝ) * outcomeCellCount (pilotTrainingRecords d v) mx my e.2 e.1.val y /
      armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val - P.eta e.2 e.1.val y| ≤
      10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
      (my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
        ((4 / my) * (armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val : ℝ)) u /
        armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val := by
  have hc := pilot_bernstein_cellCount_eq mx hmx d v e
  have hj := pilot_bernstein_jointCount_eq mx my hmx d v e y hs
  rw [hy.2] at hj
  have hN : 0 < Causalean.Stat.Concentration.ConditionalBernstein.cellCount
      (pilotDesignKey mx hmx) (pilotDesignKey mx hmx e) d := by rwa [hc]
  rw [← hc] at hdev
  have hn := Causalean.Stat.Concentration.ConditionalBernstein.normalized_deviation_le
    (pilotDesignKey mx hmx) (pilotOutcomeKernel P) (histogramCell my (j.val + 1))
    (pilotDesignKey mx hmx e) d v (4 / my) u hN hdev
  have hb := pilot_conditional_density_bias_le P hModel mx my hmx hmy d e j y hy hN
  rw [hc, hj] at hn
  rw [hc] at hb
  let mean := Causalean.Stat.Concentration.ConditionalBernstein.conditionalMean
    (pilotDesignKey mx hmx) (pilotOutcomeKernel P) (histogramCell my (j.val + 1))
    (pilotDesignKey mx hmx e) d
  let N := (armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val : ℝ)
  have hmul : |(my : ℝ) * outcomeCellCount (pilotTrainingRecords d v) mx my e.2 e.1.val y / N -
      (my : ℝ) * mean / N| ≤
      (my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
        ((4 / my) * N) u / N := by
    calc
      _ = (my : ℝ) * |(outcomeCellCount (pilotTrainingRecords d v) mx my e.2 e.1.val y : ℝ) / N -
          mean / N| := by rw [mul_div_assoc, mul_div_assoc, ← mul_sub, abs_mul,
            abs_of_nonneg (Nat.cast_nonneg my)]
      _ ≤ _ := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg my)
  exact (abs_sub_le _ ((my : ℝ) * mean / N) _).trans
    (by simpa only [add_comm] using add_le_add hmul hb)

/-- The product outcome kernel keeps all sampled outcomes on the unit interval. -/
-- @node: pilot_outcome_fibre_support
lemma pilot_outcome_fibre_support (P : ObsLaw) {m : ℕ} (d : Fin m → PilotDesign) :
    ∀ᵐ v ∂Causalean.Stat.finProductKernel m (pilotOutcomeKernel P) d,
      ∀ i, v i ∈ Set.Icc 0 1 := by
  rw [Causalean.Stat.finProductKernel_apply]
  apply ae_all_iff.mpr
  intro i
  apply (Measure.tendsto_eval_ae_ae (μ := fun i => pilotOutcomeKernel P (d i)) (i := i)).eventually
  rw [pilotOutcomeKernel_apply]
  exact conditionalOutcomeKernel_ae_mem P (d i).2 (d i).1

/-- On every complete arm/covariate assignment, failure of the raw density histogram
bound in any positive-count cell has probability at most four times the cell/bin
count times the exponential tail. Empty cells are excluded only from division. -/
-- @node: pilot_raw_density_fibre_tail_le
lemma pilot_raw_density_fibre_tail_le (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (mx my : ℕ) (hmx : 0 < mx) (hmy : 0 < my)
    (d : Fin m → PilotDesign) (u : ℝ) (hu : 0 ≤ u) :
    (Causalean.Stat.finProductKernel m (pilotOutcomeKernel P) d).real
      {v | ∃ e : PilotDesign, ∃ y : ℝ, y ∈ Set.Icc 0 1 ∧
        0 < armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val ∧
        10 * (mx : ℝ) ^ (-1 / 10 : ℝ) + 10 * (my : ℝ)⁻¹ +
          (my : ℝ) * Causalean.Stat.Concentration.ConditionalBernstein.bernsteinRadius
            ((4 / my) * (armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val : ℝ)) u /
            armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val <
        |(my : ℝ) * outcomeCellCount (pilotTrainingRecords d v) mx my e.2 e.1.val y /
          armCellCount (pilotTrainingRecords d v) mx e.2 e.1.val - P.eta e.2 e.1.val y|} ≤
      4 * (mx : ℝ) * my * Real.exp (-u) := by
  let bad := Prod.mk d ⁻¹'
    Causalean.Stat.Concentration.ConditionalBernstein.histogramBadEvent
      (pilotDesignKey mx hmx) (pilotOutcomeKernel P)
      (fun j : Fin my => histogramCell my (j.val + 1)) (4 / my) u
  apply le_trans (b := (Causalean.Stat.finProductKernel m (pilotOutcomeKernel P) d).real bad)
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [pilot_outcome_fibre_support P d] with v hv
    rintro ⟨e, y, hy, hcount, hfail⟩
    by_contra hgood
    have hdev :=
      Causalean.Stat.Concentration.ConditionalBernstein.simultaneous_deviation_of_not_mem_badEvent
      (p := (d, v)) hgood
    have hi := cell_index_mem my hmy y
    let j : Fin my := ⟨cell my y - 1, by omega⟩
    have hj : j.val + 1 = cell my y := by dsimp [j]; omega
    have h := hdev (pilotDesignKey mx hmx e) j
    rw [pilot_bernstein_cellCount_eq mx hmx d v e] at h
    have hraw := pilot_raw_density_error_of_bernstein P hModel mx my hmx hmy d v e j y
      ⟨hy, hj.symm⟩ hv u hcount h
    exact (not_lt_of_ge hraw) hfail
  · exact pilot_outcome_fibre_tail_le P hModel mx my hmx hmy d u hu

end CausalSmith.Stat.DensityEffectRoughNull
