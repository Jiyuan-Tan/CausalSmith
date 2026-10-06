module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionEmpiricalMean
public import Mathlib.MeasureTheory.Integral.Prod

/-! Integration of pointwise empirical CDF bounds over a compact support. -/

public section

open MeasureTheory
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @node: measurable_projectionFiniteCDF
/-- Given [the stated mathematical inputs and assumptions](hyp:X,ν,hν,v), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurable_projectionFiniteCDF {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (hν : ν Set.univ < ⊤) (v : X → ℝ) :
    Measurable (fun t : ℝ => ν.real {x | v x ≤ t}) := by
  apply Monotone.measurable
  intro s t hst
  apply ENNReal.toReal_mono
  · exact ne_of_lt (lt_of_le_of_lt (measure_mono (by
      intro x hx
      exact trivial)) hν)
  · exact measure_mono (by
      intro x hx
      exact le_trans hx hst)

-- @node: measurable_empiricalTrialCellCDF_joint
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurable_empiricalTrialCellCDF_joint {J n : ℕ}
    (a : ArmSpace) (r : LabelSpace J) :
    Measurable (fun p : TrialSample n J × ℝ =>
      (empiricalTrialCells p.1 a r).real {y | (y : ℝ) ≤ p.2}) := by
  classical
  have heq : (fun p : TrialSample n J × ℝ =>
      (empiricalTrialCells p.1 a r).real {y | (y : ℝ) ≤ p.2}) =
      fun p => (n : ℝ)⁻¹ * ∑ i : Fin n,
        if (p.1 i).1 = r ∧ (p.1 i).2.1 = a ∧
            ((p.1 i).2.2 : ℝ) ≤ p.2 then (1 : ℝ) else 0 := by
    funext p
    rw [empiricalTrialCells_real_apply a r _
      (measurableSet_le (by fun_prop) measurable_const)]
    rfl
  rw [heq]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · have hi : Measurable (fun p : TrialSample n J × ℝ => p.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    simpa only [Set.ofPred_and, Set.inter_assoc, Function.comp_apply] using
      ((measurableSet_eq_fun hi.fst
        (measurable_const : Measurable (fun _ : TrialSample n J × ℝ => r))).inter
      (measurableSet_eq_fun hi.snd.fst
        (measurable_const : Measurable (fun _ : TrialSample n J × ℝ => a)))).inter
      (measurableSet_le (measurable_subtype_coe.comp hi.snd.snd) measurable_snd)
  · exact measurable_const
  · exact measurable_const

-- @node: measurable_trialPopulationCellCDF
/-- Given [the stated mathematical inputs and assumptions](hyp:J,μ,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurable_trialPopulationCellCDF {J : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ]
    (a : ArmSpace) (r : LabelSpace J) :
    Measurable (fun t : ℝ =>
      μ.real {z | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t}) := by
  let C : Set (Observation J) := {z | z.1 = r ∧ z.2.1 = a}
  have hC : MeasurableSet C := by
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_eq_fun (measurable_snd.fst) measurable_const)
  have hfin : (μ.restrict C) Set.univ < ⊤ := by
    simp
  have h := measurable_projectionFiniteCDF (μ.restrict C) hfin
    (fun z : Observation J => (z.2.2 : ℝ))
  convert h using 1
  funext t
  unfold Measure.real
  have hB : MeasurableSet {x : Observation J | (x.2.2 : ℝ) ≤ t} :=
    measurableSet_le (measurable_subtype_coe.comp measurable_snd.snd) measurable_const
  rw [Measure.restrict_apply hB]
  have hset : {z : Observation J | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t} =
      {x | (x.2.2 : ℝ) ≤ t} ∩ C := by
    ext z
    change (z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t) ↔
      ((z.2.2 : ℝ) ≤ t ∧ z.1 = r ∧ z.2.1 = a)
    tauto
  rw [hset]

-- @node: empiricalTrialCellCDF_mem_Icc
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,hn,a,r,x,t), this result [establishes the stated mathematical conclusion](goal). -/
lemma empiricalTrialCellCDF_mem_Icc {J n : ℕ} (hn : 0 < n)
    (a : ArmSpace) (r : LabelSpace J) (x : TrialSample n J) (t : ℝ) :
    (empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t} ∈ Set.Icc (0 : ℝ) 1 := by
  rw [empiricalTrialCells_real_apply a r _
    (measurableSet_le (by fun_prop) measurable_const)]
  unfold trialCellFrequency
  have hterm (i : Fin n) :
      (if (x i).1 = r ∧ (x i).2.1 = a ∧ ((x i).2.2 : ℝ) ≤ t then
        (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
    split_ifs <;> norm_num
  have hs0 : 0 ≤ ∑ i : Fin n,
      (if (x i).1 = r ∧ (x i).2.1 = a ∧ ((x i).2.2 : ℝ) ≤ t then
        (1 : ℝ) else 0) := Finset.sum_nonneg (fun i _ => (hterm i).1)
  have hs1 : (∑ i : Fin n,
      (if (x i).1 = r ∧ (x i).2.1 = a ∧ ((x i).2.2 : ℝ) ≤ t then
        (1 : ℝ) else 0)) ≤ n := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum
        (fun i _ => (hterm i).2)
      _ = n := by simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  constructor
  · exact mul_nonneg (inv_nonneg.mpr (le_of_lt hn')) hs0
  · exact (inv_mul_le_iff₀ hn').mpr (by simpa [mul_comm] using hs1)

-- @node: trialPopulationCellCDF_mem_Icc
/-- Given [the stated mathematical inputs and assumptions](hyp:J,μ,a,r,t), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialPopulationCellCDF_mem_Icc {J : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ]
    (a : ArmSpace) (r : LabelSpace J) (t : ℝ) :
    μ.real {z | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t} ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · unfold Measure.real
    have hm := measure_mono (μ := μ) (Set.subset_univ
      {z : Observation J | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t})
    have hfin : μ Set.univ ≠ ⊤ := by simp
    have := ENNReal.toReal_mono hfin hm
    simpa [isProbabilityMeasure_iff_real.mp inferInstance] using this

-- @node: integrable_empiricalTrialCellCDF_joint
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,hn,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma integrable_empiricalTrialCellCDF_joint {J n : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ] (hn : 0 < n)
    (a : ArmSpace) (r : LabelSpace J) :
    Integrable (Function.uncurry
      (fun (x : TrialSample n J) (t : ℝ) =>
        |(empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t} -
          μ.real {z | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t}|))
      ((Measure.pi fun _ : Fin n => μ).prod (volume.restrict (Set.Ioc 0 1))) := by
  have hm : Measurable (Function.uncurry
      (fun (x : TrialSample n J) (t : ℝ) =>
        |(empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t} -
          μ.real {z | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t}|)) :=
    (measurable_empiricalTrialCellCDF_joint a r |>.sub
      ((measurable_trialPopulationCellCDF μ a r).comp measurable_snd)).abs
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  rintro ⟨x, t⟩
  have hx := empiricalTrialCellCDF_mem_Icc hn a r x t
  have hp := trialPopulationCellCDF_mem_Icc μ a r t
  dsimp
  rw [abs_abs]
  apply abs_le.mpr
  constructor <;> linarith [hx.1, hx.2, hp.1, hp.2]

-- @node: projectionExpectedIntegratedError_le
/-- Given [the stated mathematical inputs and assumptions](hyp:Ω,μ,a,b,c,hab,F,hF,hpoint), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionExpectedIntegratedError_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (a b c : ℝ) (hab : a ≤ b)
    (F : Ω → ℝ → ℝ)
    (hF : Integrable (Function.uncurry F) (μ.prod (volume.restrict (Set.Ioc a b))))
    (hpoint : ∀ t ∈ Set.Ioc a b, ∫ x, F x t ∂μ ≤ c) :
    ∫ x, (∫ t in a..b, F x t) ∂μ ≤ (b - a) * c := by
  simp_rw [intervalIntegral.integral_of_le hab]
  have hswap := MeasureTheory.integral_integral_swap hF
  rw [hswap]
  have hconst : Integrable (fun _ : ℝ => c) (volume.restrict (Set.Ioc a b)) :=
    integrable_const _
  have hright : (∫ t in Set.Ioc a b, (∫ x, F x t ∂μ)) ≤
      ∫ t in Set.Ioc a b, c := by
    apply integral_mono_ae
    · exact hF.integral_prod_right
    · exact hconst
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hpoint t ht
  calc
    (∫ t in Set.Ioc a b, ∫ x, F x t ∂μ) ≤ ∫ t in Set.Ioc a b, c := hright
    _ = (b - a) * c := by
      rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const]
      simp

-- @node: meanIntegratedAbs_empiricalTrialCellCDF_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,hn,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma meanIntegratedAbs_empiricalTrialCellCDF_pi {J n : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ] (hn : 0 < n)
    (a : ArmSpace) (r : LabelSpace J) :
    ∫ x, (∫ t in (0 : ℝ)..1,
      |(empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t} -
        μ.real {z | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t}|)
      ∂Measure.pi (fun _ : Fin n => μ) ≤ 1 / (2 * Real.sqrt n) := by
  have hpoint (t : ℝ) (_ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      ∫ x, |(empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t} -
        μ.real {z | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t}|
        ∂Measure.pi (fun _ : Fin n => μ) ≤ 1 / (2 * Real.sqrt n) := by
    have hB : MeasurableSet {y : OutcomeSpace | (y : ℝ) ≤ t} :=
      measurableSet_le (by fun_prop) measurable_const
    simpa only [empiricalTrialCells_real_apply a r _ hB, Set.mem_ofPred_eq] using
      meanAbs_trialCellFrequency_pi μ hn a r _ hB
  have h := projectionExpectedIntegratedError_le
    (Measure.pi fun _ : Fin n => μ) 0 1 (1 / (2 * Real.sqrt n))
    (by norm_num) _ (integrable_empiricalTrialCellCDF_joint μ hn a r) hpoint
  simpa using h

-- @node: measurable_empiricalScoreCellCDF_joint
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,g,hg,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurable_empiricalScoreCellCDF_joint {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (a : ArmSpace) (r : LabelSpace J) :
    Measurable (fun p : (Fin m → ScoreSpace ε) × ℝ =>
      (empiricalScoreCells g p.1 a r).real {e | (e : ℝ) ≤ p.2}) := by
  classical
  have heq : (fun p : (Fin m → ScoreSpace ε) × ℝ =>
      (empiricalScoreCells g p.1 a r).real {e | (e : ℝ) ≤ p.2}) =
      fun p => (m : ℝ)⁻¹ * ∑ j : Fin m,
        if g (p.1 j) = r ∧ ((p.1 j : ScoreSpace ε) : ℝ) ≤ p.2 then
          armProb a (p.1 j) else 0 := by
    funext p
    rw [empiricalScoreCells_real_eq_scoreCellFrequency hOverlap g a r _
      (measurableSet_le (by fun_prop) measurable_const)]
    unfold scoreCellFrequency
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : g (p.1 j) = r ∧ ((p.1 j : ScoreSpace ε) : ℝ) ≤ p.2
    · simp [Set.indicator, hj]
    · simp [Set.indicator, hj]
  rw [heq]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  have hj : Measurable (fun p : (Fin m → ScoreSpace ε) × ℝ => p.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hp : Measurable (armProb a : ScoreSpace ε → ℝ) := by
    unfold armProb
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  apply Measurable.ite
  · exact (measurableSet_eq_fun (hg.comp hj) measurable_const).inter
      (measurableSet_le (measurable_subtype_coe.comp hj) measurable_snd)
  · exact hp.comp hj
  · exact measurable_const

-- @node: measurable_scorePopulationCellCDF
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hg,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurable_scorePopulationCellCDF {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace J) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J) :
    Measurable (fun t : ℝ =>
      ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
        (armProb a) e ∂H) := by
  have hp : Measurable (armProb a : ScoreSpace ε → ℝ) := by
    unfold armProb
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hF : Measurable (fun p : ℝ × ScoreSpace ε =>
      {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ p.1}.indicator
        (armProb a) p.2) := by
    apply Measurable.indicator
    · exact hp.comp measurable_snd
    · exact (measurableSet_eq_fun (hg.comp measurable_snd) measurable_const).inter
        (measurableSet_le (measurable_subtype_coe.comp measurable_snd) measurable_fst)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := H)).measurable

-- @node: integrable_empiricalScoreCellCDF_joint
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma integrable_empiricalScoreCellCDF_joint {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) (a : ArmSpace) (r : LabelSpace J) :
    Integrable (Function.uncurry
      (fun (x : Fin m → ScoreSpace ε) (t : ℝ) =>
        |(empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t} -
          ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
            (armProb a) e ∂H|))
      ((Measure.pi fun _ : Fin m => H).prod
        (volume.restrict (Set.Ioc ε (1 - ε)))) := by
  have hmeas : Measurable (Function.uncurry
      (fun (x : Fin m → ScoreSpace ε) (t : ℝ) =>
        |(empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t} -
          ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
            (armProb a) e ∂H|)) :=
    (measurable_empiricalScoreCellCDF_joint hOverlap g hg a r |>.sub
      ((measurable_scorePopulationCellCDF H g hg a r).comp measurable_snd)).abs
  apply Integrable.of_bound hmeas.aestronglyMeasurable 2
  apply Filter.Eventually.of_forall
  rintro ⟨x, t⟩
  have hB : MeasurableSet {e : ScoreSpace ε | (e : ℝ) ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  dsimp
  rw [empiricalScoreCells_real_eq_scoreCellFrequency hOverlap g a r _ hB]
  have hp : ∀ e : ScoreSpace ε, 0 ≤ armProb a e ∧ armProb a e ≤ 1 := by
    intro e
    exact ⟨le_trans (le_of_lt hOverlap.1) (projectionArmProb_bounds hOverlap a e).1,
      (projectionArmProb_bounds hOverlap a e).2⟩
  have hpop : 0 ≤ ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
      (armProb a) e ∂H := by
    apply integral_nonneg
    intro e
    by_cases he : g e = r ∧ (e : ℝ) ≤ t <;> simp [Set.indicator, he, (hp e).1]
  have hpop1 : (∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
      (armProb a) e ∂H) ≤ 1 := by
    calc
      _ ≤ ∫ _e : ScoreSpace ε, (1 : ℝ) ∂H := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun e => by
            by_cases he : g e = r ∧ (e : ℝ) ≤ t <;>
              simp [Set.indicator, he, (hp e).1])
        · exact integrable_const _
        · exact Filter.Eventually.of_forall (fun e => by
            by_cases he : g e = r ∧ (e : ℝ) ≤ t <;>
              simp [Set.indicator, he, (hp e).2])
      _ = 1 := by simp
  have hsample : 0 ≤ scoreCellFrequency g a r {e | (e : ℝ) ≤ t} x ∧
      scoreCellFrequency g a r {e | (e : ℝ) ≤ t} x ≤ 1 := by
    unfold scoreCellFrequency
    have hs (j : Fin m) :
        0 ≤ {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
          (armProb a) (x j) ∧
        {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
          (armProb a) (x j) ≤ 1 := by
      by_cases he : g (x j) = r ∧ ((x j : ScoreSpace ε) : ℝ) ≤ t <;>
        simp [Set.indicator, he, (hp (x j)).1, (hp (x j)).2]
    have hn : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    constructor
    · exact mul_nonneg (inv_nonneg.mpr (le_of_lt hn))
        (Finset.sum_nonneg (fun j _ => (hs j).1))
    · apply (inv_mul_le_iff₀ hn).mpr
      simpa using (Finset.sum_le_sum (fun j _ => (hs j).2) :
        (∑ j : Fin m, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
          (armProb a) (x j)) ≤ ∑ _j : Fin m, (1 : ℝ))
  rw [abs_abs]
  apply abs_le.mpr
  constructor <;> linarith [hsample.1, hsample.2, hpop, hpop1]

-- @node: meanIntegratedAbs_empiricalScoreCellCDF_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma meanIntegratedAbs_empiricalScoreCellCDF_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) (a : ArmSpace) (r : LabelSpace J) :
    ∫ x, (∫ t in ε..(1 - ε),
      |(empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t} -
        ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
          (armProb a) e ∂H|)
      ∂Measure.pi (fun _ : Fin m => H) ≤
        (1 - 2 * ε) / (2 * Real.sqrt m) := by
  have hpoint (t : ℝ) (_ht : t ∈ Set.Ioc ε (1 - ε)) :
      ∫ x, |(empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t} -
        ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
          (armProb a) e ∂H|
        ∂Measure.pi (fun _ : Fin m => H) ≤ 1 / (2 * Real.sqrt m) := by
    have hB : MeasurableSet {e : ScoreSpace ε | (e : ℝ) ≤ t} :=
      measurableSet_le (by fun_prop) measurable_const
    exact meanAbs_empiricalScoreCells_pi hOverlap H g hg hm a r _ hB
  have hε : ε ≤ 1 - ε := by linarith [hOverlap.2]
  have h := projectionExpectedIntegratedError_le
    (Measure.pi fun _ : Fin m => H) ε (1 - ε)
    (1 / (2 * Real.sqrt m)) hε _
    (integrable_empiricalScoreCellCDF_joint hOverlap H g hg hm a r) hpoint
  convert h using 1
  ring

-- @node: sum_meanTrialCellCDFError_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,hn), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_meanTrialCellCDFError_pi {J n : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ] (hn : 0 < n) :
    (∑ a : ArmSpace, ∑ r : LabelSpace J,
      ((∫ x : TrialSample n J, |(empiricalTrialCells x a r).real Set.univ -
        μ.real {z : Observation J | z.1 = r ∧ z.2.1 = a}| ∂Measure.pi (fun _ : Fin n => μ)) +
      (∫ x : TrialSample n J, (∫ t in (0 : ℝ)..1,
        |(empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t} -
          μ.real {z : Observation J | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t}|)
        ∂Measure.pi (fun _ : Fin n => μ)))) ≤ 2 * J / Real.sqrt n := by
  have hmass : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      ∫ x : TrialSample n J, |(empiricalTrialCells x a r).real Set.univ -
        μ.real {z : Observation J | z.1 = r ∧ z.2.1 = a}| ∂Measure.pi (fun _ : Fin n => μ)) ≤
      J / Real.sqrt n := by
    simpa only [empiricalTrialCells_real_apply _ _ Set.univ MeasurableSet.univ,
      Set.mem_univ, and_true] using
      sum_meanAbs_trialCellFrequency_pi μ hn
        (fun _ _ => Set.univ) (fun _ _ => MeasurableSet.univ)
  have hcdf : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      ∫ x : TrialSample n J, (∫ t in (0 : ℝ)..1,
        |(empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t} -
          μ.real {z : Observation J | z.1 = r ∧ z.2.1 = a ∧ (z.2.2 : ℝ) ≤ t}|)
        ∂Measure.pi (fun _ : Fin n => μ)) ≤ J / Real.sqrt n := by
    calc
      _ ≤ ∑ a : ArmSpace, ∑ _r : LabelSpace J,
          (1 / (2 * Real.sqrt n) : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro r _
        exact meanIntegratedAbs_empiricalTrialCellCDF_pi μ hn a r
      _ = J / Real.sqrt n := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul]
        field_simp
        ring
  simp_rw [Finset.sum_add_distrib]
  calc
    _ ≤ J / Real.sqrt n + J / Real.sqrt n := add_le_add hmass hcdf
    _ = 2 * J / Real.sqrt n := by ring

-- @node: sum_meanScoreCellCDFError_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_meanScoreCellCDFError_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) :
    (∑ a : ArmSpace, ∑ r : LabelSpace J,
      ((∫ x : Fin m → ScoreSpace ε,
        |(empiricalScoreCells g x a r).real Set.univ -
          ∫ e, {e : ScoreSpace ε | g e = r}.indicator (armProb a) e ∂H|
        ∂Measure.pi (fun _ : Fin m => H)) +
      (∫ x : Fin m → ScoreSpace ε, (∫ t in ε..(1 - ε),
        |(empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t} -
          ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
            (armProb a) e ∂H|)
        ∂Measure.pi (fun _ : Fin m => H)))) ≤
      J * (2 - 2 * ε) / Real.sqrt m := by
  have hmass : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      ∫ x : Fin m → ScoreSpace ε,
        |(empiricalScoreCells g x a r).real Set.univ -
          ∫ e, {e : ScoreSpace ε | g e = r}.indicator (armProb a) e ∂H|
        ∂Measure.pi (fun _ : Fin m => H)) ≤ J / Real.sqrt m := by
    simpa only [Set.mem_univ, and_true] using
      sum_meanAbs_empiricalScoreCells_pi hOverlap H g hg hm
        (fun _ _ => Set.univ) (fun _ _ => MeasurableSet.univ)
  have hcdf : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      ∫ x : Fin m → ScoreSpace ε, (∫ t in ε..(1 - ε),
        |(empiricalScoreCells g x a r).real {e | (e : ℝ) ≤ t} -
          ∫ e, {e : ScoreSpace ε | g e = r ∧ (e : ℝ) ≤ t}.indicator
            (armProb a) e ∂H|)
        ∂Measure.pi (fun _ : Fin m => H)) ≤
      J * (1 - 2 * ε) / Real.sqrt m := by
    calc
      _ ≤ ∑ a : ArmSpace, ∑ _r : LabelSpace J,
          ((1 - 2 * ε) / (2 * Real.sqrt m) : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro r _
        exact meanIntegratedAbs_empiricalScoreCellCDF_pi hOverlap H g hg hm a r
      _ = J * (1 - 2 * ε) / Real.sqrt m := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul]
        field_simp
        ring
  simp_rw [Finset.sum_add_distrib]
  calc
    _ ≤ J / Real.sqrt m + J * (1 - 2 * ε) / Real.sqrt m :=
      add_le_add hmass hcdf
    _ = J * (2 - 2 * ε) / Real.sqrt m := by ring

end
end CausalSmith.PartialID.UnlinkedPropensityAte
