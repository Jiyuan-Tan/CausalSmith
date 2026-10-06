module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.BernoulliHypercube

/-!
# Cell-local KL bounds for Bernoulli hypercube witnesses

This file integrates the pointwise Bernoulli KL estimate over a measurable
covariate cell and lifts the result through pilot observation and iid products.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {d : ℕ}

private noncomputable def cellUnitFiber (g : XSpace d → ℝ) (x : XSpace d) :
    Measure (UnitRecord d) :=
  let q0 := ENNReal.ofReal (1 - g x)
  let q1 := ENNReal.ofReal (g x)
  (q0 * q0) • Measure.dirac (x, (0 : ℝ), (0 : ℝ)) +
    (q0 * q1) • Measure.dirac (x, (0 : ℝ), (1 : ℝ)) +
    (q1 * q0) • Measure.dirac (x, (1 : ℝ), (0 : ℝ)) +
    (q1 * q1) • Measure.dirac (x, (1 : ℝ), (1 : ℝ))

private lemma measurable_cellUnitFiber (g : XSpace d → ℝ) (hg : Measurable g) :
    Measurable (cellUnitFiber g) := by
  rw [Measure.measurable_measure]
  intro s hs
  simp only [cellUnitFiber, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  fun_prop

private lemma cellUnitFiber_eq (g : XSpace d → ℝ) (x : XSpace d) :
    cellUnitFiber g x =
      ((bernoulliOutcomeLaw (g x)).prod (bernoulliOutcomeLaw (g x))).map
        fun ys => (x, ys.1, ys.2) := by
  unfold cellUnitFiber bernoulliOutcomeLaw
  rw [← Measure.dirac_prod]
  simp only [Measure.prod_add, Measure.add_prod, Measure.prod_smul_left,
    Measure.prod_smul_right, Measure.dirac_prod_dirac]
  simp only [smul_add, smul_smul]
  module

private lemma bernoulliUnitLaw_eq_bind_cellUnitFiber (g : XSpace d → ℝ) :
    bernoulliUnitLaw g = (cubeMeasure d).bind (cellUnitFiber g) := by
  unfold bernoulliUnitLaw
  congr 1
  funext x
  exact (cellUnitFiber_eq g x).symm

private lemma cellUnitFiber_isProbabilityMeasure (g : XSpace d → ℝ) (x : XSpace d)
    (hlo : 0 ≤ g x) (hhi : g x ≤ 1) : IsProbabilityMeasure (cellUnitFiber g x) := by
  rw [cellUnitFiber_eq]
  have hout : IsProbabilityMeasure (bernoulliOutcomeLaw (g x)) := by
    rw [show bernoulliOutcomeLaw (g x) =
      Causalean.Mathlib.Probability.bernoulliLaw (g x) by
        simp only [bernoulliOutcomeLaw,
          Causalean.Mathlib.Probability.bernoulliLaw]
        ac_rfl]
    exact Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hlo hhi
  letI : IsProbabilityMeasure (bernoulliOutcomeLaw (g x)) := hout
  exact Measure.isProbabilityMeasure_map (by fun_prop)

private lemma cellUnitFiber_klDiv_le (g g' : XSpace d → ℝ) (x : XSpace d)
    (hglo : 1 / 4 ≤ g x) (hghi : g x ≤ 3 / 4)
    (hg'lo : 1 / 4 ≤ g' x) (hg'hi : g' x ≤ 3 / 4) :
    InformationTheory.klDiv (cellUnitFiber g x) (cellUnitFiber g' x) ≤
      ENNReal.ofReal (8 * (g x - g' x) ^ 2) := by
  let μ := Causalean.Mathlib.Probability.bernoulliLaw (g x)
  let ν := Causalean.Mathlib.Probability.bernoulliLaw (g' x)
  letI : IsProbabilityMeasure μ :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
      (by linarith) (by linarith)
  letI : IsProbabilityMeasure ν :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
      (by linarith) (by linarith)
  have hac : μ ≪ ν :=
    Causalean.Mathlib.Probability.bernoulliLaw_ac_of_reference_interior
      (by linarith) (by linarith)
  have hint : Integrable (llr μ ν) μ :=
    Causalean.Mathlib.Probability.bernoulliLaw_llr_integrable
  have hprod := Causalean.Mathlib.InformationTheory.ProductKL.klDiv_prod_toReal_add
    μ ν μ ν hac hac hint hint
  have hbern := Causalean.Mathlib.Probability.bernoulliLaw_klDiv_le_four_sq_sub
    hglo hghi hg'lo hg'hi
  have hbern_fin : InformationTheory.klDiv μ ν ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hac hint
  have hprod_fin : InformationTheory.klDiv (μ.prod μ) (ν.prod ν) ≠ ⊤ := by
    exact InformationTheory.klDiv_ne_top_iff.mpr
      ⟨hac.prod hac,
        Causalean.Mathlib.InformationTheory.ProductKL.llr_prod_integrable
          μ ν μ ν hac hac hint hint⟩
  rw [cellUnitFiber_eq, cellUnitFiber_eq]
  have heq (p : ℝ) : bernoulliOutcomeLaw p =
      Causalean.Mathlib.Probability.bernoulliLaw p := by
    simp only [bernoulliOutcomeLaw, Causalean.Mathlib.Probability.bernoulliLaw]
    ac_rfl
  rw [heq, heq]
  have hemb : MeasurableEmbedding (fun ys : ℝ × ℝ => (x, ys.1, ys.2)) := by
    simpa only using (measurableEmbedding_prodMk_left x)
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding hemb]
  rw [← ENNReal.ofReal_toReal hprod_fin]
  apply ENNReal.ofReal_le_ofReal
  rw [hprod]
  have hreal : (InformationTheory.klDiv μ ν).toReal ≤ 4 * (g x - g' x) ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hbern
  linarith

private lemma cellUnitFiber_ac (g g' : XSpace d → ℝ) (x : XSpace d)
    (hglo : 1 / 4 ≤ g x) (hghi : g x ≤ 3 / 4)
    (hg'lo : 1 / 4 ≤ g' x) (hg'hi : g' x ≤ 3 / 4) :
    cellUnitFiber g x ≪ cellUnitFiber g' x := by
  let μ := Causalean.Mathlib.Probability.bernoulliLaw (g x)
  let ν := Causalean.Mathlib.Probability.bernoulliLaw (g' x)
  letI : IsProbabilityMeasure μ :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
      (by linarith [hglo]) (by linarith [hghi])
  letI : IsProbabilityMeasure ν :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
      (by linarith) (by linarith)
  have hac : μ ≪ ν :=
    Causalean.Mathlib.Probability.bernoulliLaw_ac_of_reference_interior
      (by linarith) (by linarith)
  have heq (p : ℝ) : bernoulliOutcomeLaw p =
      Causalean.Mathlib.Probability.bernoulliLaw p := by
    simp only [bernoulliOutcomeLaw, Causalean.Mathlib.Probability.bernoulliLaw]
    ac_rfl
  rw [cellUnitFiber_eq, cellUnitFiber_eq, heq, heq]
  exact (hac.prod hac).map (by fun_prop)

private lemma cellUnitFiber_fibre (g : XSpace d → ℝ) (x : XSpace d)
    (hlo : 0 ≤ g x) (hhi : g x ≤ 1) :
    cellUnitFiber g x {u | u.1 = x}ᶜ = 0 := by
  letI : IsProbabilityMeasure (cellUnitFiber g x) :=
    cellUnitFiber_isProbabilityMeasure g x hlo hhi
  letI : IsProbabilityMeasure (bernoulliOutcomeLaw (g x)) := by
    rw [show bernoulliOutcomeLaw (g x) =
      Causalean.Mathlib.Probability.bernoulliLaw (g x) by
        simp only [bernoulliOutcomeLaw,
          Causalean.Mathlib.Probability.bernoulliLaw]
        ac_rfl]
    exact Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hlo hhi
  have hmap : (cellUnitFiber g x).map Prod.fst = Measure.dirac x := by
    rw [cellUnitFiber_eq, Measure.map_map]
    · rw [show Prod.fst ∘ (fun ys : ℝ × ℝ => (x, ys.1, ys.2)) =
          (fun _ : ℝ × ℝ => x) by funext ys; rfl]
      rw [Measure.map_const, measure_univ, one_smul]
    · fun_prop
    · fun_prop
  have hs : MeasurableSet ({x}ᶜ : Set (XSpace d)) := MeasurableSet.compl (measurableSet_singleton x)
  have hm := congrArg (fun μ : Measure (XSpace d) => μ ({x}ᶜ)) hmap
  rw [Measure.map_apply measurable_fst hs, Measure.dirac_apply' _ hs] at hm
  change cellUnitFiber g x (Prod.fst ⁻¹' {x})ᶜ = 0
  simpa [Set.indicator_apply] using hm

private noncomputable def safeCellUnitFiber (g : XSpace d → ℝ) (x : XSpace d) :
    Measure (UnitRecord d) := by
  classical
  exact if x ∈ cube d then cellUnitFiber g x else Measure.dirac (x, 0, 0)

private lemma measurable_safeCellUnitFiber (g : XSpace d → ℝ) (hg : Measurable g) :
    Measurable (safeCellUnitFiber g) := by
  classical
  unfold safeCellUnitFiber
  apply Measurable.ite
  · unfold cube
    measurability
  · exact measurable_cellUnitFiber g hg
  · exact Measure.measurable_dirac.comp (by fun_prop)

private lemma safeCellUnitFiber_eq_of_mem (g : XSpace d → ℝ) {x : XSpace d}
    (hx : x ∈ cube d) : safeCellUnitFiber g x = cellUnitFiber g x := by
  classical
  simp [safeCellUnitFiber, hx]

private lemma bernoulliUnitLaw_eq_bind_safeCellUnitFiber (g : XSpace d → ℝ)
    (hg : Measurable g) :
    bernoulliUnitLaw g = (cubeMeasure d).bind (safeCellUnitFiber g) := by
  rw [bernoulliUnitLaw_eq_bind_cellUnitFiber]
  apply Measure.bind_congr_right
  filter_upwards [ae_restrict_mem (by unfold cube; measurability)] with x hx
  exact (safeCellUnitFiber_eq_of_mem g hx).symm

private lemma safeCellUnitFiber_isProbabilityMeasure (g : XSpace d → ℝ) (x : XSpace d)
    (hband : ∀ z ∈ cube d, 1 / 4 ≤ g z ∧ g z ≤ 3 / 4) :
    IsProbabilityMeasure (safeCellUnitFiber g x) := by
  classical
  by_cases hx : x ∈ cube d
  · rw [safeCellUnitFiber_eq_of_mem g hx]
    exact cellUnitFiber_isProbabilityMeasure g x (by linarith [(hband x hx).1])
      (by linarith [(hband x hx).2])
  · rw [safeCellUnitFiber, if_neg hx]
    constructor
    simp

private lemma safeCellUnitFiber_fibre (g : XSpace d → ℝ) (x : XSpace d)
    (hband : ∀ z ∈ cube d, 1 / 4 ≤ g z ∧ g z ≤ 3 / 4) :
    safeCellUnitFiber g x {u | u.1 = x}ᶜ = 0 := by
  classical
  by_cases hx : x ∈ cube d
  · rw [safeCellUnitFiber_eq_of_mem g hx]
    exact cellUnitFiber_fibre g x (by linarith [(hband x hx).1])
      (by linarith [(hband x hx).2])
  · simp [safeCellUnitFiber, hx]

/-- If two quarter-band scores differ by at most `δ` on a measurable cell and
agree off that cell, their unit-law KL is at most eight times `δ²` times the
cell mass. -/
lemma bernoulliUnitLaw_klDiv_le_cell (g g' : XSpace d → ℝ)
    (hg : Measurable g) (hg' : Measurable g')
    (hband : ∀ x ∈ cube d, 1 / 4 ≤ g x ∧ g x ≤ 3 / 4)
    (hband' : ∀ x ∈ cube d, 1 / 4 ≤ g' x ∧ g' x ≤ 3 / 4)
    (C : Set (XSpace d)) (hC : MeasurableSet C)
    (hoff : ∀ x ∉ C, g x = g' x)
    (δ : ℝ) (hδ : 0 ≤ δ) (hgap : ∀ x ∈ C, |g x - g' x| ≤ δ) :
    InformationTheory.klDiv (bernoulliUnitLaw g) (bernoulliUnitLaw g') ≤
      ENNReal.ofReal (8 * δ ^ 2 * (cubeMeasure d C).toReal) := by
  classical
  let κ : Kernel (XSpace d) (UnitRecord d) :=
    Kernel.mk (safeCellUnitFiber g) (measurable_safeCellUnitFiber g hg)
  let η : Kernel (XSpace d) (UnitRecord d) :=
    Kernel.mk (safeCellUnitFiber g') (measurable_safeCellUnitFiber g' hg')
  letI : IsProbabilityMeasure (cubeMeasure d) := cubeMeasure_isProbabilityMeasure d
  letI : IsMarkovKernel κ := by
    refine ⟨?_⟩
    intro x
    exact safeCellUnitFiber_isProbabilityMeasure g x hband
  letI : IsMarkovKernel η := by
    refine ⟨?_⟩
    intro x
    exact safeCellUnitFiber_isProbabilityMeasure g' x hband'
  have hchain : InformationTheory.klDiv (bernoulliUnitLaw g) (bernoulliUnitLaw g') =
      ∫⁻ x, InformationTheory.klDiv (κ x) (η x) ∂cubeMeasure d := by
    rw [bernoulliUnitLaw_eq_bind_safeCellUnitFiber g hg,
      bernoulliUnitLaw_eq_bind_safeCellUnitFiber g' hg']
    change InformationTheory.klDiv ((cubeMeasure d).bind κ) ((cubeMeasure d).bind η) = _
    apply Causalean.Mathlib.InformationTheory.Measure.klDiv_bind_eq_of_base_recording
      (m := cubeMeasure d) (κ := κ) (η := η)
      (proj := Prod.fst) (hproj := measurable_fst)
    · exact measurableSet_eq_fun measurable_fst (measurable_fst.comp measurable_snd)
    · exact Filter.Eventually.of_forall fun x => safeCellUnitFiber_fibre g x hband
    · exact Filter.Eventually.of_forall fun x => safeCellUnitFiber_fibre g' x hband'
    · filter_upwards [ae_restrict_mem (by unfold cube; measurability)] with x hx
      change safeCellUnitFiber g x ≪ safeCellUnitFiber g' x
      rw [safeCellUnitFiber_eq_of_mem g hx, safeCellUnitFiber_eq_of_mem g' hx]
      exact cellUnitFiber_ac g g' x (hband x hx).1 (hband x hx).2
        (hband' x hx).1 (hband' x hx).2
  rw [hchain]
  calc
    (∫⁻ x, InformationTheory.klDiv (κ x) (η x) ∂cubeMeasure d) ≤
        ∫⁻ x, C.indicator (fun _ => ENNReal.ofReal (8 * δ ^ 2)) x ∂cubeMeasure d := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (by unfold cube; measurability)] with x hxcube
      by_cases hx : x ∈ C
      · rw [Set.indicator_of_mem hx]
        change InformationTheory.klDiv (safeCellUnitFiber g x)
          (safeCellUnitFiber g' x) ≤ _
        rw [safeCellUnitFiber_eq_of_mem g hxcube,
          safeCellUnitFiber_eq_of_mem g' hxcube]
        refine (cellUnitFiber_klDiv_le g g' x ?_ ?_ ?_ ?_).trans ?_
        · exact (hband x hxcube).1
        · exact (hband x hxcube).2
        · exact (hband' x hxcube).1
        · exact (hband' x hxcube).2
        · apply ENNReal.ofReal_le_ofReal
          have hsquare : (g x - g' x) ^ 2 ≤ δ ^ 2 := by
            nlinarith [sq_nonneg (δ - |g x - g' x|), hgap x hx,
              abs_nonneg (g x - g' x), sq_abs (g x - g' x)]
          nlinarith
      · rw [Set.indicator_of_notMem hx]
        change InformationTheory.klDiv (safeCellUnitFiber g x)
          (safeCellUnitFiber g' x) ≤ 0
        rw [safeCellUnitFiber_eq_of_mem g hxcube,
          safeCellUnitFiber_eq_of_mem g' hxcube]
        have heq : cellUnitFiber g x = cellUnitFiber g' x := by
          rw [cellUnitFiber_eq, cellUnitFiber_eq, hoff x hx]
        rw [heq]
        letI : IsProbabilityMeasure (cellUnitFiber g' x) :=
          cellUnitFiber_isProbabilityMeasure g' x
            (by linarith [(hband' x hxcube).1])
            (by linarith [(hband' x hxcube).2])
        exact le_of_eq (InformationTheory.klDiv_self (cellUnitFiber g' x))
    _ = ENNReal.ofReal (8 * δ ^ 2) * cubeMeasure d C := by
      rw [lintegral_indicator hC, lintegral_const, Measure.restrict_apply_univ]
    _ = ENNReal.ofReal (8 * δ ^ 2 * (cubeMeasure d C).toReal) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top (cubeMeasure d) C),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [ENNReal.toReal_ofReal]
      positivity

/-- The cell-local unit-law budget lifts to an iid randomized-pilot sample. -/
lemma bernoulliPilotProduct_klDiv_le_cell (m : ℕ) (g g' : XSpace d → ℝ)
    (hg : Measurable g) (hg' : Measurable g')
    (hband : ∀ x ∈ cube d, 1 / 4 ≤ g x ∧ g x ≤ 3 / 4)
    (hband' : ∀ x ∈ cube d, 1 / 4 ≤ g' x ∧ g' x ≤ 3 / 4)
    (C : Set (XSpace d)) (hC : MeasurableSet C)
    (hoff : ∀ x ∉ C, g x = g' x)
    (δ : ℝ) (hδ : 0 ≤ δ) (hgap : ∀ x ∈ C, |g x - g' x| ≤ δ) :
    InformationTheory.klDiv
      (Measure.pi fun _ : Fin m => pilotUnitLaw (bernoulliUnitLaw g))
      (Measure.pi fun _ : Fin m => pilotUnitLaw (bernoulliUnitLaw g')) ≤
        ENNReal.ofReal ((m : ℝ) * (8 * δ ^ 2 * (cubeMeasure d C).toReal)) := by
  apply bernoulliPilotProduct_klDiv_le_of_unit m g g' hg hg'
  · intro x hx
    constructor <;> linarith [hband x hx]
  · intro x hx
    constructor <;> linarith [hband' x hx]
  · positivity
  · exact bernoulliUnitLaw_klDiv_le_cell g g' hg hg' hband hband' C hC hoff δ hδ hgap

end CausalSmith.Experimentation.PilotscorePairingFrontier
