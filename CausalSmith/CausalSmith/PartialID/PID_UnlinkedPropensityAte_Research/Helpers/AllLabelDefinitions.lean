module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Basic

/-! Definitions shared by the all-label ambiguity proof leaves. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,J,H,g,a,r), [this definition](goal) introduces the corresponding object. -/
def cellAbsoluteDeviation {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (a : ArmSpace) (r : LabelSpace J) : ℝ :=
  sInf {v : ℝ | ∃ c ∈ Set.Icc ((1 - ε)⁻¹) ε⁻¹,
    v = ∫ e in cell g r, |1 - c * armProb a e| ∂H}

/-- For [the specified mathematical inputs](hyp:ε,J,H,g), [this definition](goal) introduces the corresponding object. -/
def halfOutcomeReleasedLaw {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J) :
    Measure (Observation J) :=
  ∑ r : LabelSpace J, ∑ a : ArmSpace,
    ((ENNReal.ofReal (armCellMass H g a r)) / 2) •
      (Measure.dirac (r, a, (⟨0, by norm_num⟩ : OutcomeSpace)) +
        Measure.dirac (r, a, (⟨1, by norm_num⟩ : OutcomeSpace)))

-- @node: armCellMass_nonneg
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,a,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellMass_nonneg {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (hOverlap : Overlap ε) (a : ArmSpace) (r : LabelSpace J) :
    0 ≤ armCellMass H g a r := by
  unfold armCellMass
  apply integral_nonneg
  intro e
  rcases e.property with ⟨he₁, he₂⟩
  rcases hOverlap with ⟨hε, _⟩
  cases a <;> simp [armProb] <;> linarith

-- @node: armCellMass_sum_arms
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellMass_sum_arms {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (r : LabelSpace J) :
    (∑ a : ArmSpace, armCellMass H g a r) = H.real (cell g r) := by
  have hint : IntegrableOn (fun e : ScoreSpace ε => (e : ℝ)) (cell g r) H := by
    apply Integrable.of_bound (by fun_prop) (|ε| + |1 - ε| + 1)
    filter_upwards [] with e
    change |(e : ℝ)| ≤ |ε| + |1 - ε| + 1
    rcases e.property with ⟨he₁, he₂⟩
    have h₁ := neg_le_abs ε
    have h₂ := le_abs_self (1 - ε)
    have h₃ := neg_le_abs (1 - ε)
    have h₄ := le_abs_self ε
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [Fintype.sum_bool, armCellMass, armProb, Bool.false_eq_true,
    ↓reduceIte]
  rw [integral_sub (integrable_const 1) hint]
  simp

-- @node: armCellMass_total
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma armCellMass_total {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hg : Measurable g) :
    (∑ r : LabelSpace J, ∑ a : ArmSpace, armCellMass H g a r) = 1 := by
  simp_rw [armCellMass_sum_arms H g]
  have h := MeasureTheory.sum_measureReal_preimage_singleton (μ := H)
    (s := Finset.univ) (f := g)
    (by intro r hr; exact measurableSet_eq_fun hg measurable_const)
  simpa [cell, Set.preimage, Set.mem_singleton_iff] using h

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,hOverlap,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma halfOutcomeReleasedLaw_cellMasses {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    [IsProbabilityMeasure H] (hOverlap : Overlap ε) (hg : Measurable g) :
    CompatibleCellMasses H g (halfOutcomeReleasedLaw H g) := by
  unfold CompatibleCellMasses
  refine ⟨inferInstance, ?_, hg, ?_⟩
  · let t (a : ArmSpace) : ENNReal :=
      ∑ r : LabelSpace J, ENNReal.ofReal (armCellMass H g a r) / 2
    have htfinite (a : ArmSpace) : t a ≠ ⊤ := by
      dsimp [t]
      apply ENNReal.sum_ne_top.mpr
      intro r hr
      exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num)
    have htReal (a : ArmSpace) : (t a).toReal =
        (∑ r : LabelSpace J, armCellMass H g a r) / 2 := by
      dsimp [t]
      rw [ENNReal.toReal_sum]
      · simp_rw [ENNReal.toReal_div, ENNReal.toReal_ofReal
          (armCellMass_nonneg H g hOverlap a _)]
        simp [← Finset.sum_div]
      · intro r hr
        exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num)
    apply isProbabilityMeasure_iff_real.mpr
    simp [halfOutcomeReleasedLaw, Measure.real_def, Finset.sum_add_distrib]
    change (t true + t false + (t true + t false)).toReal = 1
    have htf : t true + t false ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨htfinite true, htfinite false⟩
    rw [ENNReal.toReal_add htf htf,
      ENNReal.toReal_add (htfinite true) (htfinite false),
      htReal true, htReal false]
    have htotal := armCellMass_total H g hg
    simp only [Fintype.sum_bool, Finset.sum_add_distrib] at htotal
    linarith
  · intro a r
    simp [halfOutcomeReleasedLaw, Measure.real_def, Set.indicator]
    cases a <;> simp [Finset.sum_add_distrib]
    all_goals exact armCellMass_nonneg H g hOverlap _ r

end
end CausalSmith.PartialID.UnlinkedPropensityAte
