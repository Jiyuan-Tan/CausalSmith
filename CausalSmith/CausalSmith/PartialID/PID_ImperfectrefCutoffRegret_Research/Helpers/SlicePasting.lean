import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Basic
import Mathlib.MeasureTheory.Measure.Dirac

/-! Finite slice pasting for the latent `(R,D)` coordinates. -/

open MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

def pasteSlices (κ : Bool → Bool → Measure ℝ) : Measure (ℝ × Bool × Bool) :=
  ∑ r : Bool, ∑ d : Bool,
    (κ r d).map (fun s => (s, r, d))

lemma pasteSlices_slice (κ : Bool → Bool → Measure ℝ) (r d : Bool)
    (hκ : ∀ r d, IsFiniteMeasure (κ r d)) :
    (pasteSlices κ).real {z | z.2.1 = r ∧ z.2.2 = d} =
      (κ r d).real Set.univ := by
  letI := hκ true true
  letI := hκ true false
  letI := hκ false true
  letI := hκ false false
  have hmap (r' d' : Bool) :
      ((κ r' d').map (fun s => (s, r', d'))).real
          {z | z.2.1 = r ∧ z.2.2 = d} =
        if r' = r ∧ d' = d then (κ r' d').real Set.univ else 0 := by
    letI := hκ r' d'
    have hevent : MeasurableSet {z : ℝ × Bool × Bool |
        z.2.1 = r ∧ z.2.2 = d} :=
      ((measurable_fst.comp measurable_snd) (MeasurableSet.singleton r)).inter
        ((measurable_snd.comp measurable_snd) (MeasurableSet.singleton d))
    rw [map_measureReal_apply (by fun_prop) hevent]
    by_cases h : r' = r ∧ d' = d
    · rcases h with ⟨rfl, rfl⟩
      simp
    · simp [h]
  cases r <;> cases d <;>
    simp [pasteSlices, measureReal_add_apply, hmap]

-- @node: pasteSlices_slice_apply
lemma pasteSlices_slice_apply (κ : Bool → Bool → Measure ℝ) (r d : Bool)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hκ : ∀ r d, IsFiniteMeasure (κ r d)) :
    (pasteSlices κ).real {z | z.1 ∈ B ∧ z.2.1 = r ∧ z.2.2 = d} =
      (κ r d).real B := by
  letI := hκ true true
  letI := hκ true false
  letI := hκ false true
  letI := hκ false false
  have hmap (r' d' : Bool) :
      ((κ r' d').map (fun s => (s, r', d'))).real
          {z | z.1 ∈ B ∧ z.2.1 = r ∧ z.2.2 = d} =
        if r' = r ∧ d' = d then (κ r' d').real B else 0 := by
    letI := hκ r' d'
    have hevent : MeasurableSet {z : ℝ × Bool × Bool |
        z.1 ∈ B ∧ z.2.1 = r ∧ z.2.2 = d} := by
      exact (hB.preimage measurable_fst).inter
        (((measurable_fst.comp measurable_snd) (MeasurableSet.singleton r)).inter
          ((measurable_snd.comp measurable_snd) (MeasurableSet.singleton d)))
    rw [map_measureReal_apply (by fun_prop) hevent]
    by_cases h : r' = r ∧ d' = d
    · rcases h with ⟨rfl, rfl⟩
      simp
    · simp [h]
  cases r <;> cases d <;>
    simp [pasteSlices, measureReal_add_apply, hmap]

lemma pasteSlices_probability (κ : Bool → Bool → Measure ℝ)
    (hmass : ∑ r : Bool, ∑ d : Bool, (κ r d) Set.univ = 1) :
    IsProbabilityMeasure (pasteSlices κ) := by
  refine ⟨?_⟩
  have hmap (r d : Bool) :
      ((κ r d).map (fun s => (s, r, d))) Set.univ = (κ r d) Set.univ := by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  simpa [pasteSlices, hmap] using hmass

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
