module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.Experiment
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.Triple
public import Mathlib.MeasureTheory.Integral.Pi

/-! Relaxed finite-intensity tables for the many-cell lower bound. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/-- For [the specified inputs and assumptions](hyp:d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev RelaxedZengRecord (d : ℕ) := ZengRecord (d + 1)

/-- For [the specified inputs and assumptions](hyp:d,r), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def relaxedEmbedZengRecord {d : ℕ} (r : ZengRecord d) : RelaxedZengRecord d :=
  (Fin.castSucc r.1, r.2)

/-- For [the specified inputs and assumptions](hyp:d,a0,z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def relaxedZengTable (d : ℕ) (a0 : ℝ)
    (z : Fin d → MarkedParam) : Measure (RelaxedZengRecord d) :=
  ENNReal.ofReal ((1 - d * a0) / 2) •
      Measure.dirac (Fin.last d, true, false) +
    ENNReal.ofReal ((1 - d * a0) / 2) •
      Measure.dirac (Fin.last d, false, false) +
    (zengFiniteTable d (fun x => (z x).1) (fun x => (z x).2.1)
      (fun x => (z x).2.2)).map relaxedEmbedZengRecord

private lemma sum_bool_relaxed (f : Bool → ℝ≥0∞) :
    ∑ b : Bool, f b = f false + f true := by
  rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
  simp

private lemma relaxed_cell_mass (q a m : ℝ) (hq : 0 ≤ q)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hm : 0 ≤ m) (hm' : m ≤ 1) :
    ∑ b : Bool, ∑ y : Bool,
      ENNReal.ofReal (q * zengBernWeight a b *
        (if b then zengBernWeight m y else if y then 0 else 1)) =
      ENNReal.ofReal q := by
  rw [sum_bool_relaxed]
  simp_rw [sum_bool_relaxed]
  change
    (ENNReal.ofReal (q * (1 - a) * 1) + ENNReal.ofReal (q * (1 - a) * 0)) +
      (ENNReal.ofReal (q * a * (1 - m)) + ENNReal.ofReal (q * a * m)) =
        ENNReal.ofReal q
  simp only [mul_zero, mul_one, ENNReal.ofReal_zero, add_zero]
  rw [← ENNReal.ofReal_add
    (mul_nonneg (mul_nonneg hq ha) (sub_nonneg.mpr hm'))
    (mul_nonneg (mul_nonneg hq ha) hm)]
  rw [← ENNReal.ofReal_add
    (mul_nonneg hq (sub_nonneg.mpr ha'))
    (add_nonneg
      (mul_nonneg (mul_nonneg hq ha) (sub_nonneg.mpr hm'))
      (mul_nonneg (mul_nonneg hq ha) hm))]
  congr 1
  ring

private lemma zengFiniteTable_univ_relaxed (d : ℕ) (p π μ : Fin d → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hπ : ∀ x, 0 ≤ π x ∧ π x ≤ 1)
    (hμ : ∀ x, 0 ≤ μ x ∧ μ x ≤ 1) :
    zengFiniteTable d p π μ Set.univ = ENNReal.ofReal (∑ x, p x) := by
  calc
    zengFiniteTable d p π μ Set.univ =
        ∑ x, ∑ b, ∑ y, ENNReal.ofReal
          (p x * zengBernWeight (π x) b *
            if b then zengBernWeight (μ x) y else if y then 0 else 1) := by
      simp [zengFiniteTable]
    _ = ∑ x, ENNReal.ofReal (p x) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact relaxed_cell_mass (p x) (π x) (μ x) (hp x)
        (hπ x).1 (hπ x).2 (hμ x).1 (hμ x).2
    _ = ENNReal.ofReal (∑ x, p x) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      exact fun x hx => hp x

private lemma integrable_of_finite_support {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {ν : Measure α} [IsProbabilityMeasure ν]
    {s : Finset α} (hs : ν (s : Set α) = 1) {f : α → ℝ}
    (hf : StronglyMeasurable f) : Integrable f ν := by
  have hae : ∀ᵐ x ∂ν, x ∈ s := by
    apply (ae_mem_iff_measure_eq s.measurableSet.nullMeasurableSet).2
    simpa using hs
  rw [Measure.ae_mem_finset_iff.mp hae]
  apply integrable_finsetSum_measure.2
  intro x hx
  exact (integrable_dirac' hf (by simp)).smul_measure (by simp)

private lemma integral_iid_sum {d : ℕ} {ν : Measure MarkedParam}
    [IsProbabilityMeasure ν] {s : Finset MarkedParam}
    (hs : ν (s : Set MarkedParam) = 1) (f : MarkedParam → ℝ)
    (hf : StronglyMeasurable f) :
    (∫ z : Fin d → MarkedParam, ∑ x, f (z x) ∂Measure.pi (fun _ : Fin d => ν)) =
      d * ∫ t, f t ∂ν := by
  rw [integral_finsetSum]
  · calc
      ∑ x : Fin d, ∫ z, f (z x) ∂Measure.pi (fun _ : Fin d => ν) =
          ∑ _x : Fin d, ∫ t, f t ∂ν := by
            apply Finset.sum_congr rfl
            intro x hx
            exact integral_comp_eval (μ := fun _ : Fin d => ν)
              (i := x) hf.aestronglyMeasurable
      _ = d * ∫ t, f t ∂ν := by simp
  · intro x hx
    exact integrable_comp_eval (μ := fun _ : Fin d => ν)
      (i := x) (integrable_of_finite_support hs hf)

end CausalSmith.Stat.MarRareqLogfrontier
