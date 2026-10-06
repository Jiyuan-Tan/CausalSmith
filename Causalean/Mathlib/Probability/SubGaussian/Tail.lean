module
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Finite maxima of sub-Gaussian random variables

The tail of a finite pointwise maximum is bounded by the sum of the individual
sub-Gaussian tails, with the probability bound clipped at one.  The result also
covers an empty index set and makes no independence assumption.
-/

public section

noncomputable section

namespace Causalean.Mathlib.Probability.SubGaussian

open MeasureTheory ProbabilityTheory

/-- On [an underlying sample space](hyp:Ω) with [a probability measure](hyp:μ),
for [a finite family size](hyp:N), [real random variables](hyp:Z), and [positive
variance proxies](hyp:v) satisfying [their positivity condition](hyp:hv), if
[every coordinate has all exponential moments](hyp:hInt), [each coordinate
satisfies its sub-Gaussian moment bound](hyp:hmgf), and [the threshold and its
nonnegativity](hyp:t,ht), then [the probability that the largest absolute coordinate
exceeds the threshold is bounded by the clipped sum of two-sided Gaussian
tails](goal).

Proof strategy: obtain `HasSubgaussianMGF` for each coordinate from `hInt` and
`hmgf`; apply `HasSubgaussianMGF.measure_ge_le` to it and its negation.  Use
`measureReal_biUnion_finset_le` for the finite union.  Identify the finite
`sSup` with `Finset.univ.sup'` when `N > 0`, and handle `N = 0` separately. -/
theorem finite_max_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (Z : Fin N → Ω → ℝ) (v : Fin N → ℝ)
    (hv : ∀ k, 0 < v k)
    (hInt : ∀ k : Fin N, ∀ t : ℝ,
      Integrable (fun ω => Real.exp (t * Z k ω)) μ)
    (hmgf : ∀ k : Fin N, ∀ t : ℝ,
      mgf (Z k) μ t ≤ Real.exp (v k * t ^ 2 / 2))
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t < sSup ((fun k : Fin N => |Z k ω|) '' Set.univ)} ≤
      min 1 (∑ k : Fin N, 2 * Real.exp (-(t ^ 2) / (2 * v k))) := by
  classical
  by_cases hN : N = 0
  · subst N
    have hempty : {ω : Ω | t < 0} = ∅ := by
      ext ω
      simp [not_lt.mpr ht]
    simp [hempty]
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := by
    simpa using Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hN))
  have hevent :
      {ω | t < sSup ((fun k : Fin N => |Z k ω|) '' Set.univ)} =
        ⋃ k : Fin N, {ω | t < |Z k ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    have hsup : sSup ((fun k : Fin N => |Z k ω|) '' Set.univ) =
        (Finset.univ : Finset (Fin N)).sup' hne (fun k => |Z k ω|) := by
      simpa using (Finset.sup'_eq_csSup_image Finset.univ hne
        (fun k : Fin N => |Z k ω|)).symm
    rw [hsup]
    simp only [Finset.lt_sup'_iff hne, Finset.mem_univ, true_and]
  have hcoord (k : Fin N) :
      μ.real {ω | t < |Z k ω|} ≤ 2 * Real.exp (-(t ^ 2) / (2 * v k)) := by
    let c : NNReal := ⟨v k, le_of_lt (hv k)⟩
    have hc : (c : ℝ) = v k := rfl
    have hk : HasSubgaussianMGF (Z k) c μ := by
      refine ⟨hInt k, ?_⟩
      intro u
      simpa only [hc] using hmgf k u
    have hp := hk.measure_ge_le ht
    have hn := hk.neg.measure_ge_le ht
    have hs : {ω | t < |Z k ω|} ⊆
        {ω | t ≤ Z k ω} ∪ {ω | t ≤ -(Z k ω)} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
      rcases le_total 0 (Z k ω) with h | h
      · left
        simpa [abs_of_nonneg h] using le_of_lt hω
      · right
        simpa [abs_of_nonpos h] using le_of_lt hω
    calc
      μ.real {ω | t < |Z k ω|} ≤
          μ.real ({ω | t ≤ Z k ω} ∪ {ω | t ≤ -(Z k ω)}) :=
        measureReal_mono hs
      _ ≤ μ.real {ω | t ≤ Z k ω} + μ.real {ω | t ≤ -(Z k ω)} :=
        measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-(t ^ 2) / (2 * v k)) := by
        have hp' : μ.real {ω | t ≤ Z k ω} ≤
            Real.exp (-(t ^ 2) / (2 * v k)) := by simpa only [hc] using hp
        have hn' : μ.real {ω | t ≤ -(Z k ω)} ≤
            Real.exp (-(t ^ 2) / (2 * v k)) := by simpa only [hc, Pi.neg_apply] using hn
        linarith
  have hsum : μ.real {ω | t < sSup ((fun k : Fin N => |Z k ω|) '' Set.univ)} ≤
      ∑ k : Fin N, 2 * Real.exp (-(t ^ 2) / (2 * v k)) := by
    rw [hevent]
    exact (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun k _ => hcoord k)
  exact le_min (by simp) hsum

end Causalean.Mathlib.Probability.SubGaussian
