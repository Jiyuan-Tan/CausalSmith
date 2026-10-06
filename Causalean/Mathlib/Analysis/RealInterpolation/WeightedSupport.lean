module
public import Causalean.Mathlib.Analysis.RealInterpolation.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Sigma-finite support from finite weighted energy

A finite nonnegative integral controls the measure of positive superlevel sets.
Exhausting by these sets gives sigma-finite measure wherever the density is
positive almost everywhere. Applying this fact to the sum of two finite endpoint
energy densities gives sigma-finite support of an endpoint-sum function, even
when the ambient measure space is arbitrary.
-/

public section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace Causalean.Mathlib.Analysis.RealInterpolation

/-- [A measurable nonnegative density with finite integral](hyp:g,hg,hfin)
that is [positive almost everywhere on a measurable set](hyp:s,hs,hpos) gives
[sigma-finite measure on that set](goal) for [any ambient measure](hyp:μ).

Use superlevel sets g ≥ ofReal (1/(n+1)), whose measures are finite by
meas_ge_le_lintegral_div. Their union covers s except for a null set; add that
null set to the exhaustion. Do not assume μ is s-finite or globally sigma-finite.
The conclusion must follow from hfin, rather than from a strengthened hpos.
-/
theorem sigmaFinite_restrict_of_ae_pos_of_lintegral_lt_top
    {S : Type*} [MeasurableSpace S] (μ : Measure S) (s : Set S)
    (hs : MeasurableSet s) (g : S → ℝ≥0∞) (hg : Measurable g)
    (hpos : ∀ᵐ x ∂μ, x ∈ s → 0 < g x) (hfin : (∫⁻ x, g x ∂μ) < ⊤) :
    SigmaFinite (μ.restrict s) := by
  have hzero : (μ.restrict s) {x | g x = 0} = 0 := by
    have hpos' : ∀ᵐ x ∂μ.restrict s, 0 < g x := (ae_restrict_iff' hs).2 hpos
    simpa only [ae_iff, not_lt, nonpos_iff_eq_zero] using hpos'
  let c : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hc0 (n : ℕ) : c n ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hctop (n : ℕ) : c n ≠ ⊤ := by
    simp [c]
  have hfinite (n : ℕ) : (μ.restrict s) {x | c n ≤ g x} < ⊤ :=
    lt_of_le_of_lt ((Measure.restrict_apply_le _ _).trans
      (meas_ge_le_lintegral_div hg.aemeasurable (hc0 n) (hctop n)))
      (ENNReal.div_lt_top hfin.ne (hc0 n))
  apply sigmaFinite_iff.mpr
  refine ⟨{
    set := fun n => {x | c n ≤ g x} ∪ {x | g x = 0}
    set_mem := fun _ => mem_univ _
    finite := fun n => ?_
    spanning := ?_
  }⟩
  · exact lt_of_le_of_lt (measure_union_le _ _) (by simpa [hzero] using hfinite n)
  · apply eq_univ_of_forall
    intro x
    by_cases hx : g x = 0
    · exact mem_iUnion.mpr ⟨0, Or.inr hx⟩
    · obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx
      refine mem_iUnion.mpr ⟨n, Or.inl ?_⟩
      exact (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ n)).trans hn.le

/-- Let [μ be a measure](hyp:μ) and let [two measurable weights w0 and w1](hyp:w0,w1,hw0,hw1) be
[positive and finite μ-almost everywhere](hyp:hw). If [a complex function f, defined up to μ-null
sets, splits as a sum of two pieces whose weighted L² norms under w0 and w1 respectively are
finite](hyp:f,hf), then [μ restricted to the set where f is nonzero is σ-finite](goal).

Apply sigmaFinite_restrict_of_ae_pos_of_lintegral_lt_top to the sum of the two
weighted squared endpoint densities. Its integral is finite by wNorm_sq, and
where f is nonzero at least one endpoint summand is nonzero almost everywhere.
-/
theorem sigmaFinite_restrict_support_of_endpoint_sum {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (w0 w1 : S → ℝ≥0∞)
    (hw0 : Measurable w0) (hw1 : Measurable w1)
    (hw : ∀ᵐ x ∂μ, 0 < w0 x ∧ w0 x < ⊤ ∧ 0 < w1 x ∧ w1 x < ⊤)
    (f : S →ₘ[μ] ℂ)
    (hf : ∃ f0 f1 : S →ₘ[μ] ℂ, f = f0 + f1 ∧
      wNorm w0 μ f0 < ⊤ ∧ wNorm w1 μ f1 < ⊤) :
    SigmaFinite (μ.restrict {x | f x ≠ 0}) := by
  obtain ⟨f0, f1, hsum, hfin0, hfin1⟩ := hf
  let g0 : S → ℝ≥0∞ := fun x => w0 x * (‖f0 x‖₊ : ℝ≥0∞) ^ 2
  let g1 : S → ℝ≥0∞ := fun x => w1 x * (‖f1 x‖₊ : ℝ≥0∞) ^ 2
  have hg0 : Measurable g0 := hw0.mul (f0.measurable.enorm.pow_const 2)
  have hg1 : Measurable g1 := hw1.mul (f1.measurable.enorm.pow_const 2)
  apply sigmaFinite_restrict_of_ae_pos_of_lintegral_lt_top μ {x | f x ≠ 0}
    (f.measurable (measurableSet_singleton 0) |>.compl) (fun x => g0 x + g1 x)
    (hg0.add hg1)
  · filter_upwards [hw, AEEqFun.coeFn_add f0 f1] with x hx hadd
    intro hfx
    have hsumx : f x = f0 x + f1 x := by simpa only [hsum, Pi.add_apply] using hadd
    have hpos (w : ℝ≥0∞) (hwpos : 0 < w) (z : ℂ) (hz : z ≠ 0) :
        0 < w * (‖z‖₊ : ℝ≥0∞) ^ 2 := by
      have hnorm : 0 < ‖z‖₊ := nnnorm_pos.mpr hz
      positivity
    by_cases h0 : f0 x = 0
    · have h1 : f1 x ≠ 0 := by simpa [hsumx, h0] using hfx
      exact (hpos _ hx.2.2.1 _ h1).trans_le (le_add_left le_rfl)
    · exact (hpos _ hx.1 _ h0).trans_le (le_add_right le_rfl)
  · rw [lintegral_add_left hg0]
    change (∫⁻ x, w0 x * (‖f0 x‖₊ : ℝ≥0∞) ^ 2 ∂μ) +
      (∫⁻ x, w1 x * (‖f1 x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤
    rw [← wNorm_sq, ← wNorm_sq]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.pow_lt_top hfin0, ENNReal.pow_lt_top hfin1⟩

end Causalean.Mathlib.Analysis.RealInterpolation
