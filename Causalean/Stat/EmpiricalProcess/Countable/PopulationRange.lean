module
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Bounded population versions from set-integral tests

A measurable real version need not be bounded at every point. Testing its
integral on every measurable set against fixed lower and upper constants
forces an almost-everywhere range bound and integrability on finite measures.
No integrability of the tested version is assumed. This bridge allows
threshold measurability to use conditional-version primitives without
strengthening them to pointwise positivity or boundedness on null sets.
-/

public section

open MeasureTheory Set
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- Under [a finite measure μ](hyp:μ), if [a real function f](hyp:f) is
[measurable](hyp:hf), [two constants satisfy l ≤ u](hyp:l,u,hlu), and [on
every measurable set the integral of f lies between l and u times the
set's mass](hyp:htest), then [f lies between l and u almost everywhere and
is integrable](goal).

No integrability of f is assumed.
-/
theorem tested_integrals_ae_range {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (l u : ℝ) (hlu : l ≤ u)
    (htest : ∀ S : Set Ω, MeasurableSet S →
      l * μ.real S ≤ (∫ x in S, f x ∂μ) ∧
        (∫ x in S, f x ∂μ) ≤ u * μ.real S) :
    (∀ᵐ x ∂μ, f x ∈ Icc l u) ∧ Integrable f μ := by
  -- Work on S_N={x | |f x|≤N}: f is integrable on S_N by of_bound.
  -- Apply Mathlib ae_le_of_forall_setIntegral_le to the restricted law,
  -- using htest on intersections, to bound f between l and u there.
  -- The countable S_N cover all points since f is real-valued. Transfer
  -- these AE inequalities to μ and conclude Integrable.of_bound with
  -- max |l| |u|. Assuming f integrable at the start would hide the bridge.
  let S : ℕ → Set Ω := fun N => {x | |f x| ≤ (N : ℝ)}
  have hS (N : ℕ) : MeasurableSet (S N) := by
    simpa only [Real.norm_eq_abs] using (measurableSet_le hf.norm
      (measurable_const : Measurable (fun _ : Ω => (N : ℝ))))
  have hlocal (N : ℕ) : ∀ᵐ x ∂μ.restrict (S N), f x ∈ Icc l u := by
    have hfi : Integrable f (μ.restrict (S N)) :=
      Integrable.of_bound hf.aestronglyMeasurable.restrict (N : ℝ)
        ((ae_restrict_mem (hS N)).mono fun x hx => by
          simpa only [Real.norm_eq_abs, S, Set.mem_ofPred_eq] using hx)
    have hlo : (fun _ : Ω => l) ≤ᵐ[μ.restrict (S N)] f := by
      apply ae_le_of_forall_setIntegral_le (integrable_const l) hfi
      intro t ht _
      simpa [Measure.restrict_restrict ht, integral_const, Measure.real,
        Measure.restrict_apply ht, smul_eq_mul, mul_comm] using
        (htest (t ∩ S N) (ht.inter (hS N))).1
    have hup : f ≤ᵐ[μ.restrict (S N)] (fun _ : Ω => u) := by
      apply ae_le_of_forall_setIntegral_le hfi (integrable_const u)
      intro t ht _
      simpa [Measure.restrict_restrict ht, integral_const, Measure.real,
        Measure.restrict_apply ht, smul_eq_mul, mul_comm] using
        (htest (t ∩ S N) (ht.inter (hS N))).2
    exact hlo.and hup
  have hrange : ∀ᵐ x ∂μ, f x ∈ Icc l u := by
    have hall : ∀ᵐ x ∂μ, ∀ N : ℕ, x ∈ S N → f x ∈ Icc l u :=
      (ae_all_iff).2 fun N => (ae_restrict_iff' (hS N)).1 (hlocal N)
    filter_upwards [hall] with x hx
    obtain ⟨N, hN⟩ := exists_nat_ge |f x|
    exact hx N hN
  refine ⟨hrange, Integrable.of_bound hf.aestronglyMeasurable (max |l| |u|) ?_⟩
  filter_upwards [hrange] with x hx
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact (neg_le_neg (le_max_left |l| |u|)).trans ((neg_abs_le l).trans hx.1)
  · exact hx.2.trans ((le_abs_self u).trans (le_max_right |l| |u|))

end Causalean.Stat.EmpiricalProcess.Countable
