module
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Layer-cake bridge for finite absolute maxima

This module converts a bound on the upper tails of a finite pointwise maximum
into a bound on its expectation.  The exponential-moment hypothesis ensures
integrability and almost-everywhere measurability of every coordinate.
-/

public section

noncomputable section

namespace Causalean.Mathlib.Probability.SubGaussian

open MeasureTheory ProbabilityTheory

/-- On [an underlying sample space](hyp:Ω) with [a probability measure](hyp:μ),
for [a finite family size](hyp:N), [a real-valued family](hyp:Z), and [a tail
majorant](hyp:g), if [every coordinate has all exponential moments](hyp:hInt),
[the majorant is integrable on the positive half-line](hyp:hg), and [it bounds
every upper tail of the maximum](hyp:hTail), then [the expected maximum is at
most the integral of that majorant](goal).

Proof strategy: derive integrability of each coordinate using
`HasSubgaussianMGF.integrable` or `integrable_of_mem_interior_integrableExpSet`,
then integrability of the finite maximum.  Use
`Integrable.integral_eq_integral_meas_lt` and monotonicity of the integral on
`Set.Ioi 0`; for `N = 0` both sides reduce to zero or a nonnegative bound. -/
theorem expected_max_le_tail_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (Z : Fin N → Ω → ℝ) (g : ℝ → ℝ)
    (hInt : ∀ k : Fin N, ∀ t : ℝ,
      Integrable (fun ω => Real.exp (t * Z k ω)) μ)
    (hg : IntegrableOn g (Set.Ioi (0 : ℝ)) volume)
    (hTail : ∀ t : ℝ, 0 ≤ t →
      μ.real {ω | t < sSup ((fun k : Fin N => |Z k ω|) '' Set.univ)} ≤ g t) :
    ∫ ω, sSup ((fun k : Fin N => |Z k ω|) '' Set.univ) ∂μ ≤
      ∫ t in Set.Ioi (0 : ℝ), g t := by
  have hcoord : ∀ k : Fin N, Integrable (fun ω => |Z k ω|) μ := by
    intro k
    simpa using (integrable_pow_abs_of_integrable_exp_mul (μ := μ) (X := Z k)
      (t := (1 : ℝ)) one_ne_zero (hInt k 1) (hInt k (-1)) 1)
  have htail_int : IntegrableOn
      (fun t : ℝ => μ.real {ω | t < sSup ((fun k : Fin N => |Z k ω|) '' Set.univ)})
      (Set.Ioi (0 : ℝ)) volume := by
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun t : ℝ => μ.real {ω | t < sSup ((fun k : Fin N => |Z k ω|) '' Set.univ)}) :=
      Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
    have hle : (fun t : ℝ => μ.real {ω | t < sSup ((fun k : Fin N => |Z k ω|) '' Set.univ)})
        ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] g := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hTail t ht.le
    have hmeas : Measurable
        (fun t : ℝ => μ.real {ω | t < sSup ((fun k : Fin N => |Z k ω|) '' Set.univ)}) := by
      apply Measurable.ennreal_toReal
      exact Antitone.measurable (fun _ _ hst =>
        measure_mono (fun _ h => lt_of_le_of_lt hst h))
    exact Integrable.mono_nonneg hg hmeas.aestronglyMeasurable hnonneg hle
  by_cases hN : N = 0
  · subst N
    have hzero : (fun ω => sSup ((fun k : Fin 0 => |Z k ω|) '' Set.univ)) =
        (fun _ => (0 : ℝ)) := by
      funext ω
      simp
    rw [hzero, integral_zero]
    exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      (ENNReal.toReal_nonneg).trans (hTail t ht.le)
  · have hU : (Finset.univ : Finset (Fin N)).Nonempty :=
      ⟨Classical.choice (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hN)), Finset.mem_univ _⟩
    have hsup : Integrable
        (fun ω => (Finset.univ : Finset (Fin N)).sup' hU (fun k => |Z k ω|)) μ := by
      have aux : ∀ (s : Finset (Fin N)) (hs : s.Nonempty),
          Integrable (fun ω => s.sup' hs (fun k => |Z k ω|)) μ := by
        intro s hs
        induction hs using Finset.Nonempty.cons_induction with
        | singleton k => simpa using hcoord k
        | cons k s hk hs ih =>
          convert (hcoord k).sup ih using 1
          funext ω
          exact Finset.sup'_cons hs (fun j => abs (Z j ω))
      exact aux _ hU
    have hmax : Integrable
        (fun ω => sSup ((fun k : Fin N => |Z k ω|) '' Set.univ)) μ := by
      convert hsup using 1
      funext ω
      rw [Finset.sup'_eq_csSup_image]
      simp
    have hnonneg : 0 ≤ᵐ[μ]
        (fun ω => sSup ((fun k : Fin N => |Z k ω|) '' Set.univ)) := by
      apply Filter.Eventually.of_forall
      intro ω
      change 0 ≤ sSup ((fun k : Fin N => |Z k ω|) '' Set.univ)
      let k : Fin N := Classical.choice (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hN))
      have hb : BddAbove ((fun k : Fin N => |Z k ω|) '' Set.univ) :=
        (Set.finite_univ.image _).bddAbove
      exact (abs_nonneg (Z k ω)).trans
        (le_csSup hb (Set.mem_image_of_mem _ (Set.mem_univ k)))
    rw [hmax.integral_eq_integral_meas_lt hnonneg]
    exact setIntegral_mono_on htail_int hg measurableSet_Ioi (fun t ht => hTail t ht.le)

end Causalean.Mathlib.Probability.SubGaussian
