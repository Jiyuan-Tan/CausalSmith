module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.TargetSeparationTransport
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Quantitative target separation for the lower-bound directions -/

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The positive mass of the fixed endpoint bump. -/
@[no_expose]
noncomputable def endpointBumpMass (c : ClassConstants) (cut : CutoffData c) : ℝ :=
  ∫ x in (0 : ℝ)..1, cut.bump x

lemma endpointBumpMass_pos (c : ClassConstants) (cut : CutoffData c) :
    0 < endpointBumpMass c cut := by
  unfold endpointBumpMass
  apply intervalIntegral.integral_pos (by norm_num)
  · exact cut.bump_smooth.continuous.continuousOn
  · intro x hx
    exact cut.bump_nonneg x
  · rcases cut.bump_nonzero with ⟨x, hx⟩
    have hs := cut.bump_support x hx.ne'
    exact ⟨x, ⟨hs.1.le, hs.2.le⟩, hx⟩

/-- Rescaling and reflecting the endpoint bump over its terminal support
multiplies its fixed mass by the bandwidth. -/
lemma integral_rescaled_endpointBump
    (c : ClassConstants) (cut : CutoffData c) {h : ℝ} (hh : 0 < h) :
    (∫ t in (1 - h)..1, cut.bump ((1 - t) / h)) =
      h * endpointBumpMass c cut := by
  let f : ℝ → ℝ := fun t => (1 - t) / h
  let f' : ℝ → ℝ := fun _ => -1 / h
  have hderiv : ∀ t ∈ Set.uIcc (1 - h) (1 : ℝ), HasDerivAt f (f' t) t := by
    intro t ht
    simpa [f, f', one_div] using
      ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).div_const h
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := 1 - h) (b := (1 : ℝ)) (g := cut.bump) hderiv
    continuousOn_const cut.bump_smooth.continuous
  have hf0 : f (1 - h) = 1 := by dsimp [f]; rw [sub_sub_cancel]; exact div_self hh.ne'
  have hf1 : f 1 = 0 := by simp [f]
  rw [hf0, hf1] at hsub
  have hfactor :
      (∫ t in (1 - h)..1, (cut.bump ∘ f) t * f' t) =
        (-(1 / h)) * (∫ t in (1 - h)..1, cut.bump ((1 - t) / h)) := by
    calc
      _ = ∫ t in (1 - h)..1,
          (-(1 / h)) * cut.bump ((1 - t) / h) := by
        apply intervalIntegral.integral_congr
        intro t ht
        simp only [f, f', Function.comp_apply]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hfactor] at hsub
  have hmasssym : (∫ x in (1 : ℝ)..0, cut.bump x) =
      -endpointBumpMass c cut := by
    rw [intervalIntegral.integral_symm]
    rfl
  rw [hmasssym] at hsub
  have hhne : h ≠ 0 := hh.ne'
  have hinv : (1 / h) *
      (∫ t in (1 - h)..1, cut.bump ((1 - t) / h)) =
        endpointBumpMass c cut := by
    linarith [hsub]
  unfold endpointBumpMass
  calc
    (∫ t in (1 - h)..1, cut.bump ((1 - t) / h)) =
        h * ((1 / h) * (∫ t in (1 - h)..1, cut.bump ((1 - t) / h))) := by
          field_simp
    _ = h * (∫ x in (0 : ℝ)..1, cut.bump x) := by
      rw [hinv]
      rfl

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
