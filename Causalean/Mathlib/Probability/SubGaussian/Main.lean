module
public import Causalean.Mathlib.Probability.SubGaussian.Envelope
public import Causalean.Mathlib.Probability.SubGaussian.LayerCake
public import Causalean.Mathlib.Probability.SubGaussian.Tail

/-!
# Ordered sub-Gaussian maximal envelope

The expected maximum of a finite ordered family is controlled by a logarithmic
envelope when its sub-Gaussian variance proxies decay polynomially.  The theorem
applies to every finite family, including the empty family, without independence.
-/

public section

noncomputable section

namespace Causalean.Mathlib.Probability.SubGaussian

open MeasureTheory ProbabilityTheory

/-- For [a decay exponent](hyp:α) with [strictly positive value](hyp:hα), [there
is a positive constant depending only on the exponent such that, on every probability
space, for every finite family `Z_0, …, Z_{N-1}` of real random variables and all
positive scales `a` and `b`, if every `exp(t·Z_k)` is integrable and the
moment-generating function of `Z_k` at every `t` is at most `exp(v_k·t²/2)` with variance
proxy `v_k = min(a², b²(k+1)^(-α))`, then the expected largest absolute value of the
family is at most the constant times `a·√(1 + max(0, log((b/a)^(2/α))))`](goal). No
independence is assumed, and the maximum over an empty family is zero.

Proof strategy: take `Kα` from `ordered_gaussian_tail_integral`.  Each variance
proxy `v k = min (a²) (b² * (k.val + 1)^(-α))` is positive.  Apply
`finite_max_tail_le` to this family, then `expected_max_le_tail_integral`
with the same clipped finite Gaussian sum as the deterministic majorant in
`ordered_gaussian_tail_integral`.  Its integrability and integral bound come
directly from that theorem; no separate argument is needed for `N = 0`. -/
theorem orderedSubGaussianMaximal (α : ℝ) (hα : 0 < α) :
    ∃ Kα : ℝ, 0 < Kα ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (N : ℕ) (Z : Fin N → Ω → ℝ) (a b : ℝ),
      0 < a → 0 < b →
      (∀ k : Fin N, ∀ t : ℝ,
        Integrable (fun ω => Real.exp (t * Z k ω)) μ) →
      (∀ k : Fin N, ∀ t : ℝ,
        mgf (Z k) μ t ≤
          Real.exp (min (a ^ 2)
            (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) * t ^ 2 / 2)) →
      ∫ ω, sSup ((fun k : Fin N => |Z k ω|) '' Set.univ) ∂μ ≤
        Kα * a * Real.sqrt
          (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
  obtain ⟨Kα, hKα, hbound⟩ := ordered_gaussian_tail_integral α hα
  refine ⟨Kα, hKα, ?_⟩
  intro Ω _ μ _ N Z a b ha hb hInt hmgf
  let v : Fin N → ℝ := fun k =>
    min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α))
  let g : ℝ → ℝ := fun t =>
    min 1 (∑ k : Fin N, 2 * Real.exp (-(t ^ 2) / (2 * v k)))
  have hv : ∀ k : Fin N, 0 < v k := by
    intro k
    dsimp [v]
    apply lt_min <;> positivity
  obtain ⟨hg, hgb⟩ := hbound N a b ha hb
  calc
    (∫ ω, sSup ((fun k : Fin N => |Z k ω|) '' Set.univ) ∂μ) ≤
        ∫ t in Set.Ioi (0 : ℝ), g t := by
      apply expected_max_le_tail_integral μ N Z g hInt
      · exact hg
      · intro t ht
        exact finite_max_tail_le μ N Z v hv hInt hmgf t ht
    _ ≤ Kα * a * Real.sqrt
          (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := hgb

end Causalean.Mathlib.Probability.SubGaussian
