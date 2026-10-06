module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal.AlternatingAngles
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal.ResidualSquareIdentities

/-!
# Bounded oscillation of the reciprocal Chebyshev residual

The sharp residual bound and `m+2` alternating equality points are the
analytic core of the reciprocal best approximation formula.  These lemmas
state the two independent conclusions needed by the final alternation proof.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal

/-- [Positive interval endpoints](hyp:a,b,ha,hab), an [interval point](hyp:z,hz),
and a [degree bound](hyp:m) imply [the sharp absolute bound for the shifted
residual polynomial](goal). -/
theorem reciprocalResidualPoly_bound {a b z : ℝ}
    (ha : 0 < a) (hab : a < b) (hz : z ∈ Set.Icc a b) (m : ℕ) :
    |(reciprocalResidualPoly a b m).eval
      (intervalShape a b - 2 * z / (b - a))| ≤
      2 * (intervalShape a b -
        (intervalShape a b - 2 * z / (b - a))) := by
  -- Set `t = v - 2*z/(b-a)`.  `a ≤ z ≤ b` gives `-1 ≤ t ≤ 1`:
  -- expand `intervalShape`, clear the positive denominator `b-a`, and use
  -- `linarith`.  Obtain `θ ∈ Icc 0 Real.pi` with `cos θ = t` from
  -- `Real.surjOn_cos`.  The sine-square identity gives
  -- `R(t) ≤ 2*(v-t)`; the cosine-square identity gives its negative lower
  -- bound.  Both use `0 < 2/ρ` from `intervalDecay_mem_Ioo`.  Finish with
  -- `abs_le.mpr`.  Mathlib also has `Real.cos_mem_Icc` for the reverse map.
  have hd : 0 < b - a := sub_pos.mpr hab
  have ht : intervalShape a b - 2 * z / (b - a) ∈ Set.Icc (-1 : ℝ) 1 := by
    have heq : intervalShape a b - 2 * z / (b - a) =
        (a + b - 2 * z) / (b - a) := by
      unfold intervalShape
      ring
    rw [heq]
    constructor
    · apply (le_div_iff₀ hd).2
      nlinarith [hz.2]
    · apply (div_le_iff₀ hd).2
      nlinarith [hz.1]
  obtain ⟨θ, _, hθ⟩ := Real.surjOn_cos ht
  have hρ : 0 ≤ 2 / intervalDecay a b :=
    le_of_lt (div_pos (by norm_num) (intervalDecay_mem_Ioo ha hab).1)
  have hs := reciprocalResidualPoly_sin_square ha hab m θ
  have hc := reciprocalResidualPoly_cos_square ha hab m θ
  rw [hθ] at hs hc
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg
    (Real.sin (((m : ℝ) + 1) * θ / 2) -
      intervalDecay a b * Real.sin (((m : ℝ) - 1) * θ / 2)),
    sq_nonneg
    (Real.cos (((m : ℝ) + 1) * θ / 2) -
      intervalDecay a b * Real.cos (((m : ℝ) - 1) * θ / 2))]

/-- [Positive interval endpoints](hyp:a,b,ha,hab) and a [degree bound](hyp:m)
imply [the existence of ordered interval points where the shifted residual
attains alternating sharp values](goal). -/
theorem reciprocalResidualPoly_alternating_nodes {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ) :
    ∃ nodes : Fin (m + 2) → ℝ,
      StrictMono nodes ∧
      (∀ i, nodes i ∈ Set.Icc a b) ∧
      (∀ i,
        (reciprocalResidualPoly a b m).eval
          (intervalShape a b - 2 * nodes i / (b - a)) =
          (-1 : ℝ) ^ (i : ℕ) *
            (2 * (intervalShape a b -
              (intervalShape a b - 2 * nodes i / (b - a))))) := by
  -- Use `exists_reciprocalAlternatingAngles` with `ρ = intervalDecay a b`.
  -- Set `nodes i = (a+b)/2 - (b-a)*cos (angles i)/2`.  By
  -- `Real.strictAntiOn_cos`, the cosine sequence is strictly decreasing,
  -- and the positive factor `b-a` makes the node sequence strictly
  -- increasing. `Real.cos_mem_Icc` gives interval membership after clearing
  -- denominators.  Show `v - 2*nodes i/(b-a) = cos (angles i)` algebraically.
  -- At even `i`, the angle lemma kills the sine square, so the residual is
  -- `+2*(v-cos θ)`; at odd `i`, it kills the cosine square, giving the
  -- negative value. `(-1 : ℝ)^i` is `1` or `-1` by parity.
  obtain ⟨angles, hmono, hmem, hzero⟩ :=
    exists_reciprocalAlternatingAngles (intervalDecay_mem_Ioo ha hab) m
  let nodes : Fin (m + 2) → ℝ := fun i =>
    (a + b - (b - a) * Real.cos (angles i)) / 2
  have hd : 0 < b - a := sub_pos.mpr hab
  have hshift (i : Fin (m + 2)) :
      intervalShape a b - 2 * nodes i / (b - a) = Real.cos (angles i) := by
    dsimp [nodes, intervalShape]
    field_simp
    ring
  refine ⟨nodes, ?_, ?_, ?_⟩
  · intro i j hij
    have hc : Real.cos (angles j) < Real.cos (angles i) :=
      Real.strictAntiOn_cos (hmem i) (hmem j) (hmono hij)
    dsimp [nodes]
    have hp := mul_lt_mul_of_pos_left hc hd
    linarith
  · intro i
    have hc := Real.cos_mem_Icc (angles i)
    dsimp [nodes]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hc.1 hd.le,
      mul_le_mul_of_nonneg_left hc.2 hd.le]
  · intro i
    rw [hshift]
    by_cases he : Even (i : ℕ)
    · have hz := hzero i
      simp only [if_pos he] at hz
      rw [reciprocalResidualPoly_sin_square ha hab m (angles i), hz]
      simp [Even.neg_one_pow he]
    · have hz := hzero i
      simp only [if_neg he] at hz
      rw [reciprocalResidualPoly_cos_square ha hab m (angles i), hz]
      have ho : Odd (i : ℕ) := Nat.not_even_iff_odd.mp he
      simp [Odd.neg_one_pow ho]

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal
