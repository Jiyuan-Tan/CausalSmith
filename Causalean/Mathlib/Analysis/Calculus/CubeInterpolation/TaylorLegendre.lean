module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.EuclideanRemainder
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.TensorLegendre

/-!
# Euclidean sorted Taylor to scaled tensor Legendre adapter

The headline combines independently derived multinomial grouping, the explicit
degree-two inverse Legendre transform, its uniform coefficient norm bound, and
the Euclidean within-cube Hölder remainder. The coefficient vector is explicit,
the polynomial is realized at every point, and the center value is exact.
All constants are quantified before the function, scale, and Hölder exponent.
The ambient cube can be the local cube itself or any larger cube; no global
extension, research-model premise, or assumed Taylor representation is used.
-/

@[expose] public section

open scoped BigOperators Topology
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The [Taylor-to-Legendre coefficient vector](goal) of [a function on its derivative
domain](hyp:S,u) of [degree m](hyp:m) at [a centre](hyp:a) and [side length h](hyp:h) is [the
Legendre coefficient transform, at scale h, of the function's sorted Taylor coefficients at the
centre](step:1). -/
def taylorLegendreCoefficients {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (m : ℕ)
    (a : EuclideanSpace ℝ (Fin d)) (h : ℝ) : MultiIndex d m → ℝ :=
  legendreCoefficients h (taylorCoefficient S u a)

/-- For [a function on its derivative domain](hyp:S,u), [a centre](hyp:a), and [a bound L](hyp:L)
that is [nonnegative](hyp:hL), if [every sorted coordinate partial of total order at most m is at
most L in absolute value at the centre](hyp:hderiv), then [every sorted Taylor coefficient of total
order at most m is at most L in absolute value](goal). -/
theorem taylorCoefficient_abs_le {d m : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (a : EuclideanSpace ℝ (Fin d)) (L : ℝ) (hL : 0 ≤ L)
    (hderiv : ∀ κ : MultiIndex d m, |coordinatePartial S u κ.1 a| ≤ L) :
    ∀ κ : MultiIndex d m, |taylorCoefficient S u a κ| ≤ L := by
  intro κ
  have hfac : 1 ≤ (multiFactorial κ.1 : ℝ) := by
    exact_mod_cast multiFactorial_pos κ.1
  unfold taylorCoefficient
  rw [abs_div, abs_of_nonneg (by linarith : 0 ≤ (multiFactorial κ.1 : ℝ))]
  exact (div_le_div_of_nonneg_right (hderiv κ) (by linarith)).trans
    (div_le_self hL hfac)

/-- For [a degree m at most two](hyp:hm), [a function on its derivative domain](hyp:S,u), [a centre
a and an evaluation point x](hyp:a,x), and [a side length h](hyp:h) that is [positive](hyp:hh),
[the scaled Legendre polynomial built from the Taylor-to-Legendre coefficients equals the degree-m
multi-index Taylor polynomial at x](goal). -/
theorem taylorLegendreCoefficients_realize {d m : ℕ} (hm : m ≤ 2)
    (S : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (a x : EuclideanSpace ℝ (Fin d)) (h : ℝ) (hh : 0 < h) :
    legendrePolynomial a h (taylorLegendreCoefficients S u m a h) x =
      multiindexTaylor S u m a x := by
  exact legendreCoefficients_realize hm a x h hh (taylorCoefficient S u a)

/-- In [a finite Euclidean dimension](hyp:d) at [a degree](hyp:m) [at most two](hyp:hm), [there is
a positive constant C with the following property. Take a cube of positive side length, a
nonnegative L, a positive exponent s at most one, and a function that is m times continuously
differentiable on the cube, whose sorted coordinate partials of total order at most m are bounded
by L on the cube, and whose sorted partials of total order exactly m change between any two cube
points by at most L times their distance to the power s. Then for every smaller cube of positive
side length h at most one half, contained in the big cube and centred at one of its interior
points, the Taylor-to-Legendre coefficient vector at that centre satisfies four things: its scaled
Legendre polynomial equals the multi-index Taylor polynomial everywhere; on the smaller cube the
function differs from it by at most C times L times h to the power m + s; the Euclidean norm of the
coefficient vector is at most C times L; and the polynomial takes the function's value at the
centre](goal). -/
theorem euclidean_multiindex_taylor_legendre_adapter (d m : ℕ) (hm : m ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b a : EuclideanSpace ℝ (Fin d))
      (H h L s : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ),
      0 < H → 0 < h → h ≤ 1 / 2 → 0 ≤ L → 0 < s → s ≤ 1 →
      ContDiffOn ℝ m u (centeredCube b H) →
      (∀ κ : MultiIndex d m, ∀ x ∈ centeredCube b H,
        |coordinatePartial (centeredCube b H) u κ.1 x| ≤ L) →
      (∀ κ : ExactIndex d m, ∀ x ∈ centeredCube b H, ∀ z ∈ centeredCube b H,
        |coordinatePartial (centeredCube b H) u κ.1 x -
          coordinatePartial (centeredCube b H) u κ.1 z| ≤ L * ‖x - z‖ ^ s) →
      a ∈ interior (centeredCube b H) → centeredCube a h ⊆ centeredCube b H →
      ∃ θ : MultiIndex d m → ℝ,
        θ = taylorLegendreCoefficients (centeredCube b H) u m a h ∧
        (∀ x, legendrePolynomial a h θ x = multiindexTaylor (centeredCube b H) u m a x) ∧
        (∀ x ∈ centeredCube a h,
          |u x - legendrePolynomial a h θ x| ≤ C * L * h ^ ((m : ℝ) + s)) ∧
        Real.sqrt (∑ κ, θ κ ^ 2) ≤ C * L ∧
        legendrePolynomial a h θ a = u a := by
  obtain ⟨Cr, hCr, hr⟩ := local_cube_multiindex_remainder d m
  obtain ⟨Cb, hCb, hb⟩ := legendreCoefficients_l2_bound d m hm
  refine ⟨max Cr Cb, lt_max_of_lt_left hCr, ?_⟩
  intro b a H h L s u hH hh hhhalf hL hs hs1 hu hderiv hmod ha hsub
  let θ := taylorLegendreCoefficients (centeredCube b H) u m a h
  have heq : ∀ x, legendrePolynomial a h θ x =
      multiindexTaylor (centeredCube b H) u m a x :=
    fun x => taylorLegendreCoefficients_realize hm _ u a x h hh
  refine ⟨θ, rfl, heq, ?_, ?_, ?_⟩
  · intro x hx
    rw [heq]
    exact (hr b a H h L s u hH hh hL hs hs1 hu hmod ha hsub x hx).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Cr Cb) hL)
        (Real.rpow_nonneg hh.le _))
  · have hc := taylorCoefficient_abs_le (centeredCube b H) u a L hL
      (fun κ => hderiv κ a (interior_subset ha))
    exact (hb h L (taylorCoefficient (centeredCube b H) u a)
      hh hhhalf hL hc).trans
      (mul_le_mul_of_nonneg_right (le_max_right Cr Cb) hL)
  · rw [heq, multiindexTaylor_center]

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
