module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Tensor
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Coordinate Hölder data on a fixed cube

This module defines coordinate partial derivatives and their fixed-cube bounds, using the
ambient iterated Fréchet derivative convention needed by the paper adapter.
-/

@[expose] public section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- [A finite dimension](hyp:d) determines [the closed normalized cube](goal), whose coordinates lie between minus one and one. -/
abbrev cube (d : ℕ) : Set (Fin d → ℝ) :=
  Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube d

/-- [A finite dimension](hyp:d) determines [the open normalized cube](goal), whose coordinates lie strictly between minus one and one. -/
def openCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun _ => Set.Ioo (-1 : ℝ) 1)

/-- [A finite dimension, derivative order, response, coordinate-direction sequence, and evaluation point](hyp:d,j,u,f,x) determine [the corresponding coordinate partial derivative](goal), given by [the order-j iterated derivative of the response at the point, taken in the whole space and applied to the standard basis vectors of the listed coordinate directions](step:1).

The derivative is the ambient one, not the derivative within a set: at a point where the
next-lower-order derivative is not differentiable in the whole space (for instance a boundary point
of a cube outside which the response is not smooth) it takes the conventional value zero. -/
noncomputable def coordPartial {d : ℕ} (j : ℕ) (u : (Fin d → ℝ) → ℝ)
    (f : Fin j → Fin d) (x : Fin d → ℝ) : ℝ :=
  iteratedFDeriv ℝ j u x (fun k => Pi.single (f k) (1 : ℝ))

/-- For [a dimension and derivative order](hyp:d,m), [a Hölder exponent s and a constant
L](hyp:s,L), and [a real function of d variables](hyp:u), this is [the top-order Hölder condition
on the normalized cube](goal): [every coordinate partial derivative of order m, taken in the whole
space, changes between any two points of the closed cube by at most L times their distance in the
coordinatewise-maximum norm raised to the power s](step:1).

Because the partials are ambient derivatives, the condition at boundary points of the cube depends
on the function's values outside the cube; the intrinsic (within-cube) version is the
cube-extension top-order Hölder condition. -/
def TopHolder (d m : ℕ) (s L : ℝ) (u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ f : Fin m → Fin d, ∀ x ∈ cube d, ∀ y ∈ cube d,
    |coordPartial m u f x - coordPartial m u f y| ≤ L * ‖x - y‖ ^ s

/-- For [a dimension and derivative order](hyp:d,m), [a radius R](hyp:R), and [a real function of d
variables](hyp:u), this is [the uniform derivative bound on the normalized cube](goal): [every
coordinate partial derivative of every order from zero up to m, taken in the whole space, is at
most R in absolute value at every point of the closed cube](step:1).

Order zero is the function itself, so the bound includes the function's values. -/
def DerivBound (d m : ℕ) (R : ℝ) (u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ j ≤ m, ∀ f : Fin j → Fin d, ∀ x ∈ cube d, |coordPartial j u f x| ≤ R

/-- [A finite dimension, derivative order, Hölder exponent, radius, and response](hyp:d,m,s,R,u) specify a fixed-cube Hölder ball through [m-times continuous differentiability on the closed normalized cube](hyp:regularity), [the bound R on every coordinate partial of order at most m at every point of the cube](hyp:derivBound), and [the top-order Hölder condition with exponent s and the same constant R on the order-m coordinate partials](hyp:modulus).

The coordinate partials in the two bounds are ambient derivatives (taken in the whole space), so
at boundary points of the cube membership depends on the response outside the cube; the intrinsic
within-cube ball is the cube-extension Hölder ball. On the cube the two balls contain the same
functions up to a constant in the radius: an ambient-ball member lies in the within-cube ball
with the same radius, and, for Hölder exponents in (0, 1], every within-cube-ball member agrees
on the cube with an ambient-ball member whose radius is larger by a factor depending only on the
dimension, order and exponent (`CubeExtension.cubeHolderBall_of_holderBall`,
`CubeExtension.exists_holderBall_extension`). -/
structure HolderBall (d m : ℕ) (s R : ℝ) (u : (Fin d → ℝ) → ℝ) : Prop where
  regularity : ContDiffOn ℝ m u (cube d)
  derivBound : DerivBound d m R u
  modulus : TopHolder d m s R u

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
