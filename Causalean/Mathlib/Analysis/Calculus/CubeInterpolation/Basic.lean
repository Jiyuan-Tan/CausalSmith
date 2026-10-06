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

/-- [A finite dimension, derivative order, response, coordinate-direction sequence, and evaluation point](hyp:d,j,u,f,x) determine [the corresponding coordinate partial derivative](goal), given by [the iterated derivative in those coordinate directions](step:1). -/
noncomputable def coordPartial {d : ℕ} (j : ℕ) (u : (Fin d → ℝ) → ℝ)
    (f : Fin j → Fin d) (x : Fin d → ℝ) : ℝ :=
  iteratedFDeriv ℝ j u x (fun k => Pi.single (f k) (1 : ℝ))

/-- For [a dimension and derivative order](hyp:d,m), [a Hölder exponent s and a constant
L](hyp:s,L), and [a real function of d variables](hyp:u), this is [the top-order Hölder condition
on the normalized cube](goal): [every coordinate partial derivative of order m changes between any
two points of the cube by at most L times their distance raised to the power s](step:1). -/
def TopHolder (d m : ℕ) (s L : ℝ) (u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ f : Fin m → Fin d, ∀ x ∈ cube d, ∀ y ∈ cube d,
    |coordPartial m u f x - coordPartial m u f y| ≤ L * ‖x - y‖ ^ s

/-- For [a dimension and derivative order](hyp:d,m), [a radius R](hyp:R), and [a real function of d
variables](hyp:u), this is [the uniform derivative bound on the normalized cube](goal): [every
coordinate partial derivative of every order up to m is at most R in absolute value at every point
of the cube](step:1). -/
def DerivBound (d m : ℕ) (R : ℝ) (u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ j ≤ m, ∀ f : Fin j → Fin d, ∀ x ∈ cube d, |coordPartial j u f x| ≤ R

/-- [A finite dimension, derivative order, Hölder exponent, radius, and response](hyp:d,m,s,R,u) specify a fixed-cube Hölder ball through [regularity on the normalized cube](hyp:regularity), [a uniform coordinate-derivative bound](hyp:derivBound), and [a top-order Hölder modulus](hyp:modulus). -/
structure HolderBall (d m : ℕ) (s R : ℝ) (u : (Fin d → ℝ) → ℝ) : Prop where
  regularity : ContDiffOn ℝ m u (cube d)
  derivBound : DerivBound d m R u
  modulus : TopHolder d m s R u

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
