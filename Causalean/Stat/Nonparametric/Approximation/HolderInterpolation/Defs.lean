/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Generic multivariate Hölder ball and moment-cancelling product kernel — definitions

This module fixes the *generic* (estimand-agnostic) vocabulary for the Tsybakov
nonparametric-minimax lower-bound primitive
`holder_point_l1_interpolation`: for a function in a multivariate Hölder ball, a
pointwise value forces a local `L¹` mass lower bound via a moment-cancelling
kernel.

The definitions are estimand-agnostic: they apply to any regression or response
function and carry no dependency on a causal-law or treatment-effect type. This
makes the primitive reusable in every Hölder-class two-point or Assouad lower bound.

* `supBall x0 r` — the sup-norm `r`-neighbourhood (closed cube) around `x0`, together
  with its basic geometry/measure API (`supBall_eq_pi`, `isCompact_supBall`,
  `measurableSet_supBall`, `mem_supBall_self`, `volume_supBall`).
* `HolderBallStd f γ M S` — the standard `⌈γ⌉-1`-convention multivariate Hölder
  ball of order `γ`, radius `M`, on `S`.
* `prodKernel k d` — the tensorized product kernel `u ↦ ∏ᵢ k (u i)`.
* `mem_cube`, `isCompact_cube` — the same two facts for the axis-aligned box
  `[a,b]^d`, the other cube shape that shows up in Hölder-class lower bounds.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators

/-- For [a nonnegative integer dimension](hyp:d), [a centre in that-dimensional real
space](hyp:x0), and [a real radius](hyp:r), the [closed coordinatewise neighbourhood](goal) is
the set of points whose every coordinate differs from the corresponding coordinate of the centre
by at most the radius. -/
def supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, |x i - x0 i| ≤ r}

/-- A closed sup-norm ball — the axis-aligned cube of half-width `r` centred at a point — is
exactly the product of the coordinate intervals of radius `r` around the centre's coordinates. -/
lemma supBall_eq_pi {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) :
    supBall x0 r = Set.univ.pi (fun i => Set.Icc (x0 i - r) (x0 i + r)) := by
  ext x
  simp only [supBall, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
  refine ⟨fun h i => ?_, fun h i => ?_⟩
  · have := (abs_le).mp (h i); constructor <;> linarith [this.1, this.2]
  · rw [abs_le]; have := h i; constructor <;> linarith [this.1, this.2]

/-- [A closed sup-norm ball — the axis-aligned cube, or box, of half-width `r` centred at a
point `x0` in `d`-dimensional space](hyp:d,x0,r) — [is compact](goal), being a finite
product of closed bounded intervals. -/
lemma isCompact_supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) :
    IsCompact (supBall x0 r) := by
  rw [supBall_eq_pi]; exact isCompact_univ_pi (fun _ => isCompact_Icc)

/-- A closed sup-norm ball (an axis-aligned cube, or box) is a measurable set. -/
lemma measurableSet_supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) :
    MeasurableSet (supBall x0 r) := by
  rw [supBall_eq_pi]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-- A closed sup-norm ball (axis-aligned cube) of nonnegative half-width contains its own
centre. -/
lemma mem_supBall_self {d : ℕ} (x0 : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    x0 ∈ supBall x0 r := by
  intro i; simp only [sub_self, abs_zero]; exact hr

/-- [The Lebesgue volume of a closed sup-norm ball — the axis-aligned cube of side `2r`
centred at `x0` in `d` dimensions](hyp:d,x0,r) — [equals the `d`-th power of the side
length, `(2r)^d`](goal). No sign restriction on `r` is needed: a negative half-width
gives an empty cube and a zero right-hand side. -/
lemma volume_supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) :
    volume (supBall x0 r) = ENNReal.ofReal (2 * r) ^ d := by
  rw [supBall_eq_pi, Set.pi_univ_Icc, Real.volume_Icc_pi]
  simp_rw [show ∀ i : Fin d, x0 i + r - (x0 i - r) = 2 * r from fun i => by ring]
  simp

/-- Membership in an axis-aligned box: a point lies in it exactly when each of
its coordinates lies between `a` and `b`. -/
lemma mem_cube {ι : Type*} {a b : ℝ} {x : ι → ℝ} :
    x ∈ Set.univ.pi (fun _ : ι => Set.Icc a b) ↔ ∀ i, a ≤ x i ∧ x i ≤ b := by
  simp only [Set.mem_univ_pi, Set.mem_Icc]

/-- An axis-aligned box over a finite index type is compact: it is a finite product of closed
bounded intervals. -/
lemma isCompact_cube {ι : Type*} [Finite ι] (a b : ℝ) :
    IsCompact (Set.univ.pi (fun _ : ι => Set.Icc a b)) := by
  letI := Fintype.ofFinite ι
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

/-- For [a nonnegative integer dimension](hyp:d), [a real-valued function on that-dimensional
real space](hyp:f), [a real smoothness order](hyp:order), [a real radius](hyp:M), and [a region
of that space](hyp:S), the [standard multivariate Hölder ball condition](goal) requires that (1)
[the function has continuous derivatives through order $\lceil\mathrm{order}\rceil-1$ on the
region](step:1), (2) [every derivative of order at most $\lceil\mathrm{order}\rceil-1$ has norm at
most the radius there](step:2), and (3) [the derivative of order
$\lceil\mathrm{order}\rceil-1$ changes between any two points in the region by at most the radius
times their distance to the power $\mathrm{order}-(\lceil\mathrm{order}\rceil-1)$](step:3). -/
def HolderBallStd {d : ℕ} (f : (Fin d → ℝ) → ℝ) (order M : ℝ)
    (S : Set (Fin d → ℝ)) : Prop :=
  ContDiffOn ℝ (⌈order⌉₊ - 1) f S ∧
    (∀ j : ℕ, j ≤ ⌈order⌉₊ - 1 → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ M) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ (⌈order⌉₊ - 1) f x - iteratedFDeriv ℝ (⌈order⌉₊ - 1) f y‖
        ≤ M * ‖x - y‖ ^ (order - ((⌈order⌉₊ - 1 : ℕ) : ℝ)))

/-- For [a one-dimensional real-valued kernel](hyp:k) and [a nonnegative integer
dimension](hyp:d), the [multivariate product kernel](goal) assigns to each point the product of
the one-dimensional kernel evaluated at all of its coordinates. -/
def prodKernel (k : ℝ → ℝ) (d : ℕ) : (Fin d → ℝ) → ℝ :=
  fun u => ∏ i : Fin d, k (u i)

end Causalean.Stat.Nonparametric
