module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.AffineGeometry
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.BoundaryFacts

/-!
# Intrinsic coordinate jets on finite cubes

Coordinate jets are evaluated with `iteratedFDerivWithin` on the specified closed set.
Consequently the data depend only on the restriction of a response to that set.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- [The intrinsic coordinate jet](goal) of order [j](hyp:j) of
[a response u](hyp:u) on [a set S](hyp:S), in [the coordinate directions
f(0), …, f(j − 1)](hyp:f) and at [a point x](hyp:x), is the order-j iterated
Fréchet derivative of u within S at x applied to the corresponding standard
basis vectors. -/
noncomputable def coordJetOn {d : ℕ} (S : Set (Fin d → ℝ)) (j : ℕ)
    (u : (Fin d → ℝ) → ℝ) (f : Fin j → Fin d) (x : Fin d → ℝ) : ℝ :=
  iteratedFDerivWithin ℝ j u S x (fun k => Pi.single (f k) (1 : ℝ))

/-- [A response u](hyp:u) [has a top-order intrinsic Hölder modulus](goal) on
[a set S](hyp:S), for [derivative order m](hyp:m), [exponent s and coefficient
L](hyp:s,L), when for every choice of m coordinate directions the order-m
intrinsic coordinate jets of u at any two points x, y of S differ in absolute
value by at most L·‖x − y‖^s. -/
def TopHolderOn {d : ℕ} (S : Set (Fin d → ℝ)) (m : ℕ) (s L : ℝ)
    (u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ f : Fin m → Fin d, ∀ x ∈ S, ∀ y ∈ S,
    |coordJetOn S m u f x - coordJetOn S m u f y| ≤ L * ‖x - y‖ ^ s

/-- [The intrinsic jet bound](goal) for [a response u](hyp:u) on [a set
S](hyp:S) through [order m](hyp:m) with [bound R](hyp:R) states that every
intrinsic coordinate jet of u of order at most m, in any coordinate directions,
has absolute value at most R at every point of S. -/
def DerivBoundOn {d : ℕ} (S : Set (Fin d → ℝ)) (m : ℕ) (R : ℝ)
    (u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ j ≤ m, ∀ f : Fin j → Fin d, ∀ x ∈ S, |coordJetOn S j u f x| ≤ R

/-- On [a set](hyp:S) in [dimension](hyp:d), a [response](hyp:u) with
[derivative order m](hyp:m), [Hölder exponent s](hyp:s), and [radius R](hyp:R)
lies in the intrinsic Hölder ball when it [is m times continuously differentiable within the
set](hyp:regularity), [all its intrinsic coordinate jets of order at most m are bounded by R in
absolute value on the set](hyp:derivBound), and [its order-m intrinsic coordinate jets have an
s-Hölder modulus with coefficient R on the set](hyp:modulus). -/
structure HolderBallOn {d : ℕ} (S : Set (Fin d → ℝ)) (m : ℕ)
    (s R : ℝ) (u : (Fin d → ℝ) → ℝ) : Prop where
  regularity : ContDiffOn ℝ m u S
  derivBound : DerivBoundOn S m R u
  modulus : TopHolderOn S m s R u

/-- [The intrinsic Hölder ball on the normalized closed cube](goal) in
[dimension d](hyp:d), for [derivative order m](hyp:m), [exponent s](hyp:s) and
[radius R](hyp:R), is the statement that [a response u](hyp:u) belongs to the
intrinsic Hölder ball with these parameters on the cube `[-1,1]^d`. -/
abbrev CubeHolderBall (d m : ℕ) (s R : ℝ) (u : (Fin d → ℝ) → ℝ) : Prop :=
  HolderBallOn (cube d) m s R u

/-- If [two responses u and v agree on a set S](hyp:h), then at [every point x
of S](hyp:hx) [their intrinsic coordinate jets on S coincide, for every order
and every choice of coordinate directions](goal). -/
theorem coordJetOn_congr {d j : ℕ} {S : Set (Fin d → ℝ)}
    {u v : (Fin d → ℝ) → ℝ} (h : Set.EqOn u v S)
    {f : Fin j → Fin d} {x : Fin d → ℝ} (hx : x ∈ S) :
    coordJetOn S j u f x = coordJetOn S j v f x := by
  unfold coordJetOn
  rw [iteratedFDerivWithin_congr h hx j]

/-- If [two responses u and v agree on a set S](hyp:h), then [u lies in the
intrinsic Hölder ball on S of a given order, exponent and radius exactly when v
does](goal). -/
theorem holderBallOn_congr {d m : ℕ} {S : Set (Fin d → ℝ)} {s R : ℝ}
    {u v : (Fin d → ℝ) → ℝ} (h : Set.EqOn u v S) :
    HolderBallOn S m s R u ↔ HolderBallOn S m s R v := by
  constructor
  · intro hu
    refine ⟨hu.regularity.congr (fun x hx => (h hx).symm), ?_, ?_⟩
    · intro j hj f x hx
      rw [← coordJetOn_congr h hx]
      exact hu.derivBound j hj f x hx
    · intro f x hx y hy
      rw [← coordJetOn_congr h hx, ← coordJetOn_congr h hy]
      exact hu.modulus f x hx y hy
  · intro hv
    refine ⟨hv.regularity.congr (fun x hx => h hx), ?_, ?_⟩
    · intro j hj f x hx
      rw [coordJetOn_congr h hx]
      exact hv.derivBound j hj f x hx
    · intro f x hx y hy
      rw [coordJetOn_congr h hx, coordJetOn_congr h hy]
      exact hv.modulus f x hx y hy

/-- If [a response u is m times continuously differentiable within the closed
cube](hyp:hu) and [j ≤ m](hyp:hj), then at [a point x of the open cube](hyp:hx)
[the order-j intrinsic coordinate jet of u on the closed cube equals the usual
ambient order-j coordinate partial derivative](goal). -/
theorem coordJetOn_cube_eq_ambient {d m j : ℕ}
    {u : (Fin d → ℝ) → ℝ} (hu : ContDiffOn ℝ m u (cube d))
    (hj : j ≤ m) {f : Fin j → Fin d} {x : Fin d → ℝ}
    (hx : x ∈ openCube d) :
    coordJetOn (cube d) j u f x = coordPartial j u f x := by
  have hsub : openCube d ⊆ cube d := by
    intro z hz i
    exact ⟨(hz i trivial).1.le, (hz i trivial).2.le⟩
  have hopen : IsOpen (openCube d) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hreg : ContDiffAt ℝ j u x :=
    (hu.mono hsub).contDiffAt (hopen.mem_nhds hx) |>.of_le (by exact_mod_cast hj)
  have hcube : cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
    ext z
    simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
      Pi.le_def, forall_and]
  have huniq : UniqueDiffOn ℝ (cube d) := by
    rw [hcube]
    exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))
  unfold coordJetOn coordPartial
  rw [iteratedFDerivWithin_eq_iteratedFDeriv huniq hreg (hsub hx)]

/-- If [a response u is m times continuously differentiable within the closed
cube](hyp:hu) and [j ≤ m](hyp:hj), then for [any coordinate directions
f](hyp:f) [the order-j intrinsic coordinate jet of u in those directions is
continuous on the closed cube](goal). -/
theorem continuousOn_coordJetOn_cube {d m j : ℕ}
    {u : (Fin d → ℝ) → ℝ} (hu : ContDiffOn ℝ m u (cube d))
    (hj : j ≤ m) (f : Fin j → Fin d) :
    ContinuousOn (coordJetOn (cube d) j u f) (cube d) := by
  have hcube : cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
    ext z
    simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
      Pi.le_def, forall_and]
  have huniq : UniqueDiffOn ℝ (cube d) := by
    rw [hcube]
    exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))
  have heval : Continuous
      (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ =>
        T (fun k => Pi.single (f k) (1 : ℝ))) := by
    fun_prop
  exact heval.comp_continuousOn
    (hu.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) huniq)

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
