/- Cited Benaim--Hofbauer--Sorin differential-inclusion interfaces. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Stochastic approximation citation boundaries -/

open Set Filter MeasureTheory Topology intervalIntegral

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

/-- An absolutely-continuous integral solution of `x' ∈ F(x)`. -/
def DifferentialInclusionSolution {r : ℕ} (F : Vec r → Set (Vec r))
    (x : ℝ → Vec r) : Prop :=
  ∃ velocity : ℝ → Vec r,
    (∀ T ≥ 0, IntervalIntegrable velocity volume 0 T) ∧
    (∀ᵐ t ∂volume, 0 ≤ t → velocity t ∈ F (x t)) ∧
    ∀ a b, 0 ≤ a → a ≤ b → x b - x a = ∫ t in a..b, velocity t

/-- The BHS graph enlargement: both the base point and the selected velocity
may move by at most `delta`. -/
def graphEnlargement {r : ℕ} (F : Vec r → Set (Vec r))
    (delta : ℝ) (x : Vec r) : Set (Vec r) :=
  {y | ∃ x' y', dist x x' ≤ delta ∧ y' ∈ F x' ∧ dist y y' ≤ delta}

/-- BHS perturbed solution: its drift approaches the graph of `F`, and its
integrated perturbation vanishes on every bounded forward window. -/
def PerturbedSolution {r : ℕ} (F : Vec r → Set (Vec r))
    (x : ℝ → Vec r) : Prop :=
  ∃ drift noise : ℝ → Vec r, ∃ radius : ℝ → ℝ,
    (∀ T ≥ 0, IntervalIntegrable drift volume 0 T ∧
      IntervalIntegrable noise volume 0 T) ∧
    Tendsto radius atTop (nhds 0) ∧
    (∀ᵐ t ∂volume, 0 ≤ t → drift t ∈ graphEnlargement F (radius t) (x t)) ∧
    (∀ T > 0, Tendsto (fun t => ‖∫ s in t..(t + T), noise s‖) atTop (nhds 0)) ∧
    ∀ a b, 0 ≤ a → a ≤ b → x b - x a = ∫ t in a..b, drift t + noise t

def BoundedPath {r : ℕ} (x : ℝ → Vec r) : Prop :=
  ∃ C : ℝ, ∀ t ≥ 0, ‖x t‖ ≤ C

def DifferentialInclusionLimitSet {r : ℕ} (x : ℝ → Vec r) : Set (Vec r) :=
  {z | ∃ times : ℕ → ℝ, Tendsto times atTop atTop ∧
    Tendsto (fun n => x (times n)) atTop (nhds z)}

/-- The usual compact-window shadowing definition of an asymptotic
pseudotrajectory. -/
def AsymptoticPseudoTrajectory {r : ℕ} (F : Vec r → Set (Vec r))
    (x : ℝ → Vec r) : Prop :=
  ∀ T > 0, Tendsto (fun t => sInf {e : ℝ | 0 ≤ e ∧ ∃ y : ℝ → Vec r,
      DifferentialInclusionSolution F y ∧ y 0 = x t ∧
      ∀ s ∈ Icc 0 T, dist (x (t + s)) (y s) ≤ e}) atTop (nhds 0)

/-- An `(epsilon,T)` solution-chain inside `L`. -/
def InclusionChain {r : ℕ} (F : Vec r → Set (Vec r)) (L : Set (Vec r))
    (epsilon T : ℝ) (x y : Vec r) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ points : Fin (n + 1) → Vec r,
    points 0 = x ∧ points ⟨n, Nat.lt_succ_self n⟩ = y ∧
    ∀ i : Fin n, ∃ path : ℝ → Vec r,
      DifferentialInclusionSolution F path ∧ path 0 = points i.castSucc ∧
      (∀ t ∈ Icc 0 T, path t ∈ L) ∧ dist (path T) (points i.succ) < epsilon

def InternallyChainTransitive {r : ℕ} (F : Vec r → Set (Vec r))
    (L : Set (Vec r)) : Prop :=
  L.Nonempty ∧ IsCompact L ∧ ∀ x ∈ L, ∀ y ∈ L,
    ∀ epsilon > 0, ∀ T > 0, InclusionChain F L epsilon T x y

/-- A strict Lyapunov function off `Lambda`, nonincreasing on every solution. -/
def LyapunovFor {r : ℕ} (F : Vec r → Set (Vec r))
    (V : Vec r → ℝ) (Lambda : Set (Vec r)) : Prop :=
  ∀ x : Vec r, ∀ path : ℝ → Vec r, DifferentialInclusionSolution F path → path 0 = x →
    (∀ t > 0, V (path t) ≤ V x) ∧ (x ∉ Lambda → ∀ t > 0, V (path t) < V x)

/-- Michel Benaim, Josef Hofbauer, and Sylvain Sorin (2005), *Stochastic
Approximations and Differential Inclusions*, Hypothesis 1.1, Theorems 3.6 and
4.2, SIAM J. Control Optim. 44, pp. 329, 337, 343,
DOI 10.1137/S0363012904439301. -/
-- @node: lem:bhs-perturbed-limit-set
def BHSPerturbedLimitSetICT : Sort 0 :=
  ∀ (r : ℕ) (F : Vec r → Set (Vec r)),
    IsClosed {z : Vec r × Vec r | z.2 ∈ F z.1} →
    (∀ x, (F x).Nonempty ∧ IsCompact (F x) ∧ Convex ℝ (F x)) →
    (∃ C > 0, ∀ x y, y ∈ F x → ‖y‖ ≤ C * (1 + ‖x‖)) →
    ∀ y, PerturbedSolution F y → BoundedPath y →
      AsymptoticPseudoTrajectory F y ∧
        InternallyChainTransitive F (DifferentialInclusionLimitSet y)

/-- Michel Benaim, Josef Hofbauer, and Sylvain Sorin (2005), Proposition 3.27,
pp. 341--342, DOI 10.1137/S0363012904439301. -/
-- @node: lem:bhs-lyapunov-ict
def BHSLyapunovICT : Sort 0 :=
  ∀ (r : ℕ) (F : Vec r → Set (Vec r)) (V : Vec r → ℝ)
    (Lambda L : Set (Vec r)),
    IsClosed {z : Vec r × Vec r | z.2 ∈ F z.1} →
    (∀ x, (F x).Nonempty ∧ IsCompact (F x) ∧ Convex ℝ (F x)) →
    (∃ C > 0, ∀ x y, y ∈ F x → ‖y‖ ≤ C * (1 + ‖x‖)) →
    Continuous V → LyapunovFor F V Lambda →
    interior (V '' Lambda) = ∅ → InternallyChainTransitive F L →
      L ⊆ Lambda ∧ ∃ c, ∀ x ∈ L, V x = c

end

end CausalSmith.Experimentation.BanditRandomQV
