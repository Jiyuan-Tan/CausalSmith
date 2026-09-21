/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Design ±1 exactness boundary (two-block homophily SDP): shared core

Stage-2 scaffold for `exp_design_pm1_exactness_boundary_v1` (v1).

This file carries the two environment worlds, the assumption-atom `def`s, the
class structures, and the construction `def`s shared across the four theorems and
the helper lemmas. Each emitted top-level declaration carries its `@node` tag.

## Causalean substrate survey

| Submodule | Decision | Reason |
| --- | --- | --- |
| `Causalean.Experimentation.DesignBased.DesignCore` (`FiniteDesign`/`E`/`Pr`) | reuse (S1) | the finite sign-assignment law layer is exactly a PMF on a finite space with finite-sum moments; instantiated at `Ω = Fin (2*m) → Bool`. |
| `Causalean.Experimentation.DesignBased.{Exposure,PotentialOutcome}` | bypass-justified | S2 (matrices/elliptope/objective) is purely algebraic over `ℝ^{n×n}`; `lean_local_search {elliptope, assignmentCovariance, Laplacian, Frobenius}` returned none, so the geometry world is a Mathlib-matrix bypass. |

No new typeclasses or cluster-scale structures are introduced.
-/

module
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Causalean.Stat.FiniteDesign.DesignCore

/-! ## Environment S2 — reduced spectral-coordinate world (real objective geometry)

All certificates live on the reduced triangle `T_m` in the spectral coordinates
`(x,y,z)` produced by `lem:block-spectral-coordinates`; the objective there is the
linear-plus-weighted-Frobenius form `phi`. These are the shared reduced primitives.
-/

@[expose] public section

namespace CausalSmith.Experimentation.DesignPm1

open Causalean.Experimentation.DesignBased
open scoped BigOperators

-- @env: S2
/-- Reduced multiplicity weight `q = 2(m-1)` (block-contrast eigenspace multiplicity;
a derived constant, NOT the core tradeoff ratio `r`). -/
def qParam (m : ℕ) : ℝ := 2 * ((m : ℝ) - 1)

/-- The reduced triangle `T_m = {x,y,z ≥ 0 : q x + y + z = 2m}`.
@realizes X(u,v)(reduced coordinates x,y,z on T_m) -/
def InReducedTriangle (m : ℕ) (x y z : ℝ) : Prop :=
  0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ qParam m * x + y + z = 2 * (m : ℝ)

/-- The reduced objective `φ(x,y,z) = c_x x + c_y y + c_z z + κ √(q x² + y² + z²)`.
@realizes F_{r,kappa}(X)(reduced form c_x x + c_y y + c_z z + κ‖·‖)
@realizes kappa(carrier ℝ; robustness weight on the Frobenius term κ√(q x²+y²+z²); range
[0,∞) pinned by the `0 ≤ kappa` premises threaded through the consuming theorems/lemmas) -/
noncomputable def reducedObjective (q cx cy cz kappa x y z : ℝ) : ℝ :=
  cx * x + cy * y + cz * z + kappa * Real.sqrt (q * x ^ 2 + y ^ 2 + z ^ 2)

/-- Reduced linear coefficient on `x`: `c_x = q((a+b) + r/(a+b))`.
@realizes F_{r,kappa}(X)(c_x = q((a+b)+r/(a+b)))
@realizes r(carrier ℝ; tradeoff ratio entering c_x via the r/(a+b) term)
@realizes a(within-block weight in a+b and r/(a+b))
@realizes b(cross-block weight in a+b and r/(a+b)) -/
noncomputable def cX (m : ℕ) (a b r : ℝ) : ℝ := qParam m * ((a + b) + r / (a + b))

/-- Reduced linear coefficient on `y`: `c_y = 2b + r/(2b)`.
@realizes F_{r,kappa}(X)(c_y = 2b + r/(2b))
@realizes r(carrier ℝ; tradeoff ratio entering c_y via the r/(2b) term)
@realizes b(cross-block weight in 2b and r/(2b)) -/
noncomputable def cY (b r : ℝ) : ℝ := 2 * b + r / (2 * b)

/-- Reduced linear coefficient on `z`: `c_z = 2m`.
@realizes F_{r,kappa}(X)(c_z = 2m) -/
def cZ (m : ℕ) : ℝ := 2 * (m : ℝ)

/-- Parity feasibility threshold `d_m = 0` (m even), `2/m` (m odd). -/
noncomputable def parityThreshold (m : ℕ) : ℝ := if Even m then 0 else 2 / (m : ℝ)

/-! ## Environment S2 — matrix / elliptope / objective world -/

/-- Frobenius (Schatten-2) norm `‖X‖_{S_2} = √(∑ᵢⱼ Xᵢⱼ²)`.
@realizes F_{r,kappa}(X)(κ‖X‖_{S_2}, Frobenius norm) -/
noncomputable def frobeniusNorm {ι : Type*} [Fintype ι] (X : Matrix ι ι ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)

/-- The all-ones matrix `J_n = 1_n 1_nᵀ`.
@realizes J_n(all-ones matrix) -/
def allOnesMatrix (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ := Matrix.of fun _ _ => 1

/-- The community sign vector `s_m` (`+1` on block `A_m = {i : i < m}`, `−1` on `B_m`).
@realizes s_m(sign vector +1 on A_m, −1 on B_m) -/
def signVec (m : ℕ) : Fin (2 * m) → ℝ := fun i => if i.val < m then 1 else -1

/-- Orthogonal projection onto `span 1_n`, i.e. `J_n / n`. -/
noncomputable def onesProj (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun _ _ => (1 : ℝ) / (2 * (m : ℝ))

/-- Orthogonal projection onto `span s_m`, i.e. `s_m s_mᵀ / n`. -/
noncomputable def signProj (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j => signVec m i * signVec m j / (2 * (m : ℝ))

/-- The block-symmetric matrix `X(u,v)`: diagonal `1`, common within-block
off-diagonal entry `u`, common across-block entry `v`.
@realizes X(u,v)(diag 1, within-block u, across-block v) -/
def blockSymMatrix (m : ℕ) (u v : ℝ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j =>
    if i = j then 1 else if (decide (i.val < m) = decide (j.val < m)) then u else v

-- @node: def:two-block-graph
/-- The weighted two-block homophily adjacency `W`: `a/m` within a block, `b/m`
across blocks, `0` on the diagonal.
@realizes G_m(a,b)(within-block a/m, across-block b/m, diag 0)
@realizes a(within-block edge weight a/m; range 0<b<a pinned by TwoBlockHomophily)
@realizes b(cross-block edge weight b/m; range 0<b pinned by TwoBlockHomophily)
@realizes A_m, B_m(two communities via block membership i.val < m, |A_m|=|B_m|=m) -/
noncomputable def twoBlockGraph (m : ℕ) (a b : ℝ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j =>
    if i = j then 0
    else if (decide (i.val < m) = decide (j.val < m)) then a / (m : ℝ) else b / (m : ℝ)

/-- The graph Laplacian `L_m = D − W` of the two-block graph (`D` the degree diagonal).
@realizes L_m(graph Laplacian of G_m(a,b)) -/
noncomputable def twoBlockLaplacian (m : ℕ) (a b : ℝ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j =>
    if i = j then (∑ k, twoBlockGraph m a b i k) else - twoBlockGraph m a b i j

/-- The Moore–Penrose pseudoinverse `L_m^†`, realized by its spectral action:
eigenvalues `1/(a+b)` on the block-contrast subspace, `1/(2b)` on `span s_m`, `0`
on `span 1_n` (the only way it is consumed downstream).
@realizes L_m^dagger(pseudoinverse via spectral action 1/(a+b), 1/(2b), 0) -/
noncomputable def twoBlockLaplacianPinv (m : ℕ) (a b : ℝ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  (1 / (a + b)) • ((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) - onesProj m - signProj m)
    + (1 / (2 * b)) • signProj m

/-- The cut covariance `X_cut = s_m s_mᵀ`.
@realizes X_cut(s_m s_mᵀ) -/
def cutCovariance (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j => signVec m i * signVec m j

/-- The spread covariance `X_spread` with reduced coordinates `(m/(m-1), 0, 0)`
(the `u = -1/(m-1), v = 0` block-symmetric point). -/
noncomputable def spreadCovariance (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  blockSymMatrix m (-1 / ((m : ℝ) - 1)) 0

-- @node: def:design-objective
/-- The normalized design objective
`F_{r,κ}(X) = Tr(L_m X) + r Tr(L_m^† X) + κ ‖X‖_{S_2} + Tr(J_n X)`.
@realizes F_{r,kappa}(X)(Tr(L_m X) + r Tr(L_m^† X) + κ‖X‖ + Tr(J_n X))
@realizes r(carrier ℝ; homophily tradeoff weight on the `r * Tr(L^† X)` term)
@realizes kappa(carrier ℝ; robustness weight on the Schatten-2 penalty `κ‖X‖_{S_2}`; range
[0,∞) pinned by the `0 ≤ kappa` premises threaded through the consuming theorems/lemmas) -/
noncomputable def designObjective (m : ℕ) (a b r kappa : ℝ)
    (X : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : ℝ :=
  Matrix.trace (twoBlockLaplacian m a b * X)
    + r * Matrix.trace (twoBlockLaplacianPinv m a b * X)
    + kappa * frobeniusNorm X
    + Matrix.trace (allOnesMatrix m * X)

/-! ## Assumption atoms (threaded `Prop`s; never discharged) -/

-- @node: ass:two-block-homophily
/-- Two-block homophily: `m ≥ 2` and `a > b > 0` (within-block weight strictly
dominates the positive cross-block weight). -/
def TwoBlockHomophily (m : ℕ) (a b : ℝ) : Prop :=
  2 ≤ m ∧
  b < a ∧            -- @realizes a(range: 0 < b < a pins a ∈ (0,∞))
  0 < b              -- @realizes b(range: 0 < b pins b ∈ (0,∞))

-- @node: ass:low-scale-two-block
/-- Low-scale two-block normalization `a + 3b < 2m` (ensures `D = 2m − a − 3b > 0`). -/
def LowScaleTwoBlock (m : ℕ) (a b : ℝ) : Prop := a + 3 * b < 2 * (m : ℝ)

-- @node: ass:odd-community-size
/-- Odd community size (parity feasibility: forces `S_A, S_B` odd, so `y + z ≥ 2/m`). -/
def OddCommunitySize (m : ℕ) : Prop := Odd m

/-! ## Block elliptope slice `E_m^blk` (relaxed feasible set) -/

-- @node: def:block-elliptope
/-- Membership witness for the block-symmetric elliptope slice `E_m^blk`, over the
two-block homophily regime. Its member atom is `ass:two-block-homophily`; the three
inequalities are exactly the PSD constraints of the spectral coordinates
`x = 1−u`, `y = 1+(m−1)u−mv`, `z = 1+(m−1)u+mv`. -/
structure BlockElliptopeMem (m : ℕ) (a b u v : ℝ) : Prop where
  /-- Member atom: the two-block homophily regime. -/
  homophily : TwoBlockHomophily m a b
  /-- `x = 1 − u ≥ 0`. -/
  psd_x : 0 ≤ 1 - u
  /-- `y = 1 + (m−1)u − m v ≥ 0`. -/
  psd_y : 0 ≤ 1 + ((m : ℝ) - 1) * u - (m : ℝ) * v
  /-- `z = 1 + (m−1)u + m v ≥ 0`. -/
  psd_z : 0 ≤ 1 + ((m : ℝ) - 1) * u + (m : ℝ) * v

/-- The block-symmetric elliptope slice `E_m^blk` as a set of matrices.
@realizes E_m^blk(set of PSD block-symmetric correlation matrices X(u,v)) -/
def blockElliptope (m : ℕ) (a b : ℝ) : Set (Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :=
  { X | ∃ u v : ℝ, X = blockSymMatrix m u v ∧ BlockElliptopeMem m a b u v }

/-! ## Environment S1 — finite sign-assignment design world (`FiniteDesign` reuse)

@env: S1 — a design law `P` is a `FiniteDesign (Fin (2*m) → Bool)`: a PMF on the
finite sign-assignment space `{-1,1}^n` (encoded by `Bool`, sign `+1`/`−1`).
@realizes P(AUTHORITATIVE CARRIER: `FiniteDesign (Fin (2*m) → Bool)`; the space
"probability laws on {-1,1}^n" is pinned by the CONJUNCTION of the carrier's two PMF
fields — `p_nonneg : 0 ≤ p z` (nonnegativity) and `p_sum : ∑ z, p z = 1` (total mass
one) — so every inhabitant is a genuine probability law, not a sub-probability. This
carrier is the root of the P realization cluster; the design-class predicates
`BalancedSignDesign`/`BalancedDesignClass`/`blockExchangeableDesignClass` and the
consumers `assignmentSecondMoment`/`implementableCovarianceClass`/`implementabilityGap`
carry cluster-member `@realizes P` tags pinning the same law argument.)
-/

/-- The `±1` sign vector of an assignment `z` (`true ↦ +1`, `false ↦ −1`).
@realizes Z(±1 assignment sign vector) -/
def signOf (m : ℕ) (z : Fin (2 * m) → Bool) : Fin (2 * m) → ℝ :=
  fun i => if z i then 1 else -1

/-- The cut assignment `s_m` (treat block `A_m`, control block `B_m`). -/
def cutPlus (m : ℕ) : Fin (2 * m) → Bool := fun i => decide (i.val < m)

/-- The reversed cut assignment `−s_m`. -/
def cutMinus (m : ℕ) : Fin (2 * m) → Bool := fun i => decide (¬ i.val < m)

/-- The assignment second-moment matrix `X(P) = E_P[Z Zᵀ]`.
@realizes X(P)(second-moment matrix E_P[Z Zᵀ])
@realizes P(design-law argument `D : FiniteDesign (Fin (2*m) → Bool)`, the law over which
the second moment is taken) -/
noncomputable def assignmentSecondMoment (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool)) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j => D.E (fun z => signOf m z i * signOf m z j)

/-- The cut design `P_cut`: mass `1/2` on `s_m` and `1/2` on `−s_m`.
@realizes P_cut(½ δ_{s_m} + ½ δ_{−s_m})
@realizes P(cluster member — CONCRETE CARRIER+CONSTRAINTS instance: a `FiniteDesign
(Fin (2*m) → Bool)`, i.e. a probability law on {-1,1}^n, whose `p_nonneg`/`p_sum` fields
below discharge the PMF constraints that pin the symbol's space) -/
noncomputable def cutDesign (m : ℕ) : FiniteDesign (Fin (2 * m) → Bool) where
  p := fun z => (if z = cutPlus m then (1 : ℝ) / 2 else 0)
    + (if z = cutMinus m then (1 : ℝ) / 2 else 0)
  p_nonneg := fun z => by -- @realizes P(constraint 0 ≤ p z: nonnegativity of the law)
    have h : ∀ w : Fin (2 * m) → Bool, (0 : ℝ) ≤ if z = w then (1 : ℝ) / 2 else 0 := by
      intro w; split_ifs <;> norm_num
    exact add_nonneg (h _) (h _)
  p_sum := by -- @realizes P(constraint ∑ p = 1: total unit mass of the law)
    rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (cutPlus m) (fun _ => (1 : ℝ) / 2),
      Finset.sum_ite_eq' Finset.univ (cutMinus m) (fun _ => (1 : ℝ) / 2)]
    simp only [Finset.mem_univ, if_true]; norm_num

/-- The iid Rademacher design `P_iid`: uniform on `{-1,1}^n`.
@realizes P_iid(uniform Rademacher design)
@realizes P(cluster member — CONCRETE CARRIER+CONSTRAINTS instance: a `FiniteDesign
(Fin (2*m) → Bool)`, i.e. a probability law on {-1,1}^n, whose `p_nonneg`/`p_sum` fields
below discharge the PMF constraints that pin the symbol's space) -/
noncomputable def iidDesign (m : ℕ) : FiniteDesign (Fin (2 * m) → Bool) where
  p := fun _ => (Fintype.card (Fin (2 * m) → Bool) : ℝ)⁻¹
  p_nonneg := fun _ => by positivity -- @realizes P(constraint 0 ≤ p z: nonnegativity of the law)
  p_sum := by -- @realizes P(constraint ∑ p = 1: total unit mass of the law)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

-- @node: ass:balanced-sign-design
/-- Balanced sign-symmetric design: `P(Z = z) = P(Z = −z)` for all `z` (global
sign symmetry, implying zero one-point margins).
@realizes P(design-law argument `D : FiniteDesign (Fin (2*m) → Bool)`, the probability
law on {-1,1}^n this predicate constrains) -/
def BalancedSignDesign (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool)) : Prop :=
  ∀ z, D.p z = D.p (fun i => ! z i)

-- @node: def:balanced-design-class
/-- The balanced design class `P_m^bal`, bundling the single sign-symmetry atom.
@realizes P_m^bal(designs with global sign symmetry)
@realizes P(cluster member: the bundled law `D : FiniteDesign (Fin (2*m) → Bool)`, a
probability law on {-1,1}^n via the carrier's `p_nonneg`/`p_sum` fields) -/
structure BalancedDesignClass (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool)) : Prop where
  /-- Member atom: global sign symmetry. -/
  balanced : BalancedSignDesign m D

/-- A permutation of the units is a two-block automorphism: it either preserves
both blocks setwise or swaps them. -/
def IsBlockAuto (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) : Prop :=
  (∀ i, ((σ i).val < m ↔ i.val < m)) ∨ (∀ i, ((σ i).val < m ↔ ¬ i.val < m))

-- @node: def:block-exchangeable-design-class
/-- The block-exchangeable design class `P_m^sym`: laws in `P_m^bal` invariant
under permutations within `A_m`, within `B_m`, and under the community swap (the
full two-block automorphism group). (D0.R provisional revision carried as revised.)
@realizes P_m^sym(balanced designs invariant under the two-block automorphism group)
@realizes P(cluster member: this `Set (FiniteDesign (Fin (2*m) → Bool))` is the class of
probability laws `P` consumed downstream by `implementableCovarianceClass`/
`implementabilityGap`; each element is a probability law via the carrier's PMF fields) -/
def blockExchangeableDesignClass (m : ℕ) : Set (FiniteDesign (Fin (2 * m) → Bool)) :=
  { D | BalancedDesignClass m D ∧
      ∀ σ : Equiv.Perm (Fin (2 * m)), IsBlockAuto m σ →
        ∀ z, D.p (fun i => z (σ i)) = D.p z }

-- @node: def:implementable-covariance-class
/-- The implementable covariance class `C_m^pm = { X(P) : P ∈ P_m^sym }`.
@realizes C_m^pm(second moments of block-exchangeable designs)
@realizes P(cluster member: the bound design law `D ∈ blockExchangeableDesignClass m`
ranges over the probability laws `P` whose second moment `X(P)` defines this class) -/
def implementableCovarianceClass (m : ℕ) : Set (Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) :=
  { X | ∃ D ∈ blockExchangeableDesignClass m, X = assignmentSecondMoment m D }

/-- Community sum `S_A = ∑_{i ∈ A_m} Z_i` (integer-valued).
@realizes A_m, B_m(community A_m = {i : i.val < m}, cardinality m) -/
def blockSumA (m : ℕ) (z : Fin (2 * m) → Bool) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * m) => i.val < m), (if z i then (1 : ℤ) else -1)

/-- Community sum `S_B = ∑_{i ∈ B_m} Z_i` (integer-valued).
@realizes A_m, B_m(community B_m = {i : ¬ i.val < m}, cardinality m) -/
def blockSumB (m : ℕ) (z : Fin (2 * m) → Bool) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * m) => ¬ i.val < m), (if z i then (1 : ℤ) else -1)

-- @node: def:block-sum-handle
/-- The block-sum law handle `B(P)`: the joint pmf of the two community sums
`(S_A, S_B)` under `P` (the OEQ parity handle).
@realizes B(P)(joint law of the two community sums) -/
noncomputable def blockSumHandle (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool))
    (kl : ℤ × ℤ) : ℝ :=
  D.E (fun z => if blockSumA m z = kl.1 ∧ blockSumB m z = kl.2 then 1 else 0)

/-! ## Implementability gap and reduced-coordinate values -/

-- @node: def:implementability-gap
/-- The implementability gap `Δ_m^±(r,κ) = inf_{P ∈ P_m^sym} F(X(P)) − inf_{X ∈ E_m^blk} F(X)`,
as an `sInf` difference over the objective images.
@realizes Delta_m^pm(r,kappa)(implementable inf − relaxed inf; CARRIER of the gap. The bare
`sInf − sInf` real difference is a plain `ℝ`; its core-declared range `[0,∞)` is NOT carried
by this `def` alone but by the CONJUNCTION of this carrier with the companion range lemma
`implementabilityGap_nonneg` in `Helpers/GapReduction.lean`, which pins `0 ≤ Δ_m^±` via
the reduced constrained-minus-unconstrained identity.)
@realizes P(cluster member — AUTHORITATIVE link into the `sharp_rho_star` target block:
the implementable `sInf` is taken over `designObjective … '' implementableCovarianceClass m`,
i.e. over the second moments `X(P)` of the probability laws `P ∈ P_m^sym`; this is the
decl through which the P realization cluster enters `thm:sharp-rho-star`)
@realizes kappa(carrier ℝ; robustness argument of the gap; range [0,∞) pinned by the
`0 ≤ kappa` premises of the consuming theorems `sharp_rho_star`/`rounding_gap_reduction`) -/
noncomputable def implementabilityGap (m : ℕ) (a b r kappa : ℝ) : ℝ :=
  sInf (designObjective m a b r kappa '' implementableCovarianceClass m)
    - sInf (designObjective m a b r kappa '' blockElliptope m a b)

/-- The relaxed reduced value `min_{T_m} φ`. -/
noncomputable def relaxedReducedValue (m : ℕ) (a b r kappa : ℝ) : ℝ :=
  sInf { v | ∃ x y z, InReducedTriangle m x y z ∧
    v = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z }

/-- The implementable reduced value `min_{T_m ∩ {y+z ≥ d_m}} φ`. -/
noncomputable def implementableReducedValue (m : ℕ) (a b r kappa : ℝ) : ℝ :=
  sInf { v | ∃ x y z, InReducedTriangle m x y z ∧ parityThreshold m ≤ y + z ∧
    v = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z }

/-- The tight rounding-loss certificate `ρ_⋆`, realized as the reduced-coordinate
implementable-minus-relaxed value (proved equal to `Δ_m^±` by `rounding_gap_reduction`).
The bare `implementableReducedValue − relaxedReducedValue` real difference is a plain `ℝ`;
its core-declared range `[0,∞)` is NOT carried by this `def` alone but by the CONJUNCTION of
this carrier with the companion range lemma `roundingLossCertificate_nonneg` below, which
pins `0 ≤ ρ_⋆` (the constrained reduced value dominating the unconstrained one, exactly as
`Δ_m^±` is pinned nonnegative by `implementabilityGap_nonneg`).
@realizes rho_star(m,a,b,r,kappa)(reduced constrained-minus-unconstrained value; CARRIER of
the certificate, range [0,∞) pinned via the companion lemma below) -/
noncomputable def roundingLossCertificate (m : ℕ) (a b r kappa : ℝ) : ℝ :=
  implementableReducedValue m a b r kappa - relaxedReducedValue m a b r kappa

/-- **Range lemma for `ρ_⋆`.** The rounding-loss certificate lands in its core-declared
space `[0,∞)`: `0 ≤ ρ_⋆(m,a,b,r,κ)`. This holds because the implementable reduced value
(the constrained `sInf` over `T_m ∩ {y+z ≥ d_m}`) dominates the relaxed reduced value (the
unconstrained `sInf` over the larger set `T_m`), the implementable feasible set being a
subset of the relaxed one. Together with the `roundingLossCertificate` carrier `def` above,
this lemma IS the realization of the symbol's standing range condition (the bare
`sInf − sInf` real difference does not by itself guarantee nonnegativity).
@realizes rho_star(m,a,b,r,kappa)(range [0,∞) pinned via {y+z ≥ d_m}-constrained inf ≥
unconstrained inf ⇒ implementable reduced value ≥ relaxed reduced value) -/
-- @node: roundingLossCertificate_nonneg
lemma roundingLossCertificate_nonneg (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hr0 : 0 ≤ r) (hk : 0 ≤ kappa) :
    0 ≤ roundingLossCertificate m a b r kappa := by
  unfold roundingLossCertificate implementableReducedValue relaxedReducedValue
  rw [sub_nonneg]
  let Srel : Set ℝ :=
    { v | ∃ x y z, InReducedTriangle m x y z ∧
      v = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z }
  let Simp : Set ℝ :=
    { v | ∃ x y z, InReducedTriangle m x y z ∧ parityThreshold m ≤ y + z ∧
      v = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z }
  change sInf Srel ≤ sInf Simp
  apply csInf_le_csInf
  · refine ⟨0, ?_⟩
    intro v hv
    rcases hv with ⟨x, y, z, hT, rfl⟩
    rcases hHom with ⟨hm, hba, hb⟩
    rcases hT with ⟨hx, hy, hz, _hsum⟩
    unfold reducedObjective cX cY cZ
    have hq_nonneg : 0 ≤ qParam m := by
      unfold qParam
      have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith
    have hsum_pos : 0 < a + b := by linarith
    have hb2_pos : 0 < 2 * b := by positivity
    have hcx_nonneg : 0 ≤ qParam m * (a + b + r / (a + b)) := by positivity
    have hcy_nonneg : 0 ≤ 2 * b + r / (2 * b) := by positivity
    have hcz_nonneg : 0 ≤ 2 * (m : ℝ) := by positivity
    have hsqrt_nonneg : 0 ≤ Real.sqrt (qParam m * x ^ 2 + y ^ 2 + z ^ 2) :=
      Real.sqrt_nonneg _
    nlinarith [mul_nonneg hcx_nonneg hx, mul_nonneg hcy_nonneg hy,
      mul_nonneg hcz_nonneg hz, mul_nonneg hk hsqrt_nonneg]
  · refine ⟨reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa 1 1 1, ?_⟩
    refine ⟨1, 1, 1, ?_, ?_, rfl⟩
    · refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
      unfold qParam
      ring
    · unfold parityThreshold
      by_cases hEven : Even m
      · rw [if_pos hEven]
        norm_num
      · rw [if_neg hEven]
        rcases hHom with ⟨hm, _hba, _hb⟩
        have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hmpos : 0 < (m : ℝ) := by linarith
        have hdiv : 2 / (m : ℝ) ≤ 2 := by
          rw [div_le_iff₀ hmpos]
          nlinarith
        nlinarith
  · intro v hv
    rcases hv with ⟨x, y, z, hT, _hpar, rfl⟩
    exact ⟨x, y, z, hT, rfl⟩

-- @node: sym:r_star
/-- **Sharp cut-break exactness boundary `r_⋆(m,a,b,κ)`** — the HONEST-OPEN frontier
symbol (`open_phase_boundary` role; it has NO statement node and NO closed form by design;
its clean/set-valued shape is deliberately left open, see honest scope). This predicate
is the dedicated carrier that realizes the symbol's `[0,∞)` SPACE together with its
defining boundary role: `rStar` is a *nonnegative* ratio (its `[0,∞)` space) below which
the rounding loss vanishes — i.e. it lower-bounds a zero-loss `r`-region `[0, rStar)`,
the "cut-break ratio separating zero implementability loss from positive loss". No
existence, uniqueness, or exact value of such an `rStar` is asserted anywhere (honest
open scope); only the space and the separating role are pinned here.
@realizes r_star(m,a,b,kappa)(carrier/predicate for the open boundary object; its `[0,∞)`
space is pinned by the `0 ≤ rStar` conjunct, its separating role by the zero-loss clause) -/
def IsSharpExactnessBoundary (m : ℕ) (a b kappa rStar : ℝ) : Prop :=
  0 ≤ rStar ∧   -- @realizes r_star(range 0 ≤ r_⋆ pins the boundary object into its [0,∞) space)
  ∀ r, 0 ≤ r → r < rStar →
    roundingLossCertificate m a b r kappa = 0
    -- @realizes r_star(separating role: below the cut-break ratio the rounding loss is zero)

-- @node: sym:kappa_iid
/-- **iid-exactness frontier `κ_iid(m,a,b,r)`** — the dedicated carrier that realizes the
symbol's `[0,∞)` SPACE together with its defining frontier role (`iid_exactness_frontier`,
role `derived_phase_boundary`). `κ_iid` is the smallest *nonnegative* robustness weight
from which the iid covariance `I_n = X(P_iid)` remains optimal over the block-symmetric
elliptope slice `E_m^blk`, and it dominates the cut frontier
`κ_cut(m,a,b) = max 0 (min (a−b) (2(m−b)))` (the core relation `κ_iid ≥ κ_cut`). This
predicate is that carrier: the `0 ≤ κ_iid` conjunct pins the `[0,∞)` space, the
`κ_cut ≤ κ_iid` conjunct records the core ordering, and the trailing clause pins the
frontier role — above the frontier weight, `I_n` minimizes `F_{r,κ}` on `E_m^blk`. No
existence, uniqueness, or closed form of such a `κ_iid` is asserted here (the iid frontier,
like `r_⋆`, is bound only as a symbol; `robust_corner_exactness` supplies the finiteness
criterion for its EXISTENCE — a finite frontier exists iff the affine-balanced locus holds
— not its value). Mirrors the `IsSharpExactnessBoundary` carrier for `r_⋆`.
@realizes kappa_iid(m,a,b,r)(carrier/predicate for the iid-exactness frontier; its `[0,∞)`
space is pinned by the `0 ≤ κ_iid` conjunct, the `κ_iid ≥ κ_cut` ordering by the second
conjunct, and its frontier role by the optimality clause) -/
def IsIidExactnessFrontier (m : ℕ) (a b r kappaIid : ℝ) : Prop :=
  0 ≤ kappaIid ∧   -- @realizes kappa_iid(range 0 ≤ κ_iid pins the frontier into its [0,∞) space)
  max 0 (min (a - b) (2 * ((m : ℝ) - b))) ≤ kappaIid ∧
    -- @realizes kappa_iid(ordering κ_iid ≥ κ_cut(m,a,b), core-def closed form of κ_cut)
  ∀ kappa : ℝ, kappaIid < kappa →
    (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) ∈ blockElliptope m a b ∧
      ∀ X ∈ blockElliptope m a b,
        designObjective m a b r kappa 1 ≤ designObjective m a b r kappa X
    -- @realizes kappa_iid(frontier role: above the frontier weight I_n stays F-optimal on E_m^blk)

end CausalSmith.Experimentation.DesignPm1
