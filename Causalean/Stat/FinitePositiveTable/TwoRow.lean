module
public import Causalean.Stat.FinitePositiveTable.Marginals

/-!
# Row, total, and cancellation identities for fixed kernels

This module proves the graph-independent row normalization, total normalization, and positive
marginal cancellation identities used to read conditional independence from fixed kernels.
-/

@[expose] public section

open Finset
open scoped BigOperators

noncomputable section

namespace Causalean.Stat.FinitePositiveTable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {r : V → ℕ}

/-- The [kernel](hyp:q), [row coordinate](hyp:d), and [reference profile](hyp:x) determine [the
kernel's coordinate-row mass](goal) [by summing over that coordinate](step:1). -/
def coordinateRowMass (q : Kernel r) (d : V) (x : ProfileSpace r) : ℝ :=
  ∑ zd : Fin (r d), q (Function.update x d zd)

/-- The [kernel](hyp:q), [two varying coordinates](hyp:a,d), and [reference profile](hyp:x)
determine [the kernel's coordinate-rectangle mass](goal) [by summing over both coordinates](step:1). -/
def coordinateRectangleMass (q : Kernel r) (a d : V) (x : ProfileSpace r) : ℝ :=
  ∑ za : Fin (r a), ∑ zd : Fin (r d),
    q (Function.update (Function.update x a za) d zd)

/-- The [kernel](hyp:q), [column coordinate](hyp:a), and [reference profile](hyp:x) determine
[the kernel's coordinate-column mass](goal) [by summing over that coordinate](step:1). -/
def coordinateColumnMass (q : Kernel r) (a : V) (x : ProfileSpace r) : ℝ :=
  ∑ za : Fin (r a), q (Function.update x a za)

/-- The [positive table](hyp:p), [kernel](hyp:q), [three distinct-role coordinates](hyp:a,c,d),
and [residual kernel](hyp:K) determine [the marginal-times-kernel representation](goal) [when the
kernel factors into the positive `a` marginal and the residual three-coordinate kernel](step:1). -/
def HasMarginalKernelForm (p : PositiveTable r) (q : Kernel r) (a c d : V)
    (K : Fin (r a) → Fin (r c) → Fin (r d) → ℝ) : Prop :=
  ∀ x, q x = marginalMass p {a} x * K (x a) (x c) (x d)

/-- The [residual kernel](hyp:K) has [normalized rows in its final coordinate](goal) [when each
such row sums to one](step:1). -/
def KernelRowsNormalized {a c d : V}
    (K : Fin (r a) → Fin (r c) → Fin (r d) → ℝ) : Prop :=
  ∀ xa xc, ∑ xd, K xa xc xd = 1

/-- The [residual kernel](hyp:K) has [pointwise nonnegativity](goal) [when every entry is
nonnegative](step:1). -/
def KernelNonnegative {a c d : V}
    (K : Fin (r a) → Fin (r c) → Fin (r d) → ℝ) : Prop :=
  ∀ xa xc xd, 0 ≤ K xa xc xd

/-- The [kernel](hyp:q), [two coordinates](hyp:a,d), and [profile](hyp:x) determine [the
multiplicative conditional-independence identity at that profile](goal) [by equating the
profile-and-rectangle product with the row-and-column product](step:1). -/
def KernelCondIndepAt (q : Kernel r) (a d : V) (x : ProfileSpace r) : Prop :=
  q x * coordinateRectangleMass q a d x =
    coordinateRowMass q d x * coordinateColumnMass q a x

/-- The [kernel](hyp:q) and [two coordinates](hyp:a,d) determine [their multiplicative
conditional-independence identity at every profile](goal) [by requiring the pointwise identity
at each profile](step:1). -/
def KernelCondIndep (q : Kernel r) (a d : V) : Prop :=
  ∀ x, KernelCondIndepAt q a d x

/-- For [a positive common factor](hyp:m,hm) and [an equality after multiplying two real
numbers by it](hyp:x,y,h), [the two real numbers are equal](goal). -/
theorem eq_of_pos_mul_eq_mul {m x y : ℝ} (hm : 0 < m) (h : m * x = m * y) : x = y := by
  exact mul_left_cancel₀ hm.ne' h

/-- For [a positive table](hyp:p), [a kernel](hyp:q), [two coordinates distinct from the row
coordinate](hyp:a,c,d,had,hcd), [a residual kernel](hyp:K), [its marginal-times-kernel
form](hyp:hform), [normalized residual rows](hyp:hrows), and [a profile](hyp:x), [the kernel's
row mass equals the positive table's `a` marginal](goal). -/
theorem coordinateRowMass_eq_marginalMass
    (p : PositiveTable r) (q : Kernel r) {a c d : V}
    (had : a ≠ d) (hcd : c ≠ d)
    (K : Fin (r a) → Fin (r c) → Fin (r d) → ℝ)
    (hform : HasMarginalKernelForm p q a c d K)
    (hrows : KernelRowsNormalized K) (x : ProfileSpace r) :
    coordinateRowMass q d x = marginalMass p {a} x := by
  unfold HasMarginalKernelForm at hform
  unfold KernelRowsNormalized at hrows
  unfold coordinateRowMass
  have hm (zd : Fin (r d)) :
      marginalMass p {a} (Function.update x d zd) = marginalMass p {a} x := by
    unfold marginalMass kernelMarginalMass
    exact fiberSum_update_of_not_mem p.mass (by simpa using had.symm) x zd
  simp_rw [hform, hm]
  simp only [Function.update_of_ne had, Function.update_of_ne hcd,
    Function.update_self]
  rw [← Finset.mul_sum, hrows]
  exact mul_one _

/-- For [a positive table](hyp:p), [a kernel](hyp:q), [two coordinates distinct from the row
coordinate](hyp:a,c,d,had,hcd), [a residual kernel](hyp:K), [its marginal-times-kernel
form](hyp:hform), [normalized residual rows](hyp:hrows), and [a profile](hyp:x), [the kernel's
rectangle mass equals one](goal). -/
theorem coordinateRectangleMass_eq_one
    (p : PositiveTable r) (q : Kernel r) {a c d : V}
    (had : a ≠ d) (hcd : c ≠ d)
    (K : Fin (r a) → Fin (r c) → Fin (r d) → ℝ)
    (hform : HasMarginalKernelForm p q a c d K)
    (hrows : KernelRowsNormalized K) (x : ProfileSpace r) :
    coordinateRectangleMass q a d x = 1 := by
  unfold coordinateRectangleMass
  change (∑ za : Fin (r a), coordinateRowMass q d (Function.update x a za)) = 1
  simp_rw [coordinateRowMass_eq_marginalMass p q had hcd K hform hrows]
  unfold marginalMass kernelMarginalMass
  rw [sum_fiberSum_singleton_update, p.sum_mass_eq_one]

/-- For [a positive table](hyp:p), [a kernel](hyp:q), [three coordinates](hyp:a,c,d), [a
residual kernel](hyp:K), [its marginal-times-kernel form](hyp:hform), [nonnegative residual
entries](hyp:hK), and [a profile](hyp:x), [the kernel is nonnegative](goal). -/
theorem kernel_nonneg_of_marginalKernelForm
    (p : PositiveTable r) (q : Kernel r) {a c d : V}
    (K : Fin (r a) → Fin (r c) → Fin (r d) → ℝ)
    (hform : HasMarginalKernelForm p q a c d K)
    (hK : KernelNonnegative K) (x : ProfileSpace r) : 0 ≤ q x := by
  rw [hform]
  exact mul_nonneg (marginalMass_pos p {a} x).le (hK (x a) (x c) (x d))

/-- For [a positive table](hyp:p), [a kernel](hyp:q), [three pairwise distinct coordinates](hyp:a,c,d,hac,had,hcd),
[a residual kernel](hyp:K), [its marginal-times-kernel form](hyp:hform), [normalized residual
rows](hyp:hrows), and [the kernel's multiplicative conditional-independence identity](hyp:hci),
[the residual row is unchanged when the positive-marginal coordinate is replaced](goal). -/
theorem kernelRows_eq_of_condIndep
    (p : PositiveTable r) (q : Kernel r) {a c d : V}
    (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    (K : Fin (r a) → Fin (r c) → Fin (r d) → ℝ)
    (hform : HasMarginalKernelForm p q a c d K)
    (hrows : KernelRowsNormalized K)
    (hci : KernelCondIndep q a d) :
    ∀ (x : ProfileSpace r) (za : Fin (r a)),
      K (x a) (x c) (x d) = K za (x c) (x d) := by
  intro x za
  have hKcol (y : ProfileSpace r) :
      K (y a) (y c) (y d) = coordinateColumnMass q a y := by
    have h := hci y
    unfold KernelCondIndepAt at h
    rw [coordinateRectangleMass_eq_one p q had hcd K hform hrows y,
      coordinateRowMass_eq_marginalMass p q had hcd K hform hrows y,
      hform y] at h
    simp only [mul_one] at h
    exact eq_of_pos_mul_eq_mul (marginalMass_pos p {a} y) h
  have hcol :
      coordinateColumnMass q a (Function.update x a za) =
        coordinateColumnMass q a x := by
    unfold coordinateColumnMass
    apply Finset.sum_congr rfl
    intro z hz
    rw [Function.update_idem]
  calc
    K (x a) (x c) (x d) = coordinateColumnMass q a x := hKcol x
    _ = coordinateColumnMass q a (Function.update x a za) := hcol.symm
    _ = K ((Function.update x a za) a) ((Function.update x a za) c)
        ((Function.update x a za) d) := (hKcol (Function.update x a za)).symm
    _ = K za (x c) (x d) := by
      simp only [Function.update_self, Function.update_of_ne hac.symm,
        Function.update_of_ne had.symm]

end Causalean.Stat.FinitePositiveTable
