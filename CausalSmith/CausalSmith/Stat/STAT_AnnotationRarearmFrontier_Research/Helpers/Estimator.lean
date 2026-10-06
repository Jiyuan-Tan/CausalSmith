module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Basic
public import Causalean.Stat.Concentration.Poisson.FactorialPolynomial
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
Ordered three-pool estimator with degree calibrated to rare-label information.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[The hybrid schedule records the stated pool sizes, Poisson intensities, polynomial degree, and
bandwidth](goal).
-/
structure HybridTuning where
  h0 : Nat
  hp : Nat
  hf : Nat
  Mp : Nat
  Mf : Nat
  L : Nat
  k0 : Nat
  u : Real
  tp : Real
  t : Real
  B : Real
/--
[The public tuning implements the ordered splits and logarithmic degree based on rare-label
information](goal).
-/
noncomputable def hybridTuning (n m : Nat) (eps : Real) : HybridTuning :=
  let h0 := n / 3
  let hp := (n - h0) / 2
  let hf := n - h0 - hp
  let Mp := hp + m / 2
  let Mf := hf + m - m / 2
  let u : Real := h0 / 8
  let tp : Real := Mp / 8
  let t : Real := Mf / 8
  let L := Nat.floor (Real.log ((n : Real) * eps) / 1024)
  let B : Real := 2 ^ 20 * L / min tp t
  ⟨h0, hp, hf, Mp, Mf, L, Nat.floor (tp * B / 4), u, tp, t, B⟩
/--
[The first Chebyshev continuation divides its zero-constant numerator by the polynomial
variable](goal).
-/
noncomputable def chebE (L : Nat) : Polynomial Real :=
  ((2 * (L : Real) ^ 2)⁻¹ •
    (1 - (Polynomial.Chebyshev.T Real L).comp (1 - 2 * Polynomial.X))).divByMonic Polynomial.X
/--
[The second continuation divides one minus the first by the polynomial variable](goal).
-/
noncomputable def chebG (L : Nat) : Polynomial Real :=
  (1 - chebE L).divByMonic Polynomial.X
/--
[Complete records in an ordered block with a fixed mark](goal).
-/
def labeledBlockCount {n d : Nat} (s : Fin n → Obs d) (offset r : Nat)
    (j : Fin d) (a y : Bool) : Nat :=
  (Finset.univ.filter fun i => offset ≤ i.val ∧ i.val < offset + r ∧ s i = (j, a, y)).card
/--
[The count uses an ordered auxiliary block and the specified arm-cell mark](goal).
-/
def auxiliaryBlockCount {m d : Nat} (s : Fin m → AuxObs d) (offset r : Nat)
    (j : Fin d) (a : Bool) : Nat :=
  (Finset.univ.filter fun i => offset ≤ i.val ∧ i.val < offset + r ∧ s i = (j, a)).card
/--
[Concatenation order is complete-record projections followed by auxiliary records](goal).
-/
def pooledArmCount {n m d : Nat} (s : Sample n m d)
    (lo size ao r : Nat) (j : Fin d) (a : Bool) : Nat :=
  labeledBlockCount s.1 lo (min r size) j a false +
  labeledBlockCount s.1 lo (min r size) j a true +
  auxiliaryBlockCount s.2 ao (r - size) j a
/--
[A pilot count selects the polynomial or inverse-count arm contribution](goal).
-/
noncomputable def hybridCellValue (L : Nat) (B : Real) (k0 : Nat) (u t : Real)
    (Z J K Kopp : Nat) : Real :=
  let Ghat : Real := ∑ h ∈ Finset.range (L - 1),
    (chebG L).coeff h * (K.descFactorial h : Real) / (t * B) ^ h
  if J ≤ k0 then (Z : Real) / u * (1 + (Kopp : Real) * Ghat / (t * B))
  else (Z : Real) / u * (1 + (Kopp : Real) / ((K : Real) + 1))
/--
[A valid prefix triple contributes the clipped sum of treated-minus-control hybrid cell
values](goal).
-/
noncomputable def hybridPrefixStatistic {n m d : Nat} (eps : Real)
    (r0 rp rf : Nat) (s : Sample n m d) : Real :=
  let tun := hybridTuning n m eps
  let Z := fun a j => labeledBlockCount s.1 0 r0 j a true
  let J := fun a j => pooledArmCount s tun.h0 tun.hp 0 rp j a
  let K := fun a j => pooledArmCount s (tun.h0 + tun.hp) tun.hf (m / 2) rf j a
  let V := fun a j => hybridCellValue tun.L tun.B tun.k0 tun.u tun.t
    (Z a j) (J a j) (K a j) (K (!a) j)
  max (-1) (min 1 (∑ j : Fin d, (V true j - V false j)))
-- @node: def:estimator-handle
/--
[The attaining data-only rule averages all valid prefix triples with their Poisson weights;
overflow outputs zero](goal).
-/
noncomputable def hybridEstimator (n m d : Nat) (eps : Real) : Sample n m d → Real :=
  fun s => if (n : Real) * eps < Real.exp 4096 then 0 else
    let tun := hybridTuning n m eps
    ∑ r0 ∈ Finset.range (tun.h0 + 1), ∑ rp ∈ Finset.range (tun.Mp + 1),
      ∑ rf ∈ Finset.range (tun.Mf + 1),
        Real.exp (-tun.u - tun.tp - tun.t) *
          (tun.u ^ r0 / (r0.factorial : Real)) * (tun.tp ^ rp / (rp.factorial : Real)) *
          (tun.t ^ rf / (rf.factorial : Real)) * hybridPrefixStatistic eps r0 rp rf s
  -- @realizes \widehat\tau(explicit finite prefix average; overflow is zero; ignores seed)
/--
[The finite prefix-average rule is measurable on the original finite data](goal).
-/
@[fun_prop]
-- @node: hybridEstimator_measurable
lemma hybridEstimator_measurable (n m d : Nat) (eps : Real) :
    Measurable (hybridEstimator n m d eps) := by
  fun_prop
/-- [Under the stated inputs and conditions](hyp:lambda,hlambda,N,f,hf), A finite Poisson average with zero output on omitted counts preserves [-1,1].  This gives [the stated result](goal).-/
-- @node: finitePoissonAverage_mem_Icc
lemma finitePoissonAverage_mem_Icc (lambda : Real) (hlambda : 0 ≤ lambda)
    (N : Nat) (f : Nat → Real) (hf : ∀ k, f k ∈ Set.Icc (-1) 1) :
    (∑ k ∈ Finset.range (N + 1), Real.exp (-lambda) *
      (lambda ^ k / (k.factorial : Real)) * f k) ∈ Set.Icc (-1) 1 := by
  let rate : NNReal := ⟨lambda, hlambda⟩
  let w := Causalean.Mathlib.Probability.PoissonAddOnePoincare.poissonWeight rate
  have hw (k : Nat) : 0 ≤ w k :=
    Causalean.Mathlib.Probability.PoissonAddOnePoincare.poissonWeight_nonneg rate k
  have hsum : ∑ k ∈ Finset.range (N + 1), w k ≤ 1 := by
    have hp := Causalean.Mathlib.Probability.PoissonAddOnePoincare.poissonWeight_hasSum_one rate
    exact (hp.summable.sum_le_tsum _ (fun k _ => hw k)).trans_eq hp.tsum_eq
  have habs : |∑ k ∈ Finset.range (N + 1), w k * f k| ≤ 1 := by
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), |w k * f k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (N + 1), w k := Finset.sum_le_sum (fun k _ => by
        rw [abs_mul, abs_of_nonneg (hw k)]
        exact mul_le_of_le_one_right (hw k) (abs_le.mpr (hf k)))
      _ ≤ 1 := hsum
  have hwdef (k : Nat) : w k = Real.exp (-lambda) *
      (lambda ^ k / (k.factorial : Real)) := by
    change Real.exp (-lambda) * lambda ^ k / (k.factorial : Real) = _
    rw [mul_div_assoc]
  simp_rw [hwdef] at habs
  exact abs_le.mp habs

/--
[Under the stated inputs and conditions](hyp:eps,s,n,m,d), [The prefix-average rule takes values between minus one and one](goal).
-/
-- @node: hybridEstimator_mem_Icc
lemma hybridEstimator_mem_Icc (n m d : Nat) (eps : Real) (s : Sample n m d) :
    hybridEstimator n m d eps s ∈ Set.Icc (-1) 1 := by
  classical
  by_cases hsmall : (n : Real) * eps < Real.exp 4096
  · simp [hybridEstimator, hsmall]
  · rw [hybridEstimator, if_neg hsmall]
    let tun := hybridTuning n m eps
    have hu : 0 ≤ tun.u := by dsimp [tun, hybridTuning]; positivity
    have hp : 0 ≤ tun.tp := by dsimp [tun, hybridTuning]; positivity
    have ht : 0 ≤ tun.t := by dsimp [tun, hybridTuning]; positivity
    have hclip (r0 rp rf : Nat) : hybridPrefixStatistic eps r0 rp rf s ∈ Set.Icc (-1) 1 := by
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (min_le_left _ _)
    have havg := finitePoissonAverage_mem_Icc tun.u hu tun.h0 _ (fun r0 =>
      finitePoissonAverage_mem_Icc tun.tp hp tun.Mp _ (fun rp =>
        finitePoissonAverage_mem_Icc tun.t ht tun.Mf _ (hclip r0 rp)))
    convert havg using 1
    simp only [tun, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r0 _
    apply Finset.sum_congr rfl
    intro rp _
    apply Finset.sum_congr rfl
    intro rf _
    rw [show -(hybridTuning n m eps).u - (hybridTuning n m eps).tp -
      (hybridTuning n m eps).t = -(hybridTuning n m eps).u +
      -(hybridTuning n m eps).tp + -(hybridTuning n m eps).t by ring,
      Real.exp_add, Real.exp_add]
    ring


end CausalSmith.Stat.AnnotationRarearmFrontier
