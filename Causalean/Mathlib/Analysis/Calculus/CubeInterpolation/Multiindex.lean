module
public import Causalean.Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.List.OfFn

/-!
# Finite coordinate multi-indices

Natural count vectors, bounded-degree indices, and their sorted coordinate words.
The finite index type uses natural coordinates, so it can be identified directly
with existing sorted-partial Taylor definitions. No function or polynomial
representation is assumed in this combinatorial layer.
-/

@[expose] public section

open scoped BigOperators
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The [total order](goal) of [a vector of coordinate counts](hyp:κ) is [the sum of its
entries](step:1). -/
def multiOrder {d : ℕ} (κ : Fin d → ℕ) : ℕ := ∑ i, κ i

/-- The [multi-index factorial](goal) of [a vector of coordinate counts](hyp:κ) is [the product of
the factorials of its entries](step:1). -/
def multiFactorial {d : ℕ} (κ : Fin d → ℕ) : ℕ := ∏ i, (κ i).factorial

/-- For [a dimension d and a degree bound m](hyp:d,m), this is [the type of bounded-degree
multi-indices](goal): [vectors of d natural-number counts whose total order is at most m](step:1).
-/
abbrev MultiIndex (d m : ℕ) := {κ : Fin d → ℕ // multiOrder κ ≤ m}

/-- For [a vector of coordinate counts](hyp:κ) and [any coordinate](hyp:i), [the count at that
coordinate is at most the vector's total order](goal). -/
theorem coordinate_le_order {d : ℕ} (κ : Fin d → ℕ) (i : Fin d) :
    κ i ≤ multiOrder κ := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ i)

/-- For [any dimension d and degree bound m](hyp:d,m), including dimension zero, [there are only
finitely many count vectors of total order at most m](goal). -/
instance multiIndex_finite (d m : ℕ) : Finite (MultiIndex d m) := by
  let encode : MultiIndex d m → (Fin d → Fin (m + 1)) := fun κ i =>
    ⟨κ.1 i, Nat.lt_succ_of_le ((coordinate_le_order κ.1 i).trans κ.2)⟩
  apply Finite.of_injective encode
  intro κ κ' h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

/-- For [any dimension d and degree bound m](hyp:d,m), this supplies [a finite enumeration of the
count vectors of total order at most m](goal), so that sums over them make sense. -/
instance multiIndex_fintype (d m : ℕ) : Fintype (MultiIndex d m) := Fintype.ofFinite _

/-- For [a dimension d and an order k](hyp:d,k), this is [the type of fixed-order
multi-indices](goal): [vectors of d natural-number counts whose total order is exactly k](step:1).
-/
abbrev ExactIndex (d k : ℕ) := {κ : Fin d → ℕ // multiOrder κ = k}

/-- For [any dimension d and order k](hyp:d,k), [there are only finitely many count vectors of
total order exactly k](goal). -/
instance exactIndex_finite (d k : ℕ) : Finite (ExactIndex d k) := by
  let encode : ExactIndex d k → MultiIndex d k := fun κ => ⟨κ.1, κ.2.le⟩
  apply Finite.of_injective encode
  intro κ κ' h
  exact Subtype.ext (congrArg (fun q : MultiIndex d k => q.1) h)

/-- For [any dimension d and order k](hyp:d,k), this supplies [a finite enumeration of the count
vectors of total order exactly k](goal), so that sums over them make sense. -/
instance exactIndex_fintype (d k : ℕ) : Fintype (ExactIndex d k) := Fintype.ofFinite _

/-- The [increasing coordinate list](goal) of [a vector of coordinate counts](hyp:κ) [lists the
coordinates in increasing order, repeating each one as many times as its count](step:1). -/
def countList {d : ℕ} (κ : Fin d → ℕ) : List (Fin d) :=
  (List.ofFn fun i => List.replicate (κ i) i).flatten

/-- For [a vector of coordinate counts](hyp:κ), [the length of its increasing coordinate list
equals its total order](goal). -/
theorem countList_length {d : ℕ} (κ : Fin d → ℕ) :
    (countList κ).length = multiOrder κ := by
  simp [countList, List.length_flatten, List.sum_ofFn, multiOrder]

/-- The [sorted word](goal) of [a vector of coordinate counts](hyp:κ) is [the coordinate word, of
length equal to the total order, whose entry at each position is the entry of the increasing
coordinate list at that position](step:1). -/
def sortedWord {d : ℕ} (κ : Fin d → ℕ) : Fin (multiOrder κ) → Fin d :=
  fun r => (countList κ).get ⟨r.val, by rw [countList_length]; exact r.isLt⟩

/-- The [sorted word of fixed length k](goal) of [a count vector whose total order is exactly
k](hyp:κ) is [its sorted word, with positions relabelled to run over the k positions](step:1). -/
def sortedWordOfOrder {d k : ℕ} (κ : ExactIndex d k) : Fin k → Fin d :=
  fun r => sortedWord κ.1 (Fin.cast κ.2.symm r)

/-- The [centred coordinate monomial](goal) for [a centre a and a point x](hyp:a,x) and [a vector
of coordinate counts](hyp:κ) is [the product over coordinates of the difference between the
coordinates of x and a, raised to that coordinate's count](step:1). -/
def centeredMonomial {d : ℕ} (a x : EuclideanSpace ℝ (Fin d))
    (κ : Fin d → ℕ) : ℝ := ∏ i, (x i - a i) ^ κ i

/-- For [a vector of coordinate counts](hyp:κ), [its multi-index factorial is strictly
positive](goal). -/
theorem multiFactorial_pos {d : ℕ} (κ : Fin d → ℕ) : 0 < multiFactorial κ := by
  exact Finset.prod_pos (fun i _ => Nat.factorial_pos (κ i))

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

