module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.EuclideanJets
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Geometry
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Words

/-!
# Within-cube diagonal and sorted multi-index Taylor polynomials

Coordinate derivatives use Euclidean coordinate vectors and iterated within-set
Fréchet derivatives, so boundary values never presume a smooth ambient extension.
The algebraic conversion accepts permutation invariance; a separate lemma derives
that invariance from within-cube regularity. Multinomial grouping is at arbitrary
order, and the degree-two adapter later specializes it to orders zero, one, two.
-/

@[expose] public section

open scoped BigOperators Topology
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The [sorted coordinate partial](goal) of [a function on its derivative domain](hyp:S,u) for [a
vector of coordinate counts](hyp:κ) at [an evaluation point](hyp:x) is [the ordered coordinate
partial along the increasing word that repeats each coordinate as many times as its count](step:1).
-/
def coordinatePartial {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (κ : Fin d → ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ := wordPartialWithin S u (sortedWord κ) x

/-- The [diagonal Taylor polynomial](goal) of [a function on its derivative domain](hyp:S,u) of
[degree m](hyp:m) with [centre a, evaluated at x](hyp:a,x), is [the sum over orders k from 0 to m
of one over k factorial times the order-k derivative within the domain at a, taken k times in the
direction x − a](step:1). -/
def diagonalTaylor {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (m : ℕ)
    (a x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), (k.factorial : ℝ)⁻¹ *
    iteratedFDerivWithin ℝ k u S a (fun _ => x - a)

/-- The [sorted Taylor coefficient](goal) of [a function on its derivative domain](hyp:S,u) at [a
centre](hyp:a) for [a vector of coordinate counts of total order at most m](hyp:κ) is [the sorted
coordinate partial for those counts at the centre divided by the product of the factorials of the
counts](step:1). -/
def taylorCoefficient {d m : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (a : EuclideanSpace ℝ (Fin d))
    (κ : MultiIndex d m) : ℝ := coordinatePartial S u κ.1 a / (multiFactorial κ.1 : ℝ)

/-- The [multi-index Taylor polynomial](goal) of [a function on its derivative domain](hyp:S,u) of
[degree m](hyp:m) with [centre a, evaluated at x](hyp:a,x), is [the sum over all count vectors of
total order at most m of the sorted Taylor coefficient times the matching monomial in the
coordinates of x − a](step:1). -/
def multiindexTaylor {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (m : ℕ)
    (a x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ κ : MultiIndex d m, taylorCoefficient S u a κ * centeredMonomial a x κ.1

/-- For [a function on its derivative domain](hyp:S,u) and [a point](hyp:a) at which [the order-k
derivative within the domain is unchanged by reordering its directions](hyp:hsym), [two coordinate
words of length k](hyp:w,v) in which [every coordinate occurs equally often](hyp:hc) [give the same
ordered coordinate partial at that point](goal). -/
theorem wordPartialWithin_eq_of_count {d k : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (a : EuclideanSpace ℝ (Fin d))
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → EuclideanSpace ℝ (Fin d)),
      iteratedFDerivWithin ℝ k u S a (v ∘ σ) = iteratedFDerivWithin ℝ k u S a v)
    (w v : Fin k → Fin d) (hc : coordCount w = coordCount v) :
    wordPartialWithin S u w a = wordPartialWithin S u v a := by
  -- Use coordCount_eq_iff_perm, then evaluate hsym on coordinate directions.
  obtain ⟨σ, rfl⟩ := (coordCount_eq_iff_perm w v).mp hc
  simpa only [wordPartialWithin, Function.comp_def] using
    hsym σ (fun r => EuclideanSpace.single (v r) 1)

/-- For [a function on its derivative domain](hyp:S,u), [a degree m](hyp:m), and [a centre a and an
evaluation point x](hyp:a,x), if [for every order up to m the derivative within the domain at a is
unchanged by reordering its directions](hyp:hsym), then [the diagonal Taylor polynomial equals the
multi-index Taylor polynomial](goal). -/
theorem diagonal_taylor_eq_multiindex_taylor {d : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (m : ℕ) (a x : EuclideanSpace ℝ (Fin d))
    (hsym : ∀ k ≤ m, ∀ (σ : Equiv.Perm (Fin k))
      (v : Fin k → EuclideanSpace ℝ (Fin d)),
      iteratedFDerivWithin ℝ k u S a (v ∘ σ) = iteratedFDerivWithin ℝ k u S a v) :
    diagonalTaylor S u m a x = multiindexTaylor S u m a x := by
  -- At each order use the coordinate expansion, word_product_eq_count_product,
  -- and group_word_sum_by_count. word_fiber_card_mul_factorial cancels k!;
  -- combine the exact-order sums into the bounded-degree subtype sum.
  -- For factorial cancellation, cast the multiplicative fiber identity to ℝ
  -- and use positivity of both factorials. Do not cast natural division as
  -- unrestricted real division. For sortedWordOfOrder, eliminate κ.2 before
  -- comparing the Fin.cast-reindexed multilinear evaluation with coordinatePartial.
  -- Group MultiIndex d m by its order in Fin (m+1) using sum_fiberwise;
  -- each fiber is equivalent to ExactIndex d k.val. Fintype.sum_equiv
  -- transports the fiber sum, and Fin.sum_univ_eq_sum_range restores range notation.
  classical
  have horder (k : ℕ) (hk : k ≤ m) :
      (k.factorial : ℝ)⁻¹ * iteratedFDerivWithin ℝ k u S a (fun _ => x - a) =
        ∑ κ : ExactIndex d k,
          coordinatePartial S u κ.1 a / (multiFactorial κ.1 : ℝ) *
            centeredMonomial a x κ.1 := by
    rw [within_diagonal_derivative_coordinate_expansion]
    rw [group_word_sum_by_count (hF := by
      intro v w hc
      rw [word_product_eq_count_product v, word_product_eq_count_product w, hc,
        wordPartialWithin_eq_of_count S u a (hsym k hk) v w hc])]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro κ _
    have hsorted : wordPartialWithin S u (sortedWordOfOrder κ) a =
        coordinatePartial S u κ.1 a := by
      rcases κ with ⟨κ, hκ⟩
      subst k
      rfl
    have hcount : coordCount (sortedWordOfOrder κ) = κ.1 := by
      rcases κ with ⟨κ, hκ⟩
      subst k
      exact sortedWord_count κ
    rw [word_product_eq_count_product, hcount, hsorted]
    have hf : ((wordFiber k κ.1).card : ℝ) * (multiFactorial κ.1 : ℝ) =
        (k.factorial : ℝ) := by
      exact_mod_cast word_fiber_card_mul_factorial κ.1 κ.2
    have hkfac : (k.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have hκfac : (multiFactorial κ.1 : ℝ) ≠ 0 := by
      exact_mod_cast (multiFactorial_pos κ.1).ne'
    have hcancel : (k.factorial : ℝ)⁻¹ *
        ((k.factorial / multiFactorial κ.1 : ℕ) : ℝ) =
          (multiFactorial κ.1 : ℝ)⁻¹ := by
      rw [← word_fiber_card_eq_multinomial κ.1 κ.2]
      apply (mul_right_cancel₀ hκfac)
      rw [mul_assoc, hf, inv_mul_cancel₀ hkfac, inv_mul_cancel₀ hκfac]
    change (k.factorial : ℝ)⁻¹ *
        (((k.factorial / multiFactorial κ.1 : ℕ) : ℝ) *
          (centeredMonomial a x κ.1 * coordinatePartial S u κ.1 a)) = _
    rw [← mul_assoc, hcancel]
    simp only [div_eq_mul_inv]
    ring
  let order : MultiIndex d m → Fin (m + 1) :=
    fun κ => ⟨multiOrder κ.1, Nat.lt_succ_of_le κ.2⟩
  unfold diagonalTaylor multiindexTaylor
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← Finset.sum_fiberwise Finset.univ order]
  apply Finset.sum_congr rfl
  intro k _
  rw [horder k.val (Nat.le_of_lt_succ k.isLt)]
  rw [Finset.sum_subtype (p := fun κ : MultiIndex d m => order κ = k)
    (F := inferInstance)
    (Finset.univ.filter fun κ => order κ = k) (by intro κ; simp)
    (fun κ => taylorCoefficient S u a κ * centeredMonomial a x κ.1)]
  let e : {κ : MultiIndex d m // order κ = k} ≃ ExactIndex d k.val :=
    { toFun := fun κ => ⟨κ.1.1, congrArg Fin.val κ.2⟩
      invFun := fun κ =>
        ⟨⟨κ.1, κ.2.le.trans (Nat.le_of_lt_succ k.isLt)⟩,
          by apply Fin.ext; exact κ.2⟩
      left_inv := fun κ => by apply Subtype.ext; rfl
      right_inv := fun κ => by rfl }
  exact (Fintype.sum_equiv e _ _ (fun κ => by rfl)).symm

/-- For [a cube with centre b and side length H](hyp:b,H) that is [positive](hyp:hH), [a function
u](hyp:u) that is [m times continuously differentiable on the cube](hyp:hu), and [a centre
a](hyp:a) [in the cube](hyp:ha), [the degree-m diagonal Taylor polynomial of u within the cube
equals its degree-m multi-index Taylor polynomial](goal) at [every evaluation point](hyp:x). -/
theorem cube_diagonal_taylor_eq_multiindex {d m : ℕ}
    (b a x : EuclideanSpace ℝ (Fin d)) (H : ℝ) (hH : 0 < H)
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : ContDiffOn ℝ m u (centeredCube b H)) (ha : a ∈ centeredCube b H) :
    diagonalTaylor (centeredCube b H) u m a x =
      multiindexTaylor (centeredCube b H) u m a x := by
  -- Apply the algebraic conversion using euclidean_within_jet_perm,
  -- uniqueDiffOn_centeredCube, and centeredCube_subset_closure_interior.
  apply diagonal_taylor_eq_multiindex_taylor
  intro k hk σ v
  exact euclidean_within_jet_perm (uniqueDiffOn_centeredCube b H hH)
    (hu.of_le (by exact_mod_cast hk)) ha
    (centeredCube_subset_closure_interior b H hH ha) σ v

/-- For [a function on its derivative domain](hyp:S,u), [any degree](hyp:m), and [any
centre](hyp:a), [the multi-index Taylor polynomial evaluated at its own centre equals the
function's value there](goal). -/
theorem multiindexTaylor_center {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (m : ℕ) (a : EuclideanSpace ℝ (Fin d)) :
    multiindexTaylor S u m a a = u a := by
  -- Every nonzero count vector gives a zero centered monomial; the zero
  -- vector contributes the order-zero within derivative, which is u a.
  classical
  let zeroIndex : MultiIndex d m := ⟨fun _ => 0, by simp [multiOrder]⟩
  unfold multiindexTaylor
  rw [Finset.sum_eq_single zeroIndex]
  · have heval (k : ℕ) (hk : k = 0)
        (v : Fin k → EuclideanSpace ℝ (Fin d)) :
        iteratedFDerivWithin ℝ k u S a v = u a := by
      subst k
      exact iteratedFDerivWithin_zero_apply v
    have hp : coordinatePartial S u (fun _ => 0) a = u a :=
      heval _ (by simp [multiOrder]) _
    simp [taylorCoefficient, zeroIndex, hp, multiFactorial, centeredMonomial]
  · intro κ _ hκ
    have hpos : ∃ i, κ.1 i ≠ 0 := by
      by_contra h
      apply hκ
      apply Subtype.ext
      funext i
      simpa using not_exists.mp h i
    obtain ⟨i, hi⟩ := hpos
    have hz : centeredMonomial a a κ.1 = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [hz, mul_zero]
  · simp

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

