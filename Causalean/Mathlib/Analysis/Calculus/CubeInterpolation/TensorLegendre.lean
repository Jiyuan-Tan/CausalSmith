module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Legendre

/-!
# Tensorized inverse Legendre realization

The finite triangular inverse matrix realizes centered coordinate monomials
and arbitrary polynomials of total degree at most two. All coefficients are
explicit finite sums. Natural powers of the cube side control every matrix
entry; no coefficient bound or representation is a hypothesis.
-/

@[expose] public section

open scoped BigOperators
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The [scaled tensor Legendre entry](goal) for [a centre a](hyp:a), [a side length h](hyp:h), [a
multi-index](hyp:κ), and [a point x](hyp:x) is [the product over coordinates of the normalized
Legendre entry whose degree is that coordinate's count, evaluated at the coordinate of x − a
divided by h](step:1). -/
def scaledTensorLegendre {d m : ℕ} (a : EuclideanSpace ℝ (Fin d)) (h : ℝ)
    (κ : MultiIndex d m) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, legendreEntry (κ.1 i) ((x i - a i) / h)

/-- The [tensor inverse coefficient](goal) at [scale h](hyp:h) for [an input and an output vector
of coordinate degrees](hyp:α,β) is [the product over coordinates of the one-dimensional inverse
Legendre entries for the matching pair of degrees](step:1). -/
def inverseTensorCoeff {d : ℕ} (h : ℝ) (α β : Fin d → ℕ) : ℝ :=
  ∏ i, inverseEntry h (α i) (β i)

/-- For [any scale](hyp:h), [an input multi-index of total
order at most m](hyp:α), and [an output vector of degrees](hyp:β), if [some output degree exceeds
the input degree in the same coordinate](hyp:hβ), then [the tensor inverse coefficient is
zero](goal). -/
theorem inverseTensorCoeff_zero {d m : ℕ} (h : ℝ)
    (α : MultiIndex d m) (β : Fin d → ℕ) (hβ : ¬ ∀ i, β i ≤ α.1 i) :
    inverseTensorCoeff h α.1 β = 0 := by
  -- Find an offending coordinate and use inverseEntry_above in prod_eq_zero.
  classical
  push Not at hβ
  obtain ⟨i, hi⟩ := hβ
  unfold inverseTensorCoeff
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (inverseEntry_above h _ _ hi)

/-- For [a degree bound m at most two](hyp:hm), [a scale h](hyp:h) that is [positive](hyp:hh), [an
input multi-index of total order at most m](hyp:α), and [any output vector of degrees](hyp:β), [the
tensor inverse coefficient is at most h raised to the total order of the input multi-index, in
absolute value](goal). -/
theorem inverseTensorCoeff_abs_le {d m : ℕ} (hm : m ≤ 2)
    (h : ℝ) (hh : 0 < h) (α : MultiIndex d m) (β : Fin d → ℕ) :
    |inverseTensorCoeff h α.1 β| ≤ h ^ multiOrder α.1 := by
  -- Apply inverseEntry_abs_le coordinatewise and prod_pow_eq_pow_sum.
  unfold inverseTensorCoeff
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ i, h ^ α.1 i := Finset.prod_le_prod
      (fun i _ => abs_nonneg _) (fun i _ =>
        inverseEntry_abs_le h hh _ _ ((coordinate_le_order α.1 i).trans (α.2.trans hm)))
    _ = h ^ multiOrder α.1 := Finset.prod_pow_eq_pow_sum _ _ _

/-- For [a degree bound m at most two](hyp:hm), [a centre a and a point x](hyp:a,x), [a side length
h](hyp:h) that is [positive](hyp:hh), and [a multi-index of total order at most m](hyp:α), [the
centred monomial with those exponents equals the sum, over all multi-indices of total order at most
m, of the tensor inverse coefficient times the scaled tensor Legendre entry](goal). -/
theorem degree_two_monomial_scaledLegendre {d m : ℕ} (hm : m ≤ 2)
    (a x : EuclideanSpace ℝ (Fin d)) (h : ℝ) (hh : 0 < h)
    (α : MultiIndex d m) :
    centeredMonomial a x α.1 = ∑ β : MultiIndex d m,
      inverseTensorCoeff h α.1 β.1 * scaledTensorLegendre a h β x := by
  -- Substitute t=(x_i-a_i)/h into monomial_inverse_legendre, expand the
  -- finite product of sums, and discard indices above α coordinatewise.
  -- Triangularity proves total-degree preservation without any tensor box
  -- relaxation of the index set. The identity holds for all x, not just a cube.
  -- Mathlib Fintype.prod_sum expands the coordinate Fin 3 sums. Compare
  -- the resulting Fin d → Fin 3 box with MultiIndex d m by zero-extension:
  -- nonzero terms satisfy β≤α coordinatewise, hence multiOrder β≤m.
  -- Preserve this total-degree restriction; the full box is not the API index.
  classical
  -- Embed the total-degree simplex into the coordinate box without enlarging the API.
  let encode : MultiIndex d m → (Fin d → Fin 3) := fun β i =>
    ⟨β.1 i, by
      have := (coordinate_le_order β.1 i).trans (β.2.trans hm)
      omega⟩
  have encode_inj : Function.Injective encode := by
    intro β γ he
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun he i)
  let term : (Fin d → Fin 3) → ℝ := fun b =>
    inverseTensorCoeff h α.1 (fun i => (b i).val) *
      ∏ i, legendreEntry (b i).val ((x i - a i) / h)
  have outside (b : Fin d → Fin 3)
      (hb : b ∉ Finset.univ.image encode) : term b = 0 := by
    have hnot : ¬ ∀ i, (b i).val ≤ α.1 i := by
      intro hle
      have horder : multiOrder (fun i => (b i).val) ≤ m :=
        (Finset.sum_le_sum (fun i _ => hle i)).trans α.2
      let β : MultiIndex d m := ⟨fun i => (b i).val, horder⟩
      apply hb
      refine Finset.mem_image.mpr ⟨β, Finset.mem_univ _, ?_⟩
      funext i
      apply Fin.ext
      rfl
    simp only [term, inverseTensorCoeff_zero h α _ hnot, zero_mul]
  calc
    centeredMonomial a x α.1 =
        ∏ i, ∑ j : Fin 3, inverseEntry h (α.1 i) j.val *
          legendreEntry j.val ((x i - a i) / h) := by
      apply Finset.prod_congr rfl
      intro i _
      have hi := monomial_inverse_legendre (α.1 i)
        ((coordinate_le_order α.1 i).trans (α.2.trans hm)) h ((x i - a i) / h)
      simpa only [mul_div_cancel₀ _ hh.ne'] using hi
    _ = ∑ b : Fin d → Fin 3, ∏ i, inverseEntry h (α.1 i) (b i).val *
        legendreEntry (b i).val ((x i - a i) / h) := Fintype.prod_sum _
    _ = ∑ b : Fin d → Fin 3, term b := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [term, inverseTensorCoeff, Finset.prod_mul_distrib]
    _ = ∑ b ∈ Finset.univ.image encode, term b := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _)
        (fun b _ hb => outside b hb)
    _ = ∑ β : MultiIndex d m,
        inverseTensorCoeff h α.1 β.1 * scaledTensorLegendre a h β x := by
      rw [Finset.sum_image (fun β _ γ _ he => encode_inj he)]
      rfl

/-- The [Legendre coefficients](goal) at [scale h](hyp:h) of [a vector of centred-monomial
coefficients](hyp:c) are given [for each output multi-index by the sum over input multi-indices of
the monomial coefficient times the tensor inverse coefficient](step:1). -/
def legendreCoefficients {d m : ℕ} (h : ℝ) (c : MultiIndex d m → ℝ) :
    MultiIndex d m → ℝ := fun β => ∑ α, c α * inverseTensorCoeff h α.1 β.1

/-- The [scaled Legendre polynomial](goal) with [centre a](hyp:a), [side length h](hyp:h), and
[coefficient vector](hyp:θ), evaluated at [a point x](hyp:x), is [the sum over multi-indices of the
scaled tensor Legendre entry times its coefficient](step:1). -/
def legendrePolynomial {d m : ℕ} (a : EuclideanSpace ℝ (Fin d)) (h : ℝ)
    (θ : MultiIndex d m → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ κ, scaledTensorLegendre a h κ x * θ κ

/-- For [a degree bound m at most two](hyp:hm), [a centre a and a point x](hyp:a,x), [a side length
h](hyp:h) that is [positive](hyp:hh), and [a vector of monomial coefficients](hyp:c), [the scaled
Legendre polynomial with the transformed coefficients equals the centred polynomial with the
original coefficients, evaluated at x](goal). -/
theorem legendreCoefficients_realize {d m : ℕ} (hm : m ≤ 2)
    (a x : EuclideanSpace ℝ (Fin d)) (h : ℝ) (hh : 0 < h)
    (c : MultiIndex d m → ℝ) :
    legendrePolynomial a h (legendreCoefficients h c) x =
      ∑ α, c α * centeredMonomial a x α.1 := by
  -- Exchange the two finite sums and use the monomial realization.
  classical
  unfold legendrePolynomial legendreCoefficients
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [degree_two_monomial_scaledLegendre hm a x h hh α, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  ring

/-- In [a dimension](hyp:d) and for [a degree bound m](hyp:m) [at most two](hyp:hm), [there is a
positive constant C such that, for every side length h that is positive and at most one half and
every coefficient vector whose entries are bounded in absolute value by a nonnegative L, the
Euclidean norm of the Legendre coefficients is at most C times L](goal). -/
theorem legendreCoefficients_l2_bound (d m : ℕ) (hm : m ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h L : ℝ) (c : MultiIndex d m → ℝ),
      0 < h → h ≤ 1 / 2 → 0 ≤ L → (∀ α, |c α| ≤ L) →
      Real.sqrt (∑ β, legendreCoefficients h c β ^ 2) ≤ C * L := by
  -- Let N be card (MultiIndex d m). Every matrix entry is ≤1 because
  -- |entry|≤h^|α| and h≤1; thus |θβ|≤N L and the norm ≤sqrt(N) N L.
  -- Adding one to sqrt(N) N makes the bound positive without a dimension side condition.
  classical
  let N : ℝ := Fintype.card (MultiIndex d m)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨Real.sqrt N * N + 1, by positivity, ?_⟩
  intro h L c hh hhhalf hL hc
  have hentry (α β : MultiIndex d m) : |inverseTensorCoeff h α.1 β.1| ≤ 1 :=
    (inverseTensorCoeff_abs_le hm h hh α β.1).trans
      (pow_le_one₀ hh.le (by linarith))
  have hθ (β : MultiIndex d m) : |legendreCoefficients h c β| ≤ N * L := by
    unfold legendreCoefficients
    calc
      _ ≤ ∑ α, |c α * inverseTensorCoeff h α.1 β.1| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _α : MultiIndex d m, L := Finset.sum_le_sum (fun α _ => by
        rw [abs_mul]
        simpa using mul_le_mul (hc α) (hentry α β) (abs_nonneg _) hL)
      _ = N * L := by simp [N]
  have hsum : (∑ β, legendreCoefficients h c β ^ 2) ≤ N * (N * L) ^ 2 := by
    calc
      _ ≤ ∑ _β : MultiIndex d m, (N * L) ^ 2 := Finset.sum_le_sum (fun β _ => by
        simpa only [sq_abs] using
          pow_le_pow_left₀ (abs_nonneg _) (hθ β) 2)
      _ = N * (N * L) ^ 2 := by simp [N]
  calc
    _ ≤ Real.sqrt (N * (N * L) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt N * N * L := by
      rw [Real.sqrt_mul hN, Real.sqrt_sq (mul_nonneg hN hL)]
      ring
    _ ≤ (Real.sqrt N * N + 1) * L := by nlinarith

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

