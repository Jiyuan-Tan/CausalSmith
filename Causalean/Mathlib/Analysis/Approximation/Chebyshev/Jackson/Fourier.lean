module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Reciprocal

/-!
# Finite Fourier reconstruction and localized Jackson packets

The generic summation-by-parts statement uses a finitely supported complex
sequence on `ℤ`. The packet statements specialize it to the two high-frequency
shifts of the normalized order-four Jackson kernel.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

open MeasureTheory
open scoped BigOperators

/-- The [Fourier series](goal) of [a complex sequence indexed by the integers](hyp:a) at [a real
angle u](hyp:u) is [the sum over all integers j of the j-th term of the sequence times the complex
exponential of i j u](step:1); it is a Fourier polynomial when the sequence has finite support. -/
noncomputable def finiteFourier (a : ℤ → ℂ) (u : ℝ) : ℂ :=
  ∑' j : ℤ, a j * Complex.exp (Complex.I * (j : ℂ) * (u : ℂ))

/-- The [second forward difference](goal) of [a complex sequence indexed by the integers](hyp:a) at
[an index j](hyp:j) is [the term at j + 2 minus twice the term at j + 1 plus the term at
j](step:1). -/
def complexDelta2 (a : ℤ → ℂ) (j : ℤ) : ℂ :=
  a (j + 2) - 2 * a (j + 1) + a j

/-- For [a complex sequence indexed by the integers](hyp:a) [with finite support](hyp:ha) and [any
real angle u](hyp:u), [the Fourier series of the second forward difference of the sequence equals
the square of (the complex exponential of −i u, minus one) times the Fourier series of the sequence
itself](goal). -/
theorem finiteFourier_twice_summation_by_parts (a : ℤ → ℂ)
    (ha : Function.HasFiniteSupport a) (u : ℝ) :
    finiteFourier (complexDelta2 a) u =
      (Complex.exp (-Complex.I * (u : ℂ)) - 1) ^ 2 * finiteFourier a u := by
  let z : ℂ := Complex.I * (u : ℂ)
  let F : ℤ → ℂ := fun j => a j * Complex.exp ((j : ℂ) * z)
  have hs (k : ℤ) : Summable (fun j : ℤ =>
      a (j + k) * Complex.exp ((j : ℂ) * z)) := by
    apply summable_of_hasFiniteSupport
    apply Function.HasFiniteSupport.mul_left
    exact ha.fun_comp_of_injective (Equiv.addRight k).injective
  have hshift (k : ℤ) :
      (∑' j : ℤ, a (j + k) * Complex.exp ((j : ℂ) * z)) =
        Complex.exp (-(k : ℂ) * z) * (∑' j : ℤ, F j) := by
    calc
      _ = ∑' j : ℤ, Complex.exp (-(k : ℂ) * z) * F (j + k) := by
        congr 1
        funext j
        dsimp [F]
        have he : Complex.exp (-(k : ℂ) * z) *
            Complex.exp (((j + k : ℤ) : ℂ) * z) =
              Complex.exp ((j : ℂ) * z) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        calc
          a (j + k) * Complex.exp ((j : ℂ) * z) =
              a (j + k) * (Complex.exp (-(k : ℂ) * z) *
                Complex.exp (((j + k : ℤ) : ℂ) * z)) := by rw [he]
          _ = _ := by ring
      _ = Complex.exp (-(k : ℂ) * z) *
          (∑' j : ℤ, F (j + k)) := by rw [tsum_mul_left]
      _ = _ := by
        congr 1
        simpa [Equiv.addRight] using (Equiv.tsum_eq (Equiv.addRight k) F)
  have hexp : Complex.exp (-(2 : ℂ) * z) =
      Complex.exp (-z) ^ 2 := by
    rw [show -(2 : ℂ) * z = -z + -z by ring, Complex.exp_add]
    ring
  have hz : -z = -Complex.I * (u : ℂ) := by simp [z]
  have hphase (j : ℤ) : Complex.I * (j : ℂ) * (u : ℂ) = (j : ℂ) * z := by
    dsimp [z]
    ring
  simp only [finiteFourier, complexDelta2]
  simp_rw [hphase]
  change (∑' j : ℤ, (a (j + 2) - 2 * a (j + 1) + a j) *
      Complex.exp ((j : ℂ) * z)) =
    (Complex.exp (-Complex.I * (u : ℂ)) - 1) ^ 2 * (∑' j : ℤ, F j)
  simp only [add_mul, sub_mul]
  rw [Summable.tsum_add, Summable.tsum_sub]
  · rw [hshift 2]
    simp only [mul_assoc]
    rw [tsum_mul_left, hshift 1]
    change Complex.exp (-((2 : ℤ) : ℂ) * z) * (∑' j : ℤ, F j) -
      2 * (Complex.exp (-((1 : ℤ) : ℂ) * z) * (∑' j : ℤ, F j)) +
      (∑' j : ℤ, F j) =
        (Complex.exp (-Complex.I * (u : ℂ)) - 1) ^ 2 * (∑' j : ℤ, F j)
    norm_num only [Int.cast_ofNat, one_mul]
    rw [hexp]
    ring_nf
    rw [hz]
    ring
  · exact hs 2
  · simpa only [mul_assoc, ← mul_assoc] using (hs 1).mul_left (2 : ℂ)
  · exact (hs 2).sub (by
      simpa only [mul_assoc, ← mul_assoc] using (hs 1).mul_left (2 : ℂ))
  · simpa only [add_zero] using hs 0

/-- The [torus distance](goal) of [a real angle](hyp:u) is [the smallest distance from the angle to
an integer multiple of 2π](step:1). -/
noncomputable def torusDistance (u : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ j : ℤ, r = |u - 2 * Real.pi * j|}

/-- The [plus-shifted antiderivative coefficient](goal) of [order N](hyp:N) at [an integer
frequency j](hyp:j) is [the normalized Jackson coefficient at j divided by the square of 4N +
j](step:1). -/
noncomputable def packetCoeffPlus (N : ℕ) (j : ℤ) : ℝ :=
  weightedCoeff N 1 j

/-- The [minus-shifted antiderivative coefficient](goal) of [order N](hyp:N) at [an integer
frequency j](hyp:j) is [the normalized Jackson coefficient at j divided by the square of 4N −
j](step:1). -/
noncomputable def packetCoeffMinus (N : ℕ) (j : ℤ) : ℝ :=
  weightedCoeff N (-1) j

/-- The [oscillatory Jackson packet](goal) of [order N](hyp:N) at [an angle u](hyp:u) is [the
scaled Jackson kernel at u times the cosine of 4N u](step:1). -/
noncomputable def packetOscillation (N : ℕ) (u : ℝ) : ℝ :=
  kernel N u * Real.cos ((4 * N : ℝ) * u)

/-- The [packet antiderivative](goal) of [order N](hyp:N) at [an angle u](hyp:u) is [minus one half
times the sum, over integer frequencies j between −(2N − 2) and 2N − 2, of the plus-shifted
coefficient times the cosine of (4N + j) u plus the minus-shifted coefficient times the cosine of
(4N − j) u](step:1); it is the candidate twice antiderivative of the oscillatory Jackson packet. -/
noncomputable def packetAntideriv (N : ℕ) (u : ℝ) : ℝ :=
  -(1 / 2 : ℝ) *
    ∑ j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ),
      (packetCoeffPlus N j * Real.cos (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) +
       packetCoeffMinus N j * Real.cos (((4 * (N : ℤ) - j : ℤ) : ℝ) * u))

/-- For [an order N](hyp:N) that is [positive](hyp:hN) and [any angle u](hyp:u), [the scaled
Jackson kernel equals the cosine series over frequencies j between −(2N − 2) and 2N − 2 with the
normalized Jackson coefficients](goal). -/
theorem packet_kernel_reconstruction (N : ℕ) (hN : 0 < N) (u : ℝ) :
    kernel N u =
      ∑ j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ),
        normalizedCoeff N j * Real.cos ((j : ℝ) * u) :=
  kernel_fourier N hN u

/-- For [an order N](hyp:N) that is [at least two](hyp:hN), [the packet antiderivative integrates
to zero over the period from −π to π](goal). -/
theorem packet_zero_mean (N : ℕ) (hN : 2 ≤ N) :
    (∫ u in Set.Icc (-Real.pi) Real.pi, packetAntideriv N u) = 0 := by
  have hcos (k : ℤ) (hk : k ≠ 0) :
      (∫ u in Set.Icc (-Real.pi) Real.pi, Real.cos ((k : ℝ) * u)) = 0 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi)
        (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [intervalIntegral.integral_comp_mul_left Real.cos hk0, integral_cos]
    simp
  have hfreq (j : ℤ)
      (hj : j ∈ Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ)) :
      4 * (N : ℤ) + j ≠ 0 ∧ 4 * (N : ℤ) - j ≠ 0 := by
    have hj' := Finset.mem_Icc.mp hj
    constructor <;> omega
  have hInt (k : ℤ) :
      IntegrableOn (fun u : ℝ => Real.cos ((k : ℝ) * u))
        (Set.Icc (-Real.pi) Real.pi) := by
    exact (show Continuous (fun u : ℝ => Real.cos ((k : ℝ) * u)) by fun_prop)
      |>.continuousOn.integrableOn_compact isCompact_Icc
  unfold packetAntideriv
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
  · apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j hj
    rw [MeasureTheory.integral_add ((hInt _).const_mul _) ((hInt _).const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    obtain ⟨hp, hm⟩ := hfreq j hj
    rw [hcos _ hp, hcos _ hm]
    ring
  · intro j hj
    exact ((hInt _).const_mul _).add ((hInt _).const_mul _)

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

