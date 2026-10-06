module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Fourier

/-!
# Twice differentiating the Jackson packet polynomial

The finite reciprocal-weighted cosine series is a twice antiderivative of
the modulated Jackson kernel.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

/-- For [an order N](hyp:N) that is [at least two](hyp:hN) and [any real angle u](hyp:u), [the
second derivative of the packet antiderivative at u equals the oscillatory Jackson packet at
u](goal). -/
theorem packet_twice_deriv (N : ℕ) (hN : 2 ≤ N) (u : ℝ) :
    deriv (deriv (packetAntideriv N)) u = packetOscillation N u := by
  let S : Finset ℤ := Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ)
  let p (j : ℤ) : ℝ := ((4 * (N : ℤ) + j : ℤ) : ℝ)
  let m (j : ℤ) : ℝ := ((4 * (N : ℤ) - j : ℤ) : ℝ)
  let a (j : ℤ) : ℝ := packetCoeffPlus N j
  let b (j : ℤ) : ℝ := packetCoeffMinus N j
  have hcos (c k x : ℝ) :
      HasDerivAt (fun y : ℝ => c * Real.cos (k * y))
        (-c * k * Real.sin (k * x)) x := by
    convert ((Real.hasDerivAt_cos (k * x)).comp x
      ((hasDerivAt_id x).const_mul k)).const_mul c using 1 <;>
      first | rfl | ring
  have hsin (c k x : ℝ) :
      HasDerivAt (fun y : ℝ => c * Real.sin (k * y))
        (c * k * Real.cos (k * x)) x := by
    convert ((Real.hasDerivAt_sin (k * x)).comp x
      ((hasDerivAt_id x).const_mul k)).const_mul c using 1 <;>
      first | rfl | ring
  have hfirst (x : ℝ) :
      deriv (packetAntideriv N) x =
        (1 / 2 : ℝ) * ∑ j ∈ S,
          (a j * p j * Real.sin (p j * x) +
           b j * m j * Real.sin (m j * x)) := by
    have ht (j : ℤ) : HasDerivAt
        (fun y : ℝ => a j * Real.cos (p j * y) + b j * Real.cos (m j * y))
        (-(a j) * p j * Real.sin (p j * x) -
         b j * m j * Real.sin (m j * x)) x := by
      convert (hcos (a j) (p j) x).add (hcos (b j) (m j) x) using 1 <;>
        first | rfl | ring
    have hs := (HasDerivAt.fun_sum (u := S) (fun j hj => ht j)).const_mul (-1 / 2 : ℝ)
    have hs' := hs.deriv
    convert hs' using 1
    · congr 1
      funext y
      simp only [packetAntideriv, S, a, b, p, m]
      ring
    · simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
  have hsecond : HasDerivAt
      (fun x : ℝ => (1 / 2 : ℝ) * ∑ j ∈ S,
        (a j * p j * Real.sin (p j * x) +
         b j * m j * Real.sin (m j * x)))
      ((1 / 2 : ℝ) * ∑ j ∈ S,
        (a j * p j ^ 2 * Real.cos (p j * u) +
         b j * m j ^ 2 * Real.cos (m j * u))) u := by
    have ht (j : ℤ) : HasDerivAt
        (fun x : ℝ => a j * p j * Real.sin (p j * x) +
          b j * m j * Real.sin (m j * x))
        (a j * p j ^ 2 * Real.cos (p j * u) +
         b j * m j ^ 2 * Real.cos (m j * u)) u := by
      convert (hsin (a j * p j) (p j) u).add
        (hsin (b j * m j) (m j) u) using 1 <;>
        first | rfl | ring
    convert (HasDerivAt.fun_sum (u := S) (fun j hj => ht j)).const_mul (1 / 2 : ℝ) using 1
  rw [show deriv (packetAntideriv N) = fun x =>
      (1 / 2 : ℝ) * ∑ j ∈ S,
        (a j * p j * Real.sin (p j * x) +
         b j * m j * Real.sin (m j * x)) from funext hfirst]
  rw [hsecond.deriv]
  have hcancel (j : ℤ) (hj : j ∈ S) :
      a j * p j ^ 2 = normalizedCoeff N j ∧
      b j * m j ^ 2 = normalizedCoeff N j := by
    have hj' : -((2 * N - 2 : ℕ) : ℤ) ≤ j ∧ j ≤ ((2 * N - 2 : ℕ) : ℤ) :=
      Finset.mem_Icc.mp hj
    have hp : p j ≠ 0 := by
      dsimp [p]
      have : 4 * (N : ℤ) + j ≠ 0 := by omega
      exact_mod_cast this
    have hm : m j ≠ 0 := by
      dsimp [m]
      have : 4 * (N : ℤ) - j ≠ 0 := by omega
      exact_mod_cast this
    constructor
    · have hden : 4 * (N : ℝ) + (1 : ℝ) * (j : ℝ) = p j := by
        dsimp [p]; push_cast; ring
      change normalizedCoeff N j * (1 / (4 * (N : ℝ) + 1 * (j : ℝ)) ^ 2) *
        p j ^ 2 = normalizedCoeff N j
      rw [hden]
      field_simp
    · have hden : 4 * (N : ℝ) + (-1 : ℝ) * (j : ℝ) = m j := by
        dsimp [m]; push_cast; ring
      change normalizedCoeff N j * (1 / (4 * (N : ℝ) + -1 * (j : ℝ)) ^ 2) *
        m j ^ 2 = normalizedCoeff N j
      rw [hden]
      field_simp
  have htrig (j : ℤ) :
      Real.cos (p j * u) + Real.cos (m j * u) =
        2 * Real.cos ((j : ℝ) * u) * Real.cos ((4 * N : ℝ) * u) := by
    have hp : p j * u = (4 * N : ℝ) * u + (j : ℝ) * u := by
      dsimp [p]; push_cast; ring
    have hm : m j * u = (4 * N : ℝ) * u - (j : ℝ) * u := by
      dsimp [m]; push_cast; ring
    rw [hp, hm, Real.cos_add, Real.cos_sub]
    ring
  calc
    (1 / 2 : ℝ) * ∑ j ∈ S,
        (a j * p j ^ 2 * Real.cos (p j * u) +
         b j * m j ^ 2 * Real.cos (m j * u)) =
      (∑ j ∈ S, normalizedCoeff N j * Real.cos ((j : ℝ) * u)) *
        Real.cos ((4 * N : ℝ) * u) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          obtain ⟨hp, hm⟩ := hcancel j hj
          rw [hp, hm]
          rw [← mul_add, htrig]
          ring
    _ = packetOscillation N u := by
      rw [← packet_kernel_reconstruction N (by omega : 0 < N) u]
      rfl

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

