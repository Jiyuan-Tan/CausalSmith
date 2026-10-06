module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Kernel
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Center
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Derivative
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Localization
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Support
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Localized high-frequency Jackson packet
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators

/-- For [the displayed parameters](hyp:N,u), [packetKernel](goal) is the object specified by this definition. -/
noncomputable def packetKernel (N : ℕ) (u : ℝ) : ℝ :=
  2 * Real.pi * Causalean.Mathlib.Analysis.JacksonApproximation.jackson N u

/-- For [the displayed parameters](hyp:N,j), [kernelCoeff](goal) is the object specified by this definition. -/
noncomputable def kernelCoeff (N : ℕ) (j : ℤ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ u in Set.Icc (-Real.pi) Real.pi,
      packetKernel N u * Real.cos (j * u)

/-- For [the displayed parameters](hyp:N,j), [packetCoeffPlus](goal) is the object specified by this definition. -/
noncomputable def packetCoeffPlus (N : ℕ) (j : ℤ) : ℝ :=
  if |j| ≤ (2 * N - 2 : ℕ) then
    kernelCoeff N j / ((4 * (N : ℤ) + j : ℤ) : ℝ) ^ 2
  else 0

/-- For [the displayed parameters](hyp:N,j), [packetCoeffMinus](goal) is the object specified by this definition. -/
noncomputable def packetCoeffMinus (N : ℕ) (j : ℤ) : ℝ :=
  if |j| ≤ (2 * N - 2 : ℕ) then
    kernelCoeff N j / ((4 * (N : ℤ) - j : ℤ) : ℝ) ^ 2
  else 0

/-- For [the displayed parameters](hyp:N,u), [packetOscillation](goal) is the object specified by this definition. -/
noncomputable def packetOscillation (N : ℕ) (u : ℝ) : ℝ :=
  packetKernel N u * Real.cos ((4 * N : ℝ) * u)

/-- For [the displayed parameters](hyp:N,u), [packetAntideriv](goal) is the object specified by this definition. -/
noncomputable def packetAntideriv (N : ℕ) (u : ℝ) : ℝ :=
  -(1 / 2 : ℝ) *
    ∑ j ∈ Finset.Icc (-(2 * (N : ℤ) - 2)) (2 * (N : ℤ) - 2),
      (packetCoeffPlus N j * Real.cos (((4 * (N : ℤ) + j : ℤ) : ℝ) * u) +
       packetCoeffMinus N j * Real.cos (((4 * (N : ℤ) - j : ℤ) : ℝ) * u))

/-- For [the displayed parameters](hyp:u), [torusDistance](goal) is the object specified by this definition. -/
noncomputable def torusDistance (u : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ j : ℤ, r = |u - 2 * Real.pi * j|}

private def secondDiff (a : ℤ → ℝ) (j : ℤ) : ℝ :=
  a (j + 2) - 2 * a (j + 1) + a j

-- @node: secondDiff_mul
private lemma secondDiff_mul (f q : ℤ → ℝ) (j : ℤ) :
    secondDiff (fun k => f k * q k) j =
      f (j + 2) * secondDiff q j +
        ((f (j + 2) - f (j + 1)) + (f (j + 1) - f j)) * (q (j + 1) - q j) +
        q (j + 1) * secondDiff f j := by
  simp only [secondDiff]
  ring

-- @node: summable_abs_secondDiff_of_interval_support
private lemma summable_abs_secondDiff_of_interval_support (a : ℤ → ℝ) (B : ℤ)
    (ha : ∀ j : ℤ, j ∉ Finset.Icc (-B) B → a j = 0) :
    Summable (fun j : ℤ => |secondDiff a j|) := by
  apply summable_of_hasFiniteSupport
  refine (Set.finite_Icc (-(B + 2)) B).subset ?_
  intro j hj
  simp only [Function.mem_support] at hj
  simp only [Set.mem_Icc]
  by_contra hjbounds
  by_cases hjlow : j < -(B + 2)
  · have h0 : a j = 0 := ha j (by simp only [Finset.mem_Icc]; omega)
    have h1 : a (j + 1) = 0 := ha (j + 1) (by simp only [Finset.mem_Icc]; omega)
    have h2 : a (j + 2) = 0 := ha (j + 2) (by simp only [Finset.mem_Icc]; omega)
    exact hj (by simp [secondDiff, h0, h1, h2])
  · have hjhigh : B < j := by
      have hjlower : -(B + 2) ≤ j := le_of_not_gt hjlow
      by_contra hn
      exact hjbounds ⟨hjlower, le_of_not_gt hn⟩
    have h0 : a j = 0 := ha j (by simp only [Finset.mem_Icc]; omega)
    have h1 : a (j + 1) = 0 := ha (j + 1) (by simp only [Finset.mem_Icc]; omega)
    have h2 : a (j + 2) = 0 := ha (j + 2) (by simp only [Finset.mem_Icc]; omega)
    exact hj (by simp [secondDiff, h0, h1, h2])

-- @node: packetKernel_normalized_integral
/-- In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN), the [stated conclusion](goal) holds. -/
lemma packetKernel_normalized_integral (N : ℕ) (hN : 0 < N) :
    (∫ u in Set.Icc (-Real.pi) Real.pi,
      packetKernel N u / (2 * Real.pi)) = 1 := by
  have hden : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  convert Causalean.Mathlib.Analysis.JacksonApproximation.jackson_integral_eq_one N hN using 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  simp only [packetKernel]
  field_simp

-- @node: packetKernel_zero_eq
private lemma packetKernel_zero_eq (N : ℕ) (hN : 0 < N) :
    packetKernel N 0 =
      3 * (N : ℝ) ^ 3 / (2 * (N : ℝ) ^ 2 + 1) := by
  unfold packetKernel Causalean.Mathlib.Analysis.JacksonApproximation.jackson
  rw [Causalean.Mathlib.Analysis.JacksonApproximation.jraw_eq_of_sin_eq_zero N (by simp),
    Causalean.Mathlib.Analysis.JacksonApproximation.jrawMass_eq N hN]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

-- @node: packetKernel_zero_bounds
private lemma packetKernel_zero_bounds (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ≤ packetKernel N 0 ∧ packetKernel N 0 ≤ (3 / 2 : ℝ) * N := by
  rw [packetKernel_zero_eq N hN]
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < 2 * (N : ℝ) ^ 2 + 1 := by positivity
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  · apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg (N : ℝ)]

-- @node: packetCoeffPlus_secondDiff_summable
private lemma packetCoeffPlus_secondDiff_summable (N : ℕ) :
    Summable fun j : ℤ =>
      |packetCoeffPlus N (j + 2) - 2 * packetCoeffPlus N (j + 1) +
        packetCoeffPlus N j| := by
  change Summable (fun j : ℤ => |secondDiff (packetCoeffPlus N) j|)
  apply summable_abs_secondDiff_of_interval_support
      (packetCoeffPlus N) ((2 * N - 2 : ℕ) : ℤ)
  intro j hj
  simp only [packetCoeffPlus]
  split_ifs with h
  · exfalso
    apply hj
    simp only [Finset.mem_Icc]
    exact abs_le.mp h
  · rfl

-- @node: packetCoeffMinus_secondDiff_summable
private lemma packetCoeffMinus_secondDiff_summable (N : ℕ) :
    Summable fun j : ℤ =>
      |packetCoeffMinus N (j + 2) - 2 * packetCoeffMinus N (j + 1) +
        packetCoeffMinus N j| := by
  change Summable (fun j : ℤ => |secondDiff (packetCoeffMinus N) j|)
  apply summable_abs_secondDiff_of_interval_support
      (packetCoeffMinus N) ((2 * N - 2 : ℕ) : ℤ)
  intro j hj
  simp only [packetCoeffMinus]
  split_ifs with h
  · exfalso
    apply hj
    simp only [Finset.mem_Icc]
    exact abs_le.mp h
  · rfl

private lemma kernelCoeff_eq_staged (N : ℕ) (hN : 0 < N) (j : ℤ) :
    kernelCoeff N j =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.normalizedCoeff N j := by
  exact
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.kernelCoeff_eq_normalizedCoeff
      N hN j

private lemma packetCoeffPlus_eq_staged (N : ℕ) (hN : 0 < N) (j : ℤ) :
    packetCoeffPlus N j =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packetCoeffPlus N j := by
  simp only [packetCoeffPlus,
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packetCoeffPlus,
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.weightedCoeff,
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.reciprocalSquare]
  split_ifs with hj
  · rw [kernelCoeff_eq_staged N hN j]
    push_cast
    ring
  · have hfar : ((2 * N - 2 : ℕ) : ℤ) < |j| := by omega
    rw [Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.normalizedCoeff_support
      N j hfar]
    simp

private lemma packetCoeffMinus_eq_staged (N : ℕ) (hN : 0 < N) (j : ℤ) :
    packetCoeffMinus N j =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packetCoeffMinus N j := by
  simp only [packetCoeffMinus,
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packetCoeffMinus,
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.weightedCoeff,
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.reciprocalSquare]
  split_ifs with hj
  · rw [kernelCoeff_eq_staged N hN j]
    push_cast
    ring
  · have hfar : ((2 * N - 2 : ℕ) : ℤ) < |j| := by omega
    rw [Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.normalizedCoeff_support
      N j hfar]
    simp

private lemma packetAntideriv_eq_staged (N : ℕ) (hN : 0 < N) (u : ℝ) :
    packetAntideriv N u =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packetAntideriv N u := by
  unfold packetAntideriv
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packetAntideriv
  simp_rw [packetCoeffPlus_eq_staged N hN, packetCoeffMinus_eq_staged N hN]
  have hbound : 2 * (N : ℤ) - 2 = ((2 * N - 2 : ℕ) : ℤ) := by omega
  rw [hbound]

private lemma packetOscillation_eq_staged (N : ℕ) (u : ℝ) :
    packetOscillation N u =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packetOscillation N u := rfl

private lemma torusDistance_eq_staged (u : ℝ) :
    torusDistance u =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.torusDistance u := rfl

-- @node: lem:jackson-packet-localization
/-- In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma jackson_packet_localization :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ N : ℕ, 2 ≤ N →
        (∫ u in Set.Icc (-Real.pi) Real.pi,
          packetKernel N u / (2 * Real.pi)) = 1 ∧
        (Summable fun j : ℤ =>
          |packetCoeffPlus N (j + 2) - 2 * packetCoeffPlus N (j + 1) +
            packetCoeffPlus N j|) ∧
        (Summable fun j : ℤ =>
          |packetCoeffMinus N (j + 2) - 2 * packetCoeffMinus N (j + 1) +
            packetCoeffMinus N j|) ∧
        (∑' j : ℤ,
          |packetCoeffPlus N (j + 2) - 2 * packetCoeffPlus N (j + 1) +
            packetCoeffPlus N j|) ≤ C / N ^ 3 ∧
        (∑' j : ℤ,
          |packetCoeffMinus N (j + 2) - 2 * packetCoeffMinus N (j + 1) +
            packetCoeffMinus N j|) ≤ C / N ^ 3 ∧
        (∀ r : ℤ, |r| < (2 * N + 2 : ℕ) ∨ (6 * N - 2 : ℕ) < |r| →
          (∫ u in Set.Icc (-Real.pi) Real.pi,
            packetOscillation N u * Real.cos (r * u)) = 0 ∧
          (∫ u in Set.Icc (-Real.pi) Real.pi,
            packetOscillation N u * Real.sin (r * u)) = 0) ∧
        (∀ u : ℝ, deriv (deriv (packetAntideriv N)) u = packetOscillation N u) ∧
        (∫ u in Set.Icc (-Real.pi) Real.pi, packetAntideriv N u) = 0 ∧
        c / N ≤ |packetAntideriv N 0| ∧
        |packetAntideriv N 0| ≤ C / N ∧
        (∀ u : ℝ,
          |packetAntideriv N u| ≤
            C / (N * (1 + N * torusDistance u) ^ 2)) ∧
        (∫ u in Set.Icc (-Real.pi) Real.pi,
          |packetAntideriv N u| / (2 * Real.pi)) ≤ C / N ^ 2 := by
  obtain ⟨c, Ccenter, hc, hcC, hcenter⟩ :=
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packet_center_bounds
  obtain ⟨Cpoint, hCpoint, hpoint⟩ :=
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packet_pointwise_localization
  obtain ⟨Cl1, hCl1, hl1⟩ :=
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packet_l1_localization
  let C : ℝ := max 512 (max Ccenter (max Cpoint Cl1))
  have h512C : (512 : ℝ) ≤ C := le_max_left _ _
  have hcenterC : Ccenter ≤ C :=
    (le_max_left Ccenter (max Cpoint Cl1)).trans (le_max_right 512 _)
  have hpointC : Cpoint ≤ C :=
    ((le_max_left Cpoint Cl1).trans (le_max_right Ccenter _)).trans
      (le_max_right 512 _)
  have hl1C : Cl1 ≤ C :=
    ((le_max_right Cpoint Cl1).trans (le_max_right Ccenter _)).trans
      (le_max_right 512 _)
  refine ⟨c, C, hc, hcC.trans hcenterC, ?_⟩
  intro N hN
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hplus (j : ℤ) := packetCoeffPlus_eq_staged N hNpos j
  have hminus (j : ℤ) := packetCoeffMinus_eq_staged N hNpos j
  have hantifun : packetAntideriv N =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packetAntideriv N := by
    funext u
    exact packetAntideriv_eq_staged N hNpos u
  refine ⟨packetKernel_normalized_integral N hNpos,
    packetCoeffPlus_secondDiff_summable N,
    packetCoeffMinus_secondDiff_summable N, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h :=
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.weightedCoeff_delta2_l1
        N hN 1 (Or.inl rfl)
    simp_rw [hplus]
    change (∑' j : ℤ,
      |Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.weightedCoeff N 1 (j + 2) -
        2 * Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.weightedCoeff N 1 (j + 1) +
        Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.weightedCoeff N 1 j|) ≤
          C / (N : ℝ) ^ 3
    calc
      _ ≤ 512 / (N : ℝ) ^ 3 := by
        convert h using 1
        congr 1
        funext j
        simp only [Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.delta2,
          Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.delta]
        congr 1
        ring
      _ ≤ _ := div_le_div_of_nonneg_right h512C (by positivity)
  · have h :=
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.weightedCoeff_delta2_l1
        N hN (-1) (Or.inr rfl)
    simp_rw [hminus]
    change (∑' j : ℤ,
      |Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.weightedCoeff N (-1) (j + 2) -
        2 * Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.weightedCoeff N (-1) (j + 1) +
        Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.weightedCoeff N (-1) j|) ≤
          C / (N : ℝ) ^ 3
    calc
      _ ≤ 512 / (N : ℝ) ^ 3 := by
        convert h using 1
        congr 1
        funext j
        simp only [Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.delta2,
          Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.delta]
        congr 1
        ring
      _ ≤ _ := div_le_div_of_nonneg_right h512C (by positivity)
  · intro r hr
    simpa only [packetOscillation_eq_staged] using
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packet_shifted_support
        N hN r hr
  · intro u
    rw [hantifun]
    simpa only [packetOscillation_eq_staged] using
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packet_twice_deriv N hN u
  · rw [hantifun]
    exact Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.packet_zero_mean N hN
  · rw [packetAntideriv_eq_staged N hNpos]
    exact (hcenter N hN).1
  · rw [packetAntideriv_eq_staged N hNpos]
    exact (hcenter N hN).2.trans
      (div_le_div_of_nonneg_right hcenterC hNR.le)
  · intro u
    rw [packetAntideriv_eq_staged N hNpos u, torusDistance_eq_staged]
    exact (hpoint N hN u).trans
      (div_le_div_of_nonneg_right hpointC (by positivity))
  · simp_rw [packetAntideriv_eq_staged N hNpos]
    exact (hl1 N hN).trans
      (div_le_div_of_nonneg_right hl1C (by positivity))

end CausalSmith.Stat.OptvalueVanishingoverlapRate
