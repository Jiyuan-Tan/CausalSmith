module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Basic
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.AbsoluteValue
public import Causalean.Mathlib.Analysis.Duality.MomentPrior
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Helpers/CitedGates

Finite original-record private value frontiers: Helpers/CitedGates.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


/-- Fix [the local protocol](hyp:K). [Best uniform polynomial error for the absolute-value function](goal). -/
def bestAbsApproxError (K : ℕ) : ℝ :=
  ⨅ p : {p : Polynomial ℝ // p.natDegree ≤ K},
    sSup ((fun x : ℝ => abs (p.1.eval x - abs x)) '' Set.Icc (-1) 1)
/-- Fix [the natural-number parameter D](hyp:D). [Explicit truncated first-kind Chebyshev absolute-value approximation](goal). -/
def chebyshevAbsPoly (D : ℕ) : Polynomial ℝ :=
  Polynomial.C (2 / Real.pi) +
    ∑ v ∈ Finset.Icc 1 (D/2),
      Polynomial.C ((4 / Real.pi) * (-1 : ℝ)^(v+1) / (4 * (v : ℝ)^2 - 1)) *
        Polynomial.Chebyshev.T ℝ (2 * (v : ℤ))

/-- [Vákár and Ong (2018), Theorem 10 and proof, pp. 19–20; Definition 1 p. 8, finite-reference reduction p. 18. Handle: VakarOng2018SFinite, arXiv:1810.01837v2. Logical gate: jointly measurable density for finite dominated kernels](goal). -/
def MeasurableKernelRadonNikodym : Sort 0 :=
  ∀ {H Z : Type} [MeasurableSpace H] [MeasurableSpace Z] [StandardBorelSpace Z]
    (K L : Kernel H Z) [IsFiniteKernel K] [IsFiniteKernel L],
    (∀ h, K h ≪ L h) → ∃ f : H × Z → ℝ≥0∞, Measurable f ∧
      ∀ h E, MeasurableSet E → K h E = ∫⁻ z in E, f (h,z) ∂(L h)

/-- [Hoeffding (1963), Theorem 2, equal-range specialization, printed p. 16. Handle: Hoeffding1963Bounded, DOI 10.1080/01621459.1963.10500830. Logical gate: upper, lower and hence two-sided bounded mean tails](goal). -/
def BoundedMeanConcentration : Sort 0 :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (m : ℕ) (_hm : 0 < m) (b : ℝ) (H : Fin m → Ω → ℝ),
    iIndepFun H mu → (∀ i, Measurable (H i)) → (∀ i w, H i w ∈ Set.Icc (-b) b) →
    ∀ x : ℝ, 0 ≤ x →
      mu.real {w | x ≤ (m : ℝ)⁻¹ * ∑ i, (H i w - ∫ t, H i t ∂mu)} ≤
        Real.exp (-(m : ℝ) * x^2 / (2*b^2)) ∧
      mu.real {w | (m : ℝ)⁻¹ * ∑ i, (H i w - ∫ t, H i t ∂mu) ≤ -x} ≤
        Real.exp (-(m : ℝ) * x^2 / (2*b^2))

/-- [Cai and Low (2011), Lemma 2, equations (24), (27), (28), p. 13, D=2K. Handle: CaiLow2011Nonsmooth, arXiv:1105.3039. Logical approximation gate](goal). -/
def CaiLowChebyshevApproximation : Sort 0 :=
  ∀ D : ℕ, Even D → 2 ≤ D →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, abs ((chebyshevAbsPoly D).eval x - abs x) ≤
      2 / (Real.pi * (D+1))) ∧
    (∀ v : ℕ, v ≤ D → |(chebyshevAbsPoly D).coeff v| ≤ (2 : ℝ)^((3 : ℝ)*D/2))

/-- [Cai and Low (2011), Lemma 1, p. 10. Handle: CaiLow2011Nonsmooth, arXiv:1105.3039. Symmetric moment-matched probability measures with exact gap](goal). -/
def CaiLowMomentDuality : Sort 0 :=
  ∀ K : ℕ, 0 < K → Even K → ∃ xi0 xi1 : Measure ℝ,
    IsProbabilityMeasure xi0 ∧ IsProbabilityMeasure xi1 ∧
    xi0 (Set.Icc (-1 : ℝ) 1)ᶜ = 0 ∧ xi1 (Set.Icc (-1 : ℝ) 1)ᶜ = 0 ∧
    xi0.map (fun x => -x) = xi0 ∧ xi1.map (fun x => -x) = xi1 ∧
    (∀ l : ℕ, l ≤ K → (∫ x, x^l ∂xi1) = ∫ x, x^l ∂xi0) ∧
    (∫ x, |x| ∂xi1) - (∫ x, |x| ∂xi0) = 2 * bestAbsApproxError K

-- @node: lem:bernstein-absolute-approximation-limit
/-- [Cai and Low (2011), Section 3.1, p. 8, Bernstein constant paragraph; Bernstein (1913), pp. 1–2 and 55–56. Handle: CaiLow2011Nonsmooth, arXiv:1105.3039. Positive even-degree absolute approximation limit](goal). -/
def BernsteinAbsoluteApproximationLimit : Sort 0 :=
  ∃ betaStar : ℝ, (0.278 : ℝ) < betaStar ∧ betaStar < (0.286 : ℝ) ∧
    Filter.Tendsto (fun k : ℕ => (2 * k : ℝ) * bestAbsApproxError (2*k))
      Filter.atTop (nhds betaStar)

open Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality
open Causalean.Mathlib.Analysis.Approximation.Chebyshev.AbsoluteValue

-- @node: lem:measurable-kernel-radon-nikodym
/-- [Every pointwise-dominated pair of finite kernels on a standard Borel target admits a jointly
measurable Radon--Nikodym density representing each kernel measure](goal). -/
theorem measurableKernelRadonNikodym_proved : MeasurableKernelRadonNikodym := by
  intro H Z _ _ _ K L _ _ hKL
  refine ⟨fun hz ↦ K.rnDeriv L hz.1 hz.2, K.measurable_rnDeriv L, ?_⟩
  intro h E hE
  exact (Kernel.setLIntegral_rnDeriv (hKL h) hE).symm

-- @node: lem:bounded-mean-concentration
/-- Hoeffding's inequality for finite independent bounded real-valued families
[establishes the bounded-mean concentration gate](goal). -/
theorem boundedMeanConcentration_proved : BoundedMeanConcentration := by
  unfold BoundedMeanConcentration
  intro Ω _ mu _ m hm b H hInd hMeas hBdd x hx
  have hb : 0 ≤ b := by
    let i : Fin m := ⟨0, hm⟩
    obtain ⟨w⟩ := nonempty_of_isProbabilityMeasure mu
    exact le_trans (neg_le_self_iff.mp (le_trans (hBdd i w).1 (hBdd i w).2)) (le_refl b)
  rcases hb.eq_or_lt with rfl | hb
  · constructor <;> simpa using (measureReal_le_one (μ := mu))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let c : NNReal := (‖b - (-b)‖₊ / 2) ^ 2
  have hc : (c : ℝ) = b ^ 2 := by
    simp only [c, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_pos (by linarith : 0 < b + b)]
    ring
  have upper (G : Fin m → Ω → ℝ) (hGInd : iIndepFun G mu)
      (hGMeas : ∀ i, Measurable (G i))
      (hGBdd : ∀ i w, G i w ∈ Set.Icc (-b) b) :
      mu.real {w | x ≤ (m : ℝ)⁻¹ * ∑ i, (G i w - ∫ t, G i t ∂mu)} ≤
        Real.exp (-(m : ℝ) * x ^ 2 / (2 * b ^ 2)) := by
    let Y : Fin m → Ω → ℝ := fun i w => G i w - ∫ t, G i t ∂mu
    have hYInd : iIndepFun Y mu :=
      hGInd.comp (fun i y => y - ∫ t, G i t ∂mu)
        (fun _ => measurable_id.sub measurable_const)
    have hSubG : ∀ i ∈ Finset.univ, HasSubgaussianMGF (Y i) c mu := by
      intro i _
      simpa [Y, c] using hasSubgaussianMGF_of_mem_Icc
        (μ := mu) (X := G i) (hGMeas i).aemeasurable (ae_of_all _ (hGBdd i))
    have hmx : 0 ≤ (m : ℝ) * x := mul_nonneg hmR.le hx
    have hTail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      hYInd hSubG hmx
    have hEvent :
        {w | x ≤ (m : ℝ)⁻¹ * ∑ i, (G i w - ∫ t, G i t ∂mu)} =
          {w | (m : ℝ) * x ≤ ∑ i, Y i w} := by
      ext w
      simp only [Set.mem_setOf_eq, Y]
      constructor
      · intro h
        calc
          (m : ℝ) * x ≤ (m : ℝ) * ((m : ℝ)⁻¹ * ∑ i, (G i w - ∫ t, G i t ∂mu)) :=
            mul_le_mul_of_nonneg_left h hmR.le
          _ = ∑ i, (G i w - ∫ t, G i t ∂mu) := by
            field_simp
      · intro h
        calc
          x = (m : ℝ)⁻¹ * ((m : ℝ) * x) := by
            field_simp
          _ ≤ (m : ℝ)⁻¹ * ∑ i, (G i w - ∫ t, G i t ∂mu) :=
            mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hmR.le)
    rw [hEvent]
    refine hTail.trans_eq ?_
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change -((m : ℝ) * x) ^ 2 / (2 * ((m : ℝ) * (c : ℝ))) =
      -(m : ℝ) * x ^ 2 / (2 * b ^ 2)
    rw [hc]
    field_simp
  constructor
  · exact upper H hInd hMeas hBdd
  · let G : Fin m → Ω → ℝ := fun i w => -H i w
    have hGInd : iIndepFun G mu :=
      hInd.comp (fun _ y => -y) (fun _ => measurable_neg)
    have hGMeas : ∀ i, Measurable (G i) := fun i => (hMeas i).neg
    have hGBdd : ∀ i w, G i w ∈ Set.Icc (-b) b := by
      intro i w
      simpa [G] using And.intro (neg_le_neg (hBdd i w).2) (neg_le_neg (hBdd i w).1)
    have h := upper G hGInd hGMeas hGBdd
    have hEvent :
        {w | (m : ℝ)⁻¹ * ∑ i, (H i w - ∫ t, H i t ∂mu) ≤ -x} =
          {w | x ≤ (m : ℝ)⁻¹ * ∑ i, (G i w - ∫ t, G i t ∂mu)} := by
      ext w
      simp only [Set.mem_setOf_eq, G, integral_neg]
      have hsum :
          (∑ i, (-H i w - -∫ a, H i a ∂mu)) =
            -∑ i, (H i w - ∫ a, H i a ∂mu) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum, mul_neg]
      constructor <;> intro h' <;> linarith
    rw [hEvent]
    exact h

-- The run's explicit even Chebyshev truncation is the public half-degree truncation.
private lemma chebyshevAbsPoly_eq_library (D : ℕ) :
    chebyshevAbsPoly D =
      Causalean.Mathlib.Analysis.Approximation.Chebyshev.AbsoluteValue.absChebPoly (D / 2) := by
  rw [Causalean.Mathlib.Analysis.Approximation.Chebyshev.AbsoluteValue.absChebPoly_eq_sum_Icc]
  unfold chebyshevAbsPoly
  rfl

-- The run's indexed infimum agrees with Causalean's best uniform absolute-value approximation error.
private lemma bestAbsApproxError_eq_library (K : ℕ) :
    bestAbsApproxError K = bestUniformApproxErrorAbs K := by
  unfold bestAbsApproxError bestUniformApproxErrorAbs
  change sInf (Set.range (fun p : {p : Polynomial ℝ // p.natDegree ≤ K} ↦
    sSup ((fun x : ℝ ↦ abs (p.1.eval x - abs x)) '' Set.Icc (-1) 1))) = _
  congr 1
  ext e
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p.1, p.2, ?_⟩
    simp only [uniformApproxErrorAbs, symmUnitInterval, abs_sub_comm]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    simp only [uniformApproxErrorAbs, symmUnitInterval, abs_sub_comm]

-- @node: lem:cai-low-moment-duality
/-- [The Cai--Low symmetric moment-matched prior gate](goal) follows from the extremal
absolute-value approximation duality construction. -/
theorem caiLowMomentDuality_proved : CaiLowMomentDuality := by
  intro K _hK _hEven
  obtain ⟨P⟩ := exists_symmetric_momentMatched_absGap (K := K)
  refine ⟨P.ν₀, P.ν₁, P.probability₀, P.probability₁, P.supported₀, P.supported₁,
    P.symmetric₀, P.symmetric₁, ?_, ?_⟩
  · intro l hl
    exact (P.moments_eq l hl).symm
  · rw [bestAbsApproxError_eq_library]
    exact P.abs_gap

-- @node: lem:cai-low-chebyshev-approximation
/-- [The Cai--Low Chebyshev absolute-value approximation gate](goal) follows from the public
half-degree truncation bounds. -/
theorem caiLowChebyshevApproximation_proved : CaiLowChebyshevApproximation := by
  intro D hD hD2
  rw [chebyshevAbsPoly_eq_library]
  constructor
  · intro x hx
    exact absChebPoly_halfDegree_error_le D hD hx
  · intro v _hv
    exact absChebPoly_halfDegree_coeff_le D hD v


end CausalSmith.Stat.LdpOptvalueUniformFrontier
