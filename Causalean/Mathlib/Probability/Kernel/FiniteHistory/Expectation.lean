module
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Expectations from finite sequential kernel laws

This module derives iterated-integral identities for bounded real expectations, and a covariance
bound from a uniform bound on centered kernel means, directly from composition-product laws.
The results integrate over kernels rather than conditioning on positive-probability history
atoms.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Mathlib.Probability.Kernel.FiniteHistory

/-- If [a joint law ν](hyp:ν) [is the composition product of an s-finite base measure μ with an
s-finite kernel K](hyp:μ,K,hν), then for [every real function f integrable under ν](hyp:f,hf),
[the integral of f under ν equals the integral under μ of the inner integral of f against
K](goal). -/
theorem integral_compProd_of_law
    {H B : Type*} [MeasurableSpace H] [MeasurableSpace B]
    (μ : Measure H) (K : Kernel H B) [SFinite μ] [IsSFiniteKernel K]
    (ν : Measure (H × B)) (hν : ν = μ ⊗ₘ K)
    (f : H × B → ℝ) (hf : Integrable f ν) :
    ∫ z, f z ∂ν = ∫ h, ∫ b, f (h, b) ∂K h ∂μ := by
  subst ν
  exact Measure.integral_compProd hf

/-- If [a joint law ν](hyp:ν) [is the composition product of a probability measure μ with a
Markov kernel K](hyp:μ,K,hν), then for [every measurable real function f](hyp:f,hf) [bounded in
absolute value by a constant C](hyp:C,hbound), [the integral of f under ν equals the integral
under μ of the inner integral of f against K](goal). -/
theorem integral_compProd_bounded
    {H B : Type*} [MeasurableSpace H] [MeasurableSpace B]
    (μ : Measure H) (K : Kernel H B) [IsProbabilityMeasure μ] [IsMarkovKernel K]
    (ν : Measure (H × B)) (hν : ν = μ ⊗ₘ K)
    (f : H × B → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ z, |f z| ≤ C) :
    ∫ z, f z ∂ν = ∫ h, ∫ b, f (h, b) ∂K h ∂μ := by
  subst ν
  have hfi : Integrable f (μ ⊗ₘ K) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hbound z)
  exact Measure.integral_compProd hfi

/-- Let [μ be a probability law of histories](hyp:μ), [action a Markov kernel from histories to
finitely many actions](hyp:action), and [transition a Markov kernel from history-action pairs to a
reward and one of finitely many next states](hyp:transition). If [the history-action law νA is μ
composed with the action kernel](hyp:νA,hA) and [the full law ν is νA composed with the
transition kernel](hyp:ν,hν), then for [every measurable function f of history, action, reward
and next state](hyp:f,hf) [bounded in absolute value by a constant C](hyp:C,hbound), [the
integral of f under ν equals the iterated integral over histories, then actions, then reward and
next state](goal). -/
theorem integral_action_transition
    {H A S : Type*} [MeasurableSpace H] [MeasurableSpace A]
    [MeasurableSpace S] [Finite A] [Finite S]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (action : Kernel H A) [IsMarkovKernel action]
    (transition : Kernel (H × A) (ℝ × S)) [IsMarkovKernel transition]
    (νA : Measure (H × A)) (hA : νA = μ ⊗ₘ action)
    (ν : Measure ((H × A) × (ℝ × S))) (hν : ν = νA ⊗ₘ transition)
    (f : H → A → ℝ → S → ℝ)
    (hf : Measurable fun z : (H × A) × (ℝ × S) => f z.1.1 z.1.2 z.2.1 z.2.2)
    (C : ℝ) (hbound : ∀ h a r s, |f h a r s| ≤ C) :
    ∫ z, f z.1.1 z.1.2 z.2.1 z.2.2 ∂ν =
      ∫ h, ∫ a, ∫ rs, f h a rs.1 rs.2 ∂transition (h, a) ∂action h ∂μ := by
  subst νA
  -- Apply `integral_compProd_bounded` first to `ν`, then to `νA`.
  -- The inner kernel integral is measurable and bounded by `C`.
  have hg : Measurable (fun z : H × A =>
      ∫ rs, f z.1 z.2 rs.1 rs.2 ∂transition z) :=
    (hf.stronglyMeasurable.integral_kernel_prod_right').measurable
  have hgbound : ∀ z : H × A,
      |∫ rs, f z.1 z.2 rs.1 rs.2 ∂transition z| ≤ C := by
    intro z
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := transition z)
        (f := fun rs : ℝ × S => f z.1 z.2 rs.1 rs.2)
        (C := C) (Filter.Eventually.of_forall fun rs => by
          simpa only [Real.norm_eq_abs] using hbound z.1 z.2 rs.1 rs.2))
  calc
    ∫ z, f z.1.1 z.1.2 z.2.1 z.2.2 ∂ν =
        ∫ z : H × A, ∫ rs, f z.1 z.2 rs.1 rs.2 ∂transition z ∂(μ ⊗ₘ action) := by
      exact integral_compProd_bounded (μ ⊗ₘ action) transition ν hν _ hf C
        (fun z => hbound z.1.1 z.1.2 z.2.1 z.2.2)
    _ = ∫ h, ∫ a, ∫ rs, f h a rs.1 rs.2 ∂transition (h, a) ∂action h ∂μ := by
      exact integral_compProd_bounded μ action (μ ⊗ₘ action) rfl _ hg C hgbound

/-- Let [the joint law ν](hyp:ν) of a first and second window [be the composition product of a
probability law μ of the first window with a Markov kernel K](hyp:μ,K,hν). Let [f be a measurable
function of the first window](hyp:f,hf) [bounded in absolute value by a nonnegative constant
Cf](hyp:Cf,hCf,hf_bound), and [g a measurable function of the second window](hyp:g,hg)
[bounded in absolute value by a constant Cg](hyp:Cg,hg_bound). If [for every first
window x the kernel mean of g given x differs from the overall mean of g under ν by at most a
constant D](hyp:D,hkernel), then [the covariance of f and g under ν — the mean of
their product minus the product of their means — is at most Cf·D in absolute value](goal). -/
theorem covariance_compProd_of_centered_kernel_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (K : Kernel X Y) [IsMarkovKernel K]
    (ν : Measure (X × Y)) (hν : ν = μ ⊗ₘ K)
    (f : X → ℝ) (hf : Measurable f)
    (Cf : ℝ) (hCf : 0 ≤ Cf) (hf_bound : ∀ x, |f x| ≤ Cf)
    (g : Y → ℝ) (hg : Measurable g)
    (Cg : ℝ) (hg_bound : ∀ y, |g y| ≤ Cg)
    (D : ℝ)
    (hkernel : ∀ x,
      |(∫ y, g y ∂K x) - (∫ z, g z.2 ∂ν)| ≤ D) :
    |(∫ z, f z.1 * g z.2 ∂ν) -
        (∫ x, f x ∂μ) * (∫ z, g z.2 ∂ν)| ≤ Cf * D := by
  let c : ℝ := ∫ z, g z.2 ∂ν
  have hkg_meas : Measurable (fun x => ∫ y, g y ∂K x) := by
    simpa using ((hg.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right').measurable
  have hkg_bound : ∀ x, |∫ y, g y ∂K x| ≤ Cg := by
    intro x
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := K x) (f := g) (C := Cg)
        (Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs] using hg_bound y))
  have hfg_bound : ∀ z : X × Y, |f z.1 * g z.2| ≤ Cf * Cg := by
    intro z
    rw [abs_mul]
    exact mul_le_mul (hf_bound z.1) (hg_bound z.2) (abs_nonneg _) hCf
  have hfg_meas : Measurable (fun z : X × Y => f z.1 * g z.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hf_int : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable Cf
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hf_bound x)
  have hkgf_int : Integrable (fun x => f x * ∫ y, g y ∂K x) μ := by
    apply Integrable.of_bound ((hf.mul hkg_meas).aestronglyMeasurable) (Cf * Cg)
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using
        mul_le_mul (hf_bound x) (hkg_bound x) (abs_nonneg _) hCf
  have hfg_eq : (∫ z, f z.1 * g z.2 ∂ν) =
      ∫ x, f x * (∫ y, g y ∂K x) ∂μ := by
    rw [integral_compProd_bounded μ K ν hν _ hfg_meas (Cf * Cg) hfg_bound]
    congr 1
    funext x
    simpa only [Prod.fst, Prod.snd] using integral_const_mul (μ := K x) (f x) g
  have hcenter_eq : (∫ x, f x * ((∫ y, g y ∂K x) - c) ∂μ) =
      (∫ x, f x * (∫ y, g y ∂K x) ∂μ) - (∫ x, f x ∂μ) * c := by
    simp_rw [mul_sub]
    rw [integral_sub hkgf_int (hf_int.mul_const c), integral_mul_const]
  rw [hfg_eq]
  change |(∫ x, f x * (∫ y, g y ∂K x) ∂μ) - (∫ x, f x ∂μ) * c| ≤ Cf * D
  rw [← hcenter_eq]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x => f x * ((∫ y, g y ∂K x) - c)) (C := Cf * D)
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul (hf_bound x) (hkernel x) (abs_nonneg _) hCf))

end Causalean.Mathlib.Probability.Kernel.FiniteHistory

