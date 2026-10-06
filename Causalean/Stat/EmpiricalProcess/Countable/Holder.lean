module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Mixed fourth moments

The fourth-power Holder inequality and finite-maximum moment legality are
independent of martingales. They are the lowest analytic layer for Doob's
inequality; neither assumes a maximal-moment estimate.
-/

public section

open MeasureTheory
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- Under [any measure μ](hyp:μ), if [two real functions f and
g](hyp:f,g) are [nonnegative](hyp:hf,hg), [almost everywhere strongly
measurable](hyp:hfm,hgm), and [have integrable squares](hyp:hf2,hg2), then
[their product is integrable and the square of its integral is at most the
product of the integrals of their squares](goal).

This Cauchy–Schwarz form uses ordinary squares, so it needs no
finite-measure assumption.
-/
theorem integral_product_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    Integrable (fun x => f x * g x) μ ∧
      (∫ x, f x * g x ∂μ)^2 ≤
        (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hfl := (memLp_two_iff_integrable_sq hfm).2 hf2
  have hgl := (memLp_two_iff_integrable_sq hgm).2 hg2
  have hprod : MemLp (fun x => f x * g x) 1 μ := hgl.mul' hfl
  refine ⟨(memLp_one_iff_integrable.mp hprod), ?_⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num)
    (Filter.Eventually.of_forall hf) (Filter.Eventually.of_forall hg)
    (by simpa using hfl) (by simpa using hgl)
  simp only [Real.rpow_two] at h
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have hn : 0 ≤ ∫ x, f x * g x ∂μ := integral_nonneg fun x => mul_nonneg (hf x) (hg x)
  have hn1 : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hn2 : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hs := pow_le_pow_left₀ hn h 2
  rw [mul_pow, Real.sq_sqrt hn1, Real.sq_sqrt hn2] at hs
  exact hs

/-- Under [any measure μ](hyp:μ), if [two real functions A and
B](hyp:A,B) are [nonnegative](hyp:hA,hB), [almost everywhere strongly
measurable](hyp:hAm,hBm), and [have integrable fourth
powers](hyp:hA4,hB4), then [A^3·B is integrable and the fourth power of
its integral is at most the cube of the integral of A^4 times the integral
of B^4](goal). -/
theorem fourth_moment_holder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Ω → ℝ) (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x)
    (hA4 : Integrable (fun x => A x ^ 4) μ)
    (hB4 : Integrable (fun x => B x ^ 4) μ)
    (hAm : AEStronglyMeasurable A μ) (hBm : AEStronglyMeasurable B μ) :
    Integrable (fun x => A x ^ 3 * B x) μ ∧
    (∫ x, A x ^ 3 * B x ∂μ)^4 ≤
      (∫ x, A x ^ 4 ∂μ)^3 * (∫ x, B x ^ 4 ∂μ) := by
  have hA2 : Integrable (fun x => (A x ^ 2)^2) μ := by
    simpa only [← pow_mul] using hA4
  have hB2 : Integrable (fun x => (B x ^ 2)^2) μ := by
    simpa only [← pow_mul] using hB4
  have hAB2 : Integrable (fun x => (A x * B x)^2) μ := by
    refine (hA4.add hB4).mono_nonneg ((hAm.mul hBm).pow 2)
      (Filter.Eventually.of_forall fun x => sq_nonneg _) ?_
    exact Filter.Eventually.of_forall fun x => by
      change (A x * B x)^2 ≤ A x ^ 4 + B x ^ 4
      nlinarith [sq_nonneg (A x ^ 2 - B x ^ 2)]
  obtain ⟨hi, hc⟩ := integral_product_sq_le μ (fun x => A x ^ 2)
    (fun x => A x * B x) (fun x => sq_nonneg _)
    (fun x => mul_nonneg (hA x) (hB x)) (hAm.pow 2) (hAm.mul hBm) hA2 hAB2
  obtain ⟨_, hd⟩ := integral_product_sq_le μ (fun x => A x ^ 2)
    (fun x => B x ^ 2) (fun x => sq_nonneg _) (fun x => sq_nonneg _)
    (hAm.pow 2) (hBm.pow 2) hA2 hB2
  have heq : (fun x => A x ^ 2 * (A x * B x)) = (fun x => A x ^ 3 * B x) := by
    funext x; ring
  rw [heq] at hi hc
  simp only [← pow_mul, mul_pow] at hc hd
  refine ⟨hi, ?_⟩
  have hs := pow_le_pow_left₀ (sq_nonneg (∫ x, A x ^ 3 * B x ∂μ)) hc 2
  have ht := mul_le_mul_of_nonneg_left hd (sq_nonneg (∫ x, A x ^ 4 ∂μ))
  calc
    (∫ x, A x ^ 3 * B x ∂μ)^4 ≤
        ((∫ x, A x ^ 4 ∂μ) * (∫ x, A x ^ 2 * B x ^ 2 ∂μ))^2 := by
      simpa only [← pow_mul] using hs
    _ ≤ (∫ x, A x ^ 4 ∂μ)^3 * (∫ x, B x ^ 4 ∂μ) := by
      nlinarith only [ht]

/-- Under [a measure μ](hyp:μ), if [a nonempty finite family of real
functions](hyp:f) consists of [almost everywhere strongly measurable
functions](hyp:hm) [with integrable fourth powers](hyp:h4), then [their
pointwise maximum is almost everywhere strongly measurable and has an
integrable fourth power](goal). -/
theorem finite_iSup_fourth_integrable {Ω ι : Type*} [MeasurableSpace Ω]
    [Finite ι] [Nonempty ι] (μ : Measure Ω) (f : ι → Ω → ℝ)
    (hm : ∀ i, AEStronglyMeasurable (f i) μ)
    (h4 : ∀ i, Integrable (fun x => f i x ^ 4) μ) :
    AEStronglyMeasurable (fun x => ⨆ i, f i x) μ ∧
      Integrable (fun x => (⨆ i, f i x)^4) μ := by
  classical
  let := Fintype.ofFinite ι
  have hmax : AEStronglyMeasurable (fun x => ⨆ i, f i x) μ :=
    (AEMeasurable.iSup fun i => (hm i).aemeasurable).aestronglyMeasurable
  refine ⟨hmax, ?_⟩
  have hsum : Integrable (fun x => ∑ i, f i x ^ 4) μ :=
    integrable_finsetSum _ fun i _ => h4 i
  refine hsum.mono_nonneg (hmax.pow 4)
    (Filter.Eventually.of_forall fun x => by positivity) ?_
  exact Filter.Eventually.of_forall fun x => by
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => f i x)
    rw [← hi]
    exact Finset.single_le_sum (f := fun j => f j x ^ 4)
      (fun j _ => by positivity) (Finset.mem_univ i)

end Causalean.Stat.EmpiricalProcess.Countable
