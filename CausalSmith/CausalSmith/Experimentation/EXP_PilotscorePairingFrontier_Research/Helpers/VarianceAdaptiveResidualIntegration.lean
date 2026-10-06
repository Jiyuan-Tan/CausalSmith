module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.VarianceAdaptiveResidual
public import Causalean.Mathlib.Probability.Independence.Conditional.FiniteProductResidual

/-!
# Conditional integration for adaptive matched residuals

This paper helper applies the reviewed finite-product conditional-residual API
to matching coefficients that depend on an independent side variable and all
sample covariates. The substrate import is intentionally visible while that API
is staged for promotion.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open Causalean.Mathlib.Probability.Independence.Conditional.FiniteProductResidual

variable {A Z C : Type*} [MeasurableSpace A] [StandardBorelSpace A]
  [MeasurableSpace Z] [StandardBorelSpace Z] [MeasurableSpace C]

@[expose] def reassocSwapEquiv {B R S : Type*} [MeasurableSpace B] [MeasurableSpace R]
    [MeasurableSpace S] : (B × R) × S ≃ᵐ (B × S) × R where
  toFun z := ((z.1.1, z.2), z.1.2)
  invFun z := ((z.1.1, z.2), z.1.2)
  left_inv z := by rcases z with ⟨⟨b, r⟩, s⟩; rfl
  right_inv z := by rcases z with ⟨⟨b, s⟩, r⟩; rfl
  measurable_toFun :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  measurable_invFun :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)

@[expose] def reassocSwap {B R S : Type*} [MeasurableSpace B] [MeasurableSpace R]
    [MeasurableSpace S] : (B × R) × S → (B × S) × R := reassocSwapEquiv

/-- Reassociating a pilot/randomizer side product around an iid main-sample
product preserves the corresponding three-factor product law. -/
lemma measurePreserving_reassocSwap {B R S : Type*}
    [MeasurableSpace B] [MeasurableSpace R] [MeasurableSpace S]
    (μB : Measure B) (μR : Measure R) (μS : Measure S)
    [SigmaFinite μB] [SigmaFinite μR] [SigmaFinite μS] :
    MeasurePreserving (reassocSwap : (B × R) × S → (B × S) × R)
      ((μB.prod μR).prod μS) ((μB.prod μS).prod μR) := by
  have h₁ := MeasureTheory.measurePreserving_prodAssoc μB μR μS
  have h₂ := (MeasurePreserving.id μB).prod
    (Measure.measurePreserving_swap (μ := μR) (ν := μS))
  have h₃ := (MeasureTheory.measurePreserving_prodAssoc μB μS μR).symm
  have hcomp := h₃.comp (h₂.comp h₁)
  convert hcomp using 1 <;> rfl

/-- A covariate-adaptive matched score coefficient is orthogonal to every
conditionally centered one-record residual. -/
lemma integral_sum_adaptive_score_mul_residual_eq_zero
    (ρ : Measure A) (μ : Measure Z) [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (X : Z → C) (r : Z → ℝ) (q : C → ℝ)
    (M : A × (Fin N → C) → Match N)
    (hX : Measurable X) (hr : Measurable r) (hq : Measurable q) (hM : Measurable M)
    (hir : Integrable r μ)
    (hzero : μ[r | MeasurableSpace.comap X inferInstance] =ᵐ[μ] 0)
    (hint : ∀ i : Fin N, Integrable (fun az : A × (Fin N → Z) =>
      (q (X (az.2 i)) - q (X (az.2 ((M (covariateInfo X az)).val i)))) *
        r (az.2 i)) (productLaw ρ μ)) :
    ∫ az, ∑ i : Fin N,
      (q (X (az.2 i)) - q (X (az.2 ((M (covariateInfo X az)).val i)))) *
        r (az.2 i) ∂productLaw ρ μ = 0 := by
  rw [integral_finset_sum Finset.univ (fun i _ => hint i)]
  apply Finset.sum_eq_zero
  intro i _
  let b : A × (Fin N → C) → ℝ := fun ax =>
    q (ax.2 i) - ∑ j : Fin N,
      if (M ax).val i = j then q (ax.2 j) else 0
  have hb : Measurable b := by
    unfold b
    apply Measurable.sub
    · exact hq.comp (measurable_pi_apply i |>.comp measurable_snd)
    · apply Finset.measurable_fun_sum
      intro j _
      apply Measurable.ite
      · exact measurableSet_eq_fun
          ((measurable_of_finite (fun M' : Match N => M'.val i)).comp hM)
          measurable_const
      · exact hq.comp (measurable_pi_apply j |>.comp measurable_snd)
      · exact measurable_const
  have hbpoint (ax : A × (Fin N → C)) :
      b ax = q (ax.2 i) - q (ax.2 ((M ax).val i)) := by
    dsimp [b]
    rw [Finset.sum_eq_single ((M ax).val i)]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  have hbi : Integrable
      (fun az => b (covariateInfo X az) * r (az.2 i)) (productLaw ρ μ) := by
    apply (hint i).congr
    filter_upwards [] with az
    rw [hbpoint]
    rfl
  have hz := integral_covariate_mul_residual_eq_zero ρ μ hX hr hir hzero i b hb hbi
  calc
    (∫ az, (q (X (az.2 i)) - q (X (az.2 ((M (covariateInfo X az)).val i)))) *
        r (az.2 i) ∂productLaw ρ μ) =
        ∫ az, b (covariateInfo X az) * r (az.2 i) ∂productLaw ρ μ := by
      apply integral_congr_ae
      filter_upwards [] with az
      rw [hbpoint]
      rfl
    _ = 0 := hz

/-- Distinct-coordinate conditional residual orthogonality kills the adaptive
matched residual cross-product, even though the match uses all covariates. -/
lemma integral_sum_residual_mul_adaptive_match_eq_zero
    (ρ : Measure A) (μ : Measure Z) [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (X : Z → C) (r : Z → ℝ) (M : A × (Fin N → C) → Match N)
    (hX : Measurable X) (hr : Measurable r) (hM : Measurable M)
    (hir : Integrable r μ)
    (hzero : μ[r | MeasurableSpace.comap X inferInstance] =ᵐ[μ] 0)
    (hint : ∀ i j : Fin N, Integrable (fun az : A × (Fin N → Z) =>
      (if (M (covariateInfo X az)).val i = j then 1 else 0) *
        r (az.2 i) * r (az.2 j)) (productLaw ρ μ)) :
    ∫ az, ∑ i : Fin N,
      r (az.2 i) * r (az.2 ((M (covariateInfo X az)).val i))
      ∂productLaw ρ μ = 0 := by
  have hpoint (az : A × (Fin N → Z)) (i : Fin N) :
      r (az.2 i) * r (az.2 ((M (covariateInfo X az)).val i)) =
        ∑ j : Fin N, (if (M (covariateInfo X az)).val i = j then 1 else 0) *
          r (az.2 i) * r (az.2 j) := by
    classical
    rw [Finset.sum_eq_single ((M (covariateInfo X az)).val i)]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  simp_rw [hpoint]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hint i j))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => hint i j)]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i = j
  · subst j
    have hfun : (fun az : A × (Fin N → Z) =>
        (if (M (covariateInfo X az)).val i = i then 1 else 0) *
          r (az.2 i) * r (az.2 i)) = 0 := by
      funext az
      simp [(M (covariateInfo X az)).property.2 i]
    rw [hfun]
    simp
  · let b : A × (Fin N → C) → ℝ := fun ax =>
      if (M ax).val i = j then 1 else 0
    have hb : Measurable b := by
      classical
      apply Measurable.ite
      · exact measurableSet_eq_fun
          ((measurable_of_finite (fun M' : Match N => M'.val i)).comp hM)
          measurable_const
      · exact measurable_const
      · exact measurable_const
    apply integral_covariate_mul_residual_mul_residual_eq_zero
      ρ μ hX hr hir hzero i j hij b hb
    convert hint i j using 1

/-- Products with an adaptively selected partner are integrable when both
record-level factors are square-integrable. -/
lemma integrable_sum_adaptive_pair_mul
    (ρ : Measure A) (μ : Measure Z) [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (X : Z → C) (f g : Z → ℝ) (M : A × (Fin N → C) → Match N)
    (hX : Measurable X) (hM : Measurable M)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun az : A × (Fin N → Z) => ∑ i : Fin N,
      f (az.2 i) * g (az.2 ((M (covariateInfo X az)).val i)))
      (productLaw ρ μ) := by
  classical
  have hfi (i : Fin N) : MemLp (fun az : A × (Fin N → Z) => f (az.2 i)) 2
      (productLaw ρ μ) :=
    hf.comp_measurePreserving (measurePreserving_selectedRecord ρ μ i)
  have hgi (i : Fin N) : MemLp (fun az : A × (Fin N → Z) => g (az.2 i)) 2
      (productLaw ρ μ) :=
    hg.comp_measurePreserving (measurePreserving_selectedRecord ρ μ i)
  have hterm (i j : Fin N) : Integrable (fun az : A × (Fin N → Z) =>
      (if (M (covariateInfo X az)).val i = j then 1 else 0) *
        f (az.2 i) * g (az.2 j)) (productLaw ρ μ) := by
    have hp := (hfi i).integrable_mul (hgi j)
    have hmidx : Measurable (fun az : A × (Fin N → Z) =>
        (M (covariateInfo X az)).val i) :=
      (measurable_of_finite (fun M' : Match N => M'.val i)).comp
        (hM.comp (measurable_covariateInfo hX))
    have hs : MeasurableSet {az : A × (Fin N → Z) |
        (M (covariateInfo X az)).val i = j} :=
      measurableSet_eq_fun hmidx measurable_const
    apply (hp.indicator hs).congr
    filter_upwards [] with az
    by_cases h : (M (covariateInfo X az)).val i = j <;>
      simp [Set.indicator, h]
  have hall : Integrable (fun az : A × (Fin N → Z) => ∑ i : Fin N,
      ∑ j : Fin N, (if (M (covariateInfo X az)).val i = j then 1 else 0) *
        f (az.2 i) * g (az.2 j)) (productLaw ρ μ) :=
    integrable_finset_sum Finset.univ fun i _ =>
      integrable_finset_sum Finset.univ fun j _ => hterm i j
  apply hall.congr
  filter_upwards [] with az
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single ((M (covariateInfo X az)).val i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

end CausalSmith.Experimentation.PilotscorePairingFrontier
