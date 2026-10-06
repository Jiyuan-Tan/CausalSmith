module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.ProductPools.Transfer

/-!
Run-facing aliases for the generic finite-family Poisson-prefix transfer theorems.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

open Causalean.Stat
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily

-- @node: zero_overflow_prefix_risk
/-- [Under the stated inputs and conditions](hyp:I,X,P,lambda,h,T,hT,hTmem,theta,htheta),
zero overflow output costs at most the overflow probability for a target in `[-1,1]`. This gives
[the stated result](goal). -/
lemma zero_overflow_prefix_risk {I : Type*} [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (P : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → NNReal) (h : I → Nat) {T : PrefixFamily X → Real}
    (hT : Measurable T) (hTmem : ∀ s, T s ∈ Set.Icc (-1) 1)
    {theta : Real} (htheta : theta ∈ Set.Icc (-1) 1) :
    sqRisk (fixedPoolsLaw P h) (prefixRaoBlackwellStatistic lambda T 0) theta ≤
      sqRisk (independentPoissonPrefixLaw P lambda) T theta +
        ∑ i, (poissonMeasure (lambda i)).real (Set.Ioi (h i)) :=
  Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily.zero_overflow_prefix_risk
    P lambda h hT hTmem htheta

-- @node: eighth_pool_poisson_overflow
/-- [Under the stated inputs and conditions](hyp:h), a Poisson prefix with one eighth of the pool's
mean overflows with probability at most `exp(-h)`. This gives [the stated result](goal). -/
lemma eighth_pool_poisson_overflow (h : Nat) :
    (poissonMeasure ((h : NNReal) / 8)).real (Set.Ioi h) ≤ Real.exp (-(h : Real)) :=
  Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily.eighth_pool_poisson_overflow h

-- @node: lem:finite-prefix-transfer
/-- [Under the stated hypotheses](hyp:P,hh,hT,hTmem,htheta,hA), For finitely many independent iid pools on arbitrary measurable observation spaces (including
infinite Borel alphabets), a measurable statistic with values in [-1,1] and a target in [-1,1],
finite independent prefix averaging with zero overflow output transfers risk with the stated
exponential tail penalty and yields a total deterministic measurable rule.
For Borel observation spaces the resulting rule is Borel. No alphabet finiteness is required. This gives [the stated conclusion](goal). -/
lemma finite_prefix_transfer {I : Type*} [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (P : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (h : I → Nat) (hh : ∀ i, 1 ≤ h i) {T : PrefixFamily X → Real}
    (hT : Measurable T) (hTmem : ∀ s, T s ∈ Set.Icc (-1) 1)
    {theta Ab : Real} (htheta : theta ∈ Set.Icc (-1) 1)
    (hA : sqRisk (independentPoissonPrefixLaw P (fun i => (h i : NNReal) / 8)) T theta ≤ Ab) :
    Measurable (prefixRaoBlackwellStatistic (N := h) (fun i => (h i : NNReal) / 8) T 0) ∧
    (∀ s, prefixRaoBlackwellStatistic (N := h) (fun i => (h i : NNReal) / 8) T 0 s ∈ Set.Icc
      (-1) 1) ∧
    sqRisk (fixedPoolsLaw P h)
      (prefixRaoBlackwellStatistic (N := h) (fun i => (h i : NNReal) / 8) T 0) theta ≤
        Ab + ∑ i, Real.exp (-(h i : Real)) :=
  Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily.finite_prefix_transfer
    P h hT hTmem htheta hA

end CausalSmith.Stat.AnnotationRarearmFrontier
