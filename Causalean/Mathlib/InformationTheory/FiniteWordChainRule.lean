import Causalean.Mathlib.InformationTheory.KLBind
import Causalean.Mathlib.Probability.SignedTwoPoint
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Kullback--Leibler chain rule for finite words

This module disintegrates an arbitrary probability mass function on a finite word into its
strict-prefix marginal and a totalized conditional law for the last symbol. It then expresses
Kullback--Leibler divergence recursively through the resulting chronological factorization,
without requiring full support except for the explicit pointwise conditional-divergence formula.
-/

namespace Causalean.Mathlib.InformationTheory.FiniteWordChainRule

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω]

/-- Given [a finite word](hyp:u) and [a final symbol](hyp:x), [append the symbol to the word](goal). -/
def appendSymbol {k : Nat} (u : Fin k → Ω) (x : Ω) : Fin (k + 1) → Ω :=
  Fin.lastCases x u

/-- [Appending a symbol to a finite word](hyp:u,x) [agrees with Mathlib's tuple append
`Fin.snoc`](goal). -/
theorem appendSymbol_eq_snoc {k : Nat} (u : Fin k → Ω) (x : Ω) :
    appendSymbol u x = Fin.snoc (α := fun _ ↦ Ω) u x := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [appendSymbol]

/-- Given [a prefix length](hyp:k), [split a nonempty finite word into its strict prefix and last
symbol](goal). -/
def lastCoordinateSplit (k : Nat) : (Fin (k + 1) → Ω) ≃ (Fin k → Ω) × Ω where
  toFun w := (fun i ↦ w i.castSucc, w (Fin.last k))
  invFun ux := appendSymbol ux.1 ux.2
  left_inv w := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [appendSymbol]
    · simp [appendSymbol]
  right_inv ux := by
    rcases ux with ⟨u, x⟩
    ext i <;> simp [appendSymbol]

/-- Given [a probability mass function on nonempty finite words](hyp:p), [its strict-prefix
marginal](goal) sums over the final symbol. -/
noncomputable def prefixPMF {k : Nat} (p : PMF (Fin (k + 1) → Ω)) :
    PMF (Fin k → Ω) :=
  PMF.ofFintype (fun u ↦ ∑ x : Ω, p (appendSymbol u x)) (by
    calc
      ∑ u, ∑ x : Ω, p (appendSymbol u x) =
          ∑ ux : (Fin k → Ω) × Ω, p (appendSymbol ux.1 ux.2) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ w, p w := by
        rw [← (lastCoordinateSplit k).sum_comp]
        apply Finset.sum_congr rfl
        intro w _
        change p ((lastCoordinateSplit k).symm ((lastCoordinateSplit k) w)) = p w
        rw [Equiv.symm_apply_apply]
      _ = 1 := by simpa only [tsum_fintype] using PMF.tsum_coe p)

/-- For [a finite-word law](hyp:p) and [a strict prefix](hyp:u), [the prefix mass is the sum of
the masses of all one-symbol extensions](goal). -/
@[simp]
lemma prefixPMF_apply {k : Nat} (p : PMF (Fin (k + 1) → Ω)) (u : Fin k → Ω) :
    prefixPMF p u = ∑ x : Ω, p (appendSymbol u x) := by
  simp [prefixPMF]

/-- Given [a finite-word law](hyp:p) and [a strict prefix](hyp:u), [the conditional law of the
last symbol](goal) is the normalized extension mass, totalized by a point mass on null prefixes. -/
noncomputable def nextSymbolPMF {k : Nat} (p : PMF (Fin (k + 1) → Ω))
    (u : Fin k → Ω) : PMF Ω :=
  if h : prefixPMF p u = 0 then
    PMF.pure (Classical.choice inferInstance)
  else
    PMF.ofFintype
      (fun x ↦ p (appendSymbol u x) / prefixPMF p u)
      (by
        calc
          ∑ x : Ω, p (appendSymbol u x) / prefixPMF p u =
              (∑ x : Ω, p (appendSymbol u x)) / prefixPMF p u := by
                simp_rw [ENNReal.div_eq_inv_mul]
                rw [Finset.mul_sum]
          _ = prefixPMF p u / prefixPMF p u := by rw [prefixPMF_apply]
          _ = 1 := ENNReal.div_self h (PMF.apply_ne_top _ _))

/-- Given [a finite-word law](hyp:p), [its conditional last-symbol laws form a kernel on strict
prefixes](goal). -/
noncomputable def nextSymbolKernel {k : Nat} (p : PMF (Fin (k + 1) → Ω)) :
    Kernel (Fin k → Ω) Ω :=
  Kernel.ofFunOfCountable (fun u ↦ (nextSymbolPMF p u).toMeasure)

/-- For [a finite-word law](hyp:p), [the conditional last-symbol kernel is Markov](goal). -/
instance nextSymbolKernel_isMarkov {k : Nat} (p : PMF (Fin (k + 1) → Ω)) :
    IsMarkovKernel (nextSymbolKernel p) where
  isProbabilityMeasure u := by
    change IsProbabilityMeasure (nextSymbolPMF p u).toMeasure
    infer_instance

/-- Given [a finite-word law](hyp:p), [a strict prefix](hyp:u), and [a final symbol](hyp:x),
[prefix mass times conditional final-symbol mass recovers the joint word mass](goal), including
on null prefixes. -/
lemma prefix_mul_nextSymbol {k : Nat} (p : PMF (Fin (k + 1) → Ω))
    (u : Fin k → Ω) (x : Ω) :
    prefixPMF p u * nextSymbolPMF p u x = p (appendSymbol u x) := by
  classical
  by_cases h : prefixPMF p u = 0
  · have hx : p (appendSymbol u x) = 0 := by
      have hsum := prefixPMF_apply p u
      rw [h] at hsum
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ bot_le)).mp hsum.symm
        x (Finset.mem_univ x)
    simp [nextSymbolPMF, h, hx]
  · rw [nextSymbolPMF, dif_neg h, PMF.ofFintype_apply]
    exact ENNReal.mul_div_cancel h (PMF.apply_ne_top _ _)

/-- If [a finite-word law has strictly positive mass at every word](hyp:hp), [its strict-prefix
marginal also has strictly positive mass everywhere](goal). -/
lemma prefixPMF_fullSupport {k : Nat} {p : PMF (Fin (k + 1) → Ω)}
    (hp : ∀ w, 0 < p w) : ∀ u, 0 < prefixPMF p u := by
  intro u
  rw [prefixPMF_apply]
  exact lt_of_lt_of_le (hp (appendSymbol u (Classical.choice inferInstance)))
    (Finset.single_le_sum (f := fun x ↦ p (appendSymbol u x)) (fun _ _ ↦ bot_le)
      (Finset.mem_univ (Classical.choice inferInstance)))

/-- If [a finite-word law has strictly positive mass at every word](hyp:hp), then for [every
strict prefix](hyp:u), [its totalized conditional last-symbol law has strictly positive mass at
every symbol](goal). -/
lemma nextSymbolPMF_fullSupport {k : Nat} {p : PMF (Fin (k + 1) → Ω)}
    (hp : ∀ w, 0 < p w) (u : Fin k → Ω) : ∀ x, 0 < nextSymbolPMF p u x := by
  intro x
  have hprefix := prefixPMF_fullSupport hp u
  rw [nextSymbolPMF, dif_neg (ne_of_gt hprefix), PMF.ofFintype_apply]
  exact ENNReal.div_pos (ne_of_gt (hp (appendSymbol u x))) (PMF.apply_ne_top _ _)

/-- Given [two strictly positive finite probability mass functions](hyp:hp,hq), [the first
induced measure is absolutely continuous with respect to the second](goal). -/
lemma absolutelyContinuous_of_strictlyPositivePMF {W : Type*} [Fintype W]
    [MeasurableSpace W] [MeasurableSingletonClass W] {p q : PMF W}
    (hp : ∀ w, 0 < p w) (hq : ∀ w, 0 < q w) : p.toMeasure ≪ q.toMeasure := by
  apply Measure.AbsolutelyContinuous.mk
  intro s _ hqs
  have hs_empty : s = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    have hle : q.toMeasure {w} ≤ q.toMeasure s :=
      measure_mono (Set.singleton_subset_iff.mpr hw)
    rw [hqs] at hle
    have hzero : q.toMeasure {w} = 0 := bot_unique hle
    rw [q.toMeasure_apply_singleton w (MeasurableSet.singleton w)] at hzero
    exact (ne_of_gt (hq w)) hzero
  simp [hs_empty]

/-- Given [two finite-word laws that are strictly positive everywhere](hyp:hp,hq), then for
[every strict prefix](hyp:u), [the first conditional last-symbol law is absolutely continuous
with respect to the second](goal). -/
lemma nextSymbolPMF_absolutelyContinuous {k : Nat}
    {p q : PMF (Fin (k + 1) → Ω)} (hp : ∀ w, 0 < p w) (hq : ∀ w, 0 < q w)
    (u : Fin k → Ω) :
    (nextSymbolPMF p u).toMeasure ≪ (nextSymbolPMF q u).toMeasure :=
  absolutelyContinuous_of_strictlyPositivePMF (nextSymbolPMF_fullSupport hp u)
    (nextSymbolPMF_fullSupport hq u)

/-- Given [a finite-word law](hyp:p), [transport by the last-coordinate split equals the
composition of its prefix marginal and conditional last-symbol kernel](goal). -/
lemma lastCoordinateSplit_compProd {k : Nat} (p : PMF (Fin (k + 1) → Ω)) :
    Measure.map (lastCoordinateSplit k) p.toMeasure =
      (prefixPMF p).toMeasure.compProd (nextSymbolKernel p) := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨u, x⟩
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have hpre : (lastCoordinateSplit k : (Fin (k + 1) → Ω) → (Fin k → Ω) × Ω) ⁻¹'
      ({(u, x)} : Set ((Fin k → Ω) × Ω)) = {appendSymbol u x} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hw
      apply (lastCoordinateSplit k).injective
      rw [hw]
      exact ((lastCoordinateSplit k).right_inv (u, x)).symm
    · intro hw
      rw [hw]
      exact (lastCoordinateSplit k).right_inv (u, x)
  rw [hpre, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have hpair : ({(u, x)} : Set ((Fin k → Ω) × Ω)) = {u} ×ˢ {x} := by
    ext y
    simp
  rw [hpair, Measure.compProd_apply_prod (measurableSet_singleton u)
    (measurableSet_singleton x)]
  simp only [lintegral_singleton]
  change p (appendSymbol u x) =
    (nextSymbolPMF p u).toMeasure {x} * (prefixPMF p).toMeasure {u}
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]
  exact (prefix_mul_nextSymbol p u x).symm

/-- Given [two finite-word laws](hyp:p,q), [one chronological extension splits their KL
divergence into the prefix KL and a shared-prefix conditional-kernel KL](goal). -/
lemma klDiv_lastCoordinate_eq_add {k : Nat} (p q : PMF (Fin (k + 1) → Ω)) :
    InformationTheory.klDiv p.toMeasure q.toMeasure =
      InformationTheory.klDiv (prefixPMF p).toMeasure (prefixPMF q).toMeasure +
        InformationTheory.klDiv
          ((prefixPMF p).toMeasure.compProd (nextSymbolKernel p))
          ((prefixPMF p).toMeasure.compProd (nextSymbolKernel q)) := by
  let e : (Fin (k + 1) → Ω) ≃ᵐ (Fin k → Ω) × Ω :=
    { toEquiv := lastCoordinateSplit k
      measurable_toFun := measurable_of_finite _
      measurable_invFun := measurable_of_finite _ }
  rw [← Causalean.Mathlib.Probability.klDiv_map_measurableEquiv e]
  change InformationTheory.klDiv
      (Measure.map (lastCoordinateSplit k) p.toMeasure)
      (Measure.map (lastCoordinateSplit k) q.toMeasure) = _
  rw [lastCoordinateSplit_compProd, lastCoordinateSplit_compProd]
  exact InformationTheory.klDiv_compProd_eq_add _ _ _ _

/-- Given [two finite-word laws](hyp:p,q) whose conditional last-symbol laws satisfy [pointwise
absolute continuity](hyp:hac), [their shared-prefix conditional KL is the prefix-probability-
weighted sum of pointwise conditional divergences](goal). -/
lemma conditionalKL_eq_sum {k : Nat} (p q : PMF (Fin (k + 1) → Ω))
    (hac : ∀ u, (nextSymbolPMF p u).toMeasure ≪ (nextSymbolPMF q u).toMeasure) :
    InformationTheory.klDiv
        ((prefixPMF p).toMeasure.compProd (nextSymbolKernel p))
        ((prefixPMF p).toMeasure.compProd (nextSymbolKernel q)) =
      ∑ u : Fin k → Ω, prefixPMF p u *
        InformationTheory.klDiv (nextSymbolPMF p u).toMeasure
          (nextSymbolPMF q u).toMeasure := by
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_right_of_forall_ac]
  · rw [MeasureTheory.lintegral_fintype]
    apply Finset.sum_congr rfl
    intro u _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]
    change prefixPMF p u * InformationTheory.klDiv (nextSymbolPMF p u).toMeasure
      (nextSymbolPMF q u).toMeasure = _
    rfl
  · exact Filter.Eventually.of_forall hac

/-- Given [two finite-word laws](hyp:p,q) whose conditional last-symbol laws satisfy [pointwise
absolute continuity](hyp:hac), [one chronological extension is the prefix KL plus the explicit
average of pointwise conditional divergences](goal). -/
lemma klDiv_lastCoordinate_eq_add_sum {k : Nat} (p q : PMF (Fin (k + 1) → Ω))
    (hac : ∀ u, (nextSymbolPMF p u).toMeasure ≪ (nextSymbolPMF q u).toMeasure) :
    InformationTheory.klDiv p.toMeasure q.toMeasure =
      InformationTheory.klDiv (prefixPMF p).toMeasure (prefixPMF q).toMeasure +
        ∑ u : Fin k → Ω, prefixPMF p u *
          InformationTheory.klDiv (nextSymbolPMF p u).toMeasure
            (nextSymbolPMF q u).toMeasure := by
  rw [klDiv_lastCoordinate_eq_add, conditionalKL_eq_sum p q hac]

/-- Given [two finite-word laws](hyp:p,q) that [have strictly positive mass at every word](hyp:hp,hq),
[one chronological extension is the prefix KL plus the explicit average of pointwise conditional
divergences](goal). -/
lemma klDiv_lastCoordinate_eq_add_sum_of_fullSupport {k : Nat}
    (p q : PMF (Fin (k + 1) → Ω)) (hp : ∀ w, 0 < p w) (hq : ∀ w, 0 < q w) :
    InformationTheory.klDiv p.toMeasure q.toMeasure =
      InformationTheory.klDiv (prefixPMF p).toMeasure (prefixPMF q).toMeasure +
        ∑ u : Fin k → Ω, prefixPMF p u *
          InformationTheory.klDiv (nextSymbolPMF p u).toMeasure
            (nextSymbolPMF q u).toMeasure :=
  klDiv_lastCoordinate_eq_add_sum p q
    (fun u ↦ nextSymbolPMF_absolutelyContinuous hp hq u)

/-- [The chronological conditional-KL sum](goal) recursively adds the shared-prefix conditional
divergence of two finite-word laws at each word length. -/
noncomputable def chainKL :
    (k : Nat) → PMF (Fin k → Ω) → PMF (Fin k → Ω) → ℝ≥0∞
  | 0, _, _ => 0
  | k + 1, p, q =>
      chainKL k (prefixPMF p) (prefixPMF q) +
        InformationTheory.klDiv
          ((prefixPMF p).toMeasure.compProd (nextSymbolKernel p))
          ((prefixPMF p).toMeasure.compProd (nextSymbolKernel q))

/-- Given [a word length](hyp:k) and [two finite-word laws](hyp:p,q), [their KL divergence equals
the chronological sum of their history-dependent one-step conditional increments](goal). -/
lemma klDiv_eq_chainKL (k : Nat) (p q : PMF (Fin k → Ω)) :
    InformationTheory.klDiv p.toMeasure q.toMeasure = chainKL k p q := by
  induction k with
  | zero =>
      have hpq : p.toMeasure = q.toMeasure := by
        apply Measure.ext
        intro s hs
        by_cases hnonempty : s.Nonempty
        · rcases hnonempty with ⟨x, hx⟩
          have hs_univ : s = Set.univ := by
            apply Set.eq_univ_of_forall
            intro y
            simpa only [Subsingleton.elim y x] using hx
          simp [hs_univ]
        · have hs_empty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
          simp [hs_empty]
      rw [hpq]
      simp [chainKL]
  | succ k ih =>
      rw [klDiv_lastCoordinate_eq_add, ih]
      rfl

end Causalean.Mathlib.InformationTheory.FiniteWordChainRule
