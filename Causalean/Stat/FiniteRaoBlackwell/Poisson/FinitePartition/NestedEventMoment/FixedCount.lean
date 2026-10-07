module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.Basic
public import Causalean.Stat.UStatistic.OrderM.Variance

/-!
# Fixed-count iid nested-event factorial moment

This module evaluates the ordered event kernel under a product probability law
and then evaluates the weighted nested-event statistic on each fixed-size iid
sample fibre.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat

variable {X : Type*} [MeasurableSpace X]

/-- Two [events](hyp:A,B) with [measurable membership](hyp:hA,hB), an [order](hyp:v),
and [positive order](hyp:hv) give a [measurable ordered nested-event kernel](goal). -/
theorem measurable_nestedEventKernel (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (v : ℕ) (hv : 1 ≤ v) :
    Measurable (nestedEventKernel A B v hv) := by
  classical
  unfold nestedEventKernel
  have hfirst : MeasurableSet {x : Fin v → X | x ⟨0, hv⟩ ∈ A} :=
    hA.preimage (measurable_pi_apply _)
  have htail : MeasurableSet {x : Fin v → X |
      ∀ j : Fin v, j.val ≠ 0 → x j ∈ B} := by
    have hm : MeasurableSet (⋂ j : Fin v,
        {x : Fin v → X | j.val ≠ 0 → x j ∈ B}) := by
      apply MeasurableSet.iInter
      intro j
      by_cases hj : j.val = 0
      · simp [hj]
      · have hpre : MeasurableSet {x : Fin v → X | x j ∈ B} :=
          hB.preimage (measurable_pi_apply j)
        convert hpre using 1
        ext x
        simp [hj]
    convert hm using 1
    ext x
    simp
  exact measurable_const.ite (hfirst.inter htail) measurable_const

omit [MeasurableSpace X] in
private theorem nestedEventKernel_eq_indicator (A B : Set X)
    (v : ℕ) (hv : 1 ≤ v) (x : Fin v → X) :
    nestedEventKernel A B v hv x =
      (Set.univ.pi (fun j : Fin v => if j.val = 0 then A else B)).indicator
        (fun _ => (1 : ℝ)) x := by
  classical
  have hmem : x ∈ Set.univ.pi (fun j : Fin v => if j.val = 0 then A else B) ↔
      x ⟨0, hv⟩ ∈ A ∧ ∀ j : Fin v, j.val ≠ 0 → x j ∈ B := by
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h
      constructor
      · simpa using h ⟨0, hv⟩
      · intro j hj
        simpa [hj] using h j
    · rintro ⟨hA, hB⟩ j
      by_cases hj : j.val = 0
      · have hj0 : j = ⟨0, hv⟩ := Fin.ext hj
        simpa [hj, hj0] using hA
      · simpa [hj] using hB j hj
  simp only [nestedEventKernel, Set.indicator_apply, hmem]

/-- Under an [observation probability law](hyp:P), two [events](hyp:A,B) with
[measurable membership](hyp:hA,hB), an [order](hyp:v), and [positive order](hyp:hv), the
[ordered nested-event kernel is integrable under the iid product law](goal). -/
theorem integrable_nestedEventKernel (P : Measure X) [IsProbabilityMeasure P]
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (v : ℕ) (hv : 1 ≤ v) :
    Integrable (nestedEventKernel A B v hv)
      (Measure.pi (fun _ : Fin v => P)) := by
  classical
  let C : Set (Fin v → X) :=
    Set.univ.pi (fun j : Fin v => if j.val = 0 then A else B)
  have hC : MeasurableSet C := by
    apply MeasurableSet.pi Set.countable_univ
    intro j _
    split_ifs <;> assumption
  have hfin : IsFiniteMeasure (Measure.pi (fun _ : Fin v => P)) := inferInstance
  have hint : Integrable (C.indicator (fun _ => (1 : ℝ)))
      (Measure.pi (fun _ : Fin v => P)) :=
    (integrable_const (1 : ℝ)).indicator hC
  convert hint using 1
  funext x
  exact nestedEventKernel_eq_indicator A B v hv x

/-- Under an [observation probability law](hyp:P), two [events](hyp:A,B) with
[measurable membership](hyp:hA,hB), an [order](hyp:v), and [positive order](hyp:hv), the
[iid mean of the ordered nested-event kernel equals the smaller-event probability times the
required power of the larger-event probability](goal). -/
theorem integral_nestedEventKernel (P : Measure X) [IsProbabilityMeasure P]
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (v : ℕ) (hv : 1 ≤ v) :
    (∫ x : Fin v → X, nestedEventKernel A B v hv x
        ∂Measure.pi (fun _ : Fin v => P)) =
      (P A).toReal * (P B).toReal ^ (v - 1) := by
  classical
  let C : Set (Fin v → X) :=
    Set.univ.pi (fun j : Fin v => if j.val = 0 then A else B)
  have hC : MeasurableSet C := by
    apply MeasurableSet.pi Set.countable_univ
    intro j _
    split_ifs <;> assumption
  have hprob : (Measure.pi (fun _ : Fin v => P)) C =
      P A * (P B) ^ (v - 1) := by
    change (Measure.pi (fun _ : Fin v => P))
      (Set.univ.pi (fun j : Fin v => if j.val = 0 then A else B)) = _
    rw [Measure.pi_pi]
    rw [Fintype.prod_eq_mul_prod_compl ⟨0, hv⟩]
    simp only [↓reduceIte]
    have htail : (∏ j ∈ ({⟨0, hv⟩}ᶜ : Finset (Fin v)),
        P (if j.val = 0 then A else B)) =
        (P B) ^ (v - 1) := by
      have heq : ∀ j ∈ ({⟨0, hv⟩}ᶜ : Finset (Fin v)),
          P (if j.val = 0 then A else B) = P B := by
        intro j hj
        have hj0 : j ≠ ⟨0, hv⟩ := by simpa using hj
        have hjv : j.val ≠ 0 := by
          intro h
          exact hj0 (Fin.ext h)
        simp [hjv]
      rw [Finset.prod_congr rfl heq, Finset.prod_const]
      simp [Finset.card_compl, Fintype.card_fin]
    rw [htail]
  have hkernel : nestedEventKernel A B v hv =
      C.indicator (fun _ => (1 : ℝ)) := by
    funext x
    exact nestedEventKernel_eq_indicator A B v hv x
  rw [hkernel, integral_indicator hC, setIntegral_const]
  simp only [smul_eq_mul, mul_one, Measure.real]
  rw [hprob, ENNReal.toReal_mul, ENNReal.toReal_pow]

/-- Under an [observation probability law](hyp:P), two [events](hyp:A,B) with
[measurable membership](hyp:hA,hB) and [the first contained in the second](hyp:hAB), an
[order](hyp:v) with [positive order](hyp:hv), and a [fixed sample size](hyp:n), the [iid
mean of the weighted nested-event factorial equals the falling factorial of the sample size of
the given order, times the smaller-event probability, times the larger-event probability raised
to the order minus one](goal). -/
theorem integral_weightedFactorial_fixedCount (P : Measure X)
    [IsProbabilityMeasure P] (A B : Set X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ⊆ B) (v n : ℕ) (hv : 1 ≤ v) :
    (∫ x : Fin n → X, weightedFactorial A B v (fixedSizeEmbed n x)
        ∂Measure.pi (fun _ : Fin n => P)) =
      (n.descFactorial v : ℝ) * (P A).toReal * (P B).toReal ^ (v - 1) := by
  /- Rewrite by weightedFactorial_eq_injectiveTupleSum. For each injective
     t : Fin v → Fin n, the coordinate projection x ↦ fun j => x (t j)
     pushes the finite product law P^n to P^v. Prove this using `iIndepFun_pi`
     and `iIndepFun_iff_map_fun_eq_pi_map` (or a finite-product marginal
     theorem); then transfer integrability and the kernel integral. Sum over
     injectiveTuples and use injectiveTuples_card_eq_descFactorial. This also
     handles n < v because the tuple finset is empty and n.descFactorial v = 0.
     The IIDSample theorem in OrderM.Variance is a useful analogue but its
     sample interface is indexed by ℕ, unlike this finite product fibre. -/
  classical
  let μ : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => P)
  let ν : Measure (Fin v → X) := Measure.pi (fun _ : Fin v => P)
  let f (t : Fin v → Fin n) (x : Fin n → X) : Fin v → X := fun j => x (t j)
  have hproj (t : Fin v → Fin n) (ht : Function.Injective t) :
      μ.map (f t) = ν := by
    have hind : iIndepFun (fun j : Fin v => Function.eval (t j)) μ :=
      (iIndepFun_pi (X := fun _ : Fin n => id)
        (fun _ => measurable_id.aemeasurable)).precomp ht
    have hmap := (iIndepFun_iff_map_fun_eq_pi_map
      (fun j : Fin v => (measurable_pi_apply (t j)).aemeasurable)).mp hind
    calc
      μ.map (f t) = Measure.pi (fun j : Fin v => μ.map (Function.eval (t j))) := hmap
      _ = ν := by
        congr 1
        funext j
        exact (measurePreserving_eval (fun _ : Fin n => P) (t j)).map_eq
  have hterm (t : Fin v → Fin n) (ht : t ∈ injectiveTuples v n) :
      (∫ x : Fin n → X, nestedEventKernel A B v hv (f t x) ∂μ) =
        (P A).toReal * (P B).toReal ^ (v - 1) := by
    have hti : Function.Injective t := by simpa [injectiveTuples] using ht
    have hm : Measurable (f t) :=
      measurable_pi_lambda _ (fun j => measurable_pi_apply (t j))
    have hk := (integrable_nestedEventKernel P A B hA hB v hv).aestronglyMeasurable
    calc
      _ = ∫ y : Fin v → X, nestedEventKernel A B v hv y ∂(μ.map (f t)) :=
        (integral_map hm.aemeasurable (by simpa [hproj t hti, ν] using hk)).symm
      _ = _ := by rw [hproj t hti]; exact integral_nestedEventKernel P A B hA hB v hv
  rw [show (fun x : Fin n → X => weightedFactorial A B v (fixedSizeEmbed n x)) =
      (fun x => ∑ t ∈ injectiveTuples v n, nestedEventKernel A B v hv (f t x)) by
        funext x
        exact weightedFactorial_eq_injectiveTupleSum A B hAB v n hv x]
  rw [integral_finsetSum]
  · have hsum : (∑ t ∈ injectiveTuples v n,
        ∫ x : Fin n → X, nestedEventKernel A B v hv (f t x) ∂μ) =
        ∑ t ∈ injectiveTuples v n,
          (P A).toReal * (P B).toReal ^ (v - 1) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hterm t ht
    rw [show Measure.pi (fun _ : Fin n => P) = μ by rfl, hsum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [injectiveTuples_card_eq_descFactorial]
    ring
  · intro t ht
    have hti : Function.Injective t := by simpa [injectiveTuples] using ht
    have hm : Measurable (f t) :=
      measurable_pi_lambda _ (fun j => measurable_pi_apply (t j))
    have hk := integrable_nestedEventKernel P A B hA hB v hv
    have hkmap : Integrable (nestedEventKernel A B v hv) (μ.map (f t)) := by
      rw [hproj t hti]
      exact hk
    exact (integrable_map_measure hkmap.aestronglyMeasurable hm.aemeasurable).mp hkmap

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
