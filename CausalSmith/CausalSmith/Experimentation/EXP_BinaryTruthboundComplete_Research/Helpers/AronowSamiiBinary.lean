import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.BooleanMobius
import Causalean.Experimentation.ExposureMappingInterference.Variance.Conservative
import Causalean.Experimentation.DesignBased.Exposure

/-! Binary Horvitz–Thompson specialization of the Aronow–Samii zero-joint correction. -/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- A local observed binary coordinate, coerced to a real. -/
def observedReal (E : Setup) (z : E.Omega) (y : E.O z → Fin 2) (i : Fin E.K) : ℝ :=
  if h : i ∈ E.O z then ((y ⟨i, h⟩ : ℕ) : ℝ) else 0

/-- The assignment-level simplified Aronow–Samii table. -/
noncomputable def asTable (E : Setup)
    (_hsingle : ∀ i, 0 < jointObsProb E {i})
    (_hHT : ∀ z i, E.v z i = (if i ∈ E.O z then 1 else 0) / jointObsProb E {i}) :
    AssignmentRule E := fun z y =>
  (∑ i, ∑ k,
    if 0 < jointObsProb E {i, k} then
      (if {i, k} ⊆ E.O z then 1 else 0) *
        ((jointObsProb E {i, k} - jointObsProb E {i} * jointObsProb E {k}) *
          observedReal E z y i * observedReal E z y k) /
        (jointObsProb E {i, k} * jointObsProb E {i} * jointObsProb E {k})
    else 0) +
  (∑ i, ∑ k,
    if i ≠ k ∧ jointObsProb E {i, k} = 0 then
      observedReal E z y i / (2 * jointObsProb E {i}) +
        observedReal E z y k / (2 * jointObsProb E {k})
    else 0)
  -- @realizes g_z^{\mathrm{AS}}(positive-joint quadratic terms plus Young singleton replacements)

/-- Expected binary Aronow–Samii correction. -/
-- @node: def:aronow-samii-binary-correction
noncomputable def asBinaryCorrection (E : Setup)
    (hsingle : ∀ i, 0 < jointObsProb E {i})
    (hHT : ∀ z i, E.v z i = (if i ∈ E.O z then 1 else 0) / jointObsProb E {i}) :
    Theta E → ℝ :=
  expectedRule E (asTable E hsingle hHT)
  -- @realizes b_{\mathrm{AS}}(design expectation of g_z^{AS})

/-- In [a finite binary experiment](hyp:E) with [positive singleton observation probabilities](hyp:hsingle) and [Horvitz–Thompson scores](hyp:hHT), [the correction excess at every schedule equals half the sum of squared pair totals over distinct pairs that are never jointly observed](goal). -/
-- @node: asBinaryCorrection_excess_identity
lemma asBinaryCorrection_excess_identity (E : Setup)
    (hsingle : ∀ i, 0 < jointObsProb E {i})
    (hHT : ∀ z i, E.v z i = (if i ∈ E.O z then 1 else 0) / jointObsProb E {i}) :
    ∀ θ, asBinaryCorrection E hsingle hHT θ - trueVarianceFn E θ =
      (1 / 2 : ℝ) * ∑ i, ∑ k,
        if i ≠ k ∧ jointObsProb E {i, k} = 0 then
          (((θ i : ℕ) : ℝ) + ((θ k : ℕ) : ℝ)) ^ 2 else 0 := by
  classical
  intro θ
  let t : Fin E.K → ℝ := fun i => ((θ i : ℕ) : ℝ)
  let R : E.Omega → Fin E.K → ℝ := fun z i => if i ∈ E.O z then 1 else 0
  have hobs (z : E.Omega) (i : Fin E.K) :
      observedReal E z (restrict E z θ) i = R z i * t i := by
    simp [observedReal, restrict, R, t]
  have hsingleE (i : Fin E.K) : E.design.E (fun z => R z i) = jointObsProb E {i} := by
    unfold jointObsProb Causalean.Experimentation.DesignBased.FiniteDesign.E
    apply Finset.sum_congr rfl
    intro z _
    simp only [R]
    by_cases hi : i ∈ E.O z <;> simp [hi]
  have hpairE (i k : Fin E.K) :
      E.design.E (fun z => R z i * R z k) = jointObsProb E {i, k} := by
    unfold jointObsProb Causalean.Experimentation.DesignBased.FiniteDesign.E
    apply Finset.sum_congr rfl
    intro z _
    simp only [R]
    have hpair : {i, k} ⊆ E.O z ↔ i ∈ E.O z ∧ k ∈ E.O z := by
      constructor
      · intro h
        exact ⟨h (by simp), h (by simp)⟩
      · rintro ⟨hi, hk⟩ j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl <;> assumption
    by_cases hi : i ∈ E.O z <;> by_cases hk : k ∈ E.O z <;>
      simp [hpair, hi, hk]
  have htarget (i : Fin E.K) : targetCoeff E i = 1 := by
    unfold targetCoeff
    simp_rw [hHT]
    rw [show E.design.E (fun z => (if i ∈ E.O z then 1 else 0) /
        jointObsProb E {i}) = E.design.E (fun z => R z i) / jointObsProb E {i} by
      rw [div_eq_mul_inv, ← E.design.E_mul_const]
      apply E.design.E_congr
      intro z
      simp [R, div_eq_mul_inv]]
    rw [hsingleE]
    exact div_self (ne_of_gt (hsingle i))
  have hsecond (i k : Fin E.K) :
      E.design.E (fun z =>
        observedReal E z (restrict E z θ) i / (2 * jointObsProb E {i}) +
          observedReal E z (restrict E z θ) k / (2 * jointObsProb E {k})) =
        (t i + t k) / 2 := by
    have hobsE (j : Fin E.K) :
        E.design.E (fun z => observedReal E z (restrict E z θ) j) =
          t j * jointObsProb E {j} := by
      calc
        E.design.E (fun z => observedReal E z (restrict E z θ) j) =
            E.design.E (fun z => t j * R z j) := by
              apply E.design.E_congr
              intro z
              rw [hobs]
              ring
        _ = t j * E.design.E (fun z => R z j) := E.design.E_const_mul _ _
        _ = t j * jointObsProb E {j} := by rw [hsingleE]
    rw [E.design.E_add]
    rw [show E.design.E (fun z => observedReal E z (restrict E z θ) i /
          (2 * jointObsProb E {i})) =
        E.design.E (fun z => observedReal E z (restrict E z θ) i) /
          (2 * jointObsProb E {i}) by
      rw [div_eq_mul_inv, ← E.design.E_mul_const]
      apply E.design.E_congr
      intro z
      simp [div_eq_mul_inv]]
    rw [show E.design.E (fun z => observedReal E z (restrict E z θ) k /
          (2 * jointObsProb E {k})) =
        E.design.E (fun z => observedReal E z (restrict E z θ) k) /
          (2 * jointObsProb E {k}) by
      rw [div_eq_mul_inv, ← E.design.E_mul_const]
      apply E.design.E_congr
      intro z
      simp [div_eq_mul_inv]]
    rw [hobsE, hobsE]
    field_simp [ne_of_gt (hsingle i), ne_of_gt (hsingle k)]
    <;> ring
  have hjoint_nonneg (i k : Fin E.K) : 0 ≤ jointObsProb E {i, k} := by
    unfold jointObsProb Causalean.Experimentation.DesignBased.FiniteDesign.E
    exact Finset.sum_nonneg fun z _ => mul_nonneg (E.design.p_nonneg z) (by positivity)
  have hvariance (i k : Fin E.K) :
      varianceMatrix E i k =
        jointObsProb E {i, k} / (jointObsProb E {i} * jointObsProb E {k}) - 1 := by
    unfold varianceMatrix
    rw [htarget i, htarget k]
    simp_rw [hHT]
    rw [show E.design.E (fun z =>
        ((if i ∈ E.O z then 1 else 0) / jointObsProb E {i}) *
          ((if k ∈ E.O z then 1 else 0) / jointObsProb E {k})) =
        E.design.E (fun z => R z i * R z k) /
          (jointObsProb E {i} * jointObsProb E {k}) by
      rw [div_eq_mul_inv, ← E.design.E_mul_const]
      apply E.design.E_congr
      intro z
      simp only [R]
      ring]
    rw [hpairE]
    ring
  have hfirst (i k : Fin E.K) (hp : 0 < jointObsProb E {i, k}) :
      E.design.E (fun z =>
        (if {i, k} ⊆ E.O z then 1 else 0) *
          ((jointObsProb E {i, k} - jointObsProb E {i} * jointObsProb E {k}) *
            observedReal E z (restrict E z θ) i *
              observedReal E z (restrict E z θ) k) /
          (jointObsProb E {i, k} * jointObsProb E {i} * jointObsProb E {k})) =
        varianceMatrix E i k * t i * t k := by
    rw [hvariance]
    rw [show E.design.E (fun z =>
        (if {i, k} ⊆ E.O z then 1 else 0) *
          ((jointObsProb E {i, k} - jointObsProb E {i} * jointObsProb E {k}) *
            observedReal E z (restrict E z θ) i *
              observedReal E z (restrict E z θ) k) /
          (jointObsProb E {i, k} * jointObsProb E {i} * jointObsProb E {k})) =
        E.design.E (fun z => R z i * R z k) *
          ((jointObsProb E {i, k} - jointObsProb E {i} * jointObsProb E {k}) *
            t i * t k /
            (jointObsProb E {i, k} * jointObsProb E {i} * jointObsProb E {k})) by
      rw [← E.design.E_mul_const]
      apply E.design.E_congr
      intro z
      rw [hobs, hobs]
      have hpair : {i, k} ⊆ E.O z ↔ i ∈ E.O z ∧ k ∈ E.O z := by
        constructor
        · intro h
          exact ⟨h (by simp), h (by simp)⟩
        · rintro ⟨hi, hk⟩ j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl <;> assumption
      by_cases hi : i ∈ E.O z <;> by_cases hk : k ∈ E.O z <;>
        simp [R, hpair, hi, hk] <;> ring]
    rw [hpairE]
    field_simp [ne_of_gt hp, ne_of_gt (hsingle i), ne_of_gt (hsingle k)]
    <;> ring
  unfold asBinaryCorrection expectedRule asTable trueVarianceFn
  rw [E.design.E_add]
  simp_rw [E.design.E_sum Finset.univ]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  have halgebra : (∑ i, ∑ k,
        ((if 0 < jointObsProb E {i, k} then
            varianceMatrix E i k * t i * t k else 0) +
          (if i ≠ k ∧ jointObsProb E {i, k} = 0 then (t i + t k) / 2 else 0) -
          varianceMatrix E i k * t i * t k)) =
      ∑ i, ∑ k, if i ≠ k ∧ jointObsProb E {i, k} = 0 then
        (1 / 2 : ℝ) * (t i + t k) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        by_cases hp : 0 < jointObsProb E {i, k}
        · simp [hp, ne_of_gt hp]
        · have hz : jointObsProb E {i, k} = 0 :=
            le_antisymm (not_lt.mp hp) (hjoint_nonneg i k)
          by_cases hik : i = k
          · subst k
            have : jointObsProb E {i, i} = jointObsProb E {i} := by simp
            exact (ne_of_gt (hsingle i) (this ▸ hz)).elim
          · simp [hp, hz, hik, hvariance, t]
            have hi : ((θ i : ℕ) : ℝ) ^ 2 = ((θ i : ℕ) : ℝ) := by
              have hi' : (θ i : ℕ) = 0 ∨ (θ i : ℕ) = 1 := by omega
              rcases hi' with hi' | hi' <;> simp [hi']
            have hk : ((θ k : ℕ) : ℝ) ^ 2 = ((θ k : ℕ) : ℝ) := by
              have hk' : (θ k : ℕ) = 0 ∨ (θ k : ℕ) = 1 := by omega
              rcases hk' with hk' | hk' <;> simp [hk']
            nlinarith [hi, hk]
  -- Reduce both design expectations termwise, then use the Boolean identity x²=x.
  simp_rw [show ∀ i k,
      E.design.E (fun z =>
        if 0 < jointObsProb E {i, k} then
          (if {i, k} ⊆ E.O z then 1 else 0) *
              ((jointObsProb E {i, k} - jointObsProb E {i} * jointObsProb E {k}) *
                observedReal E z (restrict E z θ) i * observedReal E z (restrict E z θ) k) /
              (jointObsProb E {i, k} * jointObsProb E {i} * jointObsProb E {k})
        else 0) =
      if 0 < jointObsProb E {i, k} then varianceMatrix E i k * t i * t k else 0 from
    fun i k => by split <;> simp_all [hfirst]]
  simp_rw [show ∀ i k,
      E.design.E (fun z =>
        if i ≠ k ∧ jointObsProb E {i, k} = 0 then
          observedReal E z (restrict E z θ) i / (2 * jointObsProb E {i}) +
            observedReal E z (restrict E z θ) k / (2 * jointObsProb E {k})
        else 0) =
      if i ≠ k ∧ jointObsProb E {i, k} = 0 then (t i + t k) / 2 else 0 from
    fun i k => by split <;> simp_all [hsecond]]
  dsimp [t] at halgebra ⊢
  rw [halgebra]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split <;> simp_all

/-- In [an experiment](hyp:E), [a coordinate set](hyp:S) with [positive joint observation probability](hyp:h) [belongs to the observable complex](goal). -/
-- @node: observableComplex_of_jointObsProb_pos
lemma observableComplex_of_jointObsProb_pos (E : Setup) (S : Finset (Fin E.K))
    (h : 0 < jointObsProb E S) : S ∈ observableComplex E := by
  classical
  unfold observableComplex
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨by simp, ?_⟩
  by_contra hn
  push_neg at hn
  unfold jointObsProb Causalean.Experimentation.DesignBased.FiniteDesign.E at h
  simp only [if_neg (hn _), mul_zero, Finset.sum_const_zero] at h
  exact (lt_irrefl 0 h)

/-- In [an experiment](hyp:E) with [positive singleton observation probabilities](hyp:hsingle) and [Horvitz–Thompson scores](hyp:hHT), the [covariance entry for two coordinates](hyp:i,k) [is their joint observation probability divided by the product of their marginal observation probabilities, minus one](goal). -/
-- @node: ht_varianceMatrix_formula
lemma ht_varianceMatrix_formula (E : Setup)
    (hsingle : ∀ i, 0 < jointObsProb E {i})
    (hHT : ∀ z i, E.v z i = (if i ∈ E.O z then 1 else 0) / jointObsProb E {i})
    (i k : Fin E.K) :
    varianceMatrix E i k =
      jointObsProb E {i, k} / (jointObsProb E {i} * jointObsProb E {k}) - 1 := by
  classical
  have hsingleE (j : Fin E.K) :
      E.design.E (fun z => if j ∈ E.O z then (1 : ℝ) else 0) = jointObsProb E {j} := by
    unfold jointObsProb Causalean.Experimentation.DesignBased.FiniteDesign.E
    apply Finset.sum_congr rfl
    intro z _
    by_cases hj : j ∈ E.O z <;> simp [hj]
  have htarget (j : Fin E.K) : targetCoeff E j = 1 := by
    unfold targetCoeff
    simp_rw [hHT]
    rw [show E.design.E (fun z => (if j ∈ E.O z then 1 else 0) /
        jointObsProb E {j}) =
        E.design.E (fun z => if j ∈ E.O z then (1 : ℝ) else 0) /
          jointObsProb E {j} by
      rw [div_eq_mul_inv, ← E.design.E_mul_const]
      apply E.design.E_congr
      intro z
      simp [div_eq_mul_inv]]
    rw [hsingleE]
    exact div_self (ne_of_gt (hsingle j))
  have hpairE : E.design.E (fun z =>
      (if i ∈ E.O z then (1 : ℝ) else 0) * (if k ∈ E.O z then 1 else 0)) =
      jointObsProb E {i, k} := by
    unfold jointObsProb Causalean.Experimentation.DesignBased.FiniteDesign.E
    apply Finset.sum_congr rfl
    intro z _
    have hpair : {i, k} ⊆ E.O z ↔ i ∈ E.O z ∧ k ∈ E.O z := by
      constructor
      · intro hs
        exact ⟨hs (by simp), hs (by simp)⟩
      · rintro ⟨hi, hk⟩ j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl <;> assumption
    by_cases hi : i ∈ E.O z <;> by_cases hk : k ∈ E.O z <;> simp [hpair, hi, hk]
  unfold varianceMatrix
  rw [htarget, htarget]
  simp_rw [hHT]
  rw [show E.design.E (fun z =>
      ((if i ∈ E.O z then 1 else 0) / jointObsProb E {i}) *
        ((if k ∈ E.O z then 1 else 0) / jointObsProb E {k})) =
      E.design.E (fun z =>
        (if i ∈ E.O z then (1 : ℝ) else 0) * (if k ∈ E.O z then 1 else 0)) /
        (jointObsProb E {i} * jointObsProb E {k}) by
    rw [div_eq_mul_inv, ← E.design.E_mul_const]
    apply E.design.E_congr
    intro z
    ring]
  rw [hpairE]
  ring

end CausalSmith.Experimentation.BinaryTruthbound
