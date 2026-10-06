/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.SequentialSampling
public import Causalean.Stat.FiniteDesign.ProductMeasure
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
# Transport from permutation prefixes to simple random samples

This module identifies the unordered first `K` entries of a uniform permutation with complete
randomization on size-`K` subsets.  It then transports the exact expectation and variance of a
simple-random-sample mean to the ordered prefix representation.
-/

@[expose] public section

open scoped BigOperators Pointwise

namespace Causalean.Experimentation.DesignBased
open Causalean.Stat

open FinitePopulationMoments
open MeasureTheory
open scoped ENNReal

/-- Given [a finite design](hyp:D) and [a map between finite measurable spaces](hyp:f), [the
measure induced by the pushed-forward design equals the measure-theoretic pushforward of the
induced measure](goal). -/
theorem FiniteDesign.toMeasure_map {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (D : FiniteDesign A) (f : A → B) :
    (D.map f).toMeasure = Measure.map f D.toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro b
  rw [FiniteDesign.toMeasure_singleton]
  rw [Measure.map_apply (measurable_of_finite f) (measurableSet_singleton b)]
  rw [FiniteDesign.toMeasure_apply]
  simp only [Measure.dirac_apply' _ (Set.toFinite _).measurableSet]
  rw [FiniteDesign.map_p]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases h : f a = b <;> simp [h]
  · intro a _
    by_cases h : f a = b <;> simp [h, D.p_nonneg]

private lemma FiniteDesign.eq_of_p_eq {Ω : Type*} [Fintype Ω]
    (D E : FiniteDesign Ω) (h : D.p = E.p) : D = E := by
  cases D
  cases E
  simp only [FiniteDesign.mk.injEq]
  exact h

private lemma uniformOrbit_p
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    (D : FiniteDesign G)
    (huniform : ∀ g, D.p g = 1 / (Fintype.card G : ℝ))
    (x : X) :
    ∀ y, (D.map fun g => g • x).p y = 1 / (Fintype.card X : ℝ) := by
  classical
  let _ : Nonempty X := ⟨x⟩
  let P := D.map fun g => g • x
  have hp_eq : ∀ y z : X, P.p y = P.p z := by
    intro y z
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G y z
    let e : G ≃ G := Equiv.mulLeft a
    have hsum := Equiv.sum_comp e (fun g : G =>
      if g • x = z then D.p g else 0)
    dsimp only [P]
    rw [FiniteDesign.map_p, FiniteDesign.map_p, ← hsum]
    apply Finset.sum_congr rfl
    intro g _
    change (if g • x = y then D.p g else 0) =
      if (a * g) • x = z then D.p (a * g) else 0
    rw [mul_smul, huniform, huniform]
    by_cases h : g • x = y
    · rw [if_pos h, if_pos (by rw [h, ha])]
    · rw [if_neg h, if_neg]
      intro hh
      apply h
      exact (MulAction.injective a) (hh.trans ha.symm)
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card X ≠ 0)
  have hsum : (∑ z : X, P.p z) = 1 := P.p_sum
  intro y
  have hconst : (∑ z : X, P.p z) = (Fintype.card X : ℝ) * P.p y := by
    calc
      (∑ z : X, P.p z) = ∑ _z : X, P.p y := by
        apply Finset.sum_congr rfl
        intro z _
        exact hp_eq z y
      _ = (Fintype.card X : ℝ) * P.p y := by simp
  rw [hconst] at hsum
  change P.p y = _
  rw [eq_div_iff hcard]
  simpa [mul_comm] using hsum

/-- Given [a feasible prefix length](hyp:K,hK), the [canonical size-`K` subset of the first
positions](goal) consists of the indices `0, ..., K - 1`. -/
def permutationPrefixBase {N : ℕ} (K : ℕ) (hK : K ≤ N) :
    Set.powersetCard (Fin N) K :=
  ⟨Finset.univ.image (fun i : Fin K => Fin.castLE hK i), by
    change (Finset.univ.image (fun i : Fin K => Fin.castLE hK i)).card = K
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro i _ j _ hij
      apply Fin.ext
      exact congrArg (fun x : Fin N => x.val) hij⟩

/-- Given [a feasible prefix length](hyp:K,hK) and [an ordering](hyp:π), the [unordered prefix
set](goal) contains exactly the population indices in the first `K` positions of the ordering. -/
noncomputable def permutationPrefixSet {N : ℕ} (K : ℕ) (hK : K ≤ N)
    (π : PermutationSampleSpace N) :
    {S : Finset (Fin N) // S.card = K} :=
  ⟨Finset.univ.image (fun i : Fin K => π (Fin.castLE hK i)), by
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro i _ j _ hij
      apply Fin.ext
      exact congrArg (fun x : Fin N => x.val) (π.injective hij)⟩

/-- Given [a feasible prefix length](hyp:K,hK) and [an ordering](hyp:π), [its unordered prefix
set is the image of the canonical prefix under the ordering](goal). -/
lemma permutationPrefixSet_eq_smul {N : ℕ} (K : ℕ) (hK : K ≤ N)
    (π : PermutationSampleSpace N) :
    permutationPrefixSet K hK π = π • permutationPrefixBase K hK := by
  apply Subtype.ext
  simp only [permutationPrefixSet, permutationPrefixBase, Set.powersetCard.coe_smul,
    Finset.smul_finset_def, Finset.image_image]
  congr 1

/-- Given [a feasible sample size](hyp:K,hK), [the unordered first-`K` prefix of a uniform
permutation has exactly the complete-randomization law](goal). -/
theorem uniformPermutationDesign_map_prefixSet_eq_completeRandomization
    {N : ℕ} (K : ℕ) (hK : K ≤ N) :
    (uniformPermutationDesign N).map (permutationPrefixSet K hK) =
      completeRandomization (V := Fin N) K (by simpa using hK) := by
  classical
  letI : MulAction (Equiv.Perm (Fin N)) {S : Finset (Fin N) // S.card = K} :=
    inferInstanceAs (MulAction (Equiv.Perm (Fin N)) (Set.powersetCard (Fin N) K))
  letI : MulAction.IsPretransitive (Equiv.Perm (Fin N))
      {S : Finset (Fin N) // S.card = K} :=
    Set.powersetCard.isPretransitive
  let x : {S : Finset (Fin N) // S.card = K} :=
    ⟨(permutationPrefixBase K hK).val, (permutationPrefixBase K hK).property⟩
  apply FiniteDesign.eq_of_p_eq
  funext S
  have hp := uniformOrbit_p (uniformPermutationDesign N) (fun π => by rfl) x S
  have hfun : (fun π : PermutationSampleSpace N => π • x) = permutationPrefixSet K hK := by
    funext π
    exact (permutationPrefixSet_eq_smul K hK π).symm
  rw [hfun] at hp
  change ((uniformPermutationDesign N).map (permutationPrefixSet K hK)).p S =
      (completeRandomization (V := Fin N) K (by simpa using hK)).p S
  exact hp

/-- Given [a feasible sample size](hyp:K,hK), [population outcomes](hyp:y), and [an
ordering](hyp:π), [the ordinary mean of the unordered prefix set equals the ordered prefix
sample mean](goal). -/
lemma sampleMean_permutationPrefixSet_eq {N : ℕ} (K : ℕ) (hK : K ≤ N)
    (y : Fin N → ℝ) (π : PermutationSampleSpace N) :
    sampleMean K y (permutationPrefixSet K hK π) = permutationSampleMean K hK y π := by
  classical
  unfold sampleMean permutationSampleMean
  change (∑ i : Fin N, if i ∈
      Finset.univ.image (fun j : Fin K => π (Fin.castLE hK j))
    then y i else 0) / (K : ℝ) =
      (∑ j : Fin K, y (π (Fin.castLE hK j))) / (K : ℝ)
  rw [Finset.sum_ite_mem_eq, Finset.sum_image]
  intro i _ j _ hij
  apply Fin.ext
  exact congrArg (fun x : Fin N => x.val) (π.injective hij)

private lemma FiniteDesign.Var_map {A B : Type*} [Fintype A] [Fintype B]
    (D : FiniteDesign A) (f : A → B) (g : B → ℝ) :
    (D.map f).Var g = D.Var (fun a => g (f a)) := by
  unfold FiniteDesign.Var
  rw [D.E_map f g]
  exact D.E_map f _

/-- Given [a positive feasible sample size](hyp:K,hK,hKpos) and [population outcomes](hyp:y),
[the ordered prefix sample mean is unbiased for the population mean](goal). -/
theorem uniformPermutationDesign_E_permutationSampleMean
    {N : ℕ} (K : ℕ) (hK : K ≤ N) (hKpos : 0 < K) (y : Fin N → ℝ) :
    (uniformPermutationDesign N).E (permutationSampleMean K hK y) = popMean y := by
  rw [← E_sampleMean K (by simpa using hK) hKpos y]
  rw [← uniformPermutationDesign_map_prefixSet_eq_completeRandomization K hK]
  rw [FiniteDesign.E_map]
  apply FiniteDesign.E_congr
  intro π
  exact (sampleMean_permutationPrefixSet_eq K hK y π).symm

/-- Given [a positive feasible sample size](hyp:K,hK,hKpos), [a population of at least two
units](hyp:N,hN), and [population outcomes](hyp:y), [the ordered prefix sample mean has the exact
sampling-without-replacement variance](goal). -/
theorem uniformPermutationDesign_Var_permutationSampleMean
    {N : ℕ} (K : ℕ) (hK : K ≤ N) (hKpos : 0 < K) (hN : 2 ≤ N)
    (y : Fin N → ℝ) :
    (uniformPermutationDesign N).Var (permutationSampleMean K hK y) =
      (1 / (K : ℝ) - 1 / (N : ℝ)) * popVar y := by
  have hmap :
      ((uniformPermutationDesign N).map (permutationPrefixSet K hK)).Var (sampleMean K y) =
        (uniformPermutationDesign N).Var (permutationSampleMean K hK y) := by
    rw [FiniteDesign.Var_map]
    apply FiniteDesign.Var_congr
    intro π
    exact sampleMean_permutationPrefixSet_eq K hK y π
  rw [← hmap, uniformPermutationDesign_map_prefixSet_eq_completeRandomization K hK]
  simpa using Var_sampleMean K (by simpa using hK) hKpos (by simpa using hN) y

end Causalean.Experimentation.DesignBased
