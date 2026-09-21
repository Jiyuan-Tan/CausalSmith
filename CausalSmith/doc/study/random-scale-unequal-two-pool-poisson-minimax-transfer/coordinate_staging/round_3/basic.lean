/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.Basic
import Causalean.Stat.Minimax.Mixture

/-!
# Ordered retention for random-scale unequal Poisson pools

This module defines a measurable deterministic retention kernel from two ordered finite
Poisson records to two fixed, possibly unequal, sample arrays.  It records the exact product
law of the retained arrays on the event that both counts are large enough, and packages the
conditional laws used by a shared-random-scale experiment.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

universe uTheta uX uY uA

variable {Theta : Type uTheta} {X : Type uX} {Y : Type uY}
  [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]

/-- Given [the first observation space](hyp:X) and [the second observation space](hyp:Y),
[the raw two-pool observation](goal) consists of two ordered finite records with unrelated
realized counts. [It is represented by their product](step:1). -/
abbrev RawTwoPool (X : Type uX) (Y : Type uY)
    [MeasurableSpace X] [MeasurableSpace Y] := FiniteSample X × FiniteSample Y

/-- Given [a raw experiment kernel](hyp:K), [the first mark kernel](hyp:P), [the second mark
kernel](hyp:Q), [a shared nonnegative scale](hyp:S), and [two intensity multipliers](hyp:u,v),
[the shared-scale two-pool experiment property](goal) says that each parameter selects two
independent marked Poisson records with the stated scaled intensities. [It is given by the
fibrewise product-law identity](step:1). -/
def IsRandomScaleTwoPoolExperiment
    (K : Kernel Theta (RawTwoPool X Y))
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    [∀ theta, IsProbabilityMeasure (P theta)]
    [∀ theta, IsProbabilityMeasure (Q theta)]
    (S : Theta → ℝ≥0) (u v : ℝ≥0) : Prop :=
  ∀ theta,
    K theta =
      (finitePoissonSampleLaw (P theta) (u * S theta)).prod
        (finitePoissonSampleLaw (Q theta) (v * S theta))

/-- Given [the first fixed sample size](hyp:n), [the second fixed sample size](hyp:m), [a
fixed-pool experiment kernel](hyp:K), [the first mark kernel](hyp:P), and [the second mark
kernel](hyp:Q), [the fixed unequal-pool experiment property](goal) says that each parameter
selects the corresponding independent iid product law. [It is given by the fibrewise
product-law identity](step:1). -/
def IsFixedTwoPoolExperiment
    (n m : ℕ)
    (K : Kernel Theta (FixedPools (X := X) (Y := Y) n m))
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    [∀ theta, IsProbabilityMeasure (P theta)]
    [∀ theta, IsProbabilityMeasure (Q theta)] : Prop :=
  ∀ theta, K theta = fixedPoolsLaw (P theta) (Q theta) n m

/-- Given [the first requested prefix length](hyp:n) and [the second requested prefix
length](hyp:m), [the retention-success event](goal) is that both raw records contain their
respective requested numbers of marks. [It is given by the conjunction of the two count
bounds](step:1). -/
def retentionSuccessSet (n m : ℕ) : Set (RawTwoPool X Y) :=
  {z | n ≤ z.1.count ∧ m ≤ z.2.count}

/-- Given [the first requested prefix length](hyp:n) and [the second requested prefix
length](hyp:m), [the retention-failure event](goal) is that at least one raw record is too
short. [It is given by the union of the two lower-count events](step:1). -/
def retentionFailureSet (n m : ℕ) : Set (RawTwoPool X Y) :=
  {z | z.1.count < n} ∪ {z | z.2.count < m}

/-- Given [the first requested prefix length](hyp:n) and [the second requested prefix
length](hyp:m), [the retention-success event is measurable](goal). -/
theorem measurableSet_retentionSuccessSet (n m : ℕ) :
    MeasurableSet (retentionSuccessSet (X := X) (Y := Y) n m) := by
  exact (measurableSet_le measurable_const
    (measurable_finiteSample_count.comp measurable_fst)).inter
      (measurableSet_le measurable_const
        (measurable_finiteSample_count.comp measurable_snd))

/-- Given [the first requested prefix length](hyp:n) and [the second requested prefix
length](hyp:m), [the retention-failure event is measurable](goal). -/
theorem measurableSet_retentionFailureSet (n m : ℕ) :
    MeasurableSet (retentionFailureSet (X := X) (Y := Y) n m) := by
  exact (measurableSet_lt
    (measurable_finiteSample_count.comp measurable_fst) measurable_const).union
      (measurableSet_lt
        (measurable_finiteSample_count.comp measurable_snd) measurable_const)

/-- Given [the first requested prefix length](hyp:n) and [the second requested prefix
length](hyp:m), [success is exactly the complement of retention failure](goal). -/
theorem retentionSuccessSet_eq_compl_failureSet (n m : ℕ) :
    retentionSuccessSet (X := X) (Y := Y) n m =
      (retentionFailureSet (X := X) (Y := Y) n m)ᶜ := by
  ext z
  simp [retentionSuccessSet, retentionFailureSet]

/-- Given [a fallback fixed array](hyp:fallback) and [a finite record](hyp:s), [the ordered
prefix](goal) retains its initial requested segment when available and otherwise returns the
fallback. [It is given by the count test](step:1). -/
def orderedPrefix (fallback : Fin n → X) (s : FiniteSample X) : Fin n → X :=
  if h : n ≤ s.count then fun i => s.points (Fin.castLE h i) else fallback

/-- Given [a fallback fixed array](hyp:fallback), [ordered prefix retention is
measurable](goal). -/
theorem measurable_orderedPrefix (fallback : Fin n → X) :
    Measurable (orderedPrefix fallback : FiniteSample X → (Fin n → X)) := by
  unfold orderedPrefix
  apply measurable_pi_lambda
  intro i t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro k
  change MeasurableSet ((fun x : Fin k → X =>
    (if h : n ≤ k then fun i => x (Fin.castLE h i) else fallback) i) ⁻¹' t)
  by_cases h : n ≤ k
  · simp only [dif_pos h]
    exact ht.preimage (measurable_pi_apply (Fin.castLE h i))
  · simp only [dif_neg h]
    exact measurable_const ht

/-- Given [a fallback first array](hyp:fallbackX) and [a fallback second array](hyp:fallbackY),
[the two-pool ordered-retention map](goal) applies ordered prefix retention in each coordinate.
[It is given by the pair of retained prefixes](step:1). -/
def twoPoolOrderedRetention
    (fallbackX : Fin n → X) (fallbackY : Fin m → Y) :
    RawTwoPool X Y → FixedPools (X := X) (Y := Y) n m :=
  fun z => (orderedPrefix fallbackX z.1, orderedPrefix fallbackY z.2)

/-- Given [a fallback first array](hyp:fallbackX) and [a fallback second array](hyp:fallbackY),
[the unequal two-pool ordered-retention map is measurable](goal). -/
theorem measurable_twoPoolOrderedRetention
    (fallbackX : Fin n → X) (fallbackY : Fin m → Y) :
    Measurable (twoPoolOrderedRetention fallbackX fallbackY) := by
  exact (measurable_orderedPrefix fallbackX).comp measurable_fst |>.prodMk
    ((measurable_orderedPrefix fallbackY).comp measurable_snd)

private lemma map_prefixCoordinates_pi
    (P : Measure X) [IsProbabilityMeasure P]
    {n k : ℕ} (h : n ≤ k) :
    Measure.map (fun x : Fin k → X => fun i : Fin n => x (Fin.castLE h i))
      (Measure.pi (fun _ : Fin k => P)) = Measure.pi (fun _ : Fin n => P) := by
  classical
  symm
  refine Measure.pi_eq (μ := fun _ : Fin n => P) (fun s hs => ?_)
  rw [Measure.map_apply (by fun_prop) (.univ_pi hs)]
  have hpre : (fun x : Fin k → X => fun i : Fin n => x (Fin.castLE h i)) ⁻¹'
      (Set.univ.pi s) =
      Set.univ.pi (fun j : Fin k =>
        if hj : j.val < n then s ⟨j.val, hj⟩ else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx j
      split
      · exact hx ⟨j.val, ‹j.val < n›⟩
      · trivial
    · intro hx i
      simpa using hx (Fin.castLE h i)
  rw [hpre, Measure.pi_pi]
  let t : Finset (Fin k) := Finset.univ.filter fun j => j.val < n
  have ht (j : t) : j.val.val < n := by
    simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using j.property
  let e : Fin n ≃ t :=
    { toFun := fun i => ⟨Fin.castLE h i, by simp [t, i.isLt]⟩
      invFun := fun j => ⟨j.val.val, ht j⟩
      left_inv := fun i => by rfl
      right_inv := fun j => by ext; rfl }
  calc
    (∏ j : Fin k, P (if hj : j.val < n then s ⟨j.val, hj⟩ else Set.univ)) =
        ∏ j : Fin k, if hj : j.val < n then P (s ⟨j.val, hj⟩) else 1 := by
          apply Fintype.prod_congr
          intro j
          split <;> simp
    _ = ∏ j : t, P (s ⟨j.val.val, ht j⟩) := by
      rw [Finset.prod_dite]
      simp only [Finset.prod_const_one, mul_one]
      apply Fintype.prod_congr
      intro j
      congr 2
    _ = ∏ i : Fin n, P (s i) := by
      symm
      apply Fintype.prod_equiv e
      intro i
      rfl

private lemma map_orderedPrefix_fixedSizeEmbed_pi
    (P : Measure X) [IsProbabilityMeasure P]
    (fallback : Fin n → X) {k : ℕ} (h : n ≤ k) :
    Measure.map (orderedPrefix fallback)
        (Measure.map (fixedSizeEmbed k) (Measure.pi (fun _ : Fin k => P))) =
      Measure.pi (fun _ : Fin n => P) := by
  rw [Measure.map_map (measurable_orderedPrefix fallback)
    (measurable_fixedSizeEmbed k)]
  have hfun : orderedPrefix fallback ∘ fixedSizeEmbed k =
      fun x : Fin k → X => fun i : Fin n => x (Fin.castLE h i) := by
    funext x
    simp [orderedPrefix, fixedSizeEmbed, h, FiniteSample.count, FiniteSample.points]
  rw [hfun, map_prefixCoordinates_pi P h]

/-- Given [a fallback first array](hyp:fallbackX) and [a fallback second array](hyp:fallbackY),
[the ordered-record retention kernel](goal) deterministically applies two-pool ordered
retention. [It is given by the Dirac kernel at that measurable map](step:1). -/
noncomputable def orderedRetentionKernel
    (fallbackX : Fin n → X) (fallbackY : Fin m → Y) :
    Kernel (RawTwoPool X Y) (FixedPools (X := X) (Y := Y) n m) :=
  Kernel.deterministic (twoPoolOrderedRetention fallbackX fallbackY)
    (measurable_twoPoolOrderedRetention fallbackX fallbackY)

/-- Given [a mark law](hyp:P), [a Poisson intensity](hyp:lambda), and [a fallback fixed
array](hyp:fallback), [the pushforward of the successful-count restriction has the
unnormalized iid prefix law](goal), with its scalar mass equal to the Poisson success
probability. -/
theorem map_orderedPrefix_restrict_count_ge
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0)
    (fallback : Fin n → X) :
    Measure.map (orderedPrefix fallback)
        ((finitePoissonSampleLaw P lambda).restrict
          (FiniteSample.count ⁻¹' Set.Ici n)) =
      (poissonMeasure lambda) (Set.Ici n) • Measure.pi (fun _ : Fin n => P) := by
  let μ := finitePoissonSampleLaw P lambda
  have hdecomp :
      μ.restrict (FiniteSample.count ⁻¹' Set.Ici n) =
        Measure.sum (fun k : (Set.Ici n : Set ℕ) =>
          μ.restrict (FiniteSample.count ⁻¹' ({k.1} : Set ℕ))) := by
    rw [← Set.biUnion_preimage_singleton]
    exact Measure.restrict_biUnion (Set.to_countable (Set.Ici n))
      (pairwiseDisjoint_fiber FiniteSample.count (Set.Ici n))
      (fun k => measurable_finiteSample_count (measurableSet_singleton k))
  rw [show finitePoissonSampleLaw P lambda = μ by rfl, hdecomp,
    Measure.map_sum ((measurable_orderedPrefix fallback).aemeasurable)]
  simp_rw [show ∀ k : (Set.Ici n : Set ℕ),
      Measure.map (orderedPrefix fallback)
          (μ.restrict (FiniteSample.count ⁻¹' ({k.1} : Set ℕ))) =
        (poissonMeasure lambda) ({k.1} : Set ℕ) •
          Measure.pi (fun _ : Fin n => P) by
    intro k
    rw [show μ = finitePoissonSampleLaw P lambda by rfl,
      finitePoissonSampleLaw_restrict_count_eq, Measure.map_smul,
      map_orderedPrefix_fixedSizeEmbed_pi P fallback k.2]]
  ext A hA
  simp only [Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_mul_right]
  congr 1
  simpa using (tsum_measure_preimage_singleton
    (μ := poissonMeasure lambda) (s := Set.Ici n) (f := id)
    (Set.to_countable (Set.Ici n))
    (fun k _ => measurableSet_singleton k))

/-- Given [the first mark law](hyp:P), [the second mark law](hyp:Q), [the first Poisson
intensity](hyp:lambdaX), [the second Poisson intensity](hyp:lambdaY), [the first requested
length](hyp:n), [the second requested length](hyp:m), [a fallback first array](hyp:fallbackX),
and [a fallback second array](hyp:fallbackY), [ordered retention on joint success has the
unnormalized exact product law](goal), including the complete auxiliary iid law. -/
theorem map_twoPoolOrderedRetention_restrict_success
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) (n m : ℕ)
    (fallbackX : Fin n → X) (fallbackY : Fin m → Y) :
    Measure.map (twoPoolOrderedRetention fallbackX fallbackY)
        (((finitePoissonSampleLaw P lambdaX).prod
          (finitePoissonSampleLaw Q lambdaY)).restrict
            (retentionSuccessSet (X := X) (Y := Y) n m)) =
      ((poissonMeasure lambdaX) (Set.Ici n) *
          (poissonMeasure lambdaY) (Set.Ici m)) •
        fixedPoolsLaw P Q n m := by
  let μX : Measure (FiniteSample X) := finitePoissonSampleLaw P lambdaX
  let μY : Measure (FiniteSample Y) := finitePoissonSampleLaw Q lambdaY
  let sX : Set (FiniteSample X) := FiniteSample.count ⁻¹' Set.Ici n
  let sY : Set (FiniteSample Y) := FiniteSample.count ⁻¹' Set.Ici m
  have hsuccess : retentionSuccessSet (X := X) (Y := Y) n m = sX ×ˢ sY := by
    ext z
    simp [retentionSuccessSet, sX, sY]
  rw [hsuccess, ← Measure.prod_restrict]
  change Measure.map (Prod.map (orderedPrefix fallbackX) (orderedPrefix fallbackY))
      ((μX.restrict sX).prod (μY.restrict sY)) = _
  rw [← Measure.map_prod_map _ _ (measurable_orderedPrefix fallbackX)
      (measurable_orderedPrefix fallbackY),
    show Measure.map (orderedPrefix fallbackX) (μX.restrict sX) =
        (poissonMeasure lambdaX) (Set.Ici n) •
          Measure.pi (fun _ : Fin n => P) by
      exact map_orderedPrefix_restrict_count_ge P lambdaX fallbackX,
    show Measure.map (orderedPrefix fallbackY) (μY.restrict sY) =
        (poissonMeasure lambdaY) (Set.Ici m) •
          Measure.pi (fun _ : Fin m => Q) by
      exact map_orderedPrefix_restrict_count_ge Q lambdaY fallbackY,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rfl

/-- Given [the first mark law](hyp:P), [the second mark law](hyp:Q), [the first Poisson
intensity](hyp:lambdaX), [the second Poisson intensity](hyp:lambdaY), [the first requested
length](hyp:n), [the second requested length](hyp:m), [a fallback first array](hyp:fallbackX),
[a fallback second array](hyp:fallbackY), and [positive joint-success mass](hyp:hpos),
[normalizing retained successful records gives the exact fixed product law](goal), preserving
the full auxiliary distribution. -/
theorem normalized_map_twoPoolOrderedRetention_restrict_success
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) (n m : ℕ)
    (fallbackX : Fin n → X) (fallbackY : Fin m → Y)
    (hpos : (poissonMeasure lambdaX) (Set.Ici n) *
        (poissonMeasure lambdaY) (Set.Ici m) ≠ 0) :
    (((poissonMeasure lambdaX) (Set.Ici n) *
        (poissonMeasure lambdaY) (Set.Ici m))⁻¹) •
        Measure.map (twoPoolOrderedRetention fallbackX fallbackY)
          (((finitePoissonSampleLaw P lambdaX).prod
            (finitePoissonSampleLaw Q lambdaY)).restrict
              (retentionSuccessSet (X := X) (Y := Y) n m)) =
      fixedPoolsLaw P Q n m := by
  rw [map_twoPoolOrderedRetention_restrict_success]
  rw [smul_smul, ENNReal.inv_mul_cancel hpos
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)), one_smul]

end Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer
