/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.GaussianCDF
import Causalean.Experimentation.DesignBased.MeasureBridge
import Causalean.Experimentation.DesignBased.ProductMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Process.Filtration

/-!
# Finite-design Heyde--Brown bridge

This module turns a finite product randomization design into the product probability space and
reveal filtration needed by a supplied Heyde--Brown fourth-moment inequality.  It identifies the
finite and measure-theoretic conditional expectations, predictable variations, moments, and CDF
expressions, then specializes the supplied inequality without postulating or proving it.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Causalean.Experimentation.DesignBased

variable {N : ℕ}
variable {alpha : Fin N → Type*} [∀ i, Fintype (alpha i)]
variable [∀ i, MeasurableSpace (alpha i)] [∀ i, MeasurableSingletonClass (alpha i)]

/-- A [reveal permutation](hyp:pi) and [coordinate](hyp:i) determine [that coordinate's reveal
rank](goal), namely [the step at which the permutation reveals it](step:1). -/
def prefixRank (pi : Equiv.Perm (Fin N)) (i : Fin N) : Fin N := pi.symm i

/-- A [reveal permutation](hyp:pi), [prefix length](hyp:k), and [two assignments](hyp:w,w')
determine [agreement through the reveal prefix](goal): the assignments have the same values on
every coordinate already revealed [by this equality condition](step:1). -/
def AgreeOnPrefix (pi : Equiv.Perm (Fin N)) (k : Fin (N + 1))
    (w w' : ∀ i, alpha i) : Prop :=
  ∀ i, (prefixRank pi i).val < k.val → w' i = w i

/-- A [reveal permutation](hyp:pi) and [prefix length](hyp:k) determine [the σ-algebra generated
by the revealed coordinates](goal), which records exactly the information available after that
many reveal steps [by generating from those coordinate evaluations](step:1). -/
def revealMeasurableSpace (pi : Equiv.Perm (Fin N)) (k : Fin (N + 1)) :
    MeasurableSpace (∀ i, alpha i) :=
  ⨆ i, if (prefixRank pi i).val < k.val then
    MeasurableSpace.comap (fun w : ∀ j, alpha j => w i) inferInstance
  else ⊥

/-- A [reveal permutation](hyp:pi) determines [the reveal filtration](goal), whose time-k
σ-algebra is [the prefix σ-algebra](step:1), is [monotone in reveal time](step:2), and [lies
inside the full product σ-algebra](step:3). -/
noncomputable def revealFiltration (pi : Equiv.Perm (Fin N)) :
    Filtration (Fin (N + 1)) (inferInstance : MeasurableSpace (∀ i, alpha i)) where
  seq := revealMeasurableSpace pi
  mono' := by
    intro k l hkl
    unfold revealMeasurableSpace
    refine iSup_mono fun i ↦ ?_
    by_cases hik : (prefixRank pi i).val < k.val
    · have hil : (prefixRank pi i).val < l.val := lt_of_lt_of_le hik hkl
      simp [hik, hil]
    · simp [hik]
  le' := by
    intro k
    unfold revealMeasurableSpace
    refine iSup_le fun i ↦ ?_
    split_ifs
    · simpa only [MeasurableSpace.pi] using
        (le_iSup (fun j : Fin N ↦
          MeasurableSpace.comap (fun w : ∀ q, alpha q => w j) inferInstance) i)
    · exact bot_le

/-- A [family of coordinate designs](hyp:D), [reveal permutation](hyp:pi), [prefix length](hyp:k),
and [statistic](hyp:f) determine [the explicit prefix conditional expectation](goal), obtained by
averaging over unrevealed coordinates while holding revealed coordinates fixed
[by the stated finite sum](step:1). -/
noncomputable def prefixCondExp (D : ∀ i, FiniteDesign (alpha i))
    (pi : Equiv.Perm (Fin N)) (k : Fin (N + 1))
    (f : (∀ i, alpha i) → ℝ) : (∀ i, alpha i) → ℝ :=
  by
    classical
    exact fun w ↦ ∑ w' : ∀ i, alpha i,
      if AgreeOnPrefix pi k w w' then
        (∏ i, if k.val ≤ (prefixRank pi i).val then (D i).p (w' i) else 1) * f w'
      else 0

/-- A [family of coordinate designs](hyp:D), [reveal permutation](hyp:pi), and [increment
family](hyp:X) satisfy [the prefix martingale-difference condition](goal) when [each increment
has zero conditional mean immediately before its reveal](step:1) and [is visible after that
reveal](step:2). -/
def IsPrefixMartingaleDifference (D : ∀ i, FiniteDesign (alpha i))
    (pi : Equiv.Perm (Fin N)) (X : Fin N → (∀ i, alpha i) → ℝ) : Prop :=
  (∀ s, prefixCondExp D pi (Fin.castSucc s) (X s) = 0) ∧
    (∀ s, prefixCondExp D pi (Fin.succ s) (X s) = X s)

/-- A [family of coordinate designs](hyp:D), [reveal permutation](hyp:pi), and [increment
family](hyp:X) determine [the finite-design predictable variation](goal), the sum of conditional
second moments just before each reveal step [by the displayed finite sum](step:1). -/
noncomputable def finitePredictableVariation (D : ∀ i, FiniteDesign (alpha i))
    (pi : Equiv.Perm (Fin N)) (X : Fin N → (∀ i, alpha i) → ℝ) :
    (∀ i, alpha i) → ℝ :=
  fun w ↦ ∑ s, prefixCondExp D pi (Fin.castSucc s) (fun z ↦ (X s z) ^ 2) w

/-- A [probability measure](hyp:mu), [filtration](hyp:F), and [increment family](hyp:X) determine
[the measure-theoretic predictable variation](goal), the sum of conditional second moments at
the preceding filtration times [by the displayed finite sum](step:1). -/
noncomputable def measurePredictableVariation {Omega : Type*} [m : MeasurableSpace Omega]
    (mu : Measure Omega) (F : Filtration (Fin (N + 1)) m)
    (X : Fin N → Omega → ℝ) : Omega → ℝ :=
  fun w ↦ ∑ s, mu[(fun z ↦ (X s z) ^ 2) | F (Fin.castSucc s)] w

/-- A [family of coordinate designs](hyp:D), [reveal permutation](hyp:pi), and [increment
family](hyp:X) determine [the finite fourth-moment error](goal): the sum of fourth moments plus
the second moment of predictable variation minus one [by the displayed sum of two terms](step:1). -/
noncomputable def finiteFourthMomentError (D : ∀ i, FiniteDesign (alpha i))
    (pi : Equiv.Perm (Fin N)) (X : Fin N → (∀ i, alpha i) → ℝ) : ℝ :=
  (∑ s, (prodDesign D).E (fun w ↦ |X s w| ^ 4)) +
    (prodDesign D).E (fun w ↦ |finitePredictableVariation D pi X w - 1| ^ 2)

/-- A [probability measure](hyp:mu), [filtration](hyp:F), and [increment family](hyp:X) determine
[the measure-theoretic fourth-moment error](goal): the sum of fourth moments plus the second
moment of predictable variation minus one [by the displayed sum of two terms](step:1). -/
noncomputable def measureFourthMomentError {Omega : Type*} [m : MeasurableSpace Omega]
    (mu : Measure Omega) (F : Filtration (Fin (N + 1)) m)
    (X : Fin N → Omega → ℝ) : ℝ :=
  (∑ s, ∫ w, |X s w| ^ 4 ∂mu) +
    ∫ w, |measurePredictableVariation mu F X w - 1| ^ 2 ∂mu

/-- A [finite randomization design](hyp:D) and [real statistic](hyp:Y) determine [its
finite-design Kolmogorov expression](goal), the largest absolute gap between its CDF and the
standard-normal CDF [by taking the supremum over thresholds](step:1). -/
noncomputable def finiteKolmogorovExpr {Omega : Type*} [Fintype Omega]
    (D : FiniteDesign Omega) (Y : Omega → ℝ) : ℝ :=
  sSup (Set.range fun t : ℝ ↦ |D.Pr (fun w ↦ Y w ≤ t) - stdNormalCdf t|)

/-- A [measure](hyp:mu) and [real random variable](hyp:Y) determine [its measure-theoretic
Kolmogorov expression](goal), the largest absolute gap between its CDF and the standard-normal
CDF [by taking the supremum over thresholds](step:1). -/
noncomputable def measureKolmogorovExpr {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (Y : Omega → ℝ) : ℝ :=
  sSup (Set.range fun t : ℝ ↦ |mu.real {w | Y w ≤ t} - stdNormalCdf t|)

/-- A [probability measure](hyp:mu), [filtration](hyp:F), [increment family](hyp:X), and
[constant](hyp:C) define [the supplied Heyde--Brown fourth-moment premise](goal): adapted,
centered, normalized increments with finite fourth moments obey the stated one-fifth-power
Kolmogorov bound [by the four displayed assumptions and conclusion](step:1). -/
def HeydeBrownFourthMomentPremise {Omega : Type*} [m : MeasurableSpace Omega]
    (mu : Measure Omega) (F : Filtration (Fin (N + 1)) m)
    (X : Fin N → Omega → ℝ) (C : ℝ) : Prop :=
  (∀ s, AEStronglyMeasurable[F (Fin.succ s)] (X s) mu) →
  (∀ s, mu[X s | F (Fin.castSucc s)] =ᵐ[mu] 0) →
  (∑ s, ∫ w, (X s w) ^ 2 ∂mu) = 1 →
  (∀ s, MemLp (X s) 4 mu) →
  measureKolmogorovExpr mu (fun w ↦ ∑ s, X s w) ≤
    C * Real.rpow (measureFourthMomentError mu F X) (1 / 5 : ℝ)

set_option maxHeartbeats 1000000 in
-- The finite dependent-product normalization below needs more elaboration than the default budget.
/-- A [family of coordinate designs](hyp:D), [reveal permutation](hyp:pi), [prefix length](hyp:k),
and [statistic](hyp:f) give [an almost-everywhere identification of the explicit prefix average
with conditional expectation](goal) under the product-design measure and its reveal σ-algebra. -/
theorem prefixCondExp_ae_eq_condExp (D : ∀ i, FiniteDesign (alpha i))
    (pi : Equiv.Perm (Fin N)) (k : Fin (N + 1))
    (f : (∀ i, alpha i) → ℝ) :
    prefixCondExp D pi k f =ᵐ[(prodDesign D).toMeasure]
      (prodDesign D).toMeasure[f | (revealFiltration pi) k] := by
  classical
  let m0 : MeasurableSpace (∀ i, alpha i) := inferInstance
  let m : MeasurableSpace (∀ i, alpha i) := (revealFiltration pi) k
  let mInv : MeasurableSpace (∀ i, alpha i) := by
    exact {
      MeasurableSet' := fun s ↦
        ∀ w w', AgreeOnPrefix pi k w w' → (w ∈ s ↔ w' ∈ s)
      measurableSet_empty := by simp
      measurableSet_compl := by
        intro s hs w w' hww'
        simpa only [Set.mem_compl_iff] using not_congr (hs w w' hww')
      measurableSet_iUnion := by
        intro s hs w w' hww'
        constructor <;> intro hw
        · simp only [Set.mem_iUnion] at hw ⊢
          obtain ⟨i, hi⟩ := hw
          exact ⟨i, (hs i w w' hww').1 hi⟩
        · simp only [Set.mem_iUnion] at hw ⊢
          obtain ⟨i, hi⟩ := hw
          exact ⟨i, (hs i w w' hww').2 hi⟩ }
  have hm : m ≤ m0 := by
    simpa only [m, m0] using (revealFiltration pi).le k
  have hmInv : m ≤ mInv := by
    unfold m revealFiltration revealMeasurableSpace
    refine iSup_le fun i ↦ ?_
    by_cases hi : (prefixRank pi i).val < k.val
    · simp only [hi, if_true]
      intro s hs
      rw [MeasurableSpace.measurableSet_comap] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      change ∀ w w', AgreeOnPrefix pi k w w' →
        (w i ∈ t ↔ w' i ∈ t)
      intro w w' hww'
      rw [hww' i hi]
    · simp [hi]
  have hmem_of_agree {s : Set (∀ i, alpha i)} (hs : MeasurableSet[m] s)
      {w w' : ∀ i, alpha i} (hww' : AgreeOnPrefix pi k w w') :
      w ∈ s ↔ w' ∈ s := by
    exact hmInv s hs w w' hww'
  have hcell (w' : ∀ i, alpha i) :
      MeasurableSet[m] {w | AgreeOnPrefix pi k w w'} := by
    have hset : {w | AgreeOnPrefix pi k w w'} =
        ⋂ i, if (prefixRank pi i).val < k.val then {w | w i = w' i} else Set.univ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h i
        by_cases hi : (prefixRank pi i).val < k.val
        · simp [hi, (h i hi).symm]
        · simp [hi]
      · intro h i hi
        have h' : w i = w' i := by simpa [hi] using h i
        exact h'.symm
    rw [hset]
    refine MeasurableSet.iInter fun i ↦ ?_
    by_cases hi : (prefixRank pi i).val < k.val
    · simp only [hi, if_true]
      have hbase : MeasurableSet[
          MeasurableSpace.comap (fun w : ∀ q, alpha q => w i) (inferInstance)]
          {w | w i = w' i} :=
        (measurableSet_singleton (w' i)).preimage
          (comap_measurable (fun w : ∀ q, alpha q => w i))
      have hcomponent : MeasurableSet[
          if (prefixRank pi i).val < k.val then
            MeasurableSpace.comap (fun w : ∀ q, alpha q => w i) inferInstance else ⊥]
          {w | w i = w' i} := by
        rw [if_pos hi]
        exact hbase
      exact (le_iSup (fun j : Fin N ↦
        if (prefixRank pi j).val < k.val then
          MeasurableSpace.comap (fun w : ∀ q, alpha q => w j) inferInstance else ⊥) i)
        _ hcomponent
    · simp [hi]
  have hmeas : Measurable[m] (prefixCondExp D pi k f) := by
    unfold prefixCondExp
    exact Finset.measurable_sum Finset.univ fun w' _ ↦
      Measurable.ite (hcell w') measurable_const measurable_const
  let _ : MeasurableSpace (∀ i, alpha i) := m0
  have hf : Integrable f (prodDesign D).toMeasure := Integrable.of_finite
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf ?_ ?_
    hmeas.stronglyMeasurable.aestronglyMeasurable
  · intro s _ _
    exact (show Integrable (prefixCondExp D pi k f) (prodDesign D).toMeasure from
      Integrable.of_finite).integrableOn
  · intro s hs _
    have hs0 : MeasurableSet[m0] s := hm s hs
    rw [← integral_indicator hs0, ← integral_indicator hs0,
      FiniteDesign.integral_toMeasure, FiniteDesign.integral_toMeasure]
    have hmass (w' : ∀ i, alpha i) :
        (∑ z : ∀ i, alpha i,
          if AgreeOnPrefix pi k z w' then ∏ i, (D i).p (z i) else 0) =
          ∏ i, if (prefixRank pi i).val < k.val then (D i).p (w' i) else 1 := by
      have hterm (z : ∀ i, alpha i) :
          (if AgreeOnPrefix pi k z w' then ∏ i, (D i).p (z i) else 0) =
            ∏ i, if (prefixRank pi i).val < k.val then
              if z i = w' i then (D i).p (z i) else 0
            else (D i).p (z i) := by
        by_cases hz : AgreeOnPrefix pi k z w'
        · rw [if_pos hz]
          apply Finset.prod_congr rfl
          intro i _
          by_cases hi : (prefixRank pi i).val < k.val
          · simp [hi, (hz i hi).symm]
          · simp [hi]
        · rw [if_neg hz]
          simp only [AgreeOnPrefix] at hz
          push Not at hz
          obtain ⟨i, hi, hne⟩ := hz
          exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hne.symm])).symm
      calc
        (∑ z : ∀ i, alpha i,
            if AgreeOnPrefix pi k z w' then ∏ i, (D i).p (z i) else 0) =
            ∑ z : ∀ i, alpha i, ∏ i,
              if (prefixRank pi i).val < k.val then
                if z i = w' i then (D i).p (z i) else 0
              else (D i).p (z i) := Finset.sum_congr rfl fun z _ ↦ hterm z
        _ = ∏ i, ∑ a : alpha i,
              if (prefixRank pi i).val < k.val then
                if a = w' i then (D i).p a else 0
              else (D i).p a :=
          (Fintype.prod_sum (fun i (a : alpha i) ↦
            if (prefixRank pi i).val < k.val then
              if a = w' i then (D i).p a else 0
            else (D i).p a)).symm
        _ = ∏ i, if (prefixRank pi i).val < k.val then
              (D i).p (w' i) else 1 := by
          apply Finset.prod_congr rfl
          intro i _
          by_cases hi : (prefixRank pi i).val < k.val
          · simp [hi]
          · simp [hi, (D i).p_sum]
    have hsplit (w' : ∀ i, alpha i) :
        (∏ i, if k.val ≤ (prefixRank pi i).val then (D i).p (w' i) else 1) *
          (∏ i, if (prefixRank pi i).val < k.val then (D i).p (w' i) else 1) =
          ∏ i, (D i).p (w' i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : (prefixRank pi i).val < k.val
      · have hnle : ¬k.val ≤ (prefixRank pi i).val := Nat.not_le_of_gt hi
        simp [hi, hnle]
      · have hle : k.val ≤ (prefixRank pi i).val := Nat.le_of_not_gt hi
        simp [hi, hle]
    have hswap (z : ∀ i, alpha i) :
        (∏ i, (D i).p (z i)) *
            (if z ∈ s then
              ∑ w' : ∀ i, alpha i,
                if AgreeOnPrefix pi k z w' then
                  (∏ i, if k.val ≤ (prefixRank pi i).val then
                    (D i).p (w' i) else 1) * f w'
                else 0
            else 0) =
          ∑ w' : ∀ i, alpha i,
            if w' ∈ s then
              (∏ i, if k.val ≤ (prefixRank pi i).val then
                (D i).p (w' i) else 1) * f w' *
                  (if AgreeOnPrefix pi k z w' then
                    ∏ i, (D i).p (z i) else 0)
            else 0 := by
      by_cases hz : z ∈ s
      · rw [if_pos hz, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w' _
        by_cases ha : AgreeOnPrefix pi k z w'
        · have hw' : w' ∈ s := (hmem_of_agree hs ha).1 hz
          simp only [ha, if_true, hw']
          ring
        · simp [ha]
      · rw [if_neg hz]
        simp only [mul_zero]
        symm
        apply Finset.sum_eq_zero
        intro w' _
        by_cases ha : AgreeOnPrefix pi k z w'
        · have hw' : w' ∉ s := fun hw' ↦ hz ((hmem_of_agree hs ha).2 hw')
          simp [hw']
        · simp [ha]
    simp only [FiniteDesign.E, prodDesign_p, Set.indicator, prefixCondExp]
    calc
      (∑ z,
          (∏ i, (D i).p (z i)) *
            if z ∈ s then
              ∑ w', if AgreeOnPrefix pi k z w' then
                (∏ i, if k.val ≤ (prefixRank pi i).val then
                  (D i).p (w' i) else 1) * f w'
              else 0
            else 0) =
          ∑ z, ∑ w',
            if w' ∈ s then
              (∏ i, if k.val ≤ (prefixRank pi i).val then
                (D i).p (w' i) else 1) * f w' *
                  (if AgreeOnPrefix pi k z w' then
                    ∏ i, (D i).p (z i) else 0)
            else 0 := Finset.sum_congr rfl fun z _ ↦ hswap z
      _ = ∑ w', ∑ z,
            if w' ∈ s then
              (∏ i, if k.val ≤ (prefixRank pi i).val then
                (D i).p (w' i) else 1) * f w' *
                  (if AgreeOnPrefix pi k z w' then
                    ∏ i, (D i).p (z i) else 0)
            else 0 := Finset.sum_comm
      _ = ∑ w', (∏ i, (D i).p (w' i)) * if w' ∈ s then f w' else 0 := by
        apply Finset.sum_congr rfl
        intro w' _
        by_cases hw' : w' ∈ s
        · simp only [hw', if_true]
          rw [← Finset.mul_sum, hmass]
          rw [← hsplit w']
          ring
        · simp [hw']

/-- A [family of coordinate designs](hyp:D), [reveal permutation](hyp:pi), [prefix length](hyp:k),
[statistic](hyp:f), and [pointwise equality to its prefix conditional expectation](hyp:hf) imply
[that the statistic is almost-everywhere strongly measurable for the reveal σ-algebra](goal). -/
theorem aestronglyMeasurable_reveal_of_prefixCondExp_eq
    (D : ∀ i, FiniteDesign (alpha i)) (pi : Equiv.Perm (Fin N)) (k : Fin (N + 1))
    (f : (∀ i, alpha i) → ℝ) (hf : prefixCondExp D pi k f = f) :
    AEStronglyMeasurable[(revealFiltration pi) k] f (prodDesign D).toMeasure := by
  rw [← hf]
  exact stronglyMeasurable_condExp.aestronglyMeasurable.congr
    (prefixCondExp_ae_eq_condExp D pi k f).symm

/-- A [family of coordinate designs](hyp:D), [reveal permutation](hyp:pi), [prefix length](hyp:k),
[statistic](hyp:f), and [zero explicit prefix conditional expectation](hyp:hf) imply [the
measure-theoretic conditional expectation is almost everywhere zero](goal). -/
theorem condExp_ae_eq_zero_of_prefixCondExp_eq_zero
    (D : ∀ i, FiniteDesign (alpha i)) (pi : Equiv.Perm (Fin N)) (k : Fin (N + 1))
    (f : (∀ i, alpha i) → ℝ) (hf : prefixCondExp D pi k f = 0) :
    (prodDesign D).toMeasure[f | (revealFiltration pi) k] =ᵐ[(prodDesign D).toMeasure] 0 := by
  simpa only [hf] using (prefixCondExp_ae_eq_condExp D pi k f).symm

/-- A [family of coordinate designs](hyp:D), [reveal permutation](hyp:pi), and [increment
family](hyp:X) give [an almost-everywhere equality between finite-design and measure-theoretic
predictable variations](goal) under the product-design measure. -/
theorem finitePredictableVariation_ae_eq_measurePredictableVariation
    (D : ∀ i, FiniteDesign (alpha i)) (pi : Equiv.Perm (Fin N))
    (X : Fin N → (∀ i, alpha i) → ℝ) :
    finitePredictableVariation D pi X =ᵐ[(prodDesign D).toMeasure]
      measurePredictableVariation (prodDesign D).toMeasure (revealFiltration pi) X := by
  unfold finitePredictableVariation measurePredictableVariation
  filter_upwards [ae_all_iff.2 (fun s ↦
    prefixCondExp_ae_eq_condExp D pi (Fin.castSucc s) (fun z ↦ (X s z) ^ 2))]
    with w hw
  exact Finset.sum_congr rfl fun s _ ↦ hw s

/-- A [family of coordinate designs](hyp:D) and [real statistic](hyp:Y) give [an exact
identification between the finite-design and measure-theoretic Kolmogorov expressions](goal)
under the induced product-design measure. -/
theorem finiteKolmogorovExpr_eq_measureKolmogorovExpr
    (D : ∀ i, FiniteDesign (alpha i)) (Y : (∀ i, alpha i) → ℝ) :
    finiteKolmogorovExpr (prodDesign D) Y =
      measureKolmogorovExpr (prodDesign D).toMeasure Y := by
  classical
  unfold finiteKolmogorovExpr measureKolmogorovExpr
  apply congrArg sSup
  congr 1
  funext t
  rw [FiniteDesign.Pr_eq_measureReal]

/-- A [family of coordinate designs](hyp:D), [reveal permutation](hyp:pi), and [increment
family](hyp:X) give [an exact identification between finite-design and measure-theoretic
fourth-moment errors](goal), including the predictable-variation term. -/
theorem finiteFourthMomentError_eq_measureFourthMomentError
    (D : ∀ i, FiniteDesign (alpha i)) (pi : Equiv.Perm (Fin N))
    (X : Fin N → (∀ i, alpha i) → ℝ) :
    finiteFourthMomentError D pi X =
      measureFourthMomentError (prodDesign D).toMeasure (revealFiltration pi) X := by
  unfold finiteFourthMomentError measureFourthMomentError
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    exact ((prodDesign D).integral_toMeasure (fun w ↦ |X s w| ^ 4)).symm
  · rw [← (prodDesign D).integral_toMeasure
      (fun w ↦ |finitePredictableVariation D pi X w - 1| ^ 2)]
    apply integral_congr_ae
    filter_upwards [finitePredictableVariation_ae_eq_measurePredictableVariation D pi X]
      with w hw
    rw [hw]

/-- Given [coordinate designs](hyp:D), a [reveal permutation](hyp:pi), an [increment family](hyp:X),
and a [bound constant](hyp:C), if [the increments are prefix martingale differences](hyp:hX),
[their total second moment is one](hyp:hsecond), and
[the supplied Heyde--Brown premise holds](hyp:hHeydeBrown),
then [their sum satisfies the finite-design one-fifth-power Kolmogorov bound](goal). -/
theorem finiteDesign_heydeBrown_fourthMoment
    (D : ∀ i, FiniteDesign (alpha i)) (pi : Equiv.Perm (Fin N))
    (X : Fin N → (∀ i, alpha i) → ℝ) (C : ℝ)
    (hX : IsPrefixMartingaleDifference D pi X)
    (hsecond : ∑ s, (prodDesign D).E (fun w ↦ (X s w) ^ 2) = 1)
    (hHeydeBrown : HeydeBrownFourthMomentPremise
      (prodDesign D).toMeasure (revealFiltration pi) X C) :
    finiteKolmogorovExpr (prodDesign D) (fun w ↦ ∑ s, X s w) ≤
      C * Real.rpow (finiteFourthMomentError D pi X) (1 / 5 : ℝ) := by
  rw [finiteKolmogorovExpr_eq_measureKolmogorovExpr,
    finiteFourthMomentError_eq_measureFourthMomentError]
  exact hHeydeBrown
    (fun s ↦ aestronglyMeasurable_reveal_of_prefixCondExp_eq
      D pi (Fin.succ s) (X s) (hX.2 s))
    (fun s ↦ condExp_ae_eq_zero_of_prefixCondExp_eq_zero
      D pi (Fin.castSucc s) (X s) (hX.1 s))
    (by simpa only [← (prodDesign D).E_eq_integral] using hsecond)
    (fun s ↦ (prodDesign D).memLp_toMeasure (X s) 4)

end Causalean.Experimentation.DesignBased
