module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridThreePoolPrefix

/-! Readback of the generic three finite prefixes as the paper's block counts. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory Causalean.Stat
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

private lemma histogram_prefix_eq_filter
    {X : Type*} [MeasurableSpace X] [DecidableEq X]
    {N r : Nat} (z : Fin N → X) (hr : r ≤ N) (v : X) :
    finiteSampleHistogram (prefixOfLE z r hr).points v =
      (Finset.univ.filter fun i : Fin N ↦ i.1 < r ∧ z i = v).card := by
  classical
  unfold finiteSampleHistogram prefixOfLE
  let e : {i : Fin r // z ⟨i.1, lt_of_lt_of_le i.2 hr⟩ = v} ≃
      {i : Fin N // i.1 < r ∧ z i = v} :=
    { toFun := fun i ↦ ⟨⟨i.1.1, lt_of_lt_of_le i.1.2 hr⟩, i.1.2, i.2⟩
      invFun := fun i ↦ ⟨⟨i.1.1, i.2.1⟩, i.2.2⟩
      left_inv := by intro i; apply Subtype.ext; rfl
      right_inv := by intro i; apply Subtype.ext; rfl }
  change Fintype.card {i : Fin r // z ⟨i.1, lt_of_lt_of_le i.2 hr⟩ = v} = _
  rw [Fintype.card_congr e]
  exact Fintype.card_subtype _

private lemma card_prefix_offset_eq_filter {X : Type*} [DecidableEq X]
    {N L r offset : Nat} (z : Fin N → X) (hbound : offset + L ≤ N)
    (hr : r ≤ L) (v : X) :
    (Finset.univ.filter fun i : Fin L ↦
        i.1 < r ∧ z ⟨offset + i.1, lt_of_lt_of_le (by omega) hbound⟩ = v).card =
      (Finset.univ.filter fun i : Fin N ↦
        offset ≤ i.1 ∧ i.1 < offset + r ∧ z i = v).card := by
  classical
  let e : {i : Fin L // i.1 < r ∧
        z ⟨offset + i.1, lt_of_lt_of_le (by omega) hbound⟩ = v} ≃
      {i : Fin N // offset ≤ i.1 ∧ i.1 < offset + r ∧ z i = v} :=
    { toFun := fun i ↦
        ⟨⟨offset + i.1.1, lt_of_lt_of_le (by omega) hbound⟩,
          Nat.le_add_right _ _, Nat.add_lt_add_left i.2.1 _, i.2.2⟩
      invFun := fun i ↦
        ⟨⟨i.1.1 - offset, by
            exact lt_of_lt_of_le
              ((Nat.sub_lt_iff_lt_add' i.2.1).2 i.2.2.1) hr⟩, by
          constructor
          · exact (Nat.sub_lt_iff_lt_add' i.2.1).2 i.2.2.1
          · have hi : offset + (i.1.1 - offset) = i.1.1 :=
              Nat.add_sub_of_le i.2.1
            simpa [hi] using i.2.2.2⟩
      left_inv := by intro i; apply Subtype.ext; apply Fin.ext; simp
      right_inv := by intro i; apply Subtype.ext; apply Fin.ext; simp; omega }
  rw [← Fintype.card_subtype (fun i : Fin L ↦ i.1 < r ∧
      z ⟨offset + i.1, lt_of_lt_of_le (by omega) hbound⟩ = v),
    ← Fintype.card_subtype (fun i : Fin N ↦
      offset ≤ i.1 ∧ i.1 < offset + r ∧ z i = v),
    Fintype.card_congr e]

private lemma histogram_prefix_append
    {X : Type*} [MeasurableSpace X] [DecidableEq X] {A B r : Nat}
    (z₁ : Fin A → X) (z₂ : Fin B → X) (hr : r ≤ A + B) (v : X) :
    finiteSampleHistogram (prefixOfLE (Fin.append z₁ z₂) r hr).points v =
      finiteSampleHistogram
          (prefixOfLE z₁ (min r A) (Nat.min_le_right _ _)).points v +
        finiteSampleHistogram (prefixOfLE z₂ (r - A) (by omega)).points v := by
  classical
  unfold finiteSampleHistogram prefixOfLE
  let e : {i : Fin r // Fin.append z₁ z₂
        ⟨i.1, lt_of_lt_of_le i.2 hr⟩ = v} ≃
      ({i : Fin (min r A) // z₁ ⟨i.1,
          lt_of_lt_of_le i.2 (Nat.min_le_right _ _)⟩ = v} ⊕
       {i : Fin (r - A) // z₂ ⟨i.1, lt_of_lt_of_le i.2 (by omega)⟩ = v}) :=
    { toFun := fun i ↦ if hi : i.1.1 < A then
          Sum.inl ⟨⟨i.1.1, lt_min i.1.2 hi⟩, by
            have hip := i.2
            rw [show ⟨i.1.1, lt_of_lt_of_le i.1.2 hr⟩ =
                Fin.castAdd B ⟨i.1.1, hi⟩ by apply Fin.ext; rfl,
              Fin.append_left] at hip
            exact hip⟩
        else Sum.inr ⟨⟨i.1.1 - A, by omega⟩, by
          have hip := i.2
          rw [show ⟨i.1.1, lt_of_lt_of_le i.1.2 hr⟩ =
              Fin.natAdd A ⟨i.1.1 - A, by omega⟩ by apply Fin.ext; simp; omega,
            Fin.append_right] at hip
          exact hip⟩
      invFun := fun i ↦ match i with
        | Sum.inl j => ⟨⟨j.1.1, by omega⟩, by
            rw [show ⟨j.1.1, lt_of_lt_of_le (by omega) hr⟩ =
                Fin.castAdd B ⟨j.1.1,
                  lt_of_lt_of_le j.1.2 (Nat.min_le_right _ _)⟩ by apply Fin.ext; rfl,
              Fin.append_left]
            exact j.2⟩
        | Sum.inr j => ⟨⟨A + j.1.1, by omega⟩, by
            rw [show ⟨A + j.1.1, lt_of_lt_of_le (by omega) hr⟩ =
                Fin.natAdd A ⟨j.1.1, lt_of_lt_of_le j.1.2 (by omega)⟩ by
                  apply Fin.ext; simp, Fin.append_right]
            exact j.2⟩
      left_inv := by
        intro i
        dsimp
        split_ifs with hi
        · apply Subtype.ext; rfl
        · apply Subtype.ext; apply Fin.ext
          exact Nat.add_sub_of_le (Nat.le_of_not_gt hi)
      right_inv := by
        intro i
        rcases i with i | i
        · simp [lt_of_lt_of_le i.1.2 (Nat.min_le_right _ _)]
        · simp [Nat.not_lt.mpr (Nat.le_add_right A i.1.1)] }
  change Fintype.card {i : Fin r // Fin.append z₁ z₂
      ⟨i.1, lt_of_lt_of_le i.2 hr⟩ = v} = _
  rw [Fintype.card_congr e, Fintype.card_sum]
  rfl

private lemma histogram_forgetOutcome {N d : Nat}
    (z : Fin N → Obs d) (x : Fin d) (a : Bool) :
    finiteSampleHistogram (fun i ↦ ((z i).1, (z i).2.1)) (x, a) =
      finiteSampleHistogram z (x, a, false) +
        finiteSampleHistogram z (x, a, true) := by
  classical
  unfold finiteSampleHistogram
  let e : {i : Fin N // ((z i).1, (z i).2.1) = (x, a)} ≃
      ({i : Fin N // z i = (x, a, false)} ⊕
        {i : Fin N // z i = (x, a, true)}) :=
    { toFun := fun i => if hy : (z i.1).2.2 = false then
          Sum.inl ⟨i.1, by
            apply Prod.ext
            · exact congrArg (fun q : Fin d × Bool => q.1) i.2
            · apply Prod.ext
              · exact congrArg (fun q : Fin d × Bool => q.2) i.2
              · exact hy⟩
        else Sum.inr ⟨i.1, by
          have hy' : (z i.1).2.2 = true := by
            cases h : (z i.1).2.2 <;> simp_all
          apply Prod.ext
          · exact congrArg (fun q : Fin d × Bool => q.1) i.2
          · apply Prod.ext
            · exact congrArg (fun q : Fin d × Bool => q.2) i.2
            · exact hy'⟩
      invFun := fun i => match i with
        | Sum.inl j => ⟨j.1, by simpa using congrArg (fun w => (w.1, w.2.1)) j.2⟩
        | Sum.inr j => ⟨j.1, by simpa using congrArg (fun w => (w.1, w.2.1)) j.2⟩
      left_inv := by
        intro i
        dsimp
        split_ifs <;> apply Subtype.ext <;> rfl
      right_inv := by
        intro i
        rcases i with i | i
        · simp [i.2]
        · simp [i.2] }
  rw [Fintype.card_congr e, Fintype.card_sum]

private lemma histogram_prefix_forgetOutcome {N r d : Nat}
    (z : Fin N → Obs d) (hr : r ≤ N) (x : Fin d) (a : Bool) :
    finiteSampleHistogram
        (prefixOfLE (fun i ↦ ((z i).1, (z i).2.1)) r hr).points (x, a) =
      finiteSampleHistogram (prefixOfLE z r hr).points (x, a, false) +
        finiteSampleHistogram (prefixOfLE z r hr).points (x, a, true) := by
  change finiteSampleHistogram
      (fun i ↦ (((prefixOfLE z r hr).points i).1,
        ((prefixOfLE z r hr).points i).2.1)) (x, a) = _
  exact histogram_forgetOutcome (z := (prefixOfLE z r hr).points) x a

/-- The three retained generic prefixes read back as exactly the paper's
complete, pilot, and factorial block counts.  [the stated conditions](hyp:hr0,hrp,hrf) [the stated conclusion](goal). -/
lemma finitePrefixHybridStatistic_fixedPools {n m d : Nat}
    (eps : Real) (sample : Sample n m d) (r0 rp rf : Nat)
    (hr0 : r0 ≤ (blockSizes n m).M0)
    (hrp : rp ≤ (blockSizes n m).np + (blockSizes n m).mp)
    (hrf : rf ≤ (blockSizes n m).nf + (blockSizes n m).mf) :
    finitePrefixHybridStatistic n m eps
        (fun i ↦ match i with
          | ThreePoolIndex.complete =>
              prefixOfLE (hybridFixedPools sample .complete) r0 hr0
          | ThreePoolIndex.sharedLeft =>
              prefixOfLE (hybridFixedPools sample .sharedLeft) rp hrp
          | ThreePoolIndex.sharedRight =>
              prefixOfLE (hybridFixedPools sample .sharedRight) rf hrf) =
      prefixOutput eps sample r0 rp rf := by
  classical
  let bs := blockSizes n m
  simp only [threePoolCapacity, ThreePoolAlphabet] at hr0 hrp hrf ⊢
  change r0 ≤ bs.M0 at hr0
  change rp ≤ bs.np + bs.mp at hrp
  change rf ≤ bs.nf + bs.mf at hrf
  have hmarked (x : Fin d) (a : Bool) :
      finiteSampleHistogram
          (prefixOfLE (hybridFixedPools sample .complete) r0 hr0).points
          (x, a, true) = labeledBlockCount sample.1 0 r0 x a true := by
    simp only [hybridFixedPools, threePoolCapacity, ThreePoolAlphabet, id_eq]
    rw [histogram_prefix_eq_filter]
    unfold labeledBlockCount
    have h := card_prefix_offset_eq_filter sample.1
      (offset := 0) (L := bs.M0) (r := r0)
      (by dsimp [bs, blockSizes]; omega) hr0 (x, a, true)
    simpa [hybridFixedPools, bs] using h
  have hp (x : Fin d) (a : Bool) :
      finiteSampleHistogram
          (prefixOfLE (hybridFixedPools sample .sharedLeft) rp hrp).points (x, a) =
        pooledArmCount sample bs.M0 bs.np 0 rp x a := by
    simp only [hybridFixedPools, threePoolCapacity, ThreePoolAlphabet, id_eq]
    rw [histogram_prefix_append, histogram_prefix_forgetOutcome,
      histogram_prefix_eq_filter, histogram_prefix_eq_filter,
      histogram_prefix_eq_filter]
    unfold pooledArmCount labeledArmBlockCount labeledBlockCount auxiliaryBlockCount
    have hL0 := card_prefix_offset_eq_filter sample.1
      (offset := bs.M0) (L := bs.np) (r := min rp bs.np)
      (by dsimp [bs, blockSizes]; omega) (Nat.min_le_right _ _) (x, a, false)
    have hL1 := card_prefix_offset_eq_filter sample.1
      (offset := bs.M0) (L := bs.np) (r := min rp bs.np)
      (by dsimp [bs, blockSizes]; omega) (Nat.min_le_right _ _) (x, a, true)
    have hA := card_prefix_offset_eq_filter sample.2
      (offset := 0) (L := bs.mp) (r := rp - bs.np)
      (by dsimp [bs, blockSizes]; omega) (by omega) (x, a)
    simpa [hybridFixedPools, bs] using
      (congrArg₂ (fun p q : Nat ↦ p + q)
        (congrArg₂ (fun p q : Nat ↦ p + q) hL0 hL1) hA)
  have hf (x : Fin d) (a : Bool) :
      finiteSampleHistogram
          (prefixOfLE (hybridFixedPools sample .sharedRight) rf hrf).points (x, a) =
        pooledArmCount sample (bs.M0 + bs.np) bs.nf bs.mp rf x a := by
    simp only [hybridFixedPools, threePoolCapacity, ThreePoolAlphabet, id_eq]
    rw [histogram_prefix_append, histogram_prefix_forgetOutcome,
      histogram_prefix_eq_filter, histogram_prefix_eq_filter,
      histogram_prefix_eq_filter]
    unfold pooledArmCount labeledArmBlockCount labeledBlockCount auxiliaryBlockCount
    have hL0 := card_prefix_offset_eq_filter sample.1
      (offset := bs.M0 + bs.np) (L := bs.nf) (r := min rf bs.nf)
      (by dsimp [bs, blockSizes]; omega) (Nat.min_le_right _ _) (x, a, false)
    have hL1 := card_prefix_offset_eq_filter sample.1
      (offset := bs.M0 + bs.np) (L := bs.nf) (r := min rf bs.nf)
      (by dsimp [bs, blockSizes]; omega) (Nat.min_le_right _ _) (x, a, true)
    have hA := card_prefix_offset_eq_filter sample.2
      (offset := bs.mp) (L := bs.mf) (r := rf - bs.nf)
      (by dsimp [bs, blockSizes]; omega) (by omega) (x, a)
    simpa [hybridFixedPools, bs] using
      (congrArg₂ (fun p q : Nat ↦ p + q)
        (congrArg₂ (fun p q : Nat ↦ p + q) hL0 hL1) hA)
  simp only [hybridFixedPools, threePoolCapacity, ThreePoolAlphabet, id_eq]
    at hmarked hp hf ⊢
  unfold finitePrefixHybridStatistic prefixOutput hybridPrefixCounts
  simp_rw [hmarked, hp, hf]
  rfl

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
