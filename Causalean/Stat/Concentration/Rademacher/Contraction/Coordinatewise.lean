/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Rademacher.Contraction.Absolute

/-!
# Coordinatewise Rademacher contraction

This module gives the Ledoux--Talagrand contraction principle when the scalar contraction may
depend on the sample coordinate.  Thus the transformed signed sum contains
`σ k * φ k (F i (S k))`, with a common Lipschitz constant but a different map `φ k` at every
coordinate.  The signed theorem has constant `L`; the absolute-value form has constant `2L`.
-/

@[expose] public section

namespace Causalean.Stat.Concentration

variable {ι 𝒳 : Type*}

/-- Given [a sample size](hyp:n), [coordinatewise scalar maps](hyp:φ), [a function
class](hyp:F), and [a realized sample](hyp:S), the [coordinatewise transformed signed
Rademacher average](goal) averages the supremum of the signed transformed sums over all sign
vectors. -/
noncomputable def coordinateRademacherAverageWithoutAbs (n : ℕ) (φ : Fin n → ℝ → ℝ)
    (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) : ℝ :=
  (Fintype.card (Signs n) : ℝ)⁻¹ *
    ∑ σ : Signs n, ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ k (F i (S k))

/-- Given [a sample size](hyp:n), [coordinatewise scalar maps](hyp:φ), [a function
class](hyp:F), and [a realized sample](hyp:S), the [coordinatewise transformed absolute
Rademacher average](goal) averages the supremum of the absolute signed transformed sums. -/
noncomputable def coordinateRademacherAverage (n : ℕ) (φ : Fin n → ℝ → ℝ)
    (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) : ℝ :=
  (Fintype.card (Signs n) : ℝ)⁻¹ *
    ∑ σ : Signs n, ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ k (F i (S k))|

private def coordFlip (n : ℕ) (k : Fin n) (σ : Signs n) : Signs n := fun j =>
  if j = k then -σ j else σ j

private lemma coordSign_neg_coe (s : SignAtom) : ((-s : SignAtom) : ℤ) = -(s : ℤ) := by
  rcases s with ⟨z, hz⟩
  rfl

private lemma coordSign_neg_neg (s : SignAtom) : -(-s : SignAtom) = s := by
  ext
  simp [coordSign_neg_coe]

private lemma coordFlip_same (n : ℕ) (k : Fin n) (σ : Signs n) :
    ((coordFlip n k σ k : ℤ) : ℝ) = -((σ k : ℤ) : ℝ) := by
  simp [coordFlip, coordSign_neg_coe]

private lemma coordFlip_ne (n : ℕ) {k j : Fin n} (h : j ≠ k) (σ : Signs n) :
    coordFlip n k σ j = σ j := by
  simp [coordFlip, h]

private lemma coordFlip_involutive (n : ℕ) (k : Fin n) (σ : Signs n) :
    coordFlip n k (coordFlip n k σ) = σ := by
  funext j
  by_cases h : j = k
  · subst j
    ext
    simp [coordFlip, coordSign_neg_neg]
  · simp [coordFlip, h]

private noncomputable def coordFlipEquiv (n : ℕ) (k : Fin n) : Signs n ≃ Signs n where
  toFun := coordFlip n k
  invFun := coordFlip n k
  left_inv := coordFlip_involutive n k
  right_inv := coordFlip_involutive n k

private noncomputable def coordHybridInner
    (φ : Fin n → ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (S : Fin n → 𝒳) (m : ℕ) (σ : Signs n) (i : ι) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
    if (k : ℕ) < m then L * F i (S k) else φ k (F i (S k))

private noncomputable def coordHybridAverage
    (φ : Fin n → ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (S : Fin n → 𝒳) (m : ℕ) : ℝ :=
  (Fintype.card (Signs n) : ℝ)⁻¹ *
    ∑ σ : Signs n, ⨆ i, coordHybridInner φ L F S m σ i

private noncomputable def coordHybridBase
    (φ : Fin n → ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (S : Fin n → 𝒳) (m : ℕ) (k : Fin n) (σ : Signs n) (i : ι) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase k, (σ j : ℝ) *
    if (j : ℕ) < m then L * F i (S j) else φ j (F i (S j))

private lemma coordBranch_succ_of_ne
    (φ : Fin n → ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {m : ℕ} (hm : m < n) {j : Fin n} (hj : j ≠ ⟨m, hm⟩)
    (S : Fin n → 𝒳) (i : ι) :
    (if (j : ℕ) < m + 1 then L * F i (S j) else φ j (F i (S j))) =
      if (j : ℕ) < m then L * F i (S j) else φ j (F i (S j)) := by
  have hjval : (j : ℕ) ≠ m := by
    intro h
    apply hj
    ext
    exact h
  by_cases h : (j : ℕ) < m
  · simp [h, Nat.lt_trans h (Nat.lt_succ_self m)]
  · have h' : ¬ (j : ℕ) < m + 1 := by omega
    simp [h, h']

private lemma coordInner_eq_base_add
    (φ : Fin n → ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    coordHybridInner φ L F S m σ i =
      coordHybridBase φ L F S m ⟨m, hm⟩ σ i +
        (n : ℝ)⁻¹ * (σ ⟨m, hm⟩ : ℝ) * φ ⟨m, hm⟩ (F i (S ⟨m, hm⟩)) := by
  unfold coordHybridInner coordHybridBase
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ ⟨m, hm⟩)]
  simp
  ring

private lemma coordInner_flip_eq_base_sub
    (φ : Fin n → ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    coordHybridInner φ L F S m (coordFlip n ⟨m, hm⟩ σ) i =
      coordHybridBase φ L F S m ⟨m, hm⟩ σ i -
        (n : ℝ)⁻¹ * (σ ⟨m, hm⟩ : ℝ) * φ ⟨m, hm⟩ (F i (S ⟨m, hm⟩)) := by
  unfold coordHybridInner coordHybridBase
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ ⟨m, hm⟩)]
  have hsum :
      (∑ j ∈ Finset.univ.erase ⟨m, hm⟩, ((coordFlip n ⟨m, hm⟩ σ j : ℝ) *
        if (j : ℕ) < m then L * F i (S j) else φ j (F i (S j)))) =
      ∑ j ∈ Finset.univ.erase ⟨m, hm⟩, ((σ j : ℝ) *
        if (j : ℕ) < m then L * F i (S j) else φ j (F i (S j))) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [coordFlip_ne n (Finset.mem_erase.mp hj).1 σ]
  rw [Finset.sdiff_singleton_eq_erase, hsum, coordFlip_same]
  simp
  ring

private lemma coordInner_succ_eq_base_add
    (φ : Fin n → ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    coordHybridInner φ L F S (m + 1) σ i =
      coordHybridBase φ L F S m ⟨m, hm⟩ σ i +
        (n : ℝ)⁻¹ * (σ ⟨m, hm⟩ : ℝ) * (L * F i (S ⟨m, hm⟩)) := by
  unfold coordHybridInner coordHybridBase
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ ⟨m, hm⟩)]
  have hsum :
      (∑ j ∈ Finset.univ.erase ⟨m, hm⟩, ((σ j : ℝ) *
        if (j : ℕ) < m + 1 then L * F i (S j) else φ j (F i (S j)))) =
      ∑ j ∈ Finset.univ.erase ⟨m, hm⟩, ((σ j : ℝ) *
        if (j : ℕ) < m then L * F i (S j) else φ j (F i (S j))) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [coordBranch_succ_of_ne φ L F hm (Finset.mem_erase.mp hj).1 S i]
  rw [Finset.sdiff_singleton_eq_erase, hsum]
  simp
  ring

private lemma coordInner_flip_succ_eq_base_sub
    (φ : Fin n → ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    coordHybridInner φ L F S (m + 1) (coordFlip n ⟨m, hm⟩ σ) i =
      coordHybridBase φ L F S m ⟨m, hm⟩ σ i -
        (n : ℝ)⁻¹ * (σ ⟨m, hm⟩ : ℝ) * (L * F i (S ⟨m, hm⟩)) := by
  unfold coordHybridInner coordHybridBase
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ ⟨m, hm⟩)]
  have hsum :
      (∑ j ∈ Finset.univ.erase ⟨m, hm⟩, ((coordFlip n ⟨m, hm⟩ σ j : ℝ) *
        if (j : ℕ) < m + 1 then L * F i (S j) else φ j (F i (S j)))) =
      ∑ j ∈ Finset.univ.erase ⟨m, hm⟩, ((σ j : ℝ) *
        if (j : ℕ) < m then L * F i (S j) else φ j (F i (S j))) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [coordBranch_succ_of_ne φ L F hm (Finset.mem_erase.mp hj).1 S i]
    rw [coordFlip_ne n (Finset.mem_erase.mp hj).1 σ]
  rw [Finset.sdiff_singleton_eq_erase, hsum, coordFlip_same]
  simp
  ring

private lemma coordPair_le [Nonempty ι] [Finite ι]
    (φ : Fin n → ℝ → ℝ) {L : ℝ}
    (hφ : ∀ k x y, |φ k x - φ k y| ≤ L * |x - y|)
    (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) {m : ℕ} (hm : m < n) (σ : Signs n) :
    (⨆ i, coordHybridInner φ L F S m σ i) +
        (⨆ i, coordHybridInner φ L F S m (coordFlip n ⟨m, hm⟩ σ) i) ≤
      (⨆ i, coordHybridInner φ L F S (m + 1) σ i) +
        (⨆ i, coordHybridInner φ L F S (m + 1) (coordFlip n ⟨m, hm⟩ σ) i) := by
  classical
  let k : Fin n := ⟨m, hm⟩
  let c : ℝ := (n : ℝ)⁻¹
  let a : ι → ℝ := fun i => coordHybridBase φ L F S m k σ i
  let b : ι → ℝ := fun i => F i (S k)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have h1 : (⨆ i, coordHybridInner φ L F S m σ i) =
      ⨆ i, a i + c * (σ k : ℝ) * φ k (b i) := by
    refine iSup_congr fun i => ?_
    exact coordInner_eq_base_add φ L F hm S σ i
  have h2 : (⨆ i, coordHybridInner φ L F S m (coordFlip n k σ) i) =
      ⨆ i, a i - c * (σ k : ℝ) * φ k (b i) := by
    refine iSup_congr fun i => ?_
    exact coordInner_flip_eq_base_sub φ L F hm S σ i
  have h3 : (⨆ i, coordHybridInner φ L F S (m + 1) σ i) =
      ⨆ i, a i + c * (σ k : ℝ) * (L * b i) := by
    refine iSup_congr fun i => ?_
    exact coordInner_succ_eq_base_add φ L F hm S σ i
  have h4 : (⨆ i, coordHybridInner φ L F S (m + 1) (coordFlip n k σ) i) =
      ⨆ i, a i - c * (σ k : ℝ) * (L * b i) := by
    refine iSup_congr fun i => ?_
    exact coordInner_flip_succ_eq_base_sub φ L F hm S σ i
  have hp := sup_pair_lipschitz_scaled (φ k) hc (hφ k) a b
  rcases signAtom_coe_real_eq_neg_one_or_one (σ k) with hs | hs
  · rw [h1, h2, h3, h4]
    simpa [hs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hp
  · rw [h1, h2, h3, h4]
    simpa [hs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hp

private lemma sum_coordFlip (n : ℕ) (k : Fin n) (A : Signs n → ℝ) :
    ∑ σ : Signs n, A (coordFlip n k σ) = ∑ σ : Signs n, A σ :=
  Fintype.sum_bijective (coordFlip n k) (coordFlipEquiv n k).bijective _ _ fun _ => rfl

private lemma coordHybrid_step [Nonempty ι] [Finite ι]
    (φ : Fin n → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ k x y, |φ k x - φ k y| ≤ L * |x - y|)
    (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) {m : ℕ} (hm : m < n) :
    coordHybridAverage φ L F S m ≤ coordHybridAverage φ L F S (m + 1) := by
  classical
  unfold coordHybridAverage
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  let k : Fin n := ⟨m, hm⟩
  let A : Signs n → ℝ := fun σ => ⨆ i, coordHybridInner φ L F S m σ i
  let B : Signs n → ℝ := fun σ => ⨆ i, coordHybridInner φ L F S (m + 1) σ i
  have hp : ∑ σ : Signs n, (A σ + A (coordFlip n k σ)) ≤
      ∑ σ : Signs n, (B σ + B (coordFlip n k σ)) := by
    refine Finset.sum_le_sum fun σ _ => ?_
    exact coordPair_le φ hφ F S hm σ
  have hA : ∑ σ : Signs n, (A σ + A (coordFlip n k σ)) = 2 * ∑ σ, A σ := by
    rw [Finset.sum_add_distrib, sum_coordFlip]
    ring
  have hB : ∑ σ : Signs n, (B σ + B (coordFlip n k σ)) = 2 * ∑ σ, B σ := by
    rw [Finset.sum_add_distrib, sum_coordFlip]
    ring
  rw [hA, hB] at hp
  nlinarith

private lemma coordHybrid_zero [Finite ι]
    (φ : Fin n → ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) :
    coordHybridAverage φ L F S 0 = coordinateRademacherAverageWithoutAbs n φ F S := by
  simp [coordHybridAverage, coordHybridInner, coordinateRademacherAverageWithoutAbs]

private lemma coordHybrid_full [Finite ι]
    (φ : Fin n → ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) :
    coordHybridAverage φ L F S n =
      empiricalRademacherComplexity_without_abs n (fun i x => L * F i x) S := by
  simp [coordHybridAverage, coordHybridInner, empiricalRademacherComplexity_without_abs]

private lemma coordHybrid_zero_le_full [Nonempty ι] [Finite ι]
    (φ : Fin n → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ k x y, |φ k x - φ k y| ≤ L * |x - y|)
    (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) :
    coordHybridAverage φ L F S 0 ≤ coordHybridAverage φ L F S n := by
  let H := fun m => coordHybridAverage φ L F S m
  have hchain : ∀ m, m ≤ n → H 0 ≤ H m := by
    intro m hm
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
      exact (ih (Nat.le_trans (Nat.le_succ m) hm)).trans
        (coordHybrid_step φ hL hφ F S (Nat.lt_of_succ_le hm))
  exact hchain n le_rfl

/-- **Coordinatewise Ledoux--Talagrand contraction, signed form.** If [the common
constant is nonnegative](hyp:hL) and [every coordinate map `φ k` is `L`-Lipschitz](hyp:hφ),
then [the coordinatewise transformed signed Rademacher average of the class `F` on `S` is at
most `L` times its ordinary signed empirical Rademacher complexity](goal). -/
theorem rademacher_contraction_coordinatewise
    [Nonempty ι] [Finite ι]
    {n : ℕ} (φ : Fin n → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ k x y, |φ k x - φ k y| ≤ L * |x - y|)
    (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) :
    coordinateRademacherAverageWithoutAbs n φ F S ≤
      L * empiricalRademacherComplexity_without_abs n F S := by
  classical
  letI := Fintype.ofFinite ι
  calc
    coordinateRademacherAverageWithoutAbs n φ F S = coordHybridAverage φ L F S 0 :=
      (coordHybrid_zero φ L F S).symm
    _ ≤ coordHybridAverage φ L F S n := coordHybrid_zero_le_full φ hL hφ F S
    _ = empiricalRademacherComplexity_without_abs n (fun i x => L * F i x) S :=
      coordHybrid_full φ L F S
    _ = L * empiricalRademacherComplexity_without_abs n F S :=
      empiricalRademacherComplexity_without_abs_smul_class F L hL n S

private def coordWithZero (F : ι → 𝒳 → ℝ) : Option ι → 𝒳 → ℝ
  | none, _ => 0
  | some i, x => F i x

private lemma coordinate_abs_withZero_eq [Nonempty ι] [Finite ι]
    (F : ι → 𝒳 → ℝ) (n : ℕ) (φ : Fin n → ℝ → ℝ)
    (hzero : ∀ k, φ k 0 = 0) (S : Fin n → 𝒳) :
    coordinateRademacherAverage n φ (coordWithZero F) S =
      coordinateRademacherAverage n φ F S := by
  classical
  letI := Fintype.ofFinite ι
  unfold coordinateRademacherAverage
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  apply le_antisymm
  · refine ciSup_le fun o => ?_
    cases o with
    | none =>
      simp only [coordWithZero, hzero, mul_zero, Finset.sum_const_zero, abs_zero, abs_mul,
        abs_inv, Nat.abs_cast]
      let i₀ : ι := Classical.choice inferInstance
      exact le_trans
        (mul_nonneg (by positivity)
          (abs_nonneg (∑ k : Fin n, (σ k : ℝ) * φ k (F i₀ (S k)))))
        (le_ciSup (Finite.bddAbove_range (fun i : ι =>
          (n : ℝ)⁻¹ * |∑ k : Fin n, (σ k : ℝ) * φ k (F i (S k))|)) i₀)
    | some i =>
      exact le_ciSup (Finite.bddAbove_range (fun i : ι =>
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ k (F i (S k))|)) i
  · refine ciSup_le fun i => ?_
    exact le_ciSup (Finite.bddAbove_range (fun o : Option ι =>
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ k (coordWithZero F o (S k))|))
      (some i)

private lemma signed_withZero_le_abs [Nonempty ι] [Finite ι]
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n (coordWithZero F) S ≤
      empiricalRademacherComplexity n F S := by
  classical
  letI := Fintype.ofFinite ι
  unfold empiricalRademacherComplexity_without_abs empiricalRademacherComplexity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)
  refine ciSup_le fun o => ?_
  cases o with
  | none =>
    simp only [coordWithZero, mul_zero, Finset.sum_const_zero, abs_mul, abs_inv,
      Nat.abs_cast]
    let i₀ : ι := Classical.choice inferInstance
    exact le_trans
      (mul_nonneg (by positivity)
        (abs_nonneg (∑ k : Fin n, (σ k : ℝ) * F i₀ (S k))))
      (le_ciSup (Finite.bddAbove_range (fun i : ι =>
        (n : ℝ)⁻¹ * |∑ k : Fin n, (σ k : ℝ) * F i (S k)|)) i₀)
  | some i =>
    exact (le_abs_self _).trans (le_ciSup (Finite.bddAbove_range (fun i : ι =>
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)|)) i)

private lemma coordinate_abs_le_signed_add_neg [Finite ι]
    (F : Option ι → 𝒳 → ℝ) (n : ℕ) (φ : Fin n → ℝ → ℝ)
    (S : Fin n → 𝒳) (hzero : ∀ k, φ k (F none (S k)) = 0) :
    coordinateRademacherAverage n φ F S ≤
      coordinateRademacherAverageWithoutAbs n φ F S +
        coordinateRademacherAverageWithoutAbs n (fun k x => -φ k x) F S := by
  classical
  unfold coordinateRademacherAverage coordinateRademacherAverageWithoutAbs
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)
  have hz : (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ k (F none (S k)) = 0 := by
    have : ∀ k : Fin n, (σ k : ℝ) * φ k (F none (S k)) = 0 :=
      fun k => by rw [hzero k, mul_zero]
    simp_rw [this]
    simp
  have hp := iSup_abs_le_iSup_add_iSup_neg_of_exists_zero
    (fun i : Option ι => (n : ℝ)⁻¹ *
      ∑ k : Fin n, (σ k : ℝ) * φ k (F i (S k))) ⟨none, hz⟩
  have hneg :
      (⨆ i : Option ι, -((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ k (F i (S k)))) =
        ⨆ i : Option ι, (n : ℝ)⁻¹ *
          ∑ k : Fin n, (σ k : ℝ) * (-φ k (F i (S k))) := by
    refine iSup_congr fun i => ?_
    calc
      -((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ k (F i (S k))) =
          (n : ℝ)⁻¹ * (-∑ k : Fin n, (σ k : ℝ) * φ k (F i (S k))) := by ring
      _ = (n : ℝ)⁻¹ * ∑ k : Fin n, -((σ k : ℝ) * φ k (F i (S k))) := by
        rw [Finset.sum_neg_distrib]
      _ = (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (-φ k (F i (S k))) := by
        congr 1
        refine Finset.sum_congr rfl fun k _ => by ring
  simpa [hneg] using hp

/-- **Coordinatewise Ledoux--Talagrand contraction, absolute-value form.** If
[every coordinate map fixes zero and is `L`-Lipschitz](hyp:hφ), then [the coordinatewise
transformed absolute Rademacher average of `F` on `S` is at most `2L` times the ordinary
absolute empirical Rademacher complexity](goal). -/
theorem rademacher_contraction_abs_coordinatewise
    [Nonempty ι] [Finite ι]
    {n : ℕ} (φ : Fin n → ℝ → ℝ) {L : ℝ} (hφ : ∀ k, LipschitzAt0 (φ k) L)
    (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) :
    coordinateRademacherAverage n φ F S ≤
      2 * L * empiricalRademacherComplexity n F S := by
  classical
  letI := Fintype.ofFinite ι
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coordinateRademacherAverage, empiricalRademacherComplexity]
  · have hL : 0 ≤ L := by
      have h := (hφ (⟨0, hn⟩ : Fin n)).2 0 1
      rw [(hφ _).1] at h
      norm_num at h
      exact (abs_nonneg _).trans h
    let F₀ : Option ι → 𝒳 → ℝ := coordWithZero F
    have hsplit := coordinate_abs_le_signed_add_neg F₀ n φ S
      (fun k => by simp [F₀, coordWithZero, (hφ k).1])
    have hpos : coordinateRademacherAverageWithoutAbs n φ F₀ S ≤
        L * empiricalRademacherComplexity_without_abs n F₀ S :=
      rademacher_contraction_coordinatewise φ hL (fun k => (hφ k).2) F₀ S
    have hneg : coordinateRademacherAverageWithoutAbs n (fun k x => -φ k x) F₀ S ≤
        L * empiricalRademacherComplexity_without_abs n F₀ S := by
      apply rademacher_contraction_coordinatewise (fun k x => -φ k x) hL
      · intro k
        exact (lipschitzAt0_neg (φ k) (hφ k)).2
    have hbase := signed_withZero_le_abs F n S
    calc
      coordinateRademacherAverage n φ F S = coordinateRademacherAverage n φ F₀ S :=
        (coordinate_abs_withZero_eq F n φ (fun k => (hφ k).1) S).symm
      _ ≤ coordinateRademacherAverageWithoutAbs n φ F₀ S +
            coordinateRademacherAverageWithoutAbs n (fun k x => -φ k x) F₀ S := hsplit
      _ ≤ L * empiricalRademacherComplexity_without_abs n F₀ S +
            L * empiricalRademacherComplexity_without_abs n F₀ S := add_le_add hpos hneg
      _ = 2 * L * empiricalRademacherComplexity_without_abs n F₀ S := by ring
      _ ≤ 2 * L * empiricalRademacherComplexity n F S :=
        mul_le_mul_of_nonneg_left hbase (by nlinarith)

end Causalean.Stat.Concentration
