/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Ledoux–Talagrand contraction principle

For an `L`-Lipschitz real transformation `φ` that fixes zero, the signed
empirical Rademacher complexity of the composed class `φ ∘ F` is at most `L`
times the signed empirical Rademacher complexity of `F`. The corresponding
absolute-value empirical Rademacher complexity theorem in this file pays the
extra standard factor and gives a `2L` bound.

The proof formalizes the usual hybrid/sign-swap argument through private
helpers such as `hybrid_pair_le` and `hybridAverage_mono_step`. The
without-absolute-values headline theorem is `rademacher_contraction`; the
absolute-value corollary is `rademacher_contraction_abs`.

References:
* Ledoux & Talagrand, *Probability in Banach Spaces*, Springer 1991,
  Theorem 4.12.
-/

module
public import Causalean.Stat.Concentration.Rademacher.Rademacher

/-! # Signed Rademacher contraction

This file proves the finite-index Ledoux--Talagrand contraction principle for
signed empirical Rademacher averages. It defines `LipschitzAt0`, develops the
hybrid sign-swap argument, and exports `rademacher_contraction` together with
the signed scaling law. Absolute-value and arbitrary-index consequences are
provided by `Contraction/Absolute.lean`. -/

@[expose] public section

namespace Causalean
namespace Stat
namespace Concentration

/-- For [a real-valued transformation](hyp:φ) and [a real constant](hyp:L), [the transformation is Lipschitz at zero with constant $L$](goal) exactly when (1) [it maps zero to zero](step:1) and (2) [for every two real numbers $x$ and $y$, its increment has absolute value at most $L|x-y|$](step:2).

The zero condition is used by the absolute-value contraction theorem; the signed theorem needs only the global Lipschitz inequality. -/
def LipschitzAt0 (φ : ℝ → ℝ) (L : ℝ) : Prop :=
  φ 0 = 0 ∧ ∀ x y, |φ x - φ y| ≤ L * |x - y|

section Contraction

variable {ι 𝒳 : Type*}

/-- The [sign atom](goal) is the two-element type containing the signs minus one and one. It
provides the individual Rademacher signs used in the signed contraction argument. -/
abbrev SignAtom := ({-1, 1} : Finset ℤ)

private lemma signAtom_neg_coe_int (s : SignAtom) :
    ((-s : SignAtom) : ℤ) = - (s : ℤ) := by
  rcases s with ⟨z, hz⟩
  rfl

private lemma signAtom_neg_neg (s : SignAtom) : -(-s : SignAtom) = s := by
  ext
  simp [signAtom_neg_coe_int]

private def flipSign (n : ℕ) (k : Fin n) (σ : Signs n) : Signs n := fun j =>
  if j = k then -σ j else σ j

private lemma flipSign_apply_same (n : ℕ) (k : Fin n) (σ : Signs n) :
    (((flipSign n k σ k : ℤ) : ℝ) = -(((σ k : ℤ) : ℝ))) := by
  simp [flipSign, signAtom_neg_coe_int]

private lemma flipSign_apply_ne (n : ℕ) {k j : Fin n} (h : j ≠ k) (σ : Signs n) :
    flipSign n k σ j = σ j := by
  simp [flipSign, h]

private lemma flipSign_involutive (n : ℕ) (k : Fin n) (σ : Signs n) :
    flipSign n k (flipSign n k σ) = σ := by
  funext j
  by_cases h : j = k
  · subst h
    simp [flipSign, signAtom_neg_neg]
  · simp [flipSign, h]

private noncomputable def flipSignEquiv (n : ℕ) (k : Fin n) : Signs n ≃ Signs n where
  toFun := flipSign n k
  invFun := flipSign n k
  left_inv := flipSign_involutive n k
  right_inv := flipSign_involutive n k

/-- A real-valued function on a nonempty finite population attains a largest value, and its
supremum is that value. -/
lemma finite_iSup_eq_value {α : Type*} [Nonempty α] [Finite α]
    (f : α → ℝ) : ∃ a : α, (⨆ x, f x) = f a ∧ ∀ x, f x ≤ f a := by
  classical
  rcases Finite.exists_max f with ⟨a, ha⟩
  refine ⟨a, ?_, ha⟩
  exact le_antisymm (ciSup_le ha) (le_ciSup (Finite.bddAbove_range f) a)

/-- For a finite nonempty collection, the sum of the largest values obtained by adding and
subtracting a nonnegative multiple of a transformation with a given Lipschitz constant is no
greater than the corresponding sum using that linear bound. -/
lemma sup_pair_lipschitz_scaled
    {ι : Type*} [Nonempty ι] [Finite ι]
    (φ : ℝ → ℝ) {L c : ℝ} (hc : 0 ≤ c)
    (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|)
    (a : ι → ℝ) (b : ι → ℝ) :
    (⨆ i, a i + c * φ (b i)) + (⨆ i, a i - c * φ (b i))
      ≤ (⨆ i, a i + c * (L * b i)) + (⨆ i, a i - c * (L * b i)) := by
  classical
  rcases finite_iSup_eq_value (fun i : ι => a i + c * φ (b i)) with
    ⟨i₁, hi₁eq, _hi₁max⟩
  rcases finite_iSup_eq_value (fun i : ι => a i - c * φ (b i)) with
    ⟨i₂, hi₂eq, _hi₂max⟩
  rw [hi₁eq, hi₂eq]
  have hdiff : φ (b i₁) - φ (b i₂) ≤ L * |b i₁ - b i₂| := by
    exact (le_abs_self _).trans (hφ (b i₁) (b i₂))
  have hcdiff : c * (φ (b i₁) - φ (b i₂)) ≤ c * (L * |b i₁ - b i₂|) := by
    exact mul_le_mul_of_nonneg_left hdiff hc
  by_cases hcase : b i₂ ≤ b i₁
  · have habs : |b i₁ - b i₂| = b i₁ - b i₂ :=
      abs_of_nonneg (sub_nonneg.mpr hcase)
    have hmain :
        a i₁ + c * φ (b i₁) + (a i₂ - c * φ (b i₂))
          ≤ (a i₁ + c * (L * b i₁)) + (a i₂ - c * (L * b i₂)) := by
      rw [habs] at hcdiff
      linarith
    refine hmain.trans ?_
    exact add_le_add
      (le_ciSup (Finite.bddAbove_range (fun i : ι => a i + c * (L * b i))) i₁)
      (le_ciSup (Finite.bddAbove_range (fun i : ι => a i - c * (L * b i))) i₂)
  · have hcase' : b i₁ ≤ b i₂ := le_of_not_ge hcase
    have habs : |b i₁ - b i₂| = b i₂ - b i₁ := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr hcase')
    have hmain :
        a i₁ + c * φ (b i₁) + (a i₂ - c * φ (b i₂))
          ≤ (a i₂ + c * (L * b i₂)) + (a i₁ - c * (L * b i₁)) := by
      rw [habs] at hcdiff
      linarith
    refine hmain.trans ?_
    have hp := le_ciSup (Finite.bddAbove_range (fun i : ι => a i + c * (L * b i))) i₂
    have hm := le_ciSup (Finite.bddAbove_range (fun i : ι => a i - c * (L * b i))) i₁
    linarith

private noncomputable def hybridInner
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (n : ℕ) (S : Fin n → 𝒳) (m : ℕ) (σ : Signs n) (i : ι) : ℝ :=
  (n : ℝ)⁻¹ *
    ∑ k : Fin n, (σ k : ℝ) *
      (if (k : ℕ) < m then L * F i (S k) else φ (F i (S k)))

private noncomputable def hybridAverage
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (n : ℕ) (S : Fin n → 𝒳) (m : ℕ) : ℝ :=
  (Fintype.card (Signs n) : ℝ)⁻¹ *
    ∑ σ : Signs n, ⨆ i, hybridInner φ L F n S m σ i

private noncomputable def hybridBase
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (n : ℕ) (S : Fin n → 𝒳) (m : ℕ) (k : Fin n) (σ : Signs n) (i : ι) : ℝ :=
  (n : ℝ)⁻¹ *
    ∑ j ∈ (Finset.univ.erase k), (σ j : ℝ) *
      (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j)))

private lemma hybrid_branch_succ_eq_of_ne
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {n : ℕ} {m : ℕ} (hm : m < n) {j : Fin n}
    (hj : j ≠ (⟨m, hm⟩ : Fin n)) (S : Fin n → 𝒳) (i : ι) :
    (if (j : ℕ) < m + 1 then L * F i (S j) else φ (F i (S j)))
      =
    (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j))) := by
  have hjval : (j : ℕ) ≠ m := by
    intro h
    apply hj
    ext
    simpa using h
  by_cases hjm : (j : ℕ) < m
  · have hjm' : (j : ℕ) < m + 1 := Nat.lt_trans hjm (Nat.lt_succ_self m)
    simp [hjm, hjm']
  · have hjm' : ¬ (j : ℕ) < m + 1 := by
      intro hlt
      have hle : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp hlt
      omega
    simp [hjm, hjm']

private lemma hybridInner_eq_base_add_phi
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {n : ℕ} {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    hybridInner φ L F n S m σ i
      =
    hybridBase φ L F n S m (⟨m, hm⟩ : Fin n) σ i
      + (n : ℝ)⁻¹ * (σ (⟨m, hm⟩ : Fin n) : ℝ) * φ (F i (S ⟨m, hm⟩)) := by
  unfold hybridInner hybridBase
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ (⟨m, hm⟩ : Fin n))]
  simp
  ring

private lemma hybridInner_flip_eq_base_sub_phi
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {n : ℕ} {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    hybridInner φ L F n S m (flipSign n (⟨m, hm⟩ : Fin n) σ) i
      =
    hybridBase φ L F n S m (⟨m, hm⟩ : Fin n) σ i
      - (n : ℝ)⁻¹ * (σ (⟨m, hm⟩ : Fin n) : ℝ) * φ (F i (S ⟨m, hm⟩)) := by
  unfold hybridInner hybridBase
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ (⟨m, hm⟩ : Fin n))]
  have hsum :
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
          ((flipSign n (⟨m, hm⟩ : Fin n) σ j : ℝ) *
            (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j)))) =
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
      ((σ j : ℝ) *
            (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j)))) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjne : j ≠ (⟨m, hm⟩ : Fin n) := (Finset.mem_erase.mp hj).1
    simp [flipSign_apply_ne n hjne σ]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [hsum]
  have hflip := flipSign_apply_same n (⟨m, hm⟩ : Fin n) σ
  simp only [Int.reduceNeg, mul_ite, Finset.mem_univ, Finset.sum_erase_eq_sub,
    lt_self_iff_false, ↓reduceIte]
  rw [hflip]
  ring

private lemma hybridInner_succ_eq_base_add_linear
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {n : ℕ} {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    hybridInner φ L F n S (m + 1) σ i
      =
    hybridBase φ L F n S m (⟨m, hm⟩ : Fin n) σ i
      + (n : ℝ)⁻¹ * (σ (⟨m, hm⟩ : Fin n) : ℝ) * (L * F i (S ⟨m, hm⟩)) := by
  unfold hybridInner hybridBase
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ (⟨m, hm⟩ : Fin n))]
  have hsum :
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
          ((σ j : ℝ) *
            (if (j : ℕ) < m + 1 then L * F i (S j) else φ (F i (S j)))) =
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
          ((σ j : ℝ) *
            (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j)))) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjne : j ≠ (⟨m, hm⟩ : Fin n) := (Finset.mem_erase.mp hj).1
    rw [hybrid_branch_succ_eq_of_ne φ L F hm hjne S i]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [hsum]
  simp
  ring

private lemma hybridInner_flip_succ_eq_base_sub_linear
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {n : ℕ} {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    hybridInner φ L F n S (m + 1) (flipSign n (⟨m, hm⟩ : Fin n) σ) i
      =
    hybridBase φ L F n S m (⟨m, hm⟩ : Fin n) σ i
      - (n : ℝ)⁻¹ * (σ (⟨m, hm⟩ : Fin n) : ℝ) * (L * F i (S ⟨m, hm⟩)) := by
  unfold hybridInner hybridBase
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ (⟨m, hm⟩ : Fin n))]
  have hsum :
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
          ((flipSign n (⟨m, hm⟩ : Fin n) σ j : ℝ) *
            (if (j : ℕ) < m + 1 then L * F i (S j) else φ (F i (S j)))) =
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
          ((σ j : ℝ) *
            (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j)))) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjne : j ≠ (⟨m, hm⟩ : Fin n) := (Finset.mem_erase.mp hj).1
    rw [hybrid_branch_succ_eq_of_ne φ L F hm hjne S i]
    simp [flipSign_apply_ne n hjne σ]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [hsum]
  have hflip := flipSign_apply_same n (⟨m, hm⟩ : Fin n) σ
  simp only [Int.reduceNeg, mul_ite, Finset.mem_univ, Finset.sum_erase_eq_sub,
    lt_self_iff_false, ↓reduceIte, lt_add_iff_pos_right, zero_lt_one]
  rw [hflip]
  ring

/-- [Every sign atom, viewed as a real number, is either minus one or one](goal). -/
lemma signAtom_coe_real_eq_neg_one_or_one (s : SignAtom) :
    (s : ℝ) = -1 ∨ (s : ℝ) = 1 := by
  rcases s with ⟨z, hz⟩
  simp only [Finset.mem_insert, Int.reduceNeg, Finset.mem_singleton, Int.cast_eq_one] at hz ⊢
  rcases hz with rfl | rfl
  · left
    norm_num
  · right
    norm_num

private lemma hybrid_pair_le
    [Nonempty ι] [Finite ι]
    (φ : ℝ → ℝ) {L : ℝ}
    (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|)
    (F : ι → 𝒳 → ℝ) {n : ℕ} (S : Fin n → 𝒳)
    {m : ℕ} (hm : m < n) (σ : Signs n) :
    (⨆ i, hybridInner φ L F n S m σ i)
        + (⨆ i, hybridInner φ L F n S m (flipSign n (⟨m, hm⟩ : Fin n) σ) i)
      ≤
    (⨆ i, hybridInner φ L F n S (m + 1) σ i)
        + (⨆ i, hybridInner φ L F n S (m + 1)
              (flipSign n (⟨m, hm⟩ : Fin n) σ) i) := by
  classical
  let k : Fin n := ⟨m, hm⟩
  let c : ℝ := (n : ℝ)⁻¹
  let a : ι → ℝ := fun i => hybridBase φ L F n S m k σ i
  let b : ι → ℝ := fun i => F i (S k)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hφ₁ :
      (⨆ i, hybridInner φ L F n S m σ i)
        = ⨆ i, a i + c * (σ k : ℝ) * φ (b i) := by
    refine iSup_congr fun i => ?_
    dsimp [a, b, c, k]
    rw [hybridInner_eq_base_add_phi φ L F hm S σ i]
  have hφ₂ :
      (⨆ i, hybridInner φ L F n S m (flipSign n k σ) i)
        = ⨆ i, a i - c * (σ k : ℝ) * φ (b i) := by
    refine iSup_congr fun i => ?_
    dsimp [a, b, c, k]
    rw [hybridInner_flip_eq_base_sub_phi φ L F hm S σ i]
  have hlin₁ :
      (⨆ i, hybridInner φ L F n S (m + 1) σ i)
        = ⨆ i, a i + c * (σ k : ℝ) * (L * b i) := by
    refine iSup_congr fun i => ?_
    dsimp [a, b, c, k]
    rw [hybridInner_succ_eq_base_add_linear φ L F hm S σ i]
  have hlin₂ :
      (⨆ i, hybridInner φ L F n S (m + 1) (flipSign n k σ) i)
        = ⨆ i, a i - c * (σ k : ℝ) * (L * b i) := by
    refine iSup_congr fun i => ?_
    dsimp [a, b, c, k]
    rw [hybridInner_flip_succ_eq_base_sub_linear φ L F hm S σ i]
  rcases signAtom_coe_real_eq_neg_one_or_one (σ k) with hσ | hσ
  · have hpair := sup_pair_lipschitz_scaled φ hc hφ a b
    rw [hφ₁, hφ₂, hlin₁, hlin₂]
    simpa [hσ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hpair
  · have hpair := sup_pair_lipschitz_scaled φ hc hφ a b
    rw [hφ₁, hφ₂, hlin₁, hlin₂]
    simpa [hσ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hpair

private lemma sum_flipSign (n : ℕ) (k : Fin n) (A : Signs n → ℝ) :
    ∑ σ : Signs n, A (flipSign n k σ) = ∑ σ : Signs n, A σ := by
  exact Fintype.sum_bijective (flipSign n k) (flipSignEquiv n k).bijective _ _ fun _ => rfl

private lemma hybridAverage_mono_step
    [Nonempty ι] [Finite ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|)
    (F : ι → 𝒳 → ℝ) {n : ℕ} (S : Fin n → 𝒳)
    {m : ℕ} (hm : m < n) :
    hybridAverage φ L F n S m ≤ hybridAverage φ L F n S (m + 1) := by
  classical
  unfold hybridAverage
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  let k : Fin n := ⟨m, hm⟩
  let A : Signs n → ℝ := fun σ => ⨆ i, hybridInner φ L F n S m σ i
  let B : Signs n → ℝ := fun σ => ⨆ i, hybridInner φ L F n S (m + 1) σ i
  have hpair_sum :
      ∑ σ : Signs n, (A σ + A (flipSign n k σ))
        ≤ ∑ σ : Signs n, (B σ + B (flipSign n k σ)) := by
    refine Finset.sum_le_sum ?_
    intro σ _
    dsimp [A, B, k]
    exact hybrid_pair_le φ hφ F S hm σ
  have hA :
      ∑ σ : Signs n, (A σ + A (flipSign n k σ))
        = 2 * ∑ σ : Signs n, A σ := by
    calc
      ∑ σ : Signs n, (A σ + A (flipSign n k σ))
          = (∑ σ : Signs n, A σ) + ∑ σ : Signs n, A (flipSign n k σ) := by
            exact Finset.sum_add_distrib
      _ = (∑ σ : Signs n, A σ) + ∑ σ : Signs n, A σ := by
            rw [sum_flipSign n k A]
      _ = 2 * ∑ σ : Signs n, A σ := by ring
  have hB :
      ∑ σ : Signs n, (B σ + B (flipSign n k σ))
        = 2 * ∑ σ : Signs n, B σ := by
    calc
      ∑ σ : Signs n, (B σ + B (flipSign n k σ))
          = (∑ σ : Signs n, B σ) + ∑ σ : Signs n, B (flipSign n k σ) := by
            exact Finset.sum_add_distrib
      _ = (∑ σ : Signs n, B σ) + ∑ σ : Signs n, B σ := by
            rw [sum_flipSign n k B]
      _ = 2 * ∑ σ : Signs n, B σ := by ring
  have htwo : 2 * (∑ σ : Signs n, A σ) ≤ 2 * (∑ σ : Signs n, B σ) := by
    simpa [hA, hB] using hpair_sum
  nlinarith

private lemma hybridAverage_zero_eq
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (n : ℕ) (S : Fin n → 𝒳) :
    hybridAverage φ L F n S 0
      = empiricalRademacherComplexity_without_abs n (fun i x => φ (F i x)) S := by
  unfold hybridAverage hybridInner empiricalRademacherComplexity_without_abs
  simp

private lemma hybridAverage_full_eq_linear
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (n : ℕ) (S : Fin n → 𝒳) :
    hybridAverage φ L F n S n
      = empiricalRademacherComplexity_without_abs n (fun i x => L * F i x) S := by
  unfold hybridAverage hybridInner empiricalRademacherComplexity_without_abs
  simp

private lemma hybridAverage_zero_le_full
    [Nonempty ι] [Finite ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|)
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    hybridAverage φ L F n S 0 ≤ hybridAverage φ L F n S n := by
  classical
  let H : ℕ → ℝ := fun m => hybridAverage φ L F n S m
  have hchain : ∀ m, m ≤ n → H 0 ≤ H m := by
    intro m hm
    induction m with
    | zero =>
        exact le_rfl
    | succ m ih =>
        have hm_le : m ≤ n := Nat.le_trans (Nat.le_succ m) hm
        have hm_lt : m < n := Nat.lt_of_succ_le hm
        exact le_trans (ih hm_le) (hybridAverage_mono_step φ hL hφ F S hm_lt)
  simpa [H] using hchain n le_rfl

/-- Without-abs analogue of `empiricalRademacherComplexity_smul_class`:
    the signed scaling carries `c`, not `|c|`. -/
theorem empiricalRademacherComplexity_without_abs_smul_class
    (F : ι → 𝒳 → ℝ) (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n (fun i x => c * F i x) S
      = c * empiricalRademacherComplexity_without_abs n F S := by
  unfold empiricalRademacherComplexity_without_abs
  have hsum :
      (∑ σ : Signs n,
          ⨆ i,
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k)))
        =
      c * ∑ σ : Signs n,
          ⨆ i,
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    calc
      (⨆ i,
          (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k)))
          =
        ⨆ i,
          c * ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
          refine iSup_congr fun i => ?_
          calc
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k))
                =
              (n : ℝ)⁻¹ * (c * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
                congr 1
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun k _ => by ring
            _ =
              c * ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
                ring
      _ =
        c * ⨆ i,
          (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k) := by
          exact
            (Real.mul_iSup_of_nonneg hc
              (fun i =>
                (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k))).symm
  rw [hsum]
  ring

/-- If [the proposed Lipschitz constant is nonnegative](hyp:hL) and [the scalar transform is
Lipschitz with that constant](hyp:hφ), then [the empirical Rademacher complexity without
absolute values of the transformed class is at most that constant times the original
complexity](goal). -/
theorem rademacher_contraction_core
    [Nonempty ι] [Finite ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|)
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n
        (fun i x => φ (F i x)) S
      ≤ L * empiricalRademacherComplexity_without_abs n F S := by
  calc
    empiricalRademacherComplexity_without_abs n (fun i x => φ (F i x)) S
        = hybridAverage φ L F n S 0 := by
          rw [hybridAverage_zero_eq]
    _ ≤ hybridAverage φ L F n S n :=
          hybridAverage_zero_le_full φ hL hφ F n S
    _ = empiricalRademacherComplexity_without_abs n (fun i x => L * F i x) S := by
          rw [hybridAverage_full_eq_linear]
    _ = L * empiricalRademacherComplexity_without_abs n F S :=
          empiricalRademacherComplexity_without_abs_smul_class F L hL n S

/-- **Ledoux–Talagrand contraction principle (signed form).** If [`L` is nonnegative](hyp:hL) and
    [`φ : ℝ → ℝ` is `L`-Lipschitz, i.e. `|φ x - φ y| ≤ L * |x - y|` for all `x, y`](hyp:hLip),
    then [composing each function of the family `F` with `φ` does not increase the signed
    (without-abs) empirical Rademacher complexity on the sample `S` by more than the factor
    `L`](goal). -/
theorem rademacher_contraction
    [Nonempty ι] [Finite ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, |φ x - φ y| ≤ L * |x - y|)
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n
        (fun i x => φ (F i x)) S
      ≤ L * empiricalRademacherComplexity_without_abs n F S := by
  classical
  letI := Fintype.ofFinite ι
  exact rademacher_contraction_core φ hL hLip F n S



end Contraction
end Concentration
end Stat
end Causalean
