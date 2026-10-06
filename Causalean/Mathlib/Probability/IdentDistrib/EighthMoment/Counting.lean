module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Counting eighth-power index patterns without singleton fibers

This module bounds the variance-weighted sum of index maps supported on an arbitrary finite
set. It uses a deliberately loose counting bound: group maps by their image, bound the number
with a fixed k-element image by k⁸, and use choose(m,k) ≤ mᵏ/k!. This avoids enumerating set
partitions while retaining ample room below the requested coefficient 8!.

Primary library references include `Finset.sum_pow'`, `Finset.card_powersetCard`,
`Nat.choose_le_pow_div`, and `Finset.card_eq_sum_card_image`.
-/

@[expose] public section

open scoped BigOperators

namespace Causalean.Mathlib.Probability.IdentDistrib.EighthMoment

variable {α : Type*} [DecidableEq α]

/-- [The multiplicity](goal) of [an index value r](hyp:r) in [a map a assigning an index to each
of eight slots](hyp:a) is [the number of slots that a sends to r](step:1). -/
def multiplicity (a : Fin 8 → α) (r : α) : ℕ :=
  (Finset.univ.filter (fun j => a j = r)).card

/-- The [image](goal) of [an eight-slot index map](hyp:a) is [given by the finite set of its
used coordinates](step:1). -/
def patternImage (a : Fin 8 → α) : Finset α := Finset.univ.image a

/-- [An eight-slot index map](hyp:a) has [no singleton fibers](goal) [when every used
coordinate is required to occur at least twice](step:1). -/
def NoSingleton (a : Fin 8 → α) : Prop :=
  ∀ r ∈ patternImage a, 2 ≤ multiplicity a r

/-- The [surviving patterns](goal) on [a finite coordinate set](hyp:S) are [given by filtering
the supported eight-slot maps to retain fibers of size at least two](step:1). -/
noncomputable def survivingPatterns (S : Finset α) : Finset (Fin 8 → α) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin 8 => S)).filter NoSingleton

/-- An index map [without singleton fibers](hyp:ha) uses [between one and four
coordinates](goal). -/
theorem patternImage_card_bounds (a : Fin 8 → α) (ha : NoSingleton a) :
    1 ≤ (patternImage a).card ∧ (patternImage a).card ≤ 4 := by
  -- Sum fiber cardinalities to 8 using `Finset.card_eq_sum_card_image`; all fibers contribute ≥2.
  have hsum : ∑ r ∈ patternImage a, multiplicity a r = 8 := by
    simpa [patternImage, multiplicity] using
      (Finset.card_eq_sum_card_image a Finset.univ).symm
  have hle : (patternImage a).card * 2 ≤ 8 := by
    calc
      (patternImage a).card * 2 = ∑ r ∈ patternImage a, 2 := by simp
      _ ≤ ∑ r ∈ patternImage a, multiplicity a r := Finset.sum_le_sum ha
      _ = 8 := hsum
  constructor
  · exact Finset.card_pos.mpr ⟨a 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  · omega

/-- Among eight-slot maps supported on [a finite set](hyp:S), the number with
[a prescribed image](hyp:T) is [at most the eighth power of that image's size](goal). -/
theorem card_patterns_with_image_le (S T : Finset α) :
    ((Fintype.piFinset (fun _ : Fin 8 => S)).filter
      (fun a => patternImage a = T)).card ≤ T.card ^ 8 := by
  -- Containment in `Fintype.piFinset (fun _ : Fin 8 => T)` suffices; its card is T.card^8.
  classical
  calc
    _ ≤ (Fintype.piFinset (fun _ : Fin 8 => T)).card := by
      apply Finset.card_le_card
      intro a ha
      apply Fintype.mem_piFinset.mpr
      intro j
      rw [← (Finset.mem_filter.mp ha).2]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    _ = T.card ^ 8 := Fintype.card_piFinset_const T 8

/-- For [a nonnegative weight](hyp:hv), the sum of image-size powers over surviving maps
on [a finite coordinate set](hyp:S) is [bounded by an image-size binomial sum](goal). -/
theorem weighted_survivingPatterns_le_choose_sum (S : Finset α) (v : ℝ) (hv : 0 ≤ v) :
    (∑ a ∈ survivingPatterns S, v ^ (patternImage a).card) ≤
      ∑ k ∈ Finset.Icc 1 4, (S.card.choose k : ℝ) * (k : ℝ) ^ 8 * v ^ k := by
  -- Group by image T ∈ S.powerset, then by T.card. Use the preceding two lemmas and
  -- `Finset.card_powersetCard`. The nonnegative weight permits enlarging each image fiber.
  classical
  let P := S.powerset.filter (fun T => T.card ∈ Finset.Icc 1 4)
  have hmaps : ∀ a ∈ survivingPatterns S, patternImage a ∈ P := by
    intro a ha
    obtain ⟨hs, hn⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      intro r hr
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
      exact Fintype.mem_piFinset.mp hs j
    · exact Finset.mem_Icc.mpr (patternImage_card_bounds a hn)
  calc
    _ = ∑ T ∈ P, ∑ a ∈ (survivingPatterns S).filter (fun a => patternImage a = T),
        v ^ (patternImage a).card :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ T ∈ P, (T.card : ℝ) ^ 8 * v ^ T.card := by
      apply Finset.sum_le_sum
      intro T hT
      have hc : ((survivingPatterns S).filter (fun a => patternImage a = T)).card
          ≤ T.card ^ 8 := by
        apply le_trans (Finset.card_le_card _) (card_patterns_with_image_le S T)
        intro a ha
        obtain ⟨hs, he⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, he⟩
      calc
        _ = (((survivingPatterns S).filter (fun a => patternImage a = T)).card : ℝ)
            * v ^ T.card := by
          rw [← nsmul_eq_mul]
          rw [← Finset.sum_const]
          apply Finset.sum_congr rfl
          intro a ha
          rw [(Finset.mem_filter.mp ha).2]
        _ ≤ (T.card : ℝ) ^ 8 * v ^ T.card :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (pow_nonneg hv _)
    _ = ∑ k ∈ Finset.Icc 1 4, ∑ T ∈ P.filter (fun T => T.card = k),
        (T.card : ℝ) ^ 8 * v ^ T.card := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro T hT
      exact (Finset.mem_filter.mp hT).2
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hfilter : P.filter (fun T => T.card = k) = S.powersetCard k := by
        ext T
        simp only [P, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powerset]
        constructor
        · rintro ⟨⟨hT, _⟩, he⟩
          exact ⟨hT, he⟩
        · rintro ⟨hT, he⟩
          exact ⟨⟨hT, he ▸ hk⟩, he⟩
      calc
        _ = ∑ T ∈ P.filter (fun T => T.card = k), (k : ℝ) ^ 8 * v ^ k := by
          apply Finset.sum_congr rfl
          intro T hT
          rw [(Finset.mem_filter.mp hT).2]
        _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, hfilter, Finset.card_powersetCard]
          exact mul_assoc _ _ _ |>.symm

/-- For [a nonnegative weight](hyp:hv) and [a finite set size](hyp:m), the loose image
counting polynomial is [bounded by an explicit polynomial in size times weight](goal). -/
theorem choose_sum_le_polynomial (m : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    (∑ k ∈ Finset.Icc 1 4, (m.choose k : ℝ) * (k : ℝ) ^ 8 * v ^ k) ≤
      (m : ℝ) * v + 128 * ((m : ℝ) * v) ^ 2 +
        1094 * ((m : ℝ) * v) ^ 3 + 2731 * ((m : ℝ) * v) ^ 4 := by
  -- Use `Nat.choose_le_pow_div (α := ℝ)` for k=1,2,3,4 and nonnegativity of v^k.
  -- The coefficients round up 1^8/1!, 2^8/2!, 3^8/3!, and 4^8/4! respectively.
  have h2 := mul_le_mul_of_nonneg_right
    (Nat.choose_le_pow_div (α := ℝ) 2 m) (pow_nonneg hv 2)
  have h3 := mul_le_mul_of_nonneg_right
    (Nat.choose_le_pow_div (α := ℝ) 3 m) (pow_nonneg hv 3)
  have h4 := mul_le_mul_of_nonneg_right
    (Nat.choose_le_pow_div (α := ℝ) 4 m) (pow_nonneg hv 4)
  norm_num [Nat.factorial] at h2 h3 h4
  have hIcc : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  norm_num [hIcc, mul_pow, Nat.choose_one_right]
  nlinarith [mul_nonneg (pow_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) 3)
      (pow_nonneg hv 3),
    mul_nonneg (pow_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) 4)
      (pow_nonneg hv 4)]

/-- For [a nonnegative scalar](hyp:ht), the second power is [bounded by its first plus
fourth powers](goal). -/
theorem sq_le_self_add_fourth (t : ℝ) (ht : 0 ≤ t) : t ^ 2 ≤ t + t ^ 4 := by
  by_cases h : t ≤ 1
  · have h2 : t ^ 2 ≤ t := by nlinarith
    nlinarith [sq_nonneg (t ^ 2)]
  · have h2 : 1 ≤ t ^ 2 := by nlinarith
    nlinarith [sq_nonneg (t ^ 2 - 1)]

/-- For [a nonnegative scalar](hyp:ht), the third power is [bounded by its first plus
fourth powers](goal). -/
theorem cube_le_self_add_fourth (t : ℝ) (ht : 0 ≤ t) : t ^ 3 ≤ t + t ^ 4 := by
  by_cases h : t ≤ 1
  · have h2 : t ^ 2 ≤ 1 := by nlinarith
    have := mul_nonneg ht (sub_nonneg.mpr h2)
    nlinarith [sq_nonneg (t ^ 2)]
  · have h3 : 0 ≤ t ^ 3 := pow_nonneg ht _
    have := mul_nonneg h3 (sub_nonneg.mpr (le_of_not_ge h))
    nlinarith

/-- For [a nonnegative scalar](hyp:ht), the loose counting polynomial is [bounded by
eight factorial times the sum of its first and fourth powers](goal). -/
theorem polynomial_le_factorial (t : ℝ) (ht : 0 ≤ t) :
    t + 128 * t ^ 2 + 1094 * t ^ 3 + 2731 * t ^ 4 ≤
      (Nat.factorial 8 : ℝ) * (t ^ 4 + t) := by
  have h2 := sq_le_self_add_fourth t ht
  have h3 := cube_le_self_add_fourth t ht
  norm_num [Nat.factorial] at *
  nlinarith [sq_nonneg (t ^ 2)]

/-- For [a nonnegative weight](hyp:hv), the weighted number of surviving patterns on
[a finite coordinate set](hyp:S) is [at most eight factorial times the sum of the first
and fourth powers of size times weight](goal). -/
theorem weighted_survivingPatterns_le (S : Finset α) (v : ℝ) (hv : 0 ≤ v) :
    (∑ a ∈ survivingPatterns S, v ^ (patternImage a).card) ≤
      (Nat.factorial 8 : ℝ) * (((S.card : ℝ) * v) ^ 4 + (S.card : ℝ) * v) := by
  exact (weighted_survivingPatterns_le_choose_sum S v hv).trans
    ((choose_sum_le_polynomial S.card v hv).trans
      (polynomial_le_factorial _ (mul_nonneg (Nat.cast_nonneg _) hv)))

end Causalean.Mathlib.Probability.IdentDistrib.EighthMoment
