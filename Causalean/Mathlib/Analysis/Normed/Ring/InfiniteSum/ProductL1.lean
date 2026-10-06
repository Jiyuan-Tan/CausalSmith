module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# L1 bounds for normalized product series

Normalized nonnegative series retain unit mass under finite products, with tensorized L1 bounds.
-/

public section

namespace Causalean.Mathlib.Analysis.Normed.Ring.InfiniteSum

/-- For [two summable nonnegative real series](hyp:a,b,ha,hb,ha0,hb0), the
pointwise absolute difference is summable. The result is [summability of the pointwise absolute difference](goal). -/
lemma normalized_likelihood_abs_gap_summable {A : Type*} (a b : A → ℝ)
    (ha : Summable a) (hb : Summable b)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x) :
    Summable (fun x => |a x - b x|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ (ha.add hb)
  intro x
  calc
    |a x - b x| ≤ |a x| + |b x| := by simpa using abs_sub_le (a x) 0 (b x)
    _ = a x + b x := by rw [abs_of_nonneg (ha0 x), abs_of_nonneg (hb0 x)]

/-- For [two pairs of normalized nonnegative real series](hyp:a₀,a₁,b₀,b₁,ha₀,ha₁,hb₀,hb₁,ha₀0,ha₁0,hb₀0,hb₁0),
the `ℓ¹` gap between their binary products is at most the sum of the two
marginal gaps. The result is [the binary-product `ℓ¹` gap bound by the two marginal gaps](goal). -/
lemma normalized_likelihood_tensor_gap_le {A B : Type*}
    (a₀ a₁ : A → ℝ) (b₀ b₁ : B → ℝ)
    (ha₀ : HasSum a₀ 1) (ha₁ : HasSum a₁ 1)
    (hb₀ : HasSum b₀ 1) (hb₁ : HasSum b₁ 1)
    (ha₀0 : ∀ x, 0 ≤ a₀ x) (ha₁0 : ∀ x, 0 ≤ a₁ x)
    (hb₀0 : ∀ y, 0 ≤ b₀ y) (hb₁0 : ∀ y, 0 ≤ b₁ y) :
    (∑' z : A × B, |a₀ z.1 * b₀ z.2 - a₁ z.1 * b₁ z.2|) ≤
      (∑' x, |a₀ x - a₁ x|) + ∑' y, |b₀ y - b₁ y| := by
  have hga := normalized_likelihood_abs_gap_summable a₀ a₁
    ha₀.summable ha₁.summable ha₀0 ha₁0
  have hgb := normalized_likelihood_abs_gap_summable b₀ b₁
    hb₀.summable hb₁.summable hb₀0 hb₁0
  have he₀ := hga.mul_of_nonneg hb₁.summable (fun _ => abs_nonneg _) hb₁0
  have he₁ := ha₀.summable.mul_of_nonneg hgb ha₀0 (fun _ => abs_nonneg _)
  have hpoint (z : A × B) :
      |a₀ z.1 * b₀ z.2 - a₁ z.1 * b₁ z.2| ≤
        |a₀ z.1 - a₁ z.1| * b₁ z.2 + a₀ z.1 * |b₀ z.2 - b₁ z.2| := by
    calc
      _ = |(a₀ z.1 - a₁ z.1) * b₁ z.2 + a₀ z.1 * (b₀ z.2 - b₁ z.2)| := by ring_nf
      _ ≤ |(a₀ z.1 - a₁ z.1) * b₁ z.2| + |a₀ z.1 * (b₀ z.2 - b₁ z.2)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (hb₁0 _), abs_of_nonneg (ha₀0 _)]
  have hg := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpoint (he₀.add he₁)
  calc
    _ ≤ ∑' z : A × B,
        (|a₀ z.1 - a₁ z.1| * b₁ z.2 + a₀ z.1 * |b₀ z.2 - b₁ z.2|) :=
      hg.tsum_le_tsum hpoint (he₀.add he₁)
    _ = _ := by
      rw [he₀.tsum_add he₁, ← hga.tsum_mul_tsum hb₁.summable he₀,
        ← ha₀.summable.tsum_mul_tsum hgb he₁, hb₁.tsum_eq, ha₀.tsum_eq,
        mul_one, one_mul]

/-- For a [finite number of nonnegative factor series](hyp:m,a,ha0), each of
which [sums to one](hyp:ha), the product series over coordinate assignments also
sums to one. The result is [normalization of the finite product series](goal). -/
lemma normalized_likelihood_fin_product_hasSum_one {A : Type*} (m : ℕ)
    (a : Fin m → A → ℝ) (ha : ∀ j, HasSum (a j) 1)
    (ha0 : ∀ j x, 0 ≤ a j x) :
    HasSum (fun x : Fin m → A => ∏ j : Fin m, a j (x j)) 1 := by
  induction m with
  | zero =>
      simpa using (hasSum_fintype (fun _ : Fin 0 → A => (1 : ℝ)))
  | succ m ih =>
      let b : (Fin m → A) → ℝ := fun x => ∏ j : Fin m, a j.succ (x j)
      have hb : HasSum b 1 := ih (fun j => a j.succ) (fun j => ha j.succ)
        (fun j x => ha0 j.succ x)
      have hb0 : ∀ x, 0 ≤ b x := fun x => Finset.prod_nonneg (fun j _ => ha0 j.succ (x j))
      have hp := (ha 0).mul hb
        ((ha 0).summable.mul_of_nonneg hb.summable (ha0 0) hb0)
      have hfn : (fun z : A × (Fin m → A) => a 0 z.1 * b z.2) =
          (fun x : Fin (m + 1) → A => ∏ j : Fin (m + 1), a j (x j)) ∘
            (Fin.consEquiv (fun _ : Fin (m + 1) => A)) := by
        funext z
        simp [Fin.prod_univ_succ, Fin.consEquiv, b, Function.comp_def]
      rw [hfn] at hp
      exact (Fin.consEquiv (fun _ : Fin (m + 1) => A)).hasSum_iff.mp
        (by simpa only [one_mul] using hp)

/-- For [two finite families of nonnegative factor series](hyp:m,a,b,ha0,hb0),
each [normalized to sum to one](hyp:ha,hb), the `ℓ¹` gap between the product
series is at most the sum of their marginal `ℓ¹` gaps. The result is [the finite-product `ℓ¹` gap bound by the sum of marginal gaps](goal). -/
lemma normalized_likelihood_fin_product_l1_le {A : Type*} (m : ℕ)
    (a b : Fin m → A → ℝ) (ha : ∀ j, HasSum (a j) 1)
    (hb : ∀ j, HasSum (b j) 1)
    (ha0 : ∀ j x, 0 ≤ a j x) (hb0 : ∀ j x, 0 ≤ b j x) :
    (∑' x : Fin m → A,
      |(∏ j : Fin m, a j (x j)) - ∏ j : Fin m, b j (x j)|) ≤
      ∑ j : Fin m, ∑' x : A, |a j x - b j x| := by
  induction m with
  | zero => simp
  | succ m ih =>
      let aTail : (Fin m → A) → ℝ := fun x => ∏ j : Fin m, a j.succ (x j)
      let bTail : (Fin m → A) → ℝ := fun x => ∏ j : Fin m, b j.succ (x j)
      have haTail := normalized_likelihood_fin_product_hasSum_one m
        (fun j => a j.succ) (fun j => ha j.succ) (fun j x => ha0 j.succ x)
      have hbTail := normalized_likelihood_fin_product_hasSum_one m
        (fun j => b j.succ) (fun j => hb j.succ) (fun j x => hb0 j.succ x)
      have haTail0 : ∀ x, 0 ≤ aTail x := fun x => Finset.prod_nonneg (fun j _ => ha0 j.succ (x j))
      have hbTail0 : ∀ x, 0 ≤ bTail x := fun x => Finset.prod_nonneg (fun j _ => hb0 j.succ (x j))
      have hbin := normalized_likelihood_tensor_gap_le (a 0) (b 0) aTail bTail
        (ha 0) (hb 0) haTail hbTail (ha0 0) (hb0 0) haTail0 hbTail0
      have hrec := ih (fun j => a j.succ) (fun j => b j.succ)
        (fun j => ha j.succ) (fun j => hb j.succ)
        (fun j x => ha0 j.succ x) (fun j x => hb0 j.succ x)
      calc
        _ = ∑' z : A × (Fin m → A),
            |a 0 z.1 * aTail z.2 - b 0 z.1 * bTail z.2| := by
          rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => A)).tsum_eq]
          apply tsum_congr
          intro z
          simp [Fin.prod_univ_succ, Fin.consEquiv, aTail, bTail]
        _ ≤ (∑' x : A, |a 0 x - b 0 x|) +
            ∑' x : Fin m → A, |aTail x - bTail x| := hbin
        _ ≤ (∑' x : A, |a 0 x - b 0 x|) +
            ∑ j : Fin m, ∑' x : A, |a j.succ x - b j.succ x| :=
          add_le_add le_rfl hrec
        _ = _ := (Fin.sum_univ_succ (fun j => ∑' x : A, |a j x - b j x|)).symm



end Causalean.Mathlib.Analysis.Normed.Ring.InfiniteSum
