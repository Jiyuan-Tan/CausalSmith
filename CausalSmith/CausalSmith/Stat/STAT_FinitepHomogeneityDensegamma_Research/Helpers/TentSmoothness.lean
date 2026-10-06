module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.FrameBounds
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PairedTent

/-! Lipschitz and Hölder bounds for the disjoint paired-tent construction. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The compact tent has global Lipschitz constant two. [This is the stated conclusion](goal). -/
-- @node: tentBase_abs_sub_le
lemma tentBase_abs_sub_le (x y : ℝ) : |tentBase x-tentBase y| ≤ 2*|x-y| := by
  rw [tentBase_eq_max_min, tentBase_eq_max_min]
  have hm := abs_min_sub_min_le_max x (1-x) y (1-y)
  have he : (1-x)-(1-y) = -(x-y) := by ring
  rw [he, abs_neg, max_self] at hm
  calc
    _ ≤ max |(0:ℝ)-0| |2*min x (1-x)-2*min y (1-y)| :=
      abs_max_sub_max_le_max _ _ _ _
    _ = 2*|min x (1-x)-min y (1-y)| := by
      rw [show 2*min x (1-x)-2*min y (1-y) = 2*(min x (1-x)-min y (1-y)) by ring]
      simp [abs_mul]
    _ ≤ _ := by gcongr

/-- Each signed paired bump is Lipschitz with constant four times the rank. [This is the stated conclusion](goal). -/
-- @node: paired_bump_abs_sub_le
lemma paired_bump_abs_sub_le (M : ℕ) (σ : Fin (M/2) → Bool)
    (j : Fin (M/2)) (x y : ℝ) :
    |signVal (σ j)*(tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*x-(2*j.val+1)))-
      signVal (σ j)*(tentBase ((M:ℝ)*y-2*j.val)-tentBase ((M:ℝ)*y-(2*j.val+1)))| ≤
      4*(M:ℝ)*|x-y| := by
  have h0 := tentBase_abs_sub_le ((M:ℝ)*x-2*j.val) ((M:ℝ)*y-2*j.val)
  have h1 := tentBase_abs_sub_le ((M:ℝ)*x-(2*j.val+1)) ((M:ℝ)*y-(2*j.val+1))
  have e0 : (M:ℝ)*x-2*j.val-((M:ℝ)*y-2*j.val) = (M:ℝ)*(x-y) := by ring
  have e1 : (M:ℝ)*x-(2*j.val+1)-((M:ℝ)*y-(2*j.val+1)) = (M:ℝ)*(x-y) := by ring
  rw [e0] at h0
  simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg M : (0:ℝ) ≤ M)] at h0
  rw [e1] at h1
  simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg M : (0:ℝ) ≤ M)] at h1
  have hs : |signVal (σ j)| = 1 := by cases σ j <;> norm_num [signVal]
  rw [← mul_sub, abs_mul, hs, one_mul]
  have ht := abs_sub
    (tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*y-2*j.val))
    (tentBase ((M:ℝ)*x-(2*j.val+1))-tentBase ((M:ℝ)*y-(2*j.val+1)))
  have e : tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*x-(2*j.val+1))-
      (tentBase ((M:ℝ)*y-2*j.val)-tentBase ((M:ℝ)*y-(2*j.val+1))) =
      (tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*y-2*j.val))-
      (tentBase ((M:ℝ)*x-(2*j.val+1))-tentBase ((M:ℝ)*y-(2*j.val+1))) := by ring
  rw [e]
  linarith

/-- Two nonzero paired bumps at the same point must have the same index. This statement assumes [the hj condition](hyp:hj), [the hk condition](hyp:hk). [This is the stated conclusion](goal). -/
-- @node: paired_bump_unique
lemma paired_bump_unique (M : ℕ) (x : ℝ) (j k : Fin (M/2))
    (hj : tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*x-(2*j.val+1)) ≠ 0)
    (hk : tentBase ((M:ℝ)*x-2*k.val)-tentBase ((M:ℝ)*x-(2*k.val+1)) ≠ 0) : j = k := by
  have hs := coarseTent_pair_support M x j hj
  have ht := coarseTent_pair_support M x k hk
  have h1 : (k.val:ℝ) < j.val+1 := by linarith
  have h2 : (j.val:ℝ) < k.val+1 := by linarith
  have h1' : k.val < j.val+1 := by exact_mod_cast h1
  have h2' : j.val < k.val+1 := by exact_mod_cast h2
  apply Fin.ext
  omega

/-- Disjoint support keeps the Lipschitz bound independent of the number of pairs. [This is the stated conclusion](goal). -/
-- @node: coarseTent_abs_sub_le
lemma coarseTent_abs_sub_le (M : ℕ) (σ : Fin (M/2) → Bool) (x y : ℝ) :
    |coarseTent M σ x-coarseTent M σ y| ≤ 8*(M:ℝ)*|x-y| := by
  classical
  let f := fun (z : ℝ) (j : Fin (M/2)) => signVal (σ j)*
    (tentBase ((M:ℝ)*z-2*j.val)-tentBase ((M:ℝ)*z-(2*j.val+1)))
  let S := fun z => Finset.univ.filter (fun j => f z j ≠ 0)
  have hc (z : ℝ) : (S z).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    have hj' : f z j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hk' : f z k ≠ 0 := (Finset.mem_filter.mp hk).2
    apply paired_bump_unique M z j k
    · intro h; apply hj'; simp [f, h]
    · intro h; apply hk'; simp [f, h]
  have hs : (S x ∪ S y).card ≤ 2 :=
    (Finset.card_union_le _ _).trans (by linarith [hc x, hc y])
  have he : coarseTent M σ x-coarseTent M σ y =
      ∑ j ∈ S x ∪ S y, (f x j-f y j) := by
    unfold coarseTent
    rw [← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hx : f x j = 0 := by
      by_contra h
      exact hj (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    have hy : f y j = 0 := by
      by_contra h
      exact hj (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    change f x j-f y j = 0
    rw [hx, hy, sub_self]
  rw [he]
  calc
    _ ≤ ∑ j ∈ S x ∪ S y, |f x j-f y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ S x ∪ S y, 4*(M:ℝ)*|x-y| := by
      apply Finset.sum_le_sum
      intro j _
      exact paired_bump_abs_sub_le M σ j x y
    _ = ((S x ∪ S y).card:ℝ)*(4*(M:ℝ)*|x-y|) := by simp
    _ ≤ 2*(4*(M:ℝ)*|x-y|) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hs)
      positivity
    _ = _ := by ring

/-- Combining the Lipschitz and unit envelopes gives the rank-scaled Hölder bound. This statement assumes [the hM condition](hyp:hM), [the hs condition](hyp:hs), [the hs1 condition](hyp:hs1). [This is the stated conclusion](goal). -/
-- @node: coarseTent_scaled_holder
lemma coarseTent_scaled_holder (M : ℕ) (hM : 0 < M) (σ : Fin (M/2) → Bool)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (x y : ℝ) :
    (M:ℝ)⁻¹^s*|coarseTent M σ x-coarseTent M σ y| ≤ 8*|x-y|^s := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have ht : 0 ≤ (M:ℝ)*|x-y| := by positivity
  have hb : |coarseTent M σ x-coarseTent M σ y| ≤
      8*((M:ℝ)*|x-y|)^s := by
    by_cases hsmall : (M:ℝ)*|x-y| ≤ 1
    · have hr := Real.self_le_rpow_of_le_one ht hsmall hs1
      have hl := coarseTent_abs_sub_le M σ x y
      nlinarith
    · have hr := Real.one_le_rpow (le_of_not_ge hsmall) hs
      have hl := abs_sub (coarseTent M σ x) (coarseTent M σ y)
      have hx := coarseTent_abs_le_one M σ x
      have hy := coarseTent_abs_le_one M σ y
      linarith
  calc
    _ ≤ (M:ℝ)⁻¹^s*(8*((M:ℝ)*|x-y|)^s) := by gcongr
    _ = 8*((M:ℝ)⁻¹*((M:ℝ)*|x-y|))^s := by
      rw [Real.mul_rpow (inv_nonneg.mpr hMr.le) ht]
      ring
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hMr.ne', one_mul]

/-- The prescribed paired effect belongs to the required Hölder ball. This statement assumes [the hv condition](hyp:hv), [the hN condition](hyp:hN), [the hh condition](hyp:hh). [This is the stated conclusion](goal). -/
-- @node: tentEffect_holderBall
lemma tentEffect_holderBall (n : ℕ) (v : Params) (hv : v.Valid)
    (hN : 0 < tentRank n v) (hh : tentH n v ≤ 1)
    (σ : Fin (tentRank n v/2) → Bool) : holderBall v.γ (tentEffect n v σ) := by
  have hg : 0 ≤ v.γ := by linarith [hv.2.2.2.1]
  have hγ : v.γ ≤ 1 := hv.2.2.2.2
  have hh0 : 0 ≤ tentH n v := by unfold tentH; positivity
  have ha : 0 ≤ tentH n v^v.γ := Real.rpow_nonneg hh0 _
  refine ⟨continuous_tentEffect n v σ, ?_, ?_⟩
  · intro x
    rw [tentEffect, abs_mul, abs_mul, abs_of_nonneg (by norm_num [kappa0] : 0 ≤ kappa0),
      abs_of_nonneg ha]
    have hb := coarseTent_abs_le_one (tentRank n v) σ x
    have hp := Real.rpow_le_one hh0 hh hg
    calc
      _ ≤ kappa0*1*1 := by gcongr <;> norm_num [kappa0]
      _ ≤ 20 := by norm_num [kappa0]
  · intro x y
    have hb := coarseTent_scaled_holder (tentRank n v) hN σ v.γ hg hγ x y
    rw [show tentEffect n v σ x-tentEffect n v σ y =
      kappa0*(tentH n v^v.γ*(coarseTent (tentRank n v) σ x-coarseTent (tentRank n v) σ y)) by
        unfold tentEffect; ring, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num [kappa0] : 0 ≤ kappa0), abs_of_nonneg ha]
    calc
      _ ≤ kappa0*(8*|(x:ℝ)-(y:ℝ)|^v.γ) := by
        apply mul_le_mul_of_nonneg_left hb
        norm_num [kappa0]
      _ ≤ 20*|(x:ℝ)-(y:ℝ)|^v.γ := by
        have hp : 0 ≤ |(x:ℝ)-(y:ℝ)|^v.γ := Real.rpow_nonneg (abs_nonneg _) _
        norm_num [kappa0]
        nlinarith

end CausalSmith.Stat.FinitepHomogeneityDensegamma
