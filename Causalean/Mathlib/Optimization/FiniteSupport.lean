module
public import Mathlib

/-! # Sparse finite linear-program maximizers

This module proves the finite basic-feasible-solution sparsity principle for a
nonnegative real linear program with equality moments. It preserves any one
additional scalar moment without treating the objective as an extra independent
constraint, and it works with repeated indexed coefficient columns.
-/

@[expose] public section

noncomputable section

namespace Causalean.Mathlib.Optimization

variable {ι : Type*} [Fintype ι]

/-- The [indexed support](goal) of a [finite real weight vector](hyp:x) consists
of exactly the coordinates carrying nonzero weights. -/
def weightSupport (x : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => x i ≠ 0)

/-- The [scalar moment](goal) of a [coefficient vector](hyp:a) against a
[finite real weight vector](hyp:x) is their finite coordinate pairing. -/
def moment (a x : ι → ℝ) : ℝ := ∑ i, a i * x i

/-- A [nonnegative finite weight vector](hyp:x,hxnonneg) and a [nonzero
direction](hyp:d,hdnonzero) that [vanishes outside its nonzero coordinates](hyp:hsupp)
have [a nonnegative boundary perturbation with strictly smaller indexed support](goal).
No assumption on the signs of the direction is needed. -/
theorem exists_boundary_perturbation {ι : Type*} [Fintype ι]
    (x d : ι → ℝ) (hxnonneg : ∀ i, 0 ≤ x i)
    (hdnonzero : d ≠ 0) (hsupp : ∀ i, x i = 0 → d i = 0) :
    ∃ t : ℝ, (∀ i, 0 ≤ x i + t * d i) ∧
      (weightSupport (fun i => x i + t * d i)).card < (weightSupport x).card := by
  classical
  have move (v : ι → ℝ) (hv : ∃ i, 0 < v i)
      (hvsupp : ∀ i, x i = 0 → v i = 0) :
      ∃ r : ℝ, (∀ i, 0 ≤ x i - r * v i) ∧
        (weightSupport (fun i => x i - r * v i)).card < (weightSupport x).card := by
    let s : Finset ι := Finset.univ.filter (fun i => 0 < v i)
    have hs : s.Nonempty := by
      obtain ⟨i, hi⟩ := hv
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    obtain ⟨j, hj, hmin⟩ := s.exists_min_image (fun i => x i / v i) hs
    have hvj : 0 < v j := (Finset.mem_filter.mp hj).2
    let r := x j / v j
    have hr : 0 ≤ r := div_nonneg (hxnonneg j) (le_of_lt hvj)
    have hnonneg : ∀ i, 0 ≤ x i - r * v i := by
      intro i
      by_cases hvi : 0 < v i
      · have hle : r ≤ x i / v i := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvi⟩)
        have hmul : r * v i ≤ x i := (le_div_iff₀ hvi).mp hle
        linarith
      · have hvi' : v i ≤ 0 := le_of_not_gt hvi
        have hprod : r * v i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr hvi'
        linarith [hxnonneg i]
    have hz : x j - r * v j = 0 := by
      dsimp [r]
      field_simp
      ring
    have hjx : j ∈ weightSupport x := by
      simp only [weightSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hxj
      exact (not_lt_of_ge (hvsupp j hxj).le) hvj
    have hjnew : j ∉ weightSupport (fun i => x i - r * v i) := by
      simp [weightSupport, hz]
    have hsub : weightSupport (fun i => x i - r * v i) ⊆ weightSupport x := by
      intro i hi
      simp only [weightSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      intro hxi
      simp [hxi, hvsupp i hxi] at hi
    refine ⟨r, hnonneg, Finset.card_lt_card ?_⟩
    exact (Finset.ssubset_iff_of_subset hsub).2 ⟨j, hjx, hjnew⟩
  have ⟨i₀, hi₀⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hdnonzero
    funext i
    exact h i
  by_cases hpos : 0 < d i₀
  · obtain ⟨r, hr, hc⟩ := move d ⟨i₀, hpos⟩ hsupp
    refine ⟨-r, ?_, ?_⟩
    · intro i
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hr i
    · convert hc using 1
      congr 2
      ext i
      ring
  · have hneg : d i₀ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hi₀
    obtain ⟨r, hr, hc⟩ := move (fun i => -d i) ⟨i₀, by simpa using hneg⟩
      (by intro i hi; simp [hsupp i hi])
    refine ⟨r, ?_, ?_⟩
    · intro i
      convert hr i using 1
      ring
    · convert hc using 1
      congr 2
      ext i
      ring

/-- Given [base moment coefficients](hyp:A), an [additional scalar coefficient](hyp:g),
and a [finite real weight vector](hyp:x) whose [indexed support exceeds the number of
base moments plus one](hyp:hlarge), there is [a nonzero direction supported on that
support whose base and additional moments all vanish](goal). The coefficient columns may
repeat or be linearly dependent. -/
theorem exists_kernel_direction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℝ) (g : ι → ℝ) (x : ι → ℝ)
    (hlarge : Fintype.card κ + 1 < (weightSupport x).card) :
    ∃ d : ι → ℝ, d ≠ 0 ∧
      (∀ i, x i = 0 → d i = 0) ∧
      (∀ k, moment (A k) d = 0) ∧ moment g d = 0 := by
  classical
  let S := weightSupport x
  let L : (S → ℝ) →ₗ[ℝ] ((κ ⊕ Unit) → ℝ) :=
    { toFun := fun v t => ∑ i : S, (Sum.elim A (fun _ => g) t) i.1 * v i
      map_add' := by
        intro u v
        ext t
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        ext t
        simp [smul_eq_mul, Finset.mul_sum, mul_left_comm] }
  have hdim : Module.finrank ℝ ((κ ⊕ Unit) → ℝ) < Module.finrank ℝ (S → ℝ) := by
    simpa [S, Fintype.card_sum] using hlarge
  obtain ⟨v, hv, hvne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt hdim :
      LinearMap.ker L ≠ ⊥)
  let d : ι → ℝ := fun i => if h : i ∈ S then v ⟨i, h⟩ else 0
  have hsum (a : ι → ℝ) : moment a d = ∑ i : S, a i.1 * v i := by
    simp only [moment]
    calc
      (∑ i : ι, a i * d i) = ∑ i ∈ S, a i * d i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i hi hiS
        simp [d, hiS]
      _ = ∑ i : S, a i.1 * v i := by
        rw [← Finset.sum_attach]
        simp [d, Finset.univ_eq_attach]
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · intro hd
    apply hvne
    funext i
    have hi : d i.1 = v i := by simp [d, i.2]
    rw [hd] at hi
    exact hi.symm
  · intro i hxi
    have hi : i ∉ S := by simp [S, weightSupport, hxi]
    simp [d, hi]
  · intro k
    have hk := congrFun (show L v = 0 from hv) (Sum.inl k)
    simpa [L, hsum] using hk
  · have hg := congrFun (show L v = 0 from hv) (Sum.inr ())
    simpa [L, hsum] using hg

/-- Given [base moment coefficients](hyp:A), [prescribed base moments](hyp:b), an
[objective coefficient](hyp:c), a [nonnegative base-feasible vector](hyp:x,hxnonneg,hxmoment)
that [globally maximizes the objective among such vectors](hyp:hmax), and a
[supported base-moment-kernel direction](hyp:d,hsupp,hkernel), the [objective moment
of that direction is zero](goal). -/
theorem objective_orthogonal_of_maximal {ι κ : Type*} [Fintype ι]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c x d : ι → ℝ)
    (hxnonneg : ∀ i, 0 ≤ x i)
    (hxmoment : ∀ k, moment (A k) x = b k)
    (hmax : ∀ z : ι → ℝ, (∀ i, 0 ≤ z i) →
      (∀ k, moment (A k) z = b k) → moment c z ≤ moment c x)
    (hsupp : ∀ i, x i = 0 → d i = 0)
    (hkernel : ∀ k, moment (A k) d = 0) :
    moment c d = 0 := by
  classical
  have hcoordinate (i : ι) : ∃ r : ℝ, 0 < r ∧ r * |d i| ≤ x i := by
    by_cases hx : x i = 0
    · refine ⟨1, by norm_num, ?_⟩
      simp [hsupp i hx, hx]
    · have hxpos : 0 < x i := lt_of_le_of_ne (hxnonneg i) (Ne.symm hx)
      refine ⟨x i / (|d i| + 1), by positivity, ?_⟩
      have hden : 0 < |d i| + 1 := by positivity
      have heq : (x i / (|d i| + 1)) * (|d i| + 1) = x i :=
        div_mul_cancel₀ (x i) (ne_of_gt hden)
      nlinarith [abs_nonneg (d i)]
  have hfinite (s : Finset ι) :
      ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, r * |d i| ≤ x i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨r, hr, hbound⟩ := ih
      obtain ⟨t, ht, htbound⟩ := hcoordinate i
      refine ⟨min r t, lt_min hr ht, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (mul_le_mul_of_nonneg_right (min_le_right r t) (abs_nonneg _)).trans htbound
      · exact (mul_le_mul_of_nonneg_right (min_le_left r t) (abs_nonneg _)).trans
          (hbound j hj)
  obtain ⟨ε, hε, hεbound⟩ := hfinite Finset.univ
  have hplus_nonneg (i : ι) : 0 ≤ x i + ε * d i := by
    have hb := hεbound i (Finset.mem_univ i)
    have hd : 0 ≤ ε * (|d i| + d i) :=
      mul_nonneg hε.le (by linarith [neg_le_abs (d i)])
    nlinarith
  have hminus_nonneg (i : ι) : 0 ≤ x i - ε * d i := by
    have hb := hεbound i (Finset.mem_univ i)
    have hd : 0 ≤ ε * (|d i| - d i) :=
      mul_nonneg hε.le (sub_nonneg.mpr (le_abs_self (d i)))
    nlinarith
  have hplus (a : ι → ℝ) :
      moment a (fun i => x i + ε * d i) = moment a x + ε * moment a d := by
    simp only [moment, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hminus (a : ι → ℝ) :
      moment a (fun i => x i - ε * d i) = moment a x - ε * moment a d := by
    simp only [moment, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hp := hmax (fun i => x i + ε * d i) hplus_nonneg (by
    intro k
    rw [hplus, hkernel k, mul_zero, add_zero]
    exact hxmoment k)
  have hm := hmax (fun i => x i - ε * d i) hminus_nonneg (by
    intro k
    rw [hminus, hkernel k, mul_zero, sub_zero]
    exact hxmoment k)
  rw [hplus] at hp
  rw [hminus] at hm
  nlinarith

/-- Given [base moment coefficients](hyp:A), [prescribed base moments](hyp:b), an
[additional scalar coefficient](hyp:g), an [objective coefficient](hyp:c), and an
[initial nonnegative globally maximizing feasible vector](hyp:x,hxnonneg,hxmoment,hmax),
there is [a nonnegative global maximizer with the same base, additional, and objective
moments and at most one more nonzero coordinate than the number of base moments](goal).
Repeated indexed coefficient columns are allowed. -/
theorem exists_sparse_maximizer {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℝ) (b : κ → ℝ) (g c x : ι → ℝ)
    (hxnonneg : ∀ i, 0 ≤ x i)
    (hxmoment : ∀ k, moment (A k) x = b k)
    (hmax : ∀ z : ι → ℝ, (∀ i, 0 ≤ z i) →
      (∀ k, moment (A k) z = b k) → moment c z ≤ moment c x) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧
      (∀ k, moment (A k) y = b k) ∧
      moment g y = moment g x ∧
      moment c y = moment c x ∧
      (weightSupport y).card ≤ Fintype.card κ + 1 ∧
      (∀ z : ι → ℝ, (∀ i, 0 ≤ z i) →
        (∀ k, moment (A k) z = b k) → moment c z ≤ moment c y) := by
  classical
  let P : ℕ → Prop := fun n => ∃ y : ι → ℝ,
    (∀ i, 0 ≤ y i) ∧ (∀ k, moment (A k) y = b k) ∧
    moment g y = moment g x ∧ moment c y = moment c x ∧
    (weightSupport y).card = n
  have hex : ∃ n, P n := by
    refine ⟨(weightSupport x).card, x, hxnonneg, hxmoment, rfl, rfl, rfl⟩
  obtain ⟨y, hynonneg, hymoment, hyg, hyc, hycard⟩ := Nat.find_spec hex
  have hymax : ∀ z : ι → ℝ, (∀ i, 0 ≤ z i) →
      (∀ k, moment (A k) z = b k) → moment c z ≤ moment c y := by
    intro z hznonneg hzmoment
    rw [hyc]
    exact hmax z hznonneg hzmoment
  have hmin (z : ι → ℝ) (hznonneg : ∀ i, 0 ≤ z i)
      (hzmoment : ∀ k, moment (A k) z = b k)
      (hzg : moment g z = moment g x)
      (hzc : moment c z = moment c x) :
      (weightSupport y).card ≤ (weightSupport z).card := by
    rw [hycard]
    exact Nat.find_min' hex ⟨z, hznonneg, hzmoment, hzg, hzc, rfl⟩
  have hcard : (weightSupport y).card ≤ Fintype.card κ + 1 := by
    by_contra h
    have hlarge : Fintype.card κ + 1 < (weightSupport y).card := by omega
    obtain ⟨d, hdne, hdsupp, hdA, hdg⟩ := exists_kernel_direction A g y hlarge
    have hdc : moment c d = 0 :=
      objective_orthogonal_of_maximal A b c y d hynonneg hymoment hymax hdsupp hdA
    obtain ⟨t, hnonneg, hlt⟩ :=
      exists_boundary_perturbation y d hynonneg hdne hdsupp
    let z : ι → ℝ := fun i => y i + t * d i
    have hmoment (a : ι → ℝ) :
        moment a z = moment a y + t * moment a d := by
      simp only [moment, z, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hzA : ∀ k, moment (A k) z = b k := by
      intro k
      rw [hmoment, hdA k, mul_zero, add_zero]
      exact hymoment k
    have hzg : moment g z = moment g x := by
      rw [hmoment, hdg, mul_zero, add_zero]
      exact hyg
    have hzc : moment c z = moment c x := by
      rw [hmoment, hdc, mul_zero, add_zero]
      exact hyc
    have hle := hmin z hnonneg hzA hzg hzc
    exact (not_lt_of_ge hle) hlt
  exact ⟨y, hynonneg, hymoment, hyg, hyc, hcard, hymax⟩

end Causalean.Mathlib.Optimization
