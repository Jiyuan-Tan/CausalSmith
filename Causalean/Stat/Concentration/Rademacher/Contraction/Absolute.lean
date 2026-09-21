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
public import Causalean.Stat.Concentration.Rademacher.Contraction.Signed

/-! # Absolute Rademacher contraction

Starting from the signed finite-index contraction theorem, this file derives
the standard factor-two absolute-value contraction bound. It also supplies
scaling and subtraction rules for empirical Rademacher complexity and the
arbitrary-index contraction theorem under boundedness of the relevant
suprema. -/

@[expose] public section

namespace Causalean
namespace Stat
namespace Concentration

section Contraction

variable {ι 𝒳 : Type*}


private def withZero (F : ι → 𝒳 → ℝ) : Option ι → 𝒳 → ℝ
  | none, _ => 0
  | some i, x => F i x

/-- Negating a function that fixes zero preserves the same Lipschitz
constant. -/
lemma lipschitzAt0_neg (φ : ℝ → ℝ) {L : ℝ} (hφ : LipschitzAt0 φ L) :
    LipschitzAt0 (fun x => -φ x) L := by
  refine ⟨by simp [hφ.1], ?_⟩
  intro x y
  rw [show -φ x - -φ y = -(φ x - φ y) from by ring, abs_neg]
  exact hφ.2 x y

/-- If a finite collection of real numbers includes zero, its largest absolute value is at most
the sum of its largest value and the largest value after negation. -/
lemma iSup_abs_le_iSup_add_iSup_neg_of_exists_zero
    {α : Type*} [Finite α] (x : α → ℝ) (h0 : ∃ a : α, x a = 0) :
    (⨆ a, |x a|) ≤ (⨆ a, x a) + (⨆ a, -x a) := by
  classical
  letI := Fintype.ofFinite α
  rcases h0 with ⟨a0, ha0⟩
  letI : Nonempty α := ⟨a0⟩
  have hsup_nonneg : 0 ≤ ⨆ a, x a := by
    rw [← ha0]
    exact le_ciSup (Finite.bddAbove_range x) a0
  have hsup_neg_nonneg : 0 ≤ ⨆ a, -x a := by
    rw [← show -x a0 = 0 by rw [ha0]; simp]
    exact le_ciSup (Finite.bddAbove_range fun a => -x a) a0
  refine ciSup_le ?_
  intro a
  by_cases hx : 0 ≤ x a
  · rw [abs_of_nonneg hx]
    have hxle : x a ≤ ⨆ a, x a := le_ciSup (Finite.bddAbove_range x) a
    linarith
  · have hxle : -x a ≤ ⨆ a, -x a := le_ciSup (Finite.bddAbove_range fun a => -x a) a
    rw [abs_of_neg (lt_of_not_ge hx)]
    linarith

private lemma empirical_abs_withZero_eq
    [Nonempty ι] [Finite ι]
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (withZero F) S
      = empiricalRademacherComplexity n F S := by
  classical
  letI := Fintype.ofFinite ι
  unfold empiricalRademacherComplexity
  congr 1
  refine Finset.sum_congr rfl ?_
  intro σ _
  apply le_antisymm
  · refine ciSup_le ?_
    intro o
    cases o with
    | none =>
        simp only [Int.reduceNeg, withZero, mul_zero, Finset.sum_const_zero, abs_zero, abs_mul,
          abs_inv, Nat.abs_cast]
        let i0 : ι := Classical.choice inferInstance
        exact le_trans
          (mul_nonneg (by positivity)
            (abs_nonneg (∑ k : Fin n, (σ k : ℝ) * F i0 (S k))))
          (le_ciSup (Finite.bddAbove_range
            (fun i : ι => (n : ℝ)⁻¹ * |∑ k : Fin n, (σ k : ℝ) * F i (S k)|)) i0)
    | some i =>
        exact le_ciSup (Finite.bddAbove_range
          (fun i : ι => |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)|)) i
  · refine ciSup_le ?_
    intro i
    exact le_ciSup (Finite.bddAbove_range
      (fun o : Option ι =>
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * withZero F o (S k)|)) (some i)

private lemma empirical_without_abs_withZero_le_abs
    [Nonempty ι] [Finite ι]
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n (withZero F) S
      ≤ empiricalRademacherComplexity n F S := by
  classical
  letI := Fintype.ofFinite ι
  unfold empiricalRademacherComplexity_without_abs empiricalRademacherComplexity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum ?_
  intro σ _
  refine ciSup_le ?_
  intro o
  cases o with
  | none =>
      simp only [Int.reduceNeg, withZero, mul_zero, Finset.sum_const_zero, abs_mul, abs_inv,
        Nat.abs_cast]
      let i0 : ι := Classical.choice inferInstance
      exact le_trans
        (mul_nonneg (by positivity)
          (abs_nonneg (∑ k : Fin n, (σ k : ℝ) * F i0 (S k))))
        (le_ciSup (Finite.bddAbove_range
          (fun i : ι => (n : ℝ)⁻¹ * |∑ k : Fin n, (σ k : ℝ) * F i (S k)|)) i0)
  | some i =>
      exact le_trans (le_abs_self _)
        (le_ciSup (Finite.bddAbove_range
          (fun i : ι => |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)|)) i)

/-- If a function class contains the zero function, its empirical Rademacher complexity with
absolute values is bounded by the sum of the corresponding unsigned complexities for the class
and its negation. -/
lemma empirical_abs_withZero_le_no_abs_plus_neg
    [Finite ι]
    (F : Option ι → 𝒳 → ℝ) (hzero : ∀ x, F none x = 0)
    (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n F S
      ≤ empiricalRademacherComplexity_without_abs n F S
          + empiricalRademacherComplexity_without_abs n (fun i x => -F i x) S := by
  classical
  letI := Fintype.ofFinite ι
  unfold empiricalRademacherComplexity empiricalRademacherComplexity_without_abs
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro σ _
  have hzero_inner :
      (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F none (S k) = 0 := by
    simp [hzero]
  have hpoint :=
    iSup_abs_le_iSup_add_iSup_neg_of_exists_zero
      (fun i : Option ι =>
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k))
      ⟨none, hzero_inner⟩
  have hneg :
      (⨆ i : Option ι,
          -((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)))
        =
      (⨆ i : Option ι,
          (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (-F i (S k))) := by
    refine iSup_congr fun i => ?_
    calc
      -((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k))
          =
        (n : ℝ)⁻¹ * (-(∑ k : Fin n, (σ k : ℝ) * F i (S k))) := by
          ring
      _ =
        (n : ℝ)⁻¹ * (∑ k : Fin n, -((σ k : ℝ) * F i (S k))) := by
          rw [Finset.sum_neg_distrib]
      _ =
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (-F i (S k)) := by
          congr 1
          refine Finset.sum_congr rfl fun k _ => by ring
  simpa [hneg] using hpoint

/-- **Contraction principle, absolute-value form.** If [`φ` fixes `0` and is `L`-Lipschitz, i.e.
    `φ 0 = 0` and `|φ x - φ y| ≤ L * |x - y|` for all `x, y`](hyp:hφ), then [composing each
    function of the family `F` with `φ` multiplies the (absolute-value) empirical Rademacher
    complexity on the sample `S` by at most `2 * L`](goal).

    The proof reduces to `rademacher_contraction` applied to `φ` and `-φ`. -/
theorem rademacher_contraction_abs
    [Nonempty ι] [Finite ι]
    (φ : ℝ → ℝ) {L : ℝ} (hφ : LipschitzAt0 φ L)
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n
        (fun i x => φ (F i x)) S
      ≤ 2 * L * empiricalRademacherComplexity n F S := by
  classical
  letI := Fintype.ofFinite ι
  have hL : 0 ≤ L := by
    have h := hφ.2 0 1
    norm_num [hφ.1] at h
    exact (abs_nonneg _).trans h
  let F0 : Option ι → 𝒳 → ℝ := withZero F
  let G0 : Option ι → 𝒳 → ℝ := fun i x => φ (F0 i x)
  have hG0_zero : ∀ x, G0 none x = 0 := by
    intro x
    simp [G0, F0, withZero, hφ.1]
  have hG0_eq : G0 = withZero (fun i x => φ (F i x)) := by
    funext o x
    cases o with
    | none =>
        simp [G0, F0, withZero, hφ.1]
    | some i =>
        simp [G0, F0, withZero]
  have h_abs_split :
      empiricalRademacherComplexity n G0 S
        ≤ empiricalRademacherComplexity_without_abs n G0 S
            + empiricalRademacherComplexity_without_abs n (fun i x => -G0 i x) S :=
    empirical_abs_withZero_le_no_abs_plus_neg G0 hG0_zero n S
  have h_contraction_pos :
      empiricalRademacherComplexity_without_abs n G0 S
        ≤ L * empiricalRademacherComplexity_without_abs n F0 S := by
    simpa [G0] using rademacher_contraction_core φ hL hφ.2 F0 n S
  have h_contraction_neg :
      empiricalRademacherComplexity_without_abs n (fun i x => -G0 i x) S
        ≤ L * empiricalRademacherComplexity_without_abs n F0 S := by
    simpa [G0] using
      rademacher_contraction_core (fun x => -φ x) hL (lipschitzAt0_neg φ hφ).2 F0 n S
  have hF0_le :
      empiricalRademacherComplexity_without_abs n F0 S
        ≤ empiricalRademacherComplexity n F S := by
    simpa [F0] using empirical_without_abs_withZero_le_abs F n S
  calc
    empiricalRademacherComplexity n (fun i x => φ (F i x)) S
        = empiricalRademacherComplexity n (withZero (fun i x => φ (F i x))) S := by
          exact (empirical_abs_withZero_eq (fun i x => φ (F i x)) n S).symm
    _ = empiricalRademacherComplexity n G0 S := by
          rw [hG0_eq]
    _ ≤ empiricalRademacherComplexity_without_abs n G0 S
          + empiricalRademacherComplexity_without_abs n (fun i x => -G0 i x) S :=
          h_abs_split
    _ ≤ L * empiricalRademacherComplexity_without_abs n F0 S
          + L * empiricalRademacherComplexity_without_abs n F0 S :=
          add_le_add h_contraction_pos h_contraction_neg
    _ = 2 * L * empiricalRademacherComplexity_without_abs n F0 S := by ring
    _ ≤ 2 * L * empiricalRademacherComplexity n F S := by
          exact mul_le_mul_of_nonneg_left hF0_le (by nlinarith)

/-- **Scalar-multiplication law for empirical Rademacher complexity.** Scaling
    each element of a function class by `c` scales the absolute-value empirical
    Rademacher complexity by `|c|`. -/
theorem empiricalRademacherComplexity_smul_class
    (F : ι → 𝒳 → ℝ) (c : ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun i x => c * F i x) S
      = |c| * empiricalRademacherComplexity n F S := by
  unfold empiricalRademacherComplexity
  have hsum :
      (∑ σ : Signs n,
          ⨆ i,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k))|)
        =
      |c| * ∑ σ : Signs n,
          ⨆ i,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    calc
      (⨆ i,
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k))|)
          =
        ⨆ i,
          |c| * |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)| := by
          refine iSup_congr fun i => ?_
          have hlin :
              (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k))
                =
              c * ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
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
          rw [hlin, abs_mul]
      _ =
        |c| * ⨆ i,
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)| := by
          exact
            (Real.mul_iSup_of_nonneg (abs_nonneg c)
              (fun i =>
                |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)|)).symm
  rw [hsum]
  ring

/-- A signed empirical average of a uniformly bounded function has absolute
value no larger than the same uniform bound. -/
lemma absInner_le_of_bound
    (H : ι → 𝒳 → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hH : ∀ i x, |H i x| ≤ M)
    (n : ℕ) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * H i (S k)| ≤ M := by
  by_cases hn : n = 0
  · subst hn; simpa using hM0
  · have hn_pos : 0 < (n : ℝ) := by positivity
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)]
    calc
      (n : ℝ)⁻¹ * |∑ k : Fin n, (σ k : ℝ) * H i (S k)|
          ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, M := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
            intro k _
            rw [abs_mul]
            rcases signAtom_coe_real_eq_neg_one_or_one (σ k) with h | h
            · rw [h]; simpa using hH i (S k)
            · rw [h]; simpa using hH i (S k)
      _ = M := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp

/-- Signed empirical averages of a uniformly bounded function class are bounded above by the
common absolute bound. -/
lemma absInner_bddAbove
    (H : ι → 𝒳 → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hH : ∀ i x, |H i x| ≤ M)
    (n : ℕ) (S : Fin n → 𝒳) (σ : Signs n) :
    BddAbove (Set.range
      (fun i => |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * H i (S k)|)) := by
  refine ⟨M, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact absInner_le_of_bound H hM0 hH n S σ i

/-- **Empirical Rademacher complexity is sub-additive over differences of classes.**
For classes `F, G` sharing the index `ι`, each with a uniform bound, the complexity of
`fun i x => F i x - G i x` is at most the sum of the individual complexities. -/
theorem empiricalRademacherComplexity_sub_le
    [Nonempty ι]
    (F G : ι → 𝒳 → ℝ) {MF MG : ℝ} (hMF0 : 0 ≤ MF) (hMG0 : 0 ≤ MG)
    (hF : ∀ i x, |F i x| ≤ MF) (hG : ∀ i x, |G i x| ≤ MG)
    (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun i x => F i x - G i x) S
      ≤ empiricalRademacherComplexity n F S + empiricalRademacherComplexity n G S := by
  classical
  unfold empiricalRademacherComplexity
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
  intro σ _
  have hbddF := absInner_bddAbove F hMF0 hF n S σ
  have hbddG := absInner_bddAbove G hMG0 hG n S σ
  refine ciSup_le (fun i => ?_)
  have hsplit :
      (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (F i (S k) - G i (S k))
        = ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k))
          - ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * G i (S k)) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  exact add_le_add (le_ciSup hbddF i) (le_ciSup hbddG i)

/-- **Ledoux–Talagrand contraction over an arbitrary (possibly infinite) index.**
For an `L`-Lipschitz `φ` with `φ 0 = 0` and a class `F` with a uniform bound `M`,
`R̂_n(φ ∘ F) ≤ 2L · R̂_n(F)` for *any* nonempty index `ι`. The infinite-index case is
reduced to the finite-index `rademacher_contraction_abs` by choosing, for each of the
finitely many sign vectors, an `ε`-approximate maximizer; their finite collection is a
finite subindex on which the Fintype contraction applies. -/
theorem empiricalRademacherComplexity_contraction_abs_of_bddAbove
    [Nonempty ι]
    (φ : ℝ → ℝ) {L : ℝ} (hφ : LipschitzAt0 φ L)
    (F : ι → 𝒳 → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i x, |F i x| ≤ M)
    (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun i x => φ (F i x)) S
      ≤ 2 * L * empiricalRademacherComplexity n F S := by
  classical
  have hL : 0 ≤ L := by
    have h := hφ.2 0 1
    norm_num [hφ.1] at h
    exact (abs_nonneg _).trans h
  haveI hSigns : Nonempty (Signs n) := ⟨fun _ => ⟨1, by decide⟩⟩
  -- uniform bound for the composed class `φ ∘ F`
  have hLM0 : 0 ≤ L * M := mul_nonneg hL hM0
  have hφM : ∀ i x, |φ (F i x)| ≤ L * M := by
    intro i x
    have h := hφ.2 (F i x) 0
    rw [hφ.1, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hM i x) hL)
  have hcard : (0 : ℝ) < (Fintype.card (Signs n) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Signs n)
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- per-sign ε-approximate maximizers (explicit supremand form)
  have hex : ∀ σ : Signs n,
      ∃ i, (⨆ j, |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j (S k))|) - ε
            < |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F i (S k))| := by
    intro σ
    exact exists_lt_of_lt_ciSup (sub_lt_self _ hε)
  choose iσ hiσ using hex
  -- the finite subindex collecting all per-sign maximizers
  set T : Finset ι := Finset.image iσ Finset.univ with hT
  haveI : Nonempty {x // x ∈ T} :=
    ⟨⟨iσ (Classical.arbitrary (Signs n)),
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩⟩
  -- Fintype contraction on the subindex `↥T`
  have hcontr := rademacher_contraction_abs (ι := {x // x ∈ T}) φ hφ
    (fun j => F j.val) n S
  -- (b) restricting the index only lowers the (with-abs) complexity
  have hb : empiricalRademacherComplexity n (fun j : {x // x ∈ T} => F j.val) S
      ≤ empiricalRademacherComplexity n F S := by
    unfold empiricalRademacherComplexity
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
    intro σ _
    exact ciSup_le (fun j => le_ciSup (absInner_bddAbove F hM0 hM n S σ) j.val)
  -- (a) the ε-maximizers recover the full supremum up to ε
  have ha : empiricalRademacherComplexity n (fun i x => φ (F i x)) S
      ≤ empiricalRademacherComplexity n (fun (j : {x // x ∈ T}) x => φ (F j.val x)) S + ε := by
    unfold empiricalRademacherComplexity
    have hpt : ∀ σ : Signs n,
        (⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F i (S k))|)
          ≤ (⨆ j : {x // x ∈ T},
              |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j.val (S k))|) + ε := by
      intro σ
      have hmem : iσ σ ∈ T := Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
      have hbddT : BddAbove (Set.range
          (fun j : {x // x ∈ T} =>
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j.val (S k))|)) :=
        Finite.bddAbove_range _
      have hle := le_ciSup hbddT (⟨iσ σ, hmem⟩ : {x // x ∈ T})
      have := hiσ σ
      linarith
    calc
      (Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F i (S k))|
          ≤ (Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n,
                ((⨆ j : {x // x ∈ T},
                    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j.val (S k))|) + ε) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hpt σ) (by positivity)
      _ = (Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n,
                (⨆ j : {x // x ∈ T},
                    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j.val (S k))|)
            + (Fintype.card (Signs n) : ℝ)⁻¹ * (Fintype.card (Signs n) : ℝ) * ε := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
      _ = (Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n,
                (⨆ j : {x // x ∈ T},
                    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j.val (S k))|)
            + ε := by
            rw [inv_mul_cancel₀ (ne_of_gt hcard)]; ring
  calc
    empiricalRademacherComplexity n (fun i x => φ (F i x)) S
        ≤ empiricalRademacherComplexity n (fun (j : {x // x ∈ T}) x => φ (F j.val x)) S + ε := ha
    _ ≤ 2 * L * empiricalRademacherComplexity n (fun j : {x // x ∈ T} => F j.val) S + ε := by
          linarith [hcontr]
    _ ≤ 2 * L * empiricalRademacherComplexity n F S + ε := by
          nlinarith [mul_le_mul_of_nonneg_left hb (by linarith : (0:ℝ) ≤ 2 * L)]



end Contraction
end Concentration
end Stat
end Causalean
