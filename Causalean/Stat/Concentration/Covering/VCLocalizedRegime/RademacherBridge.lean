module
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.Envelope

/-!
# Boolean trace entropy and finite-class Rademacher bridges

This file converts binary trace-cardinality control into finite growth-family
bounds and then into empirical Rademacher estimates for star-hull patterns.
It owns the representative and coefficient constructions used by the later
finite-pattern Massart bounds.
-/

@[expose] public section

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory

universe u v

section RademacherBridge

variable {Ω : Type*} {ι : Type u} {𝒳 : Type v} [MeasurableSpace Ω]
variable [Nonempty ι] [Countable ι]

omit [Nonempty ι] [Countable ι] in
/-- Given [a Boolean classifier family](hyp:π) and [a natural-number
bound](hyp:d), [binary trace-entropy control](goal) holds exactly when either
every finite sample has trace-family VC dimension at most $d$, or every sample
of size $m$ has at most $(m+1)^d$ realized label patterns.

The first branch supplies a VC-dimension bound and the second supplies a direct
growth-cardinality bound. Both yield the polynomial trace bound consumed by
the finite-pattern Massart estimate. -/
def BinaryTraceEntropyControl (π : ι → 𝒳 → Bool) (d : ℕ) : Prop :=
  (∀ {m : ℕ} (S : Fin m → 𝒳), (growthFamily π S).vcDim ≤ d) ∨
  (∀ (m : ℕ) (S : Fin m → 𝒳), (growthFamily π S).card ≤ (m + 1) ^ d)

omit [Nonempty ι] [Countable ι] in
/-- A Boolean class whose trace family has bounded VC dimension, or a direct
trace-size bound, realizes no more patterns on a finite sample than a
polynomial of degree d in one plus the sample size. -/
lemma growthFamily_card_le_succ_pow_of_trace
    (π : ι → 𝒳 → Bool) (d n : ℕ)
    (Htrace : BinaryTraceEntropyControl π d) (S : Fin n → 𝒳) :
    (growthFamily π S).card ≤ (n + 1) ^ d := by
  rcases Htrace with hvc | hcard
  · exact le_trans
      (card_growthFamily_le_sum_choose (growthFamily π S) (hvc S))
      (sum_choose_le_succ_pow n d)
  · exact hcard n S

omit [Nonempty ι] [Countable ι] in
/-- When a Boolean growth family on a sample has positive cardinality and at most the
degree-`d` polynomial number of patterns in one plus the sample size, twice the logarithm
of twice its cardinality is no greater than twice that degree times the logarithm of one
plus the sample size, plus two. -/
lemma log_two_growth_card_le
    (π : ι → 𝒳 → Bool) (d n : ℕ) (S : Fin n → 𝒳)
    (hcard_pos : 0 < (growthFamily π S).card)
    (hcard : (growthFamily π S).card ≤ (n + 1) ^ d) :
    2 * Real.log (2 * ((growthFamily π S).card : ℝ))
      ≤ 2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2 := by
  let N : ℕ := (growthFamily π S).card
  let M : ℕ := (n + 1) ^ d
  have hleR : (2 : ℝ) * N ≤ 2 * M := by
    exact_mod_cast (Nat.mul_le_mul_left 2 hcard)
  have hlog_le : Real.log (2 * (N : ℝ)) ≤ Real.log (2 * (M : ℝ)) := by
    exact Real.log_le_log (by positivity) hleR
  have hlogM :
      Real.log (2 * (M : ℝ)) =
        Real.log 2 + (d : ℝ) * Real.log ((n : ℝ) + 1) := by
    dsimp [M]
    norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    rw [Real.log_mul]
    · rw [Real.log_pow]
    · norm_num
    · positivity
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  dsimp [N] at hlog_le
  nlinarith

/-- The absolute empirical Rademacher complexity of a finite class is bounded
by a Massart logarithmic factor times a common radius. -/
lemma empiricalRademacher_withAbs_finiteClass_le
    {ι' Z : Type*} {m : ℕ} (hm : 0 < m) (H : ι' → Z → ℝ) (S' : Fin m → Z)
    (f : Finset ι') (hf : f.Nonempty) (ρ : ℝ)
    (hradius : ∀ i ∈ f,
      Real.sqrt (∑ k : Fin m, ((m : ℝ)⁻¹ * |H i (S' k)|) ^ 2) ≤ ρ) :
    empiricalRademacherComplexity m (F_on H f) S'
      ≤ ρ * Real.sqrt (2 * Real.log (2 * (f.card : ℝ))) := by
  classical
  let Hd : ι' × Bool → Z → ℝ := fun jb z =>
    if jb.2 then H jb.1 z else -H jb.1 z
  let fd : Finset (ι' × Bool) := f.product (Finset.univ : Finset Bool)
  have hfd_nonempty : fd.Nonempty := by
    rcases hf with ⟨i, hi⟩
    refine ⟨(i, true), ?_⟩
    simp [fd, hi]
  have hpoint :
      empiricalRademacherComplexity m (F_on H f) S'
        ≤ empiricalRademacherComplexity_without_abs m (F_on Hd fd) S' := by
    haveI : Nonempty {j // j ∈ f} := by
      rcases hf with ⟨i, hi⟩
      exact ⟨⟨i, hi⟩⟩
    unfold empiricalRademacherComplexity empiricalRademacherComplexity_without_abs
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum ?_
    intro σ _
    refine ciSup_le ?_
    intro j
    let x : ℝ :=
      (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) * F_on H f j (S' k)
    have htrue :
        x =
          (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
            F_on Hd fd ⟨(j.1, true), by simp [fd, j.2]⟩ (S' k) := by
      simp [x, Hd, F_on]
    have hfalse :
        -x =
          (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
            F_on Hd fd ⟨(j.1, false), by simp [fd, j.2]⟩ (S' k) := by
      simp [x, Hd, F_on, Finset.mul_sum]
    have hle_true :
        x ≤
          ⨆ jb : {jb // jb ∈ fd},
            (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
              F_on Hd fd jb (S' k) := by
      rw [htrue]
      exact le_ciSup
        (Finite.bddAbove_range fun jb : {jb // jb ∈ fd} =>
          (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
            F_on Hd fd jb (S' k))
        ⟨(j.1, true), by simp [fd, j.2]⟩
    have hle_false :
        -x ≤
          ⨆ jb : {jb // jb ∈ fd},
            (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
              F_on Hd fd jb (S' k) := by
      rw [hfalse]
      exact le_ciSup
        (Finite.bddAbove_range fun jb : {jb // jb ∈ fd} =>
          (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
            F_on Hd fd jb (S' k))
        ⟨(j.1, false), by simp [fd, j.2]⟩
    have hlower :
        -(⨆ jb : {jb // jb ∈ fd},
            (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
              F_on Hd fd jb (S' k)) ≤ x := by
      linarith
    simpa [x] using abs_le.mpr ⟨hlower, hle_true⟩
  have hpointwise :
      ∀ i ∈ fd, ∀ j : Fin m, |Hd i (S' j)| ≤ (m : ℝ) * ρ := by
    intro i hi j
    rcases i with ⟨i, b⟩
    have hi_f : i ∈ f := by
      simpa [fd] using (Finset.mem_product.mp hi).1
    have hterm :
        ((m : ℝ)⁻¹ * |H i (S' j)|) ^ 2
          ≤ ∑ k : Fin m, ((m : ℝ)⁻¹ * |H i (S' k)|) ^ 2 := by
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin m)))
        (f := fun k : Fin m => ((m : ℝ)⁻¹ * |H i (S' k)|) ^ 2)
        (by intro k _; exact sq_nonneg _)
        (by simp)
    have hscaled :
        (m : ℝ)⁻¹ * |H i (S' j)| ≤ ρ := by
      have hsqrt :=
        (Real.sqrt_le_sqrt hterm).trans (hradius i hi_f)
      have hnonneg : 0 ≤ (m : ℝ)⁻¹ * |H i (S' j)| := by
        exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m)) (abs_nonneg _)
      simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] using hsqrt
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt hmR)
    have hcancel : (m : ℝ) * ((m : ℝ)⁻¹ * |H i (S' j)|) = |H i (S' j)| := by
      field_simp [ne_of_gt hmR]
    have hH : |H i (S' j)| ≤ (m : ℝ) * ρ := by
      simpa [hcancel, mul_assoc] using hmul
    by_cases hb : b = true
    · simp [Hd, hb, hH]
    · have hbfalse : b = false := by cases b <;> simp at hb ⊢
      simpa [Hd, hbfalse, abs_neg] using hH
  have hmass :
      empiricalRademacherComplexity_without_abs m (F_on Hd fd) S'
        ≤
      (Finset.sup' fd hfd_nonempty fun j =>
          Real.sqrt (∑ i : Fin m,
            ((m : ℝ)⁻¹ * |Hd j (S' i)|) ^ 2)) *
        Real.sqrt (2 * Real.log fd.card) := by
    rw [empiricalRademacherComplexity_without_abs_eq_empiricalRademacherComplexity_pmf_without_abs]
    exact massart_lemma_pmf (F := Hd) (S := S') fd hfd_nonempty
  have hsup :
      (Finset.sup' fd hfd_nonempty fun j =>
          Real.sqrt (∑ i : Fin m,
            ((m : ℝ)⁻¹ * |Hd j (S' i)|) ^ 2)) ≤ ρ := by
    refine Finset.sup'_le _ _ ?_
    intro jb hjb
    rcases jb with ⟨i, b⟩
    have hi_f : i ∈ f := by
      simpa [fd] using (Finset.mem_product.mp hjb).1
    by_cases hb : b = true
    · simpa [Hd, hb] using hradius i hi_f
    · have hbfalse : b = false := by cases b <;> simp at hb ⊢
      simpa [Hd, hbfalse, abs_neg] using hradius i hi_f
  have hcard : (fd.card : ℝ) = 2 * (f.card : ℝ) := by
    simp [fd, Nat.cast_mul, mul_comm]
  calc
    empiricalRademacherComplexity m (F_on H f) S'
        ≤ empiricalRademacherComplexity_without_abs m (F_on Hd fd) S' := hpoint
    _ ≤
        (Finset.sup' fd hfd_nonempty fun j =>
          Real.sqrt (∑ i : Fin m,
            ((m : ℝ)⁻¹ * |Hd j (S' i)|) ^ 2)) *
        Real.sqrt (2 * Real.log fd.card) := hmass
    _ ≤ ρ * Real.sqrt (2 * Real.log fd.card) :=
        mul_le_mul_of_nonneg_right hsup (Real.sqrt_nonneg _)
    _ = ρ * Real.sqrt (2 * Real.log (2 * (f.card : ℝ))) := by
        rw [hcard]

/-- Restricting a finite function family to its full index set leaves its
empirical Rademacher complexity unchanged. -/
lemma empiricalRademacherComplexity_F_on_univ_eq
    {ι' Z : Type*} [Fintype ι']
    {m : ℕ} (H : ι' → Z → ℝ) (S' : Fin m → Z) :
    empiricalRademacherComplexity m (F_on H (Finset.univ : Finset ι')) S'
      = empiricalRademacherComplexity m H S' := by
  classical
  cases isEmpty_or_nonempty ι' with
  | inl _ => simp [empiricalRademacherComplexity]
  | inr _ =>
    unfold empiricalRademacherComplexity
    apply congrArg
    refine Finset.sum_congr rfl ?_
    intro σ _
    haveI : Nonempty {j // j ∈ (Finset.univ : Finset ι')} := by
      rcases (inferInstance : Nonempty ι') with ⟨i⟩
      exact ⟨⟨i, by simp⟩⟩
    apply le_antisymm
    · refine ciSup_le ?_
      intro i
      exact le_ciSup
        (Finite.bddAbove_range fun j : ι' =>
          |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) * H j (S' k)|)
        i.1
    · refine ciSup_le ?_
      intro i
      have hidx : i ∈ (Finset.univ : Finset ι') := by simp
      exact le_ciSup
        (Finite.bddAbove_range fun j : {j // j ∈ (Finset.univ : Finset ι')} =>
          |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) * F_on H (Finset.univ : Finset ι') j (S' k)|)
        ⟨i, hidx⟩

/-- Scaling a function by a constant scales its empirical root-mean-square
norm by the absolute value of that constant. -/
lemma empiricalNorm_const_mul
    {𝒳 : Type*} {n : ℕ} (S : Fin n → 𝒳) (c : ℝ)
    (f : 𝒳 → ℝ) :
    empiricalNorm S (fun x => c * f x) = |c| * empiricalNorm S f := by
  classical
  unfold empiricalNorm
  have hsum :
      (∑ i : Fin n, (c * f (S i)) ^ 2)
        = c ^ 2 * ∑ i : Fin n, (f (S i)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring_nf
  have hnonneg :
      0 ≤ (1 / (n : ℝ)) * ∑ i : Fin n, (f (S i)) ^ 2 := by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  calc
    Real.sqrt ((1 / (n : ℝ)) * ∑ i : Fin n, (c * f (S i)) ^ 2)
        = Real.sqrt (c ^ 2 * ((1 / (n : ℝ)) * ∑ i : Fin n, (f (S i)) ^ 2)) := by
          rw [hsum]
          ring_nf
    _ = Real.sqrt (c ^ 2) *
          Real.sqrt ((1 / (n : ℝ)) * ∑ i : Fin n, (f (S i)) ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg c)]
    _ = |c| * Real.sqrt ((1 / (n : ℝ)) * ∑ i : Fin n, (f (S i)) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]

/-- Given [a Boolean classifier family](hyp:π), [a finite sample](hyp:S), and [a realized label pattern on that sample](hyp:A), [a representative classifier index](goal) is chosen whose labels realize that pattern. -/
noncomputable def growthFamilyRep
    {ι 𝒳 : Type*} {n : ℕ} (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳)
    (A : {A // A ∈ growthFamily π S}) : ι :=
  Classical.choose ((mem_growthFamily_iff (π := π) (S := S) (A := A.1)).mp A.2)

/-- The chosen growth-family representative realizes the pattern it represents. -/
lemma growthFamilyRep_spec
    {ι 𝒳 : Type*} {n : ℕ} (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳)
    (A : {A // A ∈ growthFamily π S}) :
    restrictionPattern (π (growthFamilyRep π S A)) S = A.1 :=
  Classical.choose_spec ((mem_growthFamily_iff (π := π) (S := S) (A := A.1)).mp A.2)

/-- Given [a real-valued function family](hyp:F), [a localization norm](hyp:norm), [a Boolean factorization family](hyp:π), [a finite sample](hyp:S), [a localization radius](hyp:r), and [a realized label pattern](hyp:A), [the star-hull pattern coefficient](goal) is the supremum of the active zeroed-star-hull scale coefficients among functions realizing that pattern on the sample. -/
noncomputable def starHullPatternCoeff
    {ι 𝒳 : Type*} {n : ℕ} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳) (r : ℝ)
    (A : {A // A ∈ growthFamily π S}) : ℝ :=
  ⨆ i : {i : ι // restrictionPattern (π i) S = A.1},
    starHullZeroOutScaleCoeff F norm r i.1

/-- Given [a real-valued function family](hyp:F), [a localization norm](hyp:norm), [a Boolean factorization family](hyp:π), [a finite sample](hyp:S), and [a localization radius](hyp:r), [the star-hull pattern class](goal) assigns to each realized label pattern the representative function for that pattern, multiplied by its star-hull pattern coefficient. -/
noncomputable def starHullPatternClass
    {ι 𝒳 : Type*} {n : ℕ} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳) (r : ℝ) :
    {A // A ∈ growthFamily π S} → 𝒳 → ℝ :=
  fun A x => starHullPatternCoeff F norm π S r A *
    F (growthFamilyRep π S A) x

/-- The largest active scalar in a zeroed star hull is nonnegative because
the zero scalar is always available. -/
lemma starHullZeroOutScaleCoeff_nonneg
    {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (r : ℝ) (i : ι) :
    0 ≤ starHullZeroOutScaleCoeff F norm r i := by
  classical
  let c : Set.Icc (0 : ℝ) 1 → ℝ := fun a =>
    if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0
  have hc_bdd : BddAbove (Set.range c) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    dsimp [c]
    split_ifs
    · exact a.property.2
    · norm_num
  let a0 : Set.Icc (0 : ℝ) 1 := ⟨0, by simp [Set.mem_Icc]⟩
  have hval : c a0 = 0 := by simp [c, a0]
  rw [starHullZeroOutScaleCoeff]
  change 0 ≤ ⨆ a : Set.Icc (0 : ℝ) 1, c a
  simpa [hval] using le_ciSup hc_bdd a0

private lemma activeCoeff_le_starHullZeroOutScaleCoeff
    {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (r : ℝ) (a : Set.Icc (0 : ℝ) 1) (i : ι) :
    (if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0)
      ≤ starHullZeroOutScaleCoeff F norm r i := by
  classical
  let c : Set.Icc (0 : ℝ) 1 → ℝ := fun a =>
    if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0
  have hc_bdd : BddAbove (Set.range c) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    dsimp [c]
    split_ifs
    · exact a.property.2
    · norm_num
  rw [starHullZeroOutScaleCoeff]
  exact le_ciSup hc_bdd a

/-- The coefficient assigned to any observed Boolean pattern by the localized
star-hull pattern class is nonnegative. -/
lemma starHullPatternCoeff_nonneg
    {ι 𝒳 : Type*} {n : ℕ} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳) (r : ℝ)
    (A : {A // A ∈ growthFamily π S}) :
    0 ≤ starHullPatternCoeff F norm π S r A := by
  classical
  let rep : {i : ι // restrictionPattern (π i) S = A.1} :=
    ⟨growthFamilyRep π S A, growthFamilyRep_spec π S A⟩
  have hcoeff_le : BddAbove
      (Set.range fun i : {i : ι // restrictionPattern (π i) S = A.1} =>
        starHullZeroOutScaleCoeff F norm r i.1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact starHullZeroOutScaleCoeff_le_one F norm r i.1
  have hrep_le :
      starHullZeroOutScaleCoeff F norm r rep.1
        ≤ starHullPatternCoeff F norm π S r A := by
    rw [starHullPatternCoeff]
    exact le_ciSup hcoeff_le rep
  exact (starHullZeroOutScaleCoeff_nonneg F norm r rep.1).trans hrep_le

private lemma starHullZeroOutScaleCoeff_le_patternCoeff
    {ι 𝒳 : Type*} {n : ℕ} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳) (r : ℝ)
    (A : {A // A ∈ growthFamily π S}) (i : ι)
    (hiA : restrictionPattern (π i) S = A.1) :
    starHullZeroOutScaleCoeff F norm r i
      ≤ starHullPatternCoeff F norm π S r A := by
  classical
  have hcoeff_le : BddAbove
      (Set.range fun i : {i : ι // restrictionPattern (π i) S = A.1} =>
        starHullZeroOutScaleCoeff F norm r i.1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact starHullZeroOutScaleCoeff_le_one F norm r i.1
  rw [starHullPatternCoeff]
  exact le_ciSup hcoeff_le ⟨i, hiA⟩

/-- When a function class factorizes samplewise through Boolean labels, any function
with a given observed Boolean pattern agrees on the sample with that pattern's chosen representative. -/
lemma sample_eq_growthFamilyRep_of_pattern
    {ι 𝒳 : Type*} {n : ℕ} {F : ι → 𝒳 → ℝ}
    {π : ι → 𝒳 → Bool} {S : Fin n → 𝒳} {φ : Fin n → Bool → ℝ}
    (hfactorS : ∀ i j, F i (S j) = φ j (π i (S j)))
    (A : {A // A ∈ growthFamily π S}) {i : ι}
    (hiA : restrictionPattern (π i) S = A.1) (k : Fin n) :
    F i (S k) = F (growthFamilyRep π S A) (S k) := by
  rw [hfactorS i k, hfactorS (growthFamilyRep π S A) k]
  apply congrArg (φ k)
  apply Bool.eq_iff_iff.mpr
  rw [← restrictionPattern_mem_iff (p := π i) (S := S) (j := k),
    hiA, ← growthFamilyRep_spec π S A,
    restrictionPattern_mem_iff (p := π (growthFamilyRep π S A)) (S := S) (j := k)]

/-- For [a nonempty function index set and observation space](hyp:ι,𝒳), [a sample
size](hyp:n), [a real-valued function class, localization norm, and Boolean label
class](hyp:F,norm,π), if [function values on every finite sample factor through those Boolean
labels](hyp:hfactor), then for [a sample and localization radius](hyp:S,r), [the empirical
Rademacher complexity of the zeroed localized star hull is no greater than that of its finite
sample-pattern class](goal).

If function values on every finite sample depend only on Boolean labels, then the
empirical Rademacher complexity of the zeroed localized star hull is no greater than
that of its finite sample-pattern class. -/
lemma starHullZeroOut_empirical_rademacher_le_patternClass
    {ι 𝒳 : Type*} [Nonempty ι] {n : ℕ}
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (S : Fin n → 𝒳) (r : ℝ) :
    empiricalRademacherComplexity n (starHullZeroOut F norm r) S
      ≤ empiricalRademacherComplexity n (starHullPatternClass F norm π S r) S := by
  classical
  rcases hfactor S with ⟨φ, hφ⟩
  haveI : Nonempty {A // A ∈ growthFamily π S} := by
    let i0 : ι := Classical.arbitrary ι
    have hmem : restrictionPattern (π i0) S ∈ growthFamily π S := by
      rw [mem_growthFamily_iff]
      exact ⟨i0, rfl⟩
    exact ⟨⟨restrictionPattern (π i0) S, hmem⟩⟩
  unfold empiricalRademacherComplexity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum ?_
  intro σ _
  refine ciSup_le ?_
  intro p
  rcases p with ⟨a, i⟩
  let A0 : Finset (Fin n) := restrictionPattern (π i) S
  have hA0 : A0 ∈ growthFamily π S := by
    rw [mem_growthFamily_iff]
    exact ⟨i, rfl⟩
  let A : {A // A ∈ growthFamily π S} := ⟨A0, hA0⟩
  have hiA : restrictionPattern (π i) S = A.1 := rfl
  let active : ℝ := if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0
  let innerI : ℝ :=
    (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)
  let innerRep : ℝ :=
    (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
      F (growthFamilyRep π S A) (S k)
  have hstar :
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F norm r (a, i) (S k)|
        = active * |innerI| := by
    simpa [active, innerI] using
      starHullZeroOut_inner_term_eq F norm r S σ a i
  have hinner : innerI = innerRep := by
    simp [innerI, innerRep,
      sample_eq_growthFamilyRep_of_pattern (F := F) (π := π)
        (S := S) (φ := φ) hφ A hiA]
  have hactive_nonneg : 0 ≤ active := by
    dsimp [active]
    split_ifs
    · exact a.property.1
    · norm_num
  have hscale_le :
      active ≤ starHullZeroOutScaleCoeff F norm r i := by
    simpa [active] using activeCoeff_le_starHullZeroOutScaleCoeff F norm r a i
  have hcoeff_le :
      starHullZeroOutScaleCoeff F norm r i
        ≤ starHullPatternCoeff F norm π S r A :=
    starHullZeroOutScaleCoeff_le_patternCoeff F norm π S r A i hiA
  have hterm_le :
      active * |innerI|
        ≤ starHullPatternCoeff F norm π S r A * |innerRep| := by
    calc
      active * |innerI|
          ≤ starHullZeroOutScaleCoeff F norm r i * |innerI| :=
            mul_le_mul_of_nonneg_right hscale_le (abs_nonneg _)
      _ ≤ starHullPatternCoeff F norm π S r A * |innerI| :=
            mul_le_mul_of_nonneg_right hcoeff_le (abs_nonneg _)
      _ = starHullPatternCoeff F norm π S r A * |innerRep| := by
            rw [hinner]
  have hpattern :
      starHullPatternCoeff F norm π S r A * |innerRep|
        =
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullPatternClass F norm π S r A (S k)| := by
    have hcoeff_nonneg := starHullPatternCoeff_nonneg F norm π S r A
    have hlin :
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullPatternClass F norm π S r A (S k)
          =
        starHullPatternCoeff F norm π S r A * innerRep := by
      dsimp [starHullPatternClass, innerRep]
      calc
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            (starHullPatternCoeff F norm π S r A *
              F (growthFamilyRep π S A) (S k))
            =
          (n : ℝ)⁻¹ * (starHullPatternCoeff F norm π S r A *
            ∑ k : Fin n, (σ k : ℝ) *
              F (growthFamilyRep π S A) (S k)) := by
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k _
            ring
        _ = starHullPatternCoeff F norm π S r A *
            ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              F (growthFamilyRep π S A) (S k)) := by
            ring
    symm
    calc
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullPatternClass F norm π S r A (S k)|
          = |starHullPatternCoeff F norm π S r A * innerRep| := by
            rw [hlin]
      _ = starHullPatternCoeff F norm π S r A * |innerRep| := by
            rw [abs_mul, abs_of_nonneg hcoeff_nonneg]
  calc
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
        starHullZeroOut F norm r (a, i) (S k)|
        = active * |innerI| := hstar
    _ ≤ starHullPatternCoeff F norm π S r A * |innerRep| := hterm_le
    _ = |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullPatternClass F norm π S r A (S k)| := hpattern
    _ ≤ ⨆ A : {A // A ∈ growthFamily π S},
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullPatternClass F norm π S r A (S k)| := by
        exact le_ciSup
          (Finite.bddAbove_range fun A : {A // A ∈ growthFamily π S} =>
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              starHullPatternClass F norm π S r A (S k)|)
          A

end RademacherBridge
end Concentration
end Stat
end Causalean
