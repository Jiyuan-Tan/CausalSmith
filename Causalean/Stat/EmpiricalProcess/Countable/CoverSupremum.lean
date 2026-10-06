module
public import Causalean.Stat.EmpiricalProcess.Countable.ChainBasic
public import Causalean.Stat.EmpiricalProcess.Countable.FiniteAverage

/-!
# Deterministic comparison of a class with its chain branches

A finite cover assigns every function to one weighted-indicator branch.
For each fixed sample, the normalized class supremum's fourth sign average
is at most the sum of the unnormalized branch fourth sign averages divided
by the fourth power of sample size. This is only a comparison of suprema;
it neither assumes nor uses a maximal moment estimate for the chains.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- A chain cover of [a bounded function class](hyp:F) with [m
branches](hyp:m) assigns [each function a branch](hyp:branch) and [a
set](hyp:sets), gives [each branch a fixed signed weight
function](hyp:weight) and [a containing set](hyp:containing), and requires
that [the sets of functions in the same branch are nested](hyp:nested),
[each function's set lies in its branch's containing
set](hyp:subset_containing), and [each function equals its branch weight
restricted to its set (zero outside)](hyp:represents). -/
structure ChainCover {Ω ι : Type*} [MeasurableSpace Ω]
    (F : BoundedClass Ω ι) (m : ℕ) where
  branch : ι → Fin m
  sets : ι → Set Ω
  weight : Fin m → Ω → ℝ
  containing : Fin m → Set Ω
  nested : ∀ i k, branch i = branch k → sets i ⊆ sets k ∨ sets k ⊆ sets i
  subset_containing : ∀ i, sets i ⊆ containing (branch i)
  represents : ∀ i, F.f i = (sets i).indicator (weight (branch i))

/-- [The energy](goal) of [branch b](hyp:b) of [a chain cover](hyp:cover)
on [a sample](hyp:x) is [the sum, over observations lying in the branch's
containing set, of the squared branch weight at the observation](step:1). -/
def coverEnergy {Ω ι : Type*} [MeasurableSpace Ω] {F : BoundedClass Ω ι}
    {m : ℕ} (cover : ChainCover F m) {n : ℕ} (x : Fin n → Ω) (b : Fin m) : ℝ :=
  chainEnergy (cover.containing b) x (fun j => cover.weight b (x j))

/-- [The branch signed supremum](goal) of [branch b](hyp:b) of [a chain
cover](hyp:cover) on [a sample](hyp:x) under [a sign vector σ](hyp:σ) is
[the chain supremum over the sets of the class functions assigned to that
branch, with the branch weight evaluated at each observation and no
sample-size normalization](step:1).

An empty branch has supremum zero.
-/
def branchSignSup {Ω ι : Type*} [MeasurableSpace Ω] {F : BoundedClass Ω ι}
    {m : ℕ} (cover : ChainCover F m) {n : ℕ} (x : Fin n → Ω)
    (σ : Fin n → Bool) (b : Fin m) : ℝ :=
  chainSignSup (fun i : {i : ι // cover.branch i = b} => cover.sets i.1)
    x (fun j => cover.weight b (x j)) σ

/-- For [a nonempty countable bounded class](hyp:F) with [a finite chain
cover](hyp:cover) and [any sample of size n](hyp:x,n), [the sign average of
the fourth power of the normalized signed supremum is at most 1/n^4 times
the sum over branches of the sign averages of the fourth powers of the
unnormalized branch signed suprema](goal), including sample size zero. -/
theorem signedSup_fourth_le_chainAverages {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] [Nonempty ι] (F : BoundedClass Ω ι) {m : ℕ}
    (cover : ChainCover F m) {n : ℕ} (x : Fin n → Ω) :
    signAverage (fun σ => signedSup F.f x σ ^ 4) ≤
      (n : ℝ)⁻¹ ^ 4 * ∑ b, signAverage (fun σ => branchSignSup cover x σ b ^ 4) := by
  classical
  let W (b : Fin m) (σ : Fin n → Bool)
      (i : {i : ι // cover.branch i = b}) : ℝ :=
    |∑ j, if x j ∈ cover.sets i.1 then
      (if σ j then (1 : ℝ) else -1) * cover.weight b (x j) else 0|
  have hW (b : Fin m) (σ : Fin n → Bool) :
      BddAbove (Set.range (W b σ)) := by
    refine ⟨∑ j, |cover.weight b (x j)|, ?_⟩
    rintro _ ⟨i, rfl⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro j _
    split_ifs <;> simp
  have hbranch (σ : Fin n → Bool) (b : Fin m) :
      0 ≤ branchSignSup cover x σ b := by
    change 0 ≤ iSup (W b σ)
    cases isEmpty_or_nonempty {i : ι // cover.branch i = b} with
    | inl h =>
      let := h
      simp
    | inr h =>
      let := h
      exact le_ciSup_of_le (hW b σ) (Classical.arbitrary _) (abs_nonneg _)
  have hm : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨cover.branch (Classical.arbitrary ι), Finset.mem_univ _⟩
  have hpoint (σ : Fin n → Bool) :
      signedSup F.f x σ ^ 4 ≤
        (n : ℝ)⁻¹ ^ 4 * ∑ b, branchSignSup cover x σ b ^ 4 := by
    let M := Finset.univ.sup' hm (branchSignSup cover x σ)
    have hleM (b : Fin m) : branchSignSup cover x σ b ≤ M :=
      Finset.le_sup' _ (Finset.mem_univ b)
    have hclass (i : ι) :
        |(n : ℝ)⁻¹ * ∑ j, (if σ j then (1 : ℝ) else -1) * F.f i (x j)| ≤
          (n : ℝ)⁻¹ * M := by
      have hsum : (∑ j, (if σ j then (1 : ℝ) else -1) * F.f i (x j)) =
          ∑ j, if x j ∈ cover.sets i then
            (if σ j then (1 : ℝ) else -1) * cover.weight (cover.branch i) (x j)
            else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [cover.represents i]
        by_cases h : x j ∈ cover.sets i <;> simp [Set.indicator, h]
      rw [hsum, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (le_ciSup (hW (cover.branch i) σ) ⟨i, rfl⟩).trans
        (hleM (cover.branch i))
    have hsup : signedSup F.f x σ ≤ (n : ℝ)⁻¹ * M := ciSup_le hclass
    have hsup0 : 0 ≤ signedSup F.f x σ :=
      le_ciSup_of_le ⟨(n : ℝ)⁻¹ * M, by rintro _ ⟨i, rfl⟩; exact hclass i⟩
        (Classical.arbitrary ι) (abs_nonneg _)
    obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' hm (branchSignSup cover x σ)
    have hM4 : M ^ 4 ≤ ∑ b, branchSignSup cover x σ b ^ 4 := by
      rw [show M = branchSignSup cover x σ b from hb]
      exact Finset.single_le_sum (f := fun b => branchSignSup cover x σ b ^ 4)
        (fun b _ => pow_nonneg (hbranch σ b) 4) (Finset.mem_univ b)
    calc
      signedSup F.f x σ ^ 4 ≤ ((n : ℝ)⁻¹ * M) ^ 4 :=
        pow_le_pow_left₀ hsup0 hsup 4
      _ = (n : ℝ)⁻¹ ^ 4 * M ^ 4 := mul_pow _ _ _
      _ ≤ (n : ℝ)⁻¹ ^ 4 * ∑ b, branchSignSup cover x σ b ^ 4 :=
        mul_le_mul_of_nonneg_left hM4 (by positivity)
  calc
    signAverage (fun σ => signedSup F.f x σ ^ 4) ≤
        signAverage (fun σ => (∑ b, branchSignSup cover x σ b ^ 4) *
          (n : ℝ)⁻¹ ^ 4) :=
      signAverage_mono _ _ (fun σ => by simpa [mul_comm] using hpoint σ)
    _ = (n : ℝ)⁻¹ ^ 4 * ∑ b, signAverage (fun σ => branchSignSup cover x σ b ^ 4) := by
      rw [signAverage_mul_const, signAverage_sum]
      simp only [mul_comm]


end Causalean.Stat.EmpiricalProcess.Countable
