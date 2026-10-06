module
public import Causalean.Experimentation.DesignBased.ProductBlock
/-! Finite fair-sign averages factor over disjoint coordinate blocks, by iterating
Causalean's two-block expectation identity. -/
@[expose] public section
noncomputable section
open scoped BigOperators
open Causalean.Experimentation.DesignBased
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- A single latent sign is a fair bit. -/
-- @node: fairBitDesign
def fairBitDesign : FiniteDesign Bool where
  p _ := 1 / 2
  p_nonneg _ := by norm_num
  p_sum := by simp [Fintype.sum_bool]

/-- The independent fair-bit design expectation is the uniform finite sign average.  [the theorem's stated inputs and assumptions](hyp:F), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι). -/
-- @node: fairSignDesign_E
lemma fairSignDesign_E {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → Bool) → ℝ) :
    (prodDesign (fun _ : ι => fairBitDesign)).E F =
      (2 : ℝ)^(-((Fintype.card ι) : ℤ)) * ∑ lam, F lam := by
  simp only [FiniteDesign.E, prodDesign_p, fairBitDesign, Finset.prod_const,
    Finset.card_univ, ← Finset.mul_sum]
  simp [zpow_neg, zpow_natCast, one_div]

/-- An arbitrary finite family of functions using pairwise disjoint coordinate blocks has
factorized product expectation under an independent coordinate design.  [the theorem's stated inputs and assumptions](hyp:ι,κ,α,D,s,A,F,hdisj,s,hdep), and [the asserted conclusion follows](goal). -/
-- @node: finiteDesign_disjointBlocks_prod
lemma finiteDesign_disjointBlocks_prod
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (D : ∀ i, FiniteDesign (α i)) (s : Finset κ) (A : κ → Finset ι)
    (F : κ → (∀ i, α i) → ℝ)
    (hdisj : Set.PairwiseDisjoint (s : Set κ) A)
    (hdep : ∀ k ∈ s, ∀ w w', (∀ i ∈ A k, w i = w' i) → F k w = F k w') :
    (prodDesign D).E (fun w => ∏ k ∈ s, F k w) =
      ∏ k ∈ s, (prodDesign D).E (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FiniteDesign.E_const]
  | @insert k s hk ih =>
    simp only [Finset.prod_insert hk]
    rw [FiniteDesign.E_prod_block_mul D (A k) (F k) (fun w => ∏ l ∈ s, F l w)]
    · rw [ih]
      · intro i hi j hj hij
        exact hdisj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
      · intro l hl
        exact hdep l (Finset.mem_insert_of_mem hl)
    · exact hdep k (Finset.mem_insert_self k s)
    · intro w w' hagree
      apply Finset.prod_congr rfl
      intro l hl
      apply hdep l (Finset.mem_insert_of_mem hl) w w'
      intro i hi
      apply hagree i
      intro hik
      have hkl : k ≠ l := by intro heq; subst l; exact hk hl
      exact Finset.disjoint_left.mp
        (hdisj (Finset.mem_insert_self k s) (Finset.mem_insert_of_mem hl) hkl) hik hi

/-- Uniform fair-sign averaging commutes with a product of functions of disjoint sign blocks.  [the theorem's stated inputs and assumptions](hyp:ι,κ,s,A,F,hdisj,s,hdep), and [the asserted conclusion follows](goal). -/
-- @node: fairSignAverage_disjointBlocks_prod
lemma fairSignAverage_disjointBlocks_prod
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (s : Finset κ) (A : κ → Finset ι) (F : κ → (ι → Bool) → ℝ)
    (hdisj : Set.PairwiseDisjoint (s : Set κ) A)
    (hdep : ∀ k ∈ s, ∀ w w', (∀ i ∈ A k, w i = w' i) → F k w = F k w') :
    (2 : ℝ)^(-((Fintype.card ι) : ℤ)) * ∑ lam, ∏ k ∈ s, F k lam =
      ∏ k ∈ s, ((2 : ℝ)^(-((Fintype.card ι) : ℤ)) * ∑ lam, F k lam) := by
  simpa only [fairSignDesign_E] using
    finiteDesign_disjointBlocks_prod (fun _ => fairBitDesign) s A F hdisj hdep
end CausalSmith.Stat.PrivateCateRoughdesign
