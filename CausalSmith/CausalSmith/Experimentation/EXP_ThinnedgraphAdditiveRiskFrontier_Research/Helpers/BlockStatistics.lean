module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockPrior
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Observed block statistics and conditional polynomial density
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

variable (n B d : ℕ)

/-- A retained graph uses a single size-d source partition for the entire fitted block layout. -/
def ValidRetainedGraph (H : OffDiag (Fin n) → Bool) : Prop :=
  2 * (B * d) ≤ n ∧
  ∃ s : SourcePartition B d, ∀ e, H e = true → blockEdge n B d s e.1.1 e.1.2
  -- @realizes r(retained arrows supported by one size-d source partition)
  -- @realizes K(shared partition prevents a source from consuming capacity in multiple blocks)

/-- The labeled sources with at least one retained arrow into the specified recipient block. -/
def revealedSources (H : OffDiag (Fin n) → Bool) (ℓ : Fin B) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j.val < B * d ∧
    ∃ i ∈ recipientBlock n B d ℓ, ∃ hji : j ≠ i, H ⟨(j,i),hji⟩ = true)

/-- The number of revealed labeled sources in a recipient block. -/
def revealedCount (H : OffDiag (Fin n) → Bool) (ℓ : Fin B) : ℕ :=
  (revealedSources n B d H ℓ).card
-- @realizes r(revealed sources per recipient block)

/-- The remaining hidden-source capacity of a block. -/
def capacity (H : OffDiag (Fin n) → Bool) (ℓ : Fin B) : ℕ := d - revealedCount n B d H ℓ
-- @realizes urow(d minus revealed source count)

/-- The sum of observed treatment signs over the revealed labeled sources. -/
def revealedSignSum (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n)) (ℓ : Fin B) : ℝ :=
  ∑ j ∈ revealedSources n B d H ℓ, signOf (z j)
-- @realizes A(sum of observed centered signs of revealed sources)

/-- The total remaining hidden-source capacity over all blocks. -/
def undiscovered (H : OffDiag (Fin n) → Bool) : ℕ := ∑ ℓ : Fin B, capacity n B d H ℓ
-- @realizes M(sum of remaining block capacities)

/-- The observed global treated count among source labels with no retained arrow. -/
def hiddenTreated (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n)) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => j.val < B * d ∧ z j = true ∧
    ¬ ∃ i : Fin n, ∃ hji : j ≠ i, H ⟨(j,i),hji⟩ = true)).card
-- @realizes K(observed treated count among all unrevealed labeled sources)

/-- A recipient label belongs to at most one block.  [For the stated data and conditions](hyp:i,ℓ,k,hℓ,hk), [the stated conclusion holds](goal). -/
-- @node: recipientBlock_unique
lemma recipientBlock_unique (i : Fin n) (ℓ k : Fin B)
    (hℓ : i ∈ recipientBlock n B d ℓ) (hk : i ∈ recipientBlock n B d k) : ℓ = k := by
  have hℓ' := (Finset.mem_filter.mp hℓ).2
  have hk' := (Finset.mem_filter.mp hk).2
  apply Fin.ext
  apply Nat.le_antisymm
  · by_contra h
    have hmul : (k.val + 1) * d ≤ ℓ.val * d :=
      Nat.mul_le_mul_right d (by omega)
    omega
  · by_contra h
    have hmul : (ℓ.val + 1) * d ≤ k.val * d :=
      Nat.mul_le_mul_right d (by omega)
    omega

/-- Partition-supported retained graphs reveal at most d sources in each block.  [For the stated data and conditions](hyp:H,hH,ℓ), [the stated conclusion holds](goal). -/
-- @node: revealedCount_le
lemma revealedCount_le (H : OffDiag (Fin n) → Bool) (hH : ValidRetainedGraph n B d H)
    (ℓ : Fin B) : revealedCount n B d H ℓ ≤ d := by
  obtain ⟨hfit, s, hs⟩ := hH
  let fiber := Finset.univ.filter (fun j : Fin (B * d) => s.1 j = ℓ)
  have hcard : (fiber.image Fin.val).card = d := by
    rw [Finset.card_image_of_injective _ Fin.val_injective]
    exact s.2 ℓ
  change (revealedSources n B d H ℓ).card ≤ d
  apply le_trans (b := (fiber.image Fin.val).card) ?_ (le_of_eq hcard)
  apply Finset.card_le_card_of_injOn Fin.val
  · intro j hj
    obtain ⟨hjlt, i, hi, hji, hedge⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨⟨hjlt', k, hsk, hik⟩, _⟩ := hs ⟨(j, i), hji⟩ hedge
    have hk : k = ℓ := recipientBlock_unique n B d i k ℓ hik hi
    apply Finset.mem_image.mpr
    refine ⟨⟨j.val, hjlt⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa [hk] using hsk⟩
  · intro a ha b hb hab
    exact Fin.ext hab
-- @realizes r(derived range {0,...,d} on the retained-graph domain)

/-- The global hidden treated count does not exceed the remaining shared-partition capacity.  [For the stated data and conditions](hyp:H,hH,z), [the stated conclusion holds](goal). -/
-- @node: hiddenTreated_le
lemma hiddenTreated_le (H : OffDiag (Fin n) → Bool) (hH : ValidRetainedGraph n B d H)
    (z : Assign (Fin n)) : hiddenTreated n B d H z ≤ undiscovered n B d H := by
  classical
  obtain ⟨hfit, s, hs⟩ := hH
  by_cases hB : B = 0
  · subst B
    simp [hiddenTreated, undiscovered]
  have hmn : B * d ≤ n := by omega
  let emb : Fin (B * d) → Fin n := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hmn⟩
  have hemb : Function.Injective emb := by
    intro a b hab
    exact Fin.ext (congrArg (fun j : Fin n => j.val) hab)
  let label : Fin n → Fin B := fun j =>
    if hj : j.val < B * d then s.1 ⟨j.val, hj⟩ else ⟨0, Nat.pos_of_ne_zero hB⟩
  have hlabel (j : Fin (B * d)) : label (emb j) = s.1 j := by
    simp [label, emb, j.isLt]
  let fiber (ℓ : Fin B) := Finset.univ.filter
    (fun j : Fin n => j.val < B * d ∧ label j = ℓ)
  have hfiber (ℓ : Fin B) :
      fiber ℓ = (Finset.univ.filter (fun j : Fin (B * d) => s.1 j = ℓ)).image emb := by
    ext j
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hj, hℓ⟩
      refine ⟨⟨j.val, hj⟩, ?_, ?_⟩
      · simpa [label, hj] using hℓ
      · exact Fin.ext rfl
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.isLt, (hlabel k).trans hk⟩
  have hfiber_card (ℓ : Fin B) : (fiber ℓ).card = d := by
    rw [hfiber, Finset.card_image_of_injective _ hemb]
    exact s.2 ℓ
  have hrevealed (ℓ : Fin B) : revealedSources n B d H ℓ ⊆ fiber ℓ := by
    intro j hj
    obtain ⟨hjlt, i, hi, hji, hedge⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨⟨hjlt', k, hsk, hik⟩, _⟩ := hs ⟨(j, i), hji⟩ hedge
    have hk : k = ℓ := recipientBlock_unique n B d i k ℓ hik hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hjlt, ?_⟩
    simpa [label, hjlt, hk] using hsk
  let hidden := Finset.univ.filter (fun j : Fin n => j.val < B * d ∧ z j = true ∧
    ¬ ∃ i : Fin n, ∃ hji : j ≠ i, H ⟨(j,i),hji⟩ = true)
  have hsplit : hidden.card = ∑ ℓ : Fin B, (hidden.filter (fun j => label j = ℓ)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  change hidden.card ≤ ∑ ℓ : Fin B, capacity n B d H ℓ
  rw [hsplit]
  apply Finset.sum_le_sum
  intro ℓ _
  have hsub : hidden.filter (fun j => label j = ℓ) ⊆
      fiber ℓ \ revealedSources n B d H ℓ := by
    intro j hj
    obtain ⟨hjhidden, hjlabel⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjlt, _, hjnone⟩ := (Finset.mem_filter.mp hjhidden).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjlt, hjlabel⟩, ?_⟩
    intro hjrevealed
    obtain ⟨_, i, _, hji, hedge⟩ := (Finset.mem_filter.mp hjrevealed).2
    exact hjnone ⟨i, hji, hedge⟩
  calc
    (hidden.filter (fun j => label j = ℓ)).card ≤
        (fiber ℓ \ revealedSources n B d H ℓ).card := Finset.card_le_card hsub
    _ = capacity n B d H ℓ := by
      rw [Finset.card_sdiff_of_subset (hrevealed ℓ), hfiber_card]
      rfl
-- @realizes K(derived range {0,...,M} on the shared-partition domain)

/-- The coefficient-constrained hypergeometric mixture density of distinct block responses. -/
def blockDensity (σ : Bool) (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (z : Assign (Fin n)) (y : Fin B → ℝ) : ℝ :=
  (∏ ℓ : Fin B, ∑ k ∈ Finset.range (capacity n B d H ℓ + 1),
    Polynomial.C (((capacity n B d H ℓ).choose k : ℝ) *
      cosSqDensity (y ℓ - signOf σ * h *
        (revealedSignSum n B d H z ℓ + 2 * k - capacity n B d H ℓ) / (2 * d))) *
      Polynomial.X ^ k).coeff (hiddenTreated n B d H z) /
        ((undiscovered n B d H).choose (hiddenTreated n B d H z) : ℝ)
-- @realizes density(coefficient-constrained conditional density; binomial normalization)
-- @realizes y(distinct real outcome vector on Fin B)
-- @realizes x(formal Polynomial.X with coefficient extraction at K)
-- @realizes k(hidden treated-count summation index 0,...,urow_ell)

/-- Expanding the polynomial product retains exactly allocations with the prescribed
total degree.  [For the stated data and conditions](hyp:B,u,w,K), [the stated conclusion holds](goal). -/
-- @node: block_allocation_coeff
lemma block_allocation_coeff (B : ℕ) (u : Fin B → ℕ) (w : ∀ ℓ, Fin (u ℓ + 1) → ℝ) (K : ℕ) :
    (∏ ℓ, ∑ k, Polynomial.C (w ℓ k) * Polynomial.X ^ k.val).coeff K =
      ∑ k : ∀ ℓ, Fin (u ℓ + 1),
        if K = ∑ ℓ, (k ℓ).val then ∏ ℓ, w ℓ (k ℓ) else 0 := by
  rw [Fintype.prod_sum]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
    Polynomial.coeff_C_mul_X_pow]

/-- The row allocation counting polynomial is the binomial polynomial.  [For the stated data and conditions](hyp:u), [the stated conclusion holds](goal). -/
-- @node: block_allocation_binomial_polynomial
lemma block_allocation_binomial_polynomial (u : ℕ) :
    (∑ k : Fin (u + 1), Polynomial.C (u.choose k.val : ℝ) * Polynomial.X ^ k.val) =
      (Polynomial.X + 1 : Polynomial ℝ) ^ u := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => Polynomial.C (u.choose k : ℝ) * Polynomial.X ^ k), add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [one_pow, mul_one]
  rw [mul_comm]
  congr 1

/-- The coefficient of the binomial polynomial counts treated subsets of a fixed total size.  [For the stated data and conditions](hyp:u,K), [the stated conclusion holds](goal). -/
-- @node: block_allocation_binomial_coeff
lemma block_allocation_binomial_coeff (u K : ℕ) :
    ((Polynomial.X + 1 : Polynomial ℝ) ^ u).coeff K = (u.choose K : ℝ) := by
  rw [← block_allocation_binomial_polynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hK : K < u + 1
  · rw [Finset.sum_eq_single ⟨K, hK⟩]
    · simp
    · intro k _ hk
      rw [if_neg]
      intro he
      apply hk
      exact Fin.ext he.symm
    · simp
  · have hzero : u.choose K = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hzero, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    omega

/-- Summing row subset counts with a fixed global treated count gives the global binomial count.  [For the stated data and conditions](hyp:B,u,K), [the stated conclusion holds](goal). -/
-- @node: block_allocation_weights_sum
lemma block_allocation_weights_sum (B : ℕ) (u : Fin B → ℕ) (K : ℕ) :
    (∑ k : ∀ ℓ, Fin (u ℓ + 1),
      if K = ∑ ℓ, (k ℓ).val then ∏ ℓ, (u ℓ).choose (k ℓ).val else 0 : ℝ) =
        ((∑ ℓ, u ℓ).choose K : ℝ) := by
  rw [← block_allocation_coeff B u (fun ℓ k => ((u ℓ).choose k.val : ℝ)) K]
  simp_rw [block_allocation_binomial_polynomial]
  rw [Finset.prod_pow_eq_pow_sum, block_allocation_binomial_coeff]

/-- The constrained row allocation weights sum to one, including zero total capacity.  [For the stated data and conditions](hyp:B,u,K,hK), [the stated conclusion holds](goal). -/
-- @node: block_allocation_weights_normalized
lemma block_allocation_weights_normalized (B : ℕ) (u : Fin B → ℕ) (K : ℕ)
    (hK : K ≤ ∑ ℓ, u ℓ) :
    (∑ k : ∀ ℓ, Fin (u ℓ + 1),
      (if K = ∑ ℓ, (k ℓ).val then ∏ ℓ, ((u ℓ).choose (k ℓ).val : ℝ) else 0) /
        ((∑ ℓ, u ℓ).choose K : ℝ)) = 1 := by
  rw [← Finset.sum_div, block_allocation_weights_sum]
  apply div_self
  exact_mod_cast (Nat.choose_pos hK).ne'

/-- The coefficient-defined density is the exact finite mixture over constrained hidden
row counts.  [For the stated data and conditions](hyp:n,B,d,σ,h,H,z,y), [the stated conclusion holds](goal). -/
-- @node: blockDensity_allocation_sum
lemma blockDensity_allocation_sum (n B d : ℕ) (σ : Bool) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n)) (y : Fin B → ℝ) :
    blockDensity n B d σ h H z y =
      (∑ k : ∀ ℓ, Fin (capacity n B d H ℓ + 1),
        if hiddenTreated n B d H z = ∑ ℓ, (k ℓ).val then
          ∏ ℓ, ((capacity n B d H ℓ).choose (k ℓ).val : ℝ) *
            cosSqDensity (y ℓ - signOf σ * h *
              (revealedSignSum n B d H z ℓ + 2 * (k ℓ).val - capacity n B d H ℓ) /
                (2 * d)) else 0) /
          ((undiscovered n B d H).choose (hiddenTreated n B d H z) : ℝ) := by
  unfold blockDensity
  simp_rw [Finset.sum_range]
  rw [block_allocation_coeff B (capacity n B d H)
    (fun ℓ k => ((capacity n B d H ℓ).choose k.val : ℝ) *
      cosSqDensity (y ℓ - signOf σ * h *
        (revealedSignSum n B d H z ℓ + 2 * k.val - capacity n B d H ℓ) / (2 * d)))]

/-- The constrained conditional block density is nonnegative for every input.  [For the stated data and conditions](hyp:n,B,d,σ,h,H,z,y), [the stated conclusion holds](goal). -/
-- @node: blockDensity_nonneg
lemma blockDensity_nonneg (n B d : ℕ) (σ : Bool) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n)) (y : Fin B → ℝ) :
    0 ≤ blockDensity n B d σ h H z y := by
  rw [blockDensity_allocation_sum]
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro k _
    split_ifs
    · apply Finset.prod_nonneg
      intro ℓ _
      exact mul_nonneg (Nat.cast_nonneg _) (by unfold cosSqDensity; split_ifs <;> positivity)
    · exact le_rfl
  · exact Nat.cast_nonneg _


/-- Copy each distinct response to its recipient block and set source and padding outcomes to
zero. -/
def copyOutcomes (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) (y : Fin B → ℝ) :
    Record (Fin n) :=
  (hz.1, hz.2, fun i => ∑ ℓ : Fin B, if i ∈ recipientBlock n B d ℓ then y ℓ else 0)

/-- The actual joint law of the detailed retained graph and every assignment coordinate. -/
def graphAssignMarginal (D : Measure (Assign (Fin n) × Audit (Fin n))) :
    Measure ((OffDiag (Fin n) → Bool) × Assign (Fin n)) :=
  (partitionLaw B d).bind (fun s =>
    D.map (fun ω => ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1, ω.1)))

/-- The actual marginal law of the detailed labeled retained graph. -/
def retainedGraphMarginal (D : Measure (Assign (Fin n) × Audit (Fin n))) :
    Measure (OffDiag (Fin n) → Bool) := (graphAssignMarginal n B d D).map Prod.fst

/-- Every retained graph in the actual fitted block experiment has common partition support.  [For the stated data and conditions](hyp:D,hfit), [the stated conclusion holds](goal). -/
-- @node: retainedGraphMarginal_valid
lemma retainedGraphMarginal_valid (D : Measure (Assign (Fin n) × Audit (Fin n)))
    (hfit : 2 * (B * d) ≤ n) :
    ∀ᵐ H ∂(retainedGraphMarginal n B d D), ValidRetainedGraph n B d H := by
  unfold retainedGraphMarginal
  apply (ae_map_iff (by fun_prop) (by measurability)).mpr
  change ∀ᵐ hz ∂(graphAssignMarginal n B d D), ValidRetainedGraph n B d hz.1
  rw [ae_iff]
  apply le_antisymm _ bot_le
  refine (Measure.bind_apply_le _ (by measurability)).trans ?_
  have hf (s : SourcePartition B d) :
      (D.map (fun ω => ((recordOf (blockSchedule n B d true 0
        (s, fun _ => 0)) ω).1, ω.1)))
        {hz | ¬ ValidRetainedGraph n B d hz.1} = 0 := by
    rw [Measure.map_apply (by fun_prop) (by measurability)]
    have hempty : (fun ω => ((recordOf (blockSchedule n B d true 0
        (s, fun _ => 0)) ω).1, ω.1)) ⁻¹'
        {hz | ¬ ValidRetainedGraph n B d hz.1} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      apply hω
      refine ⟨hfit, s, ?_⟩
      intro e he
      have hedge : blockEdge n B d s e.1.1 e.1.2 ∧ ω.2 e = true := by
        simpa only [recordOf, blockSchedule, Bool.and_eq_true, decide_eq_true_eq] using he
      exact hedge.1
    rw [hempty, measure_empty]
  simp only [hf, lintegral_zero]
  exact le_rfl
-- @realizes r(actual retained-graph marginal is supported on the size-d partition domain)
-- @realizes K(actual retained-graph marginal has one shared source partition)

/-- The indicator vector that a labeled source has at least one retained arrow. -/
def sourceReveals (H : OffDiag (Fin n) → Bool) : Fin (B * d) → Bool :=
  fun j => decide (∃ v : Fin n, v.val = j.val ∧
    ∃ i : Fin n, ∃ hvi : v ≠ i, H ⟨(v,i),hvi⟩ = true)

/-- Recover the full original-record mixture from the actual graph-assignment marginal and
conditional density. -/
def reconstructedLaw (D : Measure (Assign (Fin n) × Audit (Fin n))) (σ : Bool) (h : ℝ) :
    Measure (Record (Fin n)) :=
  (graphAssignMarginal n B d D).bind (fun hz =>
    (volume.withDensity (fun y => ENNReal.ofReal (blockDensity n B d σ h hz.1 hz.2 y))).map
      (copyOutcomes n B d hz))

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
