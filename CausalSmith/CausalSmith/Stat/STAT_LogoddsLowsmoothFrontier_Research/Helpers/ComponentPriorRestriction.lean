module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureDensities
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SignComponents

/-! # Restricting hidden sign priors to one component

Averaging a likelihood over all endpoint signs equals averaging over the signs
owned by its record block. This bridge transfers exact singleton matching to
component densities without revealing signs or assuming record independence.
-/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

attribute [local instance] Classical.propDecidable

/-- [The uniform prior on all signs has the uniform marginal on any ownership
fiber. A function depending only on that fiber has the same two averages. [the documented result](goal) Under [the stated assumptions](hyp:f,hlocal). -/
-- @node: signPrior_average_restrict
lemma signPrior_average_restrict {ν κ : Type*} [Fintype ν] [DecidableEq ν] [DecidableEq κ]
    (owner : ν → κ) (c : κ) (f : (ν → Bool) → ℝ)
    (hlocal : ∀ σ τ, (∀ s, owner s = c → σ s = τ s) → f σ = f τ) :
    (Fintype.card (ν → Bool) : ℝ)⁻¹ * ∑ σ, f σ =
      (Fintype.card ({s : ν // owner s = c} → Bool) : ℝ)⁻¹ *
        ∑ σ, f (componentSignExtension owner c σ) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun s => owner s = c) (fun _ : ν => Bool)
  have he (σ : ν → Bool) :
      f σ = f (componentSignExtension owner c (fun s => σ s.1)) := by
    apply hlocal
    intro s hs
    simp [componentSignExtension, hs]
  have hsum : (∑ σ : ν → Bool, f σ) =
      (Fintype.card ({s : ν // ¬owner s = c} → Bool) : ℝ) *
        ∑ σ, f (componentSignExtension owner c σ) := by
    rw [show (∑ σ : ν → Bool, f σ) =
      ∑ σ : ν → Bool, f (componentSignExtension owner c (fun s => σ s.1)) from
        Finset.sum_congr rfl (fun σ _ => he σ)]
    change (∑ σ, f (componentSignExtension owner c (e σ).1)) = _
    rw [e.sum_comp (fun z => f (componentSignExtension owner c z.1))]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  have hcard : (Fintype.card (ν → Bool) : ℝ) =
      (Fintype.card ({s : ν // owner s = c} → Bool) : ℝ) *
        (Fintype.card ({s : ν // ¬owner s = c} → Bool) : ℝ) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  rw [hsum, hcard, mul_inv_rev]
  have hb : (Fintype.card ({s : ν // ¬owner s = c} → Bool) : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

/-- A block product depending only on its owned signs can use the full prior,
which makes the existing whole-prior cancellation lemmas directly applicable. [the documented result](goal) Under [the stated assumptions](hyp:f,hlocal). -/
-- @node: signPrior_block_average_restrict
lemma signPrior_block_average_restrict {ι ν κ : Type*}
    [Fintype ι] [Fintype ν] [DecidableEq ν] [DecidableEq κ]
    (owner : ν → κ) (block : ι → κ) (c : κ)
    (f : ι → (ν → Bool) → ℝ)
    (hlocal : ∀ i σ τ, (∀ s, owner s = block i → σ s = τ s) → f i σ = f i τ) :
    (Fintype.card (ν → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i : {i : ι // block i = c}, f i.1 σ =
      (Fintype.card ({s : ν // owner s = c} → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i : {i : ι // block i = c}, f i.1 (componentSignExtension owner c σ) := by
  apply signPrior_average_restrict
  intro σ τ h
  apply Finset.prod_congr rfl
  intro i _
  apply hlocal
  intro s hs
  exact h s (hs.trans i.2)

/-- Exact matching of single-record averages removes every block of at most
one record, including the empty block used for unowned endpoint signs. [the documented result](goal) Under [the stated assumptions](hyp:f,g,hcard,hmatch). -/
-- @node: signPrior_small_block_matching
lemma signPrior_small_block_matching {ι ν : Type*} [Fintype ι] [Fintype ν] [DecidableEq ν]
    (f g : ι → (ν → Bool) → ℝ) (hcard : Fintype.card ι ≤ 1)
    (hmatch : ∀ i, (∑ σ, f i σ) = ∑ σ, g i σ) :
    (∑ σ, ∏ i, f i σ) = ∑ σ, ∏ i, g i σ := by
  classical
  let : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcard
  rcases isEmpty_or_nonempty ι with h | h
  · let := h
    simp
  · let := h
    let : Unique ι := { default := Classical.choice h, uniq := fun _ => Subsingleton.elim _ _ }
    simpa only [Fintype.prod_unique] using hmatch (default : ι)

/-- [Endpoint ownership transfers the full sign prior to a selected component
for literal mixed cells. Totalization is handled separately by cell validity. [the documented result](goal) Under [the stated assumptions](hyp:x,l). Under [the stated assumptions](hyp:hk). -/
-- @node: mixedCells_block_average_restrict
lemma mixedCells_block_average_restrict {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → Covariate) (c : SignComponentBlock k x)
    (l : {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} → Bool × Bool)
    (b : Bool) (η ζ : ℝ) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      ∑ σ, ∏ i : {i : Fin n // block i = c},
        4*mixedCells b k σ η ζ (l i).1 (l i).2 (x i.1) =
    (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ, ∏ i : {i : Fin n // block i = c},
        4*mixedCells b k (componentSignExtension owner c σ) η ζ (l i).1 (l i).2 (x i.1) := by
  dsimp only
  apply signPrior_average_restrict
  intro σ τ h
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  apply mixedCells_endpoint_congr
  intro j hj
  unfold endpointSign
  congr 1
  apply h
  exact (signComponentOwner_incident k hk x i.1 j hj).trans i.2

/-- [The fair component uses the same hidden-prior restriction as the mixed
component, uniformly in the effect and signed amplitude. [the documented result](goal) Under [the stated assumptions](hyp:x,l). Under [the stated assumptions](hyp:hk). -/
-- @node: fairCells_block_average_restrict
lemma fairCells_block_average_restrict {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → Covariate) (c : SignComponentBlock k x)
    (l : {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} → Bool × Bool)
    (t δ : ℝ) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      ∑ σ, ∏ i : {i : Fin n // block i = c},
        4*fairCells true k σ t δ (l i).1 (l i).2 (x i.1) =
    (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ, ∏ i : {i : Fin n // block i = c},
        4*fairCells true k (componentSignExtension owner c σ) t δ (l i).1 (l i).2 (x i.1) := by
  dsimp only
  apply signPrior_average_restrict
  intro σ τ h
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  apply fairCells_endpoint_congr
  intro j hj
  unfold endpointSign
  congr 1
  apply h
  exact (signComponentOwner_incident k hk x i.1 j hj).trans i.2

/-- [Validity on the support neighborhood transfers sign restriction to the
actual mixed record density, including its law constructor. [the documented result](goal) Under [the stated assumptions](hyp:x,l,hη,hζ). Under [the stated assumptions](hyp:hk). -/
-- @node: mixedDensity_block_average_restrict
lemma mixedDensity_block_average_restrict {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → Covariate) (c : SignComponentBlock k x)
    (l : {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} → Bool × Bool)
    (b : Bool) (η ζ : ℝ) (hη : |η| ≤ calibEps) (hζ : |ζ| ≤ calibEps) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      ∑ σ, ∏ i : {i : Fin n // block i = c},
        recordCellDensity (mixedLaw b k σ η ζ) (x i.1,l i) =
    (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ, ∏ i : {i : Fin n // block i = c},
        recordCellDensity (mixedLaw b k (componentSignExtension owner c σ) η ζ) (x i.1,l i) := by
  have hv (σ : Fin (k+1) → Bool) : ValidCells (mixedCells b k σ η ζ) :=
    ((calib_constants_spec.2.2.2 k hk σ).1 η ζ hη hζ b).1
  simp only [recordCellDensity, mixedLaw, totalCellLaw_cells_of_valid _ (hv _)]
  exact mixedCells_block_average_restrict k hk x c l b η ζ

/-- [Validity on the support neighborhood transfers sign restriction to the
actual fair record density, with every root already substituted. [the documented result](goal) Under [the stated assumptions](hyp:x,l,ht,hδ). Under [the stated assumptions](hyp:hk). -/
-- @node: fairDensity_block_average_restrict
lemma fairDensity_block_average_restrict {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → Covariate) (c : SignComponentBlock k x)
    (l : {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} → Bool × Bool)
    (t δ : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ calibEps) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      ∑ σ, ∏ i : {i : Fin n // block i = c},
        recordCellDensity (fairLaw k σ t δ) (x i.1,l i) =
    (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ, ∏ i : {i : Fin n // block i = c},
        recordCellDensity (fairLaw k (componentSignExtension owner c σ) t δ) (x i.1,l i) := by
  have hv (σ : Fin (k+1) → Bool) : ValidCells (fairCells true k σ t δ) :=
    ((calib_constants_spec.2.2.2 k hk σ).2 t δ ht hδ true).1
  simp only [recordCellDensity, fairLaw, totalCellLaw_cells_of_valid _ (hv _)]
  exact fairCells_block_average_restrict k hk x c l t δ

/-- [Empty and singleton components have identical actual mixed likelihoods,
by the support theorem's exact singleton matching and hidden-prior restriction. [the documented result](goal) Under [the stated assumptions](hyp:x,l,hη,hζ,hcard). Under [the stated assumptions](hyp:hk). -/
-- @node: mixedDensity_small_block_matching
lemma mixedDensity_small_block_matching {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → Covariate) (c : SignComponentBlock k x)
    (l : {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} → Bool × Bool)
    (η ζ : ℝ) (hη : |η| ≤ calibEps) (hζ : |ζ| ≤ calibEps)
    (hcard : Fintype.card {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} ≤ 1) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ, ∏ i : {i : Fin n // block i = c},
        recordCellDensity (mixedLaw false k (componentSignExtension owner c σ) η ζ) (x i.1,l i) =
    (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ, ∏ i : {i : Fin n // block i = c},
        recordCellDensity (mixedLaw true k (componentSignExtension owner c σ) η ζ) (x i.1,l i) := by
  dsimp only
  rw [← mixedDensity_block_average_restrict k hk x c l false η ζ hη hζ,
    ← mixedDensity_block_average_restrict k hk x c l true η ζ hη hζ]
  congr 1
  apply signPrior_small_block_matching _ _ hcard
  intro i
  simp only [recordCellDensity, ← Finset.mul_sum]
  rw [(calib_singletons_spec k hk).1 η ζ hη hζ (l i).1 (l i).2 (x i.1)]

/-- [Exact singleton matching also removes every fair component of at most
one original record; its comparator average is a constant-prior average. [the documented result](goal) Under [the stated assumptions](hyp:x,l,ht,hδ,hcard). Under [the stated assumptions](hyp:hk). -/
-- @node: fairDensity_small_block_matching
lemma fairDensity_small_block_matching {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → Covariate) (c : SignComponentBlock k x)
    (l : {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} → Bool × Bool)
    (t δ : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ calibEps)
    (hcard : Fintype.card {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} ≤ 1) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ, ∏ i : {i : Fin n // block i = c},
        recordCellDensity (fairLaw k (componentSignExtension owner c σ) t δ) (x i.1,l i) =
    (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ : {s : Fin (k+1) // owner s = c} → Bool,
        ∏ i : {i : Fin n // block i = c},
          recordCellDensity (fairComparator k t δ) (x i.1,l i) := by
  dsimp only
  rw [← fairDensity_block_average_restrict k hk x c l t δ ht hδ]
  have he (i : {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c}) :
      (∑ σ : Fin (k+1) → Bool, recordCellDensity (fairLaw k σ t δ) (x i.1,l i)) =
        ∑ _σ : Fin (k+1) → Bool, recordCellDensity (fairComparator k t δ) (x i.1,l i) := by
    have hm := (calib_singletons_spec k hk).2 t δ ht hδ (l i).1 (l i).2 (x i.1)
    have hc : (Fintype.card (Fin (k+1) → Bool) : ℝ) ≠ 0 := by positivity
    simp only [recordCellDensity, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hm' := (div_eq_iff hc).mp (show
      (∑ σ : Fin (k+1) → Bool, (fairLaw k σ t δ).cells (l i).1 (l i).2 (x i.1)) /
        (Fintype.card (Fin (k+1) → Bool) : ℝ) =
          (fairComparator k t δ).cells (l i).1 (l i).2 (x i.1) from by
            simpa only [div_eq_mul_inv, mul_comm] using hm)
    rw [hm']
    ring
  rw [signPrior_small_block_matching _ _ hcard he]
  simp [← mul_assoc, Fintype.card_ne_zero]

/-- [The record fiber is empty for unowned signs and otherwise has exactly
the support cardinality of its graph component. [the documented result](goal) -/
-- @node: signComponent_record_card
lemma signComponent_record_card {n : ℕ} (k : ℕ) (x : Fin n → Covariate)
    (c : SignComponentBlock k x) :
    Fintype.card {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} =
      match c with
      | none => 0
      | some v => v.supp.toFinset.card := by
  rw [Fintype.card_subtype]
  cases c with
  | none => simp
  | some v =>
    congr 1
    ext i
    simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

end CausalSmith.Stat.LogoddsLowsmoothFrontier
