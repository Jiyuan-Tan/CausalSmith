module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedSingletonMatching
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Factorization of the finite endpoint-sign prior

Original records sharing an endpoint sign are adjacent in the cell graph.
Distinct connected components therefore use disjoint signs. Regrouping the
uniform prior by sign ownership factors arbitrary component likelihoods.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier
attribute [local instance] Classical.propDecidable

/-- [The two endpoint indices on which a record depends. -/
-- @node: recordSignEndpoints
def recordSignEndpoints (k : ℕ) (x : Covariate) : Finset ℕ :=
  {cellIndex k x, cellIndex k x + 1}

/-- Equal and adjacent cells join distinct original records. -/
-- @node: originalRecordSignGraph
def originalRecordSignGraph {n : ℕ} (k : ℕ) (x : Fin n → Covariate) :
    SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ cellIndex k (x i) ≤ cellIndex k (x j) + 1 ∧
    cellIndex k (x j) ≤ cellIndex k (x i) + 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A shared latent endpoint forces the records into the same connected component. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hi,hj) hold, and [the stated conclusion follows](goal). -/
-- @node: shared_sign_records_reachable
lemma shared_sign_records_reachable {n : ℕ} (k : ℕ) (x : Fin n → Covariate)
    (i j : Fin n) (s : ℕ) (hi : s ∈ recordSignEndpoints k (x i))
    (hj : s ∈ recordSignEndpoints k (x j)) :
    (originalRecordSignGraph k x).Reachable i j := by
  by_cases hij : i = j
  · subst j; exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    refine ⟨hij, ?_, ?_⟩
    all_goals
      simp only [recordSignEndpoints, Finset.mem_insert, Finset.mem_singleton] at hi hj
      omega

/-- [Distinct latent-sign components have disjoint endpoint sets.](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:hij). -/
-- @node: distinct_components_disjoint_signs
lemma distinct_components_disjoint_signs {n : ℕ} (k : ℕ) (x : Fin n → Covariate)
    (i j : Fin n) (hij : ¬ (originalRecordSignGraph k x).Reachable i j) :
    Disjoint (recordSignEndpoints k (x i)) (recordSignEndpoints k (x j)) := by
  apply Finset.disjoint_left.mpr
  intro s hi hj
  exact hij (shared_sign_records_reachable k x i j s hi hj)

/-- [Regrouping independent uniform signs into arbitrary ownership fibers factors
all component averages, including empty fibers for unused signs. [the documented result](goal) Under [the stated assumptions](hyp:F). -/
-- @node: signPrior_fiber_factorization
lemma signPrior_fiber_factorization {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (owner : ι → κ)
    (F : ∀ c : κ, ({s : ι // owner s = c} → Bool) → ℝ) :
    (Fintype.card (ι → Bool) : ℝ)⁻¹ *
      (∑ σ : ι → Bool, ∏ c : κ, F c (fun s => σ s.1)) =
    ∏ c : κ, (Fintype.card ({s : ι // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ : {s : ι // owner s = c} → Bool, F c σ := by
  classical
  let e : (ι → Bool) ≃ (∀ c : κ, {s : ι // owner s = c} → Bool) :=
    Equiv.piCongrFiberwise (fun _ => Equiv.refl _)
  have hsum : (∑ σ : ι → Bool, ∏ c : κ, F c (fun s => σ s.1)) =
      ∏ c : κ, ∑ σ : {s : ι // owner s = c} → Bool, F c σ := by
    calc
      _ = ∑ σ : (∀ c : κ, {s : ι // owner s = c} → Bool), ∏ c, F c (σ c) :=
        e.sum_comp (fun σ => ∏ c, F c (σ c))
      _ = _ := (Fintype.prod_sum F).symm
  have hcard : (Fintype.card (ι → Bool) : ℝ) =
      ∏ c : κ, (Fintype.card ({s : ι // owner s = c} → Bool) : ℝ) := by
    rw [Fintype.card_congr e, Fintype.card_pi, Nat.cast_prod]
  rw [hsum, hcard, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]

/-- Extend one component's signs arbitrarily outside its ownership fiber. -/
-- @node: componentSignExtension
def componentSignExtension {ι κ : Type*} [DecidableEq κ] (owner : ι → κ)
    (c : κ) (σ : {s : ι // owner s = c} → Bool) (s : ι) : Bool :=
  if h : owner s = c then σ ⟨s, h⟩ else false

/-- Likelihood products factor under the finite prior when each record uses only
signs assigned to its block. This allows dependence between records in a block. [the documented result](goal) Under [the stated assumptions](hyp:f,hlocal). -/
-- @node: signPrior_likelihood_factorization
lemma signPrior_likelihood_factorization {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
    (owner : ι → κ) (block : ν → κ) (f : ν → (ι → Bool) → ℝ)
    (hlocal : ∀ i σ τ, (∀ s, owner s = block i → σ s = τ s) → f i σ = f i τ) :
    (Fintype.card (ι → Bool) : ℝ)⁻¹ * (∑ σ : ι → Bool, ∏ i : ν, f i σ) =
      ∏ c : κ, (Fintype.card ({s : ι // owner s = c} → Bool) : ℝ)⁻¹ *
        ∑ σ : {s : ι // owner s = c} → Bool,
          ∏ i ∈ Finset.univ.filter (fun i => block i = c),
            f i (componentSignExtension owner c σ) := by
  classical
  let F (c : κ) (σ : {s : ι // owner s = c} → Bool) : ℝ :=
    ∏ i ∈ Finset.univ.filter (fun i => block i = c),
      f i (componentSignExtension owner c σ)
  have hprod (σ : ι → Bool) : (∏ i : ν, f i σ) =
      ∏ c : κ, F c (fun s => σ s.1) := by
    rw [← Finset.prod_fiberwise Finset.univ block (fun i => f i σ)]
    apply Finset.prod_congr rfl
    intro c hc
    apply Finset.prod_congr rfl
    intro i hi
    apply hlocal
    intro s hs
    have hic := (Finset.mem_filter.mp hi).2
    simp [componentSignExtension, hs, hic]
  simp_rw [hprod]
  exact signPrior_fiber_factorization owner F

/-- A record's sign field depends only on its two endpoint signs. Under the stated assumptions. [The stated hypotheses](hyp:h) hold, and [the stated conclusion follows](goal). -/
-- @node: signFieldZ_endpoint_congr
lemma signFieldZ_endpoint_congr (k : ℕ) (σ τ : Fin (k+1) → Bool) (x : Covariate)
    (h : ∀ j ∈ recordSignEndpoints k x, endpointSign k σ j = endpointSign k τ j) :
    signFieldZ k σ x = signFieldZ k τ x := by
  unfold signFieldZ
  dsimp only
  rw [h (cellIndex k x) (by simp [recordSignEndpoints]),
    h (cellIndex k x + 1) (by simp [recordSignEndpoints])]

/-- [Both mixed hypotheses use precisely the same local endpoint support.](goal) Under [the stated assumptions](hyp:x,h). -/
-- @node: mixedCells_endpoint_congr
lemma mixedCells_endpoint_congr (b : Bool) (k : ℕ) (σ τ : Fin (k+1) → Bool)
    (η ζ : ℝ) (a y : Bool) (x : Covariate)
    (h : ∀ j ∈ recordSignEndpoints k x, endpointSign k σ j = endpointSign k τ j) :
    mixedCells b k σ η ζ a y x = mixedCells b k τ η ζ a y x := by
  unfold mixedCells
  rw [signFieldZ_endpoint_congr k σ τ x h]

/-- [The random fair family and the comparator use no signs outside these endpoints.](goal) Under [the stated assumptions](hyp:x,h). -/
-- @node: fairCells_endpoint_congr
lemma fairCells_endpoint_congr (b : Bool) (k : ℕ) (σ τ : Fin (k+1) → Bool)
    (t δ : ℝ) (a y : Bool) (x : Covariate)
    (h : ∀ j ∈ recordSignEndpoints k x, endpointSign k σ j = endpointSign k τ j) :
    fairCells b k σ t δ a y x = fairCells b k τ t δ a y x := by
  unfold fairCells
  rw [signFieldZ_endpoint_congr k σ τ x h]

/-- [Local cell likelihoods factor whenever each endpoint is owned by its record's block.](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:hcell,howner). -/
-- @node: recordCells_prior_factorization
lemma recordCells_prior_factorization {n k : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ] (x : Fin n → Covariate)
    (owner : Fin (k+1) → κ) (block : Fin n → κ)
    (cell : Fin n → (Fin (k+1) → Bool) → ℝ)
    (hcell : ∀ i σ τ,
      (∀ j ∈ recordSignEndpoints k (x i), endpointSign k σ j = endpointSign k τ j) →
      cell i σ = cell i τ)
    (howner : ∀ i j, j ∈ recordSignEndpoints k (x i) →
      owner ⟨min j k, Nat.lt_succ_of_le (min_le_right _ _)⟩ = block i) :
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      (∑ σ : Fin (k+1) → Bool, ∏ i : Fin n, cell i σ) =
    ∏ c : κ, (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ : {s : Fin (k+1) // owner s = c} → Bool,
        ∏ i ∈ Finset.univ.filter (fun i => block i = c),
          cell i (componentSignExtension owner c σ) := by
  apply signPrior_likelihood_factorization owner block cell
  intro i σ τ hsign
  apply hcell
  intro j hj
  unfold endpointSign
  rw [hsign _ (howner i j hj)]

/-- [The conditional likelihood of the actual mixed formula factors without
replacing original records or asserting independence inside a block. [the documented result](goal) Under [the stated assumptions](hyp:x,howner). -/
-- @node: mixedCells_prior_factorization
lemma mixedCells_prior_factorization {n k : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ] (b : Bool) (η ζ : ℝ)
    (x : Fin n → Covariate) (a y : Fin n → Bool)
    (owner : Fin (k+1) → κ) (block : Fin n → κ)
    (howner : ∀ i j, j ∈ recordSignEndpoints k (x i) →
      owner ⟨min j k, Nat.lt_succ_of_le (min_le_right _ _)⟩ = block i) :
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      (∑ σ : Fin (k+1) → Bool, ∏ i : Fin n, 4*mixedCells b k σ η ζ (a i) (y i) (x i)) =
    ∏ c : κ, (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ : {s : Fin (k+1) // owner s = c} → Bool,
        ∏ i ∈ Finset.univ.filter (fun i => block i = c),
          4*mixedCells b k (componentSignExtension owner c σ) η ζ (a i) (y i) (x i) := by
  apply recordCells_prior_factorization x owner block _ _ howner
  intro i σ τ h
  rw [mixedCells_endpoint_congr b k σ τ η ζ (a i) (y i) (x i) h]

/-- [The same exact finite-prior factorization holds for the actual fair cells,
including the deterministic comparator and both amplitude axes. [the documented result](goal) Under [the stated assumptions](hyp:x,howner). -/
-- @node: fairCells_prior_factorization
lemma fairCells_prior_factorization {n k : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ] (b : Bool) (t δ : ℝ)
    (x : Fin n → Covariate) (a y : Fin n → Bool)
    (owner : Fin (k+1) → κ) (block : Fin n → κ)
    (howner : ∀ i j, j ∈ recordSignEndpoints k (x i) →
      owner ⟨min j k, Nat.lt_succ_of_le (min_le_right _ _)⟩ = block i) :
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      (∑ σ : Fin (k+1) → Bool, ∏ i : Fin n, 4*fairCells b k σ t δ (a i) (y i) (x i)) =
    ∏ c : κ, (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ : {s : Fin (k+1) // owner s = c} → Bool,
        ∏ i ∈ Finset.univ.filter (fun i => block i = c),
          4*fairCells b k (componentSignExtension owner c σ) t δ (a i) (y i) (x i) := by
  apply recordCells_prior_factorization x owner block _ _ howner
  intro i σ τ h
  rw [fairCells_endpoint_congr b k σ τ t δ (a i) (y i) (x i) h]

/-- [Components plus one empty record block accommodate unused endpoint signs. -/
-- @node: SignComponentBlock
abbrev SignComponentBlock {n : ℕ} (k : ℕ) (x : Fin n → Covariate) :=
  Option (originalRecordSignGraph k x).ConnectedComponent

/-- The finite component quotient supports literal finite sign averages.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: signComponentBlock_fintype
instance signComponentBlock_fintype {n : ℕ} (k : ℕ) (x : Fin n → Covariate) :
    Fintype (SignComponentBlock k x) := Fintype.ofFinite _

/-- [Assign a used endpoint sign to any incident record's component; unused signs
are assigned to the empty block. Reachability makes this choice harmless. -/
-- @node: signComponentOwner
def signComponentOwner {n : ℕ} (k : ℕ) (x : Fin n → Covariate)
    (s : Fin (k+1)) : SignComponentBlock k x :=
  if h : ∃ i : Fin n, (s : ℕ) ∈ recordSignEndpoints k (x i) then
    some ((originalRecordSignGraph k x).connectedComponentMk (Classical.choose h))
  else none

/-- Each record's two signs are owned by its actual graph component. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hk,hj) hold, and [the stated conclusion follows](goal). -/
-- @node: signComponentOwner_incident
lemma signComponentOwner_incident {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → Covariate) (i : Fin n) (j : ℕ)
    (hj : j ∈ recordSignEndpoints k (x i)) :
    signComponentOwner k x ⟨min j k, Nat.lt_succ_of_le (min_le_right _ _)⟩ =
      some ((originalRecordSignGraph k x).connectedComponentMk i) := by
  classical
  have hjk : j ≤ k := by
    have hi := cellIndex_lt k hk (x i)
    simp only [recordSignEndpoints, Finset.mem_insert, Finset.mem_singleton] at hj
    omega
  let s : Fin (k+1) := ⟨min j k, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hs : (s : ℕ) = j := min_eq_left hjk
  have hex : ∃ i' : Fin n, (s : ℕ) ∈ recordSignEndpoints k (x i') :=
    ⟨i, by simpa only [hs] using hj⟩
  change signComponentOwner k x s = _
  rw [signComponentOwner, dif_pos hex]
  congr 1
  exact SimpleGraph.ConnectedComponent.sound
    (shared_sign_records_reachable k x (Classical.choose hex) i (s : ℕ)
      (Classical.choose_spec hex) (by simpa only [hs] using hj))

/-- [Conditional finite-prior likelihoods factor over the actual connected
components. The unused-sign block contributes an empty record product equal to one. [the documented result](goal) Under [the stated assumptions](hyp:x,hcell). Under [the stated assumptions](hyp:hk). -/
-- @node: recordCells_component_factorization
lemma recordCells_component_factorization {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → Covariate) (cell : Fin n → (Fin (k+1) → Bool) → ℝ)
    (hcell : ∀ i σ τ,
      (∀ j ∈ recordSignEndpoints k (x i), endpointSign k σ j = endpointSign k τ j) →
      cell i σ = cell i τ) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      (∑ σ : Fin (k+1) → Bool, ∏ i : Fin n, cell i σ) =
    ∏ c : SignComponentBlock k x,
      (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ : {s : Fin (k+1) // owner s = c} → Bool,
        ∏ i ∈ Finset.univ.filter (fun i => block i = c),
          cell i (componentSignExtension owner c σ) := by
  classical
  exact recordCells_prior_factorization x (signComponentOwner k x)
    (fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)) cell hcell
    (signComponentOwner_incident k hk x)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
