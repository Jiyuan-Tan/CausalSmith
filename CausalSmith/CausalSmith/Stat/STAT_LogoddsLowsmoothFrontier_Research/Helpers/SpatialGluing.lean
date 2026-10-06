module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedSingletonMatching
public import Mathlib.Topology.LocallyFinite

/-! # Shared-endpoint spatial gluing

Closed cells cover the covariate interval. Matching endpoint values allow
continuous local formulas to pass through the discontinuous cell selector.
-/
public section
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [On a closed cell the selector is its index, except possibly at its right endpoint.](goal) Under [the stated assumptions](hyp:hj,x). Under [the stated assumptions](hyp:hx). -/
-- @node: cellIndex_closed_cell
lemma cellIndex_closed_cell (k j : ℕ) (hj : j < k) (x : Covariate)
    (hx : (k : ℝ) * (x : ℝ) ∈ Set.Icc (j : ℝ) (j + 1)) :
    cellIndex k x = j ∨
      (cellIndex k x = j + 1 ∧ (k : ℝ) * (x : ℝ) = j + 1) := by
  have hk : 1 ≤ k := by omega
  have hlo : j ≤ (⌊(k : ℝ) * (x : ℝ)⌋ : ℤ).toNat := by
    have h : (j : ℤ) ≤ ⌊(k : ℝ) * (x : ℝ)⌋ := Int.le_floor.mpr (by exact_mod_cast hx.1)
    omega
  have hlow : j ≤ cellIndex k x := by
    unfold cellIndex
    omega
  have hcoord := cellCoord_mem_unit k hk x
  have hhigh : cellIndex k x ≤ j + 1 := by
    have h : (cellIndex k x : ℝ) ≤ (j + 1 : ℕ) := by
      dsimp [cellCoord] at hcoord
      push_cast
      linarith [hx.2, hcoord.1]
    exact_mod_cast h
  by_cases he : cellIndex k x = j
  · exact Or.inl he
  · have he' : cellIndex k x = j + 1 := by omega
    refine Or.inr ⟨he', ?_⟩
    dsimp [cellCoord] at hcoord
    rw [he'] at hcoord
    push_cast at hcoord
    linarith [hx.2, hcoord.1]

/-- A finite chain of continuous local profiles glues when adjacent endpoint values agree. No matching derivatives at endpoints are required. the documented result Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hk,hc,he) hold, and [the stated conclusion follows](goal). -/
-- @node: continuous_cell_profile
lemma continuous_cell_profile (k : ℕ) (hk : 1 ≤ k) (F : ℕ → ℝ → ℝ)
    (hc : ∀ j < k, ContinuousOn (F j) (Set.Icc (0 : ℝ) 1))
    (he : ∀ j, j + 1 < k → F j 1 = F (j + 1) 0) :
    Continuous (fun x : Covariate => F (cellIndex k x) (cellCoord k x)) := by
  let S (j : Fin k) : Set Covariate :=
    {x | (k : ℝ) * (x : ℝ) ∈ Set.Icc (j : ℝ) (j + 1)}
  have hclosed : ∀ j, IsClosed (S j) := by
    intro j
    exact isClosed_Icc.preimage (by fun_prop)
  have hcover : (⋃ j, S j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    refine Set.mem_iUnion.mpr ⟨⟨cellIndex k x, cellIndex_lt k hk x⟩, ?_⟩
    have h := cellCoord_mem_unit k hk x
    change (k : ℝ) * (x : ℝ) ∈ Set.Icc (cellIndex k x : ℝ) (cellIndex k x+1)
    dsimp [cellCoord] at h
    constructor <;> linarith [h.1,h.2]
  apply (locallyFinite_of_finite S).continuous hcover hclosed
  intro j
  have hmap : Continuous (fun x : Covariate => (k : ℝ) * (x : ℝ)-(j : ℝ)) := by
    fun_prop
  have hm : Set.MapsTo (fun x : Covariate => (k : ℝ) * (x : ℝ)-(j : ℝ))
      (S j) (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  apply ((hc j j.isLt).comp hmap.continuousOn hm).congr
  intro x hx
  change F (cellIndex k x) (cellCoord k x) = F j ((k : ℝ) * (x : ℝ)-(j : ℝ))
  rcases cellIndex_closed_cell k j j.isLt x hx with hi | ⟨hi,hxend⟩
  · simp only [hi, cellCoord]
  · have hnext : (j : ℕ)+1 < k := by
      rw [← hi]
      exact cellIndex_lt k hk x
    have hu : cellCoord k x = 0 := by
      simp [cellCoord, hi, hxend]
    have hv : (k : ℝ) * (x : ℝ)-(j : ℝ) = 1 := by linarith
    rw [hi, hu, hv]
    exact (he j hnext).symm

/-- [The shared endpoint sign field is continuous for every realization.](goal) Under [the stated assumptions](hyp:hk). -/
-- @node: signFieldZ_continuous
lemma signFieldZ_continuous (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k + 1) → Bool) :
    Continuous (signFieldZ k σ) := by
  apply continuous_cell_profile k hk
    (fun j u => endpointSign k σ j * Real.cos (Real.pi*u/2) +
      endpointSign k σ (j + 1) * Real.sin (Real.pi*u/2))
  · intro j hj
    fun_prop
  · intro j hj
    simp

/-- A periodic endpoint profile remains continuous after the cell-coordinate selector, despite that selector jumping from one to zero. the documented result Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hk,hf,hend) hold, and [the stated conclusion follows](goal). -/
-- @node: continuous_cellCoord_comp
lemma continuous_cellCoord_comp (k : ℕ) (hk : 1 ≤ k) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (hend : f 1 = f 0) :
    Continuous (fun x : Covariate => f (cellCoord k x)) := by
  exact continuous_cell_profile k hk (fun _ => f) (fun _ _ => hf) (fun _ _ => hend)

/-- [Mixed local tables glue because their root has equal endpoint values and
the two adjacent sign profiles share the same sign there. [the documented result](goal) Under [the stated assumptions](hyp:hk,hη,hζ). Under [the stated assumptions](hyp:hs). -/
-- @node: mixedCells_continuous_of_smooth
lemma mixedCells_continuous_of_smooth (ε : ℝ) (hs : CalibrationSmooth ε)
    (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k + 1) → Bool) (η ζ : ℝ)
    (hη : |η| ≤ ε) (hζ : |ζ| ≤ ε) (b a y : Bool) :
    Continuous (mixedCells b k σ η ζ a y) := by
  let s (j : ℕ) : Bool × Bool :=
    (σ ⟨min j k, Nat.lt_succ_of_le (min_le_right _ _)⟩,
     σ ⟨min (j + 1) k, Nat.lt_succ_of_le (min_le_right _ _)⟩)
  change Continuous (fun x : Covariate =>
    localMixedCell b (s (cellIndex k x)) a y ![η,ζ,cellCoord k x])
  apply continuous_cell_profile k hk (fun j u => localMixedCell b (s j) a y ![η,ζ,u])
  · intro j hj
    have hm : Continuous (fun u : ℝ => ![η,ζ,u]) := by fun_prop
    exact (hs.2.2.1 b (s j) a y).continuousOn.comp hm.continuousOn
      (by intro u hu; exact ⟨hη,hζ,hu⟩)
  · intro j hj
    simp [localMixedCell, localSignField, s, ← mixedRoot_endpoints]

/-- [Both fair local tables glue: their centers agree at the two endpoints,
and the random risks use the same shared sign. [the documented result](goal) Under [the stated assumptions](hyp:hk,ht,hδ). Under [the stated assumptions](hyp:hs). -/
-- @node: fairCells_continuous_of_smooth
lemma fairCells_continuous_of_smooth (ε : ℝ) (hs : CalibrationSmooth ε)
    (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k + 1) → Bool) (t δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |δ| ≤ ε) (b a y : Bool) :
    Continuous (fairCells b k σ t δ a y) := by
  let s (j : ℕ) : Bool × Bool :=
    (σ ⟨min j k, Nat.lt_succ_of_le (min_le_right _ _)⟩,
     σ ⟨min (j + 1) k, Nat.lt_succ_of_le (min_le_right _ _)⟩)
  change Continuous (fun x : Covariate =>
    localFairCell b (s (cellIndex k x)) a y ![t,δ,cellCoord k x])
  apply continuous_cell_profile k hk (fun j u => localFairCell b (s j) a y ![t,δ,u])
  · intro j hj
    have hm : Continuous (fun u : ℝ => ![t,δ,u]) := by fun_prop
    exact (hs.2.2.2 b (s j) a y).continuousOn.comp hm.continuousOn
      (by intro u hu; exact ⟨ht,hδ,hu⟩)
  · intro j hj
    simp [localFairCell, localSignField, s, ← fairRoot_endpoints]

end CausalSmith.Stat.LogoddsLowsmoothFrontier
