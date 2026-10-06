module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentInteriorSingleton

/-! Boundary disclosure geometry for the exact conditional singleton calculation. -/
public section
set_option linter.style.whitespace false
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The paired tent is zero at every coarse grid boundary. This statement assumes [the hK condition](hyp:hK), [the hi condition](hyp:hi). [This is the stated conclusion](goal). -/
-- @node: coarseTent_boundaryNode_zero
lemma coarseTent_boundaryNode_zero (K M : ℕ) (hK : 0 < K)
    (i : Fin (K+1)) (hi : boundaryNode K M i) (σ : Fin (M/2) → Bool) :
    coarseTent M σ ((i:ℝ)/K) = 0 := by
  have he : i.val*M = K*(i.val*M/K) := by
    have hh := Nat.mod_add_div (i.val*M) K
    dsimp [boundaryNode] at hi
    omega
  have hr : (M:ℝ)*((i:ℝ)/K) = (i.val*M/K:ℕ) := by
    have hc : (i:ℝ)*(M:ℝ) = (K:ℝ)*(i.val*M/K:ℕ) := by exact_mod_cast he
    field_simp
    nlinarith
  have ht (q r : ℕ) : tentBase ((q:ℝ)-(r:ℝ)) = 0 := by
    by_cases h : q ≤ r
    · have hh : (q:ℝ) ≤ r := by exact_mod_cast h
      unfold tentBase
      split <;> rename_i h'
      · have hz : (q:ℝ)-(r:ℝ) = 0 := by linarith [h'.1]
        simp [hz]
      · rfl
    · have hh : (r:ℝ)+1 ≤ q := by exact_mod_cast (show r+1 ≤ q by omega)
      unfold tentBase
      split <;> rename_i h'
      · have hz : (q:ℝ)-(r:ℝ) = 1 := by linarith [h'.2]
        simp [hz]
      · rfl
  unfold coarseTent
  rw [hr]
  apply Finset.sum_eq_zero
  intro j _
  have h0 := ht (i.val*M/K) (2*j.val)
  have h1 := ht (i.val*M/K) (2*j.val+1)
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h0 h1
  rw [h0, h1]
  ring

/-- Two distinct coarse-boundary nodes cannot both be active at one covariate. This statement assumes [the hM condition](hyp:hM), [the hKM condition](hyp:hKM), [the hi condition](hyp:hi), [the hj condition](hyp:hj), [the hfi condition](hyp:hfi), [the hfj condition](hyp:hfj). [This is the stated conclusion](goal). -/
-- @node: active_boundaryNode_unique
lemma active_boundaryNode_unique (K M : ℕ) (hM : 0 < M) (hKM : 2*M ≤ K)
    (x : unitInterval) (i j : Fin (K+1))
    (hi : boundaryNode K M i) (hj : boundaryNode K M j)
    (hfi : frameCoord K i x ≠ 0) (hfj : frameCoord K j x ≠ 0) : i = j := by
  have hK : 0 < K := by omega
  have hdi := abs_lt.mp (frameCoord_nonzero_distance K hK i x hfi)
  have hdj := abs_lt.mp (frameCoord_nonzero_distance K hK j x hfj)
  have hei : i.val*M = K*(i.val*M/K) := by
    have := Nat.mod_add_div (i.val*M) K
    dsimp [boundaryNode] at hi
    omega
  have hej : j.val*M = K*(j.val*M/K) := by
    have := Nat.mod_add_div (j.val*M) K
    dsimp [boundaryNode] at hj
    omega
  have hri : (i:ℝ)*(M:ℝ) = (K:ℝ)*(i.val*M/K:ℕ) := by exact_mod_cast hei
  have hrj : (j:ℝ)*(M:ℝ) = (K:ℝ)*(j.val*M/K:ℕ) := by exact_mod_cast hej
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hk : 2*(M:ℝ) ≤ K := by exact_mod_cast hKM
  have heq : i.val*M/K = j.val*M/K := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have hh : (i.val*M/K:ℕ) + (1:ℝ) ≤ (j.val*M/K:ℕ) := by
        exact_mod_cast (show i.val*M/K+1 ≤ j.val*M/K by omega)
      nlinarith
    · have hh : (j.val*M/K:ℕ) + (1:ℝ) ≤ (i.val*M/K:ℕ) := by
        exact_mod_cast (show j.val*M/K+1 ≤ i.val*M/K by omega)
      nlinarith
  apply Fin.ext
  nlinarith [hei, hej]

end CausalSmith.Stat.FinitepHomogeneityDensegamma
