import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Basic
import Causalean.Stat.Minimax.FiniteSquaredLoss.Saddle
import Mathlib.Order.SaddlePoint

/-! Compact finite-state game separation and saddle-point scaffolding. -/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

variable {K n : ℕ} (c : Contrast ℝ K)

/-- A least-favorable response-count prior and an optimal orbit procedure form a saddle. -/
def HasOrbitSaddle (n : ℕ) (c : Contrast ℝ K) : Prop :=
  ∃ (q : OrbitProcedure K n c)
      (nu : Causalean.Experimentation.DesignBased.FiniteDesign (CountVec K n)),
    (∀ m, orbitRisk c q m ≤ orbitGameValue K n c) ∧
    (∀ q', orbitGameValue K n c ≤ nu.E (fun m => orbitRisk c q' m))

-- @node: finite_orbit_game_has_saddle
/-- [the finite response-type orbit game admits optimal mixed strategies for both players with a common saddle value](goal). -/
lemma finite_orbit_game_has_saddle : HasOrbitSaddle n c := by
  classical
  let X : AllocVec K n → Type := fun r => ObsVec r
  let l : ℝ := -Lc c / 2
  let u : ℝ := Lc c / 2
  have hK : K ≠ 0 := by
    intro hK
    apply c.nonzero
    funext a
    exact Fin.elim0 (hK ▸ a)
  letI : Nonempty (Arm K) :=
    Fintype.card_pos_iff.mp (by simpa using Nat.pos_of_ne_zero hK)
  letI : Nonempty (CountVec K n) :=
    ⟨scheduleCounts (fun _ _ => false)⟩
  let a₀ : Arm K := Classical.choice inferInstance
  let r₀ : AllocVec K n :=
    ⟨fun a => if a = a₀ then ⟨n, Nat.lt_succ_self n⟩ else 0, by
      rw [Finset.sum_eq_single a₀]
      · simp
      · intro b _ hba
        simp [hba]
      · simp⟩
  letI : Nonempty (AllocVec K n) := ⟨r₀⟩
  have hlu : l ≤ u := by
    dsimp [l, u]
    have hLc : 0 ≤ Lc c := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  let P : CountVec K n → ∀ r : AllocVec K n, X r → ℝ :=
    fun m r x => (orbitLik m r x : ℝ)
  let tau : CountVec K n → ℝ := tauCount c
  have hP : ∀ m r x, 0 ≤ P m r x := by
    intro m r x
    change (0 : ℝ) ≤ ((orbitLik m r x : ℚ) : ℝ)
    exact_mod_cast orbitLik_nonneg m r x
  let e : OrbitProcedure K n c ≃
      Causalean.Stat.Minimax.FiniteSquaredLoss.Procedure X l u :=
    { toFun := fun q => ⟨q.1, q.2⟩
      invFun := fun q => (q.design, q.decision)
      left_inv := fun _ => rfl
      right_inv := fun q => by cases q; rfl }
  have hvalue :
      Causalean.Stat.minimaxValue
          (Causalean.Stat.Minimax.FiniteSquaredLoss.risk P tau :
            Causalean.Stat.Minimax.FiniteSquaredLoss.Procedure X l u →
              CountVec K n → ℝ) =
        orbitGameValue K n c := by
    unfold orbitGameValue Causalean.Stat.minimaxValue
    rw [← e.iInf_comp]
    rfl
  obtain ⟨qstar, deltastar, nu, hupper, hlower⟩ :=
    Causalean.Stat.Minimax.FiniteSquaredLoss.finite_bounded_squared_loss_has_saddle
      P tau hlu hP
  refine ⟨(qstar, deltastar), nu, ?_, ?_⟩
  · intro m
    change Causalean.Stat.Minimax.FiniteSquaredLoss.risk P tau
        ⟨qstar, deltastar⟩ m ≤ orbitGameValue K n c
    rw [← hvalue]
    exact hupper m
  · intro q'
    have h := hlower (e q')
    rw [hvalue] at h
    exact h

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
