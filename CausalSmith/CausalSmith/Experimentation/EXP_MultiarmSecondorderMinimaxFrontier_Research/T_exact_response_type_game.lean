import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.Symmetrization
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.FiniteGame
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.OrbitCounting

/-! Exact lossless reduction of the labeled game to response-type orbits. -/

open scoped BigOperators
open Finset Set

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

private noncomputable def pointFiniteDesign {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    Causalean.Experimentation.DesignBased.FiniteDesign Ω := by
  classical
  exact
    { p := fun x => if x = Classical.choice inferInstance then 1 else 0
      p_nonneg := fun x => by split <;> positivity
      p_sum := by simp }

private lemma scheduleCounts_surjective {K n : ℕ} :
    Function.Surjective (scheduleCounts : Schedule K n → CountVec K n) := by
  intro m
  obtain ⟨z, hz⟩ := exists_fun_card_fiber_eq
    (C := RespType K) (fun t => (m.1 t : ℕ)) m.2
  refine ⟨z, Subtype.ext (funext fun t => Fin.ext ?_)⟩
  simpa [scheduleCounts, rawScheduleCount, ← Fintype.card_subtype] using hz t

private lemma labeledRisk_nonneg {K n : ℕ} (c : Contrast ℝ K)
    (p : Procedure K n c) (z : Schedule K n) : 0 ≤ labeledRisk c p z :=
  p.1.mse_nonneg _ _

private lemma orbitRisk_nonneg {K n : ℕ} (c : Contrast ℝ K)
    (q : OrbitProcedure K n c) (m : CountVec K n) : 0 ≤ orbitRisk c q m := by
  classical
  unfold orbitRisk
  apply Finset.sum_nonneg
  intro r _
  apply mul_nonneg (q.1.p_nonneg r)
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg
  · change (0 : ℝ) ≤ ((orbitLik m r x : ℚ) : ℝ)
    exact_mod_cast orbitLik_nonneg m r x
  · exact sq_nonneg _

private lemma permutation_average_le_labeledWorstCase {K n : ℕ}
    (c : Contrast ℝ K) (p : Procedure K n c) (z : Schedule K n) : by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  exact (Fintype.card (Equiv.Perm (Unit n)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Unit n), labeledRisk c p (permuteSchedule σ z) ≤
    Causalean.Stat.worstCaseRisk (fun p z => labeledRisk c p z) p := by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  let W := Causalean.Stat.worstCaseRisk (fun p z => labeledRisk c p z) p
  have hterm (σ : Equiv.Perm (Unit n)) :
      labeledRisk c p (permuteSchedule σ z) ≤ W :=
    Causalean.Stat.le_worstCaseRisk (Set.finite_range _).bddAbove _
  calc
    (Fintype.card (Equiv.Perm (Unit n)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Unit n), labeledRisk c p (permuteSchedule σ z) ≤
      (Fintype.card (Equiv.Perm (Unit n)) : ℝ)⁻¹ *
        ∑ _σ : Equiv.Perm (Unit n), W := by
          gcongr with σ
          exact hterm σ
    _ = W := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card (Equiv.Perm (Unit n)) : ℝ) ≠ 0 := by positivity
      field_simp

private lemma rhoN_eq_orbitGameValue (K n : ℕ) (c : Contrast ℝ K)
    (hK : AdmissibleArmCount K) : rhoN K n c = orbitGameValue K n c := by
  classical
  have hKpos : 0 < K := by unfold AdmissibleArmCount at hK; omega
  letI : Nonempty (Arm K) := Fintype.card_pos_iff.mp (by simpa using hKpos)
  letI : Nonempty (Assign K n) := Pi.instNonempty
  letI : Nonempty (Schedule K n) := Pi.instNonempty
  let a0 : Arm K := Classical.choice inferInstance
  let r0 : AllocVec K n :=
    ⟨fun a => if a = a0 then ⟨n, Nat.lt_succ_self n⟩ else 0, by
      rw [Finset.sum_eq_single a0]
      · simp
      · intro b _ hba; simp [hba]
      · simp⟩
  letI : Nonempty (AllocVec K n) := ⟨r0⟩
  letI : Nonempty (CountVec K n) := ⟨scheduleCounts (Classical.choice inferInstance)⟩
  let zeroEst : Estimator K n c := fun _ _ => ⟨0, by
    have hLc : 0 ≤ Lc c := Finset.sum_nonneg fun _ _ => abs_nonneg _
    constructor <;> linarith⟩
  letI : Nonempty (Procedure K n c) := ⟨(pointFiniteDesign, zeroEst)⟩
  let zeroOrbitEst : OrbitEstimator K n c := fun _ _ => ⟨0, by
    have hLc : 0 ≤ Lc c := Finset.sum_nonneg fun _ _ => abs_nonneg _
    constructor <;> linarith⟩
  letI : Nonempty (OrbitProcedure K n c) := ⟨(pointFiniteDesign, zeroOrbitEst)⟩
  apply le_antisymm
  · unfold rhoN orbitGameValue
    apply Causalean.Stat.minimaxValue_le_minimaxValue
      (Causalean.Stat.bddBelow_range_worstCaseRisk
        (fun p z => labeledRisk_nonneg c p z))
    intro q
    let p := (orbitToInvariantProcedure c q).1
    refine ⟨p, ?_⟩
    apply Causalean.Stat.worstCaseRisk_le
    intro z
    calc
      labeledRisk c p z = orbitRisk c q (scheduleCounts z) :=
        labeledRisk_eq_orbitRisk_of_realizes c p q
          ((orbitToInvariantProcedure_realizes c q).1)
          ((orbitToInvariantProcedure_realizes c q).2) z
      _ ≤ Causalean.Stat.worstCaseRisk (fun q m => orbitRisk c q m) q :=
        Causalean.Stat.le_worstCaseRisk (Set.finite_range _).bddAbove _
  · unfold rhoN orbitGameValue
    apply Causalean.Stat.minimaxValue_le_minimaxValue
      (Causalean.Stat.bddBelow_range_worstCaseRisk
        (fun q m => orbitRisk_nonneg c q m))
    intro p
    obtain ⟨pbar, q, _hinv, _havg, _hpbar, hdom⟩ := lossless_symmetrization c p
    refine ⟨q, ?_⟩
    apply Causalean.Stat.worstCaseRisk_le
    intro m
    obtain ⟨z, hz⟩ := scheduleCounts_surjective m
    subst m
    exact (hdom z).trans (permutation_average_le_labeledWorstCase c p z)

-- @node: thm:exact-response-type-game
/-- [there are at least two treatment arms](hyp:hK), [the labeled finite-population minimax game and its response-type orbit game have exactly the same value](goal). -/
theorem exact_response_type_game (K n : ℕ) (c : Contrast ℝ K)
    (hK : AdmissibleArmCount K) :
    LosslessSymmetrization n c ∧
    ExactInvariantProcedureCorrespondence n c ∧
    (∀ z : Schedule K n, tauC c z = tauCount c (scheduleCounts z)) ∧
    rhoN K n c = orbitGameValue K n c ∧
    HasOrbitSaddle n c := by
  exact ⟨lossless_symmetrization c,
    exact_invariant_procedure_correspondence c,
    tauC_eq_tauCount_scheduleCounts c,
    rhoN_eq_orbitGameValue K n c hK,
    finite_orbit_game_has_saddle c⟩

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
