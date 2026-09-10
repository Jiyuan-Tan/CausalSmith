import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_exact_response_type_game
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_embedded_two_arm_converse
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_universal_second_order_rate

/-! Scope comparison: exact binary orbit games for every fixed arm count. -/

open Filter

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

/-- A common carrier in which schedule domains with different arm counts can be compared. -/
abbrev AmbientRealSchedule (n : ℕ) := Fin n → ℕ → ℝ

/-- Extend a two-arm bounded-outcome schedule by zero outside its two treatment arms. -/
def embedHullSchedule {n : ℕ} {L U : ℝ} (Y : HullSchedule n L U) :
    AmbientRealSchedule n :=
  fun i a => if h : a < 2 then Y.1 i ⟨a, h⟩ else 0

/-- Extend a binary `K`-arm schedule by zero outside its treatment-arm domain. -/
def embedBinarySchedule {K n : ℕ} (z : Schedule K n) : AmbientRealSchedule n :=
  fun i a => if h : a < K then if z i ⟨a, h⟩ then 1 else 0 else 0

/-- Hull's bounded two-arm schedule domain, embedded in a common real schedule space. -/
def HullBoundedScheduleDomain (n : ℕ) (L U : ℝ) : Set (AmbientRealSchedule n) :=
  Set.range (embedHullSchedule (n := n) (L := L) (U := U))

/-- The present paper's binary `K`-arm schedule domain in the same ambient space. -/
def BinaryScheduleDomain (K n : ℕ) : Set (AmbientRealSchedule n) :=
  Set.range (embedBinarySchedule (K := K) (n := n))

-- @node: twoArmContrast_C0
/-- [the two arm contrast c0 property holds](goal). -/
lemma twoArmContrast_C0 : C0 twoArmContrast = 1 := by
  norm_num [C0, Lc, twoArmContrast, ratContrastToReal, twoArmContrastQ,
    Fin.sum_univ_succ]


-- @node: twoArm_secondOrder_lower_witness
/-- [the two arm second order lower witness property holds](goal). -/
lemma twoArm_secondOrder_lower_witness :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n ≥ N,
      κ * (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤ dN 2 twoArmContrast n := by
  have hu := universal_second_order_rate 2 twoArmContrast (by
    show 2 ≤ (2 : ℕ)
    omega)
  rcases hu with ⟨_, _, hk, _, ⟨N, _htail, hN⟩, _⟩
  refine ⟨kappaC twoArmContrast, hk, N, ?_⟩
  intro n hn
  have hrho : rhoN 2 n twoArmContrast ≤
      Causalean.Stat.worstCaseRisk
        (fun (p : Procedure 2 n twoArmContrast) (z : Schedule 2 n) =>
          labeledRisk twoArmContrast p z)
        (shrinkageProcedure 2 n twoArmContrast) := by
    unfold rhoN
    apply Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    intro p z
    exact p.1.mse_nonneg _ _
  have hrisk := hrho.trans (hN n hn)
  unfold dN
  rw [twoArmContrast_C0] at hrisk ⊢
  simp only [one_mul, one_div] at hrisk ⊢
  linarith

-- @node: hull_not_subset_binary
/-- [there are at least two treatment arms](hyp:hK), [the population size is positive](hyp:hn), [the stated side condition holds](hyp:hLU), [the hull not subset binary property holds](goal). -/
lemma hull_not_subset_binary (K n : ℕ) (hK : 3 ≤ K) (hn : 0 < n)
    (L U : ℝ) (hLU : L < U) :
    ¬ HullBoundedScheduleDomain n L U ⊆ BinaryScheduleDomain K n := by
  obtain ⟨v, hvL, hvU, hv0, hv1⟩ :
      ∃ v : ℝ, L ≤ v ∧ v ≤ U ∧ v ≠ 0 ∧ v ≠ 1 := by
    by_cases hL0 : L = 0
    · by_cases hU1 : U = 1
      · refine ⟨1 / 2, ?_⟩
        subst L; subst U
        norm_num
      · by_cases hU0 : U = 0
        · subst L; subst U; linarith
        · exact ⟨U, le_of_lt hLU, le_rfl, hU0, hU1⟩
    · by_cases hL1 : L = 1
      · by_cases hU0 : U = 0
        · subst L; subst U; linarith
        · by_cases hU1 : U = 1
          · subst L; subst U; linarith
          · exact ⟨U, le_of_lt hLU, le_rfl, hU0, hU1⟩
      · exact ⟨L, le_rfl, le_of_lt hLU, hL0, hL1⟩
  let Y : HullSchedule n L U := ⟨fun _ _ => v, fun _ _ => ⟨hvL, hvU⟩⟩
  intro hsub
  obtain ⟨z, hz⟩ := hsub ⟨Y, rfl⟩
  have heq := congrFun (congrFun hz (⟨0, hn⟩ : Fin n)) 0
  simp [embedHullSchedule, embedBinarySchedule, Y] at heq
  let a0 : Arm K := ⟨0, by omega⟩
  have hK0 : 0 < K := by omega
  cases hy : z ⟨0, hn⟩ a0 <;> simp [a0, hy, hK0] at heq
  · exact hv0 heq.symm
  · exact hv1 heq.symm

/-- [Every two-arm binary response schedule is one of the four response types that remain separately indexed in the orbit likelihood.](goal) -/
-- @node: twoArm_responseType_cases
lemma twoArm_responseType_cases (t : RespType 2) :
    t = (fun _ => false) ∨ t = twoArmNegativeEffectType ∨
      t = twoArmPositiveEffectType ∨ t = (fun _ => true) := by
  cases h0 : t 0 <;> cases h1 : t 1
  · left
    funext a
    fin_cases a <;> simp [h0, h1]
  · right; left
    funext a
    fin_cases a <;> simp [twoArmNegativeEffectType, h0, h1]
  · right; right; left
    funext a
    fin_cases a <;> simp [twoArmPositiveEffectType, h0, h1]
  · right; right; right
    funext a
    fin_cases a <;> simp [h0, h1]

/-- [The four two-arm response types are pairwise distinct.](goal) -/
-- @node: twoArm_responseTypes_pairwise_distinct
lemma twoArm_responseTypes_pairwise_distinct :
    let t00 : RespType 2 := fun _ => false
    let t01 : RespType 2 := twoArmNegativeEffectType
    let t10 : RespType 2 := twoArmPositiveEffectType
    let t11 : RespType 2 := fun _ => true
    t00 ≠ t01 ∧ t00 ≠ t10 ∧ t00 ≠ t11 ∧
      t01 ≠ t10 ∧ t01 ≠ t11 ∧ t10 ≠ t11 := by
  dsimp
  constructor
  · intro h; have := congrFun h 1; simp [twoArmNegativeEffectType] at this
  constructor
  · intro h; have := congrFun h 0; simp [twoArmPositiveEffectType] at this
  constructor
  · intro h; have := congrFun h 0; simp at this
  constructor
  · intro h
    have := congrFun h 0
    simp [twoArmNegativeEffectType, twoArmPositiveEffectType] at this
  constructor
  · intro h; have := congrFun h 0; simp [twoArmNegativeEffectType] at this
  · intro h; have := congrFun h 1; simp [twoArmPositiveEffectType] at this

/-- [the population size is positive](hyp:hn), [For the contrast `(1,-1)`, only the positive- and negative-effect response types contribute to the orbit target.](goal) -/
-- @node: twoArm_tauCount_eq_effect_difference
lemma twoArm_tauCount_eq_effect_difference (n : ℕ) (hn : 0 < n)
    (m : CountVec 2 n) :
    tauCount twoArmContrast m =
      (((pPlus m : ℕ) : ℝ) - ((pMinus m : ℕ) : ℝ)) / n := by
  let t00 : RespType 2 := fun _ => false
  let t01 : RespType 2 := twoArmNegativeEffectType
  let t10 : RespType 2 := twoArmPositiveEffectType
  let t11 : RespType 2 := fun _ => true
  have huniv : (Finset.univ : Finset (RespType 2)) = {t00, t01, t10, t11} := by
    ext t
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    simpa [t00, t01, t10, t11] using twoArm_responseType_cases t
  let f : RespType 2 → ℝ := fun t =>
    (m.1 t : ℝ) * ∑ a, twoArmContrast a * if t a then 1 else 0
  simp only [tauCount]
  change (n : ℝ)⁻¹ * ∑ t, f t = _
  rw [huniv]
  rcases twoArm_responseTypes_pairwise_distinct with
    ⟨h01, h02, h03, h12, h13, h23⟩
  have hc0 : twoArmContrast (0 : Fin 2) = 1 := by
    norm_num [twoArmContrast, ratContrastToReal, twoArmContrastQ]
  have hc1 : twoArmContrast (1 : Fin 2) = -1 := by
    change ((-1 : ℚ) : ℝ) = -1
    norm_num
  simp [f, t00, t01, t10, t11, pPlus, pMinus,
    twoArmPositiveEffectType, twoArmNegativeEffectType, Fin.sum_univ_two,
    h01, h02, h03, h12, h13, h23, hc0, hc1]
  field_simp
  ring

-- keep: public nonassertive payload preserving the frozen theorem's delivery-scope clauses.
/-- The multi-arm strict extension scope property holds. -/
def multiarmStrictExtensionScope : List String :=
  ["no exact second-order constant or source-specific optimizer is delivered",
   "no bounded-outcome fixed-K-at-least-three extension is asserted",
   "no multi-arm scalar-nonrepresentability claim is asserted"]

-- @node: thm:multiarm-strict-extension
/-- [with at least three active contrast arms, the multi-arm response-schedule hull strictly contains the binary two-arm subclass while retaining the stated second-order lower witness](goal). -/
theorem multiarm_strict_extension :
    (∀ n, 0 < n →
      rhoN 2 n twoArmContrast = orbitGameValue 2 n twoArmContrast ∧
      C0 twoArmContrast = 1) ∧
    (∀ n, 0 < n → ∀ m : CountVec 2 n,
      tauCount twoArmContrast m =
        (((pPlus m : ℕ) : ℝ) - ((pMinus m : ℕ) : ℝ)) / n) ∧
    (∀ n (m : CountVec 2 n) (r : AllocVec 2 n) (x : ObsVec r),
      let t00 : RespType 2 := fun _ => false
      let t01 : RespType 2 := twoArmNegativeEffectType
      let t10 : RespType 2 := twoArmPositiveEffectType
      let t11 : RespType 2 := fun _ => true
      t00 ≠ t01 ∧ t00 ≠ t10 ∧ t00 ≠ t11 ∧
      t01 ≠ t10 ∧ t01 ≠ t11 ∧ t10 ≠ t11 ∧
      (∀ t : RespType 2, t = t00 ∨ t = t01 ∨ t = t10 ∨ t = t11) ∧
      orbitLik m r x =
        ((∏ a, ((r.1 a : ℕ).factorial : ℚ)) / (n.factorial : ℚ)) *
          ∑ h ∈ contingencyFiber m r x,
            ∏ t, (((m.1 t : ℕ).factorial : ℚ) /
              (∏ a, ((h t a : ℕ).factorial : ℚ)))) ∧
    (∀ n, 8 ≤ n →
      dN 2 twoArmContrast n ≤ 43 * (n : ℝ) ^ (-(4 / 3 : ℝ))) ∧
    (∃ κ : ℝ, 0 < κ ∧ ∃ N : ℕ, ∀ n ≥ N,
      κ * (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤ dN 2 twoArmContrast n) ∧
    (∀ K n (c : Contrast ℝ K), 3 ≤ K →
      rhoN K n c = orbitGameValue K n c ∧ Fintype.card (RespType K) = 2 ^ K) ∧
    (∀ N L U
      (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 N))
      (est : HullEstimator N), IsMeasurableHullEstimator est →
      (⨆ Y : HullSchedule N L U, hullRisk D est Y) ∈
        {v : ℝ | ∃ (D' : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 N))
            (est' : HullEstimator N), IsMeasurableHullEstimator est' ∧
              v = ⨆ Y : HullSchedule N L U, hullRisk D' est' Y}) ∧
    (∀ K, 3 ≤ K → ∀ n, 0 < n → ∀ L U : ℝ, L < U →
      ¬ HullBoundedScheduleDomain n L U ⊆ BinaryScheduleDomain K n) := by
  refine ⟨?_, twoArm_tauCount_eq_effect_difference, ?_, ?_,
    twoArm_secondOrder_lower_witness, ?_, ?_, ?_⟩
  · intro n hn
    exact ⟨(exact_response_type_game 2 n twoArmContrast
      (by norm_num [AdmissibleArmCount])).2.2.2.1, twoArmContrast_C0⟩
  · intro n m r x
    dsimp
    exact ⟨twoArm_responseTypes_pairwise_distinct.1,
      twoArm_responseTypes_pairwise_distinct.2.1,
      twoArm_responseTypes_pairwise_distinct.2.2.1,
      twoArm_responseTypes_pairwise_distinct.2.2.2.1,
      twoArm_responseTypes_pairwise_distinct.2.2.2.2.1,
      twoArm_responseTypes_pairwise_distinct.2.2.2.2.2,
      twoArm_responseType_cases, rfl⟩
  · intro n hn
    have h := (embedded_two_arm_converse 2 n twoArmContrast
      (by norm_num [AdmissibleArmCount]) (by omega)).2.2.1 hn
    simpa [twoArmContrast_C0] using h.2.2
  · intro K n c hK
    exact ⟨(exact_response_type_game K n c (by
      show 2 ≤ K
      omega)).2.2.2.1, by simp [RespType, Arm]⟩
  · intro N L U D est hest
    exact ⟨D, est, hest, rfl⟩
  · intro K hK n hn L U hLU
    exact hull_not_subset_binary K n hK hn L U hLU

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
