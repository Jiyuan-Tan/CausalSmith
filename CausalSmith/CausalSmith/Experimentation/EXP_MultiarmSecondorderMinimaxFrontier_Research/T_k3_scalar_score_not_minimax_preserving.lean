import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.K3FullDataWitness
import Causalean.Experimentation.DesignBased.ProductVariance

/-! Exact early diagnostic showing scalar sign-score compression loses information. -/

open scoped BigOperators

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

/-- The three-arm signed score assigns the contrast coefficient to a response type according to its active outcome pattern. -/
noncomputable def k3SignedScore (A : Assign 3 n) (y : ObservedOutcome n) (i : Unit n) : ℝ :=
  (if 0 < cDagger (A i) then 1 else -1) * (2 * (if y i then 1 else 0) - 1)

/-- The three-arm mean level is the average signed score under a response-type distribution. -/
noncomputable def k3Mu (z : Schedule 3 n) (i : Unit n) : ℝ :=
  (if z i 0 then 1 else 0) -
    ((if z i 1 then 1 else 0) + (if z i 2 then 1 else 0)) / 2

/-- The five possible scalar score means `{-1,-1/2,0,1/2,1}`. -/
noncomputable def k3MeanLevel (j : Fin 5) : ℝ :=
  (j : ℝ) / 2 - 1

/-- Risk in the five-level scalar score experiment, distinct from the two-arm triple game. -/
noncomputable def k3ScalarScoreRisk (n : ℕ)
    (f : (Fin n → Bool) → ℝ) (mu : Fin n → Fin 5) : ℝ :=
  ∑ s : Fin n → Bool,
    (∏ i, if s i then (1 + k3MeanLevel (mu i)) / 2
      else (1 - k3MeanLevel (mu i)) / 2) *
    (f s - (n : ℝ)⁻¹ * ∑ i, k3MeanLevel (mu i)) ^ 2

/-- Minimax value of the genuine five-level scalar score experiment. -/
noncomputable def k3ScalarMinimaxValue (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ f : (Fin n → Bool) → ℝ,
    v = ⨆ mu : Fin n → Fin 5, k3ScalarScoreRisk n f mu}

/-- Feasible absolute total of `n` five-level scalar means. -/
def FeasibleK3ScalarTotal (n : ℕ) (M : ℝ) : Prop :=
  ∃ mu : Fin n → Fin 5, |∑ i, k3MeanLevel (mu i)| = M

/-- The scalar moment minimum is the least attainable second moment among distributions with the prescribed mean level. -/
noncomputable def scalarMomentMinimum (n : ℕ) (M : ℝ) : ℝ :=
  sInf {Q : ℝ | ∃ mu : Fin n → Fin 5,
    |∑ i, k3MeanLevel (mu i)| = M ∧ Q = ∑ i, k3MeanLevel (mu i) ^ 2}

-- @node: k3MeanLevel_sq_ge_half_abs
/-- [the three-arm mean level squared is at least half abs](goal). -/
lemma k3MeanLevel_sq_ge_half_abs (j : Fin 5) :
    |k3MeanLevel j| / 2 ≤ k3MeanLevel j ^ 2 := by
  fin_cases j <;> norm_num [k3MeanLevel]

-- @node: k3MeanLevel_sq_ge_three_abs_sub_one
/-- [the three-arm mean level squared is at least three abs sub one](goal). -/
lemma k3MeanLevel_sq_ge_three_abs_sub_one (j : Fin 5) :
    (3 * |k3MeanLevel j| - 1) / 2 ≤ k3MeanLevel j ^ 2 := by
  fin_cases j <;> norm_num [k3MeanLevel]

-- @node: scalarMomentMinimum_wedge_lower
/-- [the grid resolution is positive](hyp:hM), [The two pointwise scalar inequalities give both branches of the local wedge.](goal) -/
lemma scalarMomentMinimum_wedge_lower (n : ℕ) (M : ℝ)
    (hM : FeasibleK3ScalarTotal n M) :
    (if M ≤ (n : ℝ) / 2 then M / 2 else (3 * M - n) / 2) ≤
      scalarMomentMinimum n M := by
  classical
  rcases hM with ⟨mu₀, hmu₀⟩
  let S : Set ℝ := {Q : ℝ | ∃ mu : Fin n → Fin 5,
    |∑ i, k3MeanLevel (mu i)| = M ∧ Q = ∑ i, k3MeanLevel (mu i) ^ 2}
  have hSne : S.Nonempty := ⟨∑ i, k3MeanLevel (mu₀ i) ^ 2, mu₀, hmu₀, rfl⟩
  have hbound : ∀ Q ∈ S,
      (if M ≤ (n : ℝ) / 2 then M / 2 else (3 * M - n) / 2) ≤ Q := by
    rintro Q ⟨mu, htotal, rfl⟩
    have habs : M ≤ ∑ i, |k3MeanLevel (mu i)| := by
      rw [← htotal]
      exact Finset.abs_sum_le_sum_abs _ _
    split_ifs with hlocal
    · calc
        M / 2 ≤ (∑ i, |k3MeanLevel (mu i)|) / 2 := by linarith
        _ = ∑ i, |k3MeanLevel (mu i)| / 2 := by rw [Finset.sum_div]
        _ ≤ ∑ i, k3MeanLevel (mu i) ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ k3MeanLevel_sq_ge_half_abs (mu i)
    · calc
        (3 * M - n) / 2 ≤
            (3 * (∑ i, |k3MeanLevel (mu i)|) - n) / 2 := by linarith
        _ = ∑ i, (3 * |k3MeanLevel (mu i)| - 1) / 2 := by
          rw [← Finset.sum_div, Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          rw [← Finset.mul_sum]
          ring
        _ ≤ ∑ i, k3MeanLevel (mu i) ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ k3MeanLevel_sq_ge_three_abs_sub_one (mu i)
  change _ ≤ sInf S
  exact le_csInf hSne hbound

-- @node: feasible_total_half_integer
/-- [the grid resolution is positive](hyp:hM), [Every feasible total of five-level means is a nonnegative half-integer.](goal) -/
lemma feasible_total_half_integer (n : ℕ) (M : ℝ)
    (hM : FeasibleK3ScalarTotal n M) :
    ∃ k : ℕ, k ≤ 2 * n ∧ M = (k : ℝ) / 2 := by
  rcases hM with ⟨mu, hmu⟩
  let t : ℤ := ∑ i, ((mu i : ℕ) : ℤ) - 2 * (n : ℤ)
  have hsum_le : ∑ i, (mu i : ℕ) ≤ 4 * n := by
    calc
      ∑ i, (mu i : ℕ) ≤ ∑ _i : Fin n, 4 :=
        Finset.sum_le_sum fun i _ => Nat.le_pred_of_lt (mu i).isLt
      _ = 4 * n := by simp [mul_comm]
  have ht_bounds : -(2 * (n : ℤ)) ≤ t ∧ t ≤ 2 * (n : ℤ) := by
    dsimp [t]
    constructor
    · have : 0 ≤ ∑ i, ((mu i : ℕ) : ℤ) := by positivity
      omega
    · have hsum_le' : ∑ i, ((mu i : ℕ) : ℤ) ≤ 4 * (n : ℤ) := by
        exact_mod_cast hsum_le
      omega
  refine ⟨t.natAbs, ?_, ?_⟩
  · have habs : |t| ≤ 2 * (n : ℤ) := (abs_le).2 ht_bounds
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs]
    simpa using habs
  · rw [← hmu]
    have hsum : ∑ i, k3MeanLevel (mu i) = (t : ℝ) / 2 := by
      simp only [k3MeanLevel, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      dsimp [t]
      push_cast
      rw [← Finset.sum_div]
      ring
    rw [hsum, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num

-- @node: low_level_attainer
/-- [the low-level index satisfies its stated feasibility condition](hyp:hk), [Below the corner, half-level coordinates attain the scalar wedge.](goal) -/
lemma low_level_attainer (n k : ℕ) (hk : k ≤ n) :
    ∃ mu : Fin n → Fin 5,
      (∑ i, k3MeanLevel (mu i)) = (k : ℝ) / 2 ∧
      (∑ i, k3MeanLevel (mu i) ^ 2) = (k : ℝ) / 4 := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      refine ⟨Fin.elim0, ?_, ?_⟩ <;> simp
  | succ n ih =>
      cases k with
      | zero =>
          refine ⟨fun _ => 2, ?_, ?_⟩ <;> simp [k3MeanLevel]
      | succ k =>
          have hk' : k ≤ n := by omega
          obtain ⟨mu, hsum, hsq⟩ := ih k hk'
          refine ⟨Fin.cases 3 mu, ?_, ?_⟩
          · rw [Fin.sum_univ_succ]
            simp only [Fin.cases_zero, Fin.cases_succ, hsum]
            norm_num [k3MeanLevel]
            ring
          · rw [Fin.sum_univ_succ]
            simp only [Fin.cases_zero, Fin.cases_succ, hsq]
            norm_num [k3MeanLevel]
            ring

-- @node: high_level_attainer
/-- [the high-level index satisfies its stated feasibility condition](hyp:hl), [Beyond the corner, a mixture of half-level and unit coordinates attains the wedge.](goal) -/
lemma high_level_attainer (n l : ℕ) (hl : l ≤ n) :
    ∃ mu : Fin n → Fin 5,
      (∑ i, k3MeanLevel (mu i)) = (n : ℝ) - (l : ℝ) / 2 ∧
      (∑ i, k3MeanLevel (mu i) ^ 2) = (n : ℝ) - 3 * (l : ℝ) / 4 := by
  induction n generalizing l with
  | zero =>
      have : l = 0 := by omega
      subst l
      refine ⟨Fin.elim0, ?_, ?_⟩ <;> simp
  | succ n ih =>
      cases l with
      | zero =>
          refine ⟨fun _ => 4, ?_, ?_⟩ <;> simp [k3MeanLevel] <;> ring
      | succ l =>
          have hl' : l ≤ n := by omega
          obtain ⟨mu, hsum, hsq⟩ := ih l hl'
          refine ⟨Fin.cases 3 mu, ?_, ?_⟩
          · rw [Fin.sum_univ_succ]
            simp only [Fin.cases_zero, Fin.cases_succ, hsum]
            norm_num [k3MeanLevel]
            ring
          · rw [Fin.sum_univ_succ]
            simp only [Fin.cases_zero, Fin.cases_succ, hsq]
            norm_num [k3MeanLevel]
            ring

-- @node: scalarMomentMinimum_wedge_upper
/-- [the grid resolution is positive](hyp:hM), [The explicit half-level/unit configurations attain the lower wedge bound.](goal) -/
lemma scalarMomentMinimum_wedge_upper (n : ℕ) (M : ℝ)
    (hM : FeasibleK3ScalarTotal n M) :
    scalarMomentMinimum n M ≤
      if M ≤ (n : ℝ) / 2 then M / 2 else (3 * M - n) / 2 := by
  obtain ⟨k, hk, hMk⟩ := feasible_total_half_integer n M hM
  have hbdd : BddBelow {Q : ℝ | ∃ mu : Fin n → Fin 5,
      |∑ i, k3MeanLevel (mu i)| = M ∧
        Q = ∑ i, k3MeanLevel (mu i) ^ 2} := by
    refine ⟨0, ?_⟩
    rintro Q ⟨mu, _, rfl⟩
    positivity
  unfold scalarMomentMinimum
  by_cases hkn : k ≤ n
  · have hbranch : M ≤ (n : ℝ) / 2 := by
      rw [hMk]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hkn) (by norm_num)
    rw [if_pos hbranch]
    obtain ⟨mu, hsum, hsq⟩ := low_level_attainer n k hkn
    apply csInf_le hbdd
    refine ⟨mu, ?_, ?_⟩
    · rw [hsum, abs_of_nonneg (by positivity), hMk]
    · rw [hsq, hMk]
      ring
  · have hnk : n ≤ k := by omega
    let l := 2 * n - k
    have hl : l ≤ n := by dsimp [l]; omega
    have hkl : k = 2 * n - l := by dsimp [l]; omega
    have hl2 : l ≤ 2 * n := by omega
    have hbranch : ¬ M ≤ (n : ℝ) / 2 := by
      rw [hMk]
      apply not_le_of_gt
      exact div_lt_div_of_pos_right (by exact_mod_cast (show n < k by omega)) (by norm_num)
    rw [if_neg hbranch]
    obtain ⟨mu, hsum, hsq⟩ := high_level_attainer n l hl
    apply csInf_le hbdd
    refine ⟨mu, ?_, ?_⟩
    · rw [hsum, abs_of_nonneg]
      · rw [hMk, hkl, Nat.cast_sub hl2]
        push_cast
        ring
      · have hlR : (l : ℝ) ≤ n := by exact_mod_cast hl
        linarith
    · rw [hsq, hMk, hkl, Nat.cast_sub hl2]
      push_cast
      ring

-- @node: scalarMomentMinimum_wedge
/-- [the grid resolution is positive](hyp:hM), [Exact scalar moment wedge over every feasible half-integer total.](goal) -/
lemma scalarMomentMinimum_wedge (n : ℕ) (M : ℝ)
    (hM : FeasibleK3ScalarTotal n M) :
    scalarMomentMinimum n M =
      if M ≤ (n : ℝ) / 2 then M / 2 else (3 * M - n) / 2 := by
  exact le_antisymm (scalarMomentMinimum_wedge_upper n M hM)
    (scalarMomentMinimum_wedge_lower n M hM)

-- @node: k3SignedScore_mean
/-- [The signed score has the response-type mean stated in the scalar reduction.](goal) -/
lemma k3SignedScore_mean (n : ℕ) (z : Schedule 3 n) (i : Unit n) :
    let D := Causalean.Experimentation.DesignBased.prodDesign
      (fun _ : Unit n => qStarDesign cDagger)
    D.E (fun A => k3SignedScore A (obsOutcome z A) i) = k3Mu z i := by
  open Causalean.Experimentation.DesignBased in
    dsimp
    let g : Arm 3 → ℝ := fun a => (if 0 < cDagger a then 1 else -1) *
      (2 * (if z i a then 1 else 0) - 1)
    have hmarg := FiniteDesign.E_prod_apply
      (D := fun _ : Unit n => qStarDesign cDagger) i g
    rw [show (fun A => k3SignedScore A (obsOutcome z A) i) = fun A => g (A i) by
      funext A
      rfl, hmarg]
    unfold FiniteDesign.E
    dsimp [g]
    cases h0 : z i 0 <;> cases h1 : z i 1 <;> cases h2 : z i 2 <;>
      norm_num [qStarDesign, qStar, cDagger, Lc, cDaggerQ, ratContrastToReal,
        k3Mu, Fin.sum_univ_succ, h0, h1, h2]

-- @node: k3SignedScore_var
/-- [The signed score is unit-valued, so its variance is one minus its squared mean.](goal) -/
lemma k3SignedScore_var (n : ℕ) (z : Schedule 3 n) (i : Unit n) :
    let D := Causalean.Experimentation.DesignBased.prodDesign
      (fun _ : Unit n => qStarDesign cDagger)
    D.Var (fun A => k3SignedScore A (obsOutcome z A) i) = 1 - k3Mu z i ^ 2 := by
  open Causalean.Experimentation.DesignBased in
    dsimp
    let g : Arm 3 → ℝ := fun a => (if 0 < cDagger a then 1 else -1) *
      (2 * (if z i a then 1 else 0) - 1)
    rw [show (fun A => k3SignedScore A (obsOutcome z A) i) = fun A => g (A i) by
      funext A
      rfl]
    rw [FiniteDesign.Var_prod_apply, FiniteDesign.Var_eq]
    have hEg : (qStarDesign cDagger).E g = k3Mu z i := by
      rw [← k3SignedScore_mean n z i]
      exact (FiniteDesign.E_prod_apply
        (D := fun _ : Unit n => qStarDesign cDagger) i g).symm
    rw [hEg]
    have hsq : (qStarDesign cDagger).E (fun a => g a ^ 2) = 1 := by
      rw [show (fun a => g a ^ 2) = fun _ => 1 by
        funext a
        by_cases hc : 0 < cDagger a <;>
          by_cases hy : z i a = true <;> norm_num [g, hc, hy]]
      exact FiniteDesign.E_const _ _
    rw [hsq]

-- @node: tauC_cDagger_eq_k3Mu_average
/-- [The average signed-score mean is exactly the three-arm contrast target.](goal) -/
lemma tauC_cDagger_eq_k3Mu_average (n : ℕ) (z : Schedule 3 n) :
    tauC cDagger z = (∑ i, k3Mu z i) / n := by
  unfold tauC
  rw [div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases h0 : z i 0 <;> cases h1 : z i 1 <;> cases h2 : z i 2 <;>
    norm_num [cDagger, cDaggerQ, ratContrastToReal, k3Mu,
      Fin.sum_univ_succ, h0, h1, h2]

-- @node: k3SignedScore_average_mse
/-- [the population size is positive](hyp:hn), [Independence across units turns the signed-score variances into the exact average MSE.](goal) -/
lemma k3SignedScore_average_mse (n : ℕ) (hn : 0 < n) (z : Schedule 3 n) :
    let D := Causalean.Experimentation.DesignBased.prodDesign
      (fun _ : Unit n => qStarDesign cDagger)
    D.mse (fun A => (∑ i, k3SignedScore A (obsOutcome z A) i) / n)
      (tauC cDagger z) = 1 / (n : ℝ) -
        (∑ i, k3Mu z i ^ 2) / (n : ℝ) ^ 2 := by
  open Causalean.Experimentation.DesignBased in
    dsimp
    let g : ∀ _ : Unit n, Arm 3 → ℝ := fun i a =>
      (if 0 < cDagger a then 1 else -1) * (2 * (if z i a then 1 else 0) - 1)
    let est : Assign 3 n → ℝ := fun A => ∑ i, ((n : ℝ)⁻¹) * g i (A i)
    have hest : (fun A => (∑ i, k3SignedScore A (obsOutcome z A) i) / n) = est := by
      funext A
      dsimp [est, g]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      unfold k3SignedScore
      simp only [obsOutcome, potentialOutcome]
      have hnR : (n : ℝ) ≠ 0 := by positivity
      field_simp
      rfl
    rw [hest]
    have hEi (i : Unit n) :
        (prodDesign (fun _ : Unit n => qStarDesign cDagger)).E
          (fun A => g i (A i)) = k3Mu z i := by
      rw [← k3SignedScore_mean n z i]
      apply FiniteDesign.E_congr
      intro A
      rfl
    have hunb : (prodDesign (fun _ : Unit n => qStarDesign cDagger)).Unbiased est
        (tauC cDagger z) := by
      unfold FiniteDesign.Unbiased est
      rw [FiniteDesign.E_sum]
      simp only [FiniteDesign.E_const_mul]
      calc
        ∑ i, (n : ℝ)⁻¹ *
            (prodDesign (fun _ : Unit n => qStarDesign cDagger)).E
              (fun A => g i (A i)) =
            ∑ i, (n : ℝ)⁻¹ * k3Mu z i := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hEi i]
        _ = (∑ i, k3Mu z i) / n := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          rw [div_eq_mul_inv]
          ring
        _ = tauC cDagger z := (tauC_cDagger_eq_k3Mu_average n z).symm
    rw [FiniteDesign.mse_eq_var_of_unbiased _ hunb]
    dsimp [est]
    rw [FiniteDesign.Var_prod_linear_comb]
    have hVi (i : Unit n) :
        (qStarDesign cDagger).Var (g i) = 1 - k3Mu z i ^ 2 := by
      rw [← k3SignedScore_var n z i]
      exact (FiniteDesign.Var_prod_apply
        (D := fun _ : Unit n => qStarDesign cDagger) i (g i)).symm
    simp_rw [hVi]
    have hnR : (n : ℝ) ≠ 0 := by positivity
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp
    ring

-- @node: k3ScalarRule
/-- The exact three-observation scalar rule from the finite minimax calculation. -/
noncomputable def k3ScalarRule (s : Fin 3 → Bool) : ℝ :=
  ((3 - Real.sqrt 3) / 6) * ∑ i, if s i then 1 else -1

-- @node: k3ScalarRule_mem_Icc
/-- [The exact scalar rule stays in the natural target interval.](goal) -/
lemma k3ScalarRule_mem_Icc (s : Fin 3 → Bool) : k3ScalarRule s ∈ Set.Icc (-1) 1 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs1 : 1 ≤ Real.sqrt 3 := by nlinarith
  have hs3 : Real.sqrt 3 ≤ 3 := by nlinarith
  have ha0 : 0 ≤ (3 - Real.sqrt 3) / 6 := by linarith
  have ha : (3 - Real.sqrt 3) / 6 ≤ 1 / 3 := by linarith
  have hsum : |∑ i, (if s i then (1 : ℝ) else -1)| ≤ 3 := by
    calc
      |∑ i, (if s i then (1 : ℝ) else -1)| ≤
          ∑ i, |if s i then (1 : ℝ) else -1| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _i : Fin 3, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : s i <;> simp [h]
      _ = 3 := by norm_num
  have habs : |k3ScalarRule s| ≤ 1 := by
    rw [k3ScalarRule, abs_mul, abs_of_nonneg ha0]
    nlinarith [abs_nonneg (∑ i, (if s i then (1 : ℝ) else -1))]
  exact abs_le.mp habs

-- @node: k3ScalarBoolDesign
/-- The Bernoulli score law with mean equal to the selected five-level parameter. -/
noncomputable def k3ScalarBoolDesign (j : Fin 5) :
    Causalean.Experimentation.DesignBased.FiniteDesign Bool where
  p b := if b then (1 + k3MeanLevel j) / 2 else (1 - k3MeanLevel j) / 2
  p_nonneg b := by fin_cases j <;> cases b <;> norm_num [k3MeanLevel]
  p_sum := by simp; ring

-- @node: k3ScalarProductDesign
/-- Independent three-coordinate score law for a vector of scalar means. -/
noncomputable def k3ScalarProductDesign (mu : Fin 3 → Fin 5) :
    Causalean.Experimentation.DesignBased.FiniteDesign (Fin 3 → Bool) :=
  Causalean.Experimentation.DesignBased.prodDesign
    (fun i ↦ k3ScalarBoolDesign (mu i))

-- @node: k3ScalarBoolDesign_mean
/-- [the three-arm scalar bool design mean property holds](goal). -/
lemma k3ScalarBoolDesign_mean (j : Fin 5) :
    (k3ScalarBoolDesign j).E (fun b ↦ if b then (1 : ℝ) else -1) =
      k3MeanLevel j := by
  fin_cases j <;>
    norm_num [k3ScalarBoolDesign,
      Causalean.Experimentation.DesignBased.FiniteDesign.E, k3MeanLevel]

-- @node: k3ScalarBoolDesign_var
/-- [the three-arm scalar bool design var property holds](goal). -/
lemma k3ScalarBoolDesign_var (j : Fin 5) :
    (k3ScalarBoolDesign j).Var (fun b ↦ if b then (1 : ℝ) else -1) =
      1 - k3MeanLevel j ^ 2 := by
  open Causalean.Experimentation.DesignBased in
    rw [FiniteDesign.Var_eq, k3ScalarBoolDesign_mean]
    fin_cases j <;>
      norm_num [k3ScalarBoolDesign, FiniteDesign.E, k3MeanLevel]

-- @node: k3ScalarRule_risk_le
/-- [The explicit linear scalar rule has risk at most `1 - sqrt 3 / 2` at every state.](goal) -/
lemma k3ScalarRule_risk_le (mu : Fin 3 → Fin 5) :
    k3ScalarScoreRisk 3 k3ScalarRule mu ≤ 1 - Real.sqrt 3 / 2 := by
  open Causalean.Experimentation.DesignBased in
    change (k3ScalarProductDesign mu).mse k3ScalarRule
      ((3 : ℝ)⁻¹ * ∑ i, k3MeanLevel (mu i)) ≤ _
    let g : ∀ _ : Fin 3, Bool → ℝ := fun _ b ↦ if b then 1 else -1
    let α : ℝ := (3 - Real.sqrt 3) / 6
    have hrule : k3ScalarRule = fun s ↦ ∑ i, α * g i (s i) := by
      funext s
      simp only [k3ScalarRule, α, g, Finset.mul_sum]
    rw [hrule, FiniteDesign.mse_eq_var_add_bias_sq]
    change (prodDesign (fun i ↦ k3ScalarBoolDesign (mu i))).Var
        (fun s ↦ ∑ i, α * g i (s i)) + _ ≤ _
    rw [FiniteDesign.Var_prod_linear_comb]
    have hmean : (k3ScalarProductDesign mu).E
        (fun s ↦ ∑ i, α * g i (s i)) =
        α * ∑ i, k3MeanLevel (mu i) := by
      unfold k3ScalarProductDesign
      rw [FiniteDesign.E_sum]
      simp_rw [FiniteDesign.E_const_mul, FiniteDesign.E_prod_apply]
      simp only [g, k3ScalarBoolDesign_mean]
      rw [Finset.mul_sum]
    unfold FiniteDesign.bias
    rw [hmean]
    simp only [g]
    simp_rw [k3ScalarBoolDesign_var]
    have hcs : (∑ i, k3MeanLevel (mu i)) ^ 2 ≤
        3 * ∑ i, k3MeanLevel (mu i) ^ 2 := by
      simpa using (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
        (fun _ ↦ (1 : ℝ)) (fun i ↦ k3MeanLevel (mu i)))
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    dsimp [α]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    norm_num1
    nlinarith [Real.sqrt_nonneg 3]

-- @node: k3ScalarMinimaxValue_le_exact
/-- [The explicit scalar rule gives the upper half of the exact three-score minimax value.](goal) -/
lemma k3ScalarMinimaxValue_le_exact :
    k3ScalarMinimaxValue 3 ≤ 1 - Real.sqrt 3 / 2 := by
  have hbdd : BddBelow {v : ℝ | ∃ f : (Fin 3 → Bool) → ℝ,
      v = ⨆ mu : Fin 3 → Fin 5, k3ScalarScoreRisk 3 f mu} := by
    refine ⟨0, ?_⟩
    rintro v ⟨f, rfl⟩
    have hrisk : 0 ≤ k3ScalarScoreRisk 3 f (fun _ ↦ 0) := by
      unfold k3ScalarScoreRisk
      apply Finset.sum_nonneg
      intro s _
      exact mul_nonneg (Finset.prod_nonneg fun i _ ↦ by
        by_cases h : s i <;> simp [k3MeanLevel, h]) (sq_nonneg _)
    exact hrisk.trans (le_ciSup (Set.finite_range _).bddAbove (fun _ ↦ 0))
  unfold k3ScalarMinimaxValue
  calc
    sInf {v : ℝ | ∃ f : (Fin 3 → Bool) → ℝ,
        v = ⨆ mu : Fin 3 → Fin 5, k3ScalarScoreRisk 3 f mu} ≤
        ⨆ mu : Fin 3 → Fin 5, k3ScalarScoreRisk 3 k3ScalarRule mu :=
      csInf_le hbdd ⟨k3ScalarRule, rfl⟩
    _ ≤ 1 - Real.sqrt 3 / 2 := ciSup_le fun mu ↦ k3ScalarRule_risk_le mu

-- @node: k3ScalarLeastFavorableWeight
/-- Exact least-favorable weights on the five homogeneous scalar states. -/
noncomputable def k3ScalarLeastFavorableWeight (j : Fin 5) : ℝ :=
  ![((-11 + 7 * Real.sqrt 3) / 12),
    ((8 - 4 * Real.sqrt 3) / 3),
    ((-5 + 3 * Real.sqrt 3) / 2),
    ((8 - 4 * Real.sqrt 3) / 3),
    ((-11 + 7 * Real.sqrt 3) / 12)] j

-- @node: k3ScalarPriorRisk
/-- The three-arm scalar prior risk property holds. -/
noncomputable def k3ScalarPriorRisk (f : (Fin 3 → Bool) → ℝ) : ℝ :=
  ∑ j : Fin 5, k3ScalarLeastFavorableWeight j *
    k3ScalarScoreRisk 3 f (fun _ ↦ j)

-- @node: fin3FunEquiv
/-- Coordinate equivalence used to evaluate the scalar three-coordinate certificate. -/
def fin3FunEquiv (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun f := (f 0, f 1, f 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

-- @node: k3ScalarLeastFavorableWeight_nonneg
/-- [the three-arm scalar least favorable weight is nonnegative](goal). -/
lemma k3ScalarLeastFavorableWeight_nonneg (j : Fin 5) :
    0 ≤ k3ScalarLeastFavorableWeight j := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt0 := Real.sqrt_nonneg 3
  fin_cases j <;> norm_num [k3ScalarLeastFavorableWeight] <;> nlinarith

-- @node: k3ScalarLeastFavorableWeight_sum
/-- [the three-arm scalar least favorable weight sums](goal). -/
lemma k3ScalarLeastFavorableWeight_sum :
    ∑ j : Fin 5, k3ScalarLeastFavorableWeight j = 1 := by
  norm_num [k3ScalarLeastFavorableWeight, Fin.sum_univ_succ]
  ring_nf

set_option maxHeartbeats 800000 in
-- @node: k3ScalarPriorRisk_decomposition
/-- [Posterior square completion for the exact five-state scalar prior.](goal) -/
lemma k3ScalarPriorRisk_decomposition (f : (Fin 3 → Bool) → ℝ) :
    k3ScalarPriorRisk f = k3ScalarPriorRisk k3ScalarRule +
      ∑ s : Fin 3 → Bool,
        (∑ j : Fin 5, k3ScalarLeastFavorableWeight j *
          (∏ i : Fin 3, if s i then (1 + k3MeanLevel j) / 2
            else (1 - k3MeanLevel j) / 2)) * (f s - k3ScalarRule s) ^ 2 := by
  unfold k3ScalarPriorRisk k3ScalarScoreRisk
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs =>
    lhs
    rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
    norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ,
      k3ScalarLeastFavorableWeight, k3MeanLevel,
      k3ScalarRule, h0, h1, h2] <;> nlinarith [hsqrt]

set_option maxHeartbeats 800000 in
-- @node: k3ScalarRule_homogeneous_risk
/-- [the three-arm scalar rule homogeneous risk property holds](goal). -/
lemma k3ScalarRule_homogeneous_risk (j : Fin 5) :
    k3ScalarScoreRisk 3 k3ScalarRule (fun _ ↦ j) =
      ((3 - Real.sqrt 3) / 6) ^ 2 * (3 * (1 - k3MeanLevel j ^ 2)) +
      (3 * ((3 - Real.sqrt 3) / 6) * k3MeanLevel j - k3MeanLevel j) ^ 2 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold k3ScalarScoreRisk
  rw [Fintype.sum_equiv (fin3FunEquiv Bool) _
    (fun p ↦
      ((if p.1 then (1 + k3MeanLevel j) / 2 else (1 - k3MeanLevel j) / 2) *
       (if p.2.1 then (1 + k3MeanLevel j) / 2 else (1 - k3MeanLevel j) / 2) *
       (if p.2.2 then (1 + k3MeanLevel j) / 2 else (1 - k3MeanLevel j) / 2)) *
      (k3ScalarRule ![p.1, p.2.1, p.2.2] - k3MeanLevel j) ^ 2)]
  · simp only [Fintype.sum_prod_type]
    fin_cases j <;>
      norm_num [k3MeanLevel, k3ScalarRule, Fin.sum_univ_succ] <;>
      nlinarith [hsqrt]
  · intro s
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
      norm_num [fin3FunEquiv, Fin.sum_univ_succ, Fin.prod_univ_succ,
        k3ScalarRule, h0, h1, h2] <;> ring

-- @node: k3ScalarPriorRisk_rule
/-- [the three-arm scalar prior risk rule property holds](goal). -/
lemma k3ScalarPriorRisk_rule :
    k3ScalarPriorRisk k3ScalarRule = 1 - Real.sqrt 3 / 2 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold k3ScalarPriorRisk
  simp_rw [k3ScalarRule_homogeneous_risk]
  norm_num [k3ScalarLeastFavorableWeight, k3MeanLevel, k3ScalarRule,
    Fin.sum_univ_succ]
  nlinarith [hsqrt]

-- @node: k3ScalarPriorRisk_lower
/-- [the three-arm scalar prior risk lower property holds](goal). -/
lemma k3ScalarPriorRisk_lower (f : (Fin 3 → Bool) → ℝ) :
    1 - Real.sqrt 3 / 2 ≤ k3ScalarPriorRisk f := by
  rw [k3ScalarPriorRisk_decomposition, k3ScalarPriorRisk_rule]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro s hs
  apply mul_nonneg
  · apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (k3ScalarLeastFavorableWeight_nonneg j)
    apply Finset.prod_nonneg
    intro i hi
    fin_cases j <;> cases s i <;> norm_num [k3MeanLevel]
  · positivity

-- @node: k3ScalarMinimaxValue_ge_exact
/-- [The exact prior gives the lower half of the scalar minimax calculation.](goal) -/
lemma k3ScalarMinimaxValue_ge_exact :
    1 - Real.sqrt 3 / 2 ≤ k3ScalarMinimaxValue 3 := by
  let S : Set ℝ := {v : ℝ | ∃ f : (Fin 3 → Bool) → ℝ,
    v = ⨆ mu : Fin 3 → Fin 5, k3ScalarScoreRisk 3 f mu}
  have hSne : S.Nonempty :=
    ⟨⨆ mu : Fin 3 → Fin 5, k3ScalarScoreRisk 3 (fun _ ↦ 0) mu,
      fun _ ↦ 0, rfl⟩
  change _ ≤ sInf S
  apply le_csInf hSne
  rintro v ⟨f, rfl⟩
  calc
    1 - Real.sqrt 3 / 2 ≤ k3ScalarPriorRisk f := k3ScalarPriorRisk_lower f
    _ ≤ ⨆ mu : Fin 3 → Fin 5, k3ScalarScoreRisk 3 f mu := by
      unfold k3ScalarPriorRisk
      calc
        ∑ j : Fin 5, k3ScalarLeastFavorableWeight j *
            k3ScalarScoreRisk 3 f (fun _ ↦ j) ≤
            ∑ j : Fin 5, k3ScalarLeastFavorableWeight j *
              (⨆ mu : Fin 3 → Fin 5, k3ScalarScoreRisk 3 f mu) := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left
            (le_ciSup (Set.finite_range
              (fun mu : Fin 3 → Fin 5 ↦ k3ScalarScoreRisk 3 f mu)).bddAbove
                (fun _ ↦ j))
            (k3ScalarLeastFavorableWeight_nonneg j)
        _ = _ := by rw [← Finset.sum_mul, k3ScalarLeastFavorableWeight_sum, one_mul]

-- @node: prop:k3-scalar-score-not-minimax-preserving
/-- [for the certified three-arm contrast, compressing the full data to the scalar signed score strictly increases the minimax risk](goal). -/
theorem k3_scalar_score_not_minimax_preserving :
    (∀ n : ℕ, 0 < n → ∀ z : Schedule 3 n, ∀ i : Unit n,
      let D := Causalean.Experimentation.DesignBased.prodDesign
        (fun _ : Unit n => qStarDesign cDagger)
      D.E (fun A => k3SignedScore A (obsOutcome z A) i) = k3Mu z i ∧
      D.Var (fun A => k3SignedScore A (obsOutcome z A) i) = 1 - k3Mu z i ^ 2) ∧
    (∀ n : ℕ, 0 < n → ∀ z : Schedule 3 n,
      let D := Causalean.Experimentation.DesignBased.prodDesign
        (fun _ : Unit n => qStarDesign cDagger)
      D.mse (fun A => (∑ i, k3SignedScore A (obsOutcome z A) i) / n)
        (tauC cDagger z) = 1 / (n : ℝ) -
          (∑ i, k3Mu z i ^ 2) / (n : ℝ) ^ 2) ∧
    k3ScalarMinimaxValue 3 = 1 - Real.sqrt 3 / 2 ∧
    (fullDataRuleRiskBound : ℝ) < (scalarBayesCertificate : ℝ) ∧
    (scalarBayesCertificate : ℝ) < 1 - Real.sqrt 3 / 2 ∧
    (∃ fullRule : Estimator 3 3 cDagger,
      Causalean.Stat.worstCaseRisk
        (fun (p : Procedure 3 3 cDagger) (z : Schedule 3 3) => labeledRisk cDagger p z)
        (Causalean.Experimentation.DesignBased.prodDesign
          (fun _ : Unit 3 => qStarDesign cDagger), fullRule) = fullDataRuleRiskBound) ∧
    (∀ n : ℕ, ∀ M : ℝ, FeasibleK3ScalarTotal n M →
      scalarMomentMinimum n M =
        if M ≤ (n : ℝ) / 2 then M / 2 else (3 * M - n) / 2) := by
  refine ⟨?_, ?_, ?_, k3_rational_separation.1,
    (by
      have hsqrt : Real.sqrt 3 < (117787 : ℝ) / 68000 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 117787 / 68000)]
        norm_num
      norm_num [scalarBayesCertificate]
      linarith), ?_, ?_⟩
  · intro n hn z i
    exact ⟨k3SignedScore_mean n z i, k3SignedScore_var n z i⟩
  · intro n hn z
    exact k3SignedScore_average_mse n hn z
  · exact le_antisymm k3ScalarMinimaxValue_le_exact k3ScalarMinimaxValue_ge_exact
  · exact ⟨k3FullDataRule, k3FullDataRule_worstCaseRisk⟩
  · intro n M hM
    exact scalarMomentMinimum_wedge n M hM

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
