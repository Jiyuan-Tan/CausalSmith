import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Basic
import Causalean.Experimentation.DesignBased.MeasureBridge

/-! Finite-sample Lipschitz continuity of square-root minimax risk. -/

open scoped BigOperators

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

/-- The distance between two contrasts is the largest absolute difference between their response-type scores. -/
noncomputable def contrastDistance {K : ℕ} (c c' : Contrast ℝ K) : ℝ :=
  (∑ a, |c a - c' a|) / 2

-- @node: contrastTypeScore_sub_abs_le
/-- [the contrast type score sub abs is at most property holds](goal). -/
lemma contrastTypeScore_sub_abs_le {K : ℕ} (c c' : Contrast ℝ K) (t : RespType K) :
    |∑ a, (c a - c' a) * if t a then 1 else 0| ≤ contrastDistance c c' := by
  classical
  let s : Finset (Arm K) := Finset.univ.filter fun a => t a
  let sc : Finset (Arm K) := Finset.univ.filter fun a => ¬ t a
  have hzero : ∑ a, (c a - c' a) = 0 := by
    rw [Finset.sum_sub_distrib, c.sum_zero, c'.sum_zero, sub_self]
  have hpartition : s.sum (fun a => c a - c' a) +
      sc.sum (fun a => c a - c' a) = 0 := by
    calc
      s.sum (fun a => c a - c' a) + sc.sum (fun a => c a - c' a) =
          ∑ a, ((if a ∈ s then c a - c' a else 0) +
            if a ∈ sc then c a - c' a else 0) := by
              simp [Finset.sum_add_distrib]
      _ = ∑ a, (c a - c' a) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases ht : t a <;> simp [s, sc, ht]
      _ = 0 := hzero
  have hsplit : s.sum (fun a => c a - c' a) =
      -sc.sum (fun a => c a - c' a) := by
    have := hpartition
    linarith
  have hs : |s.sum (fun a => c a - c' a)| ≤ s.sum (fun a => |c a - c' a|) :=
    Finset.abs_sum_le_sum_abs _ _
  have hsc : |s.sum (fun a => c a - c' a)| ≤ sc.sum (fun a => |c a - c' a|) := by
    rw [hsplit, abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have htotal : s.sum (fun a => |c a - c' a|) + sc.sum (fun a => |c a - c' a|) =
      ∑ a, |c a - c' a| := by
    calc
      _ = ∑ a, ((if a ∈ s then |c a - c' a| else 0) +
          if a ∈ sc then |c a - c' a| else 0) := by simp [Finset.sum_add_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases ht : t a <;> simp [s, sc, ht]
  have hscore : (∑ a, (c a - c' a) * if t a then 1 else 0) =
      s.sum (fun a => c a - c' a) := by
    calc
      _ = ∑ a, if a ∈ s then c a - c' a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases ht : t a <;> simp [s, ht]
      _ = _ := by simp
  rw [hscore, contrastDistance]
  linarith

-- @node: tauC_sub_abs_le_contrastDistance
/-- [the population size is positive](hyp:hn), [the tau c sub abs is at most contrast distance](goal). -/
lemma tauC_sub_abs_le_contrastDistance {K n : ℕ} (c c' : Contrast ℝ K)
    (z : Schedule K n) (hn : 1 ≤ n) :
    |tauC c z - tauC c' z| ≤ contrastDistance c c' := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hpoint : ∀ i : Unit n,
      |∑ a, (c a - c' a) * if z i a then 1 else 0| ≤ contrastDistance c c' :=
    fun i => contrastTypeScore_sub_abs_le c c' (z i)
  rw [tauC, tauC, ← mul_sub, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, ← sub_mul]
  calc
    |(n : ℝ)⁻¹ * ∑ i, ∑ a, (c a - c' a) * if z i a then 1 else 0| =
        (n : ℝ)⁻¹ * |∑ i, ∑ a, (c a - c' a) * if z i a then 1 else 0| := by
          rw [abs_mul, abs_of_pos (inv_pos.mpr hnR)]
    _ ≤ (n : ℝ)⁻¹ * ∑ i, |∑ a, (c a - c' a) * if z i a then 1 else 0| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Unit n, contrastDistance c c' := by
          gcongr with i
          exact hpoint i
    _ = contrastDistance c c' := by
          simp [hnR.ne']

-- @node: tauC_mem_naturalInterval
/-- [the population size is positive](hyp:hn), [the tau c belongs to natural interval](goal). -/
lemma tauC_mem_naturalInterval {K n : ℕ} (c : Contrast ℝ K)
    (z : Schedule K n) (hn : 1 ≤ n) : tauC c z ∈ Set.Icc (-Lc c / 2) (Lc c / 2) := by
  let nc : Contrast ℝ K :=
    { coeff := fun a => -c a
      nonzero := by
        intro h
        apply c.nonzero
        funext a
        have := congrFun h a
        simp only [Pi.zero_apply] at this ⊢
        linarith
      sum_zero := by
        change ∑ a, -c a = 0
        rw [Finset.sum_neg_distrib, c.sum_zero, neg_zero] }
  have h := tauC_sub_abs_le_contrastDistance c nc z hn
  have hdist : contrastDistance c nc = Lc c := by
    simp only [contrastDistance, nc, Lc]
    rw [show (∑ a, |c a - -c a|) = 2 * ∑ a, |c a| by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [show c a - -c a = 2 * c a by ring, abs_mul]
      norm_num]
    ring
  have htau : tauC nc z = -tauC c z := by
    simp only [tauC, nc, Finset.mul_sum, ← Finset.sum_neg_distrib]
    ring
  rw [htau, hdist, sub_neg_eq_add, ← two_mul, abs_mul] at h
  norm_num at h
  constructor <;> linarith [le_abs_self (tauC c z), neg_abs_le (tauC c z)]

-- @node: finiteDesign_E_abs_le_sqrt_E_sq
/-- [the finite design e abs is at most sqrt e squared](goal). -/
lemma finiteDesign_E_abs_le_sqrt_E_sq {Ω : Type*} [Fintype Ω]
    (D : Causalean.Experimentation.DesignBased.FiniteDesign Ω) (X : Ω → ℝ) :
    D.E (fun ω => |X ω|) ≤ Real.sqrt (D.E fun ω => X ω ^ 2) := by
  have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset Ω)
    (fun ω => D.p_nonneg ω)
    (fun ω => mul_nonneg (D.p_nonneg ω) (sq_nonneg (X ω)))
  rw [D.p_sum, Real.sqrt_one, one_mul] at hcs
  simp only [Real.sqrt_mul (D.p_nonneg _), Real.sqrt_sq_eq_abs] at hcs
  rw [show D.E (fun ω => |X ω|) =
      ∑ ω, Real.sqrt (D.p ω) * (Real.sqrt (D.p ω) * |X ω|) by
    unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
    apply Finset.sum_congr rfl
    intro ω hω
    have hp := Real.sq_sqrt (D.p_nonneg ω)
    dsimp
    calc
      D.p ω * |X ω| = Real.sqrt (D.p ω) ^ 2 * |X ω| := by rw [hp]
      _ = Real.sqrt (D.p ω) * (Real.sqrt (D.p ω) * |X ω|) := by ring]
  simpa only [Causalean.Experimentation.DesignBased.FiniteDesign.E] using hcs

-- @node: finiteDesign_root_mse_triangle_const
/-- [the stated side condition holds](hyp:hη), [the finite design root mse triangle const property holds](goal). -/
lemma finiteDesign_root_mse_triangle_const {Ω : Type*} [Fintype Ω]
    (D : Causalean.Experimentation.DesignBased.FiniteDesign Ω) (X : Ω → ℝ)
    (η : ℝ) (hη : 0 ≤ η) :
    Real.sqrt (D.E fun ω => (|X ω| + η) ^ 2) ≤
      Real.sqrt (D.E fun ω => X ω ^ 2) + η := by
  have habs := finiteDesign_E_abs_le_sqrt_E_sq D X
  have hEX : 0 ≤ D.E (fun ω => X ω ^ 2) := D.E_nonneg fun _ => sq_nonneg _
  have hbound : D.E (fun ω => (|X ω| + η) ^ 2) ≤
      (Real.sqrt (D.E fun ω => X ω ^ 2) + η) ^ 2 := by
    rw [show D.E (fun ω => (|X ω| + η) ^ 2) =
        D.E (fun ω => X ω ^ 2) + 2 * η * D.E (fun ω => |X ω|) + η ^ 2 by
      calc
        _ = D.E (fun ω => X ω ^ 2 + (2 * η * |X ω| + η ^ 2)) :=
          D.E_congr (fun ω => by nlinarith [sq_abs (X ω)])
        _ = _ := by rw [D.E_add, D.E_add, D.E_const_mul, D.E_const]; ring]
    rw [add_sq, Real.sq_sqrt hEX]
    nlinarith
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hbound⟩

-- @node: clip_sq_dist_le
/-- [the dual vector is feasible](hyp:hy), [the clip squared dist is at most property holds](goal). -/
lemma clip_sq_dist_le {K : ℕ} (c : Contrast ℝ K) (x y : ℝ)
    (hy : y ∈ Set.Icc (-Lc c / 2) (Lc c / 2)) :
    (clip c x - y) ^ 2 ≤ (x - y) ^ 2 := by
  have hI : -Lc c / 2 ≤ Lc c / 2 := by
    have : 0 ≤ Lc c := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  by_cases hlo : x < -Lc c / 2
  · rw [clip, min_eq_right (le_trans (le_of_lt hlo) hI), max_eq_left (le_of_lt hlo)]
    have h1 : 0 ≤ y - (-Lc c / 2) := by linarith [hy.1]
    have h2 : y - (-Lc c / 2) ≤ y - x := by linarith
    nlinarith [mul_self_le_mul_self h1 h2]
  · have hlo' : -Lc c / 2 ≤ x := le_of_not_gt hlo
    by_cases hhi : x ≤ Lc c / 2
    · rw [clip, min_eq_right hhi, max_eq_right hlo']
    · have hhi' : Lc c / 2 < x := lt_of_not_ge hhi
      rw [clip, min_eq_left (le_of_lt hhi'), max_eq_right hI]
      have h1 : 0 ≤ Lc c / 2 - y := by linarith [hy.2]
      have h2 : Lc c / 2 - y ≤ x - y := by linarith
      nlinarith [mul_self_le_mul_self h1 h2]

-- @node: transferProcedure
/-- A procedure for one contrast transfers to another by applying the original procedure and clipping its output to the new contrast range. -/
noncomputable def transferProcedure {K n : ℕ} (c : Contrast ℝ K)
    {c' : Contrast ℝ K} (p : Procedure K n c') : Procedure K n c :=
  (p.1, fun A y => ⟨clip c (p.2 A y), clip_mem c _⟩)

-- @node: transferred_root_risk_le
/-- [the population size is positive](hyp:hn), [the transferred root risk is at most property holds](goal). -/
lemma transferred_root_risk_le {K n : ℕ} (c c' : Contrast ℝ K)
    (p : Procedure K n c') (z : Schedule K n) (hn : 1 ≤ n) :
    Real.sqrt (labeledRisk c (transferProcedure c p) z) ≤
      Real.sqrt (labeledRisk c' p z) + contrastDistance c c' := by
  let η := contrastDistance c c'
  have hη : 0 ≤ η := by
    dsimp [η, contrastDistance]
    positivity
  let X : Assign K n → ℝ := fun A => (p.2 A (obsOutcome z A) : ℝ) - tauC c' z
  have htarget := tauC_sub_abs_le_contrastDistance c c' z hn
  have hmse : labeledRisk c (transferProcedure c p) z ≤
      p.1.E (fun A => (|X A| + η) ^ 2) := by
    unfold labeledRisk Causalean.Experimentation.DesignBased.FiniteDesign.mse
    unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
    apply Finset.sum_le_sum
    intro A hA
    apply mul_le_mul_of_nonneg_left _ (p.1.p_nonneg A)
    have hclip := clip_sq_dist_le c (p.2 A (obsOutcome z A)) (tauC c z)
      (tauC_mem_naturalInterval c z hn)
    have habs : |(p.2 A (obsOutcome z A) : ℝ) - tauC c z| ≤ |X A| + η := by
      calc
        _ = |X A + (tauC c' z - tauC c z)| := by simp [X]
        _ ≤ |X A| + |tauC c' z - tauC c z| := abs_add_le _ _
        _ ≤ |X A| + η := by
          gcongr
          simpa [η, abs_sub_comm] using htarget
    have hsquare := mul_self_le_mul_self
      (abs_nonneg ((p.2 A (obsOutcome z A) : ℝ) - tauC c z)) habs
    rw [← pow_two, ← pow_two, sq_abs] at hsquare
    exact hclip.trans hsquare
  calc
    Real.sqrt (labeledRisk c (transferProcedure c p) z) ≤
        Real.sqrt (p.1.E fun A => (|X A| + η) ^ 2) := Real.sqrt_le_sqrt hmse
    _ ≤ Real.sqrt (p.1.E fun A => X A ^ 2) + η :=
      finiteDesign_root_mse_triangle_const p.1 X η hη
    _ = Real.sqrt (labeledRisk c' p z) + contrastDistance c c' := by
      rfl

-- @node: sqrt_worstCaseRisk_eq
/-- [the stated side condition holds](hyp:hrisk), [the sqrt worst case risk equals property holds](goal). -/
lemma sqrt_worstCaseRisk_eq {E Θ : Type*} [Nonempty Θ] [Fintype Θ]
    (risk : E → Θ → ℝ) (e : E) (hrisk : ∀ θ, 0 ≤ risk e θ) :
    Real.sqrt (Causalean.Stat.worstCaseRisk risk e) =
      Causalean.Stat.worstCaseRisk (fun e θ => Real.sqrt (risk e θ)) e := by
  unfold Causalean.Stat.worstCaseRisk
  exact Real.sqrt_monotone.map_ciSup_of_continuousAt
    Real.continuous_sqrt.continuousAt (bdd := (Set.finite_range (risk e)).bddAbove)

-- @node: sqrt_rhoN_eq_root_minimax
/-- [the sqrt rho n equals root minimax](goal). -/
lemma sqrt_rhoN_eq_root_minimax {K n : ℕ} (c : Contrast ℝ K) :
    Real.sqrt (rhoN K n c) =
      Causalean.Stat.minimaxValue
        (fun (p : Procedure K n c) (z : Schedule K n) => Real.sqrt (labeledRisk c p z)) := by
  letI : Nonempty (Procedure K n c) := ⟨contrastWeightedProcedure K n c⟩
  unfold rhoN Causalean.Stat.minimaxValue
  have hbdd : BddBelow (Set.range (fun p : Procedure K n c =>
      Causalean.Stat.worstCaseRisk
        (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z) p)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact Causalean.Stat.worstCaseRisk_nonneg (fun z => p.1.mse_nonneg _ _)
  rw [Real.sqrt_monotone.map_ciInf_of_continuousAt
    Real.continuous_sqrt.continuousAt (bdd := hbdd)]
  congr 1
  funext p
  exact sqrt_worstCaseRisk_eq _ p (fun z => p.1.mse_nonneg _ _)

-- @node: root_minimax_one_sided_contrast_le
/-- [the population size is positive](hyp:hn), [the root minimax one sided contrast is at most property holds](goal). -/
lemma root_minimax_one_sided_contrast_le (K n : ℕ) (c c' : Contrast ℝ K)
    (hn : 1 ≤ n) :
    Real.sqrt (rhoN K n c) ≤ Real.sqrt (rhoN K n c') + contrastDistance c c' := by
  rw [sqrt_rhoN_eq_root_minimax c, sqrt_rhoN_eq_root_minimax c']
  letI : Nonempty (Procedure K n c') := ⟨contrastWeightedProcedure K n c'⟩
  apply sub_le_iff_le_add.mp
  apply Causalean.Stat.le_minimaxValue
  intro p
  have htransfer : Causalean.Stat.worstCaseRisk
      (fun (q : Procedure K n c) (z : Schedule K n) => Real.sqrt (labeledRisk c q z))
      (transferProcedure c p) ≤
      Causalean.Stat.worstCaseRisk
        (fun (q : Procedure K n c') (z : Schedule K n) => Real.sqrt (labeledRisk c' q z)) p +
        contrastDistance c c' := by
    apply Causalean.Stat.worstCaseRisk_le
    intro z
    calc
      Real.sqrt (labeledRisk c (transferProcedure c p) z) ≤
          Real.sqrt (labeledRisk c' p z) + contrastDistance c c' :=
        transferred_root_risk_le c c' p z hn
      _ ≤ Causalean.Stat.worstCaseRisk
            (fun (p : Procedure K n c') (z : Schedule K n) =>
              Real.sqrt (labeledRisk c' p z)) p + contrastDistance c c' := by
        gcongr
        have hbdd : BddAbove (Set.range (fun z : Schedule K n =>
            Real.sqrt (labeledRisk c' p z))) := (Set.finite_range _).bddAbove
        exact Causalean.Stat.le_worstCaseRisk
          (risk := fun (q : Procedure K n c') (z : Schedule K n) =>
            Real.sqrt (labeledRisk c' q z)) (e := p) hbdd z
  have hmin := Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    (risk := fun (q : Procedure K n c) (z : Schedule K n) => Real.sqrt (labeledRisk c q z))
    (fun _ _ => Real.sqrt_nonneg _) (transferProcedure c p)
  linarith

-- @node: thm:contrast-risk-continuity
/-- [there are at least two treatment arms](hyp:hK), [the population size is positive](hyp:hn), [the square root of finite-sample minimax risk is Lipschitz continuous in the contrast under the response-type score distance](goal). -/
theorem contrast_risk_continuity (K n : ℕ) (c c' : Contrast ℝ K)
    (hK : AdmissibleArmCount K) (hn : 1 ≤ n) :
    |Real.sqrt (rhoN K n c) - Real.sqrt (rhoN K n c')| ≤ contrastDistance c c' := by
  rw [abs_le]
  have hsymm : contrastDistance c' c = contrastDistance c c' := by
    unfold contrastDistance
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    exact abs_sub_comm (c' a) (c a)
  constructor
  · have h := root_minimax_one_sided_contrast_le K n c' c hn
    rw [hsymm] at h
    linarith
  · have h := root_minimax_one_sided_contrast_le K n c c' hn
    linarith

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
