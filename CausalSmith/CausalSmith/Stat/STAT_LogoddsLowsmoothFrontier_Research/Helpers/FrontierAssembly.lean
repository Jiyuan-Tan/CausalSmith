module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FrontierElbows
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_FiniteHonestUpper
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ParametricNullFloor

/-! # Assembling the honest frontier

The proved upper construction supplies the operational guarantees and both
upper comparisons. The parametric floor supplies the numerator branch above
the elbow. Separate numerator and radius lower estimates combine into the
full profile against every honest, possibly randomized procedure.
-/
public section
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [A pointwise bound on expected length bounds the radius-slice supremum;
the concrete parametric null certifies that this slice is nonempty. [the documented result](goal) Under [the stated assumptions](hyp:hr,h). -/
-- @node: worstLength_le_of_expectedLength_bound
lemma worstLength_le_of_expectedLength_bound (n : ℕ) (α β r B : ℝ)
    (I : Procedure n) (hr : 0 ≤ r)
    (h : ∀ P, RadiusModel α β r P → expectedLength P n I ≤ B) :
    worstLength n α β r I ≤ B := by
  apply csSup_le
  · exact ⟨expectedLength (parametricLaw 0) n I, parametricLaw 0,
      parametricLaw_null_radius α β r hr, rfl⟩
  · rintro l ⟨P, hP, rfl⟩
    exact h P hP

/-- The finite honest upper theorem certifies the literal implementation's operational guarantees and the two upper comparisons with one absolute constant. the documented result Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: frontier_upper_comparisons
lemma frontier_upper_comparisons : ∃ C : ℝ, 0 < C ∧
    ∀ (E : ArithmeticEngine), E.Admissible →
    ∀ (N : NamingPolicy) (hN : N.Admissible) (α β : ℝ), ExponentDomain α β →
    ∀ n : ℕ, 1 ≤ n →
      FrontierOperational E N hN n α β ∧
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) (1/2) →
        lengthObjective n α β r ≤ worstLength n α β r (upperInterval E N hN n α β) ∧
        worstLength n α β r (upperInterval E N hN n α β) ≤ C * rate n α β r := by
  obtain ⟨C, hC, hUpper⟩ := finite_honest_upper
  refine ⟨C, hC, ?_⟩
  intro E hE N hN α β hD n hn
  obtain ⟨hHonest, hLength, hShape, hOne⟩ := hUpper E hE N hN α β hD n hn
  refine ⟨⟨hHonest, hShape, ?_, hOne⟩, ?_⟩
  · intro o u v
    rfl
  · intro r hr
    exact ⟨lengthObjective_le n α β r _ hHonest,
      worstLength_le_of_expectedLength_bound n α β r _ _ hr.1 (hLength r hr)⟩

/-- [Above and at the numerator elbow, the parametric null comparison supplies
the numerator lower rate for every honest procedure and every radius. [the documented result](goal) Under [the stated assumptions](hyp:hD,hs,hr,hn,hI). -/
-- @node: frontier_parametric_numerator_lower
lemma frontier_parametric_numerator_lower (α β r : ℝ) (n : ℕ)
    (hD : ExponentDomain α β) (hs : 1/2 ≤ α + β)
    (hr : r ∈ Set.Icc (0 : ℝ) (1/2)) (hn : 1 ≤ n)
    (I : Procedure n) (hI : HonestProcedure n α β I) :
    (3/16 : ℝ) * (n : ℝ) ^ (-exponentA α β) ≤ worstLength n α β r I := by
  rw [exponentA_high_branch α β hD hs]
  exact (parametric_null_floor α β r n hD hn hr).trans
    (lengthObjective_le n α β r I hI)

/-- [A lower estimate in the rough numerator regime extends to the whole
domain by taking the smaller of its constant and the proved parametric constant. [the documented result](goal) Under [the stated assumptions](hyp:hRough). -/
-- @node: frontier_numerator_lower_of_rough
lemma frontier_numerator_lower_of_rough (cA : ℝ)
    (hRough : ∀ α β r : ℝ, ExponentDomain α β → α + β ≤ 1/2 →
      r ∈ Set.Icc (0 : ℝ) (1/2) → ∀ n : ℕ, 1 ≤ n →
      ∀ I : Procedure n, HonestProcedure n α β I →
        cA * (n : ℝ) ^ (-exponentA α β) ≤ worstLength n α β r I) :
    ∀ α β r : ℝ, ExponentDomain α β → r ∈ Set.Icc (0 : ℝ) (1/2) →
      ∀ n : ℕ, 1 ≤ n → ∀ I : Procedure n, HonestProcedure n α β I →
        min cA (3/16) * (n : ℝ) ^ (-exponentA α β) ≤ worstLength n α β r I := by
  intro α β r hD hr n hn I hI
  by_cases hs : α + β ≤ 1/2
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
      (hRough α β r hD hs hr n hn I hI)
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans
      (frontier_parametric_numerator_lower α β r n hD (le_of_lt (lt_of_not_ge hs)) hr hn I hI)

/-- The positive-radius lower estimate extends to radius zero by the
nonnegativity of expected interval length, without a new comparison prior. [the documented result](goal) Under [the stated assumptions](hyp:hPositive). -/
-- @node: frontier_radius_lower_of_positive
lemma frontier_radius_lower_of_positive (cB : ℝ)
    (hPositive : ∀ α β r : ℝ, ExponentDomain α β → r ∈ Set.Ioc (0 : ℝ) (1/2) →
      ∀ n : ℕ, 1 ≤ n → ∀ I : Procedure n, HonestProcedure n α β I →
        cB * (r * (n : ℝ) ^ (-exponentB β)) ≤ worstLength n α β r I) :
    ∀ α β r : ℝ, ExponentDomain α β → r ∈ Set.Icc (0 : ℝ) (1/2) →
      ∀ n : ℕ, 1 ≤ n → ∀ I : Procedure n, HonestProcedure n α β I →
        cB * (r * (n : ℝ) ^ (-exponentB β)) ≤ worstLength n α β r I := by
  intro α β r hD hr n hn I hI
  rcases hr.1.eq_or_lt with hzero | hpos
  · rw [← hzero, zero_mul, mul_zero]
    exact worstLength_nonneg n α β 0 I
  · exact hPositive α β r hD ⟨hpos, hr.2⟩ n hn I hI

/-- Simultaneous numerator and radius lower estimates give half the smaller
constant times their sum, as in the testing-to-length roadmap. [the documented result](goal) Under [the stated assumptions](hyp:hA,hB). Under [the stated assumptions](hyp:hr). -/
-- @node: frontier_rate_lower_of_two
lemma frontier_rate_lower_of_two (n : ℕ) (α β r cA cB : ℝ) (hr : 0 ≤ r)
    (I : Procedure n)
    (hA : cA * (n : ℝ) ^ (-exponentA α β) ≤ worstLength n α β r I)
    (hB : cB * (r * (n : ℝ) ^ (-exponentB β)) ≤ worstLength n α β r I) :
    (min cA cB / 2) * rate n α β r ≤ worstLength n α β r I := by
  have hA' := (mul_le_mul_of_nonneg_right (min_le_left cA cB)
    (by positivity : 0 ≤ (n : ℝ) ^ (-exponentA α β))).trans hA
  have hB' := (mul_le_mul_of_nonneg_right (min_le_right cA cB)
    (mul_nonneg hr (by positivity : 0 ≤ (n : ℝ) ^ (-exponentB β)))).trans hB
  unfold rate diagnosticEnvelope
  linarith

/-- The proved operational and upper guarantees and a universal procedure lower bound give all three frontier comparisons, transferring the lower bound to the infimum over honest procedures. the documented result Under the stated assumptions. [The stated hypotheses](hyp:hUpper,hLower) hold, and [the stated conclusion follows](goal). -/
-- @node: universalFrontier_of_procedure_lower
lemma universalFrontier_of_procedure_lower (c C : ℝ)
    (hUpper : ∀ (E : ArithmeticEngine), E.Admissible →
      ∀ (N : NamingPolicy) (hN : N.Admissible) (α β : ℝ), ExponentDomain α β →
      ∀ n : ℕ, 1 ≤ n → FrontierOperational E N hN n α β ∧
        ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) (1/2) →
          lengthObjective n α β r ≤ worstLength n α β r (upperInterval E N hN n α β) ∧
          worstLength n α β r (upperInterval E N hN n α β) ≤ C * rate n α β r)
    (hLower : ∀ α β r : ℝ, ExponentDomain α β → r ∈ Set.Icc (0 : ℝ) (1/2) →
      ∀ n : ℕ, 1 ≤ n → ∀ I : Procedure n, HonestProcedure n α β I →
        c * rate n α β r ≤ worstLength n α β r I) : UniversalFrontier c C := by
  intro E hE N hN α β hD n hn
  obtain ⟨hOperational, hComparison⟩ := hUpper E hE N hN α β hD n hn
  refine ⟨hOperational, ?_⟩
  intro r hr
  exact ⟨le_lengthObjective n α β r _ (hLower α β r hD hr n hn), hComparison r hr⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier
