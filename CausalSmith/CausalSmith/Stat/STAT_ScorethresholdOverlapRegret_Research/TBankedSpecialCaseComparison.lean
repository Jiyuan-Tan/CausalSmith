module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.RiskBounds
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.TPhaseBoundary

/-! # Score-threshold overlap regret — accepted-bank comparison

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

/-- The current right-threshold, zero-tie restricted class at (1,1,1). -/
def RestrictedClass (n : ℕ) (P : RowLaw) (e : ℝ → ℝ) : Prop :=
  LawClass 1 1 1 n P e ∧
  P.PX.real {x | P.tau x = 0} = 0 ∧
  (∃ t ∈ Set.Icc (0:ℝ) 1,
    canonicalPolicy P =ᵐ[P.PX] rightThr t) ∨
  (LawClass 1 1 1 n P e ∧
    P.PX.real {x | P.tau x = 0} = 0 ∧
    canonicalPolicy P =ᵐ[P.PX] (fun _ => true))

-- @node: restrictedClass_subset_lawClass
/-- Every law in the comparison subclass satisfies the full present law class. -/
lemma restrictedClass_subset_lawClass (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (h : RestrictedClass n P e) : LawClass 1 1 1 n P e := by
  rcases h with h | h
  · exact h.1
  · exact h.1

/-- Restricted minimax risk, with the same full fixed-logger learner class. -/
noncomputable def restrictedMinimaxRegret (n : ℕ) : ℝ :=
  ⨅ Φ : {Φ : Learner n // LearnerClass n Φ},
    ⨆ Pe : {Pe : RowLaw × (ℝ → ℝ) // RestrictedClass n Pe.1 Pe.2},
      ∫ du, rawRegret Pe.1.1 (fun x => Φ.1 Pe.1.2 du.1 du.2 x)
        ∂experiment Pe.1.1 n

/-- Exact hypotheses of the cited bank lower-bound theorem. -/
def BankAdmissible (α γ u0 cB Cm Co co underlineP : ℝ)
    (policySet : Set (CausalSmith.Stat.PolicyRegretMarginOverlap.Policy ℝ)) : Prop :=
  CausalSmith.Stat.PolicyRegretMarginOverlap.MarginWindow u0 ∧
  0 ≤ α ∧ 0 ≤ γ ∧ 0 < Cm ∧ 0 < Co ∧ 0 < co ∧ 0 < cB ∧
  cB ≤ Cm ∧ cB ≤ Co ∧ 0 < underlineP ∧
  (0 < γ → 0 < α → cB ≤ Co*co^(-(α/γ))) ∧
  (0 < γ → α = 0 → cB ≤ Co*(4:ℝ)^(-(1/γ))) ∧
  underlineP ≤ 1/4 ∧ 8*cB < Real.log 5 ∧
  policySet.Nonempty ∧ (∀ π ∈ policySet, Measurable π)

-- @node: mHi_one_one_mem
/-- The high-effect cutoff on the comparison slice is in the score interval. -/
lemma mHi_one_one_mem (n : ℕ) (hn : 1 ≤ n) :
    mHi 1 1 n ∈ Set.Icc (0:ℝ) 1 := by
  have hnreal : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hbase : (1:ℝ) ≤ 64*(n:ℝ) := by nlinarith
  have hq0 : 0 < qHi 1 n := by
    unfold qHi
    positivity
  have hq1 : qHi 1 n ≤ 1 := by
    unfold qHi
    apply Real.rpow_le_one_of_one_le_of_nonpos hbase
    norm_num
  simp only [mHi]
  norm_num at *
  constructor <;> nlinarith

-- @node: highPair_no_ties
/-- Both high-effect alternatives have nonzero conditional effect at every score. -/
lemma highPair_no_ties (α θ : ℝ) (n : ℕ) (σ : Bool) (x : ℝ) :
    (highPair α θ n σ).tau x ≠ 0 := by
  cases σ <;> simp [highPair, blockPair, blockMeanOne, blockMeanZero, hHi] <;>
    split_ifs <;> norm_num

-- @node: highPair_restrictedClass
/-- High-effect alternatives lie in the comparison subclass once their law-class
conditions hold. -/
lemma highPair_restrictedClass (n : ℕ) (σ : Bool)
    (hClass : LawClass 1 1 1 n (highPair 1 1 n σ) (highLogger 1 1 n))
    (hm : mHi 1 1 n ∈ Set.Icc (0:ℝ) 1)
    (hCanonical : σ = false →
      canonicalPolicy (highPair 1 1 n σ) =ᵐ[(highPair 1 1 n σ).PX]
        rightThr (mHi 1 1 n)) :
    RestrictedClass n (highPair 1 1 n σ) (highLogger 1 1 n) := by
  have hzero : {x | (highPair 1 1 n σ).tau x = 0} = ∅ := by
    ext x
    simp [highPair_no_ties]
  have hmass : (highPair 1 1 n σ).PX.real
      {x | (highPair 1 1 n σ).tau x = 0} = 0 := by
    rw [hzero]
    simp
  cases σ with
  | false =>
      left
      exact ⟨hClass, hmass, mHi 1 1 n, hm, hCanonical rfl⟩
  | true =>
      right
      exact ⟨hClass, hmass, Filter.Eventually.of_forall
        (fun x => congrFun (highPair_true_canonical 1 1 n) x)⟩

-- @node: highPair_restrictedClass_eventually
/-- Both high-effect alternatives eventually belong to the restricted class. -/
lemma highPair_restrictedClass_eventually :
    ∃ N : ℕ, ∀ n ≥ N, ∀ σ : Bool,
      RestrictedClass n (highPair 1 1 n σ) (highLogger 1 1 n) := by
  obtain ⟨N, hN⟩ := highPair_mem_lawClass 1 1 1 (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨max N 1, ?_⟩
  intro n hn σ
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  exact highPair_restrictedClass n σ (hN n hnN σ).1
    (mHi_one_one_mem n hn1) (hN n hnN σ).2.2

-- @node: restrictedMinimaxRegret_lower_of_highPair
/-- A uniform two-point risk floor transfers to the restricted minimax risk. -/
lemma restrictedMinimaxRegret_lower_of_highPair (n : ℕ) (b : ℝ)
    (hmem : ∀ σ : Bool,
      RestrictedClass n (highPair 1 1 n σ) (highLogger 1 1 n))
    (hBdd : ∀ Φ : {Φ : Learner n // LearnerClass n Φ},
      BddAbove (Set.range (fun Pe : {Pe : RowLaw × (ℝ → ℝ) //
          RestrictedClass n Pe.1 Pe.2} =>
        ∫ du, rawRegret Pe.1.1 (fun x => Φ.1 Pe.1.2 du.1 du.2 x)
          ∂experiment Pe.1.1 n)))
    (hrisk : ∀ Φ : Learner n, LearnerClass n Φ →
      max (∫ du, rawRegret (highPair 1 1 n true)
            (fun x => Φ (highLogger 1 1 n) du.1 du.2 x)
            ∂experiment (highPair 1 1 n true) n)
          (∫ du, rawRegret (highPair 1 1 n false)
            (fun x => Φ (highLogger 1 1 n) du.1 du.2 x)
            ∂experiment (highPair 1 1 n false) n) ≥ b) :
    b ≤ restrictedMinimaxRegret n := by
  have hNonempty : Nonempty {Φ : Learner n // LearnerClass n Φ} :=
    ⟨⟨fun _ _ _ _ => false, by
      intro e he heRange
      constructor
      · exact measurable_const
      · intro e' heq z
        rfl⟩⟩
  letI := hNonempty
  unfold restrictedMinimaxRegret
  apply le_ciInf
  intro Φ
  have htrue :
      (∫ du, rawRegret (highPair 1 1 n true)
          (fun x => Φ.1 (highLogger 1 1 n) du.1 du.2 x)
          ∂experiment (highPair 1 1 n true) n) ≤
        (⨆ Pe : {Pe : RowLaw × (ℝ → ℝ) // RestrictedClass n Pe.1 Pe.2},
          ∫ du, rawRegret Pe.1.1 (fun x => Φ.1 Pe.1.2 du.1 du.2 x)
            ∂experiment Pe.1.1 n) := by
    let Pe : {Pe : RowLaw × (ℝ → ℝ) // RestrictedClass n Pe.1 Pe.2} :=
      ⟨(highPair 1 1 n true, highLogger 1 1 n), hmem true⟩
    exact le_ciSup_of_le (hBdd Φ) Pe le_rfl
  have hfalse :
      (∫ du, rawRegret (highPair 1 1 n false)
          (fun x => Φ.1 (highLogger 1 1 n) du.1 du.2 x)
          ∂experiment (highPair 1 1 n false) n) ≤
        (⨆ Pe : {Pe : RowLaw × (ℝ → ℝ) // RestrictedClass n Pe.1 Pe.2},
          ∫ du, rawRegret Pe.1.1 (fun x => Φ.1 Pe.1.2 du.1 du.2 x)
            ∂experiment Pe.1.1 n) := by
    let Pe : {Pe : RowLaw × (ℝ → ℝ) // RestrictedClass n Pe.1 Pe.2} :=
      ⟨(highPair 1 1 n false, highLogger 1 1 n), hmem false⟩
    exact le_ciSup_of_le (hBdd Φ) Pe le_rfl
  exact (hrisk Φ.1 Φ.2).trans (max_le htrue hfalse)

-- @node: restrictedMinimaxRegret_upper_of_uniform_risk
/-- A uniform risk bound for one admissible learner bounds restricted minimax risk. -/
lemma restrictedMinimaxRegret_upper_of_uniform_risk (n : ℕ) (b : ℝ)
    (Φ : Learner n) (hΦ : LearnerClass n Φ)
    (hNonempty : Nonempty {Pe : RowLaw × (ℝ → ℝ) //
      RestrictedClass n Pe.1 Pe.2})
    (hBelow : BddBelow (Set.range (fun Ψ : {Ψ : Learner n // LearnerClass n Ψ} =>
      ⨆ Pe : {Pe : RowLaw × (ℝ → ℝ) // RestrictedClass n Pe.1 Pe.2},
        ∫ du, rawRegret Pe.1.1 (fun x => Ψ.1 Pe.1.2 du.1 du.2 x)
          ∂experiment Pe.1.1 n)))
    (hRisk : ∀ Pe : {Pe : RowLaw × (ℝ → ℝ) // RestrictedClass n Pe.1 Pe.2},
      (∫ du, rawRegret Pe.1.1 (fun x => Φ Pe.1.2 du.1 du.2 x)
        ∂experiment Pe.1.1 n) ≤ b) :
    restrictedMinimaxRegret n ≤ b := by
  letI := hNonempty
  unfold restrictedMinimaxRegret
  exact (ciInf_le hBelow ⟨Φ, hΦ⟩).trans (ciSup_le hRisk)

-- @node: thm:banked-special-case-comparison
/-- The imported accepted-bank lower bound supplies the slice-exponent lower-bound clause. -/
theorem banked_special_case_comparison :
    (∀ α γ θ : ℝ, 0 < α → 0 < γ → θ = 1/γ →
      rExp α γ θ = min (rBank α γ) (1/(γ+1))) ∧
    (∀ α γ : ℝ, 0 < γ →
      bankBeta α γ = α*γ/(α+1) ∧
      bankD α γ = 2+α+bankBeta α γ ∧
      (1+α)/bankD α γ = rBank α γ) ∧
    (rBank 1 1 = 4/7 ∧ (1:ℝ)/(1+1) = 1/2 ∧ rExp 1 1 1 = 1/2) ∧
    (∃ c C : ℝ, ∃ N : ℕ, 0 < c ∧ c ≤ C ∧
      ∀ n ≥ N,
        c*(n:ℝ)^(-(1/2:ℝ)) ≤ restrictedMinimaxRegret n ∧
        restrictedMinimaxRegret n ≤ C*(n:ℝ)^(-(1/2:ℝ))) ∧
    (rExp 1 (2/3) (3/2) = 3/5 ∧
      rExp 1 2 (1/2) = 1/3) ∧
    (∀ (α γ u0 cB Cm Co co underlineP : ℝ)
        (policySet : Set (CausalSmith.Stat.PolicyRegretMarginOverlap.Policy ℝ)),
      BankAdmissible α γ u0 cB Cm Co co underlineP policySet →
      0 < α → 0 < γ → ∀ θ : ℝ, θ = 1/γ →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
        c*(n:ℝ)^(-((α+1)/(α+2+α*γ/(α+θ*γ)))) ≤
          bankMinimaxRegret α γ u0 cB Cm Co co underlineP policySet n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α γ θ hα hγ hθ
    subst θ
    have ht : 0 < (1/γ : ℝ) := by positivity
    rw [rExp_eq_min_branches α γ (1/γ) hα hγ ht, rBank_of_pos α γ hγ]
    congr 1
    · unfold rLoc DExp betaExp
      have hγ0 : γ ≠ 0 := ne_of_gt hγ
      field_simp
    · unfold rHi
      have hγ0 : γ ≠ 0 := ne_of_gt hγ
      field_simp
      ring
  · intro α γ hγ
    have hγ0 : γ ≠ 0 := ne_of_gt hγ
    simp [bankBeta, bankD, rBank, hγ0, add_comm, add_left_comm]
  · constructor
    · norm_num [rBank, bankD, bankBeta]
    constructor
    · norm_num
    · norm_num [rExp, sExp, sLoc, sHi, betaExp]
  · obtain ⟨c1, c2, hc1, hc2, hInfo⟩ := high_information_all_procedure
      1 1 1 (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hInfo
    obtain ⟨N1, hMem⟩ := highPair_restrictedClass_eventually
    obtain ⟨C0, N2, hC0, hUpper⟩ := upper_bound
      1 1 1 (by norm_num) (by norm_num) (by norm_num)
    have hr : rExp 1 1 1 = (1/2:ℝ) := by
      norm_num [rExp, sExp, sLoc, sHi, betaExp]
    refine ⟨c2, max c2 C0, max (max N0 N1) (max N2 1), hc2,
      le_max_left _ _, ?_⟩
    intro n hn
    have hn0 : N0 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
    have hn1 : N1 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
    have hn2 : N2 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
    have hnPos : 0 < n := lt_of_lt_of_le (by omega : 0 < 1)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
    have hmem := hMem n hn1
    have hNonempty : Nonempty {Pe : RowLaw × (ℝ → ℝ) // RestrictedClass n Pe.1 Pe.2} :=
      ⟨⟨(highPair 1 1 n true, highLogger 1 1 n), hmem true⟩⟩
    letI := hNonempty
    have hBdd (Φ : {Φ : Learner n // LearnerClass n Φ}) :
        BddAbove (Set.range (fun Pe : {Pe : RowLaw × (ℝ → ℝ) //
            RestrictedClass n Pe.1 Pe.2} =>
          ∫ du, rawRegret Pe.1.1 (fun x => Φ.1 Pe.1.2 du.1 du.2 x)
            ∂experiment Pe.1.1 n)) := by
      refine ⟨4, ?_⟩
      rintro y ⟨Pe, rfl⟩
      exact (expectedRawRegret_bounds 1 1 1 n Pe.1.1 Pe.1.2
        (restrictedClass_subset_lawClass n Pe.1.1 Pe.1.2 Pe.2) Φ.1).2
    constructor
    · apply restrictedMinimaxRegret_lower_of_highPair n _ hmem hBdd
      intro Φ hΦ
      have h := (hN0 n hn0).2.2.2 Φ hΦ
      have heq : c1 * mHi 1 1 n * hHi = c2 * (n:ℝ)^(-(1/2:ℝ)) := by
        convert h.2 using 1 <;> norm_num
      rw [heq] at h
      exact h.1
    · let Φ : Learner n := fun e d _ x => rateSelector 1 1 1 e d x
      have hΦ : LearnerClass n Φ := rateSelector_learnerClass
        1 1 1 n (by norm_num) (by norm_num) (by norm_num) hnPos
      have hBelow : BddBelow (Set.range (fun Ψ : {Ψ : Learner n // LearnerClass n Ψ} =>
          ⨆ Pe : {Pe : RowLaw × (ℝ → ℝ) // RestrictedClass n Pe.1 Pe.2},
            ∫ du, rawRegret Pe.1.1 (fun x => Ψ.1 Pe.1.2 du.1 du.2 x)
              ∂experiment Pe.1.1 n)) := by
        refine ⟨0, ?_⟩
        rintro y ⟨Ψ, rfl⟩
        let Pe : {Pe : RowLaw × (ℝ → ℝ) // RestrictedClass n Pe.1 Pe.2} :=
          ⟨(highPair 1 1 n true, highLogger 1 1 n), hmem true⟩
        exact (expectedRawRegret_bounds 1 1 1 n Pe.1.1 Pe.1.2
          (restrictedClass_subset_lawClass n Pe.1.1 Pe.1.2 Pe.2) Ψ.1).1.trans
            (le_ciSup_of_le (hBdd Ψ) Pe le_rfl)
      apply restrictedMinimaxRegret_upper_of_uniform_risk n _ Φ hΦ hNonempty hBelow
      intro Pe
      have hP := restrictedClass_subset_lawClass n Pe.1.1 Pe.1.2 Pe.2
      have hpol (d : Fin n → Observation) :
          rateSelector 1 1 1 Pe.1.2 d ∈ binaryPolicyClass :=
        thresholdClass_subset_binaryPolicyClass _
          (firstScannedMinimizer_mem_thresholdClass _ _ _)
      have heq (d : Fin n → Observation) :
          rawRegret Pe.1.1 (rateSelector 1 1 1 Pe.1.2 d) =
            regret (Pe.1.1.toWellFormedLaw hP.wf hP.bounded)
              (measurablePolicy (rateSelector 1 1 1 Pe.1.2 d)) := by
        simp [regret, RowLaw.toWellFormedLaw, measurablePolicy, hpol d]
      change (∫ du, rawRegret Pe.1.1 (rateSelector 1 1 1 Pe.1.2 du.1)
        ∂experiment Pe.1.1 n) ≤ _
      simp_rw [heq]
      rw [integral_experiment_ignore_randomizer Pe.1.1 n hP.wf
        (fun d => regret (Pe.1.1.toWellFormedLaw hP.wf hP.bounded)
          (measurablePolicy (rateSelector 1 1 1 Pe.1.2 d)))]
      have h := hUpper n hn2 Pe.1.1 Pe.1.2 hP
      rw [hr] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · constructor
    · norm_num [rExp, sExp, sLoc, sHi, betaExp]
    · norm_num [rExp, sExp, sLoc, sHi, betaExp]
  · intro α γ u0 cB Cm Co co underlineP policySet hAd hα hγ θ hθ
    subst θ
    rcases hAd with ⟨hu0, hα0, hγ0, hCm, hCo, hco, hcB, hcBCm, hcBCo,
      hp, hwindow1, hwindow2, hpBound, hlog, hset, hmeas⟩
    obtain ⟨c, hc, hbound⟩ := bankedLocalSubstrate_proved
      α γ u0 cB Cm Co co underlineP policySet
      hu0 hα0 hγ0 hCm hCo hco hcB hcBCm hcBCo hp hwindow1 hwindow2
      hpBound hlog hset hmeas
    refine ⟨c, hc, ?_⟩
    filter_upwards [hbound] with n hn
    convert hn using 1
    have hγne : γ ≠ 0 := ne_of_gt hγ
    rw [rBank_of_pos α γ hγ]
    congr 1
    field_simp

end CausalSmith.Stat.ScorethresholdOverlapRegret
