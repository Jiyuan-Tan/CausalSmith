module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PublicCertificate

/-! TObservableUpper -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
universe u


/-- At least three observations make each modulo-three split block nonempty. [Under the stated conditions](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: blocksNonempty_of_three
lemma blocksNonempty_of_three (n : ℕ) (hn : 3 ≤ n) : blocksNonempty n := by
  intro r hr
  refine ⟨⟨r, lt_of_lt_of_le hr hn⟩, ?_⟩
  simp [splitBlock, Nat.mod_eq_of_lt hr]

/-- The observable estimator and branch-specific dictionary witnesses attain the risk frontier with one noise-uniform threshold. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: thm:observable-upper
theorem observable_upper (K : ClassConstants) (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) -- @realizes beta(smoothness exponent in (0,1])
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
      ∀ sigma ∈ Icc (0 : ℝ) (1/4), -- @realizes sigma(public error scale in [0,1/4])
      (∀ P : modelClass E K beta kappa sigma,
        IIDSampling n sigma (P.1 : Measure (StructSpace S)) (experiment n sigma (P.1 : Measure (StructSpace S))) →
        (∫ data, |totalEstimator K beta kappa n sigma data - causalTarget E (P.1 : Measure (StructSpace S))|
          ∂experiment n sigma (P.1 : Measure (StructSpace S))) ≤ C*frontierRate beta kappa sigma n) ∧
      (sigma ≤ (logScale n)^(-1/2 : ℝ) → ∃ k : ℕ,
        DictTag.fourier k ∈ weightDictionary n sigma ∧
        PairAdmissible kappa sigma (pairOf sigma (.fourier k)) ∧
        VqENN kappa sigma (pairOf sigma (.fourier k)).ell < ⊤ ∧
        score K beta kappa n sigma (.fourier k) ≤ C*frontierRate beta kappa sigma n) ∧
      ((logScale n)^(-1/2 : ℝ) < sigma → ∃ j : ℕ,
        DictTag.poly j ∈ weightDictionary n sigma ∧
        PairAdmissible kappa sigma (pairOf sigma (.poly j)) ∧
        VqENN kappa sigma (pairOf sigma (.poly j)).ell < ⊤ ∧
        score K beta kappa n sigma (.poly j) ≤ C*frontierRate beta kappa sigma n) := by
  obtain ⟨CF, hCF, nF, hF⟩ := fourier_dictionary_witness beta kappa hbeta hkappa
  obtain ⟨CM, hCM, nM, hM⟩ := inverseheat_dictionary_witness beta kappa hbeta hkappa
  refine ⟨scoreScale K * max CF CM, mul_pos (scoreScale_pos K) (lt_max_of_lt_left hCF), max 3 (max nF nM), ?_⟩
  intro S _ E n hn sigma hsigma
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hn
  have hnF : nF ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnM : nM ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hlog : 0 ≤ logScale n := Real.log_nonneg (by
    exact one_le_mul_of_one_le_of_one_le hexp hnreal)
  have hrho : 0 ≤ frontierRate beta kappa sigma n := Real.rpow_nonneg (by
    unfold frontierScale
    split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · exact div_nonneg hsigma.1 (Real.sqrt_nonneg _)
    · exact div_nonneg (Real.log_nonneg (by
        have hm : 0 ≤ sigma^2 * logScale n := mul_nonneg (sq_nonneg sigma) hlog
        linarith)) hlog) _
  have hFourier : sigma ≤ (logScale n)^(-1/2 : ℝ) → ∃ k : ℕ,
      DictTag.fourier k ∈ weightDictionary n sigma ∧
      PairAdmissible kappa sigma (pairOf sigma (.fourier k)) ∧
      VqENN kappa sigma (pairOf sigma (.fourier k)).ell < ⊤ ∧
      score K beta kappa n sigma (.fourier k) ≤ scoreScale K * max CF CM * frontierRate beta kappa sigma n := by
    intro hbranch
    obtain ⟨k, hk, hscore⟩ := hF n hnF sigma hsigma hbranch
    obtain ⟨hq, hV, _⟩ := (dictionary_score_rate E K beta kappa hbeta hkappa).1
      n (by omega) sigma hsigma _ hk
    exact ⟨k, hk, hq, hV,
      score_le_of_unitScore_le K beta kappa sigma hkappa hsigma n _ hk (hscore.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrho))⟩
  have hPoly : (logScale n)^(-1/2 : ℝ) < sigma → ∃ j : ℕ,
      DictTag.poly j ∈ weightDictionary n sigma ∧
      PairAdmissible kappa sigma (pairOf sigma (.poly j)) ∧
      VqENN kappa sigma (pairOf sigma (.poly j)).ell < ⊤ ∧
      score K beta kappa n sigma (.poly j) ≤ scoreScale K * max CF CM * frontierRate beta kappa sigma n := by
    intro hbranch
    obtain ⟨j, hj, hscore⟩ := hM n hnM sigma hsigma hbranch
    obtain ⟨hq, hV, _⟩ := (dictionary_score_rate E K beta kappa hbeta hkappa).1
      n (by omega) sigma hsigma _ hj
    exact ⟨j, hj, hq, hV,
      score_le_of_unitScore_le K beta kappa sigma hkappa hsigma n _ hj (hscore.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hrho))⟩
  obtain ⟨hselected, hmin⟩ := selectedTag_minimizes K beta kappa n sigma
  have hscore : score K beta kappa n sigma (selectedTag K beta kappa n sigma) ≤
      scoreScale K * max CF CM * frontierRate beta kappa sigma n := by
    by_cases hbranch : sigma ≤ (logScale n)^(-1/2 : ℝ)
    · obtain ⟨k, hk, _, _, hbound⟩ := hFourier hbranch
      exact (hmin _ hk).trans hbound
    · obtain ⟨j, hj, _, _, hbound⟩ := hPoly (lt_of_not_ge hbranch)
      exact (hmin _ hj).trans hbound
  refine ⟨?_, hFourier, hPoly⟩
  intro P hiid
  obtain ⟨hq, hV, hlaw⟩ := (dictionary_score_rate E K beta kappa hbeta hkappa).1
    n (by omega) sigma hsigma _ hselected
  have hcert := public_error_certificate E beta kappa hbeta hkappa n hn3 sigma hsigma
    (P.1 : Measure (StructSpace S)) P.2 hiid
    (pairOf sigma (selectedTag K beta kappa n sigma)) hq (hlaw P) hV
  simpa only [totalEstimator, if_pos (blocksNonempty_of_three n hn3), score] using
    hcert.trans hscore

end CausalSmith.Stat.NoisydoseWeakdesignTransition
