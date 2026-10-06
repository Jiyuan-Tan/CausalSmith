module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.PolynomialTuning

/-! The compact-support inverse-heat dictionary witness, assembled from S11--S16. -/
public section
noncomputable section
open Set Filter
open scoped Topology
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- This branch supplies a dictionary witness with score at most a fixed multiple of the frontier. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: inverseheat_dictionary_witness
lemma inverseheat_dictionary_witness (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      (logScale n)^(-1/2 : ℝ) < sigma →
      ∃ j : ℕ,
        DictTag.poly j ∈ weightDictionary n sigma ∧
        unitScore beta kappa n sigma (.poly j) ≤
          C*frontierRate beta kappa sigma n := by
  obtain ⟨C, hC, hcert⟩ := qM_tuned_certificate_bound beta kappa hbeta hkappa
  have hevent : ∀ᶠ n : ℕ in atTop,
      (∀ sigma ∈ Icc (0 : ℝ) (1/4), (logScale n)^(-1/2 : ℝ) < sigma → ∃ j : ℕ,
        DictTag.poly j ∈ weightDictionary n sigma ∧
        unitScore beta kappa n sigma (.poly j) ≤
          (C*(16384 : ℝ)^beta)*frontierRate beta kappa sigma n) := by
    filter_upwards [hcert, polynomial_tuned_dictionary_degree,
      directScale_eventually_below_log_cutoff beta kappa hbeta hkappa,
      eventually_ge_atTop 1] with n hncert hndegree hncut hn1
    intro sigma hsigma hbranch
    obtain ⟨j, hjmem, hjodd, hjlo, hjhi⟩ := hndegree sigma hsigma
    have hLpos : 0 < logScale n := lt_of_lt_of_le zero_lt_one (logScale_one_le n hn1)
    let B := Real.log (Real.exp 1+sigma^2*logScale n)
    have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one
      (polynomial_log_denominator_one_le _ _ hLpos.le)
    have hmpos : 0 < (2^j+1 : ℕ) := Nat.succ_pos _
    have hmR : (0 : ℝ) < (2^j+1 : ℕ) := by exact_mod_cast hmpos
    have hscale : ((2^j+1 : ℕ) : ℝ)⁻¹ ≤ 16384*polynomialScale sigma n := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hmR).mpr
      have hmul := (div_le_iff₀ (show 0 < 16384*B by positivity)).mp hjlo
      have heq : 16384*polynomialScale sigma n*((2^j+1 : ℕ) : ℝ) =
          (((2^j+1 : ℕ) : ℝ)*(16384*B))/logScale n := by
        dsimp [polynomialScale, B]
        ring
      rw [heq]
      exact (le_div_iff₀ hLpos).mpr (by simpa only [one_mul] using hmul)
    have hpolypos : 0 < polynomialScale sigma n := div_pos hBpos hLpos
    have hb : (((2^j+1 : ℕ) : ℝ)⁻¹)^beta ≤
        (16384 : ℝ)^beta*(polynomialScale sigma n)^beta := by
      calc
        _ ≤ (16384*polynomialScale sigma n)^beta :=
          Real.rpow_le_rpow (by positivity) hscale (by linarith [hbeta.1])
        _ = _ := Real.mul_rpow (by norm_num) hpolypos.le
    have hc := hncert sigma (2^j+1) hjodd hmpos hjhi
    refine ⟨j, hjmem, ?_⟩
    have hdirect : ¬ sigma ≤ directScale beta kappa n := not_le.mpr (hncut.trans_lt hbranch)
    have hfourier : ¬ sigma ≤ (logScale n)^(-1/2 : ℝ) := not_le.mpr hbranch
    have hfront : frontierRate beta kappa sigma n = (polynomialScale sigma n)^beta := by
      simp only [frontierRate, frontierScale, if_neg hdirect, if_neg hfourier]
    rw [hfront]
    calc
      unitScore beta kappa n sigma (.poly j) ≤ C*(((2^j+1 : ℕ) : ℝ)⁻¹)^beta := hc
      _ ≤ C*((16384 : ℝ)^beta*(polynomialScale sigma n)^beta) :=
        mul_le_mul_of_nonneg_left hb hC.le
      _ = _ := by ring
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact ⟨C*(16384 : ℝ)^beta, by positivity, N, hN⟩


end CausalSmith.Stat.NoisydoseWeakdesignTransition
