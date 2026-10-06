module

public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DirectGaussianChannel
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DirectZeroInformation
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.TwoPoint

/-!
# IID testing and two-point direct lower-bound assembly
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


/-- Given [the displayed inputs and assumptions](hyp:beta,n,hbeta,hn), [the stated mathematical conclusion holds](goal). -/
lemma directResolution_balance (beta : ℝ) (n : ℕ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) :
    (n : ℝ) * (directResolution beta n)^(2*beta+1) = 1 ∧
      (directResolution beta n)^beta = (n : ℝ)^(-beta/(2*beta+1)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : 2 * beta + 1 ≠ 0 := by linarith [hbeta.1]
  unfold directResolution
  constructor
  · rw [← Real.rpow_mul hnpos.le]
    have he : (-1 / (2 * beta + 1)) * (2 * beta + 1) = -1 := by
      field_simp
    rw [he, Real.rpow_neg_one]
    field_simp
  · rw [← Real.rpow_mul hnpos.le]
    congr 1
    field_simp

/-- The generic two-point calculation specialized to the legal direct bump
alternatives.  Its hypothesis is exactly the observed-product testing bound;
the independent procedure seed is appended by `experiment_tv_le`. Given [the displayed inputs and assumptions](hyp:β,h,σ,n,hβ,hh,hn,hσ,htv), [the stated mathematical conclusion holds](goal). -/
lemma direct_two_point_transfer
    (β h σ : ℝ) (n : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : h ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (htv : tvDist (sampleLaw (directAltLaw β h true hβ hh) σ n)
      (sampleLaw (directAltLaw β h false hβ hh) σ n) ≤ (1/5 : ℝ)) :
    (4/5 : ℝ) * kappa * h^β ≤ risk β n σ ∧
    (6/5 : ℝ) * kappa * h^β ≤ lengthRisk β n σ := by
  let P := directAltLaw β h true hβ hh
  let Q := directAltLaw β h false hβ hh
  have hP : Model β σ P := directAltLaw_model β h σ true hβ hh
  have hQ : Model β σ Q := directAltLaw_model β h σ false hβ hh
  have hsep : |theta P - theta Q| = 2 * kappa * h^β :=
    directAltLaw_separation β h hβ hh
  letI := experiment_probability P σ n
  letI := experiment_probability Q σ n
  have ht : tvDist (experiment P σ n) (experiment Q σ n) ≤ (1/5 : ℝ) :=
    (experiment_tv_le P Q σ n).trans htv
  have hk : 0 ≤ kappa * h^β :=
    mul_nonneg (by norm_num [kappa]) (Real.rpow_nonneg hh.1.le _)
  constructor
  · apply (ENNReal.ofReal_le_iff_le_toReal (risk_value_ne_top β σ n)).mp
    apply Causalean.Stat.le_minimaxValueENNReal_of_two_point
      (⟨P,hP⟩ : {P // Model β σ P}) (⟨Q,hQ⟩ : {P // Model β σ P})
    intro T
    apply twoPoint_max_of_sum _ _ _ (by nlinarith [hk])
    have hs := twoPoint_absRisk_sum (experiment P σ n) (experiment Q σ n)
      T.val T.property (theta P) (theta Q)
    change ENNReal.ofReal (2 * ((4/5 : ℝ) * kappa * h^β)) ≤ _
    apply le_trans _ hs
    apply ENNReal.ofReal_le_ofReal
    rw [hsep]
    nlinarith
  · apply (ENNReal.ofReal_le_iff_le_toReal (length_value_ne_top β σ n)).mp
    apply Causalean.Stat.le_minimaxValueENNReal
    intro I
    have hs := twoPoint_interval_lower (experiment P σ n) (experiment Q σ n)
      I.val.lo I.val.hi I.val.lo_meas I.val.hi_meas (theta P) (theta Q)
      (I.property P hP) (I.property Q hQ) ht
    rw [hsep] at hs
    have he : (3/5 : ℝ) * (2 * kappa * h^β) =
        (6/5 : ℝ) * kappa * h^β := by ring
    rw [he] at hs
    exact hs.trans (Causalean.Stat.le_worstCaseRiskENNReal
      (risk := fun (I : {I // I ∈ honestIntervals β n σ})
        (L : {L // Model β σ L}) => expectedLength L.val σ n I.val) I ⟨Q,hQ⟩)

/-- The legal direct witnesses give the ordinary boundary-regression lower
bound uniformly over every public noise scale. Given [the displayed inputs and assumptions](hyp:beta,hbeta), [the stated mathematical conclusion holds](goal). -/
lemma direct_uniform_lower (beta : ℝ) (hbeta : beta ∈ Ioc (0 : ℝ) 1) :
    let c := (4 / 5 : ℝ) * kappa
    0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ sigma ∈ Icc (0 : ℝ) 1,
      c * (n : ℝ)^(-beta/(2*beta+1)) ≤ risk beta n sigma ∧
      c * (n : ℝ)^(-beta/(2*beta+1)) ≤ lengthRisk beta n sigma := by
  dsimp only
  refine ⟨by norm_num [kappa], ?_⟩
  intro n hn sigma hsigma
  let h := directResolution beta n
  have hh : h ∈ Ioc (0 : ℝ) 1 := by
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hcoef : 0 < 2 * beta + 1 := by linarith [hbeta.1]
    have hexp : -1 / (2 * beta + 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) hcoef.le
    exact ⟨Real.rpow_pos_of_pos hnpos _,
      Real.rpow_le_one_of_one_le_of_nonpos hnone hexp⟩
  let P := directAltLaw beta h true hbeta hh
  let Q := directAltLaw beta h false hbeta hh
  letI := P.prob
  letI := Q.prob
  letI : IsProbabilityMeasure (Pobs P 0) :=
    Measure.isProbabilityMeasure_map (obs_measurable 0).aemeasurable
  letI : IsProbabilityMeasure (Pobs Q 0) :=
    Measure.isProbabilityMeasure_map (obs_measurable 0).aemeasurable
  have hac : Pobs P 0 ≪ Pobs Q 0 :=
    directAltLaw_observed_ac_zero beta h hbeta hh
  have hint : Integrable (fun o =>
      (((Pobs P 0).rnDeriv (Pobs Q 0) o).toReal - 1)^2) (Pobs Q 0) :=
    directAltLaw_observed_likelihood_square_integrable_zero beta h hbeta hh
  have hbalance := directResolution_balance beta n hbeta hn
  change (n : ℝ) * h^(2*beta+1) = 1 ∧
    h^beta = (n : ℝ)^(-beta/(2*beta+1)) at hbalance
  have hchi := directAltLaw_observed_chiSqDiv_zero_le beta h hbeta hh
  have hbudget : (n : ℝ) * Causalean.Stat.chiSqDiv (Pobs P 0) (Pobs Q 0) ≤
      1 / 100 := by
    calc
      _ ≤ (n : ℝ) * ((16 / 3 : ℝ) * kappa^2 * h^(2*beta+1)) :=
        mul_le_mul_of_nonneg_left hchi (Nat.cast_nonneg n)
      _ = (16 / 3 : ℝ) * kappa^2 := by
        calc
          _ = ((16 / 3 : ℝ) * kappa^2) *
              ((n : ℝ) * h^(2*beta+1)) := by ring
          _ = _ := by rw [hbalance.1, mul_one]
      _ ≤ 1 / 100 := by norm_num [kappa]
  have htv0 : tvDist (sampleLaw P 0 n) (sampleLaw Q 0 n) ≤ (1 / 5 : ℝ) := by
    exact Causalean.Stat.iid_tv_le_one_fifth_of_chiSqDiv (Pobs P 0) (Pobs Q 0)
      hac hint n hbudget
  have hP : Model beta sigma P := directAltLaw_model beta h sigma true hbeta hh
  have hQ : Model beta sigma Q := directAltLaw_model beta h sigma false hbeta hh
  have htv : tvDist (sampleLaw P sigma n) (sampleLaw Q sigma n) ≤ (1 / 5 : ℝ) :=
    (sampleLaw_tv_le_zero_of_model beta sigma n P Q hP hQ).trans htv0
  have htransfer := direct_two_point_transfer beta h sigma n hbeta hh hn hsigma htv
  rw [hbalance.2] at htransfer
  exact ⟨htransfer.1, htransfer.2.trans' (by
    have hrpow : 0 ≤ (n : ℝ)^(-beta/(2*beta+1)) := Real.rpow_nonneg (by positivity) _
    have hk : 0 ≤ kappa := by norm_num [kappa]
    nlinarith)⟩

end CausalSmith.Stat.RdTruesideNoiseFrontier
