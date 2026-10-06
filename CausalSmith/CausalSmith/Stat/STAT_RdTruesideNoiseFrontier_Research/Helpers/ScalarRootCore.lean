module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Rate

/-!
# Scalar root analysis

Existence, uniqueness, branch identification, and intermediate-branch bounds for the
true-side measurement-error resolution equation.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Given [the smoothness index, sample size, and noise level](hyp:β,n,σ), [the unique-rate-root condition](goal) requires [the root to lie between the direct resolution and one](step:1), [the scalar balance equation to hold](step:2), and [no other point in that interval to solve it](step:3). -/
def UniqueRateRoot (β : ℝ) (n : ℕ) (σ : ℝ) : Prop :=
  rateResolution β n σ ∈ Icc (directResolution β n) 1 ∧
  Real.log n + (2*β+1) * Real.log (rateResolution β n σ) = noiseCost (rateResolution β n σ) σ ∧
  ∀ h ∈ Icc (directResolution β n) 1,
    Real.log n + (2*β+1) * Real.log h = noiseCost h σ → h = rateResolution β n σ
/-- The exact intermediate-compact branch criterion. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def IntermediateCondition (β : ℝ) (n : ℕ) (σ : ℝ) : Prop :=
  Real.log ((n : ℝ) * σ^(4*(2*β+1))) ≤ σ ^ (-2 : ℝ) - 1
/-- The intermediate branch scalar equation. Given [the displayed inputs and assumptions](hyp:β,n,σ,z), [this definition specifies the stated object](goal). -/
def IntermediateEquation (β : ℝ) (n : ℕ) (σ z : ℝ) : Prop :=
  z + (3*(2*β+1)/2) * Real.log z = 1 + Real.log ((n : ℝ) * σ^(2*β+1))
/-- The compact branch scalar equation. Given [the displayed inputs and assumptions](hyp:β,n,σ,τ), [this definition specifies the stated object](goal). -/
def CompactEquation (β : ℝ) (n : ℕ) (σ τ : ℝ) : Prop :=
  2*(2*β+1) * Real.log τ + τ * (1 + Real.log (σ^2 * τ)) = Real.log n + 1
/-- Signed scalar equation whose zero defines the resolution. -/
private def rateScore (β : ℝ) (n : ℕ) (σ h : ℝ) : ℝ :=
  Real.log n + (2 * β + 1) * Real.log h - noiseCost h σ

/-- The direct resolution is positive and at most one. Given [the displayed inputs and assumptions](hyp:β,n,hβ,hn), [the stated mathematical conclusion holds](goal). -/
lemma directResolution_pos_le_one (β : ℝ) (n : ℕ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) :
    directResolution β n ∈ Ioc (0 : ℝ) 1 := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hcoef : 0 < 2 * β + 1 := by linarith [hβ.1]
  have hexp : -1 / (2 * β + 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) hcoef.le
  exact ⟨Real.rpow_pos_of_pos hnpos _,
    Real.rpow_le_one_of_one_le_of_nonpos hnone hexp⟩

private lemma rateScore_direct (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    rateScore β n σ (directResolution β n) ≤ 0 := by
  have hd := directResolution_pos_le_one β n hβ hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hcoef : 0 < 2 * β + 1 := by linarith [hβ.1]
  have hlog : Real.log n + (2 * β + 1) * Real.log (directResolution β n) = 0 := by
    unfold directResolution
    rw [Real.log_rpow hnpos]
    field_simp [hcoef.ne']
    ring
  have hcost := noiseCost_nonneg (directResolution β n) σ hd hσ
  unfold rateScore
  linarith

private lemma direct_log_identity (β : ℝ) (n : ℕ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) :
    Real.log n + (2 * β + 1) * Real.log (directResolution β n) = 0 := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hcoef : 0 < 2 * β + 1 := by linarith [hβ.1]
  unfold directResolution
  rw [Real.log_rpow hnpos]
  field_simp [hcoef.ne']
  ring

private lemma rateScore_one (β : ℝ) (n : ℕ) (σ : ℝ)
    (hσ : σ ∈ Icc (0 : ℝ) 1) : rateScore β n σ 1 = Real.log n := by
  simp [rateScore, noiseCost, hσ.2]

private lemma rateScore_continuousOn (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (rateScore β n σ) (Icc (directResolution β n) 1) := by
  have hd := directResolution_pos_le_one β n hβ hn
  apply ContinuousOn.sub
  · apply ContinuousOn.add continuousOn_const
    exact continuousOn_const.mul
      (Real.continuousOn_log.mono (fun h hh => (hd.1.trans_le hh.1).ne'))
  · exact (noiseCost_continuousOn σ hσ).mono
      (fun h hh => ⟨hd.1.trans_le hh.1, hh.2⟩)

private lemma rateScore_strictMonoOn_Ioc (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    StrictMonoOn (rateScore β n σ) (Ioc 0 1) := by
  have hcoef : 0 < 2 * β + 1 := by linarith [hβ.1]
  intro h hh t ht hlt
  have hlog : Real.log h < Real.log t :=
    Real.strictMonoOn_log hh.1 ht.1 hlt
  have hcost : noiseCost t σ ≤ noiseCost h σ :=
    noiseCost_antitoneOn σ hσ hh ht hlt.le
  unfold rateScore
  nlinarith [mul_lt_mul_of_pos_left hlog hcoef]

private lemma rateScore_strictMonoOn (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    StrictMonoOn (rateScore β n σ) (Icc (directResolution β n) 1) := by
  have hd := directResolution_pos_le_one β n hβ hn
  exact (rateScore_strictMonoOn_Ioc β n σ hβ hσ).mono
    (fun h hh => ⟨hd.1.trans_le hh.1, hh.2⟩)

private lemma noiseCost_pos_of_lt (h σ : ℝ) (hh : 0 < h) (hσ : σ ≤ 1)
    (hlt : h < σ) : 0 < noiseCost h σ := by
  have hspos : 0 < σ := hh.trans hlt
  have hdirect : ¬ σ ≤ h := not_le.mpr hlt
  by_cases hp : σ ^ 4 ≤ h
  · rw [noiseCost, if_neg hdirect, if_pos hp]
    have hratio : 1 < σ / h := (lt_div_iff₀ hh).2 (by simpa using hlt)
    linarith [Real.one_lt_rpow hratio (by norm_num : (0 : ℝ) < 2 / 3)]
  · rw [noiseCost, if_neg hdirect, if_neg hp]
    have hh1 : h < 1 := hlt.trans_le hσ
    have hfactor : 1 < h ^ (-1 / 2 : ℝ) :=
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg hh hh1 (by norm_num)
    have hsqrt : Real.sqrt h < σ ^ 2 := by
      have hfour : h < (σ ^ 2) ^ 2 := by
        simpa [show σ ^ 4 = (σ ^ 2) ^ 2 by ring] using lt_of_not_ge hp
      nlinarith [Real.sq_sqrt hh.le, Real.sqrt_nonneg h, sq_nonneg σ]
    have hlog : 0 ≤ Real.log (σ ^ 2 / Real.sqrt h) :=
      Real.log_nonneg ((le_div_iff₀ (Real.sqrt_pos.2 hh)).2 (by simpa using hsqrt.le))
    have hmul : 1 < h ^ (-1 / 2 : ℝ) *
        (1 + Real.log (σ ^ 2 / Real.sqrt h)) := by
      have hpos : 0 < 1 + Real.log (σ ^ 2 / Real.sqrt h) := by linarith
      have hm := mul_lt_mul_of_pos_right hfactor hpos
      nlinarith
    linarith

private lemma noiseCost_sigma_four (σ : ℝ) (hspos : 0 < σ) (hσ : σ ≤ 1) :
    noiseCost (σ ^ 4) σ = σ ^ (-2 : ℝ) - 1 := by
  have hfour : σ ^ 4 ≤ σ := by
    calc σ ^ 4 ≤ σ ^ 1 := pow_le_pow_of_le_one hspos.le hσ (by omega)
         _ = σ := pow_one _
  have hone := noiseCost_one_power (σ ^ 4) σ (pow_pos hspos 4) le_rfl hfour
  have hp : (σ / σ ^ 4) ^ (2 / 3 : ℝ) = σ ^ (-2 : ℝ) := by
    rw [Real.div_rpow hspos.le (pow_nonneg hspos.le 4),
      ← Real.rpow_natCast σ 4, ← Real.rpow_mul hspos.le,
      ← Real.rpow_sub hspos]
    norm_num
  linarith

private lemma exists_unique_rateScore_root (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    ∃ r ∈ Icc (directResolution β n) 1,
      rateScore β n σ r = 0 ∧
      ∀ h ∈ Icc (directResolution β n) 1,
        rateScore β n σ h ≤ 0 ↔ h ≤ r := by
  have hd := directResolution_pos_le_one β n hβ hn
  have hnlog : 0 < Real.log n := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  have hcont := rateScore_continuousOn β n σ hβ hn hσ
  have hmono := rateScore_strictMonoOn β n σ hβ hn hσ
  have hzmem : 0 ∈ Icc (rateScore β n σ (directResolution β n))
      (rateScore β n σ 1) := by
    rw [rateScore_one β n σ hσ]
    exact ⟨rateScore_direct β n σ hβ hn hσ, hnlog.le⟩
  obtain ⟨r, hr, hrzero⟩ := intermediate_value_Icc hd.2 hcont hzmem
  refine ⟨r, hr, hrzero, ?_⟩
  intro h hh
  constructor
  · intro hscore
    by_contra hnot
    have hlt : r < h := lt_of_not_ge hnot
    have := hmono hr hh hlt
    linarith
  · intro hle
    have := hmono.monotoneOn hh hr hle
    linarith

/-- The supremum construction is the unique root, derived from the piecewise noise cost. Given [the displayed inputs and assumptions](hyp:β,n,σ,hβ,hn,hσ), [the stated mathematical conclusion holds](goal). -/
lemma unique_rate_root (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    UniqueRateRoot β n σ := by
  obtain ⟨r, hr, hrzero, hsub⟩ := exists_unique_rateScore_root β n σ hβ hn hσ
  have hset : {h ∈ Icc (directResolution β n) 1 |
      Real.log n + (2 * β + 1) * Real.log h - noiseCost h σ ≤ 0} =
      Icc (directResolution β n) r := by
    ext h
    simp only [mem_ofPred_eq, mem_Icc]
    constructor
    · intro hh
      exact ⟨hh.1.1, (hsub h hh.1).mp hh.2⟩
    · intro hh
      have hi : h ∈ Icc (directResolution β n) 1 := ⟨hh.1, hh.2.trans hr.2⟩
      exact ⟨hi, (hsub h hi).mpr hh.2⟩
  have hrate : rateResolution β n σ = r := by
    unfold rateResolution
    rw [hset, csSup_Icc hr.1]
  unfold UniqueRateRoot
  rw [hrate]
  refine ⟨hr, ?_, ?_⟩
  · unfold rateScore at hrzero
    linarith
  · intro h hh heq
    apply (rateScore_strictMonoOn β n σ hβ hn hσ).injOn hh hr
    have hhzero : rateScore β n σ h = 0 := by
      unfold rateScore
      linarith
    exact hhzero.trans hrzero.symm

/-- Noise below the direct resolution leaves the scalar root at the direct rate. Given [the displayed inputs and assumptions](hyp:β,n,σ,hβ,hn,hσ,hle), [the stated mathematical conclusion holds](goal). -/
lemma rateResolution_eq_direct_of_le (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (hle : σ ≤ directResolution β n) :
    rateResolution β n σ = directResolution β n := by
  have hd := directResolution_pos_le_one β n hβ hn
  have hroot := unique_rate_root β n σ hβ hn hσ
  symm
  apply (hroot.2.2 (directResolution β n) ⟨le_rfl, hd.2⟩)
  rw [show noiseCost (directResolution β n) σ = 0 by simp [noiseCost, hle]]
  exact direct_log_identity β n hβ hn

/-- Given [the displayed inputs and assumptions](hyp:β,n,σ,hβ,hn,hσ,hnoisy), [the stated mathematical conclusion holds](goal). -/
lemma noisy_rateResolution_interior (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (hnoisy : directResolution β n < σ) :
    directResolution β n < rateResolution β n σ ∧ rateResolution β n σ < σ := by
  have hd := directResolution_pos_le_one β n hβ hn
  have hroot := unique_rate_root β n σ hβ hn hσ
  have hscoreRoot : rateScore β n σ (rateResolution β n σ) = 0 := by
    unfold rateScore
    linarith [hroot.2.1]
  have hcost : 0 < noiseCost (directResolution β n) σ :=
    noiseCost_pos_of_lt _ _ hd.1 hσ.2 hnoisy
  have hscoreDirect : rateScore β n σ (directResolution β n) < 0 := by
    unfold rateScore
    rw [direct_log_identity β n hβ hn]
    linarith
  have hleft : directResolution β n < rateResolution β n σ := by
    exact lt_of_le_of_ne hroot.1.1 (fun heq => by
      rw [heq, hscoreRoot] at hscoreDirect
      linarith)
  have hspos : 0 < σ := hd.1.trans hnoisy
  have hscoreSigma : 0 < rateScore β n σ σ := by
    have hlog := Real.strictMonoOn_log hd.1 hspos hnoisy
    have hcoef : 0 < 2 * β + 1 := by linarith [hβ.1]
    have hcostSigma : noiseCost σ σ = 0 := by simp [noiseCost]
    unfold rateScore
    rw [hcostSigma]
    nlinarith [direct_log_identity β n hβ hn,
      mul_lt_mul_of_pos_left hlog hcoef]
  have hright : rateResolution β n σ < σ := by
    by_contra hnot
    have hle : σ ≤ rateResolution β n σ := le_of_not_gt hnot
    have hm := (rateScore_strictMonoOn_Ioc β n σ hβ hσ).monotoneOn
      ⟨hspos, hσ.2⟩ ⟨hd.1.trans_le hroot.1.1, hroot.1.2⟩ hle
    linarith
  exact ⟨hleft, hright⟩

private lemma rateScore_sigma_four (β : ℝ) (n : ℕ) (σ : ℝ)
    (hn : 2 ≤ n) (hspos : 0 < σ) (hσ : σ ≤ 1) :
    rateScore β n σ (σ ^ 4) =
      Real.log ((n : ℝ) * σ ^ (4 * (2 * β + 1))) - (σ ^ (-2 : ℝ) - 1) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  unfold rateScore
  rw [show noiseCost (σ ^ 4) σ = σ ^ (-2 : ℝ) - 1 from
    noiseCost_sigma_four σ hspos hσ]
  rw [Real.log_mul hnpos.ne' (Real.rpow_pos_of_pos hspos _).ne',
    Real.log_rpow hspos, Real.log_pow]
  ring

/-- Given [the displayed inputs and assumptions](hyp:β,n,σ,hβ,hn,hσ,hnoisy), [the stated mathematical conclusion holds](goal). -/
lemma intermediateCondition_iff (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (hnoisy : directResolution β n < σ) :
    IntermediateCondition β n σ ↔ σ ^ 4 ≤ rateResolution β n σ := by
  have hd := directResolution_pos_le_one β n hβ hn
  have hspos : 0 < σ := hd.1.trans hnoisy
  have hfourpos : 0 < σ ^ 4 := pow_pos hspos 4
  have hfourle : σ ^ 4 ≤ 1 := by
    calc σ ^ 4 ≤ σ ^ 1 := pow_le_pow_of_le_one hspos.le hσ.2 (by omega)
         _ = σ := pow_one _
         _ ≤ 1 := hσ.2
  have hroot := unique_rate_root β n σ hβ hn hσ
  have hrootpos : 0 < rateResolution β n σ := hd.1.trans_le hroot.1.1
  have hscoreRoot : rateScore β n σ (rateResolution β n σ) = 0 := by
    unfold rateScore
    linarith [hroot.2.1]
  have hscoreIff : rateScore β n σ (σ ^ 4) ≤ 0 ↔
      σ ^ 4 ≤ rateResolution β n σ := by
    constructor
    · intro hs
      by_contra hnot
      have hlt := lt_of_not_ge hnot
      have hm := rateScore_strictMonoOn_Ioc β n σ hβ hσ
        ⟨hrootpos, hroot.1.2⟩ ⟨hfourpos, hfourle⟩ hlt
      linarith
    · intro hle
      have hm := (rateScore_strictMonoOn_Ioc β n σ hβ hσ).monotoneOn
        ⟨hfourpos, hfourle⟩ ⟨hrootpos, hroot.1.2⟩ hle
      linarith
  unfold IntermediateCondition
  constructor
  · intro hc
    apply hscoreIff.mp
    rw [rateScore_sigma_four β n σ hn hspos hσ.2]
    linarith
  · intro hc
    have hs := hscoreIff.mpr hc
    rw [rateScore_sigma_four β n σ hn hspos hσ.2] at hs
    linarith

/-- Given [the displayed inputs and assumptions](hyp:β,n,σ,hβ,hn,hσ,heq), [the stated mathematical conclusion holds](goal). -/
lemma direct_interface (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (heq : σ = directResolution β n) :
    rateResolution β n σ = σ ∧ rateResolution β n σ = directResolution β n ∧
      IntermediateEquation β n σ 1 := by
  have hr := rateResolution_eq_direct_of_le β n σ hβ hn hσ heq.le
  have hnpos : (0 : ℝ) < n := by positivity
  have hspos : 0 < σ := heq ▸ (directResolution_pos_le_one β n hβ hn).1
  have hprodlog : Real.log ((n : ℝ) * σ ^ (2 * β + 1)) = 0 := by
    rw [Real.log_mul hnpos.ne' (Real.rpow_pos_of_pos hspos _).ne', Real.log_rpow hspos]
    simpa [heq] using direct_log_identity β n hβ hn
  refine ⟨hr.trans heq.symm, hr, ?_⟩
  unfold IntermediateEquation
  simp [hprodlog]

/-- Given [the displayed inputs and assumptions](hyp:β,n,σ,hβ,hn,hσ,hspos,heq), [the stated mathematical conclusion holds](goal). -/
lemma intermediate_compact_interface (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (hspos : 0 < σ)
    (heq : Real.log ((n : ℝ) * σ ^ (4 * (2 * β + 1))) = σ ^ (-2 : ℝ) - 1) :
    rateResolution β n σ = σ ^ 4 ∧
      IntermediateEquation β n σ (σ ^ (-2 : ℝ)) ∧
      CompactEquation β n σ (σ ^ (-2 : ℝ)) := by
  have hd := directResolution_pos_le_one β n hβ hn
  have hfourpos : 0 < σ ^ 4 := pow_pos hspos 4
  have hfourle : σ ^ 4 ≤ 1 := by
    calc σ ^ 4 ≤ σ ^ 1 := pow_le_pow_of_le_one hspos.le hσ.2 (by omega)
         _ = σ := pow_one _
         _ ≤ 1 := hσ.2
  have hscoreFour : rateScore β n σ (σ ^ 4) = 0 := by
    rw [rateScore_sigma_four β n σ hn hspos hσ.2, heq]
    ring
  have hdirectle : directResolution β n ≤ σ ^ 4 := by
    by_contra hnot
    have hlt : σ ^ 4 < directResolution β n := lt_of_not_ge hnot
    have hm := rateScore_strictMonoOn_Ioc β n σ hβ hσ
      ⟨hfourpos, hfourle⟩ hd hlt
    have hsd := rateScore_direct β n σ hβ hn hσ
    linarith
  have hroot := unique_rate_root β n σ hβ hn hσ
  have hrate : rateResolution β n σ = σ ^ 4 := by
    symm
    apply hroot.2.2 (σ ^ 4) ⟨hdirectle, hfourle⟩
    unfold rateScore at hscoreFour
    linarith
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlogProduct : Real.log ((n : ℝ) * σ ^ (2 * β + 1)) =
      Real.log n + (2 * β + 1) * Real.log σ := by
    rw [Real.log_mul hnpos.ne' (Real.rpow_pos_of_pos hspos _).ne', Real.log_rpow hspos]
  have hlogInv : Real.log (σ ^ (-2 : ℝ)) = -2 * Real.log σ := by
    rw [Real.log_rpow hspos]
  have hlogThreshold : Real.log n + 4 * (2 * β + 1) * Real.log σ =
      σ ^ (-2 : ℝ) - 1 := by
    rw [← heq, Real.log_mul hnpos.ne' (Real.rpow_pos_of_pos hspos _).ne',
      Real.log_rpow hspos]
  have hcancel : σ ^ 2 * σ ^ (-2 : ℝ) = 1 := by
    rw [← Real.rpow_natCast σ 2, ← Real.rpow_add hspos]
    norm_num
  refine ⟨hrate, ?_, ?_⟩
  · unfold IntermediateEquation
    rw [hlogInv, hlogProduct]
    linarith
  · unfold CompactEquation
    rw [hlogInv, hcancel, Real.log_one]
    linarith

/-- Given [the displayed inputs and assumptions](hyp:β,n,σ,hβ,hn,hσ,hnoisy,hinter), [the stated mathematical conclusion holds](goal). -/
lemma intermediate_branch_representation (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (hnoisy : directResolution β n < σ) (hinter : IntermediateCondition β n σ) :
    ∃ z : ℝ, 1 < z ∧ z ≤ σ ^ (-2 : ℝ) ∧ IntermediateEquation β n σ z ∧
      rateResolution β n σ = σ * z ^ (-3 / 2 : ℝ) ∧
      ∀ z' : ℝ, 1 < z' → z' ≤ σ ^ (-2 : ℝ) →
        IntermediateEquation β n σ z' → z' = z := by
  let H := rateResolution β n σ
  let z := (σ / H) ^ (2 / 3 : ℝ)
  have hd := directResolution_pos_le_one β n hβ hn
  have hi := noisy_rateResolution_interior β n σ hβ hn hσ hnoisy
  have hHpos : 0 < H := hd.1.trans hi.1
  have hspos : 0 < σ := hHpos.trans hi.2
  have hbranch : σ ^ 4 ≤ H :=
    (intermediateCondition_iff β n σ hβ hn hσ hnoisy).mp hinter
  have hzpos : 0 < z := Real.rpow_pos_of_pos (div_pos hspos hHpos) _
  have hzone : 1 < z := by
    apply Real.one_lt_rpow
    · exact (one_lt_div hHpos).2 hi.2
    · norm_num
  have hzupper : z ≤ σ ^ (-2 : ℝ) := by
    have hratio : σ / H ≤ σ / σ ^ 4 :=
      div_le_div_of_nonneg_left hspos.le (pow_pos hspos 4) hbranch
    have hp := Real.rpow_le_rpow (div_nonneg hspos.le hHpos.le) hratio
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have heq : (σ / σ ^ 4) ^ (2 / 3 : ℝ) = σ ^ (-2 : ℝ) := by
      rw [Real.div_rpow hspos.le (pow_nonneg hspos.le 4),
        ← Real.rpow_natCast σ 4, ← Real.rpow_mul hspos.le,
        ← Real.rpow_sub hspos]
      norm_num
    exact hp.trans_eq heq
  have hcost : 1 + noiseCost H σ = z := by
    simpa [z] using noiseCost_one_power H σ hHpos hbranch hi.2.le
  have hroot := unique_rate_root β n σ hβ hn hσ
  have hrootEq : Real.log n + (2 * β + 1) * Real.log H = z - 1 := by
    dsimp [H]
    linarith [hroot.2.1, hcost]
  have hlogz : Real.log z = (2 / 3 : ℝ) * (Real.log σ - Real.log H) := by
    dsimp [z]
    rw [Real.log_rpow (div_pos hspos hHpos), Real.log_div hspos.ne' hHpos.ne']
  have hproductlog : Real.log ((n : ℝ) * σ ^ (2 * β + 1)) =
      Real.log n + (2 * β + 1) * Real.log σ := by
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [Real.log_mul hnpos.ne' (Real.rpow_pos_of_pos hspos _).ne', Real.log_rpow hspos]
  have hequation : IntermediateEquation β n σ z := by
    unfold IntermediateEquation
    rw [hproductlog, hlogz]
    nlinarith
  have hresolution : H = σ * z ^ (-3 / 2 : ℝ) := by
    have hratio : 0 ≤ σ / H := (div_pos hspos hHpos).le
    dsimp [z]
    rw [← Real.rpow_mul hratio]
    norm_num
    rw [Real.rpow_neg_one]
    field_simp [hspos.ne', hHpos.ne']
  have hunique : ∀ z' : ℝ, 1 < z' → z' ≤ σ ^ (-2 : ℝ) →
      IntermediateEquation β n σ z' → z' = z := by
    intro z' hz' _ hz'eq
    have hcoef : 0 < 3 * (2 * β + 1) / 2 := by nlinarith [hβ.1]
    apply le_antisymm
    · by_contra hnot
      have hlt : z < z' := lt_of_not_ge hnot
      have hloglt : Real.log z < Real.log z' :=
        Real.strictMonoOn_log hzpos (zero_lt_one.trans hz') hlt
      unfold IntermediateEquation at hequation hz'eq
      nlinarith [mul_lt_mul_of_pos_left hloglt hcoef]
    · by_contra hnot
      have hlt : z' < z := lt_of_not_ge hnot
      have hloglt : Real.log z' < Real.log z :=
        Real.strictMonoOn_log (zero_lt_one.trans hz') hzpos hlt
      unfold IntermediateEquation at hequation hz'eq
      nlinarith [mul_lt_mul_of_pos_left hloglt hcoef]
  exact ⟨z, hzone, hzupper, hequation, hresolution, hunique⟩

/-- Given [the displayed inputs and assumptions](hyp:β,n,σ,hβ,hn,hσ,hnoisy,hinter), [the stated mathematical conclusion holds](goal). -/
lemma intermediate_branch_bounds (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (hnoisy : directResolution β n < σ) (hinter : IntermediateCondition β n σ) :
    let S := 1 + Real.log ((n : ℝ) * σ ^ (2 * β + 1))
    let A := 1 + 3 * (2 * β + 1) / 2
    σ / S ^ (3 / 2 : ℝ) ≤ rateResolution β n σ ∧
      rateResolution β n σ ≤ A ^ (3 / 2 : ℝ) * (σ / S ^ (3 / 2 : ℝ)) := by
  dsimp only
  obtain ⟨z, hz1, _, hzeq, hres, _⟩ :=
    intermediate_branch_representation β n σ hβ hn hσ hnoisy hinter
  let S := 1 + Real.log ((n : ℝ) * σ ^ (2 * β + 1))
  let A := 1 + 3 * (2 * β + 1) / 2
  have hspos : 0 < σ :=
    (directResolution_pos_le_one β n hβ hn).1.trans hnoisy
  have hzpos : 0 < z := zero_lt_one.trans hz1
  have hkpos : 0 < 3 * (2 * β + 1) / 2 := by nlinarith [hβ.1]
  have hApos : 0 < A := by dsimp [A]; linarith
  have hlognonneg : 0 ≤ Real.log z := Real.log_nonneg hz1.le
  have hlogle : Real.log z ≤ z := by
    have := Real.log_le_sub_one_of_pos hzpos
    linarith
  have hSeq : S = z + (3 * (2 * β + 1) / 2) * Real.log z := by
    unfold IntermediateEquation at hzeq
    dsimp [S]
    linarith
  have hSpos : 0 < S := by rw [hSeq]; nlinarith
  have hzS : z ≤ S := by rw [hSeq]; nlinarith
  have hSAz : S ≤ A * z := by
    rw [hSeq]
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hlogle hkpos.le]
  have hzpowpos : 0 < z ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hzpos _
  have hSpowpos : 0 < S ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hSpos _
  have hApowpos : 0 < A ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hApos _
  have hzpow_le : z ^ (3 / 2 : ℝ) ≤ S ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hzpos.le hzS (by norm_num)
  have hSpow_le : S ^ (3 / 2 : ℝ) ≤
      A ^ (3 / 2 : ℝ) * z ^ (3 / 2 : ℝ) := by
    calc
      S ^ (3 / 2 : ℝ) ≤ (A * z) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hSpos.le hSAz (by norm_num)
      _ = _ := Real.mul_rpow hApos.le hzpos.le
  constructor
  · calc
      σ / S ^ (3 / 2 : ℝ) ≤ σ / z ^ (3 / 2 : ℝ) :=
        div_le_div_of_nonneg_left hspos.le hzpowpos hzpow_le
      _ = σ * z ^ (-3 / 2 : ℝ) := by
        rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num,
          Real.rpow_neg hzpos.le]
        ring
      _ = rateResolution β n σ := hres.symm
  · rw [hres, show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num,
      Real.rpow_neg hzpos.le]
    change σ / z ^ (3 / 2 : ℝ) ≤
      A ^ (3 / 2 : ℝ) * (σ / S ^ (3 / 2 : ℝ))
    apply (div_le_iff₀ hzpowpos).2
    rw [show A ^ (3 / 2 : ℝ) * (σ / S ^ (3 / 2 : ℝ)) * z ^ (3 / 2 : ℝ) =
      (A ^ (3 / 2 : ℝ) * σ * z ^ (3 / 2 : ℝ)) / S ^ (3 / 2 : ℝ) by ring]
    apply (le_div_iff₀ hSpowpos).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hSpow_le hspos.le)


end CausalSmith.Stat.RdTruesideNoiseFrontier
