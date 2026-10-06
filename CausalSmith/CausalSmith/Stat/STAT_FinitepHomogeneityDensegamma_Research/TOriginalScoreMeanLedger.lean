module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.MeanErrorBounds
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ProjectionGeometry
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreMeans
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TruncationMoments
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.WeightedSeparation
public import Causalean.Stat.UStatistic.LocalizedVariance.Mean

/-! Finite-moment homogeneity testing: TOriginalScoreMeanLedger. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Ledgertheta: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the law parameter](hyp:law), [the c parameter](hyp:c). [This is the stated defined object](goal). -/
def ledgerTheta (n : ℕ) (v : Params) (law : ObservedLaw) (c : ℝ) : Vec (ledgerM n v) := thetaVec law (ledgerScore n v false) c
/-- The explicit mean error ledger calibrates the whole original-mean constant null.  [the parameters and conditions in the statement](hyp:v,hv,n,hn,law,hm,b,c0,hc0), [the asserted mathematical result holds](goal). -/
-- @node: ledgerTheta_null_norm_le
lemma ledgerTheta_null_norm_le (v : Params) (hv : v.Valid) (n : ℕ) (hn : 4 ≤ n)
    (law : ObservedLaw) (hm : InModel v law) (b : Bool) (c0 : ℝ)
    (hc0 : ∀ x, law.tau x=c0) :
    ‖thetaVec law (ledgerScore n v b) c0‖ ≤ ledgerBias n v := by
  have herror := ledgerScore_weighted_mean_error_le v hv n hn law hm b c0
  have hzero : (∫ x,
        (law.e x*(1-projOp (ledgerK n v) law.e x)*(law.tau x-c0)) •
          featureMap (ledgerM n v) x ∂design) = 0 := by
    simp only [hc0, sub_self, mul_zero, zero_smul, integral_zero]
  simpa only [hzero, sub_zero] using herror

/-- [Original score mean ledger](goal). For \(n\ge4\) use Definition \(\mathrm{def:explicit\mbox{-}score\mbox{-}ledger}\), and put \(e_K=\Pi_K e_P\) and \(w_K=e_P(1-e_K)\). The mean \(\theta_P(c)=E_PZ_b(c)\) satisfies, for every \(|c|\le1/2\), \[ \left\|\theta_P(c)-\int_0^1 F_M(x)w_K(x)(\tau_P(x)-c)\,dx\right\|_2\le B, \qquad \|\theta_P(c)\|_2\ge\frac3{16}d(P)-16M^{-\gamma}-B. \] If \(P\in H_0(v)\) with effect \(c_0\), then \(\|\theta_P(c_0)\|_2\le B\). These bounds require no regularity of clipped conditional means. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hm condition](hyp:hm). -/
-- @node: lem:original-score-mean-ledger
lemma original_score_mean_ledger (v : Params) (hv : v.Valid) (n : ℕ) (hn : 4 ≤ n)
    (law : ObservedLaw) (hm : InModel v law) :
    (∀ b c, Integrable (ledgerScore n v b c) (Measure.pi fun _ : Fin n => law.P)) ∧
    (∀ b : Bool, ∀ c : ℝ, |c| ≤ 1/2 →
      ‖thetaVec law (ledgerScore n v b) c-∫ x, (law.e x*(1-projOp (ledgerK n v) law.e x)*(law.tau x-c)) • featureMap (ledgerM n v) x ∂design‖ ≤ ledgerBias n v ∧
      (3/16)*hetDist law-16*(ledgerM n v:ℝ)^(-v.γ)-ledgerBias n v ≤ ‖thetaVec law (ledgerScore n v b) c‖) ∧
    (InNull v law → ∀ b : Bool, ∀ c0 : ℝ, (∀ x, law.tau x=c0) →
      ‖thetaVec law (ledgerScore n v b) c0‖ ≤ ledgerBias n v) := by
  refine ⟨fun b c => integrable_ledgerScore n v b c law, ?_, ?_⟩
  · intro b c hc
    refine ⟨ledgerScore_weighted_mean_error_le v hv n hn law hm b c, ?_⟩
    obtain ⟨hM, hMK, _⟩ := ledger_increment_rank_bound n v hn
    have hK : 0 < ledgerK n v := lt_of_lt_of_le hM hMK
    have hdiv := ledger_coarse_dvd_fine n v hn
    have hsep := weighted_effect_coefficient_separation v hv law hm
      (ledgerM n v) (ledgerK n v) hM hK hdiv c hc
    have herr := ledgerScore_weighted_mean_error_le v hv n hn law hm b c
    change ‖thetaVec law (ledgerScore n v b) c-∫ x,
      (law.e x*(1-projOp (ledgerK n v) law.e x)*(law.tau x-c)) •
        featureMap (ledgerM n v) x ∂design‖ ≤ ledgerBias n v at herr
    have htri := norm_sub_le (thetaVec law (ledgerScore n v b) c)
      (thetaVec law (ledgerScore n v b) c-∫ x,
        (law.e x*(1-projOp (ledgerK n v) law.e x)*(law.tau x-c)) •
          featureMap (ledgerM n v) x ∂design)
    rw [sub_sub_cancel] at htri
    have hpow : 0 ≤ (ledgerM n v:ℝ)^(-v.γ) := by positivity
    linarith
  · intro hnull b c0 hc0
    exact ledgerTheta_null_norm_le v hv n hn law hm b c0 hc0

end CausalSmith.Stat.FinitepHomogeneityDensegamma
