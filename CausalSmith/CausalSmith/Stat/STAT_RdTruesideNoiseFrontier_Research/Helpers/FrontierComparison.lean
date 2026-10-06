module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Handle
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.FrontierRoot
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.MatchedFrontierLower
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.TDirectReduction

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Matched minimax chains and honesty, retaining extended expectations of the observable procedures. Given [the displayed inputs and assumptions](hyp:β,n,σ,c,C), [this definition specifies the stated object](goal). -/
def MatchedFrontier (β : ℝ) (n : ℕ) (σ c C : ℝ) : Prop :=
  c * frontierRate β n σ ≤ risk β n σ ∧
  ENNReal.ofReal (risk β n σ) ≤ attainerRisk β n σ ∧
  attainerRisk β n σ ≤ ENNReal.ofReal (certificate β n σ) ∧
  certificate β n σ ≤ C * frontierRate β n σ ∧
  c * frontierRate β n σ ≤ lengthRisk β n σ ∧
  ENNReal.ofReal (lengthRisk β n σ) ≤ attainerLength β n σ ∧
  attainerLength β n σ ≤ ENNReal.ofReal (2 * certificate β n σ) ∧
  2 * certificate β n σ ≤ C * frontierRate β n σ ∧
  honestAttainer β n σ ∈ honestIntervals β n σ

/-- The real minimax absolute risk embeds below the selected estimator's
extended worst-case risk. -/
private lemma minimaxRisk_ofReal_le_attainerRisk (β : ℝ) (n : ℕ) (σ : ℝ) :
    ENNReal.ofReal (risk β n σ) ≤ attainerRisk β n σ := by
  unfold risk attainerRisk
  rw [ENNReal.ofReal_toReal (risk_value_ne_top β σ n)]
  exact Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk
    (risk := fun (T : Estimator n) (P : {P // Model β σ P}) => absRisk P.val σ n T.val)
    (attainer β n σ)

/-- The real minimax honest length embeds below the selected interval's
extended worst-case expected length. -/
private lemma minimaxLength_ofReal_le_attainerLength (β : ℝ) (n : ℕ) (σ : ℝ)
    (hh : honestAttainer β n σ ∈ honestIntervals β n σ) :
    ENNReal.ofReal (lengthRisk β n σ) ≤ attainerLength β n σ := by
  unfold lengthRisk attainerLength
  rw [ENNReal.ofReal_toReal (length_value_ne_top β σ n)]
  have hm := Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk
    (risk := fun (I : {I // I ∈ honestIntervals β n σ}) (P : {P // Model β σ P}) =>
      expectedLength P.val σ n I.val)
    ⟨honestAttainer β n σ, hh⟩
  exact hm

/-- Once the two scalar comparisons and the finite certificate are available,
the exact matched-frontier conjunction is purely order-theoretic. -/
private lemma matchedFrontier_of_scalar_bounds
    (legendre_of_gate : ClassicalLegendreFacts) (hermite_of_gate : ClassicalHermiteFacts)
    (β : ℝ) (n : ℕ) (σ c C : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlowerRisk : c * frontierRate β n σ ≤ risk β n σ)
    (hlowerLength : c * frontierRate β n σ ≤ lengthRisk β n σ)
    (hupper : certificate β n σ ≤ C * frontierRate β n σ) :
    MatchedFrontier β n σ c (2 * C) := by
  let P := directAltLaw β 1 true hβ (by norm_num)
  have hP : Model β σ P := directAltLaw_model β 1 σ true hβ (by norm_num)
  have hcert := finite_certificate β σ n 1 P
    hβ hσ hn (by omega) hP
  have hh := hcert.2.2.2.1
  have hr := hcert.2.2.2.2.1
  have hl := hcert.2.2.2.2.2
  have hrate : 0 ≤ frontierRate β n σ := by
    unfold frontierRate
    have hr := unique_rate_root β n σ hβ hn hσ
    have hd := directResolution_pos_le_one β n hβ hn
    exact Real.rpow_nonneg (hd.1.trans_le hr.1.1).le _
  have hCr : 0 ≤ C * frontierRate β n σ := mul_nonneg hC hrate
  unfold MatchedFrontier
  refine ⟨hlowerRisk, minimaxRisk_ofReal_le_attainerRisk β n σ, hr, ?_,
    hlowerLength, minimaxLength_ofReal_le_attainerLength β n σ hh, hl, ?_, hh⟩
  · exact hupper.trans (by nlinarith)
  · nlinarith

/-- Constructed upper procedures and all-procedure lower witnesses give the matched minimax chains. Given [the displayed inputs and assumptions](hyp:legendre_of_gate,hermite_of_gate,β,hβ), [the stated mathematical conclusion holds](goal). -/
lemma matched_frontier (legendre_of_gate : ClassicalLegendreFacts)
    (hermite_of_gate : ClassicalHermiteFacts) (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ σ ∈ Icc (0 : ℝ) 1,
      MatchedFrontier β n σ c C := by
  obtain ⟨c, hc, hlower⟩ :=
    frontierRate_lower_bounds legendre_of_gate hermite_of_gate β hβ
  obtain ⟨C, hC, hupper⟩ :=
    certificate_le_frontierRate legendre_of_gate hermite_of_gate β hβ
  refine ⟨c, 2 * C, hc, by positivity, ?_⟩
  intro n hn σ hσ
  have hl := hlower n hn σ hσ
  exact matchedFrontier_of_scalar_bounds legendre_of_gate hermite_of_gate
    β n σ c C hβ hn hσ hc.le hC.le hl.1 hl.2 (hupper n hn σ hσ)

end CausalSmith.Stat.RdTruesideNoiseFrontier
