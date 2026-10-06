module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.OneCell
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedCompleteArrivalFrontier

/-! Squared-risk consequences of the one-cell observed-law testing family. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: oneCell_two_point_risk_floor
/-- Given [the specified inputs and assumptions](hyp:n,d,x,q,hn,hq,hq1), [the stated mathematical conclusion holds](goal). -/
lemma oneCell_two_point_risk_floor {n d : ℕ} (x : Fin d) (q : ℝ)
    (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∀ T : Estimator n d,
      (1 / 256 : ℝ) * min 1 (effectiveSize n q)⁻¹ ≤
        max
          (squaredRisk T
            (oneCellFamilyLaw x (1 / 2) q (by norm_num) ⟨hq.le, hq1⟩))
          (squaredRisk T
            (oneCellFamilyLaw x (1 / 2 + oneCellStep n q) q
              (oneCellStep_mem n q hn hq) ⟨hq.le, hq1⟩)) := by
  let P₀ := oneCellFamilyLaw x (1 / 2) q (by norm_num) ⟨hq.le, hq1⟩
  let P₁ := oneCellFamilyLaw x (1 / 2 + oneCellStep n q) q
    (oneCellStep_mem n q hn hq) ⟨hq.le, hq1⟩
  have hgap : ate P₁ = ate P₀ + oneCellStep n q := by
    simp [P₀, P₁, oneCellFamilyLaw_ate]
  have hrisk := complete_arrival_two_point_decision_reduction P₀ P₁
    (oneCellStep n q) (1 / 2) (oneCellStep_pos n q hn hq) (by norm_num)
    hgap (oneCell_product_testing_half x n q hn hq hq1)
  intro T
  have hstep := oneCellStep_sq_lower n q hn hq
  calc
    (1 / 256 : ℝ) * min 1 (effectiveSize n q)⁻¹ ≤
        (1 / 16) * (oneCellStep n q) ^ 2 := by nlinarith
    _ = (1 / 2) * (oneCellStep n q) ^ 2 / 8 := by ring
    _ ≤ max (squaredRisk T P₀) (squaredRisk T P₁) := hrisk T

-- @node: oneCell_minimax_risk_floors
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hq1,hslice), [the stated mathematical conclusion holds](goal). -/
lemma oneCell_minimax_risk_floors {n d : ℕ} (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1)
    (hslice : RareArrivalSlice n q) :
    (1 / 256 : ℝ) * min 1 (effectiveSize n q)⁻¹ ≤ minimaxRisk n d q ∧
    (1 / 256 : ℝ) * min 1 (effectiveSize n q)⁻¹ ≤ noSurrogateRisk n d q := by
  let x : Fin d := ⟨0, hd⟩
  let P₀ := oneCellFamilyLaw x (1 / 2) q (by norm_num) ⟨hq.le, hq1⟩
  let P₁ := oneCellFamilyLaw x (1 / 2 + oneCellStep n q) q
    (oneCellStep_mem n q hn hq) ⟨hq.le, hq1⟩
  have hP₀ : RareArrivalModelClass n d q P₀ :=
    oneCellFamilyLaw_model x (1 / 2) q hn hd (by norm_num) hq hq1 hslice
  have hP₁ : RareArrivalModelClass n d q P₁ :=
    oneCellFamilyLaw_model x (1 / 2 + oneCellStep n q) q hn hd
      (oneCellStep_mem n q hn hq) hq hq1 hslice
  have hNS₀ : ∀ᵐ r : FullRecord d ∂P₀.1, r.S0 = false ∧ r.S1 = false :=
    oneCellFamilyLaw_noSurrogate x (1 / 2) q (by norm_num) ⟨hq.le, hq1⟩
  have hNS₁ : ∀ᵐ r : FullRecord d ∂P₁.1, r.S0 = false ∧ r.S1 = false :=
    oneCellFamilyLaw_noSurrogate x (1 / 2 + oneCellStep n q) q
      (oneCellStep_mem n q hn hq) ⟨hq.le, hq1⟩
  have htwo : ∀ T : Estimator n d,
      (1 / 256 : ℝ) * min 1 (effectiveSize n q)⁻¹ ≤
        max (squaredRisk T P₀) (squaredRisk T P₁) := by
    simpa [P₀, P₁] using oneCell_two_point_risk_floor x q hn hq hq1
  let T₀ : Estimator n d :=
    Estimator.ofMap (fun _ => 0) ⟨measurable_const, by intro s; norm_num⟩
  letI : Nonempty (Estimator n d) := ⟨T₀⟩
  constructor
  · let θ₀ : {P : FullLaw d // RareArrivalModelClass n d q P} := ⟨P₀, hP₀⟩
    let θ₁ : {P : FullLaw d // RareArrivalModelClass n d q P} := ⟨P₁, hP₁⟩
    unfold minimaxRisk
    apply Causalean.Stat.le_minimaxValue_of_two_point θ₀ θ₁
    · intro T
      refine ⟨4, ?_⟩
      rintro r ⟨θ, rfl⟩
      exact (unrestricted_squaredRisk_bounds T θ.1).2
    · exact htwo
  · let θ₀ : {P : FullLaw d // RareArrivalModelClass n d q P ∧
        ∀ᵐ r : FullRecord d ∂P.1, r.S0 = false ∧ r.S1 = false} :=
      ⟨P₀, hP₀, hNS₀⟩
    let θ₁ : {P : FullLaw d // RareArrivalModelClass n d q P ∧
        ∀ᵐ r : FullRecord d ∂P.1, r.S0 = false ∧ r.S1 = false} :=
      ⟨P₁, hP₁, hNS₁⟩
    unfold noSurrogateRisk
    apply Causalean.Stat.le_minimaxValue_of_two_point θ₀ θ₁
    · intro T
      refine ⟨4, ?_⟩
      rintro r ⟨θ, rfl⟩
      exact (unrestricted_squaredRisk_bounds T θ.1).2
    · exact htwo

end CausalSmith.Stat.MarRareqLogfrontier
