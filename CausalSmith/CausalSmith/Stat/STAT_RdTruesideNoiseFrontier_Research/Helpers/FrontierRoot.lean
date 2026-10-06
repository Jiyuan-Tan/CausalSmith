module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.ScalarRootCompact

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

/-- The constructed resolution is a root in the declared interval and is its only root there. Given [the displayed inputs and assumptions](hyp:β,n,σ,c,C), [this definition specifies the stated object](goal). -/
def FrontierBranches (β : ℝ) (n : ℕ) (σ c C : ℝ) : Prop :=
  (σ ≤ directResolution β n → rateResolution β n σ = directResolution β n) ∧
  (directResolution β n < σ →
    directResolution β n < rateResolution β n σ ∧ rateResolution β n σ < σ ∧
    (IntermediateCondition β n σ ↔ σ^4 ≤ rateResolution β n σ) ∧
    (IntermediateCondition β n σ →
      ∃ z : ℝ, 1 < z ∧ z ≤ σ ^ (-2 : ℝ) ∧ IntermediateEquation β n σ z ∧
        rateResolution β n σ = σ * z ^ (-3/2 : ℝ) ∧
        (∀ z' : ℝ, 1 < z' → z' ≤ σ ^ (-2 : ℝ) → IntermediateEquation β n σ z' → z' = z) ∧
        c * (σ / (1 + Real.log ((n : ℝ) * σ^(2*β+1)))^(3/2 : ℝ)) ≤ rateResolution β n σ ∧
        rateResolution β n σ ≤ C * (σ / (1 + Real.log ((n : ℝ) * σ^(2*β+1)))^(3/2 : ℝ))) ∧
    (¬ IntermediateCondition β n σ →
      ∃ τ : ℝ, σ ^ (-2 : ℝ) < τ ∧ CompactEquation β n σ τ ∧
        rateResolution β n σ = τ ^ (-2 : ℝ) ∧
        (∀ τ' : ℝ, σ ^ (-2 : ℝ) < τ' → CompactEquation β n σ τ' → τ' = τ) ∧
        c * ((1 + Real.log n) / Real.log (Real.exp 1 + σ^2 * (1 + Real.log n))) ≤ τ ∧
        τ ≤ C * ((1 + Real.log n) / Real.log (Real.exp 1 + σ^2 * (1 + Real.log n))) ∧
        c * (Real.log (Real.exp 1 + σ^2 * (1 + Real.log n)) / (1 + Real.log n))^(2*β) ≤ frontierRate β n σ ∧
        frontierRate β n σ ≤ C * (Real.log (Real.exp 1 + σ^2 * (1 + Real.log n)) / (1 + Real.log n))^(2*β))) ∧
  (0 < σ → Real.log ((n : ℝ) * σ^(4*(2*β+1))) = σ ^ (-2 : ℝ) - 1 →
    rateResolution β n σ = σ^4 ∧
    IntermediateEquation β n σ (σ ^ (-2 : ℝ)) ∧ CompactEquation β n σ (σ ^ (-2 : ℝ))) ∧
  (σ = directResolution β n →
    rateResolution β n σ = σ ∧ rateResolution β n σ = directResolution β n ∧
    IntermediateEquation β n σ 1)

private lemma compact_branch_representation (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (hnoisy : directResolution β n < σ) (hcompact : ¬ IntermediateCondition β n σ) :
    ∃ τ : ℝ, σ ^ (-2 : ℝ) < τ ∧ CompactEquation β n σ τ ∧
      rateResolution β n σ = τ ^ (-2 : ℝ) ∧
      ∀ τ' : ℝ, σ ^ (-2 : ℝ) < τ' → CompactEquation β n σ τ' → τ' = τ := by
  let H := rateResolution β n σ
  let τ := H ^ (-1 / 2 : ℝ)
  have hd := directResolution_pos_le_one β n hβ hn
  have hi := noisy_rateResolution_interior β n σ hβ hn hσ hnoisy
  have hHpos : 0 < H := hd.1.trans hi.1
  have hspos : 0 < σ := hHpos.trans hi.2
  have hHfour : H < σ ^ 4 := lt_of_not_ge (fun hle =>
    hcompact ((intermediateCondition_iff β n σ hβ hn hσ hnoisy).mpr hle))
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hHpos _
  have hτlower : σ ^ (-2 : ℝ) < τ := by
    have hp := (Real.rpow_lt_rpow_iff_of_neg (pow_pos hspos 4) hHpos
      (by norm_num : (-1 / 2 : ℝ) < 0)).mpr hHfour
    have heq : (σ ^ 4) ^ (-1 / 2 : ℝ) = σ ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast σ 4, ← Real.rpow_mul hspos.le]
      norm_num
    exact heq ▸ hp
  have hres : H = τ ^ (-2 : ℝ) := by
    dsimp [τ]
    rw [← Real.rpow_mul hHpos.le]
    norm_num
  have hsqrt : σ ^ 2 / Real.sqrt H = σ ^ 2 * τ := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hHpos.le]
    congr 2
    · norm_num
  have hcost := noiseCost_one_compact H σ hHpos hHfour.le hσ.2 hspos
  have hroot := unique_rate_root β n σ hβ hn hσ
  have hlogτ : Real.log τ = (-1 / 2 : ℝ) * Real.log H := by
    dsimp [τ]
    rw [Real.log_rpow hHpos]
  have hrootEq : Real.log n + (2 * β + 1) * Real.log H = noiseCost H σ := by
    exact hroot.2.1
  have hcancel : 2 * (2 * β + 1) * Real.log τ =
      -(2 * β + 1) * Real.log H := by rw [hlogτ]; ring
  have hequation : CompactEquation β n σ τ := by
    rw [hsqrt] at hcost
    change 1 + noiseCost H σ = τ * (1 + Real.log (σ ^ 2 * τ)) at hcost
    unfold CompactEquation
    change 2 * (2 * β + 1) * Real.log τ +
      τ * (1 + Real.log (σ ^ 2 * τ)) = Real.log n + 1
    rw [hcancel]
    nlinarith [hrootEq]
  refine ⟨τ, hτlower, hequation, ?_, ?_⟩
  · exact hres
  · intro τ' hτ' heq'
    apply compactScalar_unique β n σ τ τ' hβ hspos hτlower hτ'
    · exact hequation
    · exact heq'

private lemma compact_branch_bounds (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (hnoisy : directResolution β n < σ) (hcompact : ¬ IntermediateCondition β n σ) :
    ∃ τ : ℝ, σ ^ (-2 : ℝ) < τ ∧ CompactEquation β n σ τ ∧
      rateResolution β n σ = τ ^ (-2 : ℝ) ∧
      (∀ τ' : ℝ, σ ^ (-2 : ℝ) < τ' → CompactEquation β n σ τ' → τ' = τ) ∧
      (1 / (2 * (1 + 2 * (2 * β + 1)))) *
          ((1 + Real.log n) / Real.log (Real.exp 1 + σ ^ 2 * (1 + Real.log n))) ≤ τ ∧
      τ ≤ (Real.exp 1 + 6) *
          ((1 + Real.log n) / Real.log (Real.exp 1 + σ ^ 2 * (1 + Real.log n))) := by
  obtain ⟨τ, hτ, heq, hres, hu⟩ :=
    compact_branch_representation β n σ hβ hn hσ hnoisy hcompact
  have hspos := (directResolution_pos_le_one β n hβ hn).1.trans hnoisy
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hb := compactScalar_bounds β n σ τ hβ hn' hspos hσ.2 hτ heq
  exact ⟨τ, hτ, heq, hres, hu, hb⟩
/-- The scalar branch formulas and both interfaces have constants uniform in sample size and noise. Given [the displayed inputs and assumptions](hyp:β,hβ), [the stated mathematical conclusion holds](goal). -/
lemma frontier_branches (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ σ ∈ Icc (0 : ℝ) 1,
      FrontierBranches β n σ c C := by
  let A := (1 + 3 * (2 * β + 1) / 2) ^ (3 / 2 : ℝ)
  let ct := 1 / (2 * (1 + 2 * (2 * β + 1)))
  let Ct := Real.exp 1 + 6
  let cr := Ct ^ (-2 * β)
  let Cr := ct ^ (-2 * β)
  let c := min 1 (min ct cr)
  let C := max A (max Ct Cr)
  have hct : 0 < ct := by
    dsimp [ct]
    apply one_div_pos.mpr
    nlinarith [hβ.1]
  have hCt : 0 < Ct := by dsimp [Ct]; positivity
  have hcr : 0 < cr := Real.rpow_pos_of_pos hCt _
  have hCr : 0 < Cr := Real.rpow_pos_of_pos hct _
  have hA : 0 < A := by
    dsimp [A]
    apply Real.rpow_pos_of_pos
    nlinarith [hβ.1]
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨c, C, hc, hC, ?_⟩
  intro n hn σ hσ
  have hd := directResolution_pos_le_one β n hβ hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hB : 0 < 1 + Real.log n := by linarith [Real.log_pos hnR]
  have hD : 0 < Real.log (Real.exp 1 + σ ^ 2 * (1 + Real.log n)) := by
    apply Real.log_pos
    have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have : 0 ≤ σ ^ 2 * (1 + Real.log n) := mul_nonneg (sq_nonneg σ) hB.le
    linarith
  unfold FrontierBranches
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hs
    exact rateResolution_eq_direct_of_le β n σ hβ hn hσ hs
  · intro hnoisy
    have hspos : 0 < σ := hd.1.trans hnoisy
    have hi := noisy_rateResolution_interior β n σ hβ hn hσ hnoisy
    refine ⟨hi.1, hi.2, intermediateCondition_iff β n σ hβ hn hσ hnoisy, ?_, ?_⟩
    · intro hinter
      obtain ⟨z, hz1, hzup, hzeq, hres, hu⟩ :=
        intermediate_branch_representation β n σ hβ hn hσ hnoisy hinter
      have hb := intermediate_branch_bounds β n σ hβ hn hσ hnoisy hinter
      let S := 1 + Real.log ((n : ℝ) * σ ^ (2 * β + 1))
      have hk : 0 < 3 * (2 * β + 1) / 2 := by nlinarith [hβ.1]
      have hS : 0 < S := by
        unfold IntermediateEquation at hzeq
        dsimp [S]
        have := Real.log_pos hz1
        nlinarith
      have hproxy : 0 ≤ σ / S ^ (3 / 2 : ℝ) :=
        (div_pos hspos (Real.rpow_pos_of_pos hS _)).le
      have hc1 : c ≤ 1 := by dsimp [c]; exact min_le_left _ _
      have hAC : A ≤ C := by dsimp [C]; exact le_max_left _ _
      refine ⟨z, hz1, hzup, hzeq, hres, hu, ?_, ?_⟩
      · exact (mul_le_mul_of_nonneg_right hc1 hproxy).trans (by simpa [S] using hb.1)
      · exact hb.2.trans (mul_le_mul_of_nonneg_right hAC hproxy)
    · intro hcompact
      obtain ⟨τ, hτ, heq, hres, hu, hlo, hhi⟩ :=
        compact_branch_bounds β n σ hβ hn hσ hnoisy hcompact
      let B := 1 + Real.log n
      let D := Real.log (Real.exp 1 + σ ^ 2 * B)
      have hτpos : 0 < τ := (Real.rpow_pos_of_pos hspos _).trans hτ
      have hp := compactPower_bounds β B D τ ct Ct hβ.1
        (by simpa [B] using hB) (by simpa [D, B] using hD) hτpos hct hCt
        (by simpa [ct, B, D] using hlo) (by simpa [Ct, B, D] using hhi)
      have hrate : frontierRate β n σ = τ ^ (-2 * β) := by
        unfold frontierRate
        rw [hres]
        calc
          (τ ^ (-2 : ℝ)) ^ β = τ ^ ((-2 : ℝ) * β) :=
            (Real.rpow_mul hτpos.le (-2 : ℝ) β).symm
          _ = τ ^ (-2 * β) := by ring
      have hR : 0 ≤ B / D := (div_pos (by simpa [B] using hB) (by simpa [D, B] using hD)).le
      have hQ : 0 ≤ D / B := (div_pos (by simpa [D, B] using hD) (by simpa [B] using hB)).le
      have hpowQ : 0 ≤ (D / B) ^ (2 * β) := Real.rpow_nonneg hQ _
      have hcct : c ≤ ct := (min_le_right 1 (min ct cr)).trans (min_le_left ct cr)
      have hccr : c ≤ cr := (min_le_right 1 (min ct cr)).trans (min_le_right ct cr)
      have hCtC : Ct ≤ C := le_trans (le_max_left Ct Cr) (le_max_right A (max Ct Cr))
      have hCrC : Cr ≤ C := le_trans (le_max_right Ct Cr) (le_max_right A (max Ct Cr))
      refine ⟨τ, hτ, heq, hres, hu, ?_, ?_, ?_, ?_⟩
      · exact (mul_le_mul_of_nonneg_right hcct hR).trans (by simpa [ct, B, D] using hlo)
      · have hhi' : τ ≤ Ct * (B / D) := by simpa [Ct, B, D] using hhi
        exact hhi'.trans (mul_le_mul_of_nonneg_right hCtC hR)
      · rw [hrate]
        exact (mul_le_mul_of_nonneg_right hccr hpowQ).trans (by simpa [cr] using hp.1)
      · rw [hrate]
        have hp' : τ ^ (-2 * β) ≤ Cr * (D / B) ^ (2 * β) := by
          simpa [Cr] using hp.2
        exact hp'.trans (mul_le_mul_of_nonneg_right hCrC hpowQ)
  · intro hspos heq
    exact intermediate_compact_interface β n σ hβ hn hσ hspos heq
  · intro heq
    exact direct_interface β n σ hβ hn hσ heq

end CausalSmith.Stat.RdTruesideNoiseFrontier
