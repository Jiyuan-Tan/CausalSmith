import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.WitnessCertificates
import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.THMSClassInclusion
import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.TWitnessSDPOptimum
import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.TComplementDegreeCollapse
import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.TDualCompleteClass

/-! Exact quartic-versus-quadratic separation in the finite witness. -/

open scoped BigOperators
open Finset Set

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- For [a witness schedule and coordinate](hyp:θ,i), [the centered rational coordinate](goal) is twice the binary value minus one. -/
-- @node: witnessCenteredRat
def witnessCenteredRat (θ : Fin 6 → Fin 2) (i : Fin 6) : ℚ := 2 * (θ i : ℕ) - 1

/-- For [a witness schedule](hyp:θ), [the rational witness polynomial](goal) is the displayed certificate polynomial. -/
-- @node: witnessPRat
def witnessPRat (θ : Fin 6 → Fin 2) : ℚ :=
  3*witnessCenteredRat θ 0*witnessCenteredRat θ 1 -
  35*witnessCenteredRat θ 0*witnessCenteredRat θ 2 +
  3*witnessCenteredRat θ 0*witnessCenteredRat θ 5 -
  3*witnessCenteredRat θ 1*witnessCenteredRat θ 2 +
  24*witnessCenteredRat θ 1*witnessCenteredRat θ 3 -
  45*witnessCenteredRat θ 1*witnessCenteredRat θ 5 -
  3*witnessCenteredRat θ 2*witnessCenteredRat θ 5 -
  12*witnessCenteredRat θ 3*witnessCenteredRat θ 4 -
  36*witnessCenteredRat θ 3*witnessCenteredRat θ 5

/-- For [a witness schedule](hyp:θ), [the rational b-star rule](goal) is the displayed certificate rule. -/
-- @node: witnessBStarRat
def witnessBStarRat (θ : Fin 6 → Fin 2) : ℚ :=
  (107 + witnessPRat θ - 3*witnessCenteredRat θ 0*witnessCenteredRat θ 1*
    witnessCenteredRat θ 2*witnessCenteredRat θ 5) / 72

/-- For [a witness schedule](hyp:θ), [the rational r-star rule](goal) is the displayed certificate rule. -/
-- @node: witnessRStarRat
def witnessRStarRat (θ : Fin 6 → Fin 2) : ℚ := (110 + witnessPRat θ) / 72

/-- For [a witness schedule](hyp:θ), [the rational true variance](goal) is the displayed certificate variance. -/
-- @node: witnessTrueVarianceRat
def witnessTrueVarianceRat (θ : Fin 6 → Fin 2) : ℚ :=
  (8*(θ 0 : ℕ)*(θ 0 : ℕ) + 6*(θ 1 : ℕ)*(θ 1 : ℕ) +
   8*(θ 2 : ℕ)*(θ 2 : ℕ) + 6*(θ 3 : ℕ)*(θ 3 : ℕ) +
   2*(θ 4 : ℕ)*(θ 4 : ℕ) + 14*(θ 5 : ℕ)*(θ 5 : ℕ) -
   16*(θ 0 : ℕ)*(θ 2 : ℕ) - 4*(θ 0 : ℕ)*(θ 4 : ℕ) +
   4*(θ 0 : ℕ)*(θ 5 : ℕ) + 12*(θ 1 : ℕ)*(θ 3 : ℕ) -
   6*(θ 1 : ℕ)*(θ 4 : ℕ) - 18*(θ 1 : ℕ)*(θ 5 : ℕ) +
   4*(θ 2 : ℕ)*(θ 4 : ℕ) - 4*(θ 2 : ℕ)*(θ 5 : ℕ) -
   6*(θ 3 : ℕ)*(θ 4 : ℕ) - 18*(θ 3 : ℕ)*(θ 5 : ℕ) +
   8*(θ 4 : ℕ)*(θ 5 : ℕ)) / 9

/-- [The witness quartet](goal) is the designated four-coordinate support used for separation. -/
-- @node: witnessQuartet
noncomputable def witnessQuartet : Finset (Fin witnessExperiment.K) :=
  {wcoord 0, wcoord 1, wcoord 2, wcoord 5}

/-- [The b-star witness objective has its stated exact value](goal). -/
-- @node: bStar_objective_exact
lemma bStar_objective_exact :
    boundObjective witnessExperiment witnessObjective bStar = 107 / 72 := by
  have hq : (∑ θ, (1/64 : ℚ) * witnessBStarRat θ) = 107/72 := by native_decide
  unfold boundObjective
  simp only [witnessObjective, witnessQ, Subtype.coe_mk]
  simp_rw [show ∀ θ, bStar θ = (witnessBStarRat θ : ℝ) from fun θ => by
    simp [bStar, witnessBStarRat, witnessPRat, witnessCenteredRat, witnessP,
      witnessX, centeredCoord, wcoord, witnessK_eq]]
  convert congrArg (fun x : ℚ => (x : ℝ)) hq using 1 <;>
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  all_goals rfl

/-- [The r-star witness objective has its stated exact value](goal). -/
-- @node: rStar_objective_exact
lemma rStar_objective_exact :
    boundObjective witnessExperiment witnessObjective rStar = 55 / 36 := by
  have hq : (∑ θ, (1/64 : ℚ) * witnessRStarRat θ) = 55/36 := by native_decide
  unfold boundObjective
  simp only [witnessObjective, witnessQ, Subtype.coe_mk]
  simp_rw [show ∀ θ, rStar θ = (witnessRStarRat θ : ℝ) from fun θ => by
    simp [rStar, witnessRStarRat, witnessPRat, witnessCenteredRat, witnessP,
      witnessX, centeredCoord, wcoord, witnessK_eq]]
  convert congrArg (fun x : ℚ => (x : ℝ)) hq using 1 <;>
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  all_goals rfl

/-- [The μ-star witness dual objective has its stated exact value](goal). -/
-- @node: muStar_objective_exact
lemma muStar_objective_exact : dualObjective witnessExperiment muStar = 107 / 72 := by
  have hq : (∑ θ, muStarRat θ * witnessTrueVarianceRat θ) = 107/72 := by native_decide
  unfold dualObjective
  simp_rw [muStar_eq_ratCast]
  simp_rw [show ∀ θ, trueVarianceFn witnessExperiment θ =
      (witnessTrueVarianceRat θ : ℝ) from fun θ => by
    rw [witness_trueVariance_explicit]
    simp [witnessTrueVarianceRat, wcoord, witnessK_eq]]
  convert congrArg (fun x : ℚ => (x : ℝ)) hq using 1 <;>
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  all_goals rfl

/-- [The ν-star witness dual objective has its stated exact value](goal). -/
-- @node: nuStar_objective_exact
lemma nuStar_objective_exact :
    (∑ θ, nuStar θ * trueVarianceFn witnessExperiment θ) = 55 / 36 := by
  have hq : (∑ θ, nuStarRat θ * witnessTrueVarianceRat θ) = 55/36 := by native_decide
  simp_rw [nuStar_eq_ratCast]
  simp_rw [show ∀ θ, trueVarianceFn witnessExperiment θ =
      (witnessTrueVarianceRat θ : ℝ) from fun θ => by
    rw [witness_trueVariance_explicit]
    simp [witnessTrueVarianceRat, wcoord, witnessK_eq]]
  convert congrArg (fun x : ℚ => (x : ℝ)) hq using 1 <;>
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  all_goals rfl

/-- [The b-star Möbius coefficient on the witness quartet has the stated value](goal). -/
-- @node: bStar_quartet_coefficient
lemma bStar_quartet_coefficient : beta witnessExperiment bStar witnessQuartet = -2/3 := by
  classical
  have hw (i : Fin 6) : wcoord i = i := by apply Fin.ext; rfl
  unfold beta witnessQuartet
  simp_rw [hw]
  change (∑ T ∈ ({0, 1, 2, 5} : Finset (Fin 6)).powerset,
      (-1 : ℝ) ^ (({0, 1, 2, 5} : Finset (Fin 6)).card - T.card) *
        bStar (vertex witnessExperiment T)) = -2/3
  have hq : (∑ T ∈ ({0, 1, 2, 5} : Finset (Fin 6)).powerset,
      (-1 : ℚ) ^ (({0, 1, 2, 5} : Finset (Fin 6)).card - T.card) *
        witnessBStarRat (fun i => if i ∈ T then 1 else 0)) = -2/3 := by native_decide
  have hver (T : Finset (Fin 6)) : vertex witnessExperiment T =
      (fun i => if i ∈ T then 1 else 0) := by
    change (fun i : Fin 6 => if i ∈ T then 1 else 0) =
      (fun i : Fin 6 => if i ∈ T then 1 else 0)
    rfl
  have hbcast : ∀ θ, bStar θ = (witnessBStarRat θ : ℝ) := fun θ => by
    simp [bStar, witnessBStarRat, witnessPRat, witnessCenteredRat, witnessP,
      witnessX, centeredCoord, hw]
  simp_rw [hbcast]
  have hbr (T : Finset (Fin 6)) := congrArg witnessBStarRat (hver T)
  simp_rw [hbr]
  convert congrArg (fun x : ℚ => (x : ℝ)) hq using 1 <;>
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

/-- [The witness certificates establish the stated quartic separation between the unrestricted and degree-restricted programs](goal). -/
-- @node: thm:quartic-separation
theorem witness_quartic_separation :
    optValue witnessExperiment witnessObjective ⊤ = 107 / 72 ∧
    optValue witnessExperiment witnessObjective 2 = 55 / 36 ∧
    optValue witnessExperiment witnessObjective 3 = 55 / 36 ∧
    optValue witnessExperiment witnessObjective 2 -
      optValue witnessExperiment witnessObjective ⊤ = 1 / 24 ∧
    bStar ∈ unrestrictedConservativeCone witnessExperiment ∧
    bStar ∉ observableSpan witnessExperiment 3 ∧
    rStar ∈ conservativeCone witnessExperiment 2 ∧
    (∀ θ, rStar θ - bStar θ =
      (1 + witnessX θ 0 * witnessX θ 1 * witnessX θ 2 * witnessX θ 5) / 24 ∧
      (rStar θ - bStar θ = 0 ∨ rStar θ - bStar θ = 1 / 12)) ∧
    expectedRule witnessExperiment hStar = bStar ∧
    (∀ z y, 0 ≤ hStar z y ∧ hStar z y ≤ 5) ∧
    muStar ∈ dualMarginSet witnessExperiment witnessObjective ∧
    dualObjective witnessExperiment muStar = 107 / 72 ∧
    (∀ S ∈ observableComplex witnessExperiment, S.card ≤ 3 →
      ∑ θ, nuStar θ * monomial witnessExperiment S θ =
        ∑ θ, witnessQ θ * monomial witnessExperiment S θ) ∧
    (∑ θ, nuStar θ * trueVarianceFn witnessExperiment θ) = 55 / 36 ∧
    (∀ H : Matrix (Fin 6) (Fin 6) ℝ, witnessHMSFeasible H →
      55 / 36 ≤ witnessHMSObjective H) := by
  classical
  have hnuNonneg : ∀ θ, 0 ≤ nuStar θ := by
    intro θ
    unfold nuStar
    split <;> norm_num
  have hmargin3 : ∀ u ∈ observableSpan witnessExperiment 3,
      (∑ θ, nuStar θ * u θ) = ∑ θ, witnessQ θ * u θ := by
    intro u hu
    unfold observableSpan at hu
    refine Submodule.span_induction
      (p := fun u _ => (∑ θ, nuStar θ * u θ) = ∑ θ, witnessQ θ * u θ)
      ?_ ?_ ?_ ?_ hu
    · intro u hu
      rcases hu with ⟨S, hS, hdeg, rfl⟩
      exact nuStar_degree_three_margins S hS (by exact_mod_cast hdeg)
    · simp
    · intro u v _ _ hu hv
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hu, hv]
    · intro c u _ hu
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        (∑ θ, nuStar θ * (c * u θ)) = c * ∑ θ, nuStar θ * u θ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro θ _
          ring
        _ = c * ∑ θ, witnessQ θ * u θ := by rw [hu]
        _ = ∑ θ, witnessQ θ * (c * u θ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro θ _
          ring
  have hweak3 : ∀ {b}, b ∈ conservativeCone witnessExperiment 3 →
      (∑ θ, nuStar θ * trueVarianceFn witnessExperiment θ) ≤
        boundObjective witnessExperiment witnessObjective b := by
    intro b hb
    calc
      (∑ θ, nuStar θ * trueVarianceFn witnessExperiment θ) ≤
          ∑ θ, nuStar θ * b θ := by
        apply Finset.sum_le_sum
        intro θ _
        exact mul_le_mul_of_nonneg_left (hb.2 θ) (hnuNonneg θ)
      _ = ∑ θ, witnessQ θ * b θ := hmargin3 b hb.1
      _ = boundObjective witnessExperiment witnessObjective b := by rfl
  have hr3 : rStar ∈ conservativeCone witnessExperiment 3 :=
    ⟨observableSpan_mono_degree witnessExperiment (by norm_num) rStar_feasible.1,
      rStar_feasible.2⟩
  have hopt3 : optValue witnessExperiment witnessObjective 3 = 55 / 36 := by
    apply le_antisymm
    · unfold optValue
      apply csInf_le
      · refine ⟨55 / 36, ?_⟩
        rintro _ ⟨b, hb, rfl⟩
        rw [← nuStar_objective_exact]
        exact hweak3 hb
      · exact ⟨rStar, hr3, rStar_objective_exact⟩
    · obtain ⟨b, hb, hobj⟩ := observable_primal_attained witnessExperiment witnessObjective 3
      rw [← nuStar_objective_exact, ← hobj]
      exact hweak3 hb
  have hopt2 : optValue witnessExperiment witnessObjective 2 = 55 / 36 := by
    apply le_antisymm
    · unfold optValue
      apply csInf_le
      · refine ⟨55 / 36, ?_⟩
        rintro _ ⟨b, hb, rfl⟩
        rw [← nuStar_objective_exact]
        exact hweak3 ⟨observableSpan_mono_degree witnessExperiment (by norm_num) hb.1, hb.2⟩
      · exact ⟨rStar, rStar_feasible, rStar_objective_exact⟩
    · obtain ⟨b, hb, hobj⟩ := observable_primal_attained witnessExperiment witnessObjective 2
      rw [← nuStar_objective_exact, ← hobj]
      exact hweak3 ⟨observableSpan_mono_degree witnessExperiment (by norm_num) hb.1, hb.2⟩
  have hoptTop : optValue witnessExperiment witnessObjective ⊤ = 107 / 72 := by
    apply le_antisymm
    · unfold optValue
      apply csInf_le
      · refine ⟨107 / 72, ?_⟩
        rintro _ ⟨b, hb, rfl⟩
        rw [← muStar_objective_exact]
        exact observable_weak_duality witnessExperiment witnessObjective ⊤ hb muStar_dual_uniform
      · exact ⟨bStar, bStar_feasible, bStar_objective_exact⟩
    · obtain ⟨b, hb, hobj⟩ := observable_primal_attained witnessExperiment witnessObjective ⊤
      rw [← muStar_objective_exact, ← hobj]
      exact observable_weak_duality witnessExperiment witnessObjective ⊤ hb muStar_dual_uniform
  have hbNot : bStar ∉ observableSpan witnessExperiment 3 := by
    intro hb
    have hz := (observableSpan_iff_beta_vanishes_degree witnessExperiment bStar 3).mp hb
      witnessQuartet (Or.inr (by
        unfold witnessQuartet
        have hw (i : Fin 6) : wcoord i = i := by apply Fin.ext; rfl
        simp_rw [hw]
        decide))
    rw [bStar_quartet_coefficient] at hz
    norm_num at hz
  have hgapPointwise : ∀ θ, rStar θ - bStar θ =
      (1 + witnessX θ 0 * witnessX θ 1 * witnessX θ 2 * witnessX θ 5) / 24 ∧
      (rStar θ - bStar θ = 0 ∨ rStar θ - bStar θ = 1 / 12) := by
    intro θ
    have heq : rStar θ - bStar θ =
        (1 + witnessX θ 0 * witnessX θ 1 * witnessX θ 2 * witnessX θ 5) / 24 := by
      simp only [rStar, bStar]
      ring
    refine ⟨heq, ?_⟩
    rw [heq]
    have h0 : θ (wcoord 0) = 0 ∨ θ (wcoord 0) = 1 := by omega
    rcases h0 with h0 | h0 <;>
      have h1 : θ (wcoord 1) = 0 ∨ θ (wcoord 1) = 1 := by omega
    all_goals rcases h1 with h1 | h1
    all_goals have h2 : θ (wcoord 2) = 0 ∨ θ (wcoord 2) = 1 := by omega
    all_goals rcases h2 with h2 | h2
    all_goals have h5 : θ (wcoord 5) = 0 ∨ θ (wcoord 5) = 1 := by omega
    all_goals rcases h5 with h5 | h5
    all_goals simp [witnessX, centeredCoord, h0, h1, h2, h5]
    all_goals norm_num
  have hHMS : ∀ H : Matrix (Fin 6) (Fin 6) ℝ, witnessHMSFeasible H →
      55 / 36 ≤ witnessHMSObjective H := by
    intro H hH
    have hpsd := hH.2.1
    have hobjNonneg : ∀ (D : Matrix (Fin 6) (Fin 6) ℝ), D.PosSemidef →
        0 ≤ witnessHMSObjective D := by
      intro D hD
      unfold witnessHMSObjective
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro θ _
      have hquad := hD.dotProduct_mulVec_nonneg
        (fun i : Fin 6 => ((θ (wcoord i) : ℕ) : ℝ))
      simp only [dotProduct, Matrix.mulVec, starRingEnd_apply, star_id_of_comm] at hquad
      rw [show (∑ i : Fin 6, ∑ k : Fin 6,
          D i k * ((θ (wcoord i) : ℕ) : ℝ) * ((θ (wcoord k) : ℕ) : ℝ)) =
          ∑ i : Fin 6, ((θ (wcoord i) : ℕ) : ℝ) *
            ∑ k : Fin 6, D i k * ((θ (wcoord k) : ℕ) : ℝ) by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring]
      exact hquad
    have hobjDiff : 0 ≤ witnessHMSObjective (H - witnessAMatrix) := by
      exact hobjNonneg _ hpsd
    have hlin : witnessHMSObjective (H - witnessAMatrix) =
        witnessHMSObjective H - witnessHMSObjective witnessAMatrix := by
      unfold witnessHMSObjective
      simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
      ring
    have hbdd : BddBelow (witnessHMSObjective '' {H | witnessHMSFeasible H}) := by
      refine ⟨witnessHMSObjective witnessAMatrix, ?_⟩
      rintro _ ⟨G, hG, rfl⟩
      have hp := hG.2.1
      have hn : 0 ≤ witnessHMSObjective (G - witnessAMatrix) := by
        exact hobjNonneg _ hp
      rw [show witnessHMSObjective (G - witnessAMatrix) =
          witnessHMSObjective G - witnessHMSObjective witnessAMatrix by
        unfold witnessHMSObjective
        simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
        ring] at hn
      linarith
    have hsinf : sInf (witnessHMSObjective '' {H | witnessHMSFeasible H}) ≤
        witnessHMSObjective H := csInf_le hbdd ⟨H, hH, rfl⟩
    rw [(witness_hms_sdp_optimum).1] at hsinf
    have hsqrt : 4 ≤ Real.sqrt 17 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17), Real.sqrt_nonneg 17]
    linarith
  refine ⟨hoptTop, hopt2, hopt3, ?_, bStar_feasible, hbNot, rStar_feasible,
    hgapPointwise, bStar_implemented, hStar_nonnegative_bounded, muStar_dual_uniform,
    muStar_objective_exact, nuStar_degree_three_margins, nuStar_objective_exact, hHMS⟩
  rw [hopt2, hoptTop]
  norm_num

end CausalSmith.Experimentation.BinaryTruthbound
