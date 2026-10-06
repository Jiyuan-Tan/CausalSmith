module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionRiskEnvelope
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Optimality

/-!
Nonnegativity of the population projection span under overlap.
-/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @node: cell_lower_le_upper_of_overlap
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a,μ,σ,hp,hmass), this result [establishes the stated mathematical conclusion](goal). -/
lemma cell_lower_le_upper_of_overlap {ε : ℝ}
    (hOverlap : Overlap ε) (a : ArmSpace)
    (μ : Measure OutcomeSpace) (σ : Measure (ScoreSpace ε))
    [IsFiniteMeasure μ] [IsFiniteMeasure σ]
    (hp : 0 < μ.real univ) (hmass : μ.real univ = σ.real univ) :
    (∫ u in (0 : ℝ)..1,
        Causalean.Stat.quantile
            (((μ univ)⁻¹ • μ).map (fun y : OutcomeSpace => (y : ℝ))) u *
          Causalean.Stat.quantile
            (((σ univ)⁻¹ • σ).map (fun e => (armProb a e)⁻¹)) (1 - u)) ≤
      ∫ u in (0 : ℝ)..1,
        Causalean.Stat.quantile
            (((μ univ)⁻¹ • μ).map (fun y : OutcomeSpace => (y : ℝ))) u *
          Causalean.Stat.quantile
            (((σ univ)⁻¹ • σ).map (fun e => (armProb a e)⁻¹)) u := by
  let Y : Measure ℝ :=
    ((μ univ)⁻¹ • μ).map (fun y : OutcomeSpace => (y : ℝ))
  let W : Measure ℝ :=
    ((σ univ)⁻¹ • σ).map (fun e => (armProb a e)⁻¹)
  have hσp : 0 < σ.real univ := by rw [← hmass]; exact hp
  letI : IsProbabilityMeasure Y := by
    dsimp [Y]
    rw [map_normalized_subtype_eq_finiteNormalize μ hp]
    infer_instance
  letI : IsProbabilityMeasure W := by
    dsimp [W]
    rw [map_normalized_inverseArmProb_eq_finiteNormalize_map a σ hσp]
    exact Measure.isProbabilityMeasure_map
      (measurable_projectionInverseArmProbReal a).aemeasurable
  have hYs : Y (Icc 0 1)ᶜ = 0 := by
    exact normalizedOutcome_support μ hp
  have hWs : W (Icc 0 ε⁻¹)ᶜ = 0 := by
    exact normalizedInverseArmProb_support hOverlap a σ hσp
  have hY2 : MemLp (fun x : ℝ => x) 2 Y := by
    apply memLp_of_bounded
    · filter_upwards [show ∀ᵐ x ∂Y, x ∈ Icc (0 : ℝ) 1 by
        rw [ae_iff]; exact hYs] with x hx
      exact hx
    · fun_prop
  have hW2 : MemLp (fun x : ℝ => x) 2 W := by
    apply memLp_of_bounded
    · filter_upwards [show ∀ᵐ x ∂W, x ∈ Icc (0 : ℝ) ε⁻¹ by
        rw [ae_iff]; exact hWs] with x hx
      exact hx
    · fun_prop
  have hopt := Causalean.Stat.countermonotone_le_product_expectation
    (Causalean.Stat.isCoupling_comonotoneCoupling Y W) hY2 hW2
  have hrest : volume.restrict (Ioc (0 : ℝ) 1) = Causalean.Stat.unifOI := by
    rw [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Ioc]
  have hcounter :
      (∫ p, p.1 * p.2 ∂(Causalean.Stat.countermonotoneCoupling Y W)) =
        ∫ u in (0 : ℝ)..1,
          Causalean.Stat.quantile Y u * Causalean.Stat.quantile W (1 - u) := by
    unfold Causalean.Stat.countermonotoneCoupling
    let r : ℝ → ℝ := fun u => 1 - u
    have hr : Measurable r := measurable_const.sub measurable_id
    have hWmap : AEMeasurable (Causalean.Stat.quantile W)
        (Causalean.Stat.unifOI.map r) := by
      simpa [r, Causalean.Stat.map_one_sub_unifOI] using
        (Causalean.Stat.aemeasurable_quantile_unifOI W)
    have hWr : AEMeasurable (fun u : ℝ =>
        Causalean.Stat.quantile W (1 - u)) Causalean.Stat.unifOI := by
      simpa [r, Function.comp_def] using hWmap.comp_measurable hr
    rw [MeasureTheory.integral_map]
    · rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hrest]
    · exact (Causalean.Stat.aemeasurable_quantile_unifOI Y).prodMk
        hWr
    · fun_prop
  have hcomono :
      (∫ p, p.1 * p.2 ∂(Causalean.Stat.comonotoneCoupling Y W)) =
        ∫ u in (0 : ℝ)..1,
          Causalean.Stat.quantile Y u * Causalean.Stat.quantile W u := by
    rw [Causalean.Stat.product_expectation_comonotoneCoupling Y W hY2 hW2,
      ← integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hrest]
  rw [hcounter, hcomono] at hopt
  simpa [Y, W] using hopt

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap,a), this result [establishes the stated mathematical conclusion](goal). -/
lemma muLower_le_muUpper_of_overlap {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) (a : ArmSpace) :
    muLower H g Prel hMass a ≤ muUpper H g Prel hMass a := by
  letI : IsProbabilityMeasure H := hMass.1
  letI : IsProbabilityMeasure Prel := hMass.2.1
  have hfin := projectionPopulationCells_finite H g Prel hOverlap hMass.2.2.1
  have hl := projectedArmEndpoint_population_eq H g Prel hMass hOverlap a false
  have hu := projectedArmEndpoint_population_eq H g Prel hMass hOverlap a true
  simp only [Bool.false_eq_true, if_false] at hl
  simp only [if_true] at hu
  rw [← hl, ← hu]
  unfold projectedArmEndpoint
  apply Finset.sum_le_sum
  intro r _
  letI : IsFiniteMeasure (trialPopulationCells Prel a r) := hfin.1 a r
  letI : IsFiniteMeasure (scorePopulationCells H g a r) := hfin.2 a r
  let q := (trialPopulationCells Prel a r).real univ
  by_cases hq : 0 < q
  · dsimp [q] at hq
    simp only [hq, if_pos]
    apply mul_le_mul_of_nonneg_left
    · apply cell_lower_le_upper_of_overlap hOverlap a
        (trialPopulationCells Prel a r) (scorePopulationCells H g a r) hq
      exact projectionCompatible_populationCells H g Prel hMass hOverlap a r
    · exact le_of_lt hq
  · dsimp [q] at hq
    simp [hq]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,hMass,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
theorem sharpATELength_nonneg_of_overlap {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (hMass : CompatibleCellMasses H g Prel)
    (hOverlap : Overlap ε) :
    0 ≤ sharpATELength H g Prel hMass := by
  have h₀ := muLower_le_muUpper_of_overlap H g Prel hMass hOverlap false
  have h₁ := muLower_le_muUpper_of_overlap H g Prel hMass hOverlap true
  unfold sharpATELength
  linarith

end
end CausalSmith.PartialID.UnlinkedPropensityAte
