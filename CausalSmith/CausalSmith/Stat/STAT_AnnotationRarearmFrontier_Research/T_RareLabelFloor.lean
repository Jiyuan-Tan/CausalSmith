module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.LabelFloorPair
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.LabelFloorTesting
public import Causalean.Stat.Minimax.LeCam

/-!
Rare-label lower bound uniform in auxiliary budget and exact-marginal side information.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


-- @node: thm:rare-label-floor
/--
[Uniform rare-label floors, explicit legal common-marginal pair, and its exact KL](goal).
-/
theorem rare_label_floor :
    (∃ c : Real, 0 < c ∧ -- @realizes c(positive numerical constant before all public indices)
      ∀ (n m d : Nat) (eps : Real), 1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
        c * labelBenchmark n eps ≤ minimaxRisk n m d eps ∧
        c * labelBenchmark n eps ≤ knownMarginalRisk n d eps) ∧
    (∀ (d : Nat) (eps delta : Real) (sign : Bool) (hd : 2 ≤ d),
      0 < eps → eps ≤ 1 / 4 → ∀ hdelta : LabelFloorAmplitude delta,
      -- @realizes \delta(separation in (0,1/8])
      ModelClass d eps (labelFloorLaw d eps delta sign hd hdelta) ∧
      ateFunctional (labelFloorLaw d eps delta sign hd hdelta) = (if sign then delta else -delta) ∧
      auxMarginal (labelFloorLaw d eps delta true hd hdelta) =
        auxMarginal (labelFloorLaw d eps delta
        false hd hdelta) ∧
      (∀ j : Fin d, j.val < 2 →
        cellMass (labelFloorLaw d eps delta sign hd hdelta) j = 1 / 2 ∧
        propensity (labelFloorLaw d eps delta sign hd hdelta) j = eps ∧
        outcomeMean (labelFloorLaw d eps delta sign hd hdelta) false j = 1 / 2 ∧
        outcomeMean (labelFloorLaw d eps delta sign hd hdelta) true j =
          1 / 2 + (if sign then delta else -delta)) ∧
      (∀ j : Fin d, 2 ≤ j.val → cellMass (labelFloorLaw d eps delta sign hd hdelta) j = 0)) ∧
    (∀ (d : Nat) (eps : Real) (hd : 2 ≤ d), 0 < eps → eps ≤ 1 / 4 →
      finiteKL (labelFloorLaw d eps (1 / 8) true hd labelFloorAmplitude_eighth)
        (labelFloorLaw d eps (1 / 8) false hd labelFloorAmplitude_eighth) =
        eps * Real.log (5 / 3) / 4) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨1 / 1024, by norm_num, ?_⟩
    intro n m d eps hn hd heps heps'
    let delta := 1 / (16 * Real.sqrt (max 1 ((n : Real) * eps)))
    let hdelta := labelFloorAmplitude_scaled ((n : Real) * eps)
    let P : ClassLaw d eps := ⟨labelFloorLaw d eps delta true hd hdelta,
      labelFloor_model d eps delta true hd hdelta heps heps'⟩
    let Q : ClassLaw d eps := ⟨labelFloorLaw d eps delta false hd hdelta,
      labelFloor_model d eps delta false hd hdelta heps heps'⟩
    have htargetP : ateFunctional P.1 = delta := by
      exact labelFloor_target d eps delta true hd hdelta heps heps'
    have htargetQ : ateFunctional Q.1 = -delta := by
      exact labelFloor_target d eps delta false hd hdelta heps heps'
    have haux : auxMarginal P.1 = auxMarginal Q.1 :=
      labelFloor_auxMarginal d eps delta hd hdelta heps heps'
    have htable : auxTable P.1 = auxTable Q.1 := congrArg (fun p => fun z => (p z).toReal) haux
    letI : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
    have hobs (R : DiscreteLaw d) : IsProbabilityMeasure (obsLaw R) := by
      unfold obsLaw
      infer_instance
    letI (R : DiscreteLaw d) : IsProbabilityMeasure (obsLaw R) := hobs R
    letI (R : DiscreteLaw d) : IsProbabilityMeasure (labeledProductLaw R n) := by
      unfold labeledProductLaw
      infer_instance
    letI (R : DiscreteLaw d) : IsProbabilityMeasure (auxProductLaw R m) := by
      unfold auxProductLaw
      infer_instance
    letI (R : DiscreteLaw d) : IsProbabilityMeasure (annotationLaw R n m) := by
      unfold annotationLaw
      infer_instance
    have htv : Causalean.Stat.tvDist (labeledProductLaw P.1 n) (labeledProductLaw Q.1 n) ≤ 1 / 4 :=
      labelFloor_scaled_tv n d eps hd heps heps'
    have hrate : delta ^ 2 / 4 = (1 / 1024 : Real) * labelBenchmark n eps :=
      labelFloor_scaled_rate n eps hn heps
    letI : Nonempty (Rule n m d) := ⟨⟨fun _ => 0, measurable_const, by intro z; norm_num⟩⟩
    letI : Nonempty (KnownRule n d) := ⟨⟨fun _ => 0, measurable_const, by intro z; norm_num⟩⟩
    constructor
    · have htvData : Causalean.Stat.tvDist
          ((annotationLaw P.1 n m).prod seedLaw) ((annotationLaw Q.1 n m).prod seedLaw) ≤ 1 / 4 := by
        rw [labelFloor_tv_common_product]
        unfold annotationLaw auxProductLaw
        rw [← haux, labelFloor_tv_common_product]
        exact htv
      have hbdd (T : Rule n m d) : BddAbove (Set.range (fun R : ClassLaw d eps => ruleRisk T.1 R.1)) := by
        refine ⟨4, ?_⟩
        rintro _ ⟨R, rfl⟩
        exact labelFloor_bounded_mse _ T.1 T.2.2 _ (ateFunctional_mem_Icc R.1)
      apply Causalean.Stat.le_minimaxValue_of_two_point
        (risk := fun (T : Rule n m d) (R : ClassLaw d eps) => ruleRisk T.1 R.1) P Q hbdd
      intro T
      have h := labelFloor_testing_mse
        ((annotationLaw P.1 n m).prod seedLaw) ((annotationLaw Q.1 n m).prod seedLaw)
        delta hdelta.1.le htvData T.1 T.2.1 T.2.2
      simpa only [ruleRisk, htargetP, htargetQ, hrate] using h
    · have htvSeed : Causalean.Stat.tvDist
          ((labeledProductLaw P.1 n).prod seedLaw) ((labeledProductLaw Q.1 n).prod seedLaw) ≤ 1 / 4 := by
        rw [labelFloor_tv_common_product]
        exact htv
      have hbdd (T : KnownRule n d) : BddAbove (Set.range (fun R : ClassLaw d eps => knownRuleRisk T.1 R.1)) := by
        refine ⟨4, ?_⟩
        rintro _ ⟨R, rfl⟩
        exact labelFloor_bounded_mse _ (fun z : (Fin n → Obs d) × Real => T.1 (z.1, auxTable R.1, z.2))
          (fun z => T.2.2 _) _ (ateFunctional_mem_Icc R.1)
      apply Causalean.Stat.le_minimaxValue_of_two_point
        (risk := fun (T : KnownRule n d) (R : ClassLaw d eps) => knownRuleRisk T.1 R.1) P Q hbdd
      intro T
      have hmeas : Measurable (fun z : (Fin n → Obs d) × Real => T.1 (z.1, auxTable P.1, z.2)) := by
        exact T.2.1.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
      have h := labelFloor_testing_mse
        ((labeledProductLaw P.1 n).prod seedLaw) ((labeledProductLaw Q.1 n).prod seedLaw)
        delta hdelta.1.le htvSeed (fun z => T.1 (z.1, auxTable P.1, z.2)) hmeas (fun z => T.2.2 _)
      simpa only [knownRuleRisk, htargetP, htargetQ, hrate, ← htable] using h
  · intro d eps delta sign hd heps heps' hdelta
    refine ⟨labelFloor_model d eps delta sign hd hdelta heps heps',
      labelFloor_target d eps delta sign hd hdelta heps heps',
      labelFloor_auxMarginal d eps delta hd hdelta heps heps', ?_, ?_⟩
    · intro j hj
      refine ⟨?_, labelFloor_propensity d eps delta sign hd hdelta heps heps' j hj, ?_, ?_⟩
      · rw [labelFloor_cellMass d eps delta sign hd hdelta heps heps', if_pos hj]
      · exact labelFloor_outcomeMean d eps delta sign hd hdelta heps heps' j hj false
      · exact labelFloor_outcomeMean d eps delta sign hd hdelta heps heps' j hj true
    · intro j hj
      rw [labelFloor_cellMass d eps delta sign hd hdelta heps heps', if_neg (by omega)]
  · exact labelFloor_KL_eighth

end CausalSmith.Stat.AnnotationRarearmFrontier
