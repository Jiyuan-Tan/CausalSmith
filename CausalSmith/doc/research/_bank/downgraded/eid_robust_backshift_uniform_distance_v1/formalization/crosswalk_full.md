# tex↔Lean crosswalk

Definition/assumption/theorem (and, in the F5 complete table, lemma)
correspondence. Durable anchors: `obj_id` (.md/.tex side) and `(file, decl)`
(Lean side). Line numbers are convenience and re-derivable.

**Guarantee boundary (read this).** The Lean column is machine-verified at the
STATEMENT level: a sorry-free theorem/lemma certifies its *statement* is true.
The `.tex` PROOFS are NOT Lean-verified at the proof level — they are human
narratives refereed once at D0.5 and reconciled to the Lean *statements* by
the proof-review loop. A `.tex` proof step can therefore be wrong while the (true) statement
is Lean-certified; where the two disagree, the Lean proof is the ground truth.

| obj_id | kind | Lean (file:decl) | .tex anchor | verdict | note |
|---|---|---|---|---|---|
| P-1 | definition | `Basic.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.admissibleSet (L64)` | P-1 | equivalent |  |
| P-2 | definition | `Basic/Occupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.maxLineOccupancy (L49)` | P-2 | equivalent |  |
| P-3 | definition | `Basic/Occupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.envDeletionDistance (L63)` | P-3 | equivalent |  |
| P-4 | definition | `Basic.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.compatibleSet (L88)` | P-4 | equivalent |  |
| P-5 | definition | `Basic/Occupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.genericOccupancy (L117)` | P-5 | equivalent |  |
| P-6 | definition | `Basic/Occupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.affineSeparation (L143)` | P-6 | equivalent |  |
| P-7 | definition | `Helpers/ConfidenceUnion.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.subsetConsensus (L68)` | P-7 | equivalent |  |
| P-8 | definition | `Helpers/ConfidenceUnion.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.honestRegionRadius (L102)` | P-8 | equivalent |  |
| P-9 | definition | `(none)` | P-9 | unmatched |  |
| P-10 | definition | `Helpers/MatrixMargins.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.opOuterRadius (L63)` | P-10 | equivalent |  |
| P-11 | definition | `Helpers/ConfidenceUnion.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.confidenceUnion (L112)` | P-11 | equivalent |  |
| P-12 | definition | `OpenQuestions.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.openQuestion_certifiedUniformInference (L12)` | P-12 | equivalent |  |
| T-1 | theorem | `TSharpReplacementRadius.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.sharp_replacement_radius (L20)` | T-1 | equivalent |  |
| T-2 | theorem | `TGenericSupportFrontier.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.generic_support_frontier (L22)` | T-2 | equivalent |  |
| T-3 | theorem | `TUniformSupportDeletionRadius.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.uniform_support_deletion_radius (L36)` | T-3 | equivalent |  |
| T-4 | theorem | `TConfidenceUnionCoverage.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.confidence_union_coverage (L23)` | T-4 | equivalent |  |
| T-5 | theorem | `TNonEffectiveFourMarginContraction.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.non_effective_four_margin_contraction (L22)` | T-5 | equivalent |  |
| L-1 | lemma | `Helpers/OverlapUniqueness.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.overlap_uniqueness (L598)` | L-1 | equivalent |  |
| L-2 | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.generic_affine_occupancy (L726)` | L-2 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.BackshiftNormalization (L69)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.NonnegativeShifts (L73)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.HonestCovarianceModel (L78)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic/Occupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.SupportFactorization (L86)` | A-4 | equivalent |  |
| A-5 | assumption | `Basic/Occupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.GenericActiveAmplitudes (L97)` | A-5 | equivalent |  |
| lem:euclidean-heine-borel | lemma | `Helpers/EuclideanHeineBorel.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.euclideanHeineBorel_mathlib (L15)` | lem:euclidean-heine-borel | equivalent |  |
| lem:compact-extreme-value | lemma | `Helpers/CompactExtremeValue.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.compactExtremeValueMinimum_mathlib (L16)` | lem:compact-extreme-value | equivalent |  |
| aux_BackshiftSystem | definition | `Basic.lean:BackshiftSystem (L42)` | aux_BackshiftSystem | unmatched |  |
| aux_CandidateConditionBound | definition | `Helpers/ContractionCompactness.lean:CandidateConditionBound (L18)` | aux_CandidateConditionBound | unmatched |  |
| aux_CollinearPairs | definition | `Basic/Occupancy.lean:CollinearPairs (L36)` | aux_CollinearPairs | unmatched |  |
| aux_contractionC0 | definition | `Helpers/ContractionLocalInverse.lean:contractionC0 (L23)` | aux_contractionC0 | unmatched |  |
| aux_coverageEvent | definition | `TConfidenceUnionCoverage.lean:coverageEvent (L16)` | aux_coverageEvent | unmatched |  |
| aux_Environment | definition | `Basic.lean:Environment (L25)` | aux_Environment | unmatched |  |
| aux_honestCount | definition | `Basic.lean:honestCount (L39)` | aux_honestCount | unmatched |  |
| aux_InferenceWorld | definition | `Helpers/ConfidenceUnion.lean:InferenceWorld (L36)` | aux_InferenceWorld | unmatched |  |
| aux_matrixConditionNumber | definition | `Helpers/MatrixMargins.lean:matrixConditionNumber (L23)` | aux_matrixConditionNumber | unmatched |  |
| aux_matrixScaleBound | definition | `Helpers/MatrixMargins.lean:matrixScaleBound (L42)` | aux_matrixScaleBound | unmatched |  |
| aux_normalizationSlack | definition | `Helpers/MatrixMargins.lean:normalizationSlack (L30)` | aux_normalizationSlack | unmatched |  |
| aux_RealMatrix | definition | `Basic.lean:RealMatrix (L19)` | aux_RealMatrix | unmatched |  |
| aux_PSDCovarianceFamily | definition | `Basic.lean:PSDCovarianceFamily (L31)` | aux_PSDCovarianceFamily | unmatched |  |
| volume_mk_zeroLocus_mvPolynomial | lemma | `Helpers/PolynomialNull.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.volume_mk_zeroLocus_mvPolynomial (L21)` | volume_mk_zeroLocus_mvPolynomial | unmatched |  |
| overlap_card_lower_bound | lemma | `Helpers/OverlapUniqueness.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.overlap_card_lower_bound (L18)` | overlap_card_lower_bound | unmatched |  |
| noncollinear_card_at_least_three | lemma | `Helpers/OverlapUniqueness.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.noncollinear_card_at_least_three (L191)` | noncollinear_card_at_least_three | unmatched |  |
| exists_nonzero_affineMinor_of_noncollinear | lemma | `Helpers/OverlapUniqueness.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.exists_nonzero_affineMinor_of_noncollinear (L217)` | exists_nonzero_affineMinor_of_noncollinear | unmatched |  |
| BackshiftExplanation.transformed_covariance_eq | lemma | `(none)` | BackshiftExplanation.transformed_covariance_eq | unmatched |  |
| centeredShiftCombination | definition | `Helpers/OverlapUniqueness.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.centeredShiftCombination (L74)` | centeredShiftCombination | unmatched |  |
| centeredShiftCombination_single | lemma | `Helpers/OverlapUniqueness.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.centeredShiftCombination_single (L81)` | centeredShiftCombination_single | unmatched |  |
| exists_centeredShiftCombination_ne_zero | lemma | `Helpers/OverlapUniqueness.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.exists_centeredShiftCombination_ne_zero (L96)` | exists_centeredShiftCombination_ne_zero | unmatched |  |
| exists_centeredShiftCombination_distinctRatios | lemma | `Helpers/OverlapUniqueness.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.exists_centeredShiftCombination_distinctRatios (L127)` | exists_centeredShiftCombination_distinctRatios | unmatched |  |
| genericActiveAmplitudes_ae_positive | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.genericActiveAmplitudes_ae_positive (L17)` | genericActiveAmplitudes_ae_positive | unmatched |  |
| genericActiveAmplitudes_ae_avoid_volume_null | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.genericActiveAmplitudes_ae_avoid_volume_null (L45)` | genericActiveAmplitudes_ae_avoid_volume_null | unmatched |  |
| genericActiveAmplitudes_ae_polynomial_ne_zero | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.genericActiveAmplitudes_ae_polynomial_ne_zero (L68)` | genericActiveAmplitudes_ae_polynomial_ne_zero | unmatched |  |
| volume_zeroLocus_mvPolynomial_finite | lemma | `Helpers/PolynomialNull.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.volume_zeroLocus_mvPolynomial_finite (L105)` | volume_zeroLocus_mvPolynomial_finite | unmatched |  |
| genericActiveAmplitudes_ae_finite_polynomials_ne_zero | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.genericActiveAmplitudes_ae_finite_polynomials_ne_zero (L87)` | genericActiveAmplitudes_ae_finite_polynomials_ne_zero | unmatched |  |
| genericActiveAmplitudes_ae_activeProjection_injective | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.genericActiveAmplitudes_ae_activeProjection_injective (L104)` | genericActiveAmplitudes_ae_activeProjection_injective | unmatched |  |
| maxLineOccupancy_ge_of_collinear | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.maxLineOccupancy_ge_of_collinear (L254)` | maxLineOccupancy_ge_of_collinear | unmatched |  |
| maxLineOccupancy_support_lower_bound | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.maxLineOccupancy_support_lower_bound (L264)` | maxLineOccupancy_support_lower_bound | unmatched |  |
| maxLineOccupancy_ge_min_two | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.maxLineOccupancy_ge_min_two (L330)` | maxLineOccupancy_ge_min_two | unmatched |  |
| maxLineOccupancy_three_forced_terms | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.maxLineOccupancy_three_forced_terms (L361)` | maxLineOccupancy_three_forced_terms | unmatched |  |
| horizontalSupport_card | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.horizontalSupport_card (L421)` | horizontalSupport_card | unmatched |  |
| verticalSupport_card | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.verticalSupport_card (L437)` | verticalSupport_card | unmatched |  |
| zeroSupport_card | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.zeroSupport_card (L453)` | zeroSupport_card | unmatched |  |
| maxLineOccupancy_le_of_forced_classification | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.maxLineOccupancy_le_of_forced_classification (L462)` | maxLineOccupancy_le_of_forced_classification | unmatched |  |
| activeCoordinatePolynomial | definition | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.activeCoordinatePolynomial (L136)` | activeCoordinatePolynomial | unmatched |  |
| eval_activeCoordinatePolynomial | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.eval_activeCoordinatePolynomial (L143)` | eval_activeCoordinatePolynomial | unmatched |  |
| affineMinorPolynomial | definition | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.affineMinorPolynomial (L155)` | affineMinorPolynomial | unmatched |  |
| eval_affineMinorPolynomial | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.eval_affineMinorPolynomial (L165)` | eval_affineMinorPolynomial | unmatched |  |
| affineMinorPolynomial_ne_zero_of_mixed_support | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.affineMinorPolynomial_ne_zero_of_mixed_support (L176)` | affineMinorPolynomial_ne_zero_of_mixed_support | unmatched |  |
| originMinorPolynomial | definition | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.originMinorPolynomial (L209)` | originMinorPolynomial | unmatched |  |
| eval_originMinorPolynomial | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.eval_originMinorPolynomial (L217)` | eval_originMinorPolynomial | unmatched |  |
| originMinorPolynomial_ne_zero_of_mixed_support | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.originMinorPolynomial_ne_zero_of_mixed_support (L228)` | originMinorPolynomial_ne_zero_of_mixed_support | unmatched |  |
| maxLineOccupancy_origin_interior_lower_bound | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.maxLineOccupancy_origin_interior_lower_bound (L375)` | maxLineOccupancy_origin_interior_lower_bound | unmatched |  |
| genericActiveAmplitudes_ae_forced_classification | lemma | `Helpers/GenericAffineOccupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.genericActiveAmplitudes_ae_forced_classification (L502)` | genericActiveAmplitudes_ae_forced_classification | unmatched |  |
| maxLineOccupancy_congr_on | lemma | `Basic/Occupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.maxLineOccupancy_congr_on (L152)` | maxLineOccupancy_congr_on | unmatched |  |
| envDeletionDistance_gt_iff | lemma | `Basic/Occupancy.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.envDeletionDistance_gt_iff (L174)` | envDeletionDistance_gt_iff | unmatched |  |
| maxLineOccupancy_mono_index | lemma | `TUniformSupportDeletionRadius.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.maxLineOccupancy_mono_index (L20)` | maxLineOccupancy_mono_index | unmatched |  |
| maxAffineMinor_pos_iff_not_collinear | lemma | `Helpers/SharpThreshold.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.maxAffineMinor_pos_iff_not_collinear (L18)` | maxAffineMinor_pos_iff_not_collinear | unmatched |  |
| envDeletionDistance_gt_iff_affineSeparation_pos | lemma | `Helpers/SharpThreshold.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.envDeletionDistance_gt_iff_affineSeparation_pos (L52)` | envDeletionDistance_gt_iff_affineSeparation_pos | unmatched |  |
| compatibleSet_eq_singleton_of_deletionDistance_gt | lemma | `Helpers/SharpThreshold.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.compatibleSet_eq_singleton_of_deletionDistance_gt (L197)` | compatibleSet_eq_singleton_of_deletionDistance_gt | unmatched |  |
| continuousAt_deformedDiagonalizer | lemma | `Helpers/GlobalCollinearAmbiguity.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.continuousAt_deformedDiagonalizer (L21)` | continuousAt_deformedDiagonalizer | unmatched |  |
| exists_deformedDiagonalizer_cycleProduct_radius | lemma | `Helpers/GlobalCollinearAmbiguity.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.exists_deformedDiagonalizer_cycleProduct_radius (L58)` | exists_deformedDiagonalizer_cycleProduct_radius | unmatched |  |
| pairCycleAdmissible_of_cycleProduct_lt_one | lemma | `Helpers/GlobalCollinearAmbiguity.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.pairCycleAdmissible_of_cycleProduct_lt_one (L76)` | pairCycleAdmissible_of_cycleProduct_lt_one | unmatched |  |
| affineLineCertificate_of_collinearPairs | definition | `Helpers/GlobalCollinearAmbiguity.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.affineLineCertificate_of_collinearPairs (L100)` | affineLineCertificate_of_collinearPairs | unmatched |  |
| exists_globally_admissible_collinear_ambiguity | lemma | `Helpers/GlobalCollinearAmbiguity.lean:CausalSmith.ExactID.RobustBackshiftUniformDistance.exists_globally_admissible_collinear_ambiguity (L124)` | exists_globally_admissible_collinear_ambiguity | unmatched |  |
| aux_invariantNoise | definition | `Helpers/ContractionUniformExclusion.lean:invariantNoise (L48)` | aux_invariantNoise | unmatched |  |
| aux_structural | definition | `Helpers/ContractionUniformExclusion.lean:structural (L46)` | aux_structural | unmatched |  |
