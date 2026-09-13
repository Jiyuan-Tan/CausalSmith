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
| P-1 | definition | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.UCVMWModel (L276)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.observableSummaryData (L463)` | P-2 | equivalent |  |
| P-3 | definition | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.empSummary (L500)` | P-3 | equivalent |  |
| P-4 | definition | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.compressedOperatorData (L548)` | P-4 | equivalent |  |
| P-5 | definition | `Helpers/QuotientLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.quotientLaw (L45)` | P-5 | equivalent |  |
| P-6 | definition | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapStratum (L307)` | P-6 | equivalent |  |
| P-7 | definition | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.sampleExperiment (L560)` | P-7 | equivalent |  |
| P-8 | definition | `Helpers/SummaryClosure.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryClosureData (L597)` | P-8 | equivalent |  |
| P-9 | definition | `Helpers/SummaryClosure.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryRepair (L633)` | P-9 | equivalent |  |
| P-10 | definition | `Helpers/Inference.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.confidenceSets (L45)` | P-10 | equivalent |  |
| P-11 | definition | `Helpers/Inference.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.clusterReport (L282)` | P-11 | equivalent |  |
| P-12 | definition | `Helpers/SummaryClosure.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.orderedWeightEstimator (L652)` | P-12 | equivalent |  |
| P-13 | definition | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessLaw (L103)` | P-13 | equivalent |  |
| P-14 | definition | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.LocalQuotientExperiment (L233)` | P-14 | equivalent |  |
| P-15 | definition | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.LocalWeightExperiment (L243)` | P-15 | equivalent |  |
| P-16 | definition | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.repairHandle (L773)` | P-16 | equivalent |  |
| P-17 | definition | `Helpers/LatticeEstimator.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.netLawEstimator (L482)` | P-17 | equivalent |  |
| P-18 | definition | `OpenQuestions.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ConstructiveTotalRepairQuestion (L16)` | P-18 | equivalent |  |
| T-1 | theorem | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.observed_vmw_margin_inclusion (L845)` | T-1 | equivalent |  |
| T-2 | theorem | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summary_closure_compact (L182)` | T-2 | equivalent |  |
| T-3 | theorem | `TGapFreePositiveMeasureModulus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.gap_free_positive_measure_modulus (L18)` | T-3 | equivalent |  |
| T-4 | theorem | `TSummaryRepairTotalBorel.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summary_repair_total_borel (L119)` | T-4 | equivalent |  |
| T-5 | theorem | `TCollisionUniformRootN.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.collision_uniform_root_n (L70)` | T-5 | equivalent |  |
| T-6 | theorem | `THonestRootNConfidence.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.honest_root_n_confidence (L151)` | T-6 | equivalent |  |
| T-7 | theorem | `TClusterAdaptiveReport.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_adaptive_report (L11)` | T-7 | equivalent |  |
| T-8 | theorem | `TLabeledWeightUpper.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.labeled_weight_upper (L11)` | T-8 | equivalent |  |
| T-9 | theorem | `TTwoClassWitnessValid.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.two_class_witness_valid (L14)` | T-9 | equivalent |  |
| T-10 | theorem | `TMatchingLocalLowerBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.matching_local_lower_bounds (L273)` | T-10 | equivalent |  |
| T-11 | theorem | `TSameClassQuotientMinimax.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.same_class_quotient_minimax (L10)` | T-11 | equivalent |  |
| T-12 | theorem | `TSameClassLabeledMinimax.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.same_class_labeled_minimax (L10)` | T-12 | equivalent |  |
| T-13 | theorem | `TFiniteNetLawEstimator.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.finite_net_law_estimator (L14)` | T-13 | equivalent |  |
| T-14 | theorem | `TPublishedVMWConverseTransfer.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.published_vmw_converse_transfer (L215)` | T-14 | equivalent |  |
| T-15 | theorem | `TPolynomialLatticeEstimator.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.polynomial_lattice_law_estimator (L12)` | T-15 | equivalent |  |
| L-1 | lemma | `Helpers/CitedGates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.borelMeasurable_compactLoss_selector (L65)` | L-1 | unmatched |  |
| L-2 | lemma | `Helpers/Concentration.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.uniform_summary_concentration (L11)` | L-2 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ReferenceProxySeparation (L210)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.TargetProxySeparation (L220)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.CausalConsistency (L229)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ArmwiseLatentIgnorability (L233)` | A-4 | equivalent |  |
| A-5 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AnchorNormalization (L242)` | A-5 | equivalent |  |
| A-6 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.BoundedTargetProxy (L246)` | A-6 | equivalent |  |
| A-7 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.BoundedProxyProduct (L255)` | A-7 | equivalent |  |
| A-8 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.BoundedOutcomeProxyProduct (L260)` | A-8 | equivalent |  |
| A-9 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.LatentArmPositivity (L265)` | A-9 | equivalent |  |
| A-10 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ProxyRankMargin (L269)` | A-10 | equivalent |  |
| A-11 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapWindow (L298)` | A-11 | equivalent |  |
| A-12 | assumption | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.DistinctEffects (L302)` | A-12 | equivalent |  |
| A-13 | assumption | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.LocalQuotientNeighborhood (L217)` | A-13 | equivalent |  |
| A-14 | assumption | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.LocalWeightNeighborhood (L225)` | A-14 | equivalent |  |
| aux_AtomicLaw | definition | `Helpers/AtomicLaw.lean:AtomicLaw (L18)` | aux_AtomicLaw | unmatched |  |
| aux_calibratedDisplacement | definition | `Helpers/Witness.lean:calibratedDisplacement (L781)` | aux_calibratedDisplacement | unmatched |  |
| aux_dS | definition | `Basic.lean:dS (L360)` | aux_dS | unmatched |  |
| aux_effectRadius | definition | `Basic.lean:effectRadius (L162)` | aux_effectRadius | unmatched |  |
| aux_expectedLawRisk | definition | `Helpers/Risk.lean:expectedLawRisk (L167)` | aux_expectedLawRisk | unmatched |  |
| aux_expectedWeightRisk | definition | `Helpers/Risk.lean:expectedWeightRisk (L176)` | aux_expectedWeightRisk | unmatched |  |
| aux_FullData | definition | `Basic.lean:FullData (L19)` | aux_FullData | unmatched |  |
| aux_LatticeEstimator | definition | `Helpers/LatticeEstimator.lean:LatticeEstimator (L546)` | aux_LatticeEstimator | unmatched |  |
| aux_LawEstimator | definition | `Helpers/Risk.lean:LawEstimator (L13)` | aux_LawEstimator | unmatched |  |
| aux_ModelLaw | definition | `Helpers/SummaryClosure.lean:ModelLaw (L13)` | aux_ModelLaw | unmatched |  |
| aux_NetLibrary | definition | `Helpers/LatticeEstimator.lean:NetLibrary (L76)` | aux_NetLibrary | unmatched |  |
| aux_Obs | definition | `Basic.lean:Obs (L29)` | aux_Obs | unmatched |  |
| aux_obsLaw | definition | `Basic.lean:obsLaw (L112)` | aux_obsLaw | unmatched |  |
| aux_orderedMasses | definition | `Helpers/SummaryClosure.lean:orderedMasses (L641)` | aux_orderedMasses | unmatched |  |
| aux_pathLaw | definition | `Helpers/Witness.lean:pathLaw (L614)` | aux_pathLaw | unmatched |  |
| aux_ProbabilityLaw | definition | `(none)` | aux_ProbabilityLaw | unmatched |  |
| aux_PublishedSpectralSeparation | definition | `Helpers/CitedGates.lean:PublishedSpectralSeparation (L113)` | aux_PublishedSpectralSeparation | unmatched |  |
| aux_PublishedVMWModel | definition | `Helpers/CitedGates.lean:PublishedVMWModel (L23)` | aux_PublishedVMWModel | unmatched |  |
| aux_RepairHandle | definition | `Helpers/Witness.lean:RepairHandle (L356)` | aux_RepairHandle | unmatched |  |
| aux_sampleLaw | definition | `Basic.lean:sampleLaw (L123)` | aux_sampleLaw | unmatched |  |
| aux_SummaryRepairData | definition | `Helpers/SummaryClosure.lean:SummaryRepairData (L607)` | aux_SummaryRepairData | unmatched |  |
| aux_SummarySpace | definition | `Basic.lean:SummarySpace (L314)` | aux_SummarySpace | unmatched |  |
| aux_TransportPlan | definition | `Helpers/AtomicLaw.lean:TransportPlan (L258)` | aux_TransportPlan | unmatched |  |
| aux_UniformlyBounded | definition | `Basic.lean:UniformlyBounded (L205)` | aux_UniformlyBounded | unmatched |  |
| aux_Valid | definition | `Helpers/AtomicLaw.lean:Valid (L38)` | aux_Valid | unmatched |  |
| aux_wass1 | definition | `Helpers/AtomicLaw.lean:wass1 (L359)` | aux_wass1 | unmatched |  |
| aux_WeightEstimator | definition | `Helpers/Risk.lean:WeightEstimator (L23)` | aux_WeightEstimator | unmatched |  |
| aux_AtomFloor | definition | `Helpers/AtomicLaw.lean:AtomFloor (L1131)` | aux_AtomFloor | unmatched |  |
| aux_CalgHasConstrainedRepresentation | definition | `Helpers/Inference.lean:CalgHasConstrainedRepresentation (L69)` | aux_CalgHasConstrainedRepresentation | unmatched |  |
| aux_ConfidenceSetData | definition | `Helpers/Inference.lean:ConfidenceSetData (L11)` | aux_ConfidenceSetData | unmatched |  |
| aux_CoreParameterDomain | definition | `Basic.lean:CoreParameterDomain (L180)` | aux_CoreParameterDomain | unmatched |  |
| aux_FullDataProbabilityLaw | definition | `Basic.lean:FullDataProbabilityLaw (L92)` | aux_FullDataProbabilityLaw | unmatched |  |
| aux_InSimplex | definition | `Helpers/Risk.lean:InSimplex (L19)` | aux_InSimplex | unmatched |  |
| aux_IsPrescribedStructuredLattice | definition | `Helpers/LatticeEstimator.lean:IsPrescribedStructuredLattice (L691)` | aux_IsPrescribedStructuredLattice | unmatched |  |
| aux_latentEffect | definition | `Basic.lean:latentEffect (L158)` | aux_latentEffect | unmatched |  |
| aux_latticeLaw | definition | `Helpers/LatticeEstimator.lean:latticeLaw (L718)` | aux_latticeLaw | unmatched |  |
| aux_LawModulo | definition | `Helpers/AtomicLaw.lean:LawModulo (L203)` | aux_LawModulo | unmatched |  |
| aux_MatrixEigenvalue | definition | `Helpers/Witness.lean:MatrixEigenvalue (L251)` | aux_MatrixEigenvalue | unmatched |  |
| aux_obsSummary | definition | `Basic.lean:obsSummary (L352)` | aux_obsSummary | unmatched |  |
| aux_PublishedAssumption4 | definition | `(none)` | aux_PublishedAssumption4 | unmatched |  |
| aux_PublishedFeatureWeightRecovery | definition | `(none)` | aux_PublishedFeatureWeightRecovery | unmatched |  |
| aux_PublishedRecoveryHypotheses | definition | `(none)` | aux_PublishedRecoveryHypotheses | unmatched |  |
| aux_quotientLawRaw | definition | `Basic.lean:quotientLawRaw (L555)` | aux_quotientLawRaw | unmatched |  |
| aux_representative | definition | `Helpers/AtomicLaw.lean:representative (L218)` | aux_representative | unmatched |  |
| aux_singularValue | definition | `Helpers/SpectralSubstrate.lean:singularValue (L41)` | aux_singularValue | unmatched |  |
| aux_stackedProxyMoment | definition | `Basic.lean:stackedProxyMoment (L480)` | aux_stackedProxyMoment | unmatched |  |
| aux_StructuredLatticePoint | definition | `Helpers/LatticeEstimator.lean:StructuredLatticePoint (L564)` | aux_StructuredLatticePoint | unmatched |  |
| aux_summaryClosure | definition | `Helpers/SummaryClosure.lean:summaryClosure (L29)` | aux_summaryClosure | unmatched |  |
| aux_InHalfOpenSummaryCube | definition | `Helpers/LatticeEstimator.lean:InHalfOpenSummaryCube (L52)` | aux_InHalfOpenSummaryCube | unmatched |  |
| aux_InSummaryBox | definition | `Helpers/LatticeEstimator.lean:InSummaryBox (L44)` | aux_InSummaryBox | unmatched |  |
| aux_LocalRadiusDomain | definition | `Helpers/Witness.lean:LocalRadiusDomain (L796)` | aux_LocalRadiusDomain | unmatched |  |
| aux_netOperationCount | definition | `Helpers/LatticeEstimator.lean:netOperationCount (L489)` | aux_netOperationCount | unmatched |  |
| aux_PublishedRecoveryEstimator | definition | `(none)` | aux_PublishedRecoveryEstimator | unmatched |  |
| aux_RepresentativeSpectralData | definition | `Helpers/LatticeEstimator.lean:RepresentativeSpectralData (L16)` | aux_RepresentativeSpectralData | unmatched |  |
| aux_SignalBasis | definition | `Basic.lean:SignalBasis (L508)` | aux_SignalBasis | unmatched |  |
| aux_SingularSystem | definition | `Helpers/SpectralSubstrate.lean:SingularSystem (L57)` | aux_SingularSystem | unmatched |  |
| aux_SummaryLexLE | definition | `Helpers/LatticeEstimator.lean:SummaryLexLE (L72)` | aux_SummaryLexLE | unmatched |  |
| aux_matrixCLM | definition | `Helpers/SpectralSubstrate.lean:matrixCLM (L20)` | aux_matrixCLM | unmatched |  |
| aux_MatrixEigenvector | definition | `Helpers/Witness.lean:MatrixEigenvector (L256)` | aux_MatrixEigenvector | unmatched |  |
| aux_prescribedLatticeConstant | definition | `Helpers/LatticeEstimator.lean:prescribedLatticeConstant (L583)` | aux_prescribedLatticeConstant | unmatched |  |
| aux_RectMatrix | definition | `Helpers/SpectralSubstrate.lean:RectMatrix (L17)` | aux_RectMatrix | unmatched |  |
| aux_summaryRadius | definition | `Basic.lean:summaryRadius (L586)` | aux_summaryRadius | unmatched |  |
| aux_ThresholdRecoversMatrixDimension | definition | `Helpers/LatticeEstimator.lean:ThresholdRecoversMatrixDimension (L600)` | aux_ThresholdRecoversMatrixDimension | unmatched |  |
| aux_twoClassRepairHandle | definition | `(none)` | aux_twoClassRepairHandle | unmatched |  |
| aux_wassDiameter | definition | `THonestRootNConfidence.lean:wassDiameter (L84)` | aux_wassDiameter | unmatched |  |
| aux_compressedOperator | definition | `Basic.lean:compressedOperator (L526)` | aux_compressedOperator | unmatched |  |
| aux_derivedRepresentativeSpectralData | definition | `(none)` | aux_derivedRepresentativeSpectralData | unmatched |  |
| aux_NetOperationCount | definition | `Helpers/LatticeEstimator.lean:NetOperationCount (L285)` | aux_NetOperationCount | unmatched |  |
| aux_observedProxyMoment | definition | `Basic.lean:observedProxyMoment (L467)` | aux_observedProxyMoment | unmatched |  |
| aux_TangentAmplitudeDomain | definition | `Helpers/Witness.lean:TangentAmplitudeDomain (L609)` | aux_TangentAmplitudeDomain | unmatched |  |
| matrixCLM_continuous | lemma | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.matrixCLM_continuous (L26)` | matrixCLM_continuous | unmatched |  |
| bernoulliMass_nonneg | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.bernoulliMass_nonneg (L17)` | bernoulliMass_nonneg | unmatched |  |
| sum_bernoulliMass | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.sum_bernoulliMass (L23)` | sum_bernoulliMass | unmatched |  |
| sum_mul_bernoulliMass | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.sum_mul_bernoulliMass (L28)` | sum_mul_bernoulliMass | unmatched |  |
| pathArmWeights_formula | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathArmWeights_formula (L478)` | pathArmWeights_formula | unmatched |  |
| pathTargetTransposeInverse_formula | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathTargetTransposeInverse_formula (L498)` | pathTargetTransposeInverse_formula | unmatched |  |
| pathReferenceFeature_second_formula | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathReferenceFeature_second_formula (L534)` | pathReferenceFeature_second_formula | unmatched |  |
| inverseGramSqrt_exists | lemma | `Helpers/LatticeEstimator.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.inverseGramSqrt_exists (L612)` | inverseGramSqrt_exists | unmatched |  |
| vmwModelScope_holds | lemma | `(none)` | vmwModelScope_holds | unmatched |  |
| clusterReport_side_conditions | lemma | `Helpers/Inference.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.clusterReport_side_conditions (L185)` | clusterReport_side_conditions | unmatched |  |
| observed_summary_block_bounds | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.observed_summary_block_bounds (L898)` | observed_summary_block_bounds | unmatched |  |
| matrixEntry_abs_le_operatorNorm | lemma | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.matrixEntry_abs_le_operatorNorm (L11)` | matrixEntry_abs_le_operatorNorm | unmatched |  |
| summaryMatrixBox | definition | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryMatrixBox (L23)` | summaryMatrixBox | unmatched |  |
| summaryMatrixBox_compact | lemma | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryMatrixBox_compact (L28)` | summaryMatrixBox_compact | unmatched |  |
| summaryVectorBox | definition | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryVectorBox (L34)` | summaryVectorBox | unmatched |  |
| summaryVectorBox_compact | lemma | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryVectorBox_compact (L39)` | summaryVectorBox_compact | unmatched |  |
| summaryCoordinateBox | definition | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryCoordinateBox (L45)` | summaryCoordinateBox | unmatched |  |
| summaryCoordinateBox_compact | lemma | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryCoordinateBox_compact (L51)` | summaryCoordinateBox_compact | unmatched |  |
| summarySpaceEquivCoordinates | definition | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summarySpaceEquivCoordinates (L59)` | summarySpaceEquivCoordinates | unmatched |  |
| summarySpaceHomeomorphCoordinates | definition | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summarySpaceHomeomorphCoordinates (L68)` | summarySpaceHomeomorphCoordinates | unmatched |  |
| summarySpaceBox | definition | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summarySpaceBox (L79)` | summarySpaceBox | unmatched |  |
| summarySpaceBox_compact | lemma | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summarySpaceBox_compact (L84)` | summarySpaceBox_compact | unmatched |  |
| admissibleImage_subset_summarySpaceBox | lemma | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.admissibleImage_subset_summarySpaceBox (L100)` | admissibleImage_subset_summarySpaceBox | unmatched |  |
| summaryClosure_compact_of_block_bounds | lemma | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryClosure_compact_of_block_bounds (L131)` | summaryClosure_compact_of_block_bounds | unmatched |  |
| admissibleImage_dS_bounded | lemma | `TSummaryClosureCompact.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.admissibleImage_dS_bounded (L141)` | admissibleImage_dS_bounded | unmatched |  |
| support_close_of_wass1_le | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.support_close_of_wass1_le (L1140)` | support_close_of_wass1_le | unmatched |  |
| hemp | assumption | `(none)` | hemp | unmatched |  |
| summaryRepairToEuc | definition | `TSummaryRepairTotalBorel.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryRepairToEuc (L16)` | summaryRepairToEuc | unmatched |  |
| summaryRepairOfEuc | definition | `TSummaryRepairTotalBorel.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryRepairOfEuc (L25)` | summaryRepairOfEuc | unmatched |  |
| summaryRepairSpaceHomeomorph | definition | `TSummaryRepairTotalBorel.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryRepairSpaceHomeomorph (L33)` | summaryRepairSpaceHomeomorph | unmatched |  |
| euclideanReindexHomeomorph | definition | `TSummaryRepairTotalBorel.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.euclideanReindexHomeomorph (L75)` | euclideanReindexHomeomorph | unmatched |  |
| compactLoss_selector_of_homeomorph | lemma | `TSummaryRepairTotalBorel.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.compactLoss_selector_of_homeomorph (L90)` | compactLoss_selector_of_homeomorph | unmatched |  |
| wass1_le_of_plan | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.wass1_le_of_plan (L364)` | wass1_le_of_plan | unmatched |  |
| wass1_optimal_plan | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.wass1_optimal_plan (L377)` | wass1_optimal_plan | unmatched |  |
| confidenceSets_constrainedRepresentation | lemma | `Helpers/Inference.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.confidenceSets_constrainedRepresentation (L78)` | confidenceSets_constrainedRepresentation | unmatched |  |
| integral_le_of_gaussian_tail | lemma | `Helpers/Risk.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.integral_le_of_gaussian_tail (L206)` | integral_le_of_gaussian_tail | unmatched |  |
| integral_le_of_sqrt_log_tail | lemma | `Helpers/Risk.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.integral_le_of_sqrt_log_tail (L267)` | integral_le_of_sqrt_log_tail | unmatched |  |
| instMeasurableSingletonClassFullData | definition | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.FullDataProbabilityLaw (L92)` | instMeasurableSingletonClassFullData | unmatched |  |
| witnessWeight_sum_nuisance | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessWeight_sum_nuisance (L161)` | witnessWeight_sum_nuisance | unmatched |  |
| singular_value_variational_lower | lemma | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.singular_value_variational_lower (L218)` | singular_value_variational_lower | unmatched |  |
| dS_symm | lemma | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.dS_symm (L367)` | dS_symm | unmatched |  |
| dS_triangle | lemma | `Basic.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.dS_triangle (L383)` | dS_triangle | unmatched |  |
| singular_value_weyl | lemma | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.singular_value_weyl (L259)` | singular_value_weyl | unmatched |  |
| singularSystem_exists | lemma | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.singularSystem_exists (L72)` | singularSystem_exists | unmatched |  |
| witnessWeight_nonneg | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessWeight_nonneg (L63)` | witnessWeight_nonneg | unmatched |  |
| measurableSet_witness_latentCell | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurableSet_witness_latentCell (L71)` | measurableSet_witness_latentCell | unmatched |  |
| measurableSet_witness_latentClass | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurableSet_witness_latentClass (L84)` | measurableSet_witness_latentClass | unmatched |  |
| integral_witnessLaw_restrict | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.integral_witnessLaw_restrict (L170)` | integral_witnessLaw_restrict | unmatched |  |
| witnessLaw_real | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessLaw_real (L192)` | witnessLaw_real | unmatched |  |
| conditionalMean_witnessLaw | lemma | `Helpers/Witness.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_witnessLaw (L203)` | conditionalMean_witnessLaw | unmatched |  |
| witness_referenceProxySeparation | lemma | `Helpers/WitnessFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_referenceProxySeparation (L99)` | witness_referenceProxySeparation | unmatched |  |
| witness_targetProxySeparation | lemma | `Helpers/WitnessFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_targetProxySeparation (L111)` | witness_targetProxySeparation | unmatched |  |
| witness_armwiseLatentIgnorability | lemma | `Helpers/WitnessFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_armwiseLatentIgnorability (L123)` | witness_armwiseLatentIgnorability | unmatched |  |
| witness_sum_restrict_latentCell | lemma | `Helpers/WitnessFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_sum_restrict_latentCell (L14)` | witness_sum_restrict_latentCell | unmatched |  |
| conditionalMean_witness_latentCell | lemma | `Helpers/WitnessFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_witness_latentCell (L44)` | conditionalMean_witness_latentCell | unmatched |  |
| witness_sum_restrict_latentClass | lemma | `Helpers/WitnessFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_sum_restrict_latentClass (L60)` | witness_sum_restrict_latentClass | unmatched |  |
| conditionalMean_witness_latentClass | lemma | `Helpers/WitnessFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_witness_latentClass (L83)` | conditionalMean_witness_latentClass | unmatched |  |
| signalMinSingular_lower_fin_two | lemma | `Helpers/WitnessSpectral.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.signalMinSingular_lower_fin_two (L12)` | signalMinSingular_lower_fin_two | unmatched |  |
| witnessTargetMatrix_signalMinSingular | lemma | `Helpers/WitnessSpectral.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessTargetMatrix_signalMinSingular (L44)` | witnessTargetMatrix_signalMinSingular | unmatched |  |
| witnessReferenceMatrix_false_signalMinSingular | lemma | `Helpers/WitnessSpectral.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessReferenceMatrix_false_signalMinSingular (L54)` | witnessReferenceMatrix_false_signalMinSingular | unmatched |  |
| witnessReferenceMatrix_true_signalMinSingular | lemma | `Helpers/WitnessSpectral.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessReferenceMatrix_true_signalMinSingular (L64)` | witnessReferenceMatrix_true_signalMinSingular | unmatched |  |
| measurableSet_obsArm | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurableSet_obsArm (L13)` | measurableSet_obsArm | unmatched |  |
| measurable_obs_Z_mul_X | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurable_obs_Z_mul_X (L22)` | measurable_obs_Z_mul_X | unmatched |  |
| obs_witness_arm_mass | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.obs_witness_arm_mass (L35)` | obs_witness_arm_mass | unmatched |  |
| witness_latentMass | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_latentMass (L61)` | witness_latentMass | unmatched |  |
| witness_latentCell_mass | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_latentCell_mass (L74)` | witness_latentCell_mass | unmatched |  |
| witness_targetFeature | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_targetFeature (L88)` | witness_targetFeature | unmatched |  |
| witness_referenceFeature | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_referenceFeature (L99)` | witness_referenceFeature | unmatched |  |
| witness_latentEffect | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_latentEffect (L113)` | witness_latentEffect | unmatched |  |
| conditionalMean_obsLaw_witness | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_obsLaw_witness (L126)` | conditionalMean_obsLaw_witness | unmatched |  |
| witness_sum_restrict_obsArm | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_sum_restrict_obsArm (L158)` | witness_sum_restrict_obsArm | unmatched |  |
| conditionalMean_obsArm_witness | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_obsArm_witness (L173)` | conditionalMean_obsArm_witness | unmatched |  |
| witnessWeight_sum_outcomes_mul | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessWeight_sum_outcomes_mul (L190)` | witnessWeight_sum_outcomes_mul | unmatched |  |
| witnessWeight_sum_outcomes | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessWeight_sum_outcomes (L213)` | witnessWeight_sum_outcomes | unmatched |  |
| conditionalMean_obsArm_ZX | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_obsArm_ZX (L224)` | conditionalMean_obsArm_ZX | unmatched |  |
| witness_observedProxyMoment_entry | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_observedProxyMoment_entry (L252)` | witness_observedProxyMoment_entry | unmatched |  |
| witness_observedProxyMoment_det | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_observedProxyMoment_det (L273)` | witness_observedProxyMoment_det | unmatched |  |
| ae_witnessLaw_of_points | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ae_witnessLaw_of_points (L288)` | ae_witnessLaw_of_points | unmatched |  |
| witness_consistency | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_consistency (L301)` | witness_consistency | unmatched |  |
| witness_anchor | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_anchor (L309)` | witness_anchor | unmatched |  |
| witness_outerProduct_norm | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_outerProduct_norm (L317)` | witness_outerProduct_norm | unmatched |  |
| witness_boundedX | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_boundedX (L340)` | witness_boundedX | unmatched |  |
| witness_boundedProxyProduct | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_boundedProxyProduct (L349)` | witness_boundedProxyProduct | unmatched |  |
| witness_boundedOutcomeProxyProduct | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_boundedOutcomeProxyProduct (L358)` | witness_boundedOutcomeProxyProduct | unmatched |  |
| witness_latentArmPositivity | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_latentArmPositivity (L381)` | witness_latentArmPositivity | unmatched |  |
| witness_proxyRankMargin | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_proxyRankMargin (L389)` | witness_proxyRankMargin | unmatched |  |
| witness_det_targetFeature | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_det_targetFeature (L402)` | witness_det_targetFeature | unmatched |  |
| witness_det_referenceFeature | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_det_referenceFeature (L409)` | witness_det_referenceFeature | unmatched |  |
| two_by_two_injective_of_signalMinSingular_pos | lemma | `Helpers/WitnessValidity.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.two_by_two_injective_of_signalMinSingular_pos (L417)` | two_by_two_injective_of_signalMinSingular_pos | unmatched |  |
| measurable_fullData_T | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurable_fullData_T (L15)` | measurable_fullData_T | unmatched |  |
| measurable_fullData_U | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurable_fullData_U (L22)` | measurable_fullData_U | unmatched |  |
| measurable_obs_T | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurable_obs_T (L29)` | measurable_obs_T | unmatched |  |
| measurableSet_latentClass | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurableSet_latentClass (L35)` | measurableSet_latentClass | unmatched |  |
| measurableSet_latentCell | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurableSet_latentCell (L41)` | measurableSet_latentCell | unmatched |  |
| measurableSet_fullDataArm | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurableSet_fullDataArm (L49)` | measurableSet_fullDataArm | unmatched |  |
| measurableSet_obsArm_generic | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurableSet_obsArm_generic (L55)` | measurableSet_obsArm_generic | unmatched |  |
| obsLaw_real_obsArm | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.obsLaw_real_obsArm (L61)` | obsLaw_real_obsArm | unmatched |  |
| fullDataArm_eq_iUnion_latentCell | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.fullDataArm_eq_iUnion_latentCell (L106)` | fullDataArm_eq_iUnion_latentCell | unmatched |  |
| fullDataArm_real_eq_sum_latentCell | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.fullDataArm_real_eq_sum_latentCell (L113)` | fullDataArm_real_eq_sum_latentCell | unmatched |  |
| arm_mass_lower_of_latentArmPositivity | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.arm_mass_lower_of_latentArmPositivity (L127)` | arm_mass_lower_of_latentArmPositivity | unmatched |  |
| latentCell_pos_of_latentArmPositivity | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.latentCell_pos_of_latentArmPositivity (L139)` | latentCell_pos_of_latentArmPositivity | unmatched |  |
| fullDataArm_pos_of_latentArmPositivity | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.fullDataArm_pos_of_latentArmPositivity (L148)` | fullDataArm_pos_of_latentArmPositivity | unmatched |  |
| latentArmWeight_lower | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.latentArmWeight_lower (L159)` | latentArmWeight_lower | unmatched |  |
| latentArmWeights_injective | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.latentArmWeights_injective (L180)` | latentArmWeights_injective | unmatched |  |
| conditionalMean_obsLaw_eq_fullData | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_obsLaw_eq_fullData (L71)` | conditionalMean_obsLaw_eq_fullData | unmatched |  |
| obsMap_preimage_obsArm | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.obsMap_preimage_obsArm (L91)` | obsMap_preimage_obsArm | unmatched |  |
| conditionalMean_obsArm_eq_fullDataArm | lemma | `Helpers/ObservedLawAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_obsArm_eq_fullDataArm (L96)` | conditionalMean_obsArm_eq_fullDataArm | unmatched |  |
| abs_matrix_entry_le_matrixCLM_norm | lemma | `Helpers/ConditionalMomentAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.abs_matrix_entry_le_matrixCLM_norm (L16)` | abs_matrix_entry_le_matrixCLM_norm | unmatched |  |
| proxy_coordinate_bounds_of_model | lemma | `Helpers/ConditionalMomentAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.proxy_coordinate_bounds_of_model (L32)` | proxy_coordinate_bounds_of_model | unmatched |  |
| latentArmWeights_minSingular | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.latentArmWeights_minSingular (L24)` | latentArmWeights_minSingular | unmatched |  |
| observedProxyMoment_minSingular_of_factorization | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.observedProxyMoment_minSingular_of_factorization (L54)` | observedProxyMoment_minSingular_of_factorization | unmatched |  |
| measurable_fullData_X | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurable_fullData_X (L18)` | measurable_fullData_X | unmatched |  |
| measurable_fullData_Z | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurable_fullData_Z (L25)` | measurable_fullData_Z | unmatched |  |
| conditionalMean_fullDataArm_eq_sum_latentCell | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_fullDataArm_eq_sum_latentCell (L73)` | conditionalMean_fullDataArm_eq_sum_latentCell | unmatched |  |
| latentCell_ZX_conditionalMean_factorization | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.latentCell_ZX_conditionalMean_factorization (L104)` | latentCell_ZX_conditionalMean_factorization | unmatched |  |
| latentCell_X_conditionalMean_eq_latentClass | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.latentCell_X_conditionalMean_eq_latentClass (L154)` | latentCell_X_conditionalMean_eq_latentClass | unmatched |  |
| observedProxyMoment_factorization | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.observedProxyMoment_factorization (L239)` | observedProxyMoment_factorization | unmatched |  |
| matrixCLM_conditionalOuterMoment_eq_integral | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.matrixCLM_conditionalOuterMoment_eq_integral (L291)` | matrixCLM_conditionalOuterMoment_eq_integral | unmatched |  |
| signalBasisLinearIsometry | definition | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.signalBasisLinearIsometry (L108)` | signalBasisLinearIsometry | unmatched |  |
| observedProxyMoment_compression_margin | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.observedProxyMoment_compression_margin (L135)` | observedProxyMoment_compression_margin | unmatched |  |
| latentIgnorability_to_normalizedFactorization | lemma | `Helpers/ConditionalMomentAdapters.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.latentIgnorability_to_normalizedFactorization (L180)` | latentIgnorability_to_normalizedFactorization | unmatched |  |
| measurable_fullData_Y | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurable_fullData_Y (L32)` | measurable_fullData_Y | unmatched |  |
| measurable_potential | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurable_potential (L40)` | measurable_potential | unmatched |  |
| measurable_obs_X | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurable_obs_X (L54)` | measurable_obs_X | unmatched |  |
| measurable_obs_Z | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurable_obs_Z (L60)` | measurable_obs_Z | unmatched |  |
| measurable_obs_Y | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurable_obs_Y (L66)` | measurable_obs_Y | unmatched |  |
| matrixCLM_conditionalMatrix_eq_integral | lemma | `Helpers/ObservedMarginAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.matrixCLM_conditionalMatrix_eq_integral (L321)` | matrixCLM_conditionalMatrix_eq_integral | unmatched |  |
| ae_abs_right_le_of_indep_product_bound | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ae_abs_right_le_of_indep_product_bound (L196)` | ae_abs_right_le_of_indep_product_bound | unmatched |  |
| ae_abs_le_of_indep_positive_event | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ae_abs_le_of_indep_positive_event (L236)` | ae_abs_le_of_indep_positive_event | unmatched |  |
| exists_reference_coordinate_positive_event | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.exists_reference_coordinate_positive_event (L269)` | exists_reference_coordinate_positive_event | unmatched |  |
| ae_abs_observedOutcome_le_on_latentCell | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ae_abs_observedOutcome_le_on_latentCell (L371)` | ae_abs_observedOutcome_le_on_latentCell | unmatched |  |
| ae_abs_potential_le_on_latentClass | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ae_abs_potential_le_on_latentClass (L422)` | ae_abs_potential_le_on_latentClass | unmatched |  |
| conditionalMatrix_norm_le_of_ae_bound | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMatrix_norm_le_of_ae_bound (L580)` | conditionalMatrix_norm_le_of_ae_bound | unmatched |  |
| observedSummary_envelopes_of_model | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.observedSummary_envelopes_of_model (L614)` | observedSummary_envelopes_of_model | unmatched |  |
| observedProxyMoment_norm_le_stackedProxyMoment | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.observedProxyMoment_norm_le_stackedProxyMoment (L724)` | observedProxyMoment_norm_le_stackedProxyMoment | unmatched |  |
| stackedProxyMoment_minSingular | lemma | `TObservedVMWMarginInclusion.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.stackedProxyMoment_minSingular (L767)` | stackedProxyMoment_minSingular | unmatched |  |
| signalMinSingular_pos_injective | lemma | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.signalMinSingular_pos_injective (L273)` | signalMinSingular_pos_injective | unmatched |  |
| gram_det_isUnit_of_injective | lemma | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.gram_det_isUnit_of_injective (L284)` | gram_det_isUnit_of_injective | unmatched |  |
| penrose_left_inverse | lemma | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.penrose_left_inverse (L312)` | penrose_left_inverse | unmatched |  |
| penrose_projection_contracts | lemma | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.penrose_projection_contracts (L343)` | penrose_projection_contracts | unmatched |  |
| penrose_norm_le | lemma | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.penrose_norm_le (L385)` | penrose_norm_le | unmatched |  |
| gram_inverse_norm_le | lemma | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.gram_inverse_norm_le (L408)` | gram_inverse_norm_le | unmatched |  |
| atomicLaw_coordinateHomeomorph | definition | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.coordinateHomeomorph (L45)` | atomicLaw_coordinateHomeomorph | unmatched |  |
| atomicLaw_valid_isCompact | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.valid_isCompact (L57)` | atomicLaw_valid_isCompact | unmatched |  |
| probabilityLaw_compactSpace | definition | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.probabilityLawCompactSpace (L108)` | probabilityLaw_compactSpace | unmatched |  |
| atomicLaw_toMeasure_singleton | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.toMeasure_singleton (L156)` | atomicLaw_toMeasure_singleton | unmatched |  |
| measureEquivalent_aggregate_weight | lemma | `(none)` | measureEquivalent_aggregate_weight | unmatched |  |
| lawModulo_compactSpace | definition | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.compactSpace (L232)` | lawModulo_compactSpace | unmatched |  |
| measureEquivalent_zeroTransportPlan | definition | `(none)` | measureEquivalent_zeroTransportPlan | unmatched |  |
| measureEquivalent_zeroTransportCost | lemma | `(none)` | measureEquivalent_zeroTransportCost | unmatched |  |
| atomicLaw_wass1_nonneg | lemma | `(none)` | atomicLaw_wass1_nonneg | unmatched |  |
| atomicLaw_wass1_comm | lemma | `(none)` | atomicLaw_wass1_comm | unmatched |  |
| atomicLaw_wass1_self | lemma | `(none)` | atomicLaw_wass1_self | unmatched |  |
| measureEquivalent_wass1_eq_zero | lemma | `(none)` | measureEquivalent_wass1_eq_zero | unmatched |  |
| transportPlan_mass_eq_zero_of_snd_weight_eq_zero | lemma | `(none)` | transportPlan_mass_eq_zero_of_snd_weight_eq_zero | unmatched |  |
| transportPlan_glue | definition | `(none)` | transportPlan_glue | unmatched |  |
| transportCost_glue_le | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.transportCost_glue_le (L604)` | transportCost_glue_le | unmatched |  |
| atomicLaw_wass1_triangle | lemma | `(none)` | atomicLaw_wass1_triangle | unmatched |  |
| transportPlan_mass_eq_zero_of_cost_eq_zero | lemma | `(none)` | transportPlan_mass_eq_zero_of_cost_eq_zero | unmatched |  |
| measureEquivalent_of_transportCost_eq_zero | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.measureEquivalent_of_transportCost_eq_zero (L731)` | measureEquivalent_of_transportCost_eq_zero | unmatched |  |
| wass1_eq_zero_iff_measureEquivalent | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.wass1_eq_zero_iff_measureEquivalent (L781)` | wass1_eq_zero_iff_measureEquivalent | unmatched |  |
| atomicLaw_wass1_congr_left | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.wass1_congr_left (L793)` | atomicLaw_wass1_congr_left | unmatched |  |
| atomicLaw_wass1_congr_right | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.wass1_congr_right (L810)` | atomicLaw_wass1_congr_right | unmatched |  |
| atomicLaw_wass1_congr | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.wass1_congr (L818)` | atomicLaw_wass1_congr | unmatched |  |
| lawModulo_wass1_self | lemma | `(none)` | lawModulo_wass1_self | unmatched |  |
| lawModulo_wass1_comm | lemma | `(none)` | lawModulo_wass1_comm | unmatched |  |
| lawModulo_wass1_triangle | lemma | `(none)` | lawModulo_wass1_triangle | unmatched |  |
| lawModulo_eq_of_wass1_eq_zero | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.eq_of_wass1_eq_zero (L856)` | lawModulo_eq_of_wass1_eq_zero | unmatched |  |
| lawModulo_rawMetricSpace | definition | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.rawMetricSpace (L868)` | lawModulo_rawMetricSpace | unmatched |  |
| lawModulo_rawMetricSpace_dist | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.rawMetricSpace_dist (L879)` | lawModulo_rawMetricSpace_dist | unmatched |  |
| probabilityLaw_coordinateTransportPlan | definition | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.probabilityLaw_coordinateTransportPlan (L887)` | probabilityLaw_coordinateTransportPlan | unmatched |  |
| atomicLaw_wass1_le_coordinateBound | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.wass1_le_coordinateBound (L967)` | atomicLaw_wass1_le_coordinateBound | unmatched |  |
| lawModulo_wass1_ofProbabilityLaw | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.wass1_ofProbabilityLaw (L1028)` | lawModulo_wass1_ofProbabilityLaw | unmatched |  |
| lawModulo_continuous_ofProbabilityLaw_rawMetric | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.continuous_ofProbabilityLaw_rawMetric (L1042)` | lawModulo_continuous_ofProbabilityLaw_rawMetric | unmatched |  |
| lawModulo_rawMetricSpace_topology_eq | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.rawMetricSpace_topology_eq (L1091)` | lawModulo_rawMetricSpace_topology_eq | unmatched |  |
| lawModulo_metricSpace | definition | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.metricSpace (L1107)` | lawModulo_metricSpace | unmatched |  |
| lawModulo_dist_eq_wass1 | lemma | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.dist_eq_wass1 (L1113)` | lawModulo_dist_eq_wass1 | unmatched |  |
| lawModulo_completeSpace | definition | `Helpers/AtomicLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw.LawModulo.completeSpace (L1119)` | lawModulo_completeSpace | unmatched |  |
| quotientFunctionalCalculus_diagonalizedOperator | definition | `Helpers/QuotientFunctionalCalculus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.DiagonalizedOperator (L22)` | quotientFunctionalCalculus_diagonalizedOperator | unmatched |  |
| quotientFunctionalCalculus_spectralWeight | definition | `Helpers/QuotientFunctionalCalculus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.spectralWeight (L35)` | quotientFunctionalCalculus_spectralWeight | unmatched |  |
| quotientFunctionalCalculus_applyFunction | definition | `Helpers/QuotientFunctionalCalculus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.applyFunction (L41)` | quotientFunctionalCalculus_applyFunction | unmatched |  |
| quotientFunctionalCalculus_anchorEval | definition | `Helpers/QuotientFunctionalCalculus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.anchorEval (L47)` | quotientFunctionalCalculus_anchorEval | unmatched |  |
| quotientFunctionalCalculus_anchorEval_applyFunction | lemma | `Helpers/QuotientFunctionalCalculus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.anchorEval_applyFunction (L54)` | quotientFunctionalCalculus_anchorEval_applyFunction | unmatched |  |
| quotientFunctionalCalculus_atomicLaw | definition | `Helpers/QuotientFunctionalCalculus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.atomicLaw (L90)` | quotientFunctionalCalculus_atomicLaw | unmatched |  |
| quotientFunctionalCalculus_atomicLaw_valid | lemma | `Helpers/QuotientFunctionalCalculus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.atomicLaw_valid (L97)` | quotientFunctionalCalculus_atomicLaw_valid | unmatched |  |
| quotientFunctionalCalculus_quotientLaw | definition | `Helpers/QuotientFunctionalCalculus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.quotientLaw (L105)` | quotientFunctionalCalculus_quotientLaw | unmatched |  |
| quotientFunctionalCalculus_wass1_le_coordinateL1 | lemma | `Helpers/QuotientFunctionalCalculus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.wass1_le_coordinateL1 (L114)` | quotientFunctionalCalculus_wass1_le_coordinateL1 | unmatched |  |
| quotientFunctionalCalculus_gapFree_operatorAnchor_bound | lemma | `Helpers/QuotientFunctionalCalculus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.gapFree_operatorAnchor_bound (L154)` | quotientFunctionalCalculus_gapFree_operatorAnchor_bound | unmatched |  |
| quotientFunctionalCalculus_gapFree_fixedK_envelope | lemma | `Helpers/QuotientFunctionalCalculus.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.gapFree_fixedK_envelope (L344)` | quotientFunctionalCalculus_gapFree_fixedK_envelope | unmatched |  |
| subspace_alignment_signalBasis_gram | lemma | `(none)` | subspace_alignment_signalBasis_gram | unmatched |  |
| subspace_alignment_cross_projection | lemma | `(none)` | subspace_alignment_cross_projection | unmatched |  |
| subspace_alignment_exact_procrustes | lemma | `(none)` | subspace_alignment_exact_procrustes | unmatched |  |
| subspace_alignment_exact_bound | lemma | `(none)` | subspace_alignment_exact_bound | unmatched |  |
| gapFreeModulusBridge_asNeutral | definition | `Helpers/GapFreeModulusBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapFreeModulusBridge.asNeutral (L16)` | gapFreeModulusBridge_asNeutral | unmatched |  |
| gapFreeModulusBridge_asNeutral_valid | lemma | `Helpers/GapFreeModulusBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapFreeModulusBridge.asNeutral_valid (L22)` | gapFreeModulusBridge_asNeutral_valid | unmatched |  |
| gapFreeModulusBridge_wass1_eq_neutralW1 | lemma | `Helpers/GapFreeModulusBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapFreeModulusBridge.wass1_eq_neutralW1 (L60)` | gapFreeModulusBridge_wass1_eq_neutralW1 | unmatched |  |
| gapFreeModulusBridge_lawModulo_wass1_eq_neutralW1 | lemma | `Helpers/GapFreeModulusBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapFreeModulusBridge.lawModulo_wass1_eq_neutralW1 (L89)` | gapFreeModulusBridge_lawModulo_wass1_eq_neutralW1 | unmatched |  |
| gapFreeModulusBridge_exists_unique_lipschitz_extension | lemma | `Helpers/GapFreeModulusBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapFreeModulusBridge.exists_unique_lipschitz_extension (L99)` | gapFreeModulusBridge_exists_unique_lipschitz_extension | unmatched |  |
| ambientOperatorBridge_ambientEffectOperator | definition | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.ambientEffectOperator (L24)` | ambientOperatorBridge_ambientEffectOperator | unmatched |  |
| ambientOperatorBridge_norm_product_difference | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.norm_product_difference (L31)` | ambientOperatorBridge_norm_product_difference | unmatched |  |
| ambientOperatorBridge_norm_ambientEffectOperator_sub_le | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.norm_ambientEffectOperator_sub_le (L62)` | ambientOperatorBridge_norm_ambientEffectOperator_sub_le | unmatched |  |
| ambientOperatorBridge_norm_mX_sub_le_dS | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.norm_mX_sub_le_dS (L132)` | ambientOperatorBridge_norm_mX_sub_le_dS | unmatched |  |
| ambientOperatorBridge_norm_firstBasis | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.norm_firstBasis (L378)` | ambientOperatorBridge_norm_firstBasis | unmatched |  |
| ambientOperatorBridge_atomicW1_le_dS_of_certificates | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.atomicW1_le_dS_of_certificates (L528)` | ambientOperatorBridge_atomicW1_le_dS_of_certificates | unmatched |  |
| ambientOperatorBridge_model_summary_rank_eq | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.model_summary_rank_eq (L283)` | ambientOperatorBridge_model_summary_rank_eq | unmatched |  |
| ambientOperatorBridge_model_summary_ambient_bounds | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.model_summary_ambient_bounds (L317)` | ambientOperatorBridge_model_summary_ambient_bounds | unmatched |  |
| ambientOperatorBridge_modelLaw_wass1_le_dS_of_certificates | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.modelLaw_wass1_le_dS_of_certificates (L586)` | ambientOperatorBridge_modelLaw_wass1_le_dS_of_certificates | unmatched |  |
| outcomeFactorization_conditionalMean_potential_latentCell | lemma | `Helpers/OutcomeFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_potential_latentCell (L16)` | outcomeFactorization_conditionalMean_potential_latentCell | unmatched |  |
| outcomeFactorization_conditionalMean_observed_eq_potential | lemma | `Helpers/OutcomeFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_observed_eq_potential (L77)` | outcomeFactorization_conditionalMean_observed_eq_potential | unmatched |  |
| outcomeFactorization_conditionalMean_observed_latentCell | lemma | `Helpers/OutcomeFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_observed_latentCell (L95)` | outcomeFactorization_conditionalMean_observed_latentCell | unmatched |  |
| outcomeFactorization_conditionalMean_target_mul_observed | lemma | `Helpers/OutcomeFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_target_mul_observed (L108)` | outcomeFactorization_conditionalMean_target_mul_observed | unmatched |  |
| outcomeFactorization_conditionalMean_targetOutcome_latentCell | lemma | `Helpers/OutcomeFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_targetOutcome_latentCell (L183)` | outcomeFactorization_conditionalMean_targetOutcome_latentCell | unmatched |  |
| outcomeFactorization_conditionalMean_reference_targetOutcome | lemma | `Helpers/OutcomeFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_reference_targetOutcome (L197)` | outcomeFactorization_conditionalMean_reference_targetOutcome | unmatched |  |
| outcomeFactorization_latentCell_outcomeProxy | lemma | `Helpers/OutcomeFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.latentCell_outcomeProxy_factorization (L235)` | outcomeFactorization_latentCell_outcomeProxy | unmatched |  |
| outcomeFactorization_observedOutcomeProxyMoment | lemma | `Helpers/OutcomeFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.observedOutcomeProxyMoment_factorization (L253)` | outcomeFactorization_observedOutcomeProxyMoment | unmatched |  |
| empSummary_measurable | lemma | `TCollisionUniformRootN.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.empSummary_measurable (L13)` | empSummary_measurable | unmatched |  |
| ambientOperatorBridge_targetFeature_transpose_firstBasis | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.targetFeature_transpose_firstBasis (L343)` | ambientOperatorBridge_targetFeature_transpose_firstBasis | unmatched |  |
| ambientOperatorBridge_moorePenroseInverse_mul_eq_one_of_injective | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.moorePenroseInverse_mul_eq_one_of_injective (L147)` | ambientOperatorBridge_moorePenroseInverse_mul_eq_one_of_injective | unmatched |  |
| ambientOperatorBridge_moorePenroseInverse_mul_transpose | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.moorePenroseInverse_mul_transpose (L166)` | ambientOperatorBridge_moorePenroseInverse_mul_transpose | unmatched |  |
| ambientOperatorBridge_moorePenrose_outcome_factorization | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.moorePenrose_outcome_factorization (L206)` | ambientOperatorBridge_moorePenrose_outcome_factorization | unmatched |  |
| ambientOperatorBridge_model_ambientEffectOperator_factorization | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.model_ambientEffectOperator_factorization (L221)` | ambientOperatorBridge_model_ambientEffectOperator_factorization | unmatched |  |
| ambientOperatorBridge_obsSummary_mX_factorization | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.obsSummary_mX_factorization (L388)` | ambientOperatorBridge_obsSummary_mX_factorization | unmatched |  |
| ambientOperatorBridge_represents_raw_quotientLaw | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.represents_raw_quotientLaw (L447)` | ambientOperatorBridge_represents_raw_quotientLaw | unmatched |  |
| ambientOperatorBridge_model_represents_raw_quotientLaw | lemma | `Helpers/AmbientOperatorBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientOperatorBridge.model_represents_raw_quotientLaw (L498)` | ambientOperatorBridge_model_represents_raw_quotientLaw | unmatched |  |
| realDiagonalizationBridge_basisMatrix | definition | `Helpers/RealDiagonalizationBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.basisMatrix (L65)` | realDiagonalizationBridge_basisMatrix | unmatched |  |
| realDiagonalizationBridge_basisInvMatrix | definition | `Helpers/RealDiagonalizationBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.basisInvMatrix (L71)` | realDiagonalizationBridge_basisInvMatrix | unmatched |  |
| realDiagonalizationBridge_basisMatrix_mul_inv | lemma | `Helpers/RealDiagonalizationBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.basisMatrix_mul_inv (L77)` | realDiagonalizationBridge_basisMatrix_mul_inv | unmatched |  |
| realDiagonalizationBridge_basisInvMatrix_mul_basis | lemma | `Helpers/RealDiagonalizationBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.basisInvMatrix_mul_basis (L99)` | realDiagonalizationBridge_basisInvMatrix_mul_basis | unmatched |  |
| realDiagonalizationBridge_ofEigenbasis | definition | `Helpers/RealDiagonalizationBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.realDiagonalizationOfEigenbasis (L115)` | realDiagonalizationBridge_ofEigenbasis | unmatched |  |
| realDiagonalizationBridge_applyFunction | lemma | `Helpers/RealDiagonalizationBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.realDiagonalizationOfEigenbasis_applyFunction (L141)` | realDiagonalizationBridge_applyFunction | unmatched |  |
| realDiagonalizationBridge_applyFunction_eq_of_apply_basis | lemma | `Helpers/RealDiagonalizationBridge.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.realDiagonalizationOfEigenbasis_applyFunction_eq_of_apply_basis (L151)` | realDiagonalizationBridge_applyFunction_eq_of_apply_basis | unmatched |  |
| realDiagonalizationBridge_signalBasis_extension | lemma | `(none)` | realDiagonalizationBridge_signalBasis_extension | unmatched |  |
| realDiagonalizationBridge_signalBasis_fin_extension | lemma | `(none)` | realDiagonalizationBridge_signalBasis_fin_extension | unmatched |  |
| modelRealDiagonalization_thinSignalFactorization | definition | `Helpers/ModelRealDiagonalization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ThinSignalFactorization (L19)` | modelRealDiagonalization_thinSignalFactorization | unmatched |  |
| modelRealDiagonalization_thinSignalFactorization_construct | definition | `Helpers/ModelRealDiagonalization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.thinSignalFactorization (L29)` | modelRealDiagonalization_thinSignalFactorization_construct | unmatched |  |
| modelRealDiagonalization_signalBasis_transpose_mul_self | lemma | `(none)` | modelRealDiagonalization_signalBasis_transpose_mul_self | unmatched |  |
| modelRealDiagonalization_forward | definition | `(none)` | modelRealDiagonalization_forward | unmatched |  |
| modelRealDiagonalization_backward | definition | `(none)` | modelRealDiagonalization_backward | unmatched |  |
| modelRealDiagonalization_forward_mul_backward | lemma | `(none)` | modelRealDiagonalization_forward_mul_backward | unmatched |  |
| modelRealDiagonalization_backward_mul_forward | lemma | `(none)` | modelRealDiagonalization_backward_mul_forward | unmatched |  |
| modelRealDiagonalization_linearEquiv | definition | `(none)` | modelRealDiagonalization_linearEquiv | unmatched |  |
| gapFreeClosureAssembly_atomicLawBorelSpace | definition | `Helpers/GapFreeClosureAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapFreeClosureAssembly.atomicLawBorelSpace (L13)` | gapFreeClosureAssembly_atomicLawBorelSpace | unmatched |  |
| gapFreeClosureAssembly_atomicLawPolishSpace | definition | `Helpers/GapFreeClosureAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapFreeClosureAssembly.atomicLawPolishSpace (L21)` | gapFreeClosureAssembly_atomicLawPolishSpace | unmatched |  |
| gapFreeClosureAssembly_probabilityLawPolishSpace | definition | `Helpers/GapFreeClosureAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapFreeClosureAssembly.probabilityLawPolishSpace (L27)` | gapFreeClosureAssembly_probabilityLawPolishSpace | unmatched |  |
| gapFreeClosureAssembly_lawModuloOpensMeasurableSpace | definition | `Helpers/GapFreeClosureAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapFreeClosureAssembly.lawModuloOpensMeasurableSpace (L33)` | gapFreeClosureAssembly_lawModuloOpensMeasurableSpace | unmatched |  |
| gapFreeClosureAssembly_lawModuloBorelSpace | definition | `Helpers/GapFreeClosureAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapFreeClosureAssembly.lawModuloBorelSpace (L50)` | gapFreeClosureAssembly_lawModuloBorelSpace | unmatched |  |
| gapFreeClosureAssembly_exists_unique_extension_with_control | lemma | `Helpers/GapFreeClosureAssembly.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.GapFreeClosureAssembly.exists_unique_extension_with_control (L60)` | gapFreeClosureAssembly_exists_unique_extension_with_control | unmatched |  |
| modelRealDiagonalization_targetFeature_entry_bound | lemma | `Helpers/ModelSpectralCertificate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.targetFeature_entry_bound (L16)` | modelRealDiagonalization_targetFeature_entry_bound | unmatched |  |
| modelRealDiagonalization_model_certificate | lemma | `Helpers/ModelSpectralCertificate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.model_realDiagonalization_certificate (L45)` | modelRealDiagonalization_model_certificate | unmatched |  |
| modelRealDiagonalization_AmbientExtension | definition | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AmbientExtension (L15)` | modelRealDiagonalization_AmbientExtension | unmatched |  |
| modelRealDiagonalization_ambientExtension | definition | `(none)` | modelRealDiagonalization_ambientExtension | unmatched |  |
| modelRealDiagonalization_ambientEigenvalue | definition | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ambientEigenvalue (L31)` | modelRealDiagonalization_ambientEigenvalue | unmatched |  |
| modelRealDiagonalization_ambientEigenvalue_signal | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ambientEigenvalue_signal (L38)` | modelRealDiagonalization_ambientEigenvalue_signal | unmatched |  |
| modelRealDiagonalization_ambientEigenvalue_nonsignal | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ambientEigenvalue_nonsignal (L46)` | modelRealDiagonalization_ambientEigenvalue_nonsignal | unmatched |  |
| modelRealDiagonalization_eigenbasis | definition | `(none)` | modelRealDiagonalization_eigenbasis | unmatched |  |
| modelRealDiagonalization_forward_signal | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.forward_signal (L61)` | modelRealDiagonalization_forward_signal | unmatched |  |
| modelRealDiagonalization_factorOperator | definition | `(none)` | modelRealDiagonalization_factorOperator | unmatched |  |
| modelRealDiagonalization_factorOperator_mul_signalEigenvectors | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.factorOperator_mul_signalEigenvectors (L86)` | modelRealDiagonalization_factorOperator_mul_signalEigenvectors | unmatched |  |
| modelRealDiagonalization_transpose_mul_ambientBasis_nonsignal | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.transpose_mul_ambientBasis_nonsignal (L102)` | modelRealDiagonalization_transpose_mul_ambientBasis_nonsignal | unmatched |  |
| modelRealDiagonalization_forward_ambientBasis_nonsignal | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.forward_ambientBasis_nonsignal (L117)` | modelRealDiagonalization_forward_ambientBasis_nonsignal | unmatched |  |
| modelRealDiagonalization_factorOperator_eigenbasis | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.factorOperator_eigenbasis (L140)` | modelRealDiagonalization_factorOperator_eigenbasis | unmatched |  |
| modelRealDiagonalization_realDiagonalization | definition | `(none)` | modelRealDiagonalization_realDiagonalization | unmatched |  |
| modelRealDiagonalization_ambientEigenvalue_comp | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ambientEigenvalue_comp (L193)` | modelRealDiagonalization_ambientEigenvalue_comp | unmatched |  |
| modelRealDiagonalization_applyFunction | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.realDiagonalization_applyFunction (L204)` | modelRealDiagonalization_applyFunction | unmatched |  |
| modelRealDiagonalization_moorePenroseInverse_thinSignalFactorization | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.moorePenroseInverse_thinSignalFactorization (L215)` | modelRealDiagonalization_moorePenroseInverse_thinSignalFactorization | unmatched |  |
| modelRealDiagonalization_factorOperator_eq_moorePenrose | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.factorOperator_eq_moorePenrose (L254)` | modelRealDiagonalization_factorOperator_eq_moorePenrose | unmatched |  |
| modelRealDiagonalization_applyFunction_moorePenrose | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.realDiagonalization_applyFunction_moorePenrose (L273)` | modelRealDiagonalization_applyFunction_moorePenrose | unmatched |  |
| modelRealDiagonalization_eucNorm_le_card_mul_bound | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.eucNorm_le_card_mul_bound (L283)` | modelRealDiagonalization_eucNorm_le_card_mul_bound | unmatched |  |
| modelRealDiagonalization_entryNormConstant | definition | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.entryNormConstant (L301)` | modelRealDiagonalization_entryNormConstant | unmatched |  |
| modelRealDiagonalization_entryNormConstant_nonneg | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.entryNormConstant_nonneg (L308)` | modelRealDiagonalization_entryNormConstant_nonneg | unmatched |  |
| modelRealDiagonalization_matrixNorm_le_entryBound | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.matrixNorm_le_entryBound (L314)` | modelRealDiagonalization_matrixNorm_le_entryBound | unmatched |  |
| modelRealDiagonalization_orthonormalBasis_entry_abs_le_one | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.orthonormalBasis_entry_abs_le_one (L330)` | modelRealDiagonalization_orthonormalBasis_entry_abs_le_one | unmatched |  |
| modelRealDiagonalization_signalBasis_entry_abs_le_one | lemma | `(none)` | modelRealDiagonalization_signalBasis_entry_abs_le_one | unmatched |  |
| modelRealDiagonalization_coord_entry_bound | lemma | `(none)` | modelRealDiagonalization_coord_entry_bound | unmatched |  |
| modelRealDiagonalization_forward_norm_bound | lemma | `(none)` | modelRealDiagonalization_forward_norm_bound | unmatched |  |
| modelRealDiagonalization_backward_norm_bound | lemma | `(none)` | modelRealDiagonalization_backward_norm_bound | unmatched |  |
| modelRealDiagonalization_conditionBound | definition | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionBound (L469)` | modelRealDiagonalization_conditionBound | unmatched |  |
| modelRealDiagonalization_conditionBound_nonneg | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionBound_nonneg (L480)` | modelRealDiagonalization_conditionBound_nonneg | unmatched |  |
| modelRealDiagonalization_conditionNumber_le | lemma | `(none)` | modelRealDiagonalization_conditionNumber_le | unmatched |  |
| modelRealDiagonalization_singularSystem_right_entry_abs_le_one | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.singularSystem_right_entry_abs_le_one (L586)` | modelRealDiagonalization_singularSystem_right_entry_abs_le_one | unmatched |  |
| modelRealDiagonalization_constructed_coordInv_entry_bound | lemma | `Helpers/ModelSpectralConstruction.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.thinSignalFactorization_coordInv_entry_bound (L601)` | modelRealDiagonalization_constructed_coordInv_entry_bound | unmatched |  |
| summaryMetric_toCoordinates_injective | lemma | `(none)` | summaryMetric_toCoordinates_injective | unmatched |  |
| summaryMetric_coordinates | definition | `Helpers/SummaryMetric.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.SummaryMetricCoordinates (L19)` | summaryMetric_coordinates | unmatched |  |
| summaryMetric_toMetricCoordinates | definition | `(none)` | summaryMetric_toMetricCoordinates | unmatched |  |
| summaryMetric_toMetricCoordinates_injective | lemma | `(none)` | summaryMetric_toMetricCoordinates_injective | unmatched |  |
| summaryMetric_fromMetricCoordinates | definition | `Helpers/SummaryMetric.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.fromMetricCoordinates (L54)` | summaryMetric_fromMetricCoordinates | unmatched |  |
| summaryMetric_toMetricCoordinates_continuous | lemma | `(none)` | summaryMetric_toMetricCoordinates_continuous | unmatched |  |
| summaryMetric_fromMetricCoordinates_continuous | lemma | `Helpers/SummaryMetric.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.fromMetricCoordinates_continuous (L82)` | summaryMetric_fromMetricCoordinates_continuous | unmatched |  |
| summaryMetric_from_toMetricCoordinates | lemma | `Helpers/SummaryMetric.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.from_toMetricCoordinates (L89)` | summaryMetric_from_toMetricCoordinates | unmatched |  |
| summaryMetric_metricSpace | definition | `Helpers/SummaryMetric.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryMetricSpace (L95)` | summaryMetric_metricSpace | unmatched |  |
| summaryMetric_dS_self | lemma | `Helpers/SummaryMetric.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.dS_self (L126)` | summaryMetric_dS_self | unmatched |  |
| summaryMetric_dS_le_dist | lemma | `Helpers/SummaryMetric.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.dS_le_dist_mul (L135)` | summaryMetric_dS_le_dist | unmatched |  |
| honestConfidence_latentClass_real_eq_sum_cells | lemma | `THonestRootNConfidence.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.latentClass_real_eq_sum_cells (L14)` | honestConfidence_latentClass_real_eq_sum_cells | unmatched |  |
| honestConfidence_latentMass_two_pi0 | lemma | `THonestRootNConfidence.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.latentMass_two_pi0_le (L30)` | honestConfidence_latentMass_two_pi0 | unmatched |  |
| honestConfidence_atomFloor_of_measureEquivalent | lemma | `(none)` | honestConfidence_atomFloor_of_measureEquivalent | unmatched |  |
| honestConfidence_quotient_atomFloor | lemma | `THonestRootNConfidence.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.quotientLaw_atomFloor (L63)` | honestConfidence_quotient_atomFloor | unmatched |  |
| honestConfidence_summaryRepair_with_modulus | lemma | `THonestRootNConfidence.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryRepair_with_modulus (L90)` | honestConfidence_summaryRepair_with_modulus | unmatched |  |
| ass:model-core-domain | assumption | `(none)` | ass:model-core-domain | unmatched |  |
| aux_DiagonalizedOperator | definition | `Helpers/QuotientFunctionalCalculus.lean:DiagonalizedOperator (L22)` | aux_DiagonalizedOperator | unmatched |  |
| aux_quotientLaw | definition | `Helpers/QuotientFunctionalCalculus.lean:quotientLaw (L105)` | aux_quotientLaw | unmatched |  |
| quotientLawRaw_valid | lemma | `Helpers/QuotientLaw.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.quotientLawRaw_valid (L14)` | quotientLawRaw_valid | unmatched |  |
| aux_exactRealSpectralRun | definition | `Helpers/LatticeEstimator.lean:exactRealSpectralRun (L434)` | aux_exactRealSpectralRun | unmatched |  |
| aux_ExactRealSpectralRun | definition | `Helpers/LatticeEstimator.lean:ExactRealSpectralRun (L355)` | aux_ExactRealSpectralRun | unmatched |  |
| aux_linked | definition | `Helpers/Inference.lean:linked (L100)` | aux_linked | unmatched |  |
| aux_netExactRealProgram | definition | `Helpers/LatticeEstimator.lean:netExactRealProgram (L462)` | aux_netExactRealProgram | unmatched |  |
| aux_NetProgramResult | definition | `Helpers/LatticeEstimator.lean:NetProgramResult (L453)` | aux_NetProgramResult | unmatched |  |
| aux_netSearchTrace | definition | `Helpers/LatticeEstimator.lean:netSearchTrace (L446)` | aux_netSearchTrace | unmatched |  |
| aux_netSummaryTrace | definition | `Helpers/LatticeEstimator.lean:netSummaryTrace (L441)` | aux_netSummaryTrace | unmatched |  |
| aux_ExactRealPrimitives | definition | `Helpers/LatticeEstimator.lean:ExactRealPrimitives (L371)` | aux_ExactRealPrimitives | unmatched |  |
| aux_RootIsolationMassExecution | definition | `Helpers/LatticeEstimator.lean:RootIsolationMassExecution (L339)` | aux_RootIsolationMassExecution | unmatched |  |
| aux_ThresholdedSignalExecution | definition | `Helpers/LatticeEstimator.lean:ThresholdedSignalExecution (L325)` | aux_ThresholdedSignalExecution | unmatched |  |
| summaryClosure_injective_of_signalMinSingular_pos | lemma | `Helpers/SummaryClosure.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryClosure_injective_of_signalMinSingular_pos (L435)` | summaryClosure_injective_of_signalMinSingular_pos | unmatched |  |
| summaryClosure_gram_det_isUnit_of_injective | lemma | `Helpers/SummaryClosure.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryClosure_gram_det_isUnit_of_injective (L446)` | summaryClosure_gram_det_isUnit_of_injective | unmatched |  |
| summaryClosure_penrose_left_inverse_of_injective | lemma | `Helpers/SummaryClosure.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryClosure_penrose_left_inverse_of_injective (L473)` | summaryClosure_penrose_left_inverse_of_injective | unmatched |  |
| publishedMomentIdentity_targetFeature_transpose_firstBasis | lemma | `Helpers/SummaryClosure.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.publishedMomentIdentity_targetFeature_transpose_firstBasis (L53)` | publishedMomentIdentity_targetFeature_transpose_firstBasis | unmatched |  |
| publishedMomentIdentity_obsSummary_mX_factorization | lemma | `Helpers/SummaryClosure.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.publishedMomentIdentity_obsSummary_mX_factorization (L87)` | publishedMomentIdentity_obsSummary_mX_factorization | unmatched |  |
| publishedMomentIdentity_injective_of_signalMinSingular_pos | lemma | `Helpers/SummaryClosure.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.publishedMomentIdentity_injective_of_signalMinSingular_pos (L144)` | publishedMomentIdentity_injective_of_signalMinSingular_pos | unmatched |  |
| publishedMomentIdentity_gram_det_isUnit_of_injective | lemma | `Helpers/SummaryClosure.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.publishedMomentIdentity_gram_det_isUnit_of_injective (L155)` | publishedMomentIdentity_gram_det_isUnit_of_injective | unmatched |  |
| publishedMomentIdentity_penrose_left_inverse_of_injective | lemma | `Helpers/SummaryClosure.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.publishedMomentIdentity_penrose_left_inverse_of_injective (L182)` | publishedMomentIdentity_penrose_left_inverse_of_injective | unmatched |  |
| publishedVMWConverseTransfer_gapStratum_separated | lemma | `TPublishedVMWConverseTransfer.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.gapStratum_publishedSpectralSeparation (L35)` | publishedVMWConverseTransfer_gapStratum_separated | unmatched |  |
| SummaryCoord | definition | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.SummaryCoord (L16)` | SummaryCoord | unmatched |  |
| summaryCoordStat | definition | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryCoordStat (L28)` | summaryCoordStat | unmatched |  |
| summaryCoordScale | definition | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryCoordScale (L36)` | summaryCoordScale | unmatched |  |
| product_hoeffding | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.product_hoeffding (L43)` | product_hoeffding | unmatched |  |
| summaryCoordStat_measurable | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryCoordStat_measurable (L75)` | summaryCoordStat_measurable | unmatched |  |
| summaryCoordStat_ae_bound | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryCoordStat_ae_bound (L101)` | summaryCoordStat_ae_bound | unmatched |  |
| summaryCoordStat_integral | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryCoordStat_integral (L135)` | summaryCoordStat_integral | unmatched |  |
| summaryCoordStat_arm_sampleMean | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryCoordStat_arm_sampleMean (L187)` | summaryCoordStat_arm_sampleMean | unmatched |  |
| summaryCoordStat_matrix_sampleMean | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryCoordStat_matrix_sampleMean (L202)` | summaryCoordStat_matrix_sampleMean | unmatched |  |
| populationArmCoord | definition | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.populationArmCoord (L211)` | populationArmCoord | unmatched |  |
| empiricalArmMatrix_entry_error | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.empiricalArmMatrix_entry_error (L219)` | empiricalArmMatrix_entry_error | unmatched |  |
| empSummary_error_of_small_deviations | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.empSummary_error_of_small_deviations (L304)` | empSummary_error_of_small_deviations | unmatched |  |
| abs_fin_average_le | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.abs_fin_average_le (L371)` | abs_fin_average_le | unmatched |  |
| empiricalArmMatrix_entry_bound | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.empiricalArmMatrix_entry_bound (L390)` | empiricalArmMatrix_entry_bound | unmatched |  |
| empSummary_error_on_support | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.empSummary_error_on_support (L433)` | empSummary_error_on_support | unmatched |  |
| measurableSet_summaryCoordSupport | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurableSet_summaryCoordSupport (L519)` | measurableSet_summaryCoordSupport | unmatched |  |
| sample_summaryCoordSupport_ae | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.sample_summaryCoordSupport_ae (L528)` | sample_summaryCoordSupport_ae | unmatched |  |
| summaryCoord_deviation_probability | lemma | `Helpers/ConcentrationCore.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryCoord_deviation_probability (L561)` | summaryCoord_deviation_probability | unmatched |  |
| pathWeight_zero | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathWeight_zero (L15)` | pathWeight_zero | unmatched |  |
| pathLaw_zero | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathLaw_zero (L25)` | pathLaw_zero | unmatched |  |
| pathLaw_zero_ucvmwModel | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathLaw_zero_ucvmwModel (L31)` | pathLaw_zero_ucvmwModel | unmatched |  |
| pathWeight_nonneg | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathWeight_nonneg (L45)` | pathWeight_nonneg | unmatched |  |
| pathWeight_sum_nuisance | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathWeight_sum_nuisance (L103)` | pathWeight_sum_nuisance | unmatched |  |
| pathLaw_real | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathLaw_real (L111)` | pathLaw_real | unmatched |  |
| pathObsPoint | definition | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathObsPoint (L134)` | pathObsPoint | unmatched |  |
| pathObsIndicator | definition | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathObsIndicator (L139)` | pathObsIndicator | unmatched |  |
| measurableSet_singleton_obs | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.measurableSet_singleton_obs (L145)` | measurableSet_singleton_obs | unmatched |  |
| pathObservedCellMass_formula | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathObservedCellMass_formula (L166)` | pathObservedCellMass_formula | unmatched |  |
| pathVisibleMass | definition | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleMass (L179)` | pathVisibleMass | unmatched |  |
| pathVisibleMass_diff_formula | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleMass_diff_formula (L188)` | pathVisibleMass_diff_formula | unmatched |  |
| pathVisibleMass_diff_bound | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleMass_diff_bound (L242)` | pathVisibleMass_diff_bound | unmatched |  |
| pathObservedCellMass_visible_formula | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathObservedCellMass_visible_formula (L258)` | pathObservedCellMass_visible_formula | unmatched |  |
| pathObservedCellMass_diff_bound | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathObservedCellMass_diff_bound (L306)` | pathObservedCellMass_diff_bound | unmatched |  |
| pathVisibleMass_base_floor | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleMass_base_floor (L360)` | pathVisibleMass_base_floor | unmatched |  |
| pathObservedCellMass_base_floor | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathObservedCellMass_base_floor (L371)` | pathObservedCellMass_base_floor | unmatched |  |
| path_sum_restrict_latentClass | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_sum_restrict_latentClass (L416)` | path_sum_restrict_latentClass | unmatched |  |
| path_latentMass | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_latentMass (L438)` | path_latentMass | unmatched |  |
| path_latentMass_l1_displacement | lemma | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_latentMass_l1_displacement (L450)` | path_latentMass_l1_displacement | unmatched |  |
| path_sum_restrict_latentCell | lemma | `Helpers/PathFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_sum_restrict_latentCell (L14)` | path_sum_restrict_latentCell | unmatched |  |
| integral_pathLaw_restrict | lemma | `Helpers/PathFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.integral_pathLaw_restrict (L43)` | integral_pathLaw_restrict | unmatched |  |
| conditionalMean_path_latentCell | lemma | `Helpers/PathFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_path_latentCell (L65)` | conditionalMean_path_latentCell | unmatched |  |
| conditionalMean_path_latentClass | lemma | `Helpers/PathFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.conditionalMean_path_latentClass (L82)` | conditionalMean_path_latentClass | unmatched |  |
| path_referenceProxySeparation | lemma | `Helpers/PathFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_referenceProxySeparation (L102)` | path_referenceProxySeparation | unmatched |  |
| path_targetProxySeparation | lemma | `Helpers/PathFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_targetProxySeparation (L129)` | path_targetProxySeparation | unmatched |  |
| path_armwiseLatentIgnorability | lemma | `Helpers/PathFactorization.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_armwiseLatentIgnorability (L156)` | path_armwiseLatentIgnorability | unmatched |  |
| klDiv_le_chiSqDiv | lemma | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.klDiv_le_chiSqDiv (L14)` | klDiv_le_chiSqDiv | unmatched |  |
| PathVisibleCell | definition | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.PathVisibleCell (L37)` | PathVisibleCell | unmatched |  |
| pathVisibleCoefficient | definition | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleCoefficient (L41)` | pathVisibleCoefficient | unmatched |  |
| pathVisibleLaw | definition | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleLaw (L49)` | pathVisibleLaw | unmatched |  |
| pathVisibleLaw_singleton | lemma | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleLaw_singleton (L55)` | pathVisibleLaw_singleton | unmatched |  |
| pathVisibleLaw_map | lemma | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleLaw_map (L84)` | pathVisibleLaw_map | unmatched |  |
| pathVisibleLaw_isProbabilityMeasure | lemma | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleLaw_isProbabilityMeasure (L108)` | pathVisibleLaw_isProbabilityMeasure | unmatched |  |
| pathVisibleLaw_base_floor | lemma | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleLaw_base_floor (L122)` | pathVisibleLaw_base_floor | unmatched |  |
| pathVisibleLaw_absolutelyContinuous | lemma | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleLaw_absolutelyContinuous (L130)` | pathVisibleLaw_absolutelyContinuous | unmatched |  |
| pathVisibleLaw_chiSqDiv_bound | lemma | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathVisibleLaw_chiSqDiv_bound (L190)` | pathVisibleLaw_chiSqDiv_bound | unmatched |  |
| pathLaw_observed_kl_bound | lemma | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathLaw_observed_kl_bound (L265)` | pathLaw_observed_kl_bound | unmatched |  |
| ae_pathLaw_of_points | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.ae_pathLaw_of_points (L15)` | ae_pathLaw_of_points | unmatched |  |
| path_consistency | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_consistency (L162)` | path_consistency | unmatched |  |
| path_anchor | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_anchor (L170)` | path_anchor | unmatched |  |
| path_boundedX | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_boundedX (L178)` | path_boundedX | unmatched |  |
| path_boundedProxyProduct | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_boundedProxyProduct (L187)` | path_boundedProxyProduct | unmatched |  |
| path_boundedOutcomeProxyProduct | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_boundedOutcomeProxyProduct (L196)` | path_boundedOutcomeProxyProduct | unmatched |  |
| path_latentCell_mass | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_latentCell_mass (L219)` | path_latentCell_mass | unmatched |  |
| path_latentArmPositivity | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_latentArmPositivity (L243)` | path_latentArmPositivity | unmatched |  |
| pathReferenceFeature_first_formula | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathReferenceFeature_first_formula (L30)` | pathReferenceFeature_first_formula | unmatched |  |
| path_targetFeature | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_targetFeature (L84)` | path_targetFeature | unmatched |  |
| path_referenceFeature | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_referenceFeature (L109)` | path_referenceFeature | unmatched |  |
| path_lowerRight_opNorm | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_lowerRight_opNorm (L254)` | path_lowerRight_opNorm | unmatched |  |
| path_lowerLeft_opNorm | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_lowerLeft_opNorm (L269)` | path_lowerLeft_opNorm | unmatched |  |
| pathTargetFeature_zero_strictRank | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathTargetFeature_zero_strictRank (L284)` | pathTargetFeature_zero_strictRank | unmatched |  |
| pathTargetFeature_entry_displacement | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathTargetFeature_entry_displacement (L294)` | pathTargetFeature_entry_displacement | unmatched |  |
| pathTargetFeature_rankMargin | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathTargetFeature_rankMargin (L316)` | pathTargetFeature_rankMargin | unmatched |  |
| baseReferenceFeature_strictRank | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.baseReferenceFeature_strictRank (L336)` | baseReferenceFeature_strictRank | unmatched |  |
| pathReferenceFeature_entry_displacement | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathReferenceFeature_entry_displacement (L349)` | pathReferenceFeature_entry_displacement | unmatched |  |
| pathReferenceFeature_rankMargin | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathReferenceFeature_rankMargin (L391)` | pathReferenceFeature_rankMargin | unmatched |  |
| path_proxyRankMargin | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_proxyRankMargin (L415)` | path_proxyRankMargin | unmatched |  |
| path_ucvmwModel | lemma | `Helpers/PathModelCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_ucvmwModel (L429)` | path_ucvmwModel | unmatched |  |
| pathBernoulli_mean | lemma | `Helpers/PathLocalExperiments.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathBernoulli_mean (L13)` | pathBernoulli_mean | unmatched |  |
| pathBernoulli_sum_mul | lemma | `Helpers/PathLocalExperiments.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathBernoulli_sum_mul (L19)` | pathBernoulli_sum_mul | unmatched |  |
| path_latentMean | lemma | `Helpers/PathLocalExperiments.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_latentMean (L28)` | path_latentMean | unmatched |  |
| path_latentEffect | lemma | `Helpers/PathLocalExperiments.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_latentEffect (L56)` | path_latentEffect | unmatched |  |
| path_effectGap | lemma | `Helpers/PathLocalExperiments.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_effectGap (L66)` | path_effectGap | unmatched |  |
| path_distinctEffects | lemma | `Helpers/PathLocalExperiments.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_distinctEffects (L104)` | path_distinctEffects | unmatched |  |
| path_gapStratum | lemma | `Helpers/PathLocalExperiments.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_gapStratum (L119)` | path_gapStratum | unmatched |  |
| path_localWeightExperiment | lemma | `Helpers/PathLocalExperiments.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_localWeightExperiment (L141)` | path_localWeightExperiment | unmatched |  |
| atomicLaw_borelSpace | definition | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.atomicLaw_borelSpace (L13)` | atomicLaw_borelSpace | unmatched |  |
| lawModulo_opensMeasurableSpace | definition | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.lawModulo_opensMeasurableSpace (L31)` | lawModulo_opensMeasurableSpace | unmatched |  |
| witnessVisibleLaw | definition | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessVisibleLaw (L42)` | witnessVisibleLaw | unmatched |  |
| witnessVisibleLaw_map | lemma | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessVisibleLaw_map (L47)` | witnessVisibleLaw_map | unmatched |  |
| witnessVisibleLaw_isProbabilityMeasure | lemma | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessVisibleLaw_isProbabilityMeasure (L60)` | witnessVisibleLaw_isProbabilityMeasure | unmatched |  |
| witnessVisibleLaw_singleton_diff_bound | lemma | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessVisibleLaw_singleton_diff_bound (L70)` | witnessVisibleLaw_singleton_diff_bound | unmatched |  |
| witnessVisibleLaw_base_floor | lemma | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessVisibleLaw_base_floor (L88)` | witnessVisibleLaw_base_floor | unmatched |  |
| witnessVisibleLaw_absolutelyContinuous | lemma | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessVisibleLaw_absolutelyContinuous (L96)` | witnessVisibleLaw_absolutelyContinuous | unmatched |  |
| witnessVisibleLaw_chiSqDiv_bound | lemma | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessVisibleLaw_chiSqDiv_bound (L148)` | witnessVisibleLaw_chiSqDiv_bound | unmatched |  |
| witnessLaw_observed_kl_bound | lemma | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessLaw_observed_kl_bound (L218)` | witnessLaw_observed_kl_bound | unmatched |  |
| witness_localQuotientExperiment | lemma | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_localQuotientExperiment (L241)` | witness_localQuotientExperiment | unmatched |  |
| witness_quotientLaw_wass1 | lemma | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witness_quotientLaw_wass1 (L258)` | witness_quotientLaw_wass1 | unmatched |  |
| pathObsLaw_absolutelyContinuous | lemma | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathObsLaw_absolutelyContinuous (L149)` | pathObsLaw_absolutelyContinuous | unmatched |  |
| pathObsLaw_llr_integrable | lemma | `Helpers/PathKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathObsLaw_llr_integrable (L167)` | pathObsLaw_llr_integrable | unmatched |  |
| witnessObsLaw_absolutelyContinuous | lemma | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessObsLaw_absolutelyContinuous (L115)` | witnessObsLaw_absolutelyContinuous | unmatched |  |
| witnessObsLaw_llr_integrable | lemma | `Helpers/WitnessKL.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.witnessObsLaw_llr_integrable (L129)` | witnessObsLaw_llr_integrable | unmatched |  |
| eventProbability_mul_threshold_le_risk | lemma | `TMatchingLocalLowerBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.eventProbability_mul_threshold_le_risk (L19)` | eventProbability_mul_threshold_le_risk | unmatched |  |
| compactMetric_distance_integrable | lemma | `TMatchingLocalLowerBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.compactMetric_distance_integrable (L42)` | compactMetric_distance_integrable | unmatched |  |
| twoPoint_expectedMetricRisk_lower | lemma | `TMatchingLocalLowerBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.twoPoint_expectedMetricRisk_lower (L55)` | twoPoint_expectedMetricRisk_lower | unmatched |  |
| simplexWeightLoss_integrable | lemma | `TMatchingLocalLowerBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.simplexWeightLoss_integrable (L109)` | simplexWeightLoss_integrable | unmatched |  |
| twoPoint_expectedWeightRisk_lower | lemma | `TMatchingLocalLowerBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.twoPoint_expectedWeightRisk_lower (L129)` | twoPoint_expectedWeightRisk_lower | unmatched |  |
| path_orderedMasses_eq_latentMass | lemma | `TMatchingLocalLowerBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_orderedMasses_eq_latentMass (L175)` | path_orderedMasses_eq_latentMass | unmatched |  |
| path_orderedMasses_inSimplex | lemma | `TMatchingLocalLowerBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.path_orderedMasses_inSimplex (L230)` | path_orderedMasses_inSimplex | unmatched |  |
| calibratedDisplacement_sample_signal_sq_le | lemma | `TMatchingLocalLowerBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.calibratedDisplacement_sample_signal_sq_le (L246)` | calibratedDisplacement_sample_signal_sq_le | unmatched |  |
| orderedMasses_measurable | lemma | `Helpers/Risk.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.orderedMasses_measurable (L30)` | orderedMasses_measurable | unmatched |  |
| orderedMasses_inSimplex | lemma | `Helpers/Risk.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.orderedMasses_inSimplex (L107)` | orderedMasses_inSimplex | unmatched |  |
| simplex_l1_le_two | lemma | `Helpers/Risk.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.simplex_l1_le_two (L156)` | simplex_l1_le_two | unmatched |  |
| cluster_effectGap_nonneg | lemma | `Helpers/ClusterBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_effectGap_nonneg (L10)` | cluster_effectGap_nonneg | unmatched |  |
| cluster_effectGap_le_support_distance | lemma | `Helpers/ClusterBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_effectGap_le_support_distance (L20)` | cluster_effectGap_le_support_distance | unmatched |  |
| cluster_effectGap_le_externalGap | lemma | `Helpers/ClusterBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_effectGap_le_externalGap (L48)` | cluster_effectGap_le_externalGap | unmatched |  |
| cluster_effectGap_toReal_pos_of_external_ne_top | lemma | `Helpers/ClusterBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_effectGap_toReal_pos_of_external_ne_top (L70)` | cluster_effectGap_toReal_pos_of_external_ne_top | unmatched |  |
| cluster_singleton_width_from_external | lemma | `Helpers/ClusterBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_singleton_width_from_external (L136)` | cluster_singleton_width_from_external | unmatched |  |
| clusterMass_mem_unitInterval | lemma | `Helpers/ClusterBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.clusterMass_mem_unitInterval (L173)` | clusterMass_mem_unitInterval | unmatched |  |
| clusterMass_eq_one_of_support_subset | lemma | `Helpers/ClusterBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.clusterMass_eq_one_of_support_subset (L190)` | clusterMass_eq_one_of_support_subset | unmatched |  |
| cluster_mass_gap_cost | lemma | `Helpers/ClusterBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_mass_gap_cost (L207)` | cluster_mass_gap_cost | unmatched |  |
| cluster_candidate_mass_error | lemma | `Helpers/ClusterBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_candidate_mass_error (L320)` | cluster_candidate_mass_error | unmatched |  |
| cluster_deterministic_report | lemma | `Helpers/ClusterBounds.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_deterministic_report (L485)` | cluster_deterministic_report | unmatched |  |
| cluster_support_nonempty | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_support_nonempty (L9)` | cluster_support_nonempty | unmatched |  |
| cluster_support_eq_of_measureEquivalent | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_support_eq_of_measureEquivalent (L26)` | cluster_support_eq_of_measureEquivalent | unmatched |  |
| cluster_distToFinset_attained | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_distToFinset_attained (L49)` | cluster_distToFinset_attained | unmatched |  |
| cluster_distToFinset_nonneg | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_distToFinset_nonneg (L66)` | cluster_distToFinset_nonneg | unmatched |  |
| cluster_distToFinset_le_of_mem | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_distToFinset_le_of_mem (L74)` | cluster_distToFinset_le_of_mem | unmatched |  |
| cluster_linked_symmetric | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_linked_symmetric (L83)` | cluster_linked_symmetric | unmatched |  |
| cluster_componentOf_mem_self | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_componentOf_mem_self (L90)` | cluster_componentOf_mem_self | unmatched |  |
| cluster_componentOf_subset_support | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_componentOf_subset_support (L96)` | cluster_componentOf_subset_support | unmatched |  |
| cluster_componentOf_eq_of_connected | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_componentOf_eq_of_connected (L104)` | cluster_componentOf_eq_of_connected | unmatched |  |
| cluster_componentOf_eq_of_linked | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_componentOf_eq_of_linked (L120)` | cluster_componentOf_eq_of_linked | unmatched |  |
| cluster_component_eq_componentOf_of_mem | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_component_eq_componentOf_of_mem (L127)` | cluster_component_eq_componentOf_of_mem | unmatched |  |
| cluster_components_partition_support | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_components_partition_support (L139)` | cluster_components_partition_support | unmatched |  |
| cluster_association_partition | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_association_partition (L164)` | cluster_association_partition | unmatched |  |
| cluster_extrema_contain_and_width | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_extrema_contain_and_width (L210)` | cluster_extrema_contain_and_width | unmatched |  |
| cluster_externalGap_le_cross | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_externalGap_le_cross (L238)` | cluster_externalGap_le_cross | unmatched |  |
| cluster_externalGap_nonneg | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_externalGap_nonneg (L264)` | cluster_externalGap_nonneg | unmatched |  |
| cluster_externalGap_toReal_pos | lemma | `Helpers/ClusterGeometry.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.cluster_externalGap_toReal_pos (L277)` | cluster_externalGap_toReal_pos | unmatched |  |
| associatedSupport | definition | `Helpers/Inference.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.associatedSupport (L121)` | associatedSupport | unmatched |  |
| clusterExternalGap | definition | `Helpers/Inference.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.clusterExternalGap (L127)` | clusterExternalGap | unmatched |  |
| aux_ConcentrationConstantDomain | definition | `Basic.lean:ConcentrationConstantDomain (L577)` | aux_ConcentrationConstantDomain | unmatched |  |
| aux_GapScaleDomain | definition | `Basic.lean:GapScaleDomain (L188)` | aux_GapScaleDomain | unmatched |  |
| aux_MiscoverageDomain | definition | `Basic.lean:MiscoverageDomain (L567)` | aux_MiscoverageDomain | unmatched |  |
| aux_TailLevelDomain | definition | `Basic.lean:TailLevelDomain (L572)` | aux_TailLevelDomain | unmatched |  |
| aux_PublishedVMWAssumption2 | definition | `Helpers/CitedGates.lean:PublishedVMWAssumption2 (L117)` | aux_PublishedVMWAssumption2 | unmatched |  |
| aux_PublishedVMWQualitativeConditions | definition | `Helpers/CitedGates.lean:PublishedVMWQualitativeConditions (L34)` | aux_PublishedVMWQualitativeConditions | unmatched |  |
| aux_PublishedVMWRecoveryRegime | definition | `Helpers/CitedGates.lean:PublishedVMWRecoveryRegime (L167)` | aux_PublishedVMWRecoveryRegime | unmatched |  |
| aux_PublishedVMWStrictLatentPositivity | definition | `Helpers/CitedGates.lean:PublishedVMWStrictLatentPositivity (L124)` | aux_PublishedVMWStrictLatentPositivity | unmatched |  |
| aux_PublishedVMWAssumption4 | definition | `Helpers/CitedGates.lean:PublishedVMWAssumption4 (L131)` | aux_PublishedVMWAssumption4 | unmatched |  |
| aux_PublishedVMWMarginRecord | definition | `Helpers/CitedGates.lean:PublishedVMWMarginRecord (L28)` | aux_PublishedVMWMarginRecord | unmatched |  |
| aux_PublishedVMWNoFixedMargins | definition | `Helpers/CitedGates.lean:PublishedVMWNoFixedMargins (L47)` | aux_PublishedVMWNoFixedMargins | unmatched |  |
| aux_PublishedVMWScopeHandle | definition | `Helpers/CitedGates.lean:PublishedVMWScopeHandle (L13)` | aux_PublishedVMWScopeHandle | unmatched |  |
| aux_ConcreteVMWAssumption4 | definition | `Helpers/CitedGates.lean:ConcreteVMWAssumption4 (L151)` | aux_ConcreteVMWAssumption4 | unmatched |  |
| aux_ExactRealPrimitivesAt | definition | `Helpers/LatticeEstimator.lean:ExactRealPrimitivesAt (L364)` | aux_ExactRealPrimitivesAt | unmatched |  |
| aux_VMWPositiveDimensionDomain | definition | `Helpers/CitedGates.lean:VMWPositiveDimensionDomain (L136)` | aux_VMWPositiveDimensionDomain | unmatched |  |
| aux_PublishedVMWTopRightSingularBasis | definition | `Helpers/CitedGates.lean:PublishedVMWTopRightSingularBasis (L140)` | aux_PublishedVMWTopRightSingularBasis | unmatched |  |
| aux_PublishedVMWTheorem72FiniteSampleRecovery | definition | `Helpers/CitedGates.lean:PublishedVMWTheorem72FiniteSampleRecovery (L176)` | aux_PublishedVMWTheorem72FiniteSampleRecovery | unmatched |  |
| genuinePenroseInverse | definition | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.genuinePenroseInverse (L212)` | genuinePenroseInverse | unmatched |  |
| genuinePenroseInverse_eq_penroseInverse_of_injective | lemma | `Helpers/SpectralSubstrate.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.genuinePenroseInverse_eq_penroseInverse_of_injective (L322)` | genuinePenroseInverse_eq_penroseInverse_of_injective | unmatched |  |
| publishedTopRightSignalBasis_exists | lemma | `TPublishedVMWConverseTransfer.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.publishedTopRightSignalBasis_exists (L56)` | publishedTopRightSignalBasis_exists | unmatched |  |
| pathObservedCellMass | definition | `Helpers/PathCertificates.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.pathObservedCellMass (L161)` | pathObservedCellMass | unmatched |  |
| netLibrary_univList_map_injective | lemma | `Helpers/NetLibraryExistence.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.netLibrary_univList_map_injective (L16)` | netLibrary_univList_map_injective | unmatched |  |
| netLibrary_univList_flatMap_injective | lemma | `Helpers/NetLibraryExistence.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.netLibrary_univList_flatMap_injective (L34)` | netLibrary_univList_flatMap_injective | unmatched |  |
| summaryLexKey_injective | lemma | `Helpers/NetLibraryExistence.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.summaryLexKey_injective (L57)` | summaryLexKey_injective | unmatched |  |
| netLibrary_nonempty | lemma | `Helpers/NetLibraryExistence.lean:CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.netLibrary_nonempty (L101)` | netLibrary_nonempty | unmatched |  |
