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
| P-1 | definition | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.TieSafeSurvivorModel (L243)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.PositiveUniformInferenceLawClass (L277)` | P-2 | equivalent |  |
| P-3 | definition | `Helpers/Capacities.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.paperObservableCapacities (L136)` | P-3 | equivalent |  |
| P-4 | definition | `Helpers/Transport.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.paperExactMassPolytope (L70)` | P-4 | equivalent |  |
| P-5 | definition | `Helpers/Capacities.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.Capacities.paperThresholdCuts (L169)` | P-5 | equivalent |  |
| P-6 | definition | `Helpers/Capacities.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.Capacities.endpointMap (L197)` | P-6 | equivalent |  |
| P-7 | definition | `Helpers/Transport.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.thresholdFlow (L2285)` | P-7 | equivalent |  |
| P-8 | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.threeLevelWitness (L143)` | P-8 | equivalent |  |
| P-9 | definition | `Helpers/Estimator.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.plugInEndpoints (L85)` | P-9 | equivalent |  |
| P-10 | definition | `Helpers/Estimator.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.guardedConfidenceSet (L324)` | P-10 | equivalent |  |
| P-11 | definition | `OpenQuestions.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.openQuestion_uniformFaceMultiplierCalibration (L31)` | P-11 | equivalent |  |
| T-1 | theorem | `TCapacityIdentification.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.capacity_identification (L660)` | T-1 | equivalent |  |
| T-2 | theorem | `TTieFaceCollapse.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.tie_face_collapse (L287)` | T-2 | equivalent |  |
| T-3 | theorem | `TFullLawEndpointAttainment.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.full_law_endpoint_attainment (L2648)` | T-3 | equivalent |  |
| T-4 | theorem | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.three_level_witness_sharp (L845)` | T-4 | equivalent |  |
| T-5 | theorem | `TNoSelectionReduction.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.no_selection_reduction (L129)` | T-5 | equivalent |  |
| T-6 | theorem | `TSharpExactMassThresholdInterval.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.sharp_exact_mass_threshold_interval (L23)` | T-6 | equivalent |  |
| T-7 | theorem | `TLinearSparseThresholdFlow.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.linear_sparse_threshold_flow (L14)` | T-7 | equivalent |  |
| T-8 | theorem | `TBranchFreePointwiseDirectionalLimit.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.branch_free_pointwise_directional_limit (L35)` | T-8 | equivalent |  |
| T-9 | theorem | `TUniformDeterministicGuard.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.uniform_deterministic_guard (L43)` | T-9 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.IVIndependence (L157)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.TreatmentConsistency (L164)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.SelectionExclusion (L169)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.OutcomeExclusion (L174)` | A-4 | equivalent |  |
| A-5 | assumption | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.InstrumentOverlap (L179)` | A-5 | equivalent |  |
| A-6 | assumption | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.NoDefiers (L186)` | A-6 | equivalent |  |
| A-7 | assumption | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.WeakSelectionMonotonicity (L191)` | A-7 | equivalent |  |
| A-8 | assumption | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.DirectionMargin (L201)` | A-8 | unmatched |  |
| A-9 | assumption | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.PositiveAggregateSurvivors (L207)` | A-9 | equivalent |  |
| A-10 | assumption | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.UniformAggregateSurvivorBound (L212)` | A-10 | equivalent |  |
| A-11 | assumption | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.IidSampling (L236)` | A-11 | equivalent |  |
| aux_benefitLower | definition | `Helpers/Capacities.lean:benefitLower (L154)` | aux_benefitLower | unmatched |  |
| aux_benefitMass | definition | `Helpers/Transport.lean:benefitMass (L103)` | aux_benefitMass | unmatched |  |
| aux_benefitUpper | definition | `Helpers/Capacities.lean:benefitUpper (L159)` | aux_benefitUpper | unmatched |  |
| aux_Capacities | definition | `Helpers/Capacities.lean:Capacities (L48)` | aux_Capacities | unmatched |  |
| aux_CompatibleLatentCellTable | definition | `(none)` | aux_CompatibleLatentCellTable | unmatched |  |
| aux_decPolytope | definition | `Helpers/Transport.lean:decPolytope (L91)` | aux_decPolytope | unmatched |  |
| aux_denseThresholdFlowCost | definition | `(none)` | aux_denseThresholdFlowCost | unmatched |  |
| aux_EndpointConvergesInProbability | definition | `TBranchFreePointwiseDirectionalLimit.lean:EndpointConvergesInProbability (L28)` | aux_EndpointConvergesInProbability | unmatched |  |
| aux_endpointError | definition | `TUniformDeterministicGuard.lean:endpointError (L36)` | aux_endpointError | unmatched |  |
| aux_endpointFromMassVectorOn | definition | `Helpers/Estimator.lean:endpointFromMassVectorOn (L188)` | aux_endpointFromMassVectorOn | unmatched |  |
| aux_gap | definition | `Helpers/Capacities.lean:gap (L67)` | aux_gap | unmatched |  |
| aux_guardRadius | definition | `Helpers/Estimator.lean:guardRadius (L304)` | aux_guardRadius | unmatched |  |
| aux_HasTangentialHadamardDirDerivAt | definition | `Helpers/CitedGates.lean:HasTangentialHadamardDirDerivAt (L93)` | aux_HasTangentialHadamardDirDerivAt | unmatched |  |
| aux_identifiedIcc | definition | `Helpers/Capacities.lean:identifiedIcc (L216)` | aux_identifiedIcc | unmatched |  |
| aux_incPolytope | definition | `Helpers/Transport.lean:incPolytope (L85)` | aux_incPolytope | unmatched |  |
| aux_IsEndpointWitness | definition | `TFullLawEndpointAttainment.lean:IsEndpointWitness (L25)` | aux_IsEndpointWitness | unmatched |  |
| aux_latentTableNonnegative | definition | `(none)` | aux_latentTableNonnegative | unmatched |  |
| aux_lowerAttainer | definition | `(none)` | aux_lowerAttainer | unmatched |  |
| aux_lowerLe | definition | `Helpers/Capacities.lean:lowerLe (L75)` | aux_lowerLe | unmatched |  |
| aux_lowerLt | definition | `Helpers/Capacities.lean:lowerLt (L79)` | aux_lowerLt | unmatched |  |
| aux_mass | definition | `Helpers/Capacities.lean:mass (L71)` | aux_mass | unmatched |  |
| aux_matrixNonnegative | definition | `Helpers/Transport.lean:matrixNonnegative (L30)` | aux_matrixNonnegative | unmatched |  |
| aux_ObservedDatum | definition | `Helpers/Capacities.lean:ObservedDatum (L24)` | aux_ObservedDatum | unmatched |  |
| aux_observedLaw | definition | `Basic.lean:observedLaw (L127)` | aux_observedLaw | unmatched |  |
| aux_p | definition | `Basic.lean:p (L109)` | aux_p | unmatched |  |
| aux_positiveSupport | definition | `Helpers/Estimator.lean:positiveSupport (L107)` | aux_positiveSupport | unmatched |  |
| aux_positiveSupportCard | definition | `Helpers/Transport.lean:positiveSupportCard (L108)` | aux_positiveSupportCard | unmatched |  |
| aux_POSlateSystem | definition | `Basic.lean:POSlateSystem (L27)` | aux_POSlateSystem | unmatched |  |
| aux_screenedCell | definition | `Helpers/Estimator.lean:screenedCell (L78)` | aux_screenedCell | unmatched |  |
| aux_screenedSupport | definition | `Helpers/Estimator.lean:screenedSupport (L113)` | aux_screenedSupport | unmatched |  |
| aux_tableSurvivorCoupling | definition | `(none)` | aux_tableSurvivorCoupling | unmatched |  |
| aux_thresholdFlowCostFor | definition | `Helpers/Transport.lean:thresholdFlowCostFor (L2926)` | aux_thresholdFlowCostFor | unmatched |  |
| aux_thresholdFlowLower | definition | `Helpers/Transport.lean:thresholdFlowLower (L2045)` | aux_thresholdFlowLower | unmatched |  |
| aux_thresholdFlowUpper | definition | `Helpers/Transport.lean:thresholdFlowUpper (L2050)` | aux_thresholdFlowUpper | unmatched |  |
| aux_tiePolytope | definition | `Helpers/Transport.lean:tiePolytope (L97)` | aux_tiePolytope | unmatched |  |
| aux_upperAttainer | definition | `(none)` | aux_upperAttainer | unmatched |  |
| aux_upperGt | definition | `Helpers/Capacities.lean:upperGt (L91)` | aux_upperGt | unmatched |  |
| aux_upperLe | definition | `Helpers/Capacities.lean:upperLe (L87)` | aux_upperLe | unmatched |  |
| aux_ValidCapacities | definition | `Helpers/Capacities.lean:ValidCapacities (L53)` | aux_ValidCapacities | unmatched |  |
| aux_WeakConverges | definition | `Helpers/CitedGates.lean:WeakConverges (L22)` | aux_WeakConverges | unmatched |  |
| aux_aggregateMass | definition | `Helpers/Capacities.lean:aggregateMass (L177)` | aux_aggregateMass | unmatched |  |
| aux_benefitProbabilityOf | definition | `(none)` | aux_benefitProbabilityOf | unmatched |  |
| aux_denseThresholdFlowCostFor | definition | `Helpers/Transport.lean:denseThresholdFlowCostFor (L2948)` | aux_denseThresholdFlowCostFor | unmatched |  |
| aux_FullLawCandidate | definition | `(none)` | aux_FullLawCandidate | unmatched |  |
| aux_FullLawFeasible | definition | `(none)` | aux_FullLawFeasible | unmatched |  |
| aux_fullLawSurvivorCoupling | definition | `(none)` | aux_fullLawSurvivorCoupling | unmatched |  |
| aux_guardedConfidenceInterval | definition | `Helpers/Estimator.lean:guardedConfidenceInterval (L356)` | aux_guardedConfidenceInterval | unmatched |  |
| aux_GuardedInferenceHandle | definition | `Helpers/Estimator.lean:GuardedInferenceHandle (L313)` | aux_GuardedInferenceHandle | unmatched |  |
| aux_observableCapacityContrasts | definition | `Helpers/Capacities.lean:observableCapacityContrasts (L104)` | aux_observableCapacityContrasts | unmatched |  |
| aux_SupportedIn | definition | `Helpers/CitedGates.lean:SupportedIn (L33)` | aux_SupportedIn | unmatched |  |
| aux_TightProbabilityLaw | definition | `Helpers/CitedGates.lean:TightProbabilityLaw (L28)` | aux_TightProbabilityLaw | unmatched |  |
| s0 | definition | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.POSlateSystem.S0 (L88)` | s0 | unmatched |  |
| s1 | definition | `Basic.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.POSlateSystem.S1 (L91)` | s1 | unmatched |  |
| aux_branchFreePolytope | definition | `Helpers/Transport.lean:branchFreePolytope (L78)` | aux_branchFreePolytope | unmatched |  |
| aux_Costed | definition | `Helpers/Transport.lean:Costed (L2329)` | aux_Costed | unmatched |  |
| aux_costedSparseThresholdFlow | definition | `Helpers/Transport.lean:costedSparseThresholdFlow (L2917)` | aux_costedSparseThresholdFlow | unmatched |  |
| aux_EndpointMapResult | definition | `Helpers/Capacities.lean:EndpointMapResult (L188)` | aux_EndpointMapResult | unmatched |  |
| aux_PartialTransportPolytopes | definition | `Helpers/Transport.lean:PartialTransportPolytopes (L40)` | aux_PartialTransportPolytopes | unmatched |  |
| aux_thresholdFlowLowerSparse | definition | `Helpers/Transport.lean:thresholdFlowLowerSparse (L2004)` | aux_thresholdFlowLowerSparse | unmatched |  |
| aux_thresholdFlowUpperSparse | definition | `Helpers/Transport.lean:thresholdFlowUpperSparse (L2010)` | aux_thresholdFlowUpperSparse | unmatched |  |
| aux_CompatibleBaseline | definition | `Helpers/Transport.lean:CompatibleBaseline (L2236)` | aux_CompatibleBaseline | unmatched |  |
| aux_denseThresholdFlowActualCostFor | definition | `Helpers/Transport.lean:denseThresholdFlowActualCostFor (L2953)` | aux_denseThresholdFlowActualCostFor | unmatched |  |
| aux_SparsePassResult | definition | `Helpers/Transport.lean:SparsePassResult (L120)` | aux_SparsePassResult | unmatched |  |
| aux_thresholdFlowActualCostFor | definition | `Helpers/Transport.lean:thresholdFlowActualCostFor (L2930)` | aux_thresholdFlowActualCostFor | unmatched |  |
| aux_ThresholdFlowResult | definition | `Helpers/Transport.lean:ThresholdFlowResult (L2277)` | aux_ThresholdFlowResult | unmatched |  |
| aux_ThresholdLatentCompletion | definition | `Helpers/Transport.lean:ThresholdLatentCompletion (L2251)` | aux_ThresholdLatentCompletion | unmatched |  |
| maxBenefitSparseOperations_le | lemma | `Helpers/Transport.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.maxBenefitSparseOperations_le (L2694)` | maxBenefitSparseOperations_le | unmatched |  |
| maxNonBenefitSparseOperations_le | lemma | `Helpers/Transport.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.maxNonBenefitSparseOperations_le (L2703)` | maxNonBenefitSparseOperations_le | unmatched |  |
| completeSparseOperations_le | lemma | `Helpers/Transport.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.completeSparseOperations_le (L2712)` | completeSparseOperations_le | unmatched |  |
| maxBenefitPass_residual_length_le | lemma | `Helpers/Transport.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.maxBenefitPass_residual_length_le (L2721)` | maxBenefitPass_residual_length_le | unmatched |  |
| maxNonBenefitPass_residual_length_le | lemma | `Helpers/Transport.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.maxNonBenefitPass_residual_length_le (L2732)` | maxNonBenefitPass_residual_length_le | unmatched |  |
| sparseCellActualOperations_le_budget | lemma | `Helpers/Transport.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.sparseCellActualOperations_le_budget (L2879)` | sparseCellActualOperations_le_budget | unmatched |  |
| sigma_xBundle | lemma | `Helpers/CondIndepBridge.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.sigma_xBundle (L40)` | sigma_xBundle | unmatched |  |
| condIndepCFBundle_of_condIndepCF | lemma | `Helpers/CondIndepBridge.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.condIndepCFBundle_of_condIndepCF (L59)` | condIndepCFBundle_of_condIndepCF | unmatched |  |
| measurable_POSlate_SofD | lemma | `TTieFaceCollapse.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.measurable_POSlate_SofD (L21)` | measurable_POSlate_SofD | unmatched |  |
| sum_rowMass_eq_totalMass | lemma | `TTieFaceCollapse.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.sum_rowMass_eq_totalMass (L26)` | sum_rowMass_eq_totalMass | unmatched |  |
| sum_columnMass_eq_totalMass | lemma | `TTieFaceCollapse.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.sum_columnMass_eq_totalMass (L32)` | sum_columnMass_eq_totalMass | unmatched |  |
| pointwise_eq_of_le_of_sum_eq | lemma | `TTieFaceCollapse.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.pointwise_eq_of_le_of_sum_eq (L38)` | pointwise_eq_of_le_of_sum_eq | unmatched |  |
| branchFree_exact_rows_of_q0_le_q1 | lemma | `TTieFaceCollapse.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.branchFree_exact_rows_of_q0_le_q1 (L50)` | branchFree_exact_rows_of_q0_le_q1 | unmatched |  |
| branchFree_exact_columns_of_q1_le_q0 | lemma | `TTieFaceCollapse.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.branchFree_exact_columns_of_q1_le_q0 (L60)` | branchFree_exact_columns_of_q1_le_q0 | unmatched |  |
| polytope_tie_iff_gap_zero | lemma | `TTieFaceCollapse.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.polytope_tie_iff_gap_zero (L70)` | polytope_tie_iff_gap_zero | unmatched |  |
| branchFree_eq_tie_of_gap_zero | lemma | `TTieFaceCollapse.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.branchFree_eq_tie_of_gap_zero (L142)` | branchFree_eq_tie_of_gap_zero | unmatched |  |
| prefix_difference_eq_tail_difference_of_gap_zero | lemma | `TTieFaceCollapse.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.prefix_difference_eq_tail_difference_of_gap_zero (L162)` | prefix_difference_eq_tail_difference_of_gap_zero | unmatched |  |
| equalSelectionComplierMass_of_zero_gap | lemma | `TTieFaceCollapse.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.equalSelectionComplierMass_of_zero_gap (L179)` | equalSelectionComplierMass_of_zero_gap | unmatched |  |
| selectedComplierMass_eq_complierMass_of_noSelection | lemma | `TNoSelectionReduction.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.selectedComplierMass_eq_complierMass_of_noSelection (L28)` | selectedComplierMass_eq_complierMass_of_noSelection | unmatched |  |
| aux_RealizesThresholdLatentCompletion | definition | `TFullLawEndpointAttainment.lean:RealizesThresholdLatentCompletion (L387)` | aux_RealizesThresholdLatentCompletion | unmatched |  |
| WNode | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.WNode (L148)` | WNode | unmatched |  |
| instDecidableEqWNode | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.instDecidableEqWNode (L151)` | instDecidableEqWNode | unmatched |  |
| instFintypeWNode | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.instFintypeWNode (L160)` | instFintypeWNode | unmatched |  |
| WValue | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.WValue (L164)` | WValue | unmatched |  |
| wMeasurableSpace | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wMeasurableSpace (L170)` | wMeasurableSpace | unmatched |  |
| instMeasurableSpaceWValue | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.instMeasurableSpaceWValue (L174)` | instMeasurableSpaceWValue | unmatched |  |
| wEval | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wEval (L178)` | wEval | unmatched |  |
| wSeedP | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wSeedP (L189)` | wSeedP | unmatched |  |
| wSeedS | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wSeedS (L202)` | wSeedS | unmatched |  |
| wSeed_p | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wSeed_p (L227)` | wSeed_p | unmatched |  |
| wSeed_propensity | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wSeed_propensity (L236)` | wSeed_propensity | unmatched |  |
| wTable | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wTable (L259)` | wTable | unmatched |  |
| wNN | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wNN (L262)` | wNN | unmatched |  |
| witnessLatentTable_complier_support | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.witnessLatentTable_complier_support (L269)` | witnessLatentTable_complier_support | unmatched |  |
| witnessLatentTable_selection_support | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.witnessLatentTable_selection_support (L277)` | witnessLatentTable_selection_support | unmatched |  |
| wNorm | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wNorm (L284)` | wNorm | unmatched |  |
| wHp | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wHp (L289)` | wHp | unmatched |  |
| wHprop | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wHprop (L295)` | wHprop | unmatched |  |
| witnessInstrumentMeasure_atom | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.witnessInstrumentMeasure_atom (L301)` | witnessInstrumentMeasure_atom | unmatched |  |
| witnessLatentMeasure_atom | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.witnessLatentMeasure_atom (L308)` | witnessLatentMeasure_atom | unmatched |  |
| witnessLatentMeasure_univ | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.witnessLatentMeasure_univ (L323)` | witnessLatentMeasure_univ | unmatched |  |
| instIsProbabilityMeasureWitnessLatent | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.instIsProbabilityMeasureWitnessLatent (L343)` | instIsProbabilityMeasureWitnessLatent | unmatched |  |
| witnessLatentMeasure_ae_compliers | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.witnessLatentMeasure_ae_compliers (L347)` | witnessLatentMeasure_ae_compliers | unmatched |  |
| witnessLatentMeasure_ae_selection | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.witnessLatentMeasure_ae_selection (L362)` | witnessLatentMeasure_ae_selection | unmatched |  |
| witnessInstrumentMeasure_univ | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.witnessInstrumentMeasure_univ (L377)` | witnessInstrumentMeasure_univ | unmatched |  |
| instIsProbabilityMeasureWitnessInstrument | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.instIsProbabilityMeasureWitnessInstrument (L385)` | instIsProbabilityMeasureWitnessInstrument | unmatched |  |
| instIsProbabilityMeasureWitnessFull | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.instIsProbabilityMeasureWitnessFull (L389)` | instIsProbabilityMeasureWitnessFull | unmatched |  |
| instIsFiniteMeasureWitnessFull | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.instIsFiniteMeasureWitnessFull (L395)` | instIsFiniteMeasureWitnessFull | unmatched |  |
| witnessObservedMeasure_univ | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.witnessObservedMeasure_univ (L401)` | witnessObservedMeasure_univ | unmatched |  |
| instIsProbabilityMeasureWitnessObserved | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.instIsProbabilityMeasureWitnessObserved (L415)` | instIsProbabilityMeasureWitnessObserved | unmatched |  |
| witnessObservedMeasure_atom | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.witnessObservedMeasure_atom (L419)` | witnessObservedMeasure_atom | unmatched |  |
| wCandidate | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wCandidate (L435)` | wCandidate | unmatched |  |
| wObservedLaw | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wObservedLaw (L439)` | wObservedLaw | unmatched |  |
| wLower | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wLower (L475)` | wLower | unmatched |  |
| wUpper | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wUpper (L500)` | wUpper | unmatched |  |
| wBenefitLower | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wBenefitLower (L525)` | wBenefitLower | unmatched |  |
| wBenefitUpper | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wBenefitUpper (L555)` | wBenefitUpper | unmatched |  |
| wCapacityFacts | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wCapacityFacts (L592)` | wCapacityFacts | unmatched |  |
| wFullLaw | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wFullLaw (L607)` | wFullLaw | unmatched |  |
| wCandidate_p | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wCandidate_p (L646)` | wCandidate_p | unmatched |  |
| instStandardBorelSpaceWCandidate | definition | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.instStandardBorelSpaceWCandidate (L651)` | instStandardBorelSpaceWCandidate | unmatched |  |
| wCandidate_propensity | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wCandidate_propensity (L655)` | wCandidate_propensity | unmatched |  |
| wCompliers | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wCompliers (L679)` | wCompliers | unmatched |  |
| wSelectionIncreasing | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wSelectionIncreasing (L694)` | wSelectionIncreasing | unmatched |  |
| wValid | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wValid (L709)` | wValid | unmatched |  |
| wModel | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wModel (L721)` | wModel | unmatched |  |
| wRealization | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wRealization (L755)` | wRealization | unmatched |  |
| wEndpoint | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wEndpoint (L793)` | wEndpoint | unmatched |  |
| wInterval | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wInterval (L807)` | wInterval | unmatched |  |
| wEndpointWitnesses | lemma | `TThreeLevelWitness.lean:CausalSmith.PartialID.SlateBenefitPartialTransport.wEndpointWitnesses (L826)` | wEndpointWitnesses | unmatched |  |
| aux_FiniteIidSampling | definition | `Basic.lean:FiniteIidSampling (L221)` | aux_FiniteIidSampling | unmatched |  |
| aux_ObservedLawDomain | definition | `Helpers/Capacities.lean:ObservedLawDomain (L123)` | aux_ObservedLawDomain | unmatched |  |
| aux_observableCapacities | definition | `Helpers/Capacities.lean:observableCapacities (L128)` | aux_observableCapacities | unmatched |  |
| aux_UniformInferenceLawClass | definition | `Basic.lean:UniformInferenceLawClass (L259)` | aux_UniformInferenceLawClass | unmatched |  |
