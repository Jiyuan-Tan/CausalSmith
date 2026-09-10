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
| P-1 | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.ClampModel (L203)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.clampPolicy (L103)` | P-2 | equivalent |  |
| P-3 | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.infoBandwidth (L275)` | P-3 | equivalent |  |
| P-4 | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.clampFrontier (L285)` | P-4 | equivalent |  |
| P-5 | definition | `Helpers/Design.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.totalGramEstimator (L218)` | P-5 | equivalent |  |
| P-6 | definition | `Helpers/Design.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.honestInterval (L260)` | P-6 | equivalent |  |
| P-7 | definition | `Helpers/Design.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.exactModulusHandle (L307)` | P-7 | equivalent |  |
| P-8 | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.FullDataClampModel (L464)` | P-8 | equivalent |  |
| P-9 | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.causalFrontierCriteria (L483)` | P-9 | equivalent |  |
| P-10 | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.ContClampModel (L530)` | P-10 | equivalent |  |
| P-11 | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.contClampFunctional (L555)` | P-11 | equivalent |  |
| P-12 | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.contFrontier (L565)` | P-12 | equivalent |  |
| P-13 | definition | `Helpers/Design.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.contFallbackEstimator (L228)` | P-13 | equivalent |  |
| P-14 | definition | `Helpers/Design.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.contHoeffdingInterval (L236)` | P-14 | equivalent |  |
| P-15 | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.ContFullDataClampModel (L572)` | P-15 | equivalent |  |
| P-16 | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.contFrontierCriteria (L649)` | P-16 | equivalent |  |
| P-17 | definition | `OpenQuestions.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.SharpConfidenceLengthConstantQuestion (L108)` | P-17 | equivalent |  |
| T-1 | theorem | `TCausalBridge.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.causal_bridge (L32)` | T-1 | equivalent |  |
| T-2 | theorem | `TMinimaxRisk.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.clamp_minimax_risk (L1093)` | T-2 | equivalent |  |
| T-3 | theorem | `THonestLength.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.honest_coverage_and_length (L128)` | T-3 | equivalent |  |
| T-4 | theorem | `TPhaseDiagram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.clamp_phase_diagram (L73)` | T-4 | equivalent |  |
| T-5 | theorem | `TOneCellCalibration.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.one_cell_calibration (L437)` | T-5 | equivalent |  |
| T-6 | theorem | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.causal_frontier_lift (L665)` | T-6 | equivalent |  |
| T-7 | theorem | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.observed_margin_surjectivity (L50)` | T-7 | equivalent |  |
| T-8 | theorem | `TCausalBridge.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.continuity_causal_bridge (L166)` | T-8 | equivalent |  |
| T-9 | theorem | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.continuity_observed_margin_surjectivity (L151)` | T-9 | equivalent |  |
| T-10 | theorem | `THonestLength.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.continuity_only_frontier (L778)` | T-10 | equivalent |  |
| L-1 | lemma | `Helpers/Pushforward.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.clamp_pushforward_decomposition (L38)` | L-1 | equivalent |  |
| L-2 | lemma | `Helpers/Pushforward.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.clamp_policy_support (L163)` | L-2 | equivalent |  |
| L-3 | lemma | `Helpers/Bandwidth.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.bandwidth_phases (L321)` | L-3 | equivalent |  |
| L-4 | lemma | `Helpers/TotalGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.total_gram_stabilization (L500)` | L-4 | equivalent |  |
| L-5 | lemma | `Helpers/CausalBridgeMeasure.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.cont_regression_extension_unique (L372)` | L-5 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.IidSampling (L129)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.CondDensityLaw (L146)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.LatentResponseConsistency (L399)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.LatentExchangeability (L421)` | A-4 | equivalent |  |
| A-5 | assumption | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.StratumMass (L162)` | A-5 | equivalent |  |
| A-6 | assumption | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.PolynomialThinning (L171)` | A-6 | equivalent |  |
| A-7 | assumption | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.HolderRegression (L184)` | A-7 | equivalent |  |
| A-8 | assumption | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.FullDataResponseContinuity (L448)` | A-8 | equivalent |  |
| aux_AsympSeq | definition | `Helpers/Bandwidth.lean:AsympSeq (L23)` | aux_AsympSeq | unmatched |  |
| aux_atomMass | definition | `Basic.lean:atomMass (L107)` | aux_atomMass | unmatched |  |
| aux_causalStabilizedCoverage | definition | `TCausalFrontierLift.lean:causalStabilizedCoverage (L263)` | aux_causalStabilizedCoverage | unmatched |  |
| aux_causalStabilizedWorstLength | definition | `TCausalFrontierLift.lean:causalStabilizedWorstLength (L273)` | aux_causalStabilizedWorstLength | unmatched |  |
| aux_causalStabilizedWorstRisk | definition | `TCausalFrontierLift.lean:causalStabilizedWorstRisk (L254)` | aux_causalStabilizedWorstRisk | unmatched |  |
| aux_clampFunctional | definition | `Basic.lean:clampFunctional (L116)` | aux_clampFunctional | unmatched |  |
| aux_ClampLaw | definition | `Basic.lean:ClampLaw (L95)` | aux_ClampLaw | unmatched |  |
| aux_ClampObs | definition | `Basic.lean:ClampObs (L85)` | aux_ClampObs | unmatched |  |
| aux_ConfidenceProcedure | definition | `Basic.lean:ConfidenceProcedure (L309)` | aux_ConfidenceProcedure | unmatched |  |
| aux_confidenceWorstLength | definition | `THonestLength.lean:confidenceWorstLength (L61)` | aux_confidenceWorstLength | unmatched |  |
| aux_deltaCrit | definition | `Basic.lean:deltaCrit (L290)` | aux_deltaCrit | unmatched |  |
| aux_deltaEdge | definition | `Basic.lean:deltaEdge (L296)` | aux_deltaEdge | unmatched |  |
| aux_FullDataLaw | definition | `Basic.lean:FullDataLaw (L368)` | aux_FullDataLaw | unmatched |  |
| aux_GoodGramEvent | definition | `Helpers/Design.lean:GoodGramEvent (L129)` | aux_GoodGramEvent | unmatched |  |
| aux_lambdaStar | definition | `Helpers/Design.lean:lambdaStar (L56)` | aux_lambdaStar | unmatched |  |
| aux_observedMinimaxLength | definition | `Basic.lean:observedMinimaxLength (L352)` | aux_observedMinimaxLength | unmatched |  |
| aux_observedMinimaxRisk | definition | `Basic.lean:observedMinimaxRisk (L336)` | aux_observedMinimaxRisk | unmatched |  |
| aux_productChiSq | definition | `TMinimaxRisk.lean:productChiSq (L41)` | aux_productChiSq | unmatched |  |
| aux_SplitBlocks | definition | `Helpers/Design.lean:SplitBlocks (L63)` | aux_SplitBlocks | unmatched |  |
| aux_stabilizedCoverage | definition | `THonestLength.lean:stabilizedCoverage (L43)` | aux_stabilizedCoverage | unmatched |  |
| aux_stabilizedWorstLength | definition | `THonestLength.lean:stabilizedWorstLength (L52)` | aux_stabilizedWorstLength | unmatched |  |
| aux_stabilizedWorstRisk | definition | `TMinimaxRisk.lean:stabilizedWorstRisk (L34)` | aux_stabilizedWorstRisk | unmatched |  |
| aux_ThresholdSequence | definition | `Basic.lean:ThresholdSequence (L264)` | aux_ThresholdSequence | unmatched |  |
| aux_UniformCoverage | definition | `Basic.lean:UniformCoverage (L345)` | aux_UniformCoverage | unmatched |  |
| aux_BernoulliOutcomeLaw | definition | `TMinimaxRisk.lean:BernoulliOutcomeLaw (L61)` | aux_BernoulliOutcomeLaw | unmatched |  |
| aux_blockAverage | definition | `Helpers/Design.lean:blockAverage (L193)` | aux_blockAverage | unmatched |  |
| aux_clampUnit | definition | `Helpers/Design.lean:clampUnit (L190)` | aux_clampUnit | unmatched |  |
| aux_ellOf | definition | `Basic.lean:ellOf (L178)` | aux_ellOf | unmatched |  |
| aux_GlobalBernoulliShift | definition | `TMinimaxRisk.lean:GlobalBernoulliShift (L220)` | aux_GlobalBernoulliShift | unmatched |  |
| aux_LocalizedBernoulliPerturbation | definition | `TMinimaxRisk.lean:LocalizedBernoulliPerturbation (L350)` | aux_LocalizedBernoulliPerturbation | unmatched |  |
| aux_ObservedMeasurableEstimator | definition | `Basic.lean:ObservedMeasurableEstimator (L312)` | aux_ObservedMeasurableEstimator | unmatched |  |
| aux_ObservedMeasurableInterval | definition | `Basic.lean:ObservedMeasurableInterval (L317)` | aux_ObservedMeasurableInterval | unmatched |  |
| aux_SharedClampDesign | definition | `TMinimaxRisk.lean:SharedClampDesign (L55)` | aux_SharedClampDesign | unmatched |  |
| aux_stabilizedInterval | definition | `THonestLength.lean:stabilizedInterval (L37)` | aux_stabilizedInterval | unmatched |  |
| aux_iidProduct | definition | `Basic.lean:iidProduct (L301)` | aux_iidProduct | unmatched |  |
| cond_weighted_bounded_sum_tail | lemma | `(none)` | cond_weighted_bounded_sum_tail | unmatched |  |
| infoBandwidth_eventually_balance | lemma | `Helpers/Bandwidth.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.infoBandwidth_eventually_balance (L31)` | infoBandwidth_eventually_balance | unmatched |  |
| balance_root_le_interior_scale | lemma | `Helpers/Bandwidth.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.balance_root_le_interior_scale (L149)` | balance_root_le_interior_scale | unmatched |  |
| interior_scale_le_balance_root | lemma | `Helpers/Bandwidth.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.interior_scale_le_balance_root (L174)` | interior_scale_le_balance_root | unmatched |  |
| interior_scale_le_threshold_of_edge_le | lemma | `Helpers/Bandwidth.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.interior_scale_le_threshold_of_edge_le (L212)` | interior_scale_le_threshold_of_edge_le | unmatched |  |
| balance_root_le_edge_scale | lemma | `Helpers/Bandwidth.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.balance_root_le_edge_scale (L241)` | balance_root_le_edge_scale | unmatched |  |
| edge_scale_le_balance_root | lemma | `Helpers/Bandwidth.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.edge_scale_le_balance_root (L265)` | edge_scale_le_balance_root | unmatched |  |
| oneCellTargetSeparation_eq | lemma | `TOneCellCalibration.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.oneCellTargetSeparation_eq (L57)` | oneCellTargetSeparation_eq | unmatched |  |
| oneCellTentSqIntegral_eq | lemma | `TOneCellCalibration.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.oneCellTentSqIntegral_eq (L120)` | oneCellTentSqIntegral_eq | unmatched |  |
| oneCellBandwidth_far | lemma | `TOneCellCalibration.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.oneCellBandwidth_far (L234)` | oneCellBandwidth_far | unmatched |  |
| oneCellProductKL_bounds | lemma | `TOneCellCalibration.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.oneCellProductKL_bounds (L322)` | oneCellProductKL_bounds | unmatched |  |
| oneCellNormalizedScale_eq | lemma | `TOneCellCalibration.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.oneCellNormalizedScale_eq (L409)` | oneCellNormalizedScale_eq | unmatched |  |
| zero_threshold_atom_and_frontier | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.zero_threshold_atom_and_frontier (L116)` | zero_threshold_atom_and_frontier | unmatched |  |
| critical_scale_div_edge_scale_tendsto_top | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.critical_scale_div_edge_scale_tendsto_top (L131)` | critical_scale_div_edge_scale_tendsto_top | unmatched |  |
| treatment_strictly_positive_ae | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.treatment_strictly_positive_ae (L27)` | treatment_strictly_positive_ae | unmatched |  |
| zero_threshold_functional | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.zero_threshold_functional (L62)` | zero_threshold_functional | unmatched |  |
| zero_threshold_totalGramEstimator | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.zero_threshold_totalGramEstimator (L77)` | zero_threshold_totalGramEstimator | unmatched |  |
| zero_threshold_stabilizedWorstRisk_asymp | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.zero_threshold_stabilizedWorstRisk_asymp (L538)` | zero_threshold_stabilizedWorstRisk_asymp | unmatched |  |
| edge_atom_scale_isLittleO_root | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.edge_atom_scale_isLittleO_root (L169)` | edge_atom_scale_isLittleO_root | unmatched |  |
| atom_interior_scale_exact | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.atom_interior_scale_exact (L196)` | atom_interior_scale_exact | unmatched |  |
| critical_atom_interior_scale_exact | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.critical_atom_interior_scale_exact (L226)` | critical_atom_interior_scale_exact | unmatched |  |
| atom_interior_div_root_exact | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.atom_interior_div_root_exact (L269)` | atom_interior_div_root_exact | unmatched |  |
| atom_interior_normalized_tendsto_critical | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.atom_interior_normalized_tendsto_critical (L327)` | atom_interior_normalized_tendsto_critical | unmatched |  |
| atom_interior_normalized_tendsto_top | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.atom_interior_normalized_tendsto_top (L401)` | atom_interior_normalized_tendsto_top | unmatched |  |
| critical_ratio_tendsto_edge_ratio_top | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.critical_ratio_tendsto_edge_ratio_top (L461)` | critical_ratio_tendsto_edge_ratio_top | unmatched |  |
| supercritical_ratio_tendsto_edge_ratio_top | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.supercritical_ratio_tendsto_edge_ratio_top (L484)` | supercritical_ratio_tendsto_edge_ratio_top | unmatched |  |
| fixed_positive_threshold_ratio_critical_top | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.fixed_positive_threshold_ratio_critical_top (L507)` | fixed_positive_threshold_ratio_critical_top | unmatched |  |
| asymp_add_reference_left | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.asymp_add_reference_left (L571)` | asymp_add_reference_left | unmatched |  |
| asymp_add_eventually_le_left | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.asymp_add_eventually_le_left (L585)` | asymp_add_eventually_le_left | unmatched |  |
| asympSeq_of_tendsto_div_pos | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.asympSeq_of_tendsto_div_pos (L361)` | asympSeq_of_tendsto_div_pos | unmatched |  |
| critical_interior_atom_asymp | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.critical_interior_atom_asymp (L377)` | critical_interior_atom_asymp | unmatched |  |
| supercritical_root_le_interior_atom | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.supercritical_root_le_interior_atom (L434)` | supercritical_root_le_interior_atom | unmatched |  |
| critical_interior_frontier_asymp | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.critical_interior_frontier_asymp (L725)` | critical_interior_frontier_asymp | unmatched |  |
| infoBandwidth_interior_asymp | lemma | `Helpers/Bandwidth.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.infoBandwidth_interior_asymp (L483)` | infoBandwidth_interior_asymp | unmatched |  |
| asympSeq_rpow | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.asympSeq_rpow (L599)` | asympSeq_rpow | unmatched |  |
| asympSeq_mul_nonnegative_left | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.asympSeq_mul_nonnegative_left (L617)` | asympSeq_mul_nonnegative_left | unmatched |  |
| asympSeq_trans | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.asympSeq_trans (L635)` | asympSeq_trans | unmatched |  |
| atomSeq_asymp_interior_of_edge_ratio_top | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.atomSeq_asymp_interior_of_edge_ratio_top (L657)` | atomSeq_asymp_interior_of_edge_ratio_top | unmatched |  |
| critical_atom_and_frontier_asymp | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.critical_atom_and_frontier_asymp (L691)` | critical_atom_and_frontier_asymp | unmatched |  |
| supercritical_frontier_asymp | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.supercritical_frontier_asymp (L747)` | supercritical_frontier_asymp | unmatched |  |
| regular_frontier_asymp | lemma | `Helpers/PhaseRates.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.regular_frontier_asymp (L822)` | regular_frontier_asymp | unmatched |  |
| fixed_positive_frontier_asymp | lemma | `Helpers/FixedPositive.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.fixed_positive_frontier_asymp (L25)` | fixed_positive_frontier_asymp | unmatched |  |
| zero_threshold_stabilizedWorstLength_asymp | lemma | `TPhaseDiagram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.zero_threshold_stabilizedWorstLength_asymp (L44)` | zero_threshold_stabilizedWorstLength_asymp | unmatched |  |
| totalGram_lambdaStar_pos | lemma | `Helpers/TotalGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.totalGram_lambdaStar_pos (L487)` | totalGram_lambdaStar_pos | unmatched |  |
| goodGram_interceptWeight_pointwise | lemma | `Helpers/TotalGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.goodGram_interceptWeight_pointwise (L336)` | goodGram_interceptWeight_pointwise | unmatched |  |
| scaledDose_mem_iff | lemma | `Helpers/TotalGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.scaledDose_mem_iff (L218)` | scaledDose_mem_iff | unmatched |  |
| local_active_count_eq | lemma | `Helpers/TotalGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.local_active_count_eq (L236)` | local_active_count_eq | unmatched |  |
| goodGram_weight_controls | lemma | `Helpers/TotalGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.goodGram_weight_controls (L383)` | goodGram_weight_controls | unmatched |  |
| measurable_clampObs_X | lemma | `Helpers/LocalWindowGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.measurable_clampObs_X (L25)` | measurable_clampObs_X | unmatched |  |
| measurable_clampObs_A | lemma | `Helpers/LocalWindowGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.measurable_clampObs_A (L30)` | measurable_clampObs_A | unmatched |  |
| stratumTreatmentMeasure_eq | lemma | `Helpers/LocalWindowGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.stratumTreatmentMeasure_eq (L89)` | stratumTreatmentMeasure_eq | unmatched |  |
| stratumTreatment_integral_eq | lemma | `Helpers/LocalWindowGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.stratumTreatment_integral_eq (L176)` | stratumTreatment_integral_eq | unmatched |  |
| lambdaStar_refMomentMatrix_coercive | lemma | `Helpers/ShiftedPowerCoercivity.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.lambdaStar_refMomentMatrix_coercive (L347)` | lambdaStar_refMomentMatrix_coercive | unmatched |  |
| conditionalTreatment_integral_eq_density | lemma | `Helpers/LocalWindowGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.conditionalTreatment_integral_eq_density (L200)` | conditionalTreatment_integral_eq_density | unmatched |  |
| scaledDose_mem_Icc_iff | lemma | `Helpers/LocalWindowGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.scaledDose_mem_Icc_iff (L221)` | scaledDose_mem_Icc_iff | unmatched |  |
| localWindowWeight_integral_eq | lemma | `Helpers/LocalWindowGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.localWindowWeight_integral_eq (L242)` | localWindowWeight_integral_eq | unmatched |  |
| integral_rpow_window_lower | lemma | `Helpers/LocalWindowGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.integral_rpow_window_lower (L272)` | integral_rpow_window_lower | unmatched |  |
| localWindowWeight_integral_lower | lemma | `Helpers/LocalWindowGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.localWindowWeight_integral_lower (L309)` | localWindowWeight_integral_lower | unmatched |  |
| localWindowGramEntry_integral_eq | lemma | `Helpers/LocalWindowGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.localWindowGramEntry_integral_eq (L375)` | localWindowGramEntry_integral_eq | unmatched |  |
| localWindow_populationGram_coercive | lemma | `Helpers/LocalWindowGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.localWindow_populationGram_coercive (L504)` | localWindow_populationGram_coercive | unmatched |  |
| lambdaStar_scaled_power_window_coercive | lemma | `Helpers/ShiftedPowerCoercivity.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.lambdaStar_scaled_power_window_coercive (L448)` | lambdaStar_scaled_power_window_coercive | unmatched |  |
| block_orderIso_sum_eq | lemma | `Helpers/TotalGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.block_orderIso_sum_eq (L250)` | block_orderIso_sum_eq | unmatched |  |
| localizedGramGood_iff_goodGramEvent | lemma | `Helpers/TotalGram.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.localizedGramGood_iff_goodGramEvent (L257)` | localizedGramGood_iff_goodGramEvent | unmatched |  |
| conditional_stratum_treatment_latent_indep | lemma | `Helpers/CausalBridgeMeasure.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.conditional_stratum_treatment_latent_indep (L29)` | conditional_stratum_treatment_latent_indep | unmatched |  |
| conditional_stratum_treatment_law | lemma | `Helpers/CausalBridgeMeasure.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.conditional_stratum_treatment_law (L139)` | conditional_stratum_treatment_law | unmatched |  |
| conditional_stratum_integral_prod | lemma | `Helpers/CausalBridgeMeasure.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.conditional_stratum_integral_prod (L186)` | conditional_stratum_integral_prod | unmatched |  |
| conditional_stratum_latent_integral_eq_mean | lemma | `Helpers/CausalBridgeMeasure.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.conditional_stratum_latent_integral_eq_mean (L260)` | conditional_stratum_latent_integral_eq_mean | unmatched |  |
| fullDataResponseMean_dist_le | lemma | `Helpers/CausalBridgeMeasure.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.fullDataResponseMean_dist_le (L289)` | fullDataResponseMean_dist_le | unmatched |  |
| fullDataResponseMean_continuousOn | lemma | `Helpers/CausalBridgeMeasure.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.fullDataResponseMean_continuousOn (L361)` | fullDataResponseMean_continuousOn | unmatched |  |
| clampModel_iidSampling | lemma | `Helpers/SampleBlocks.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.clampModel_iidSampling (L31)` | clampModel_iidSampling | unmatched |  |
| aux_contStabilizedCoverage | definition | `THonestLength.lean:contStabilizedCoverage (L251)` | aux_contStabilizedCoverage | unmatched |  |
| aux_contStabilizedWorstLength | definition | `THonestLength.lean:contStabilizedWorstLength (L261)` | aux_contStabilizedWorstLength | unmatched |  |
| aux_contStabilizedWorstRisk | definition | `THonestLength.lean:contStabilizedWorstRisk (L242)` | aux_contStabilizedWorstRisk | unmatched |  |
| aux_RegimeConstants | definition | `Basic.lean:RegimeConstants (L226)` | aux_RegimeConstants | unmatched |  |
| aux_contCausalStabilizedCoverage | definition | `THonestLength.lean:contCausalStabilizedCoverage (L279)` | aux_contCausalStabilizedCoverage | unmatched |  |
| aux_contCausalStabilizedWorstLength | definition | `THonestLength.lean:contCausalStabilizedWorstLength (L288)` | aux_contCausalStabilizedWorstLength | unmatched |  |
| aux_contCausalStabilizedWorstRisk | definition | `THonestLength.lean:contCausalStabilizedWorstRisk (L271)` | aux_contCausalStabilizedWorstRisk | unmatched |  |
| aux_ContDesignConstants | definition | `Basic.lean:ContDesignConstants (L510)` | aux_ContDesignConstants | unmatched |  |
| structuralResponseExtension | definition | `Helpers/CausalBridgeIdentification.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.structuralResponseExtension (L28)` | structuralResponseExtension | unmatched |  |
| structuralResponseExtension_measurable | lemma | `Helpers/CausalBridgeIdentification.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.structuralResponseExtension_measurable (L38)` | structuralResponseExtension_measurable | unmatched |  |
| structuralResponseExtension_eq | lemma | `Helpers/CausalBridgeIdentification.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.structuralResponseExtension_eq (L52)` | structuralResponseExtension_eq | unmatched |  |
| fullDataResponseMean_setIntegral | lemma | `Helpers/CausalBridgeIdentification.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.fullDataResponseMean_setIntegral (L68)` | fullDataResponseMean_setIntegral | unmatched |  |
| continuous_mul_treatmentDensity_integrable | lemma | `Helpers/CausalBridgeIdentification.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.continuous_mul_treatmentDensity_integrable (L180)` | continuous_mul_treatmentDensity_integrable | unmatched |  |
| continuous_regression_eq_of_density_integrals | lemma | `Helpers/CausalBridgeIdentification.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.continuous_regression_eq_of_density_integrals (L212)` | continuous_regression_eq_of_density_integrals | unmatched |  |
| fullData_observed_setIntegral | lemma | `Helpers/CausalBridgeIdentification.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.fullData_observed_setIntegral (L256)` | fullData_observed_setIntegral | unmatched |  |
| fullDataResponseMean_eq_mu | lemma | `Helpers/CausalBridgeIdentification.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.fullDataResponseMean_eq_mu (L270)` | fullDataResponseMean_eq_mu | unmatched |  |
| causalClamp_pathwise | lemma | `Helpers/CausalBridgeIdentification.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.causalClamp_pathwise (L436)` | causalClamp_pathwise | unmatched |  |
| fullData_clampAtom_integral_eq | lemma | `Helpers/CausalBridgeIdentification.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.fullData_clampAtom_integral_eq (L468)` | fullData_clampAtom_integral_eq | unmatched |  |
| aux_BridgeClampModel | definition | `Basic.lean:BridgeClampModel (L583)` | aux_BridgeClampModel | unmatched |  |
| BridgeClampModel | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.BridgeClampModel (L583)` | BridgeClampModel | unmatched |  |
| ClampModel.toBridge | lemma | `(none)` | ClampModel.toBridge | unmatched |  |
| ContClampModel.toBridge | lemma | `(none)` | ContClampModel.toBridge | unmatched |  |
| BridgeFullDataClampModel | definition | `Basic.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.BridgeFullDataClampModel (L613)` | BridgeFullDataClampModel | unmatched |  |
| FullDataClampModel.toBridge | lemma | `(none)` | FullDataClampModel.toBridge | unmatched |  |
| ContFullDataClampModel.toBridge | lemma | `(none)` | ContFullDataClampModel.toBridge | unmatched |  |
| fullDataResponseMean_eq_contRegression | lemma | `Helpers/CausalBridgeIdentification.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.fullDataResponseMean_eq_contRegression (L340)` | fullDataResponseMean_eq_contRegression | unmatched |  |
| regressionVersion_setIntegral | lemma | `Helpers/RegressionVersion.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.regressionVersion_setIntegral (L213)` | regressionVersion_setIntegral | unmatched |  |
| standardBorelRegularConditionalLaw_mathlib | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.standardBorelRegularConditionalLaw_mathlib (L32)` | standardBorelRegularConditionalLaw_mathlib | unmatched |  |
| intervalLength_Icc_eq | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.intervalLength_Icc_eq (L285)` | intervalLength_Icc_eq | unmatched |  |
| stratumRadius_measurable | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.stratumRadius_measurable (L296)` | stratumRadius_measurable | unmatched |  |
| stabilizedInterval_radius_nonneg | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.stabilizedInterval_radius_nonneg (L316)` | stabilizedInterval_radius_nonneg | unmatched |  |
| stabilizedInterval_length_measurable | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.stabilizedInterval_length_measurable (L353)` | stabilizedInterval_length_measurable | unmatched |  |
| stabilizedInterval_observedMeasurable | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.stabilizedInterval_observedMeasurable (L388)` | stabilizedInterval_observedMeasurable | unmatched |  |
| stabilizedInterval_length_le_one | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.stabilizedInterval_length_le_one (L453)` | stabilizedInterval_length_le_one | unmatched |  |
| confidenceWorstLength_stabilizedInterval_le_ofReal | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.confidenceWorstLength_stabilizedInterval_le_ofReal (L486)` | confidenceWorstLength_stabilizedInterval_le_ofReal | unmatched |  |
| stabilizedInterval_uniformCoverage | lemma | `(none)` | stabilizedInterval_uniformCoverage | unmatched |  |
| observedMinimaxLength_le_confidenceWorstLength | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.observedMinimaxLength_le_confidenceWorstLength (L553)` | observedMinimaxLength_le_confidenceWorstLength | unmatched |  |
| causalStabilizedWorstRisk_eq_observed | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.causalStabilizedWorstRisk_eq_observed (L567)` | causalStabilizedWorstRisk_eq_observed | unmatched |  |
| causalStabilizedCoverage_eq_observed | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.causalStabilizedCoverage_eq_observed (L602)` | causalStabilizedCoverage_eq_observed | unmatched |  |
| causalStabilizedWorstLength_eq_confidenceWorstLength | lemma | `TCausalFrontierLift.lean:CausalSmith.Stat.LmtpThresholdAtomFrontier.causalStabilizedWorstLength_eq_confidenceWorstLength (L639)` | causalStabilizedWorstLength_eq_confidenceWorstLength | unmatched |  |
| aux_ProperProductChiSq | definition | `TMinimaxRisk.lean:ProperProductChiSq (L48)` | aux_ProperProductChiSq | unmatched |  |
