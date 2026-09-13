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
| P-1 | definition | `Helpers/FiniteSCM.lean:CausalSmith.SCM.ProxyTargetspanTransport.PositiveLatentShiftClass (L100)` | P-1 | equivalent |  |
| P-2 | definition | `Helpers/Fibers.lean:CausalSmith.SCM.ProxyTargetspanTransport.compatibleFiber (L22)` | P-2 | equivalent |  |
| P-3 | definition | `Helpers/Fibers.lean:CausalSmith.SCM.ProxyTargetspanTransport.balancingFiber (L29)` | P-3 | equivalent |  |
| P-4 | definition | `Helpers/Fibers.lean:CausalSmith.SCM.ProxyTargetspanTransport.failureSeparator (L37)` | P-4 | equivalent |  |
| P-5 | definition | `Helpers/Perturbation.lean:CausalSmith.SCM.ProxyTargetspanTransport.outcomeNullPerturbation (L24)` | P-5 | equivalent |  |
| P-6 | definition | `Helpers/Witness.lean:CausalSmith.SCM.ProxyTargetspanTransport.rankDeficientSuccessWitness (L30)` | P-6 | equivalent |  |
| P-7 | definition | `Helpers/Fibers.lean:CausalSmith.SCM.ProxyTargetspanTransport.unconditionalBalancingMoments (L45)` | P-7 | equivalent |  |
| P-8 | definition | `Helpers/Fibers.lean:CausalSmith.SCM.ProxyTargetspanTransport.unconditionalWeightMap (L68)` | P-8 | equivalent |  |
| P-9 | definition | `Helpers/Sampling.lean:CausalSmith.SCM.ProxyTargetspanTransport.concentrationProjectionSet (L253)` | P-9 | equivalent |  |
| P-10 | definition | `Helpers/TriangularArray.lean:CausalSmith.SCM.ProxyTargetspanTransport.StudentizedArrayClass (L81)` | P-10 | equivalent |  |
| P-11 | definition | `Helpers/RegularBenchmark.lean:CausalSmith.SCM.ProxyTargetspanTransport.StronglyIdentifiedSubmodel (L134)` | P-11 | equivalent |  |
| P-12 | definition | `Helpers/TruncatedSVD.lean:CausalSmith.SCM.ProxyTargetspanTransport.regularWaldFunctional (L79)` | P-12 | equivalent |  |
| P-13 | definition | `Helpers/RegularBenchmark.lean:CausalSmith.SCM.ProxyTargetspanTransport.regularWaldEstimator (L156)` | P-13 | equivalent |  |
| P-14 | definition | `Helpers/RegularBenchmark.lean:CausalSmith.SCM.ProxyTargetspanTransport.regularWaldVariance (L163)` | P-14 | equivalent |  |
| P-15 | definition | `Helpers/RegularBenchmark.lean:CausalSmith.SCM.ProxyTargetspanTransport.regularWaldInterval (L180)` | P-15 | equivalent |  |
| P-16 | definition | `Helpers/SetGeometry.lean:CausalSmith.SCM.ProxyTargetspanTransport.euclideanDiameter (L14)` | P-16 | unmatched |  |
| P-17 | definition | `Helpers/SetGeometry.lean:CausalSmith.SCM.ProxyTargetspanTransport.euclideanHausdorffDistance (L27)` | P-17 | unmatched |  |
| T-1 | theorem | `TPositiveFullLawConverse.lean:CausalSmith.SCM.ProxyTargetspanTransport.positive_full_law_converse (L19)` | T-1 | equivalent |  |
| T-2 | theorem | `TTargetSpanIff.lean:CausalSmith.SCM.ProxyTargetspanTransport.target_span_iff (L66)` | T-2 | equivalent |  |
| T-3 | theorem | `TStrictFullrankExtension.lean:CausalSmith.SCM.ProxyTargetspanTransport.strict_fullrank_extension (L72)` | T-3 | equivalent |  |
| T-4 | theorem | `TFiniteSampleProjectionCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.finite_sample_projection_coverage (L19)` | T-4 | equivalent |  |
| T-5 | theorem | `TStudentizedUniformProjection.lean:CausalSmith.SCM.ProxyTargetspanTransport.no_uniform_studentized_wald_adaptation (L78)` | T-5 | equivalent |  |
| L-1 | lemma | `Basic.lean:CausalSmith.SCM.ProxyTargetspanTransport.observable_factorization (L19)` | L-1 | equivalent |  |
| A-1 | assumption | `Helpers/FiniteSCM.lean:CausalSmith.SCM.ProxyTargetspanTransport.LatentShiftFactorization (L72)` | A-1 | equivalent |  |
| A-2 | assumption | `Helpers/FiniteSCM.lean:CausalSmith.SCM.ProxyTargetspanTransport.TargetMechanismInvariance (L78)` | A-2 | equivalent |  |
| A-3 | assumption | `Helpers/FiniteSCM.lean:CausalSmith.SCM.ProxyTargetspanTransport.StrictPrimitivePositivity (L83)` | A-3 | equivalent |  |
| A-4 | assumption | `Helpers/FiniteSCM.lean:CausalSmith.SCM.ProxyTargetspanTransport.ProxyChannelInjectivity (L93)` | A-4 | equivalent |  |
| A-5 | assumption | `Helpers/Sampling.lean:CausalSmith.SCM.ProxyTargetspanTransport.SourceIidSampling (L151)` | A-5 | equivalent |  |
| A-6 | assumption | `Helpers/Sampling.lean:CausalSmith.SCM.ProxyTargetspanTransport.TargetIidSampling (L158)` | A-6 | equivalent |  |
| A-7 | assumption | `Helpers/TriangularArray.lean:CausalSmith.SCM.ProxyTargetspanTransport.TriangularAllocation (L46)` | A-7 | equivalent |  |
| A-8 | assumption | `Helpers/TriangularArray.lean:CausalSmith.SCM.ProxyTargetspanTransport.TriangularSourceIidSampling (L54)` | A-8 | equivalent |  |
| A-9 | assumption | `Helpers/TriangularArray.lean:CausalSmith.SCM.ProxyTargetspanTransport.TriangularTargetIidSampling (L63)` | A-9 | equivalent |  |
| A-10 | assumption | `Helpers/TriangularArray.lean:CausalSmith.SCM.ProxyTargetspanTransport.ArrayTargetSpan (L72)` | A-10 | equivalent |  |
| A-11 | assumption | `Helpers/RegularBenchmark.lean:CausalSmith.SCM.ProxyTargetspanTransport.RegularFixedRank (L100)` | A-11 | equivalent |  |
| A-12 | assumption | `Helpers/RegularBenchmark.lean:CausalSmith.SCM.ProxyTargetspanTransport.RegularSingularGap (L105)` | A-12 | equivalent |  |
| A-13 | assumption | `Helpers/RegularBenchmark.lean:CausalSmith.SCM.ProxyTargetspanTransport.RegularTargetSpan (L112)` | A-13 | equivalent |  |
| A-14 | assumption | `Helpers/RegularBenchmark.lean:CausalSmith.SCM.ProxyTargetspanTransport.RegularCellFloor (L117)` | A-14 | equivalent |  |
| A-15 | assumption | `Helpers/RegularBenchmark.lean:CausalSmith.SCM.ProxyTargetspanTransport.RegularPositiveVariance (L124)` | A-15 | equivalent |  |
| aux_condOutcomeVector | definition | `Helpers/FiniteSCM.lean:condOutcomeVector (L137)` | aux_condOutcomeVector | unmatched |  |
| aux_condProxyMatrix | definition | `Helpers/FiniteSCM.lean:condProxyMatrix (L127)` | aux_condProxyMatrix | unmatched |  |
| aux_empOutcomeMoment | definition | `(none)` | aux_empOutcomeMoment | unmatched |  |
| aux_empProxyMoment | definition | `(none)` | aux_empProxyMoment | unmatched |  |
| aux_empTargetProxy | definition | `(none)` | aux_empTargetProxy | unmatched |  |
| aux_interventionalProb | definition | `Helpers/FiniteSCM.lean:interventionalProb (L142)` | aux_interventionalProb | unmatched |  |
| aux_LatentShiftSCM | definition | `Helpers/FiniteSCM.lean:LatentShiftSCM (L35)` | aux_LatentShiftSCM | unmatched |  |
| aux_perturbedModel | definition | `Helpers/Perturbation.lean:perturbedModel (L42)` | aux_perturbedModel | unmatched |  |
| aux_ConfidenceSetSeq | definition | `Helpers/TriangularArray.lean:ConfidenceSetSeq (L136)` | aux_ConfidenceSetSeq | unmatched |  |
| aux_constRowLaw | definition | `Helpers/TriangularArray.lean:constRowLaw (L164)` | aux_constRowLaw | unmatched |  |
| aux_finEmpOutcomeMoment | definition | `Helpers/Sampling.lean:finEmpOutcomeMoment (L171)` | aux_finEmpOutcomeMoment | unmatched |  |
| aux_finEmpProxyMoment | definition | `Helpers/Sampling.lean:finEmpProxyMoment (L164)` | aux_finEmpProxyMoment | unmatched |  |
| aux_finEmpTargetProxy | definition | `Helpers/Sampling.lean:finEmpTargetProxy (L178)` | aux_finEmpTargetProxy | unmatched |  |
| aux_rowInterventionalProb | definition | `Helpers/TriangularArray.lean:rowInterventionalProb (L95)` | aux_rowInterventionalProb | unmatched |  |
| aux_stronglyIdentifiedSubmodelSet | definition | `Helpers/RegularBenchmark.lean:stronglyIdentifiedSubmodelSet (L148)` | aux_stronglyIdentifiedSubmodelSet | unmatched |  |
| aux_studentizedArrayClassSet | definition | `Helpers/TriangularArray.lean:studentizedArrayClassSet (L89)` | aux_studentizedArrayClassSet | unmatched |  |
| aux_TwoSampleArray | definition | `Helpers/TriangularArray.lean:TwoSampleArray (L29)` | aux_TwoSampleArray | unmatched |  |
| aux_UniformArrayCoverage | definition | `Helpers/TriangularArray.lean:UniformArrayCoverage (L153)` | aux_UniformArrayCoverage | unmatched |  |
| aux_waldSet | definition | `TStudentizedUniformProjection.lean:waldSet (L64)` | aux_waldSet | unmatched |  |
| aux_RankIndex | definition | `Helpers/TruncatedSVD.lean:RankIndex (L21)` | aux_RankIndex | unmatched |  |
| aux_twoSampleLaw | definition | `Helpers/Sampling.lean:twoSampleLaw (L118)` | aux_twoSampleLaw | unmatched |  |
| multinomialCov_quadForm_nonneg | lemma | `Helpers/RegularBenchmark.lean:CausalSmith.SCM.ProxyTargetspanTransport.multinomialCov_quadForm_nonneg (L43)` | multinomialCov_quadForm_nonneg | unmatched |  |
| fullrank_implies_target_span | lemma | `TStrictFullrankExtension.lean:CausalSmith.SCM.ProxyTargetspanTransport.fullrank_implies_target_span (L17)` | fullrank_implies_target_span | unmatched |  |
| outcomeNullPerturbation_sum | lemma | `Helpers/Perturbation.lean:CausalSmith.SCM.ProxyTargetspanTransport.outcomeNullPerturbation_sum (L143)` | outcomeNullPerturbation_sum | unmatched |  |
| perturbedModel_interventionalProb_sub | lemma | `Helpers/Perturbation.lean:CausalSmith.SCM.ProxyTargetspanTransport.perturbedModel_interventionalProb_sub (L174)` | perturbedModel_interventionalProb_sub | unmatched |  |
| rankDeficientSuccessWitness_positive | lemma | `Helpers/Witness.lean:CausalSmith.SCM.ProxyTargetspanTransport.rankDeficientSuccessWitness_positive (L101)` | rankDeficientSuccessWitness_positive | unmatched |  |
| rankDeficientSuccessWitness_condProxy_rank | lemma | `Helpers/Witness.lean:CausalSmith.SCM.ProxyTargetspanTransport.rankDeficientSuccessWitness_condProxy_rank (L126)` | rankDeficientSuccessWitness_condProxy_rank | unmatched |  |
| rankDeficientSuccessWitness_latentPosterior_zero | lemma | `Helpers/Witness.lean:CausalSmith.SCM.ProxyTargetspanTransport.rankDeficientSuccessWitness_latentPosterior_zero (L145)` | rankDeficientSuccessWitness_latentPosterior_zero | unmatched |  |
| rankDeficientSuccessWitness_latentPosterior_one | lemma | `Helpers/Witness.lean:CausalSmith.SCM.ProxyTargetspanTransport.rankDeficientSuccessWitness_latentPosterior_one (L155)` | rankDeficientSuccessWitness_latentPosterior_one | unmatched |  |
| rankDeficientSuccessWitness_target_span | lemma | `Helpers/Witness.lean:CausalSmith.SCM.ProxyTargetspanTransport.rankDeficientSuccessWitness_target_span (L165)` | rankDeficientSuccessWitness_target_span | unmatched |  |
| fullrank_source_column_space_eq_proxy_column_space | lemma | `TStrictFullrankExtension.lean:CausalSmith.SCM.ProxyTargetspanTransport.fullrank_source_column_space_eq_proxy_column_space (L43)` | fullrank_source_column_space_eq_proxy_column_space | unmatched |  |
| exists_failureSeparator_of_balancingFiber_empty | lemma | `TTargetSpanIff.lean:CausalSmith.SCM.ProxyTargetspanTransport.exists_failureSeparator_of_balancingFiber_empty (L17)` | exists_failureSeparator_of_balancingFiber_empty | unmatched |  |
| identified_value_of_balancing | lemma | `TTargetSpanIff.lean:CausalSmith.SCM.ProxyTargetspanTransport.identified_value_of_balancing (L49)` | identified_value_of_balancing | unmatched |  |
| coverageProxyIndicator | definition | `Helpers/FiniteSampleCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.coverageProxyIndicator (L15)` | coverageProxyIndicator | unmatched |  |
| integral_coverageProxyIndicator | lemma | `Helpers/FiniteSampleCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.integral_coverageProxyIndicator (L22)` | integral_coverageProxyIndicator | unmatched |  |
| source_proxy_coordinate_tail | lemma | `Helpers/FiniteSampleCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.source_proxy_coordinate_tail (L42)` | source_proxy_coordinate_tail | unmatched |  |
| coverageOutcomeIndicator | definition | `Helpers/FiniteSampleCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.coverageOutcomeIndicator (L84)` | coverageOutcomeIndicator | unmatched |  |
| integral_coverageOutcomeIndicator | lemma | `Helpers/FiniteSampleCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.integral_coverageOutcomeIndicator (L91)` | integral_coverageOutcomeIndicator | unmatched |  |
| source_outcome_coordinate_tail | lemma | `Helpers/FiniteSampleCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.source_outcome_coordinate_tail (L115)` | source_outcome_coordinate_tail | unmatched |  |
| target_proxy_coordinate_tail | lemma | `Helpers/FiniteSampleCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.target_proxy_coordinate_tail (L157)` | target_proxy_coordinate_tail | unmatched |  |
| radius_tail_exact | lemma | `Helpers/FiniteSampleCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.radius_tail_exact (L199)` | radius_tail_exact | unmatched |  |
| simultaneous_coordinate_concentration | lemma | `Helpers/FiniteSampleCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.simultaneous_coordinate_concentration (L219)` | simultaneous_coordinate_concentration | unmatched |  |
| interventionalProb_mem_unitInterval | lemma | `Helpers/FiniteSampleCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.interventionalProb_mem_unitInterval (L305)` | interventionalProb_mem_unitInterval | unmatched |  |
| mem_concentrationProjectionSet_of_good | lemma | `Helpers/FiniteSampleCoverage.lean:CausalSmith.SCM.ProxyTargetspanTransport.mem_concentrationProjectionSet_of_good (L342)` | mem_concentrationProjectionSet_of_good | unmatched |  |
