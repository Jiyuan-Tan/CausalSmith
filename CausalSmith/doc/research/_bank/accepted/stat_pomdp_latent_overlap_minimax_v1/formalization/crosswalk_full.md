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
| P-1 | definition | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.LatentOverlapClass (L274)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.targetValue (L295)` | P-2 | equivalent |  |
| P-3 | definition | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.minimaxRisk (L398)` | P-3 | equivalent |  |
| P-4 | definition | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.phiwEstimator (L323)` | P-4 | equivalent |  |
| P-5 | definition | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.historyDepth (L408)` | P-5 | equivalent |  |
| P-6 | definition | `Helpers/SignedDepth.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFamily (L115)` | P-6 | equivalent |  |
| P-7 | definition | `Helpers/ObservedFilter.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.filterQuantities (L166)` | P-7 | equivalent |  |
| P-8 | definition | `Helpers/LocalFrontier.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.localFrontierHandle (L111)` | P-8 | equivalent |  |
| P-9 | definition | `Helpers/InsulinGridCore/Model.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.insulinGrid (L112)` | P-9 | equivalent |  |
| P-10 | definition | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.overlapRadius (L415)` | P-10 | equivalent |  |
| P-11 | definition | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.radiusAdaptiveDepth (L420)` | P-11 | equivalent |  |
| T-1 | theorem | `TFixedCMinimax.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.fixed_c_minimax (L17)` | T-1 | equivalent |  |
| T-2 | theorem | `TUnitOverlapBoundary.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.unit_overlap_boundary (L16)` | T-2 | equivalent |  |
| T-3 | theorem | `TFiniteInsulinDemonstration.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.finite_insulin_demonstration (L13)` | T-3 | equivalent |  |
| T-4 | theorem | `TShrinkingOverlapFrontier.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.shrinking_overlap_frontier (L28)` | T-4 | equivalent |  |
| T-5 | theorem | `TUniformOverlapFrontier.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.uniform_overlap_frontier (L25)` | T-5 | equivalent |  |
| L-1 | lemma | `Helpers/PhiwUpper.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.phiw_upper (L16)` | L-1 | equivalent |  |
| L-2 | lemma | `Helpers/SignedDepthMembership.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_membership (L267)` | L-2 | equivalent |  |
| L-3 | lemma | `Helpers/ObservedKL.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.observed_path_kl (L518)` | L-3 | equivalent |  |
| L-4 | lemma | `Helpers/BiasVariance.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.radius_sensitive_phiw (L389)` | L-4 | equivalent |  |
| L-5 | lemma | `Helpers/ObservedKL.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.radius_explicit_observed_kl (L616)` | L-5 | equivalent |  |
| L-6 | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.uniform_parametric_floor (L979)` | L-6 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.PomdpKernelLaw (L213)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.SequentialIgnorability (L223)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.StationaryStart (L234)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.BoundedReward (L243)` | A-4 | equivalent |  |
| A-5 | assumption | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.PolicyOverlap (L249)` | A-5 | equivalent |  |
| A-6 | assumption | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.UniformContraction (L255)` | A-6 | equivalent |  |
| A-7 | assumption | `Basic.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.LatentStationaryOverlap (L265)` | A-7 | equivalent |  |
| aux_frontierRate | definition | `TUniformOverlapFrontier.lean:frontierRate (L15)` | aux_frontierRate | unmatched |  |
| aux_IsStationary | definition | `Basic.lean:IsStationary (L173)` | aux_IsStationary | unmatched |  |
| aux_localFrontierRate | definition | `TShrinkingOverlapFrontier.lean:localFrontierRate (L14)` | aux_localFrontierRate | unmatched |  |
| aux_ModelIndex | definition | `Basic.lean:ModelIndex (L375)` | aux_ModelIndex | unmatched |  |
| aux_observedRisk | definition | `Basic.lean:observedRisk (L389)` | aux_observedRisk | unmatched |  |
| aux_phiwObservable | definition | `Basic.lean:phiwObservable (L340)` | aux_phiwObservable | unmatched |  |
| aux_PolicyVector | definition | `Basic.lean:PolicyVector (L163)` | aux_PolicyVector | unmatched |  |
| aux_ProbabilityVector | definition | `Basic.lean:ProbabilityVector (L159)` | aux_ProbabilityVector | unmatched |  |
| aux_rateExponent | definition | `Basic.lean:rateExponent (L403)` | aux_rateExponent | unmatched |  |
| aux_RawPomdpExperiment | definition | `Basic.lean:RawPomdpExperiment (L46)` | aux_RawPomdpExperiment | unmatched |  |
| aux_shrinkingDepth | definition | `TShrinkingOverlapFrontier.lean:shrinkingDepth (L19)` | aux_shrinkingDepth | unmatched |  |
| aux_FiniteRewardModel | definition | `(none)` | aux_FiniteRewardModel | unmatched |  |
| aux_obsLaw | definition | `Basic.lean:obsLaw (L95)` | aux_obsLaw | unmatched |  |
| aux_RawEstimator | definition | `Basic.lean:RawEstimator (L329)` | aux_RawEstimator | unmatched |  |
| aux_rawObservedRisk | definition | `Basic.lean:rawObservedRisk (L384)` | aux_rawObservedRisk | unmatched |  |
| aux_signedDepthModel | definition | `(none)` | aux_signedDepthModel | unmatched |  |
| rademacher_kl_le_chiSq | lemma | `Helpers/ObservedKL.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.rademacher_kl_le_chiSq (L23)` | rademacher_kl_le_chiSq | unmatched |  |
| ass:filler:15:def:model-class:23:behavior_stationary_law | assumption | `(none)` | ass:filler:15:def:model-class:23:behavior_stationary_law | unmatched |  |
| ass:filler:15:def:model-class:21:target_stationary_law | assumption | `(none)` | ass:filler:15:def:model-class:21:target_stationary_law | unmatched |  |
| parametricAmplitude_mem | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricAmplitude_mem (L435)` | parametricAmplitude_mem | unmatched |  |
| parametricPair_kernel_toReal | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_kernel_toReal (L452)` | parametricPair_kernel_toReal | unmatched |  |
| parametricPair_policy_toReal | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_policy_toReal (L475)` | parametricPair_policy_toReal | unmatched |  |
| parametricPair_obsPMF_toReal | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_obsPMF_toReal (L487)` | parametricPair_obsPMF_toReal | unmatched |  |
| parametricEpochPMF | definition | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricEpochPMF (L541)` | parametricEpochPMF | unmatched |  |
| parametricEpochPMF_toReal | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricEpochPMF_toReal (L547)` | parametricEpochPMF_toReal | unmatched |  |
| parametricPair_obsPMF_eq_pi | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_obsPMF_eq_pi (L567)` | parametricPair_obsPMF_eq_pi | unmatched |  |
| parametricEpochEquiv | definition | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricEpochEquiv (L586)` | parametricEpochEquiv | unmatched |  |
| parametricEpochSource | definition | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricEpochSource (L600)` | parametricEpochSource | unmatched |  |
| parametricEpochPMF_eq_map_source | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricEpochPMF_eq_map_source (L607)` | parametricEpochPMF_eq_map_source | unmatched |  |
| parametricEpoch_klDiv_le | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricEpoch_klDiv_le (L658)` | parametricEpoch_klDiv_le | unmatched |  |
| parametricEpoch_fullSupport | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricEpoch_fullSupport (L746)` | parametricEpoch_fullSupport | unmatched |  |
| parametricPair_finiteObs_klDiv_le | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_finiteObs_klDiv_le (L758)` | parametricPair_finiteObs_klDiv_le | unmatched |  |
| parametricPair_observed_klDiv_le | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_observed_klDiv_le (L796)` | parametricPair_observed_klDiv_le | unmatched |  |
| parametricPair_kernelMean | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_kernelMean (L804)` | parametricPair_kernelMean | unmatched |  |
| parametricPair_targetValue | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_targetValue (L831)` | parametricPair_targetValue | unmatched |  |
| historyDepth_rate | lemma | `Helpers/BiasVariance.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.historyDepth_rate (L441)` | historyDepth_rate | unmatched |  |
| radiusAdaptiveDepth_rate | lemma | `Helpers/BiasVariance.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.radiusAdaptiveDepth_rate (L539)` | radiusAdaptiveDepth_rate | unmatched |  |
| signedDepth_eps_bound | lemma | `Helpers/SignedDepthMembership.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_eps_bound (L12)` | signedDepth_eps_bound | unmatched |  |
| signedDepth_initial_apply | lemma | `Helpers/SignedDepthMembership.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_initial_apply (L21)` | signedDepth_initial_apply | unmatched |  |
| signedDepth_stationary_overlap_base | lemma | `Helpers/SignedDepthMembership.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_stationary_overlap_base (L33)` | signedDepth_stationary_overlap_base | unmatched |  |
| signedDepth_policyOverlap | lemma | `Helpers/SignedDepthMembership.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_policyOverlap (L88)` | signedDepth_policyOverlap | unmatched |  |
| signedDepth_uniformContraction | lemma | `Helpers/SignedDepthMembership.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_uniformContraction (L113)` | signedDepth_uniformContraction | unmatched |  |
| signedDepth_rewardRegression | lemma | `Helpers/SignedDepthMembership.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_rewardRegression (L131)` | signedDepth_rewardRegression | unmatched |  |
| signedDepth_targetValue | lemma | `Helpers/SignedDepthMembership.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_targetValue (L172)` | signedDepth_targetValue | unmatched |  |
| signedDepth_behavior_stationary_eq_init | lemma | `Helpers/SignedDepthMembership.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_behavior_stationary_eq_init (L206)` | signedDepth_behavior_stationary_eq_init | unmatched |  |
| signedDepthStationaryWeight | definition | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthStationaryWeight (L11)` | signedDepthStationaryWeight | unmatched |  |
| actionOnePolicy_policyVector | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.actionOnePolicy_policyVector (L17)` | actionOnePolicy_policyVector | unmatched |  |
| signedDepthStationaryWeight_probabilityVector | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthStationaryWeight_probabilityVector (L26)` | signedDepthStationaryWeight_probabilityVector | unmatched |  |
| signedDepth_policyKernel_apply | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_policyKernel_apply (L75)` | signedDepth_policyKernel_apply | unmatched |  |
| depthMass_reset_balance | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.depthMass_reset_balance (L116)` | depthMass_reset_balance | unmatched |  |
| latentDepth_le | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.latentDepth_le (L156)` | latentDepth_le | unmatched |  |
| depthMass_succ | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.depthMass_succ (L161)` | depthMass_succ | unmatched |  |
| signedDepthRefresh | definition | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthRefresh (L168)` | signedDepthRefresh | unmatched |  |
| signedDepthResidualKernel | definition | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthResidualKernel (L173)` | signedDepthResidualKernel | unmatched |  |
| signedDepthResidualKernel_probabilityVector | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthResidualKernel_probabilityVector (L181)` | signedDepthResidualKernel_probabilityVector | unmatched |  |
| signedDepth_policyKernel_refresh | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_policyKernel_refresh (L240)` | signedDepth_policyKernel_refresh | unmatched |  |
| signedDepth_uniformContraction_actionOne | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_uniformContraction_actionOne (L259)` | signedDepth_uniformContraction_actionOne | unmatched |  |
| signedDepthStationaryWeight_isStationary | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthStationaryWeight_isStationary (L274)` | signedDepthStationaryWeight_isStationary | unmatched |  |
| signedDepth_stationaryLaw_apply | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_stationaryLaw_apply (L348)` | signedDepth_stationaryLaw_apply | unmatched |  |
| signedDepth_behaviour_eq_actionOne | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_behaviour_eq_actionOne (L371)` | signedDepth_behaviour_eq_actionOne | unmatched |  |
| signedDepth_target_eq_actionOne | lemma | `Helpers/SignedDepthStationarity.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_target_eq_actionOne (L383)` | signedDepth_target_eq_actionOne | unmatched |  |
| sqRisk_clipUnit_le_variance_add_bias_sq | lemma | `Helpers/BiasVariance.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.sqRisk_clipUnit_le_variance_add_bias_sq (L78)` | sqRisk_clipUnit_le_variance_add_bias_sq | unmatched |  |
| embed_initial_marginal | lemma | `Helpers/FinitePathMarginal.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.embed_initial_marginal (L234)` | embed_initial_marginal | unmatched |  |
| embed_stationaryStart | lemma | `Helpers/FinitePathMarginal.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.embed_stationaryStart (L296)` | embed_stationaryStart | unmatched |  |
| signedDepth_stationaryStart | lemma | `Helpers/SignedDepthMembership.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_stationaryStart (L230)` | signedDepth_stationaryStart | unmatched |  |
| parametricPair_stationaryStart | lemma | `Helpers/TwoPoint.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_stationaryStart (L232)` | parametricPair_stationaryStart | unmatched |  |
| embed_kernel_bounded_reward | lemma | `(none)` | embed_kernel_bounded_reward | unmatched |  |
| localFrontier_stationaryRatio | lemma | `Helpers/LocalFrontier.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.localFrontier_stationaryRatio (L70)` | localFrontier_stationaryRatio | unmatched |  |
| rewardRegression_abs_le_one_of_behaviorSupport | lemma | `Helpers/StationaryRewardSupport.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.rewardRegression_abs_le_one_of_behaviorSupport (L15)` | rewardRegression_abs_le_one_of_behaviorSupport | unmatched |  |
| behaviorSupport_closed_policyKernel | lemma | `Helpers/StationaryRewardSupport.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.behaviorSupport_closed_policyKernel (L125)` | behaviorSupport_closed_policyKernel | unmatched |  |
| markovOperatorIter_congr_on_behaviorSupport | lemma | `Helpers/StationaryRewardSupport.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.markovOperatorIter_congr_on_behaviorSupport (L172)` | markovOperatorIter_congr_on_behaviorSupport | unmatched |  |
| integral_curState_eq_behaviorStationary | lemma | `Helpers/StationaryRewardSupport.lean:CausalSmith.Stat.PomdpLatentOverlapMinimax.integral_curState_eq_behaviorStationary (L195)` | integral_curState_eq_behaviorStationary | unmatched |  |
