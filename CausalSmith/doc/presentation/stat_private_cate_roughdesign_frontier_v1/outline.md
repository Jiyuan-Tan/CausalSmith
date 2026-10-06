# Title
**Private estimation and honest inference for conditional treatment effects with rough nuisance functions**

**Contribution statement.** For binary observational records with fixed overlap, a Lipschitz treatment effect, Hölder-one-tenth propensity and control regressions, and an unknown measurable density bounded above and away from zero, the paper characterizes the common minimax order of pointwise absolute estimation error and expected length of uniformly honest 90% connected confidence intervals under pure differential privacy, attained by a single release of within-cell pair moments.

env_overrides: def:private-ratio=algorithmv, def:public-tuning=algorithmv, def:interval-handle=algorithmv, prop:regime-and-sanity=propositionv

# Notation

Each row identifies a mathematical object and its definition home. “Gap” denotes a required anchored presentation definition; it does not authorize an additional mathematical claim. Repeated applications of the same function or operator share one row.

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(P\) | \(P\) | Causal probability law for the covariate, treatment, potential outcomes, and observed outcome | def:complete-model |
| \(\mathcal P\) | \(\mathcal P\) | Class of causal laws satisfying the binary experiment, identification, density, overlap, and smoothness restrictions | def:complete-model |
| \(\operatorname{Prob}([0,1]\times\{0,1\}\times\{0,1\}^2\times\{0,1\})\) | \(\operatorname{Prob}([0,1]\times\{0,1\}\times\{0,1\}^2\times\{0,1\})\) | Borel probability measures on the causal-record space | def:complete-model |
| \(X\) | \(X\) | Scalar covariate in the causal record | Gap: causal-record coordinates |
| \(A\) | \(A\) | Binary treatment indicator in the causal record | Gap: causal-record coordinates |
| \(Y^{\mathrm{pot}}\) | \(Y^{\mathrm{pot}}\) | Ordered pair of binary potential outcomes | Gap: causal-record coordinates |
| \(Y(0)\) | \(Y(0)\) | Control potential outcome | Gap: causal-record coordinates |
| \(Y(1)\) | \(Y(1)\) | Treatment potential outcome | Gap: causal-record coordinates |
| \(Y(A)\) | \(Y(A)\) | Potential outcome selected by the realized treatment | Gap: causal-record coordinates |
| \(Y\) | \(Y\) | Observed binary outcome | Gap: causal-record coordinates |
| \(P_X\) | \(P_X\) | Covariate marginal of the causal law | Gap: observed and covariate marginals |
| \(P^{\mathrm{obs}}\) | \(P^{\mathrm{obs}}\) | Observed-record marginal of the causal law | Gap: observed and covariate marginals |
| \(\mathcal O^n\) | \(\mathcal O^n\) | Space of ordered datasets of observed records | Gap: observation and dataset spaces |
| \(D\) | \(D\) | Ordered dataset of observed records | Gap: observation and dataset spaces |
| \(D^{\prime}\) | \(D^{\prime}\) | Dataset compared with the original dataset under replacement adjacency | Gap: observation and dataset spaces |
| \(\mathcal L(D)\) | \(\mathcal L(D)\) | Probability distribution of the dataset | Gap: observation and dataset spaces |
| \(f_P(x)\) | \(f_P(x)\) | Version of the covariate density with respect to Lebesgue measure | Gap: observational functions |
| \(e_P(x)\) | \(e_P(x)\) | Selected version of the conditional treatment probability | Gap: observational functions |
| \(\mu_{0,P}(x)\) | \(\mu_{0,P}(x)\) | Selected version of the conditional control-outcome mean | Gap: observational functions |
| \(\tau_P(x)\) | \(\tau_P(x)\) | Selected observational treatment-effect contrast | Gap: observational functions |
| \(L\) | \(L\) | Common radius in the nuisance and contrast smoothness restrictions | Gap: model radius |
| \(x_0\) | \(x_0\) | Covariate location at which the contrast is evaluated | Gap: point target |
| \(\theta(P)\) | \(\theta(P)\) | Pointwise treatment-effect target associated with a member law | Gap: point target |
| \(d_{\mathrm H}(D,D^{\prime})\) | \(d_{\mathrm H}(D,D^{\prime})\) | Number of record positions at which two datasets differ | Gap: replacement distance |
| \(\mathcal B\) | \(\mathcal B\) | Standard Borel output space for a randomized release | Gap: release spaces and laws |
| \(\mathcal B(\mathcal B)\) | \(\mathcal B(\mathcal B)\) | Borel sigma-algebra of the output space | Gap: release spaces and laws |
| \(M\) | \(M\) | Everywhere-defined Markov kernel from datasets to the output space | def:private-kernels |
| \(M(D,E)\) | \(M(D,E)\) | Conditional probability that the release belongs to a measurable output event | def:private-kernels |
| \(\mathfrak M_{n,\epsilon}(\mathcal B)\) | \(\mathfrak M_{n,\epsilon}(\mathcal B)\) | Randomized releases satisfying pure replacement differential privacy | def:private-kernels |
| \(T(D)\) | \(T(D)\) | Scalar output of a private randomized estimator | def:risk-criterion |
| \(R_{n,\epsilon}\) | \(R_{n,\epsilon}\) | Minimax maximal expected absolute error over private scalar releases | def:risk-criterion |
| \(E_{(P^{\mathrm{obs}})^{\otimes n},T}\) | \(E_{(P^{\mathrm{obs}})^{\otimes n},T}\) | Expectation integrating the observed sample and estimator randomization | def:risk-criterion |
| \(\mathcal I\) | \(\mathcal I\) | Standard Borel space of connected Borel intervals | Gap: interval output space |
| \(I(D)\) | \(I(D)\) | Connected interval output of a private randomized procedure | def:interval-criterion |
| \(H_{n,\epsilon}\) | \(H_{n,\epsilon}\) | Minimax maximal expected interval length subject to uniform 90% coverage | def:interval-criterion |
| \(E_{(P^{\mathrm{obs}})^{\otimes n},I}\) | \(E_{(P^{\mathrm{obs}})^{\otimes n},I}\) | Expectation integrating the observed sample and interval randomization | def:interval-criterion |
| \(\Pr_{(P^{\mathrm{obs}})^{\otimes n},I}\) | \(\Pr_{(P^{\mathrm{obs}})^{\otimes n},I}\) | Probability integrating the observed sample and interval randomization | def:interval-criterion |
| \(\operatorname{Leb}(I(D))\) | \(\operatorname{Leb}(I(D))\) | Lebesgue length of the released interval | def:interval-criterion |
| \(h\) | \(h\) | Public radius of the local covariate window | Gap: public cell geometry |
| \(k\) | \(k\) | Public number of equal cells in the local window | Gap: public cell geometry |
| \(\delta\) | \(\delta\) | Cell width equal to twice the localization radius divided by the cell count | def:private-ratio |
| \(s\) | \(s\) | Number of records in an occupied public cell | def:private-ratio |
| \(S_N(D)\) | \(S_N(D)\) | Sum of count-weighted within-cell treatment–outcome pair contributions | def:private-ratio |
| \(S_D(D)\) | \(S_D(D)\) | Sum of count-weighted within-cell treatment pair contributions | def:private-ratio |
| \(\xi_N\) | \(\xi_N\) | Numerator Laplace noise in the joint release | def:private-ratio |
| \(\xi_D\) | \(\xi_D\) | Independent denominator Laplace noise in the joint release | def:private-ratio |
| \(\widetilde S\) | \(\widetilde S\) | Joint release of the noisy numerator and denominator statistics | def:private-ratio |
| \(\widetilde S_N\) | \(\widetilde S_N\) | Numerator coordinate of the joint release | def:private-ratio |
| \(\widetilde S_D\) | \(\widetilde S_D\) | Denominator coordinate of the joint release | def:private-ratio |
| \(\mathcal A\) | \(\mathcal A\) | Public occupancy scale used in the denominator floor and error envelope | Gap: public error envelopes |
| \(d_0\) | \(d_0\) | Positive public denominator floor determined by the occupancy scale | def:private-ratio |
| \(\operatorname{clip}_{[-1,1]}\) | \(\operatorname{clip}_{[-1,1]}\) | Clipping operator onto the target range | Gap: clipping operator |
| \(\widehat T_{h,k}\) | \(\widehat T_{h,k}\) | Clipped ratio of noisy pair statistics with a floored denominator | def:private-ratio |
| \(V(h,\delta)\) | \(V(h,\delta)\) | Public mean-squared-error envelope for the local private ratio | Gap: public error envelopes |
| \(\widehat I_{h,k}\) | \(\widehat I_{h,k}\) | Target-range-truncated interval centered on the local private ratio | def:private-ratio |
| \(r(n,\epsilon)\) | \(r(n,\epsilon)\) | Numerical benchmark governing public tuning and minimax orders | Gap: benchmark scale |
| \(\widehat T^*\) | \(\widehat T^*\) | Scalar estimator selected by the public benchmark-based tuning rule | def:public-tuning |
| \(\widehat I^*\) | \(\widehat I^*\) | Connected interval selected by the public benchmark-based tuning rule | def:public-tuning |
| \(I^*_{n,\epsilon}\) | \(I^*_{n,\epsilon}\) | Publicly tuned interval expressed through candidate-value inversion | def:interval-handle |
| \(B_D\) | \(B_D\) | Floored noisy denominator used in inversion | def:interval-handle |
| \(B_N\) | \(B_N\) | Noisy numerator clipped to the range determined by the floored denominator | def:interval-handle |
| \(\operatorname{clip}_{[-B_D,B_D]}\) | \(\operatorname{clip}_{[-B_D,B_D]}\) | Clipping operator onto the inversion numerator range | Gap: clipping operator |
| \(\rho\) | \(\rho\) | Public inversion radius obtained from the mean-squared-error envelope | def:interval-handle |
| \(\vartheta\) | \(\vartheta\) | Candidate target value in the inversion acceptance rule | def:interval-handle |
| \(\ell(n,\epsilon)\) | \(\ell(n,\epsilon)\) | Benchmark for the honest expected-length criterion | Gap: interval benchmark constants |
| \(c_I\) | \(c_I\) | Numerical lower-bound constant for honest expected length | Gap: interval benchmark constants |
| \(C_I\) | \(C_I\) | Numerical upper-bound constant for honest expected length | Gap: interval benchmark constants |
| \(\overline N\) | \(\overline N\) | Population mean of the numerator statistic | Gap: population pair moments |
| \(\overline D\) | \(\overline D\) | Population mean of the denominator statistic | Gap: population pair moments |
| \(j\) | \(j\) | Public-cell index in the population moment sums | Gap: public cell geometry |
| \(w_j\) | \(w_j\) | Cell occupancy weight shared by the two population moment sums | Gap: population pair moments |
| \(\nu_j\) | \(\nu_j\) | Cell-level numerator pair moment | Gap: population pair moments |
| \(d_j\) | \(d_j\) | Cell-level denominator pair moment | Gap: population pair moments |
| \(b\) | \(b\) | Public bias envelope for the population ratio | Gap: public error envelopes |
| \(W(P)\) | \(W(P)\) | Law-dependent occupancy quantity controlling population moments and variances | Gap: population pair moments |
| \(h_{\mathrm L}\) | \(h_{\mathrm L}\) | Macro localization radius for the lower-bound experiments | Gap: lower-bound geometry |
| \(\delta_{\mathrm L}\) | \(\delta_{\mathrm L}\) | Micro localization radius used in the lower-bound comparison | Gap: lower-bound geometry |
| \(t\) | \(t\) | Target-separation amplitude in the lower-bound families | Gap: lower-bound geometry |
| \(q(x)\) | \(q(x)\) | Localized contrast profile in the lower-bound families | Gap: lower-bound profiles |
| \(\lambda\) | \(\lambda\) | Sign vector indexing the finite alternative family | Gap: lower-bound profiles |
| \(S_\lambda(x)\) | \(S_\lambda(x)\) | Sign-indexed nuisance perturbation used by the alternative causal laws | Gap: lower-bound profiles |
| \(P_\lambda\) | \(P_\lambda\) | Causal alternative generated by the sign-indexed conditional Bernoulli laws | def:cosine-family |
| \(Q_n\) | \(Q_n\) | Uniform sign mixture of the alternative observed product laws | def:cosine-family |
| \(P_0\) | \(P_0\) | Null causal law used in the sign and direct comparisons | Gap: lower-bound null law |
| \(P_1\) | \(P_1\) | Direct causal alternative with a localized treatment-arm mean perturbation | def:direct-family |
| \(U\) | \(U\) | Treatment mark used in the conditional likelihood expansion | Gap: likelihood marks |
| \(V_Y\) | \(V_Y\) | Outcome mark used in the conditional likelihood expansion | Gap: likelihood marks |
| \(L_\lambda(x,U,V_Y)\) | \(L_\lambda(x,U,V_Y)\) | Conditional likelihood of the sign alternative relative to the null | Gap: likelihood and mixture comparison |
| \(E_\lambda\) | \(E_\lambda\) | Averaging operator over the uniform sign distribution | def:cosine-family |
| \(G_X\) | \(G_X\) | Covariate-dependent shared-sign graph used for conditional factorization | Gap: component experiment |
| \(C\) | \(C\) | Connected component of the shared-sign graph | Gap: component experiment |
| \(m\) | \(m\) | Number of records in a graph component | Gap: component experiment |
| \(Q_C\) | \(Q_C\) | Conditional component mark law under the sign mixture | Gap: component experiment |
| \(P_{0,C}\) | \(P_{0,C}\) | Conditional component mark law under the null | Gap: component experiment |
| \(z\) | \(z\) | First component mark configuration in the finite coupling | def:common-mass-coupling |
| \(w\) | \(w\) | Second component mark configuration in the finite coupling | def:common-mass-coupling |
| \(a_z\) | \(a_z\) | First marginal mass entry used by the component coupling | Gap: component mass arrays |
| \(b_w\) | \(b_w\) | Second marginal mass entry used by the component coupling | Gap: component mass arrays |
| \(c_z\) | \(c_z\) | Common diagonal mass entry used by the component coupling | Gap: component mass arrays |
| \(\alpha\) | \(\alpha\) | Total common mass used in the component coupling | Gap: component mass arrays |
| \(\Gamma_C(z,w)\) | \(\Gamma_C(z,w)\) | Common-mass coupling of the two finite component laws | def:common-mass-coupling |
| \(Q\) | \(Q\) | Dataset probability law in a generic release comparison | Gap: comparison operators |
| \(Q'\) | \(Q'\) | Second dataset probability law in a generic release comparison | Gap: comparison operators |
| \(MQ\) | \(MQ\) | Output law obtained by applying the randomized release to a dataset law | Gap: release spaces and laws |
| \(d_{\mathrm{TV}}(Q,Q')\) | \(d_{\mathrm{TV}}(Q,Q')\) | Total variation distance between probability laws | Gap: comparison operators |
| \(W_{\mathrm H}(Q,Q')\) | \(W_{\mathrm H}(Q,Q')\) | Minimum expected dataset Hamming distance over couplings | Gap: comparison operators |
| \(\chi^2(Q,Q')\) | \(\chi^2(Q,Q')\) | Chi-square divergence of the first probability law from the second | Gap: comparison operators |
| \(Q^{(0)}\) | \(Q^{(0)}\) | Finite mixture of observed product laws with zero target value | Gap: testing priors |
| \(Q^{(1)}\) | \(Q^{(1)}\) | Finite mixture of observed product laws with a common separated target value | Gap: testing priors |
| \(\Delta\) | \(\Delta\) | Common target separation of the two testing priors | Gap: testing priors |

notation_gaps: \(X,A,Y^{\mathrm{pot}},Y(0),Y(1),Y(A),Y\)=causal-record coordinates lack an anchored introduction, \(P_X,P^{\mathrm{obs}}\)=marginal laws lack an anchored definition, \(\mathcal O^n,D,D^{\prime},\mathcal L(D)\)=observation space and dataset conventions lack an anchored definition, \(f_P(x),e_P(x),\mu_{0,P}(x),\tau_P(x)\)=selected observational functions and their relations lack an anchored definition, \(L\)=the model radius lacks an anchored value, \(x_0,\theta(P)\)=evaluation location and point target lack an anchored definition, \(d_{\mathrm H}(D,D^{\prime})\)=replacement distance lacks an anchored definition, \(\mathcal B,\mathcal B(\mathcal B),MQ\)=output-space and induced-law conventions lack an anchored definition, \(\mathcal I\)=interval coding and its measurable structure lack an anchored definition, \(h,k,j\)=public window and cell partition lack an anchored definition, \(\mathcal A,b,V(h,\delta)\)=public occupancy and error envelopes lack defining formulas, \(\operatorname{clip}_{[-1,1]},\operatorname{clip}_{[-B_D,B_D]}\)=clipping lacks an anchored operator definition, \(r(n,\epsilon)\)=the numerical benchmark lacks an anchored defining formula, \(\ell(n,\epsilon),c_I,C_I\)=interval benchmark quantities lack a definition home, \(\overline N,\overline D,w_j,\nu_j,d_j,W(P)\)=population pair moments and occupancy weights lack defining formulas, \(h_{\mathrm L},\delta_{\mathrm L},t\)=lower-bound scales and amplitude lack an anchored specification, \(q(x),\lambda,S_\lambda(x)\)=lower-bound profiles and sign indexing lack an anchored construction, \(P_0\)=the null causal law lacks an anchored construction, \(U,V_Y,L_\lambda(x,U,V_Y)\)=likelihood marks and likelihood convention lack an anchored definition, \(G_X,C,m,Q_C,P_{0,C}\)=shared-sign graph and conditional component experiments lack an anchored definition, \(a_z,b_w,c_z,\alpha\)=component mass arrays and common mass lack defining formulas, \(Q,Q',d_{\mathrm{TV}}(Q,Q'),W_{\mathrm H}(Q,Q'),\chi^2(Q,Q')\)=dataset-law comparison conventions lack an anchored definition, \(Q^{(0)},Q^{(1)},\Delta\)=testing-prior notation lacks an anchored definition distinct from its existence certificate

# Sections

## section: Abstract

Plan the abstract around the confidential-record pointwise treatment-effect question, the declared binary fixed-overlap model, the common estimation and honest-length order, and attainment through one release of localized pair moments. Give a brief plain-language interpretation of the privacy-budget regimes. Write this section last, after the exposition and scope boundaries are settled; introduce any mathematical symbols with first-use glosses.

objs: none

bib: none

home_objs: none
## section: Introduction

Introduce the statistical question of releasing a conditional treatment effect at a specified covariate value together with a uniformly valid confidence interval. Explain why a smooth contrast can coexist with rough treatment assignment and control regression, and why unknown measurable design density matters for uniform attainment. Organize the contributions around the common minimax order, the density-free release, and the interval-specific converse. Preview the budget interpretation and paper organization. Include one factual sentence directing readers to the appendix verification note, with the note's eventual structural label referenced through cleveref. Write the introduction after the main text.

objs: none

bib: Rubin1974, Rosenbaum1983, Imbens2009

home_objs: none
## section: Related work

Make the closest comparison with \citet[][Theorems 1--2 and Remarks 2 and 11]{KennedyBalakrishnanRobinsWasserman2024}: distinguish their broader real-outcome lower-bound experiment and conditions for higher-order local-polynomial attainment from the present binary, bounded-positive-density experiment and occupancy-based private attainment. Compare the release construction with bounded private U-statistics in \citet[][Theorem 2]{ChaudhuriLohPandeySarkar2024}, and the testing argument with coupling-based private lower bounds in \citet[][Section 2]{AcharyaSunZhang2021}. Compare private heterogeneous-effect learners of \citet{NiuEtAl2022} and \citet[][Theorem 1]{SchroderMelnychukFeuerriegel2025} by estimand, privacy definition, and performance criterion. Position uniform finite-sample expected-length optimality alongside bias-aware nonparametric intervals and asymptotic private ATE inference. Use residualization, higher-order estimation, and causal forests as concise methodological context; treat smooth-nuisance kernel results as a separate model comparison. Keep novelty claims tied to this specified experiment and the supplied citation evidence.

objs: none

bib: KennedyBalakrishnanRobinsWasserman2024, ChaudhuriLohPandeySarkar2024, AcharyaSunZhang2021, NiuEtAl2022, SchroderMelnychukFeuerriegel2025, ArmstrongKolesar2018, ArmstrongKolesar2020, SchroderHartensteinFeuerriegel2025, Robinson1988, Chernozhukov2018, Nie2021, Kennedy2023, Robins2008, Robins2009, WagerAthey2018, Athey2019, Kim2026, Low1997, Cai2004

home_objs: none
## section: Observation model, identification, and decision criteria

Introduce the causal and observed records, selected regression versions, evaluation location, and pointwise target before using them. Present the sampling and identifying restrictions, then organize density, overlap, and smoothness conditions as the definition of the statistical class. Explain how continuity and positive design density resolve the pointwise interpretation, referring to \cref{lem:point-version} for the argument. Define replacement privacy and its randomized releases on the full dataset space. Introduce scalar absolute risk and maximal expected connected-interval length under uniform coverage as separate decision criteria. Resolve the model, target, release-space, and interval-space notation gaps in grouped presentation definitions before their first use.

objs: synth_4, synth_9, synth_3, synth_2, synth_1, synth_8, ass:iid, ass:consistency, ass:exchangeability, synth_10, ass:density, ass:overlap, ass:propensity-holder, ass:control-holder, ass:contrast-lipschitz, synth_16, def:complete-model, ass:pure-privacy, def:private-kernels, def:risk-criterion, synth_13, def:interval-criterion

bib: Rubin1974, Rosenbaum1983, Dwork2006, Dwork2014, Donoho1994, Low1997, Cai2004

home_objs: ass:iid, ass:consistency, ass:exchangeability, ass:density, ass:overlap, ass:propensity-holder, ass:control-holder, ass:contrast-lipschitz, def:complete-model, ass:pure-privacy, def:private-kernels, def:risk-criterion, def:interval-criterion
## section: A private release based on within-cell pairs

Introduce the public local window, equal-cell partition, occupancy scale, bias envelope, mean-squared-error envelope, and numerical benchmark before presenting the procedures that use them. Explain the shared occupancy weighting of numerator and denominator as the statistical reason the construction accommodates every admissible measurable density. Present the pair-statistic release, public tuning, and interval inversion as numbered procedures, emphasizing their common release and public inputs. Follow with \cref{thm:uniform-private-upper}, separating the statistical roles of localization bias, pair-statistic variation, denominator stabilization, and Laplace noise. Direct the detailed occupancy and replacement-sensitivity arguments to \cref{lem:occupancy-cancellation,lem:all-count-stability}; retain the central procedures in the main text.

objs: synth_12, synth_11, def:private-ratio, def:public-tuning, synth_17, def:interval-handle, thm:uniform-private-upper

bib: Hoeffding1948, Dwork2006, Dwork2014

home_objs: def:private-ratio, def:public-tuning, def:interval-handle, thm:uniform-private-upper
## section: Optimal estimation and honest confidence intervals

Present \cref{thm:matched-risk-frontier,thm:sharp-interval-frontier} as the two principal decision-theoretic results, with separate explanations of scalar loss and honest expected length. Interpret the numerical benchmark through \cref{prop:regime-and-sanity}, using a compact budget-regime table and highlighting the consistency criterion. Explain the lower-bound strategy at the level of observational indistinguishability and privacy contraction, while placing the sign-family and component-coupling apparatus in the appendix. Give the interval converse its own intuition based on simultaneous containment and connectedness, so the common order is supported by the interval criterion itself. Define the interval benchmark constants before the corresponding frozen environment.

objs: thm:matched-risk-frontier, thm:sharp-interval-frontier, prop:regime-and-sanity

bib: AcharyaSunZhang2021, Donoho1994, Cai2004

home_objs: thm:matched-risk-frontier, thm:sharp-interval-frontier, prop:regime-and-sanity
## section: Discussion and limitations

Interpret the paper's results for confidential binary observational records: how nuisance roughness, local occupancy, and privacy jointly determine useful pointwise release, and why the same benchmark governs honest uncertainty quantification. Discuss public tuning and the statistical meaning of the finite-sample guarantees. Include a clearly titled “Limitations and future work” subsection covering represented-real implementation and software privacy certification, unrestricted nonprivate minimax comparisons, broader outcome and design classes, varying overlap or smoothness, and evaluation of particular causal-effect estimators. Frame those items as scope boundaries or future directions, with literature positioning retained in the related-work section.

objs: none

bib: none

home_objs: none
## section: Appendix A. Identification and upper-bound proofs

Place the point-identification argument before the proofs that use the target interpretation. Define the population pair moments and occupancy weights before their first appearance in the auxiliary results. Prove occupancy cancellation and all-count stability, including low-count cells and replacement inputs across the entire dataset space. Then supply the upper-bound proof, explaining how the public error envelope combines bias, sampling variation, and privacy noise, and how inversion reuses the same release. Keep detailed intermediate notation and algebra here whenever the main exposition uses only their statistical interpretation.

objs: lem:point-version, lem:occupancy-cancellation, lem:all-count-stability

bib: Hoeffding1948, Efron1981, Dwork2006, Dwork2014

home_objs: lem:point-version, lem:occupancy-cancellation, lem:all-count-stability
## section: Appendix B. Lower-bound experiments and component coupling

Introduce the lower-bound geometry, profiles, sign distribution, null law, and likelihood marks before constructing the sign alternatives. Place the alternative family before its membership and likelihood certificate. Next define the shared-sign graph, conditional component laws, and mass arrays before the common-mass coupling and its contraction result. Preserve the sparse-occupancy condition at every use of that comparison. Introduce the direct alternative as the complementary experiment used in the regime selection. These constructions remain appendix material because the main text uses their testing implications rather than their internal coordinates.

objs: synth_6, synth_5, def:cosine-family, lem:positive-family-certificate, synth_14, synth_7, synth_15, def:common-mass-coupling, lem:measurable-component-contraction, def:direct-family

bib: KennedyBalakrishnanRobinsWasserman2024, AcharyaSunZhang2021, BoucheronLugosiMassart2013, KellerTrotterAppliedCombinatorics

home_objs: def:cosine-family, lem:positive-family-certificate, def:common-mass-coupling, lem:measurable-component-contraction, def:direct-family
## section: Appendix C. Testing reductions and matching lower bounds

Define dataset-law distances, induced output laws, and testing-prior notation before the generic comparison result and the testing-prior certificate. Assemble the sign and direct experiments with their applicable conditions to obtain the common testing comparison. Give separate reductions for scalar absolute loss and honest connected-interval expected length, followed by the budget-regime calculation and consistency argument. Preserve theorem-local locators for published inputs and carry their generated verification-scope footnotes with the consuming arguments.

objs: lem:private-kernel-comparison, lem:frontier-testing-priors

bib: AcharyaSunZhang2021, Tsybakov2009, BoucheronLugosiMassart2013

home_objs: lem:private-kernel-comparison, lem:frontier-testing-priors
## section: Appendix D. Verification note

End the appendix with a brief account of Lean machine-checking scope covering the identification, occupancy, stability, lower-family, coupling, testing, estimation, and interval results. Distinguish checked derivations from the stated statistical assumptions and theorem-local published inputs, using the supplied verification metadata for the precise boundary. Consolidate exact-real procedure scope and dependency disclosures here without treating formalization as a scientific contribution.

objs: none

bib: none
home_objs: none
