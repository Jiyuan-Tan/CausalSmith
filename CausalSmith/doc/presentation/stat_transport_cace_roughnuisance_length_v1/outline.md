# Title
**Honest confidence intervals for transported complier effects with rough nuisance functions**

**Contribution statement.** In an equal-size source–target experiment with scalar covariates, unknown Hölder-\(1/8\) densities, encouragement propensity and arm means, and two pointwise complier transport restrictions, the paper establishes the minimax expected-length order \(\min\{1,n^{-1/3}/a\}\), where \(n\) is each sample size and \(a\) is the transported first-stage evaluation floor, attained by one finite-sample honest interval sequence independent of that floor.

env_overrides: def:cubic-estimator=algorithmv, def:legal-iv-mixture=algorithmv, oeq:unequal-sample-frontier=remarkv

notation_gaps: \mathcal S_n=source sample lacks an anchored sampling definition, \mathcal T_n=target sample lacks an anchored sampling definition, P_n^F=primitive full-data law and its population indicator lack an anchored definition, P_{\mathrm S}=source observed law lacks an anchored definition, P_{\mathrm T}=target covariate law lacks an anchored definition, f_{\mathrm S}=source covariate density lacks an anchored definition, f_{\mathrm T}=target covariate density lacks an anchored definition, e=conditional encouragement propensity lacks an anchored definition, D(0)=potential receipt under zero encouragement lacks an anchored definition, D(1)=potential receipt under unit encouragement lacks an anchored definition, Y(0)=potential outcome under zero receipt lacks an anchored definition, Y(1)=potential outcome under unit receipt lacks an anchored definition, C=complier indicator lacks an anchored definition, m_{Az}=conditional source arm mean lacks an anchored definition, \Delta_D(x)=conditional receipt contrast lacks an anchored definition, \Delta_Y(x)=conditional outcome contrast lacks an anchored definition, T_A=transported reduced form needs an anchored family definition specifying its indices, T_D=transported first stage needs an anchored family definition, T_Y=transported outcome reduced form needs an anchored family definition, \mu=transported compliance share lacks an anchored definition, \theta=target complier effect lacks an anchored definition, \Theta=bounded effect domain lacks an anchored definition, \mathcal H^{\beta}([0,1],L)=Hölder ball lacks an anchored definition, [f_{\mathrm S}]_{\beta}=Hölder seminorm lacks an anchored operator definition, [f_{\mathrm T}]_{\beta}=Hölder seminorm lacks an anchored operator definition, [e]_{\beta}=Hölder seminorm lacks an anchored operator definition, [m_{Az}]_{\beta}=Hölder seminorm lacks an anchored operator definition, c_f=density lower envelope lacks an anchored constants definition, C_f=density upper envelope lacks an anchored constants definition, L=smoothness radius lacks an anchored constants definition, \beta=frozen environments leave the smoothness exponent unnamed by an anchored definition, \alpha=noncoverage level lacks an anchored constants definition, n_0=finite-size threshold lacks an anchored constants definition, \rho_n^{\mathcal G}=known-geometry calibration radius lacks an anchored definition, \Pi=fixed finite interval partition lacks an anchored definition, g_{\dagger}(x)=continuous witness function lacks an anchored definition, \mathcal I=marked-coordinate index set lacks an anchored definition, \mathcal B_b^G=sample blocks lack an anchored definition, m_b=block sizes lack an anchored definition, m_1=first evaluation-block size lacks an anchored definition, K_0(n)=pilot resolution rule lacks an anchored definition, K_2(n)=quadratic resolution rule lacks an anchored definition, K_3(n)=cubic resolution rule lacks an anchored definition, K_0=pilot resolution shorthand lacks an explicit anchored alias, K_2=quadratic resolution shorthand lacks an explicit anchored alias, K_3=cubic resolution shorthand lacks an explicit anchored alias, H_{i,K}^{(b)}=normalized marked histogram lacks an anchored definition, \widehat F=clipped pilot lacks an anchored definition, R_{i,K}^{(b)}=histogram residual lacks an anchored definition, g(i)=sample-channel map lacks an anchored definition, W_{i,r}=observable mark lacks an anchored definition, X_r^{g(i)}=channel-indexed observed covariate lacks an anchored definition, \mathcal A_n=inverted affine-score set lacks an anchored definition, \lambda_{\Theta}=restricted Lebesgue length lacks an anchored definition, K_{\mathrm L}=lower-experiment cell-count rule lacks an anchored definition, u_{\lambda}(x)=tiled sign perturbation lacks an anchored definition, R_z^{(b)}(d,y)=baseline conditional receipt–outcome cell law lacks an anchored definition, J_n=lower-experiment separation functional lacks an anchored definition, \chi^2=chi-square divergence needs an anchored operator definition, \operatorname{TV}=total-variation distance needs an anchored operator definition

# Notation

Notation gaps identify missing presentation definitions; their mathematical content must be supplied from an authorized source before synthesis. Ambient indices, integration variables, ordinary derivatives, expectations, probabilities and norms retain their standard meanings.

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(\mathcal S_n\) | \(\mathcal S_n\) | \(n\) observed source records | notation gap |
| \(\mathcal T_n\) | \(\mathcal T_n\) | \(n\) observed target covariate records | notation gap |
| \(P_n^F\) | \(P_n^F\) | primitive full-data law at sample-size index \(n\) | notation gap |
| \(P_{\mathrm S}\) | \(P_{\mathrm S}\) | law of one observed source record | notation gap |
| \(P_{\mathrm T}\) | \(P_{\mathrm T}\) | law of one observed target covariate | notation gap |
| \(f_{\mathrm S}\) | \(f_{\mathrm S}\) | source covariate density | notation gap |
| \(f_{\mathrm T}\) | \(f_{\mathrm T}\) | target covariate density | notation gap |
| \(e\) | \(e\) | source encouragement propensity conditional on covariates | notation gap |
| \(D(0)\) | \(D(0)\) | potential receipt under zero encouragement | notation gap |
| \(D(1)\) | \(D(1)\) | potential receipt under unit encouragement | notation gap |
| \(Y(0)\) | \(Y(0)\) | potential outcome under zero receipt | notation gap |
| \(Y(1)\) | \(Y(1)\) | potential outcome under unit receipt | notation gap |
| \(C\) | \(C\) | indicator of the complier principal stratum | notation gap |
| \(m_{Az}\) | \(m_{Az}\) | source conditional mean of response \(A\) in encouragement arm \(z\) | notation gap |
| \(\Delta_D(x)\) | \(\Delta_D(x)\) | source conditional receipt contrast | notation gap |
| \(\Delta_Y(x)\) | \(\Delta_Y(x)\) | source conditional outcome contrast | notation gap |
| \(T_A\) | \(T_A\) | target-averaged source contrast for response \(A\) | notation gap; functional representation in def:smooth-functional |
| \(T_D\) | \(T_D\) | target-averaged source receipt contrast | notation gap |
| \(T_Y\) | \(T_Y\) | target-averaged source outcome contrast | notation gap |
| \(\mu\) | \(\mu\) | transported compliance share and first stage | notation gap |
| \(\theta\) | \(\theta\) | target-population average treatment effect among compliers | notation gap |
| \(\Theta\) | \(\Theta\) | bounded domain of the complier effect | notation gap |
| \(c_f\) | \(c_f\) | fixed lower density envelope | notation gap |
| \(C_f\) | \(C_f\) | fixed upper density envelope | notation gap |
| \(L\) | \(L\) | common Hölder radius | notation gap |
| \(\beta\) | \(\beta\) | common Hölder exponent | notation gap |
| \(\alpha\) | \(\alpha\) | prescribed noncoverage probability | notation gap |
| \(n_0\) | \(n_0\) | threshold for using the cubic estimator | notation gap |
| \(\mathcal H^{\beta}([0,1],L)\) | \(\mathcal H^{\beta}([0,1],L)\) | continuous functions on \([0,1]\) with supremum norm and \(\beta\)-Hölder seminorm bounded by \(L\) | notation gap |
| \([f_{\mathrm S}]_{\beta}\) | \([f_{\mathrm S}]_{\beta}\) | \(\beta\)-Hölder seminorm of the source density | notation gap |
| \([f_{\mathrm T}]_{\beta}\) | \([f_{\mathrm T}]_{\beta}\) | \(\beta\)-Hölder seminorm of the target density | notation gap |
| \([e]_{\beta}\) | \([e]_{\beta}\) | \(\beta\)-Hölder seminorm of the encouragement propensity | notation gap |
| \([m_{Az}]_{\beta}\) | \([m_{Az}]_{\beta}\) | \(\beta\)-Hölder seminorm of an arm mean | notation gap |
| \(\mathcal M_n\) | \(\mathcal M_n\) | law triples satisfying the sampling, regularity, causal and transport restrictions | def:model-class |
| \(\mathcal M_n^{\mathrm{fix}}(\mathcal G)\) | \(\mathcal M_n^{\mathrm{fix}}(\mathcal G)\) | model subclass with a supplied density–propensity triple | def:fixed-geometry-subclass |
| \(\mathcal G\) | \(\mathcal G\) | supplied source density, target density and encouragement propensity | def:known-geometry-score |
| \(f_{\mathrm S}^0\) | \(f_{\mathrm S}^0\) | supplied source density | def:known-geometry-score |
| \(f_{\mathrm T}^0\) | \(f_{\mathrm T}^0\) | supplied target density | def:known-geometry-score |
| \(e^0\) | \(e^0\) | supplied encouragement propensity | def:known-geometry-score |
| \(\widetilde T_A^{\mathcal G}\) | \(\widetilde T_A^{\mathcal G}\) | source-sample weighted contrast using supplied geometry | def:known-geometry-score |
| \(\rho_n^{\mathcal G}\) | \(\rho_n^{\mathcal G}\) | calibration radius for the supplied-geometry score | notation gap |
| \(\mathcal A_n^{\mathcal G}\) | \(\mathcal A_n^{\mathcal G}\) | supplied-geometry affine-score acceptance set | def:known-geometry-interval |
| \(I_n^{\mathcal G}\) | \(I_n^{\mathcal G}\) | supplied-geometry interval with singleton fallback | def:known-geometry-interval |
| \(\Pi\) | \(\Pi\) | fixed finite partition into intervals | notation gap |
| \(\mathcal M_n^{\mathrm{cell}}(\Pi)\) | \(\mathcal M_n^{\mathrm{cell}}(\Pi)\) | subclass with densities and propensity constant on partition cells | def:finite-cell-subclass |
| \(\varepsilon_{\dagger}\) | \(\varepsilon_{\dagger}\) | amplitude chosen from density, overlap and smoothness slack | def:continuous-geometry-witness |
| \(g_{\dagger}(x)\) | \(g_{\dagger}(x)\) | covariate perturbation defining the continuous witnesses | notation gap |
| \(P_{\sigma}^{\dagger}\) | \(P_{\sigma}^{\dagger}\) | full-data witness indexed by a binary sign | def:continuous-geometry-witness |
| \(F(x)\) | \(F(x)\) | seven-coordinate vector of target and source marked densities | def:marked-density-vector |
| \(q_z\) | \(q_z\) | source joint density of covariates and encouragement arm \(z\) | def:marked-density-vector |
| \(r_{Az}\) | \(r_{Az}\) | source arm density marked by response \(A\) | def:marked-density-vector |
| \(\Phi_A(F)\) | \(\Phi_A(F)\) | density-ratio integrand for the transported contrast | def:smooth-functional |
| \(\mathcal I\) | \(\mathcal I\) | index set for the seven marked-density coordinates | notation gap |
| \(\mathcal B_b^G\) | \(\mathcal B_b^G\) | deterministic block \(b\) of sample channel \(G\) | notation gap |
| \(m_b\) | \(m_b\) | size of block \(b\) | notation gap |
| \(m_1\) | \(m_1\) | size of the first evaluation block | notation gap |
| \(K_0(n)\) | \(K_0(n)\) | dyadic pilot resolution rule | notation gap |
| \(K_2(n)\) | \(K_2(n)\) | dyadic quadratic-correction resolution rule | notation gap |
| \(K_3(n)\) | \(K_3(n)\) | dyadic cubic-correction resolution rule | notation gap |
| \(K_0\) | \(K_0\) | pilot resolution at the current sample size | notation gap |
| \(K_2\) | \(K_2\) | quadratic resolution at the current sample size | notation gap |
| \(K_3\) | \(K_3\) | cubic resolution at the current sample size | notation gap |
| \(H_{i,K}^{(b)}\) | \(H_{i,K}^{(b)}\) | normalized marked histogram for coordinate \(i\), resolution \(K\) and block \(b\) | notation gap |
| \(\widehat F\) | \(\widehat F\) | clipped pilot vector of marked-density estimates | notation gap |
| \(R_{i,K}^{(b)}\) | \(R_{i,K}^{(b)}\) | block-specific marked-histogram residual relative to the pilot | notation gap |
| \(x_{\ell,K}\) | \(x_{\ell,K}\) | midpoint of resolution-\(K\) cell \(\ell\) | def:cubic-estimator |
| \(g(i)\) | \(g(i)\) | source or target sample channel for coordinate \(i\) | notation gap |
| \(W_{i,r}\) | \(W_{i,r}\) | bounded observable mark for coordinate \(i\) and record \(r\) | notation gap |
| \(X_r^{g(i)}\) | \(X_r^{g(i)}\) | observed covariate of record \(r\) in coordinate \(i\)'s channel | notation gap |
| \(\mathsf L_A\) | \(\mathsf L_A\) | observable linear correction to the pilot functional | def:cubic-estimator |
| \(\mathsf Q_A\) | \(\mathsf Q_A\) | observable split-block quadratic correction | def:cubic-estimator |
| \(\mathsf C_A\) | \(\mathsf C_A\) | observable split-block cubic correction | def:cubic-estimator |
| \(\widehat T_A\) | \(\widehat T_A\) | pilot functional plus linear, quadratic and cubic corrections | def:cubic-estimator |
| \(C_{\mathrm{mse}}\) | \(C_{\mathrm{mse}}\) | computable uniform mean-square bound constant | lem:marked-cubic-mse introduces the constant; presentation definition needed before calibration |
| \(\mathcal A_n\) | \(\mathcal A_n\) | calibrated affine-score acceptance set | notation gap |
| \(I_n\) | \(I_n\) | inverted score interval with empty-set and finite-size fallbacks | def:score-interval |
| \(C_n\) | \(C_n\) | generic measurable confidence set in the effect domain | def:honest-intervals |
| \(\mathfrak H_n\) | \(\mathfrak H_n\) | connected intervals with uniform finite-sample coverage | def:honest-intervals |
| \(\mathcal M_n(a)\) | \(\mathcal M_n(a)\) | model slice with transported first stage between \(a\) and \(1/4\) | def:strength-slice |
| \(\lambda_{\Theta}\) | \(\lambda_{\Theta}\) | Lebesgue length restricted to the effect domain | notation gap |
| \(L_n(a)\) | \(L_n(a)\) | minimax expected length of globally honest connected intervals on a strength slice | def:length-frontier |
| \(c_0\) | \(c_0\) | positive lower comparison constant | thm:sharp-length-frontier-full-elbow introduces the constant |
| \(C_0\) | \(C_0\) | finite upper comparison constant | thm:honest-upper-full-elbow introduces the constant |
| \(c_{\star}\) | \(c_{\star}\) | positive lower-family amplitude subject to admissibility | def:legal-iv-mixture |
| \(K_{\mathrm L}\) | \(K_{\mathrm L}\) | number of perturbation cells in the lower experiment | notation gap |
| \(\lambda\in\{-1,1\}^{K_{\mathrm L}}\) | \(\lambda\in\{-1,1\}^{K_{\mathrm L}}\) | cellwise binary sign vector | def:legal-iv-mixture |
| \(\tau\in[-1,1]\) | \(\tau\in[-1,1]\) | continuum index controlling effect separation | def:legal-iv-mixture |
| \(b\) | \(b\) | baseline compliance share used in the lower family | def:legal-iv-mixture |
| \(\bar a\) | \(\bar a\) | maximum of the evaluation floor and the rough estimation scale | def:legal-iv-mixture |
| \(h\) | \(h\) | local alias for the lower-family perturbation height | def:legal-iv-mixture |
| \(h_n\) | \(h_n\) | amplitude times the lower cell count raised to \(-1/8\) | def:legal-iv-mixture |
| \(\operatorname{Adm}_{n,a}(c_{\star})\) | \(\operatorname{Adm}_{n,a}(c_{\star})\) | positivity and height restrictions for constructing the lower laws | def:legal-iv-mixture |
| \(u_{\lambda}(x)\) | \(u_{\lambda}(x)\) | tiled covariate perturbation indexed by cell signs | notation gap |
| \(v_{\lambda,\tau}\) | \(v_{\lambda,\tau}\) | continuum-scaled version of the sign perturbation | def:legal-iv-mixture |
| \(e_1^{(\lambda)}\) | \(e_1^{(\lambda)}\) | unit-encouragement probability in the lower family | def:legal-iv-mixture |
| \(e_0^{(\lambda)}\) | \(e_0^{(\lambda)}\) | zero-encouragement probability in the lower family | def:legal-iv-mixture |
| \(R_z^{(b)}(d,y)\) | \(R_z^{(b)}(d,y)\) | baseline receipt–outcome cell probability at compliance share \(b\) | notation gap |
| \(Q_{\lambda,\tau}\) | \(Q_{\lambda,\tau}\) | admissible no-defiers full-data and observed-law component | def:legal-iv-mixture |
| \(M_{1y}(x)\) | \(M_{1y}(x)\) | joint conditional mass of compliers and outcome \(y\) under receipt | def:legal-iv-mixture |
| \(M_{0y}(x)\) | \(M_{0y}(x)\) | joint conditional mass of compliers and outcome \(y\) under zero receipt | def:legal-iv-mixture |
| \(M_{dy}(x)\) | \(M_{dy}(x)\) | complier outcome margin for receipt state \(d\) and outcome \(y\) | def:legal-iv-mixture |
| \(M_{\tau}\) | \(M_{\tau}\) | uniform sign mixture of equal-size observed product experiments | def:legal-iv-mixture |
| \(P_{\star}\) | \(P_{\star}\) | unperturbed center law retaining baseline compliance | def:legal-iv-mixture |
| \(P_{\star}^{(n,n)}\) | \(P_{\star}^{(n,n)}\) | equal-size observed source–target product experiment at the center | def:legal-iv-mixture |
| \(J_n\) | \(J_n\) | positive separation functional for the lower continuum | notation gap |
| \(C_{\mathrm{mix}}\) | \(C_{\mathrm{mix}}\) | numerical constant in the mixture chi-square bound | lem:legal-iv-mixture-full-elbow introduces the constant |
| \(\chi^2(M_{\tau},P_{\star}^{(n,n)})\) | \(\chi^2(M_{\tau},P_{\star}^{(n,n)})\) | chi-square divergence of the mixture from the center experiment | notation gap |
| \(\operatorname{TV}(M_{\tau},P_{\star}^{(n,n)})\) | \(\operatorname{TV}(M_{\tau},P_{\star}^{(n,n)})\) | total-variation distance between mixture and center experiments | notation gap |
| \(N_{\mathrm S}\) | \(N_{\mathrm S}\) | source sample size in the unequal experiment | def:unequal-sample-handle |
| \(N_{\mathrm T}\) | \(N_{\mathrm T}\) | target sample size in the unequal experiment | def:unequal-sample-handle |
| \(\mathcal M^{\mathrm u}_{N_{\mathrm S},N_{\mathrm T}}\) | \(\mathcal M^{\mathrm u}_{N_{\mathrm S},N_{\mathrm T}}\) | law-level model observed with unequal source and target counts | def:unequal-sample-handle |
| \(\mathcal M^{\mathrm u}_{N_{\mathrm S},N_{\mathrm T}}(a)\) | \(\mathcal M^{\mathrm u}_{N_{\mathrm S},N_{\mathrm T}}(a)\) | unequal-experiment strength slice | def:unequal-sample-handle |
| \(C_{N_{\mathrm S},N_{\mathrm T}}\) | \(C_{N_{\mathrm S},N_{\mathrm T}}\) | connected random interval based on unequal samples | def:unequal-sample-handle |
| \(\mathfrak H^{\mathrm u}_{N_{\mathrm S},N_{\mathrm T}}\) | \(\mathfrak H^{\mathrm u}_{N_{\mathrm S},N_{\mathrm T}}\) | uniformly honest connected intervals for the unequal experiment | def:unequal-sample-handle |
| \(R_{N_{\mathrm S},N_{\mathrm T}}(a)\) | \(R_{N_{\mathrm S},N_{\mathrm T}}(a)\) | unequal-sample minimax expected-length criterion | def:unequal-sample-handle |

# Sections

## section: Introduction

Plan an unnumbered abstract and an introduction, both to be written after the mathematical exposition. Lead with the precision question for a target-population complier effect when source encouragement data and target covariates must jointly support inference. Introduce the equal-size, scalar-covariate, Hölder-\(1/8\) setting in words; distinguish global coverage from evaluation on a first-stage slice; and preview the sharp expected-length order, its constant-length branch, the observable attaining interval, and the no-defiers converse. Present machine checking through one factual sentence pointing to the appendix verification note, with its structural label assigned during synthesis.

objs: none

bib: Imbens1994, Angrist1996, Angrist2013, Degtiar2023

home_objs: none
## section: Related work

Organize the comparison around the closest results rather than a chronological survey. Compare the transported-CACE identification and regular inference of \citet[Theorems 3.1, 4.2 and 4.3]{ChenHuang2025Generalizing}, the transported-CACE influence curve and ratio estimation of \citet[Sections 5 and 7]{RudolphVanDerLaan2017Robust}, and the regular transported principal-effect inference of \citet[Theorem 6]{Clark2024}, retaining their distinct observation schemes and assumptions. Connect the rough reduced-form scale to \citet[Theorems 6 and 8]{ZengKennedyBodnarNaimi2025Efficient}, with their design and remainder conditions preserved, and locate the cubic marked-density construction within higher-order functional estimation. Compare finite-sample rough-class score calibration with the asymptotic identification-robust results of \citet[Theorem 3.2]{Ma2026IdentificationRobust} and the score geometry of \citet[Section 3 and Theorems 1 and 2]{SmuclerLanniMasip2025Score}. Use the supplied- and cell-geometry benchmark of \citet{CausalSmith2026TransportedLATEStrengthFrontier} as the immediate internal comparison. Define the contribution boundary as the joint equal-size rough-geometry, uniform-coverage, expected-length result and its primitive IV realization; treat the exponent and inversion principle as established methodological antecedents.

objs: none

bib: ChenHuang2025Generalizing, RudolphVanDerLaan2017Robust, Clark2024, ZengKennedyBodnarNaimi2025Efficient, Ma2026IdentificationRobust, SmuclerLanniMasip2025Score, CausalSmith2026TransportedLATEStrengthFrontier, Imbens1994, Angrist1996, Frangakis2002, Angrist2013, Degtiar2023, Robins2008, VanDerVaartTchetgenRobinsLi2009Mixtures, Chernozhukov2018, Anderson1949, Fieller1954, Dufour1997, CaiLow2004Adaptation

home_objs: none
## section: Model, transport restrictions and inference criterion

Introduce the primitive variables, source and covariate-only target observations, fixed class constants and Hölder convention through grouped presentation definitions resolving the corresponding notation gaps. Group the frozen assumptions by sampling, density and smoothness restrictions, instrument validity, and the two pointwise complier transport equalities. Explain the roles of transported compliance and the bounded effect domain, directing the identification argument to \cref{lem:transported-cace-identification}. Define global honesty before the strength slice and expected-length criterion, making the evaluation floor distinct from a restriction used to construct the interval. Place every synthesized definition immediately before its first use.

objs: ass:source-iid, ass:target-iid, ass:sample-independence, synth_1, ass:source-density-bounds, ass:target-density-bounds, ass:source-density-holder, ass:target-density-holder, ass:propensity-overlap, ass:propensity-holder, ass:arm-means-holder, ass:receipt-consistency, ass:outcome-consistency, ass:instrument-randomization, ass:exclusion, ass:monotonicity, ass:transport-complier-outcome, ass:transport-complier-share, ass:positive-strength, def:model-class, def:honest-intervals, def:strength-slice, def:length-frontier

bib: Imbens1994, Angrist1996, Frangakis2002

home_objs: ass:source-iid, ass:target-iid, ass:sample-independence, ass:source-density-bounds, ass:target-density-bounds, ass:source-density-holder, ass:target-density-holder, ass:propensity-overlap, ass:propensity-holder, ass:arm-means-holder, ass:receipt-consistency, ass:outcome-consistency, ass:instrument-randomization, ass:exclusion, ass:monotonicity, ass:transport-complier-outcome, ass:transport-complier-share, ass:positive-strength, def:model-class, def:honest-intervals, def:strength-slice, def:length-frontier
## section: Main results and an attaining interval

Build the main exposition around the sharp expected-length result and the mechanism that attains it. Introduce the observable marked-density representation, then give a concise estimator overview, the exact score-interval construction, and the exact sharp frontier before directing readers to the anchored technical construction and supporting theorem statements in the appendix. Explain how the pilot, linear through cubic corrections, and split evaluation blocks balance approximation and variance at the rough estimation scale; explain amplification by transported compliance and saturation in the bounded parameter domain. Emphasize simultaneous attainment across evaluation floors and the absence of a leading logarithmic factor. Keep exhaustive indexing, block arithmetic, histogram conventions, the full estimator algorithm, and supporting upper- and lower-bound environments in the technical appendix.

objs: def:marked-density-vector, def:smooth-functional, synth_10, def:score-interval, thm:sharp-length-frontier-full-elbow

bib: none

home_objs: def:marked-density-vector, def:smooth-functional, def:score-interval, thm:sharp-length-frontier-full-elbow
## section: Discussion and open questions

Interpret the two expected-length regimes as precision benchmarks for the declared source–target experiment and explain how the single interval responds to the actual transported first stage. Introduce the unequal-sample decision problem as an extension of the criterion, followed by a clearly titled “Open questions” subsection containing \cref{oeq:unequal-sample-frontier}. A clearly titled “Limitations and future work” subsection should delimit the scalar, fixed-smoothness, independent-record benchmark and distinguish the defined unequal-allocation problem from the delivered equal-size results. Keep off-diagonal rate claims and a source-only lower term outside the result narrative because the frozen theorem inventory supplies the equal-size bounds. Relate any application motivation to the population and sampling conditions explicitly.

objs: def:unequal-sample-handle, oeq:unequal-sample-frontier

bib: none

home_objs: def:unequal-sample-handle, oeq:unequal-sample-frontier
## section: Appendix: Identification and upper-bound proofs

Begin with the primitive-variable identification argument. Then collect the anchored technical construction in dependency order: coordinate and sampling conventions, exact block arithmetic, histograms, resolutions, pilot, residuals, the cubic algorithm, observable reduction, mean-square bound, and supporting upper- and lower-bound statements. Establish the observable marked-density reduction before the cubic mean-square argument, resolving any proof-only notation immediately before use. Organize that argument around the clipped pilot eighth moment, projection cancellation and block-conditional variance calculations, followed by the coverage and expected-length proof for the attaining interval. Retain exact estimator resolutions, repeated-coordinate block assignments and constant dependencies throughout. Separate the scientific probability calculations from any implementation representation used for checking them.

objs: lem:transported-cace-identification, synth_3, synth_2, synth_19, synth_14, synth_7, synth_4, synth_8, synth_9, synth_6, synth_5, def:cubic-estimator, lem:observable-marked-reduction, lem:marked-cubic-mse, thm:honest-upper-full-elbow, thm:honest-lower-full-elbow

bib: Hoeffding1948, Robins2008, Tsybakov2009

home_objs: lem:transported-cace-identification, def:cubic-estimator, lem:observable-marked-reduction, lem:marked-cubic-mse, thm:honest-upper-full-elbow, thm:honest-lower-full-elbow
## section: Appendix: Lower-bound construction and proof

Define the perturbation family and baseline cell laws before presenting the numbered lower-family construction. Keep its admissibility predicate explicit at the point where the probability laws are formed, and explain its role through cell nonnegativity and complier-margin compatibility. Place the legality and mixture lemma next, followed by the random-set length identity and the continuum argument establishing the converse. Track the actual compliance share of the lower family across the two strength regimes and retain the equal-size product experiment throughout. Conclude with the combination of the upper and lower arguments for the sharp result.

objs: synth_18, synth_12, synth_15, def:legal-iv-mixture, synth_17, lem:legal-iv-mixture-full-elbow, synth_16, lem:random-set-length-identity

bib: VanDerVaartTchetgenRobinsLi2009Mixtures, Tsybakov2009, Balke1997, Kitagawa2015

home_objs: def:legal-iv-mixture, lem:legal-iv-mixture-full-elbow, lem:random-set-length-identity
## section: Appendix: Comparator definitions and verification scope

Collect the supplied-geometry subclass, its score and interval, the finite-cell subclass, and the continuous witness in an auxiliary comparator subsection, with their required presentation definitions preceding first use. Treat these frozen objects as comparison apparatus and preserve the distinction between definitions and proved results. End the appendix with a brief verification note consolidating the Lean-checking scope of the supplied frozen results, the assumed sampling and model restrictions, and any theorem-local cited-dependency disclosures. Describe the checked statements at their exact scope, and identify assumed inputs through the verification metadata rather than through a contribution inventory.

objs: def:fixed-geometry-subclass, def:known-geometry-score, synth_11, def:known-geometry-interval, def:finite-cell-subclass, synth_13, def:continuous-geometry-witness

bib: CausalSmith2026TransportedLATEStrengthFrontier
home_objs: def:fixed-geometry-subclass, def:known-geometry-score, def:known-geometry-interval, def:finite-cell-subclass, def:continuous-geometry-witness
