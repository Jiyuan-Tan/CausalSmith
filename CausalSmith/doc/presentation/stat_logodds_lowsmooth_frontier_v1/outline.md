# Title
**Honest confidence intervals for homogeneous causal log odds under low smoothness**

**Contribution statement.** Under known uniform design and public propensity- and prognosis-logit Hölder exponents satisfying \(0<\beta<1/4\) and \(\beta<\alpha\le1\), the paper characterizes sharp minimax expected interval length across all effect radii and constructs one radius-independent procedure with finite-sample global coverage and matching bounds throughout this domain.

env_overrides: def:resolutions=algorithmv, def:upper-handle=algorithmv

notation_gaps: \Omega=record space and measurable structure require a presentation definition, \mathcal O=sample tuple requires a presentation definition, \mathcal C=admissible interval space requires a presentation definition, \lambda=uniform design law and independent randomization law require a presentation definition, \mathcal D=public exponent domain requires a presentation definition, \ell=logistic map requires a presentation definition, \operatorname{logit}=inverse logistic map requires a presentation definition, e(P,X)=conditional treatment probability requires a presentation definition, \mu_0(x)=control-arm conditional risk requires a presentation definition consistent with law-indexed notation, \mu_1(P,x)=treated-arm conditional risk requires a presentation definition, g(P,\cdot)=native propensity logit requires a presentation definition, \nu(P,\cdot)=native prognosis logit requires a presentation definition, \theta(P)=homogeneous scalar log-odds coefficient requires a presentation definition, [g(P,\cdot)]_\alpha=Hölder seminorm requires a presentation definition, C(P)=observable numerator coordinate requires a presentation definition, S(P)=observable denominator coordinate requires a presentation definition, s_0=positive denominator-floor constant requires a presentation definition, \Gamma(P,x)=admissible potential-outcome coupling requires a presentation definition, \Pi_k=rank-indexed projection requires a presentation definition, H_k(X_i,X_j)=projection kernel requires a presentation definition, w=conditional mean of the first mark requires a presentation definition, v=conditional mean of the second mark requires a presentation definition, \varepsilon_{\mathrm{mix}}=certified mixed-branch neighborhood radius needs an anchored presentation home, \varepsilon_{\mathrm{fair}}=certified fair-branch neighborhood radius needs an anchored presentation home, b=fixed fair-root bracket half-width needs an anchored presentation home, B=integer rational-range bound used in the concrete arithmetic routines requires an explicit presentation definition

# Notation

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(\Omega\) | \(\Omega\) | Measurable space of one observed record | notation gap |
| \(\mathcal O\) | \(\mathcal O\) | Tuple of the original observed records | notation gap |
| \(\mathcal C\) | \(\mathcal C\) | Space of admissible nonempty connected Borel effect intervals | notation gap |
| \(\lambda\) | \(\lambda\) | Uniform probability law on the unit interval | notation gap |
| \(\mathcal D\) | \(\mathcal D\) | Prescribed domain of public smoothness exponents | notation gap |
| \(\ell\) | \(\ell\) | Logistic map | notation gap |
| \(\operatorname{logit}\) | \(\operatorname{logit}\) | Inverse logistic map | notation gap |
| \(e(P,X)\) | \(e(P,X)\) | Treatment probability conditional on the covariate under the observed law | notation gap |
| \(\mu_1(P,x)\) | \(\mu_1(P,x)\) | Treated-arm conditional outcome risk under the observed law | notation gap |
| \(\mu_0(x)\) | \(\mu_0(x)\) | Control-arm conditional outcome risk in the displayed family | notation gap |
| \(\mu_1(x)\) | \(\mu_1(x)\) | Treated-arm conditional outcome risk in the displayed family | notation gap |
| \(g(P,\cdot)\) | \(g(P,\cdot)\) | Native propensity-logit function | notation gap |
| \(\nu(P,\cdot)\) | \(\nu(P,\cdot)\) | Native prognosis-logit function | notation gap |
| \(\nu(P,x)\) | \(\nu(P,x)\) | Native prognosis logit evaluated at the covariate | notation gap |
| \(\theta(P)\) | \(\theta(P)\) | Homogeneous conditional log-odds coefficient | notation gap |
| \([g(P,\cdot)]_\alpha\) | \([g(P,\cdot)]_\alpha\) | Propensity-logit Hölder seminorm at the public exponent | notation gap |
| \([\nu(P,\cdot)]_\beta\) | \([\nu(P,\cdot)]_\beta\) | Prognosis-logit Hölder seminorm at the public exponent | notation gap |
| \([f]_\gamma\) | \([f]_\gamma\) | Hölder seminorm of a continuous function at the stated exponent | notation gap |
| \(\mathcal L\) | \(\mathcal L\) | Observed laws satisfying the homogeneous logistic relation | def:logistic-class |
| \(\mathcal M(\alpha,\beta)\) | \(\mathcal M(\alpha,\beta)\) | Uniform-design homogeneous logistic laws satisfying the prescribed envelopes and seminorm bounds | def:model |
| \(\mathcal M_r(\alpha,\beta)\) | \(\mathcal M_r(\alpha,\beta)\) | Effect-radius slice of the ambient model | def:radius-model |
| \(\mathcal A_n(\alpha,\beta)\) | \(\mathcal A_n(\alpha,\beta)\) | Borel interval procedures with global \(90\%\) coverage over the ambient model | def:honest-procedures |
| \(I(\mathcal O,U)\) | \(I(\mathcal O,U)\) | Interval returned from the sample and independent randomization seed | def:honest-procedures |
| \(J_n(\alpha,\beta;r)\) | \(J_n(\alpha,\beta;r)\) | Minimax expected interval length on the radius slice subject to ambient honesty | def:length-objective |
| \(C(P)\) | \(C(P)\) | Observable numerator coordinate in the odds identity | notation gap |
| \(S(P)\) | \(S(P)\) | Observable denominator coordinate in the odds identity | notation gap |
| \(s_0\) | \(s_0\) | Uniform positive lower bound for the denominator coordinate | notation gap |
| \(\Gamma(P,x)\) | \(\Gamma(P,x)\) | Admissible conditional coupling of potential outcomes | notation gap |
| \(\widetilde P_{P,\Gamma}\) | \(\widetilde P_{P,\Gamma}\) | Full-data law generated from the coupling and observed-law treatment mechanism | def:causal-extension |
| \(Y^0\) | \(Y^0\) | Control potential outcome in the full-data construction | def:causal-extension |
| \(Y^1\) | \(Y^1\) | Treated potential outcome in the full-data construction | def:causal-extension |
| \(\Pi_k\) | \(\Pi_k\) | Projection at the stated rank | notation gap |
| \(H_k(X_i,X_j)\) | \(H_k(X_i,X_j)\) | Projection kernel evaluated at two observed covariates | notation gap |
| \(W\) | \(W\) | First bounded record mark used in the ordered-pair statistic | def:projection-statistic |
| \(V\) | \(V\) | Second bounded record mark used in the ordered-pair statistic | def:projection-statistic |
| \(w\) | \(w\) | Conditional mean of the first record mark | notation gap |
| \(v\) | \(v\) | Conditional mean of the second record mark | notation gap |
| \(\mathbb U_{n,k}(W,V)\) | \(\mathbb U_{n,k}(W,V)\) | Ordered-pair projection U-statistic for two bounded marks | def:projection-statistic |
| \(\mathsf E\) | \(\mathsf E\) | Independently fixed admissible rational interval-arithmetic engine | def:arithmetic-engine |
| \(\mathsf N\) | \(\mathsf N\) | Borel policy selecting valid names for public exponents and observed covariates | def:dyadic-name-convention |
| \(q_{\mathrm{rank}}(n)\) | \(q_{\mathrm{rank}}(n)\) | Public precision budget for selecting both projection ranks | def:resolutions |
| \(R_C\) | \(R_C\) | Real-valued target resolution for the numerator coordinate | def:resolutions |
| \(R_S\) | \(R_S\) | Real-valued target resolution for the denominator coordinate | def:resolutions |
| \([a_C,b_C]\) | \([a_C,b_C]\) | Engine enclosure of the numerator target resolution | def:resolutions |
| \([a_S,b_S]\) | \([a_S,b_S]\) | Engine enclosure of the denominator target resolution | def:resolutions |
| \(k_C(n,\alpha,\beta;\mathsf E,\mathsf N)\) | \(k_C(n,\alpha,\beta;\mathsf E,\mathsf N)\) | Integer numerator rank selected from the upper resolution enclosure | def:resolutions |
| \(k_S(n,\beta;\mathsf E,\mathsf N)\) | \(k_S(n,\beta;\mathsf E,\mathsf N)\) | Integer denominator rank selected from the upper resolution enclosure | def:resolutions |
| \(k_C\) | \(k_C\) | Retained numerator rank selected before sampling | def:coordinate-estimates |
| \(k_S\) | \(k_S\) | Retained denominator rank selected before sampling | def:coordinate-estimates |
| \(\widehat C_n\) | \(\widehat C_n\) | Sample mean of the treated outcome minus its projected product statistic | def:coordinate-estimates |
| \(\widehat S_n\) | \(\widehat S_n\) | Projected product statistic for the two displayed binary marks | def:coordinate-estimates |
| \(d_n(\alpha,\beta;r)\) | \(d_n(\alpha,\beta;r)\) | Sum of the numerator rate and the effect-radius-scaled denominator rate | def:diagnostic-envelope |
| \(s\) | \(s\) | Sum of the two public smoothness exponents in the upper construction | def:upper-handle |
| \(V_n(k)\) | \(V_n(k)\) | Public variance envelope at the stated projection rank | def:upper-handle |
| \(b_C\) | \(b_C\) | Numerator error radius in the upper construction; locally also a resolution-box endpoint | def:upper-handle; def:resolutions |
| \(b_S\) | \(b_S\) | Denominator error radius in the upper construction; locally also a resolution-box endpoint | def:upper-handle; def:resolutions |
| \(\operatorname{clip}_{[l,u]}(v)\) | \(\operatorname{clip}_{[l,u]}(v)\) | Truncation of a scalar to the displayed closed interval | def:upper-handle |
| \(c_\pm\) | \(c_\pm\) | Numerator confidence-rectangle endpoints | def:upper-handle |
| \(s_\pm\) | \(s_\pm\) | Clipped denominator confidence-rectangle endpoints | def:upper-handle |
| \(F(c,d)\) | \(F(c,d)\) | Clipped logarithmic inversion of the coordinate ratio | def:upper-handle |
| \(L\) | \(L\) | Ideal lower interval endpoint obtained by joint inversion | def:upper-handle |
| \(R\) | \(R\) | Ideal upper interval endpoint; locally also a generic true rank target | def:upper-handle; def:resolutions |
| \(K\) | \(K\) | Larger of the two retained integer ranks | def:upper-handle |
| \(q_{\mathrm{end}}(n,k_C,k_S)\) | \(q_{\mathrm{end}}(n,k_C,k_S)\) | Public precision budget for enclosing both final endpoints | def:upper-handle |
| \([L_-,L_+]\) | \([L_-,L_+]\) | Rational enclosure of the ideal lower endpoint | def:upper-handle |
| \([R_-,R_+]\) | \([R_-,R_+]\) | Rational enclosure of the ideal upper endpoint | def:upper-handle |
| \(I^{\mathrm{up}}_{n,\mathsf E,\mathsf N}(\alpha,\beta)\) | \(I^{\mathrm{up}}_{n,\mathsf E,\mathsf N}(\alpha,\beta)\) | Literal rational interval output of the fixed-budget upper construction | def:upper-handle |
| \(\rho_n(\alpha,\beta;r)\) | \(\rho_n(\alpha,\beta;r)\) | Sharp expected-length profile identified with the diagnostic envelope | def:frontier-handle |
| \(\operatorname{frontierHandle}(\mathsf E,\mathsf N)\) | \(\operatorname{frontierHandle}(\mathsf E,\mathsf N)\) | Pair consisting of the rate profile and the attaining procedure family | def:frontier-handle |
| \(I^{\mathrm{up}}_{\mathsf E,\mathsf N}\) | \(I^{\mathrm{up}}_{\mathsf E,\mathsf N}\) | Procedure sequence for the fixed engine and naming policy | def:frontier-handle |
| \(I^\star_{n,\mathsf E,\mathsf N}\) | \(I^\star_{n,\mathsf E,\mathsf N}\) | Attaining interval identified with the upper-construction output | def:frontier-handle |
| \(I_n^\star\) | \(I_n^\star\) | Concrete attaining interval for the explicit engine and dyadic-floor policy | def:frontier-handle |
| \(\mathsf E_0\) | \(\mathsf E_0\) | Explicit rational engine supplied by the constructive witness | def:arithmetic-engine; witness in lem:concrete-arithmetic-engine |
| \(\mathsf N_0\) | \(\mathsf N_0\) | Dyadic-floor naming policy | def:dyadic-name-convention |
| \(\mathsf a(\alpha,\beta)\) | \(\mathsf a(\alpha,\beta)\) | Exponent of the numerator contribution to expected interval length | def:diagnostic-envelope, with a presentation definition before first use |
| \(\mathsf b(\beta)\) | \(\mathsf b(\beta)\) | Exponent of the effect-scaled denominator contribution | def:diagnostic-envelope, with a presentation definition before first use |
| \(c_\star\) | \(c_\star\) | Lower comparison constant selected from the sharp comparison | def:frontier-handle, with a presentation definition before first use |
| \(C_\star\) | \(C_\star\) | Upper comparison constant selected from the sharp comparison | def:frontier-handle, with a presentation definition before first use |
| \(n_0\) | \(n_0\) | Sample-size threshold selected for the sharp comparison | def:frontier-handle, with a presentation definition before first use |
| \(d\) | \(d\) | Exponential effect increment in the calibration formulas | def:calibration-maps |
| \(v_*\) | \(v_*\) | Product of Bernoulli margin variances, locally specialized to the fair center | def:calibration-maps |
| \(L_*\) | \(L_*\) | Margin-dependent expression in the odds-table calibration | def:calibration-maps |
| \(D(t)\) | \(D(t)\) | Integral representation of the removable exponential quotient | def:calibration-maps |
| \(\mathfrak c(t,\xi,\upsilon)\) | \(\mathfrak c(t,\xi,\upsilon)\) | Four-cell covariance adjustment giving the prescribed odds ratio | def:calibration-maps |
| \(\mathfrak B(t,\xi,\upsilon)\) | \(\mathfrak B(t,\xi,\upsilon)\) | Smoothly extended effect-normalized covariance adjustment | def:calibration-maps |
| \(Z_u\) | \(Z_u\) | Within-cell trigonometric field generated by two independent signs | def:calibration-maps |
| \(\varepsilon_{\mathrm{mix}}\) | \(\varepsilon_{\mathrm{mix}}\) | Radius of the certified signed mixed-calibration neighborhood | notation gap |
| \(\mathfrak q(\eta,\zeta,u)\) | \(\mathfrak q(\eta,\zeta,u)\) | Unique mixed-calibration root in the fixed selection bracket | def:calibration-maps |
| \(p_*\) | \(p_*\) | Fixed fair-branch baseline risk | def:calibration-maps |
| \(\mathsf G(t,\xi)\) | \(\mathsf G(t,\xi)\) | Logistic risk shift at the stated baseline risk | def:calibration-maps |
| \(B_*\) | \(B_*\) | Fair-center normalization in the effect-shift formula | def:calibration-maps |
| \(\mathsf T(t,\delta)\) | \(\mathsf T(t,\delta)\) | Calibrated comparator effect for the fair family | def:calibration-maps |
| \(\mathfrak H(t,\delta,\xi,u)\) | \(\mathfrak H(t,\delta,\xi,u)\) | Smoothly extended normalized fair-matching residual | def:calibration-maps |
| \(\varepsilon_{\mathrm{fair}}\) | \(\varepsilon_{\mathrm{fair}}\) | Radius of the certified signed fair-calibration neighborhood | notation gap |
| \(b\) | \(b\) | Fixed fair-root bracket half-width; locally also an integer primitive base | notation gap; def:arithmetic-engine |
| \(\mathfrak p(t,\delta,u)\) | \(\mathfrak p(t,\delta,u)\) | Unique fair-calibration baseline-risk root in the fixed bracket | def:calibration-maps |
| \(\Delta\) | \(\Delta\) | Width of one cell in the equal partition | def:continuous-calibrated-priors |
| \(\mathsf Z_{k,\sigma}(x)\) | \(\mathsf Z_{k,\sigma}(x)\) | Continuous trigonometric field sharing signs at adjacent cell endpoints | def:continuous-calibrated-priors |
| \(e_0(x)\) | \(e_0(x)\) | Treatment probability in the null mixed family | def:continuous-calibrated-priors |
| \(e_1(x)\) | \(e_1(x)\) | Treatment probability in the shifted mixed family | def:continuous-calibrated-priors |
| \(e_b\) | \(e_b\) | Treatment probability selected by the mixed-family index | def:continuous-calibrated-priors |
| \(m_\sigma(x)\) | \(m_\sigma(x)\) | Sign-indexed outcome margin in the mixed family | def:continuous-calibrated-priors |
| \(m_\sigma\) | \(m_\sigma\) | Outcome margin evaluated at the current covariate in the four-cell formulas | def:continuous-calibrated-priors |
| \(c_0(x)\) | \(c_0(x)\) | Null-family covariance adjustment | def:continuous-calibrated-priors |
| \(c_1(x)\) | \(c_1(x)\) | Shifted-family calibrated covariance adjustment | def:continuous-calibrated-priors |
| \(c_b\) | \(c_b\) | Covariance adjustment selected by the mixed-family index | def:continuous-calibrated-priors |
| \(p_{11}\) | \(p_{11}\) | Conditional treated-success cell probability | def:continuous-calibrated-priors |
| \(p_{10}\) | \(p_{10}\) | Conditional treated-failure cell probability | def:continuous-calibrated-priors |
| \(p_{01}\) | \(p_{01}\) | Conditional control-success cell probability | def:continuous-calibrated-priors |
| \(p_{00}\) | \(p_{00}\) | Conditional control-failure cell probability | def:continuous-calibrated-priors |
| \(P_{b,\sigma}\) | \(P_{b,\sigma}\) | Sign-indexed calibrated mixed observed law | def:continuous-calibrated-priors |
| \(P_{0,\sigma}\) | \(P_{0,\sigma}\) | Null member of the calibrated mixed family | def:continuous-calibrated-priors |
| \(P_{1,\sigma}\) | \(P_{1,\sigma}\) | Shifted member of the calibrated mixed family | def:continuous-calibrated-priors |
| \(P_{t,\sigma}\) | \(P_{t,\sigma}\) | Sign-indexed fair-treatment law with homogeneous effect at the stated center | def:continuous-calibrated-priors |
| \(P_{*,t,\delta}\) | \(P_{*,t,\delta}\) | Deterministic fair-treatment comparator with calibrated effect | def:continuous-calibrated-priors |
| \(Q_b\) | \(Q_b\) | Uniform finite mixture of mixed-family original-record sample laws | def:continuous-calibrated-priors |
| \(Q_0\) | \(Q_0\) | Null mixed-family sample mixture | def:continuous-calibrated-priors |
| \(Q_1\) | \(Q_1\) | Shifted mixed-family sample mixture | def:continuous-calibrated-priors |
| \(Q_t\) | \(Q_t\) | Uniform finite mixture of fair-family original-record sample laws | def:continuous-calibrated-priors |
| \(\mathcal H^2(Q,Q')\) | \(\mathcal H^2(Q,Q')\) | Squared Hellinger distance under the displayed normalization | def:continuous-calibrated-priors, with a presentation definition before first use |
| \(\epsilon_q\) | \(\epsilon_q\) | Dyadic primitive endpoint-excess tolerance | def:arithmetic-engine |
| \(B\) | \(B\) | Integer bound determined by rational primitive input ranges | notation gap |

Symbols defined within proved statements but lacking a Definition environment also require anchored presentation homes: add \(\mathsf a(\alpha,\beta)\), \(\mathsf b(\beta)\), \(c_\star\), \(C_\star\), \(n_0\), and \(\mathcal H^2(Q,Q')\) to the corresponding object-family presentation definitions indicated above. Keep bound variables, routine truncation counts, and theorem-local existential constants local to their environments. Resolve the distinct local meanings of \(b_C\), \(b_S\), \(R\), and \(b\) explicitly at their respective uses.

# Sections

## section: Abstract

Plan the abstract after completion of the body. Identify the homogeneous causal conditional log-odds target, known uniform design, and public unequal smoothness exponents; summarize the sharp all-radius expected-length characterization and the attaining globally honest interval. Describe the two rate contributions in words before introducing their symbols, and emphasize finite-sample coverage and simultaneous radius evaluation.

objs: none
bib: none

home_objs: none
## section: Introduction

Lead with the precision of honest inference for a homogeneous conditional causal log-odds coefficient when prognosis is rougher than propensity. Explain why effect magnitude changes attainable interval length while coverage remains global over the ambient model. Present the positive contribution and its full exponent and radius scope, followed by a short roadmap. Include one factual sentence pointing to the appendix verification note. Write this section after the results, interpretation, and proof architecture are settled.

objs: none
bib: none

home_objs: none
## section: Related work

Compare the target and inference criterion with the closest logistic coefficient results: the nuisance-model robustness and near-null efficiency comparisons of \citet[Propositions 1--3]{Tan2019LogisticDR}, the regular asymptotic coefficient inference of \citet[arXiv version 1, Assumptions REG and ML1, Theorem 2]{LiuZhangZhou2020LogisticDML}, and the conditional log-odds treatment-effect formulation and finite-dimensional coefficient bounds of \citet[Sections 2.1.1 and 3.3, equation (5), Proposition 1]{GaoHastie2025DINA}. Position the numerator through the known-design covariance results of \citet[version 5, Theorem 1 and Corollary 1]{McGrath2026} and \citet[arXiv version 3, Assumption 4 and Theorems 2--3]{McCleanBalakrishnanKennedyWasserman2024DCDR}. Compare the homogeneous-model converse with \citet[Appendix B]{JinMackeySyrgkanis2025HardNormal} and the unrestricted average log-odds lower bound of \citet[version 2, Theorem 7.7]{JinSyrgkanis2025GeneralLinearLower}. Explain the relation to implicit-moment higher-order inference using its stated conditions and error components, and connect ambient honesty with subclass length evaluation to the honest-interval literature. Organize these comparisons around estimand, statistical class, coverage criterion, and delivered precision; reserve novelty language for the joint all-radius characterization in the prescribed homogeneous logistic experiment.

objs: none
bib: Tan2019LogisticDR, LiuZhangZhou2020LogisticDML, GaoHastie2025DINA, TchetgenTchetgen2010, TchetgenTchetgen2013, VansteelandtDukes2022AssumptionLean, McGrath2026, McCleanBalakrishnanKennedyWasserman2024DCDR, Hoeffding1948, Donoho1990, Laurent1996, Gine2008, RobinsEtAlHigherOrderInfluenceFunctions, JinMackeySyrgkanis2025HardNormal, JinSyrgkanis2025GeneralLinearLower, ZhangLiuZhang2026GeneralTreatmentHOIF, RobinsTchetgenLiVanderVaart2009Minimax, Low1997, CaiLow2004ConfidenceAdaptation

home_objs: none
## section: Model and honest interval criterion

Introduce the observed record, conditional risks, native propensity and prognosis logits, logistic maps, public exponent domain, and known design law through grouped presentation definitions before their first use. Establish the homogeneous conditional odds interpretation and state the model restrictions. Separate the ambient coverage class from the effect-radius evaluation slices, then introduce the expected-length objective. Explain the independent seed as part of the comparison class and the causal interpretation through the observable-odds result, with the full-data construction housed in the appendix.

objs: ass:uniform-design, synth_2, synth_4, synth_1, ass:homogeneous-logit, ass:effect-envelope, ass:propensity-envelope, ass:prognosis-envelope, ass:propensity-holder, ass:prognosis-holder, def:logistic-class, def:model, ass:evaluation-radius, def:radius-model, ass:global-coverage, def:honest-procedures, def:length-objective
bib: Rubin1974, Rosenbaum1983, Greenland1999

home_objs: ass:uniform-design, ass:homogeneous-logit, ass:effect-envelope, ass:propensity-envelope, ass:prognosis-envelope, ass:propensity-holder, ass:prognosis-holder, def:logistic-class, def:model, ass:evaluation-radius, def:radius-model, ass:global-coverage, def:honest-procedures, def:length-objective
## section: Sharp expected length across effect radii

Introduce the two rate contributions and the concrete attaining sequence, then place the headline comparison in \cref{thm:full-honest-frontier-answer}. Interpret ambient honesty at the null radius, arbitrary shrinking-radius sequences, and fixed positive radii. Explain the numerator transition and the radius balance using the public smoothness exponents, including the shared boundary and the propensity endpoint. Present the attainable sequence as a statistical interval procedure; direct readers to the following construction and the technical appendix for its arithmetic realization. Keep the engine-and-policy generality as a supporting guarantee attached to the same statistical result.

objs: def:diagnostic-envelope, synth_3, def:projection-statistic, def:dyadic-name-convention, def:arithmetic-engine, def:resolutions, def:coordinate-estimates, def:causal-extension, synth_5, def:calibration-maps, def:continuous-calibrated-priors, def:frontier-handle, thm:full-honest-frontier-answer
bib: none

home_objs: def:diagnostic-envelope, synth_3, def:projection-statistic, def:dyadic-name-convention, def:arithmetic-engine, def:resolutions, def:coordinate-estimates, def:causal-extension, synth_5, def:calibration-maps, def:continuous-calibrated-priors, def:frontier-handle, thm:full-honest-frontier-answer
## section: Constructing an honest interval

Define the observable coordinate family and the projection family before introducing the ordered-pair statistic. Explain why separate resolutions govern the numerator and denominator and how a confidence rectangle is inverted into an effect interval. Present the rank selection and central interval construction as numbered algorithms, followed by \cref{thm:finite-honest-upper}. Distinguish the exact-real expressions used for analysis from the rational output returned on valid named inputs, and refer to the appendix definitions for admissible arithmetic and naming conventions. Explain the radius-independent construction, clipping, and full-interval output at sample size one as parts of the delivered finite-sample procedure.

objs: def:upper-handle, thm:finite-honest-upper
bib: Hoeffding1948

home_objs: def:projection-statistic, def:resolutions, def:coordinate-estimates, def:upper-handle, thm:finite-honest-upper
## section: Interpretation and limitations

Interpret the paper’s two precision contributions, the persistence of ambient coverage when evaluation concentrates near zero, and the balance between effect magnitude and rough prognosis. Explain what the known design and public exponents contribute to this experiment. Include a clearly titled “Limitations and future work” subsection for unknown design, unknown smoothness, higher-dimensional covariates, heterogeneous effects, and practical calibration or computational optimization. Keep prospective empirical or software assessment within that subsection and distinguish it from the proved precision characterization.

objs: none
bib: none

home_objs: none
## section: Appendix A: Identification and projection bounds

Place the potential-outcome coupling presentation definition before the full-data construction. Prove the observable coordinate identity, denominator floor, and causal extension properties, then give the projection approximation, product-bias identity, and variance control. Keep the general projection notation aligned with its main-text presentation definition and use these bounds as the statistical inputs to the interval proof.

objs: lem:observable-odds, lem:projection-control
bib: Rubin1974, Rosenbaum1983, Hoeffding1948

home_objs: lem:observable-odds, lem:projection-control
## section: Appendix B: Rational realization and the upper bound

Introduce the naming convention and primitive arithmetic contracts before their first use in this appendix. Establish the explicit engine witness, then prove the uniform rank and endpoint enclosure guarantees and the upper theorem. Separate primitive admissibility from the derived precision budgets, termination, measurability, and statistical conclusions. Track the retained ranks through the endpoint calculation and explain the common guarantees for potentially different outputs under different admissible engines and valid names.

objs: lem:concrete-arithmetic-engine, lem:fixed-budget-realization
bib: none

home_objs: lem:concrete-arithmetic-engine, lem:fixed-budget-realization
## section: Appendix C: Exact calibration and same-model alternatives

Introduce all local calibration neighborhoods and maps before constructing the finite prior families. Present the scalar implicit-function tool, prove the two calibration branches on their certified domains, and establish the continuous native-logit support and joint derivative certificate. Explain the shared-endpoint sign construction and exact singleton matching as the devices preserving the homogeneous scalar coefficient and prescribed smoothness in each prior draw. Keep branch selectors and implementation identifiers confined to the technical treatment carried by the frozen objects.

objs: lem:scalar-implicit-function, lem:exact-calibrations, lem:calibrated-support
bib: RobinsTchetgenLiVanderVaart2009Minimax, JinMackeySyrgkanis2025HardNormal

home_objs: def:calibration-maps, lem:scalar-implicit-function, lem:exact-calibrations, def:continuous-calibrated-priors, lem:calibrated-support
## section: Appendix D: Original-record lower bounds and sharp comparison

Define the Hellinger normalization before the mixture bound. Prove the original-record mixture comparisons using the jointly certified calibration constants and the stipulated occupancy condition. Combine the parametric null comparison, mixed alternatives, and fair alternatives to establish the sharp comparison and its full-domain synthesis. Explain how the ambient honesty requirement yields length lower bounds on evaluation slices, including the null slice, and keep each retained theorem environment in its assigned place.

objs: synth_6, lem:original-record-mixtures, lem:parametric-null-floor, thm:sharp-honest-frontier, thm:full-honest-frontier-solution
bib: RobinsTchetgenLiVanderVaart2009Minimax, Low1997, CaiLow2004ConfidenceAdaptation

home_objs: lem:original-record-mixtures, lem:parametric-null-floor, thm:sharp-honest-frontier, thm:full-honest-frontier-solution
## section: Appendix E: Verification note

End the appendix with a concise consolidation of machine-checking scope. Identify the supplied theorem and lemma objects covered by the frozen formal layer, distinguish the model restrictions and primitive contracts taken as inputs from conclusions established under them, and preserve theorem-local disclosures for cited dependencies. Explain the role of valid names and the explicit arithmetic witness in the represented construction. Treat this note as verification metadata and keep the introduction’s reference to it factual.

objs: none
bib: none
home_objs: none
