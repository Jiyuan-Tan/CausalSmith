# Title
**Estimating optimal treatment value with many covariate cells and shrinking overlap**

**Contribution statement.** For binary treatments and outcomes with categorical covariates, the paper establishes the minimax squared-error rate \(\min\{1,d/[n\epsilon\log(ed)]\}\), where \(n\) is sample size, \(d\) is the number of covariate cells, and \(\epsilon\) is the public overlap floor, with universal comparison constants, an attaining observed-data estimator, and a matching consistency criterion.

# Notation

env_overrides: prop:identification=propositionv, def:armwise-estimator=algorithmv, oeq:sharp-path-constant=remarkv

notation_gaps: \(O_i\)=observed unit and sample alphabet require an anchored sampling definition, \(X\)=categorical covariate and its support require an anchored data definition, \(A\)=binary treatment requires an anchored data definition, \(Y\)=binary observed outcome requires an anchored data definition, \(Y(a)\)=potential outcome requires an anchored causal-data definition, \([d]\)=finite covariate alphabet requires an anchored definition, \(\mathcal J_d\)=observed atom index set requires an anchored definition, \(q_{a1,x}\)=observed atom mass requires an anchored definition, \(q_{a0,x}\)=observed atom mass requires an anchored definition, \(q_x\)=four-vector of observed atom masses requires an anchored definition, \(p_x\)=covariate cell probability requires an anchored definition, \(\pi_x\)=conditional treatment probability requires an anchored definition, \(\mu_{ax}\)=conditional outcome mean requires an anchored definition, \(\operatorname{Obs}(P)\)=observed marginal law requires an anchored definition, \(V^\star(P)\)=causal oracle value requires an anchored definition, \(L_d\)=logarithmic alphabet scale needs an anchored definition before its first main-result use, \(\phi_\epsilon(z)\)=weighted scalar positive-part functional occurs without a defining formula in the frozen layer, \(\mathbb R_K[z]\)=polynomial class is described but its degree convention needs explicit resolution before the approximation result, \(B\)=auxiliary Poisson inflation parameter needs an anchored experiment definition, \(z_\star\)=reference intensity occurs without a defining formula in the frozen layer, \(L_z\)=one-cell likelihood ratio requires an anchored experiment definition, \(L_w\)=one-cell likelihood ratio requires an anchored experiment definition, \(\alpha\)=Gram coefficient requires an anchored experiment definition, \(\Delta_a\)=armwise perturbation is introduced in a lemma rather than an anchored definition, \(\mathcal J_N(u)\)=normalized periodic Jackson function is introduced in a lemma rather than an anchored definition, \(c_N\)=normalizing constant requires an anchored packet definition, \(k_N(u)\)=modulated Jackson function requires an anchored packet definition, \(\widehat h(j)\)=Fourier coefficient operator requires an anchored packet definition, \(a_j^{\pm}\)=zero-extended Fourier coefficient sequences require an anchored packet definition, \((\delta a)_j\)=forward difference operator requires an anchored packet definition, \(\delta^2a_j^{\pm}\)=second forward difference requires an anchored packet definition, \(G_N\)=zero-mean periodic twice antiderivative requires an anchored packet definition, \(\|u\|_{\mathbb T}\)=distance to the periodic origin requires an anchored packet definition

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(n\) | \(n\) | Number of observed units | Sampling definition gap |
| \(d\) | \(d\) | Number of categorical covariate cells | Data definition gap |
| \([d]\) | \([d]\) | Finite covariate alphabet | Data definition gap |
| \(O_i\) | \(O_i\) | Observed unit indexed by sample position | Sampling definition gap |
| \(O_1,\ldots,O_n\) | \(O_1,\ldots,O_n\) | Observed sample | Sampling definition gap |
| \(X\) | \(X\) | Categorical covariate | Data definition gap |
| \(A\) | \(A\) | Binary treatment | Data definition gap |
| \(Y\) | \(Y\) | Binary observed outcome | Data definition gap |
| \(Y(0)\) | \(Y(0)\) | Potential outcome under treatment zero | Causal-data definition gap |
| \(Y(1)\) | \(Y(1)\) | Potential outcome under treatment one | Causal-data definition gap |
| \(Y(a)\) | \(Y(a)\) | Potential outcome under treatment \(a\) | Causal-data definition gap |
| \(\mathcal J_d\) | \(\mathcal J_d\) | Observed atom index set | Data definition gap |
| \(\mathbb P\) | \(\mathbb P\) | Observed probability law | def:observed-class |
| \(P\) | \(P\) | Full-data probability law in causal expressions; polynomial in approximation expressions | def:causal-class; def:weighted-error |
| \(q_{a1,x}\) | \(q_{a1,x}\) | Observed atom probability with outcome one | Atom definition gap |
| \(q_{a0,x}\) | \(q_{a0,x}\) | Observed atom probability with outcome zero | Atom definition gap |
| \(q_x\) | \(q_x\) | Four-vector of observed atom probabilities in cell \(x\) | Atom definition gap |
| \(p_x\) | \(p_x\) | Probability of covariate cell \(x\) | Cell-quantity definition gap |
| \(\pi_x\) | \(\pi_x\) | Treatment-one probability conditional on cell \(x\) | Cell-quantity definition gap |
| \(\mu_{ax}\) | \(\mu_{ax}\) | Outcome mean conditional on arm \(a\) and cell \(x\) | Cell-quantity definition gap |
| \(\mathcal D_{d,\epsilon}^{\mathrm{obs}}\) | \(\mathcal D_{d,\epsilon}^{\mathrm{obs}}\) | Observed laws satisfying the public overlap restriction | def:observed-class |
| \(\mathcal P_{d,\epsilon}\) | \(\mathcal P_{d,\epsilon}\) | Consistent, conditionally exchangeable causal completions | def:causal-class |
| \(\operatorname{Obs}(P)\) | \(\operatorname{Obs}(P)\) | Observed marginal of a full-data law | Marginal-law definition gap |
| \(\Psi(\mathbb P)\) | \(\Psi(\mathbb P)\) | Cell-mass-weighted maximum conditional outcome mean | def:observed-value |
| \(V^\star(P)\) | \(V^\star(P)\) | Unrestricted optimal causal treatment value | Causal-value definition gap |
| \(\mathfrak R_{n,d,\epsilon}\) | \(\mathfrak R_{n,d,\epsilon}\) | Minimax squared-error risk over the observed class | def:minimax-risk |
| \(\widehat V\) | \(\widehat V\) | Measurable real-valued estimator of the observed value | def:minimax-risk |
| \(L_d\) | \(L_d\) | Logarithmic alphabet scale | Rate-scale definition gap |
| \(c_\star\) | \(c_\star\) | Universal lower risk comparison constant | thm:matched-frontier; theorem-local constant |
| \(C_\star\) | \(C_\star\) | Universal upper risk comparison constant | thm:matched-frontier; theorem-local constant |
| \(s_a(u)\) | \(s_a(u)\) | Sum of the two outcome coordinates in arm \(a\) | def:armwise-extension |
| \(s(u)\) | \(s(u)\) | Total mass of the four-vector | def:armwise-extension |
| \(D_a(u)\) | \(D_a(u)\) | Arm mass truncated below by the overlap-scaled total mass | def:armwise-extension |
| \(F_\epsilon(u)\) | \(F_\epsilon(u)\) | Anchored extension of the cell contribution | def:armwise-extension |
| \(u_{a0}\) | \(u_{a0}\) | Outcome-zero coordinate of arm \(a\) in a four-vector | def:armwise-extension |
| \(u_{a1}\) | \(u_{a1}\) | Outcome-one coordinate of arm \(a\) in a four-vector | def:armwise-extension |
| \(v_{ay}\) | \(v_{ay}\) | Arm-outcome coordinate of a comparison four-vector | def:armwise-extension |
| \(\Delta_a\) | \(\Delta_a\) | Sum of absolute coordinate perturbations in arm \(a\) | Armwise-perturbation definition gap |
| \(n_{\mathrm p}\) | \(n_{\mathrm p}\) | Deterministic pilot sample size | def:fixed-sample-factorial |
| \(n_{\mathrm e}\) | \(n_{\mathrm e}\) | Deterministic evaluation sample size | def:fixed-sample-factorial |
| \(I_{\mathrm p}\) | \(I_{\mathrm p}\) | Deterministic pilot index set | def:fixed-sample-factorial |
| \(I_{\mathrm e}\) | \(I_{\mathrm e}\) | Deterministic evaluation index set | def:fixed-sample-factorial |
| \(N_j^{\mathrm p}\) | \(N_j^{\mathrm p}\) | Pilot count for observed atom \(j\) | def:fixed-sample-factorial |
| \(N_j^{\mathrm e}\) | \(N_j^{\mathrm e}\) | Evaluation count for observed atom \(j\) | def:fixed-sample-factorial |
| \(N^{\mathrm e}\) | \(N^{\mathrm e}\) | Vector of deterministic-split evaluation counts | def:fixed-sample-factorial |
| \((m)_k\) | \((m)_k\) | Falling factorial of order \(k\) | def:fixed-sample-factorial |
| \((m)_0\) | \((m)_0\) | Zeroth falling factorial | def:fixed-sample-factorial |
| \(\boldsymbol h\) | \(\boldsymbol h\) | Multi-index of factorial orders | def:fixed-sample-factorial |
| \(\boldsymbol t\) | \(\boldsymbol t\) | Multi-index in the centered factorial expansion | def:fixed-sample-factorial |
| \(|\boldsymbol h|\) | \(|\boldsymbol h|\) | Total order of the factorial multi-index | def:fixed-sample-factorial |
| \(|\boldsymbol t|\) | \(|\boldsymbol t|\) | Total order of an expansion multi-index | def:fixed-sample-factorial |
| \(h_j\) | \(h_j\) | Atom-specific factorial order | def:fixed-sample-factorial |
| \(t_j\) | \(t_j\) | Atom-specific expansion order | def:fixed-sample-factorial |
| \(b\) | \(b\) | Centering vector for the multinomial factorial statistic | def:fixed-sample-factorial |
| \(b_j\) | \(b_j\) | Atom-specific centering coordinate | def:fixed-sample-factorial |
| \(U_{\boldsymbol h}(N^{\mathrm e};b)\) | \(U_{\boldsymbol h}(N^{\mathrm e};b)\) | Centered multinomial factorial statistic | def:fixed-sample-factorial |
| \(L\) | \(L\) | Local logarithmic scale in estimation; modulation frequency in packet analysis | def:armwise-estimator; packet definition gap |
| \(m\) | \(m\) | Evaluation Poisson intensity in the estimator | def:armwise-estimator |
| \(K_n\) | \(K_n\) | Alphabet-dependent approximation tuning degree | def:armwise-estimator |
| \(H_0\) | \(H_0\) | Universal pilot-radius calibration constant | def:armwise-estimator |
| \(\kappa\) | \(\kappa\) | Universal degree calibration constant | def:armwise-estimator |
| \(D_0\) | \(D_0\) | Universal bounded-alphabet branch threshold | def:armwise-estimator |
| \(\widehat V_{n,d,\epsilon}^{\mathrm{AF}}\) | \(\widehat V_{n,d,\epsilon}^{\mathrm{AF}}\) | Deterministic observed-data estimator assembled by the prescribed branches | def:armwise-estimator |
| \(N_x\) | \(N_x\) | Full-sample covariate cell count | def:armwise-estimator |
| \(N_{ax}\) | \(N_{ax}\) | Full-sample arm count within cell \(x\) | def:armwise-estimator |
| \(S_{ax}\) | \(S_{ax}\) | Full-sample outcome sum within arm \(a\) and cell \(x\) | def:armwise-estimator |
| \(\mathsf M\) | \(\mathsf M\) | Auxiliary Poisson count subject to the sample-size cap | def:armwise-estimator |
| \(\mathsf B_i\) | \(\mathsf B_i\) | Fair auxiliary mark allocating a selected unit | def:armwise-estimator |
| \(N'_{ay,x}\) | \(N'_{ay,x}\) | Mark-one pilot atom count | def:armwise-estimator |
| \(N_{ay,x}\) | \(N_{ay,x}\) | Mark-zero evaluation atom count | def:armwise-estimator |
| \(c_{ay,x}\) | \(c_{ay,x}\) | Pilot atom count divided by evaluation intensity | def:armwise-estimator |
| \(h_{ay,x}\) | \(h_{ay,x}\) | Pilot-based localization radius | def:armwise-estimator |
| \(\ell_{ay,x}\) | \(\ell_{ay,x}\) | Nonnegative lower localization endpoint | def:armwise-estimator |
| \(u_{ay,x}\) | \(u_{ay,x}\) | Upper localization endpoint | def:armwise-estimator |
| \(b_{ay,x}\) | \(b_{ay,x}\) | Midpoint of the localization interval | def:armwise-estimator |
| \(r_{ay,x}\) | \(r_{ay,x}\) | Half-width of the localization interval | def:armwise-estimator |
| \(b_x\) | \(b_x\) | Four-vector of localization midpoints | def:armwise-estimator |
| \(r_x\) | \(r_x\) | Four-vector of localization half-widths | def:armwise-estimator |
| \(Q_x\) | \(Q_x\) | Product localization rectangle for cell \(x\) | def:armwise-estimator |
| \(J_{K_n}(t)\) | \(J_{K_n}(t)\) | Normalized fourth-power Jackson approximation kernel | def:armwise-estimator |
| \(c_{K_n}^{\mathrm J}\) | \(c_{K_n}^{\mathrm J}\) | Jackson kernel normalizing constant | def:armwise-estimator |
| \(\odot\) | \(\odot\) | Componentwise vector multiplication | def:armwise-estimator |
| \(P_{x,K_n}\) | \(P_{x,K_n}\) | Tensor Jackson polynomial on the localization rectangle | def:armwise-estimator |
| \(D\) | \(D\) | Maximum coordinate degree of the tensor polynomial | def:armwise-estimator |
| \(\boldsymbol\alpha\) | \(\boldsymbol\alpha\) | Tensor polynomial multi-index | def:armwise-estimator |
| \(\alpha_{ay}\) | \(\alpha_{ay}\) | Arm-outcome coordinate of the tensor multi-index | def:armwise-estimator |
| \(\beta_{x,\boldsymbol\alpha}\) | \(\beta_{x,\boldsymbol\alpha}\) | Centered and rescaled tensor polynomial coefficient | def:armwise-estimator |
| \(U_k(N;\zeta)\) | \(U_k(N;\zeta)\) | Centered Poisson factorial statistic of order \(k\) | def:armwise-estimator |
| \(Z_x\) | \(Z_x\) | Factorial estimate of the localized polynomial contribution | def:armwise-estimator |
| \(R_{a,x}\) | \(R_{a,x}\) | Sum of localization half-widths within arm \(a\) | def:armwise-estimator |
| \(w_{a,x}\) | \(w_{a,x}\) | Armwise sensitivity weight at the localization center | def:armwise-estimator |
| \(S_x^{\mathrm{aw}}\) | \(S_x^{\mathrm{aw}}\) | Armwise weighted clipping scale | def:armwise-estimator |
| \(T_x\) | \(T_x\) | Clipped polynomial contribution for cell \(x\) | def:armwise-estimator |
| \(\Pi_{[0,1]}\) | \(\Pi_{[0,1]}\) | Projection onto the unit interval | def:armwise-estimator |
| \(\Pi_{[F_\epsilon(b_x)-d^{1/4}S_x^{\mathrm{aw}},\,F_\epsilon(b_x)+d^{1/4}S_x^{\mathrm{aw}}]}\) | \(\Pi_{[F_\epsilon(b_x)-d^{1/4}S_x^{\mathrm{aw}},\,F_\epsilon(b_x)+d^{1/4}S_x^{\mathrm{aw}}]}\) | Projection onto the cell-specific clipping interval | def:armwise-estimator |
| \(\widetilde V\) | \(\widetilde V\) | Projected sum of clipped cell contributions with the prescribed cap-event value | def:armwise-estimator |
| \(K\) | \(K\) | Scalar polynomial and matched-moment degree | def:constrained-prior-separation |
| \(M\) | \(M\) | Scalar intensity support endpoint | def:constrained-prior-separation |
| \(\phi_\epsilon(z)\) | \(\phi_\epsilon(z)\) | Weighted scalar positive-part functional | Scalar-functional definition gap |
| \(\mathbb R_K[z]\) | \(\mathbb R_K[z]\) | Real polynomials of degree at most \(K\) | def:weighted-error |
| \(\mathcal E_{K,M,\epsilon}^{w}\) | \(\mathcal E_{K,M,\epsilon}^{w}\) | Weighted best uniform polynomial approximation error | def:weighted-error |
| \(\mathfrak N_{K,M}\) | \(\mathfrak N_{K,M}\) | Probability-prior pairs with common mean one and matching moments through degree \(K\) | def:constrained-prior-separation |
| \((\nu_0,\nu_1)\) | \((\nu_0,\nu_1)\) | Pair of constrained probability priors | def:constrained-prior-separation |
| \(\Delta_{K,M,\epsilon}\) | \(\Delta_{K,M,\epsilon}\) | Largest scalar target separation over constrained prior pairs | def:constrained-prior-separation |
| \(\mathbf z\in[0,M]^d\) | \(\mathbf z\in[0,M]^d\) | Vector of bounded cell intensities | def:sparse-family |
| \(z_x\) | \(z_x\) | Scalar intensity in covariate cell \(x\) | def:sparse-family |
| \(\widetilde q_{11,x}\) | \(\widetilde q_{11,x}\) | Unnormalized treated-success atom mass | def:sparse-family |
| \(\widetilde q_{10,x}\) | \(\widetilde q_{10,x}\) | Unnormalized treated-failure atom mass | def:sparse-family |
| \(\widetilde q_{00,x}\) | \(\widetilde q_{00,x}\) | Unnormalized control-failure atom mass | def:sparse-family |
| \(\widetilde q_{01,x}\) | \(\widetilde q_{01,x}\) | Unnormalized control-success atom mass | def:sparse-family |
| \(\widetilde q_{ay,x}\) | \(\widetilde q_{ay,x}\) | Arm-outcome atom mass in the unnormalized sparse family | def:sparse-family |
| \(S(\mathbf z)\) | \(S(\mathbf z)\) | Total unnormalized sparse-family mass | def:sparse-family |
| \(\mathbb P_{\mathbf z}^{\mathrm{sp}}\) | \(\mathbb P_{\mathbf z}^{\mathrm{sp}}\) | Normalized sparse observed law | def:sparse-family |
| \(\sigma_+\) | \(\sigma_+\) | Nonnegative input measure with finite first moment | def:weighted-handle |
| \(\sigma_-\) | \(\sigma_-\) | Nonnegative input measure with finite first moment | def:weighted-handle |
| \(t\) | \(t\) | Total mass of the positive input measure in the completion map | def:weighted-handle |
| \(u\) | \(u\) | First moment of the positive input measure in the completion map | def:weighted-handle |
| \(z_0\) | \(z_0\) | Location of the common completion atom | def:weighted-handle |
| \(\delta_{z_0}\) | \(\delta_{z_0}\) | Unit point mass at the completion location | def:weighted-handle |
| \(\mathscr H^w(\sigma_+,\sigma_-)\) | \(\mathscr H^w(\sigma_+,\sigma_-)\) | Common-atom completion map for the two input measures | def:weighted-handle |
| \(B\) | \(B\) | Total-mean inflation in the auxiliary Poisson experiment | Auxiliary-experiment definition gap |
| \(z_\star\) | \(z_\star\) | Reference intensity for the likelihood comparison | Auxiliary-experiment definition gap |
| \(L_z\) | \(L_z\) | One-cell likelihood ratio at scalar intensity \(z\) | Auxiliary-experiment definition gap |
| \(L_w\) | \(L_w\) | One-cell likelihood ratio at scalar intensity \(w\) | Auxiliary-experiment definition gap |
| \(\alpha\) | \(\alpha\) | Exact coefficient in the one-cell likelihood Gram identity | Auxiliary-experiment definition gap |
| \(N\) | \(N\) | Integer packet resolution in localization analysis; count argument in factorial estimation | Packet definition gap; def:armwise-estimator |
| \(\mathcal J_N(u)\) | \(\mathcal J_N(u)\) | Periodically normalized fourth-power Jackson function | Packet definition gap |
| \(c_N\) | \(c_N\) | Periodic Jackson normalizing constant | Packet definition gap |
| \(k_N(u)\) | \(k_N(u)\) | Jackson function modulated by the specified cosine frequency | Packet definition gap |
| \(\widehat h(j)\) | \(\widehat h(j)\) | Periodic Fourier coefficient of a function \(h\) | Packet definition gap |
| \(\widehat{\mathcal J_N}(j)\) | \(\widehat{\mathcal J_N}(j)\) | Fourier coefficient of the periodic Jackson function | Packet definition gap |
| \(a_j^{\pm}\) | \(a_j^{\pm}\) | Zero-extended Fourier coefficients divided by squared shifted frequencies | Packet definition gap |
| \((\delta a)_j\) | \((\delta a)_j\) | First forward difference of a coefficient sequence | Packet definition gap |
| \(\delta^2a_j^{\pm}\) | \(\delta^2a_j^{\pm}\) | Second forward difference of the zero-extended coefficient sequences | Packet definition gap |
| \(G_N\) | \(G_N\) | Unique zero-mean periodic twice antiderivative of the modulated Jackson function | Packet definition gap |
| \(\|u\|_{\mathbb T}\) | \(\|u\|_{\mathbb T}\) | Distance from \(u\) to the nearest multiple of \(2\pi\) | Packet definition gap |
| \(c\) | \(c\) | Universal lower comparison constant local to an auxiliary result | Theorem-local or lemma-local constant |
| \(C\) | \(C\) | Universal upper comparison constant local to an auxiliary result | Theorem-local or lemma-local constant |
| \(d_n\) | \(d_n\) | Covariate alphabet size along a triangular sequence | def:observed-class; sequence-local parameter |
| \(\epsilon_n\) | \(\epsilon_n\) | Public overlap floor along a triangular sequence | def:observed-class; sequence-local parameter |

# Sections

## section: Abstract

Plan a compact statement of the statistical question, the categorical observational model, the uniform minimax rate, the attaining construction, and the resulting consistency criterion. Gloss sample size, alphabet size, and overlap floor before using their symbols. Present the causal interpretation under consistency and conditional exchangeability. Write this section last, after the exposition and proof organization are settled.

objs: none

bib: none

home_objs: none
## section: Introduction

Lead with estimating the population value obtainable by assigning the better treatment within each covariate cell. Explain why the combination of many cells, rare treatment assignments, and treatment-effect ties makes this a useful precision benchmark. State the positive scope of the contribution, emphasize uniformity over unknown cell masses and propensities, and introduce the two statistical ideas: armwise polynomial estimation and normalized moment-matched lower experiments. Include one factual sentence directing readers to the appendix verification note. Write this section after the main body, and leave detailed literature comparisons to the immediately following section.

objs: none

bib: Murphy2003, Manski2004

home_objs: none
## section: Related work

Organize the comparison around estimand, statistical experiment, and uniformity domain. The closest estimand-specific results are optimal-value differentiability and inference in Luedtke and van der Laan, subagging inference in Shi and coauthors, and smoothed optimal-value inference in Whitehouse and coauthors; preserve the supplied theorem and assumption locators and compare their asymptotic conditions with the present uniform finite-cell risk characterization. The nearest discrete-causal comparison is Zeng and coauthors’ linear arm-mean analysis, using the June 2026 revision and its overlap-dependent bounds. Compare the polynomial approximation architecture with Jiao, Venkat, Han, and Weissman and with Jiao, Han, and Weissman’s \(L_1\)-distance results, retaining their regime qualifications. Distinguish the scalar optimized-value estimand from policy-class regret in Kitagawa and Tetenov, Athey and Wager, and Jin and coauthors, and from specified-policy evaluation in Ma and coauthors. Describe the extension of the supplied same-target fixed-overlap result conservatively; bibliographic citation of that archive requires a verified pool entry at a later stage.

objs: none

bib: LuedtkeVanderLaan2016OptimalValue, Shi2020, WhitehouseChenAusternSyrgkanis2025, ZengBalakrishnanHanKennedy2024Discrete, JiaoVenkatHanWeissman2015Functionals, JiaoHanWeissman2018L1, HanJiaoWeissman2018Local, WuYang2016Chebyshev, Kitagawa2018, Athey2021, JinRenYangWang2025Pessimism, Wang2017, Ma2022, Crump2009, Khan2010, Ma2020, Hong2020, Mou2023

home_objs: none
## section: Observational model and causal interpretation

Introduce the finite observed alphabet, atom probabilities, cell masses, propensities, outcome means, and public overlap floor in grouped presentation definitions before their first use. Separate the observed-data estimation problem from its potential-outcome interpretation while placing the causal assumptions and completion class together. Define the scalar target, minimax loss, and logarithmic rate scale. Introduce the four-cell extension before the identification result because that result uses it; explain its role as a representation of the target that also supports the estimator. Keep sampling and causal restrictions explicit and treat null cells through the stated convention.

objs: ass:iid-sampling, synth_1, ass:shrinking-overlap, def:observed-class, def:observed-value, def:minimax-risk, ass:consistency, ass:conditional-exchangeability, def:causal-class, def:armwise-extension, prop:identification

bib: Rubin1974, Rosenbaum1983, Murphy2003, Manski2004

home_objs: ass:iid-sampling, ass:shrinking-overlap, def:observed-class, def:observed-value, def:minimax-risk, ass:consistency, ass:conditional-exchangeability, def:causal-class, def:armwise-extension, prop:identification
## section: Minimax rates and consistency

Place the matched risk characterization first and the triangular-sequence consistency criterion immediately afterward. Explain the roles of the number of covariate cells and the rare-arm sample size, the saturation regime, and the fixed-alphabet and fixed-overlap specializations. Attribute the causal interpretation to \cref{prop:identification}. Give a short roadmap connecting the upper construction to \cref{thm:observable-upper} and the converse to \cref{thm:all-estimator-lower}, with the weighted approximation result identified as the central lower-bound ingredient. Keep technical experiment construction in the appendix.

objs: thm:matched-frontier, thm:consistency-threshold

bib: none

home_objs: thm:matched-frontier, thm:consistency-threshold
## section: An attaining estimator

Present the central estimator as a numbered algorithm in the main body, with its bounded-alphabet, saturated, and active branches visibly separated. Explain the active branch through pilot localization, approximation of the cell contribution, factorial estimation, clipping, and conditional averaging over auxiliary randomization. Resolve all algorithm symbols within its anchored environment and explain how the resulting statistic depends on the observed sample and the public overlap floor. Place the observable upper result after the algorithm and use the armwise sensitivity argument as intuition, referring readers to the appendix for its lemma and detailed risk proof.

objs: def:armwise-estimator, thm:observable-upper

bib: JiaoVenkatHanWeissman2015Functionals, Timan1963, Ditzian1987

home_objs: def:armwise-estimator, thm:observable-upper
## section: Discussion and open questions

Interpret the consistency criterion as a joint requirement on sample size, categorical support, and overlap. Explain how the value benchmark supports precision assessments in categorical treatment-choice problems and how its stated domain accommodates unequal propensities and treatment-effect ties. Include a clearly titled “Limitations and future work” subsection containing the anchored sharp-path question, distinguished from the proved rate comparison. Discuss leading-constant convergence, path dependence, and the proposed approximation–moment and transfer directions as future research. Keep literature positioning in the related-work section.

objs: oeq:sharp-path-constant

bib: none

home_objs: oeq:sharp-path-constant
## section: Appendix: Identification and upper-bound proofs

Prove the causal completion and identification result, then establish the armwise modulus before using it in the estimator risk analysis. Organize the upper proof by estimator branch and by the roles of localization, polynomial bias, factorial variance, clipping, and the Poisson cap. Place the deterministic-split factorial definition before its first appendix use and explain its mathematical role relative to the active estimator’s Poisson factorial statistic. Preserve the two constructions’ separate sampling conventions.

objs: lem:armwise-modulus, def:fixed-sample-factorial

bib: Timan1963, Ditzian1987, JiaoVenkatHanWeissman2015Functionals

home_objs: lem:armwise-modulus, def:fixed-sample-factorial
## section: Appendix: Weighted approximation and constrained moment priors

Introduce the scalar functional through an anchored presentation definition before the weighted-error and constrained-prior definitions. Define the common-atom completion map before its use, with its input-specific output properties established in the proof. Add grouped packet notation before the localization lemma. Develop the Fourier endpoint calculation and twice-antiderivative localization, then use those bounds to construct the common-mean, moment-matched probability pair and prove the weighted approximation comparison. Present the combined weighted-separation result here, and connect its statistical consequences to the main-body results through exact cross-references.

objs: def:weighted-error, def:constrained-prior-separation, def:weighted-handle, lem:jackson-packet-localization, thm:weighted-separation-and-frontier

bib: Timan1963, Ditzian1987, WuYang2016Chebyshev, Wu2016, Wu2020, Cai2011, Donoho1994

home_objs: def:weighted-error, def:constrained-prior-separation, def:weighted-handle, lem:jackson-packet-localization, thm:weighted-separation-and-frontier
## section: Appendix: Statistical lower bound and verification scope

Define the normalized sparse family and the auxiliary likelihood experiment before the sparse-likelihood lemma. Build the lower proof around the full armwise likelihood, constrained moment-prior normalization, target separation under the random normalizer, and product-mixture comparison. Present the dense boundary-propensity and rare-arm two-point arguments where their regimes enter, followed by the explicit bounded-loss transfer from the auxiliary Poisson experiment to exactly \(n\) observations. Complete the proofs of the matched rate and consistency criterion by referencing the established bounds. End with a brief verification note consolidating the supplied Lean machine-checking scope, separating verified statements from model assumptions and cited dependency inputs, and retaining theorem-local trust-boundary disclosures.

objs: def:sparse-family, lem:sparse-likelihood, thm:all-estimator-lower

bib: Tsybakov2009, Donoho1994, Cai2011, HanJiaoWeissman2018Local, WuYang2016Chebyshev
home_objs: def:sparse-family, lem:sparse-likelihood, thm:all-estimator-lower
