# Title
**Outcome-free records and the minimax precision of conditional treatment effect estimation**

**Contribution statement.** For a fixed interior covariate profile in a known-uniform, binary-response Hölder model with fixed overlap and public smoothness parameters, the paper establishes the sharp absolute-error minimax rate across labeled and outcome-free sample sizes, constructs an attaining projection estimator, and characterizes the sample requirements for supplied-propensity precision and strict improvement over labeled data alone.

env_overrides: def:roles=algorithmv, def:moments=algorithmv, def:marked-handle=algorithmv, prop:annotation-threshold=propositionv

notation_gaps: \(X,A,Y(0),Y(1),Y\)=primitive variables and the observed-response rule require an anchored definition, \(x_0\)=the fixed interior evaluation profile requires an anchored definition, \(\mathcal D_{n,m},U,\mathsf E_{n,m}(P)\)=the original-record experiment and independent randomizer require an anchored definition, \(P_{XA}\)=the treatment-record marginal requires an anchored definition, \(T,T^e\)=the measurable decision domains and supplied-propensity input require an anchored definition, \(N\)=the total treatment-record count requires an anchored definition, \(S,\Delta,S_{\mathrm{crit}},q_*,r_o(n),r_{\mathrm{up}}(n,m)\)=the rate parameters and benchmark orders require an anchored definition, \(C_h,\nu_h,w_h,r,r_0,q,p_v,b,k,V_J,I\)=the localization measure, polynomial bases, projection space, and identity operator require an anchored definition, \(Q_{P,h,J}\)=the population expectation of the empirical matrix requires an anchored definition, \(\mathrm{clip}_{[-1,1]}\)=the clipping operator requires an anchored definition, \(M_{+1},M_{-1}\)=the fixed-size mixtures require an anchored definition, \(\mathsf h^2(\mathbb B,\mathbb C),\xi,\nu,\mathbb B_z,\mathbb C_z\)=the general Hellinger and conditional-law notation is introduced in auxiliary lemmas rather than an anchored definition, \(\bar R\)=the expected empirical response vector is introduced in an auxiliary lemma rather than an anchored definition, \(p_*,p,\vartheta\)=the Taylor degree, Taylor polynomial, and coefficient vector are introduced in an auxiliary lemma rather than an anchored definition, \(s_{\mathrm{pub}}\)=the published average nuisance smoothness is introduced in an auxiliary lemma rather than an anchored definition, \(\Psi,\widehat\Psi,\omega,v_0,s_0,u_0\)=the testing functional, decision, prior, sample count, separation, and distance bound require an anchored definition for the auxiliary testing statement

# Notation

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(X\) | \(X\) | Covariate vector on the unit cube | notation gap |
| \(A\) | \(A\) | Binary treatment indicator | notation gap |
| \(Y(0)\) | \(Y(0)\) | Binary potential response under control | notation gap |
| \(Y(1)\) | \(Y(1)\) | Binary potential response under treatment | notation gap |
| \(Y\) | \(Y\) | Observed response selected by treatment | notation gap |
| \(P=\mathcal L(X,A,Y(0),Y(1))\) | \(P=\mathcal L(X,A,Y(0),Y(1))\) | Primitive joint potential-outcome law | `def:primitive-class` |
| \(\mathcal M(d,\alpha,\beta,\gamma,L)\) | \(\mathcal M(d,\alpha,\beta,\gamma,L)\) | Primitive laws admitting the stated uniform design, exchangeability, overlap, smoothness, and arm-interior witnesses | `def:primitive-class` |
| \(\mathcal M\) | \(\mathcal M\) | The primitive class at the fixed public parameters | `def:primitive-class` |
| \(\|f\|_{H^s}\) | \(\|f\|_{H^s}\) | Extended-real maximum of derivative sup norms and top-derivative Hölder seminorms | `def:holder-norm` |
| \(\partial^\kappa f\) | \(\partial^\kappa f\) | Partial derivative indexed by the multi-index \(\kappa\) | `def:holder-norm` |
| \(g_e\) | \(g_e\) | Admissible Borel witness for the conditional treatment probability | `def:primitive-class` |
| \(g_0\) | \(g_0\) | Admissible Borel witness for the conditional control potential-response mean | `def:primitive-class` |
| \(g_1\) | \(g_1\) | Admissible Borel witness for the conditional treated potential-response mean | `def:primitive-class` |
| \(e_P\) | \(e_P\) | Designated admissible propensity witness | `def:primitive-class` |
| \(\mu_{0,P}\) | \(\mu_{0,P}\) | Designated admissible control-mean witness | `def:primitive-class` |
| \(\mu_{1,P}\) | \(\mu_{1,P}\) | Designated admissible treated-mean witness | `def:primitive-class` |
| \(\tau_P\) | \(\tau_P\) | Canonical continuous conditional causal contrast equal everywhere to the difference of admissible arm means | `def:primitive-class` |
| \(x_0\) | \(x_0\) | Fixed interior covariate profile at which the contrast is evaluated | notation gap |
| \(\mathcal D_{n,m}\) | \(\mathcal D_{n,m}\) | Original dataset of labeled records and independent outcome-free treatment records | notation gap |
| \(U\) | \(U\) | Independent uniform randomizer available to decisions | notation gap |
| \(\mathsf E_{n,m}(P)\) | \(\mathsf E_{n,m}(P)\) | Product sampling law of the original dataset and randomizer | notation gap |
| \(P_{XA}\) | \(P_{XA}\) | Joint covariate-treatment marginal of a primitive law | notation gap |
| \(T\) | \(T\) | Borel real-valued decision using the original dataset and randomizer | notation gap |
| \(T^e\) | \(T^e\) | Borel decision additionally receiving the admissible propensity function | notation gap |
| \(\mathcal R_{n,m}(T,P)\) | \(\mathcal R_{n,m}(T,P)\) | Expected absolute error for the point contrast under the original experiment | `def:risk` |
| \(R(n,m)\) | \(R(n,m)\) | Infimum over Borel decisions of worst-case absolute-error risk | `def:minimax` |
| \(R^e(n,m)\) | \(R^e(n,m)\) | Minimax absolute-error risk when the propensity is supplied | `def:oracle-risk` |
| \(N\) | \(N\) | Total treatment-record count, comprising labeled and outcome-free records | notation gap |
| \(S\) | \(S\) | Sum of propensity and control-mean Hölder orders | notation gap |
| \(\Delta\) | \(\Delta\) | Denominator governing the unequal-channel rate exponent | notation gap |
| \(S_{\mathrm{crit}}\) | \(S_{\mathrm{crit}}\) | Nuisance-smoothness threshold separating the two rate regimes | notation gap |
| \(q_*\) | \(q_*\) | Total-record growth exponent for supplied-propensity precision | notation gap |
| \(r_o(n)\) | \(r_o(n)\) | Supplied-propensity point-estimation order | notation gap |
| \(r_{\mathrm{up}}(n,m)\) | \(r_{\mathrm{up}}(n,m)\) | Maximum of the supplied-propensity and unequal-channel rate orders | notation gap |
| \(r_*(n,m;d,\alpha,\beta,\gamma)\) | \(r_*(n,m;d,\alpha,\beta,\gamma)\) | Directly evaluable sharp rate; comparison constants may also depend on \(L\) and \(\varepsilon\) | `def:sharp-rate` |
| \(r_*\) | \(r_*\) | Sharp rate with its arguments suppressed | `def:sharp-rate` |
| \(\mathcal B_*(\zeta)\) | \(\mathcal B_*(\zeta)\) | Sample-size pairs achieving the supplied-propensity order within tolerance \(\zeta\) | `def:annotation-region` |
| \(C_h\) | \(C_h\) | Localization cube centered at the evaluation profile | notation gap |
| \(\nu_h\) | \(\nu_h\) | Uniform probability measure on the localization cube | notation gap |
| \(w_h\) | \(w_h\) | Localization density relative to Lebesgue measure | notation gap |
| \(r\) | \(r\) | Scaled orthonormal coarse polynomial basis vector | notation gap |
| \(r_0\) | \(r_0\) | Coarse basis vector evaluated at the target profile | notation gap |
| \(q\) | \(q\) | Dimension of the coarse polynomial basis | notation gap |
| \(r_u\) | \(r_u\) | Coordinate of the coarse polynomial basis vector | notation gap |
| \(p_v\) | \(p_v\) | Polynomial represented by the coarse coefficient vector \(v\) | notation gap |
| \(V_J\) | \(V_J\) | Space of cellwise degree-two polynomials on the localization partition | notation gap |
| \(\mathbf b_J\) | \(\mathbf b_J\) | Cellwise orthonormal fine polynomial basis vector in the projection formulas | `def:projection` |
| \(k\) | \(k\) | Rank of the fine projection space | notation gap |
| \(I\) | \(I\) | Identity operator on the localized square-integrable function space | notation gap |
| \(\delta\) | \(\delta\) | Fine-cell side length given by localization scale divided by grid resolution | `def:projection` |
| \(K_J(x,x')\) | \(K_J(x,x')\) | Finite-rank projection kernel formed from the fine basis | `def:projection` |
| \(\Pi_Jf(x)\) | \(\Pi_Jf(x)\) | Orthogonal projection of a function onto the fine polynomial space | `def:projection` |
| \(\mathcal D^T\) | \(\mathcal D^T\) | Concatenated treatment-record sequence with labeled outcomes discarded | `def:roles` |
| \((X_i^T,A_i^T)\) | \((X_i^T,A_i^T)\) | Indexed covariate-treatment pair in the concatenated sequence | `def:roles` |
| \((X_i,A_i)\) | \((X_i,A_i)\) | Covariate-treatment pair from a labeled record | `def:roles` |
| \((\widetilde X_{i-n},\widetilde A_{i-n})\) | \((\widetilde X_{i-n},\widetilde A_{i-n})\) | Auxiliary covariate-treatment pair occupying concatenated position \(i\) | `def:roles` |
| \(\ell\) | \(\ell\) | Number of labeled records assigned to the outcome role | `def:roles` |
| \(t\) | \(t\) | Number of records assigned to the treatment role | `def:roles` |
| \(I_L\) | \(I_L\) | Index set of outcome-role labeled records | `def:roles` |
| \(I_T\) | \(I_T\) | Index set of treatment-role records | `def:roles` |
| \(\widehat\eta_J^L(x)\) | \(\widehat\eta_J^L(x)\) | Outcome-role empirical projection of the observed response | `def:moments` |
| \(\widehat R_{h,J}\) | \(\widehat R_{h,J}\) | Empirical response vector with rectangular projection correction | `def:moments` |
| \(\widehat Q^{\mathrm{raw}}_{h,J}\) | \(\widehat Q^{\mathrm{raw}}_{h,J}\) | Unsymmetrized empirical matrix with rectangular projection correction | `def:moments` |
| \(\widehat Q_{h,J}\) | \(\widehat Q_{h,J}\) | Symmetrized corrected empirical matrix | `def:moments` |
| \(Q_{P,h,J}\) | \(Q_{P,h,J}\) | Population expectation of the symmetrized empirical matrix | notation gap |
| \(\bar R\) | \(\bar R\) | Population expectation of the empirical response vector | notation gap |
| \(\mathrm{clip}_{[-1,1]}\) | \(\mathrm{clip}_{[-1,1]}\) | Projection of a real value onto the stated bounded interval | notation gap |
| \(\lambda_{\min}(\widehat Q_{h,J})\) | \(\lambda_{\min}(\widehat Q_{h,J})\) | Smallest eigenvalue used in the empirical inversion guard | `def:estimator` |
| \(\widehat T_{h,J}\) | \(\widehat T_{h,J}\) | Clipped local polynomial decision with an empirical eigenvalue guard | `def:estimator` |
| \(h_*\) | \(h_*\) | Public localization scale balancing the two rate orders | `def:tuning` |
| \(J_*\) | \(J_*\) | Public grid resolution determined by effect and nuisance smoothness | `def:tuning` |
| \(\widehat T_{\mathrm{up}}\) | \(\widehat T_{\mathrm{up}}\) | Projection decision at the public localization and resolution choices | `def:tuning` |
| \(T_*(\mathcal D_{n,m},U)\) | \(T_*(\mathcal D_{n,m},U)\) | Total original-record decision given by the publicly tuned estimator | `def:sharp-decision` |
| \(T_*\) | \(T_*\) | Sharp-rate attaining decision | `def:sharp-decision` |
| \(p_*\) | \(p_*\) | Taylor degree determined by the effect Hölder order | notation gap |
| \(p\) | \(p\) | Taylor polynomial of the causal contrast at the target profile | notation gap |
| \(\vartheta\) | \(\vartheta\) | Coarse basis coefficient vector of the Taylor polynomial | notation gap |
| \(s_{\mathrm{pub}}\) | \(s_{\mathrm{pub}}\) | Average nuisance smoothness used in the published numerical comparison | notation gap |
| \(H^2(M_{+1},M_{-1})\) | \(H^2(M_{+1},M_{-1})\) | Squared Hellinger distance between the two fixed-size mixtures | `def:hellinger` |
| \(M_{+1}\) | \(M_{+1}\) | Positive-hypothesis mixture law for the fixed-size original-record experiment | notation gap |
| \(M_{-1}\) | \(M_{-1}\) | Negative-hypothesis mixture law for the fixed-size original-record experiment | notation gap |
| \(\mathsf h^2(\mathbb B,\mathbb C)\) | \(\mathsf h^2(\mathbb B,\mathbb C)\) | Squared Hellinger distance with the auxiliary testing normalization | notation gap |
| \(\mathbb B\) | \(\mathbb B\) | First probability law in a generic Hellinger comparison | notation gap |
| \(\mathbb C\) | \(\mathbb C\) | Second probability law in a generic Hellinger comparison | notation gap |
| \(\xi\) | \(\xi\) | Sum of the compared laws used as a dominating measure | notation gap |
| \(\nu\) | \(\nu\) | Common conditioning-coordinate marginal | notation gap |
| \(\mathbb B_z\) | \(\mathbb B_z\) | Indexed probability law in the first conditional or testing family | notation gap |
| \(\mathbb C_z\) | \(\mathbb C_z\) | Indexed probability law in the second conditional or testing family | notation gap |
| \(\Psi\) | \(\Psi\) | Real-valued functional separated across the testing families | notation gap |
| \(\widehat\Psi\) | \(\widehat\Psi\) | Measurable decision estimating the testing functional | notation gap |
| \(\omega\) | \(\omega\) | Common mixing prior in the auxiliary testing statement | notation gap |
| \(v_0\) | \(v_0\) | Product sample count in the auxiliary testing statement | notation gap |
| \(s_0\) | \(s_0\) | Lower bound on functional separation between testing families | notation gap |
| \(u_0\) | \(u_0\) | Upper bound on squared Hellinger distance between testing mixtures | notation gap |
| \(\mathfrak C\) | \(\mathfrak C\) | Prescribed finite-prior construction from localization, resolution, and amplitudes | `def:marked-handle` |
| \(a\) | \(a\) | Propensity perturbation amplitude in the lower-bound construction | `def:marked-handle` |
| \(b\) | \(b\) | Response-mean perturbation amplitude in the lower-bound construction | `def:marked-handle` |
| \(\chi(u)\) | \(\chi(u)\) | Smooth one-sided exponential transition building block | `def:marked-handle` |
| \(\vartheta(u)\) | \(\vartheta(u)\) | Smooth angular transition formed from the building block | `def:marked-handle` |
| \(\omega_z(u)\) | \(\omega_z(u)\) | Indexed compactly supported sine-cosine frame function | `def:marked-handle` |
| \(B(w)\) | \(B(w)\) | Product smooth bump on the normalized localization coordinates | `def:marked-handle` |
| \(B_h(x)\) | \(B_h(x)\) | Smooth bump centered and scaled at the target profile | `def:marked-handle` |
| \(\psi_{\mathbf z}(x)\) | \(\psi_{\mathbf z}(x)\) | Tensor-product fine-scale frame function | `def:marked-handle` |
| \(\mathcal I\) | \(\mathcal I\) | Finite lattice index set for the smooth frame | `def:marked-handle` |
| \(\phi_{\mathbf z}(x)\) | \(\phi_{\mathbf z}(x)\) | Fine-scale frame entry multiplied by the localization bump | `def:marked-handle` |
| \(\lambda,\eta\in\{-1,+1\}^{\mathcal I}\) | \(\lambda,\eta\in\{-1,+1\}^{\mathcal I}\) | Propensity and response sign arrays indexed by the finite frame | `def:marked-handle` |
| \(F_\lambda(x)\) | \(F_\lambda(x)\) | Signed propensity frame sum | `def:marked-handle` |
| \(G_\eta(x)\) | \(G_\eta(x)\) | Signed response frame sum | `def:marked-handle` |
| \(\theta\in\{-1,+1\}\) | \(\theta\in\{-1,+1\}\) | Index distinguishing the two lower-bound hypotheses | `def:marked-handle` |
| \(\rho_\theta\) | \(\rho_\theta\) | Hypothesis-dependent correlation of the sign pairs | `def:marked-handle` |
| \(w_\theta(\lambda,\eta)\) | \(w_\theta(\lambda,\eta)\) | Product probability weight of a pair of sign arrays | `def:marked-handle` |
| \(e_\lambda(x)\) | \(e_\lambda(x)\) | Constructed propensity success-probability function | `def:marked-handle` |
| \(\tau_\theta(x)\) | \(\tau_\theta(x)\) | Deterministic contrast shared by laws within a hypothesis | `def:marked-handle` |
| \(\mu_{0,\theta,\eta}(x)\) | \(\mu_{0,\theta,\eta}(x)\) | Constructed control potential-response success-probability function | `def:marked-handle` |
| \(\mu_{1,\theta,\eta}(x)\) | \(\mu_{1,\theta,\eta}(x)\) | Constructed treated potential-response success-probability function | `def:marked-handle` |
| \(P_{\theta,\lambda,\eta}\) | \(P_{\theta,\lambda,\eta}\) | Primitive law with uniform covariates and conditionally independent Bernoulli margins | `def:marked-handle` |
| \(\varpi_\theta\) | \(\varpi_\theta\) | Finite pushforward prior on the constructed primitive laws | `def:marked-handle` |
| \(\operatorname{Dirac}(P)\) | \(\operatorname{Dirac}(P)\) | Unit point mass at a primitive law | `def:marked-handle` |
| \(k_{\mathrm{aux}}\) | \(k_{\mathrm{aux}}\) | Arbitrary nonnegative auxiliary-record count in the mixture equality | `def:marked-handle` |

# Sections

## section: Abstract

Plan a compact account of the pointwise estimation question, the two sampling channels, the sharp minimax order, and the acquisition consequences under the stated primitive model. Use words for quantities whose formal definitions occur later, or attach a first-use gloss. Write the abstract last, after the exposition and proof boundaries are settled.

objs: none

bib: none

home_objs: none
## section: Introduction

Organize the introduction around the value of additional covariate-treatment records when response labels are scarce. Preview the sharp risk characterization, the attaining estimator, and the distinction between improving the supervised order and reaching supplied-propensity precision. State the known-uniform binary-response setting and public regularity conditions positively. Include one factual sentence directing readers to the appendix verification note. Write this section last.

objs: none

bib: none

home_objs: none
## section: Related work

Make the closest comparison with \citet[Section 3, Theorems 1--2 and equation (14)]{KennedyBalakrishnanRobinsWasserman2024}: supervised pointwise minimax exponents, the published attainment conditions, and the localized second-order projection architecture. Locate the algebraic supervised comparison in \cref{lem:published-cate-benchmark}, and distinguish its source-model interpretation from the original known-uniform lower-bound argument through affirmative descriptions of each result's domain. Compare the unequal-channel pointwise risk characterization with the ATE and QTE expansions of \citet[Theorem 2.1 and Corollary 2.1]{ChakraborttyDai2022}, the surrogate-assisted ATE setting of \citet[Sections 2.1, 2.5--2.6, and 4]{ChengAnanthakrishnanCai2021}, and the regular-estimator ATE efficiency results of \citet[Theorems 4.2 and 4.4 and Corollary 4.5]{Kato2026}. Briefly position supplied-predictor conditional estimation and structure-adaptive CATE results by their information inputs, function classes, and loss criteria. Use higher-order influence-function and orthogonal-regression work to explain methodological lineage, with model-specific comparisons and precise citation locators.

objs: none

bib: KennedyBalakrishnanRobinsWasserman2024, Kennedy2023, Nie2021, Foster2023, Gao2020, Robins2008, Robins2009, Robins2017, Zhang2026, ChakraborttyDai2022, ChengAnanthakrishnanCai2021, Kato2026, Kallus2025, Angelopoulos2023, SuiZhouZhouDai2026, Kim2026StructureAdaptiveCATE, KimWassermanBalakrishnanNeykov2025

home_objs: none
## section: Setup and assumptions

Introduce the primitive variables, observed-response rule, fixed evaluation profile, and two-channel sampling experiment through the required anchored definition families. Explain identification and uniqueness of the continuous point target under exchangeability, overlap, and full-support uniform design. Present the Hölder convention, existential admissible-witness class, nine restrictions, absolute-loss risk, and supplied-propensity experiment. Keep the public parameter domain and the numerical overlap and response-mean restrictions explicit. Introduce the rate parameters as a single coherent notation family before their use in subsequent sections.

objs: def:holder-norm, synth_5, ass:uniform-design, ass:exchangeability, ass:overlap, ass:propensity-holder, ass:control-holder, ass:effect-holder, ass:control-interior, ass:treated-interior, def:primitive-class, ass:sample-law, def:risk, def:minimax, def:oracle-risk

bib: Rubin1974, Rosenbaum1983, Imbens2015, Hernan2020

home_objs: def:holder-norm, def:primitive-class, ass:uniform-design, ass:exchangeability, ass:overlap, ass:propensity-holder, ass:control-holder, ass:effect-holder, ass:control-interior, ass:treated-interior, ass:sample-law, def:risk, def:minimax, def:oracle-risk
## section: Estimation with outcome-free records

Present the central estimator as a statistical construction: localization and coarse polynomial reproduction, fine projection, independent outcome and treatment roles, corrected empirical moments, guarded inversion, and public tuning. Resolve the local measure, bases, projection space, population matrix, and clipping operator before their first use. Give intuition for the allocation of information between the two roles and the four terms in \cref{thm:rectangular-upper}, emphasizing the separate localization and projection scales. Place the complete estimator in the main body and direct detailed approximation, variance, and inversion arguments to the appendix.

objs: synth_3, synth_1, synth_7, def:projection, def:roles, def:moments, def:estimator, def:tuning, def:sharp-decision, thm:rectangular-upper

bib: Fan1996, Robinson1988, Hoeffding1948, Robins2008, Robins2017

home_objs: synth_3, synth_1, def:projection, def:roles, def:moments, def:estimator, def:tuning, def:sharp-decision, thm:rectangular-upper
## section: Sharp precision and sample requirements

Lead with the explicit rate and uniform minimax sandwich, followed by the supplied-propensity benchmark and acquisition consequences. Organize the interpretation around the nuisance-smoothness threshold, the intermediate product-of-counts regime, and saturation at the supplied-propensity order, including equality cases. Explain how the original-record lower bound covers randomized decisions and how the sparse-range nuisance converse combines with the supplied-propensity floor across all sample imbalances. Present the oracle-attainment region, the exact strict-improvement criterion, and the two sample-growth requirements for a target absolute-error order. Use the one-dimensional benchmark to make the count threshold concrete.

objs: def:sharp-rate, thm:sharp-annotation-frontier, thm:supplied-propensity, def:annotation-region

bib: none

home_objs: def:sharp-rate, thm:sharp-annotation-frontier, thm:supplied-propensity, def:annotation-region
## section: Discussion and limitations

Interpret the acquisition region as a benchmark for allocating true response labels and routine covariate-treatment records under the specified model. Explain the distinct roles of outcome noise and propensity information, and the implications of public nuisance regularity for acquisition. Include a clearly titled “Limitations and future work” subsection covering general covariate distributions, unknown smoothness, uncertainty quantification, alternative losses and causal targets, and richer auxiliary information. Keep literature positioning in the related-work section; use the chart-review setting only to explain the acquisition interpretation.

objs: none

bib: ChengAnanthakrishnanCai2021, Ananthakrishnan2016

home_objs: none
## section: Appendix: Upper-bound proofs

Develop the local Taylor and projection facts, population positivity identity, rectangular sampling bound, guarded-inversion argument, and tuning calculation in their logical dependency order. Introduce the expected response vector and Taylor coefficient notation before their first use. Supply the proof of \cref{thm:rectangular-upper} and the upper-bound component of \cref{thm:supplied-propensity}. Treat the two-scale construction and public role split as statistical inputs to the proof.

objs: lem:local-polynomial-projection-facts, lem:population-positivity, lem:rectangular-sampling-bound

bib: Fan1996, Hoeffding1948, Stone1982

home_objs: lem:local-polynomial-projection-facts, lem:population-positivity, lem:rectangular-sampling-bound
## section: Appendix: Original-record lower bounds

Introduce the fixed-size mixture laws and Hellinger notation, then the prescribed smooth-frame prior construction before its certificate. Place the response-amplitude and arm-mean definition immediately after the marked-handle construction that defines its frame and bump, and explain there that the shared perturbation cancels from the contrast while the scalar amplitude \(b\) is distinct from the estimator basis vector \(\mathbf b_J(x)\). Establish the information argument through common propensity distributions, singleton cancellation, conditional component factorization, and the sparse-occupancy bound under the certificate's stated gate. Place the nuisance converse after these ingredients and combine it with the supplied-propensity lower bound to prove the complete minimax characterization. Present the derivation program as appendix proof organization, resolving the complementary sample-size ranges through the oracle floor.

objs: synth_4, synth_6, def:hellinger, synth_2, def:marked-handle, lem:hellinger-block-calculus, lem:published-fuzzy-testing, thm:marked-component-certificate, lem:nuisance-frontier-converse

bib: KennedyBalakrishnanRobinsWasserman2024, Robins2009, Tsybakov2009

home_objs: def:hellinger, def:marked-handle, synth_2, lem:hellinger-block-calculus, lem:published-fuzzy-testing, thm:marked-component-certificate, lem:nuisance-frontier-converse
## section: Appendix: Acquisition consequences and supervised comparison

Give the rate algebra proving the oracle-attainment equivalence, strict-benefit criterion, and target-error acquisition conditions. Place the published numerical comparison here as an exponent-and-cutoff identity, with the source theorem's bounded-density model and constants identified precisely. Keep the lower-bound proof for the present primitive class tied to the original-record construction and supplied-propensity subfamily.

objs: prop:annotation-threshold, lem:published-cate-benchmark

bib: KennedyBalakrishnanRobinsWasserman2024

home_objs: prop:annotation-threshold, lem:published-cate-benchmark
## section: Appendix: Verification note

End the appendix with a brief consolidated account of Lean machine-checking scope: the established estimator guarantee, supplied-propensity benchmark, smooth-frame certificate, nuisance converse, minimax sandwich, acquisition consequences, auxiliary lemmas, and numerical supervised comparison. Place the representation-level frontier handle here with the other formal-artifact conventions. Identify the primitive-model and sampling restrictions as assumed inputs. Record the published testing dependency and the numerical-comparison boundary using the generated theorem-local scope disclosures; distinguish source-literature claims from the results realized in the formal layer. Keep declaration names and proof-engineering details confined to this note.

objs: def:frontier-handle

bib: KennedyBalakrishnanRobinsWasserman2024
home_objs: def:frontier-handle
