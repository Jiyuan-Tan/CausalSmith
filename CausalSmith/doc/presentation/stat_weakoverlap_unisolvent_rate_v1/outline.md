# Title
**Minimax response recovery under global overlap tails**

**Contribution statement.** For a treated response with known Hölder smoothness above one, the paper constructs a treatment-count-selected equal-cell estimator attaining logarithm-free expected supremum risk uniformly over compact ranges of the unknown overlap exponent, establishes the matching pointwise minimax order through bounded Bernoulli experiments, and transfers the upper guarantee to Dorn’s Gaussian model under its remaining source restrictions.

env_overrides: def:mesh-selector=algorithmv, def:estimator=algorithmv, prop:strict-enlargement=propositionv, prop:dorn-a3-free-corollary=propositionv, lem:dorn-rate-scope=propositionv, def:joint-adaptation-handle=remarkv, oeq:joint-adaptation=remarkv

notation_gaps: \(m\)=polynomial degree appears without its relation to smoothness, \(\mathcal D_n\)=observed sample and measurable sample space require a definition, \(P^{\otimes n}\)=sampling-product convention requires an anchored home, \(\mu_{1,P}\)=law-indexed response notation requires identification with the target, \(\mu_P\)=source regression target requires definition, \(U\)=template vector coordinates are unspecified, \(v_\ell\)=tensor-node coordinates and index range are unspecified, \(J\)=number of tensor nodes is unspecified, \(L_U\)=the template perturbation constant requires its defining property, \(\mathcal H_n\)=candidate dyadic meshes are unspecified, \(\mathcal Q_h\)=partition convention and boundary assignment require definition, \(a_Q\)=cube-corner convention requires definition, \(E_{Q\ell}\)=scaled microcell formula is absent, \(N_{Q\ell}\)=treated microcell count formula is absent, \(\mathcal F_n\)=feasible-mesh set is used without an explicit definition, \(\widehat G_Q\)=equal-cell empirical Gram formula is absent, \(\widehat c_Q\)=equal-cell coefficient formula is absent, \(q_{Q\ell}\)=population treated microcell mass is undefined, \(q_Q\)=weakest-microcell mass within a cube is undefined, \(q_{(k)}\)=ordering convention for weakest-cell masses is undefined, \(D_\gamma\)=effective dimension is undefined, \(h_{\gamma,n}\)=oracle mesh is undefined, \(r_{\gamma,n}\)=oracle risk scale is undefined, \(\operatorname{clip}_{[-B,B]}\)=clipping operator requires an anchored definition, \(\log_+\)=positive-part logarithm convention requires definition, \(\Sigma^{\mathrm D}(\beta,L_0)\)=exact source smoothness class is undefined, \(\|u\circ T\|_{\mathcal H^\beta}\)=Hölder-radius functional is used without definition, \(\|\cdot\|_{L^\infty(P)}\)=source essential-supremum loss requires its measure convention, \(\|\cdot\|_\infty\)=spatial-supremum and coefficient-vector conventions require an anchored home, \(\operatorname{KL}\)=relative-entropy convention requires an anchored home, \(C^m([-1,1]^d)\)=source-cube derivative convention requires an anchored home, \(\mathcal E_n\)=selected-mesh event is existentially specified but has no definition home, \(Z_k\)=generic centered-variable family has no definition home, \(r^*_{\mu,n}\)=source comparison scale is defined inside a lemma rather than an anchored definition, \(\mathcal D_\gamma\)=fixed-constant source envelope is defined inside a proposition rather than an anchored definition, \(B_*\)=transferred response bound is defined inside a proposition rather than an anchored definition, \(L_*\)=transferred Hölder radius is defined inside a proposition rather than an anchored definition, \(T(x)=2x-\mathbf1\)=affine transport has no anchored definition home, \(\Sigma^{\mathrm D}(\beta,L_0)\) and \(\mathcal D_\gamma\)=their exact source restrictions must be resolved through the cited source-dependency material, whose referenced transcription leaf is absent from the frozen inventory

# Notation

Rows retain the frozen notation. “Gap” refers to the corresponding item above; it supplies a definition requirement rather than an invented construction. Ordinary probability, differentiation, matrix operations, distributions, generic constants, and ambient parameters retain their standard mathematical meanings. Local dummy symbols are scoped to their displayed construction.

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(g\) | \(g\) | Generic function subject to the intrinsic cube smoothness restrictions | def:holder |
| \(D^\alpha g\) | \(D^\alpha g\) | Coordinate derivative with continuous boundary traces | def:holder |
| \(m\) | \(m\) | Polynomial and derivative order requiring its smoothness convention | Gap |
| \(C^m(\mathcal X)\) | \(C^m(\mathcal X)\) | Functions whose interior derivatives through order \(m\) have continuous cube traces | def:holder |
| \(\mathcal H^\beta(L)\) | \(\mathcal H^\beta(L)\) | Intrinsic cube Hölder ball with derivative and modulus bounds of radius \(L\) | def:holder |
| \(\mathcal P_\gamma\) | \(\mathcal P_\gamma\) | Observational causal laws satisfying the displayed fixed-constant response and overlap restrictions | def:model |
| \(P\) | \(P\) | Law indexing the response-recovery model | def:model |
| \(X\) | \(X\) | Covariate vector on the cube | def:model |
| \(A\) | \(A\) | Binary treatment indicator | def:model |
| \(Y(0)\) | \(Y(0)\) | Control potential outcome | def:model |
| \(Y(1)\) | \(Y(1)\) | Treated potential outcome | def:model |
| \(Y\) | \(Y\) | Observed outcome under consistency | def:model |
| \(f\) | \(f\) | Covariate density subject to the displayed lower bound | def:model |
| \(e(X)\) | \(e(X)\) | Propensity evaluated at the observed covariate | def:model |
| \(\mu_1\) | \(\mu_1\) | Treated causal response represented by a Hölder function | def:model |
| \(\mu_{1,P}\) | \(\mu_{1,P}\) | Treated response indexed explicitly by its law | Gap |
| \(\mathcal D_n\) | \(\mathcal D_n\) | Observed sample governing measurable estimators | Gap |
| \(P^{\otimes n}\) | \(P^{\otimes n}\) | Product sampling law for \(n\) independent observations | Gap |
| \(U\) | \(U\) | Vector used to form the polynomial template | Gap |
| \(U(v_\ell)\) | \(U(v_\ell)\) | Template vector evaluated at a tensor node | Gap |
| \(v_\ell\) | \(v_\ell\) | Tensor nodes for the template | Gap |
| \(J\) | \(J\) | Number of template nodes | Gap |
| \(G_0\) | \(G_0\) | Equally weighted template Gram matrix | def:template |
| \(\lambda_0\) | \(\lambda_0\) | Least eigenvalue of the template Gram matrix | def:template |
| \(L_U\) | \(L_U\) | Constant entering the microcube-width rule | Gap |
| \(\eta\) | \(\eta\) | Microcube width chosen by the displayed template rule | def:template |
| \(V_\ell\) | \(V_\ell\) | Disjoint reference microcubes centered at the tensor nodes | def:template |
| \(h\) | \(h\) | Candidate mesh, with local use as the lower-experiment bump scale | def:mesh-selector; def:bounded-lower-pair |
| \(\mathcal H_n\) | \(\mathcal H_n\) | Candidate dyadic mesh collection | Gap |
| \(\mathcal Q_h\) | \(\mathcal Q_h\) | Cube partition at mesh \(h\) | Gap |
| \(Q\) | \(Q\) | Cube in the mesh partition | Gap |
| \(a_Q\) | \(a_Q\) | Corner used to normalize coordinates in a partition cube | Gap |
| \(E_{Q\ell}\) | \(E_{Q\ell}\) | Microcells within a partition cube | Gap |
| \(N_{Q\ell}\) | \(N_{Q\ell}\) | Treated observation count in a microcell | Gap |
| \(\mathcal F_n\) | \(\mathcal F_n\) | Set of meshes satisfying the count-feasibility rule | Gap |
| \(\widehat h\) | \(\widehat h\) | Numerically smallest feasible mesh with the displayed exceptional-sample convention | def:mesh-selector |
| \(\widehat G_Q\) | \(\widehat G_Q\) | Empirical equal-cell Gram matrix | Gap |
| \(\widehat c_Q\) | \(\widehat c_Q\) | Estimated equal-cell polynomial coefficients | Gap |
| \(\operatorname{clip}_{[-B,B]}\) | \(\operatorname{clip}_{[-B,B]}\) | Projection of a fitted value onto the response-bound interval | Gap |
| \(\widehat\mu_n(x)\) | \(\widehat\mu_n(x)\) | Clipped polynomial response estimate evaluated at \(x\) | def:estimator |
| \(R_{\mathrm{pt}}(n,\gamma,x_0)\) | \(R_{\mathrm{pt}}(n,\gamma,x_0)\) | Minimax expected absolute error at the evaluation point | def:risks |
| \(R_\infty(n,\gamma)\) | \(R_\infty(n,\gamma)\) | Minimax expected spatial-supremum error | def:risks |
| \(T\) | \(T\) | Generic sample-measurable estimator in the minimax infimum | def:risks |
| \(\mathfrak P\) | \(\mathfrak P\) | Nonempty source family equipped with selected propensity versions | def:dorn-a3 |
| \(\mathcal S\) | \(\mathcal S\) | Common covariate cube of the source family | def:dorn-a3 |
| \(e_P\) | \(e_P\) | Selected pointwise measurable propensity version for a family member | def:dorn-a3 |
| \((e_P)_{P\in\mathfrak P}\) | \((e_P)_{P\in\mathfrak P}\) | Family of selected propensity versions | def:dorn-a3 |
| \(e_P(X)\) | \(e_P(X)\) | Selected propensity evaluated at the random covariate | def:dorn-a3 |
| \(\mathsf A_{3}^{\mathrm{Dorn}}(\mathfrak P,(e_P)_{P\in\mathfrak P})\) | \(\mathsf A_{3}^{\mathrm{Dorn}}(\mathfrak P,(e_P)_{P\in\mathfrak P})\) | Family-level local anti-concentration condition with common constants | def:dorn-a3 |
| \(\mathsf A_{3}^{\mathrm{Dorn}}(P)\) | \(\mathsf A_{3}^{\mathrm{Dorn}}(P)\) | Singleton-family abbreviation using the displayed propensity version | def:dorn-a3 |
| \(P_P\) | \(P_P\) | Probability under the indexed source-family law | def:dorn-a3 |
| \(x^\circ\) | \(x^\circ\) | Center of the covariate cube in the strip construction | def:thin-strip |
| \(R(x)\) | \(R(x)\) | Supremum-norm distance from the construction’s specified center | def:thin-strip; def:bounded-lower-pair |
| \(F_R\) | \(F_R\) | Continuous distribution function of the radial distance under uniform covariates | def:thin-strip; def:bounded-lower-pair |
| \(S\) | \(S\) | Thin strip specified by the coordinate-power inequality | def:thin-strip |
| \(e_\star(x)\) | \(e_\star(x)\) | Displayed radial-plus-strip propensity | def:thin-strip |
| \(e_\star\) | \(e_\star\) | Selected propensity function for the strip law | def:thin-strip |
| \(p_0\) | \(p_0\) | Bernoulli success probability for the strip-law outcomes | def:thin-strip |
| \(P_{\mathrm{strip}}\) | \(P_{\mathrm{strip}}\) | Uniform-covariate causal law with the displayed strip propensity and bounded outcomes | def:thin-strip |
| \(e_0(x)\) | \(e_0(x)\) | Radial propensity for the bounded testing construction | def:bounded-lower-pair |
| \(e_0(X)\) | \(e_0(X)\) | Radial testing propensity evaluated at the random covariate | def:bounded-lower-pair |
| \(\psi(z)\) | \(\psi(z)\) | Smooth compactly supported product bump | def:bounded-lower-pair |
| \(\theta_0\) | \(\theta_0\) | Baseline Bernoulli success probability in the testing pair | def:bounded-lower-pair |
| \(p_{0,h}(x)\) | \(p_{0,h}(x)\) | Baseline treated Bernoulli success function | def:bounded-lower-pair |
| \(p_{1,h}(x)\) | \(p_{1,h}(x)\) | Bump-perturbed treated Bernoulli success function | def:bounded-lower-pair |
| \(p_{j,h}(X)\) | \(p_{j,h}(X)\) | Treated Bernoulli success probability under testing index \(j\) | def:bounded-lower-pair |
| \(P_{0,h}\) | \(P_{0,h}\) | Baseline bounded testing law on the admissible parameter domain | def:bounded-lower-pair |
| \(P_{1,h}\) | \(P_{1,h}\) | Perturbed bounded testing law on the admissible parameter domain | def:bounded-lower-pair |
| \(\mathcal P_{\mathrm{pair}}\) | \(\mathcal P_{\mathrm{pair}}\) | Sample-size-indexed collection of admissible bounded testing pairs | def:bounded-lower-pair |
| \(q_{Q\ell}\) | \(q_{Q\ell}\) | Population treated probability of a microcell | Gap |
| \(q_Q\) | \(q_Q\) | Weakest population treated microcell mass in a cube | Gap |
| \(q_{(k)}\) | \(q_{(k)}\) | Ordered weakest-cell masses | Gap |
| \(D_\gamma\) | \(D_\gamma\) | Effective dimension governing the overlap-dependent rate | Gap |
| \(h_{\gamma,n}\) | \(h_{\gamma,n}\) | Oracle mesh for the smoothness and overlap parameters | Gap |
| \(r_{\gamma,n}\) | \(r_{\gamma,n}\) | Oracle response-recovery risk scale | Gap |
| \(\mathcal E_n\) | \(\mathcal E_n\) | High-probability event supporting the selected-mesh bounds | Gap |
| \(Z_k\) | \(Z_k\) | Generic ordered centered variables in the maximal inequality | Gap |
| \(\log_+\) | \(\log_+\) | Positive-part logarithm in the maximal inequality | Gap |
| \(\widehat c_Q-\mathbb E(\widehat c_Q\mid(X_i,A_i)_{i=1}^n)\) | \(\widehat c_Q-\mathbb E(\widehat c_Q\mid(X_i,A_i)_{i=1}^n)\) | Coefficient error centered conditionally on the sampled treatment design | Gap for \(\widehat c_Q\) and the sample |
| \((X_i,A_i)_{i=1}^n\) | \((X_i,A_i)_{i=1}^n\) | Sampled covariates and treatment indicators used for conditioning | Gap |
| \(\|\cdot\|_\infty\) | \(\|\cdot\|_\infty\) | Supremum norm with function and coefficient-vector domains specified locally | Gap |
| \(\operatorname{KL}(P_{0,h}^{\otimes n},P_{1,h}^{\otimes n})\) | \(\operatorname{KL}(P_{0,h}^{\otimes n},P_{1,h}^{\otimes n})\) | Relative entropy between the two observed-sample testing laws | Gap for the operator; def:bounded-lower-pair for the laws |
| \(\mu_P\) | \(\mu_P\) | Source regression curve indexed by the observed-data law | Gap |
| \(\widehat\mu\) | \(\widehat\mu\) | Generic source regression estimator or estimator witness | Gap |
| \(r^*_{\mu,n}\) | \(r^*_{\mu,n}\) | Regression comparison scale in the fixed source setup | Gap |
| \(c(\varepsilon)\) | \(c(\varepsilon)\) | Setup-dependent threshold constant for the source probability criterion | Gap |
| \(\|\widehat\mu-\mu_P\|_{L^\infty(P)}\) | \(\|\widehat\mu-\mu_P\|_{L^\infty(P)}\) | Source essential-supremum regression loss | Gap |
| \(\mathcal D_\gamma\) | \(\mathcal D_\gamma\) | Maximal fixed-constant envelope of laws satisfying the retained source restrictions | Gap |
| \(T(x)=2x-\mathbf1\) | \(T(x)=2x-\mathbf1\) | Affine transport from the unit cube to the source cube | Gap |
| \(B_*\) | \(B_*\) | Common response bound chosen for the transported source envelope | Gap |
| \(L_*\) | \(L_*\) | Common transported Hölder radius defined by the source-class supremum | Gap |
| \(\Sigma^{\mathrm D}(\beta,L_0)\) | \(\Sigma^{\mathrm D}(\beta,L_0)\) | Source Hölder-seminorm class with the exact cited convention | Gap |
| \(\|u\circ T\|_{\mathcal H^\beta}\) | \(\|u\circ T\|_{\mathcal H^\beta}\) | Hölder-radius functional used to choose the transferred radius | Gap |
| \(C^m([-1,1]^d)\) | \(C^m([-1,1]^d)\) | Source-cube differentiability class used in smoothness completion | Gap |
| \(u\circ T\) | \(u\circ T\) | Source function composed with the affine cube transport | Gap for \(T\) and the source convention |
| \(\mu^\circ\) | \(\mu^\circ\) | Common known regression curve in the family-richness obstruction | Gap |
| \(r_n\) | \(r_n\) | Arbitrary positive comparison sequence in the family-richness obstruction | Gap |

# Sections

## section: Abstract

Plan a compact statement of the response-recovery question, the quantitative global overlap condition, the known-smoothness domain, the count-selected estimator, and the matching pointwise and expected supremum orders. Emphasize compact-range overlap adaptation and the Gaussian-model transfer as the substantive results. Write this section last, after the statements, proofs, and literature comparisons are settled; introduce any early notation with a plain-word gloss.

objs: none

bib: none

home_objs: none
## section: Introduction

Motivate recovery of the treated causal response when treatment availability varies sharply across covariates. Organize the contribution around the statistical rate, the equal-cell construction that stabilizes polynomial fitting, and treatment-count selection under unknown overlap strength. Explain why a global tail condition controls the allocation of treatment information across regions and why an expected spatial-supremum guarantee matters for whole-function recovery. Preview the Gaussian transfer and the bounded-response minimax experiment with their distinct model scopes. Reserve one factual sentence pointing to the appendix verification note, and write the introduction last.

objs: none

bib: rubin1974, rosenbaum1983, imbens2015

home_objs: none
## section: Related work

Lead with Dorn’s closest theorem-level comparator: compare the fixed-setup uniform-in-probability upper result, its pure-power rate, its attribution of overlap-exponent adaptation, and its local anti-concentration condition with the present expected spatial-supremum guarantee over fixed-constant envelopes and compact exponent ranges. Preserve the locators in \citet[Assumptions 1--3 and Theorem 1(ii), p. 12]{Dorn2026GlobalOverlap} and the construction provenance in \citep[Lemmas 11 and 13, pp. 23--24; proof, pp. 27--28]{Dorn2026GlobalOverlap}. Next compare the separate one-dimensional experiments in \citet[Assumption M and Theorem 1, pp. 3--4]{Gaiffas2005DegenerateRates}, \citet[Abstract]{Gaiffas2005AdaptiveDegenerateDesign}, and the spatially normalized criteria in \citet[Assumption D, equation (2.1), and Theorems 1--2]{gaiffas2009} and \citet[Sections 1 and 3]{schmidthieber2024}. Situate equal-cell fitting within local-polynomial and partition-series estimation, and distinguish treatment-specific response recovery from the strict-overlap CATE criterion in \citet[Theorems 1--2 and Remark 11]{KennedyBalakrishnanRobinsWasserman2024} and the functional-loss criterion in \citet[Theorems 1--3]{MouDingWainwrightBartlett2023}. Keep the literature discussion selective and attach every comparison to its experiment, smoothness class, design restrictions, and loss.

objs: none

bib: Dorn2026GlobalOverlap, Gaiffas2005DegenerateRates, Gaiffas2005AdaptiveDegenerateDesign, gaiffas2009, schmidthieber2024, Stone1982, fan1996, newey1997, belloni2015, chen2015, CattaneoFarrellFeng2020, lepski1997, pathak2022, MouDingWainwrightBartlett2023, KennedyBalakrishnanRobinsWasserman2024, khan2010, damour2021, armstrong2021

home_objs: none
## section: Setup and assumptions

Introduce the observed sample, potential outcomes, treated response, fixed model constants, and measurable-estimator convention before their first use. Present the intrinsic cube Hölder convention, followed by the sampling, density, causal-identification, global-tail, response-moment, and response-smoothness restrictions, then collect them in the law class and define the two loss criteria. Describe the response-moment restriction according to its displayed bounded-mean and conditional sub-Gaussian content. Resolve the rate-scale notation here so that subsequent results have a self-contained statistical interpretation. Group synthesized definitions by sample-and-target, smoothness, and risk-scale families; keep source-model and testing apparatus in their later homes.

objs: ass:holder-derivative-bound, ass:holder-modulus, def:holder, ass:iid, ass:density, ass:consistency, ass:exchangeability, ass:global-tail, ass:bounded-potential-outcomes, ass:holder-response, def:model, def:risks

bib: rubin1974, rosenbaum1983, imbens2015, fan1996

home_objs: def:holder, ass:holder-derivative-bound, ass:holder-modulus, ass:iid, ass:density, ass:consistency, ass:exchangeability, ass:global-tail, ass:bounded-potential-outcomes, ass:holder-response, def:model, def:risks
## section: Main results

Organize the section into construction, guarantee, and statistical explanation. First introduce the polynomial template, partitions, microcells, and equal-cell fitting quantities needed to make the central estimator explicit; then present the count-feasibility selector and fitted-response procedure as algorithms. Place \cref{thm:adaptive-minimax} immediately after the construction and explain its known-smoothness domain, compact-range overlap uniformity, expected spatial-supremum criterion, and bounded-response converse. Give a reader-level explanation of how deterministic template conditioning and the ordered treatment-information profile work together to produce the rate. Keep technical concentration statements and the testing construction in the appendix.

objs: synth_1, synth_2, def:template, synth_3, def:mesh-selector, synth_4, def:estimator, thm:adaptive-minimax

bib: fan1996, CattaneoFarrellFeng2020, tsybakov2009

home_objs: def:template, def:mesh-selector, def:estimator, thm:adaptive-minimax
## section: Local treatment geometry and the Gaussian transfer

Use two subsections to explain the class enlargement and its source-model consequence. Introduce the selected-version family predicate before the strip construction, and use \cref{prop:strict-enlargement} to exhibit the coexistence of global tail control and degenerating local treated geometry in dimensions at least two. Then define the fixed-constant source envelope and affine transport immediately before \cref{prop:dorn-a3-free-corollary}, retaining the exact source restrictions and separating the envelope-wide upper guarantee from the exponent-specific Gaussian witnesses. Place the technical source-scope analysis and smoothness-completion argument in the appendix; use the main text to explain the stronger loss criterion and the role of the retained assumptions.

objs: def:dorn-a3, def:thin-strip, prop:strict-enlargement

bib: Dorn2026GlobalOverlap

home_objs: def:dorn-a3, def:thin-strip, prop:strict-enlargement
## section: Discussion and future work

Interpret the roles of known response smoothness, compact overlap-exponent ranges, equal-cell weighting, and conditional sub-Gaussian residuals in the delivered guarantees. Include a clearly titled “Limitations and future work” subsection for the joint smoothness-and-overlap adaptation proposal and its open question, preserving their prospective status. Discuss the logarithmic adaptation price as a question tied to the proposed two-axis construction. Keep distinctions between the common-class bounded-response converse and the Gaussian-envelope upper transfer within this explicitly labelled subsection when describing non-coverage. Use prior work here only to interpret this adaptation question.

objs: def:joint-adaptation-handle, oeq:joint-adaptation

bib: lepski1997, Gaiffas2005AdaptiveDegenerateDesign

home_objs: def:joint-adaptation-handle, oeq:joint-adaptation
## section: Appendix: Identification and upper-bound proofs

Place the identification argument first, followed by the global-tail mass argument, deterministic template conditioning, and selected-mesh concentration and maximal-error analysis. Introduce the population microcell masses, weakest-cell ordering, conditioning notation, and generic centered-variable family immediately before their first use. Organize the proof of the upper part of \cref{thm:adaptive-minimax} around approximation error, conditional stochastic error, and exceptional-sample control. Explain the ordered maximal inequality at its own statistical scale, with constants tracked over the stated compact overlap range.

objs: lem:causal-identification, lem:global-holder-extension, lem:ordered-mass, lem:template-conditioning, lem:selected-mesh

bib: fan1996, tsybakov2009

home_objs: lem:causal-identification, lem:global-holder-extension, lem:ordered-mass, lem:template-conditioning, lem:selected-mesh
## section: Appendix: Bounded testing experiment and geometry proofs

Introduce the bounded testing pair before its admissibility and information-bound argument, then prove the lower part of \cref{thm:adaptive-minimax} using the pair. Keep the totalized measure-family implementation discussion with this auxiliary construction. Follow with the proof of \cref{prop:strict-enlargement}, using the strip law already introduced in the main text and distinguishing the selected-version anti-concentration statement from the normalized treated second-moment calculation. Preserve the evaluation-point and cube-boundary scope of the lower experiment.

objs: def:bounded-lower-pair, lem:bounded-lower-pair

bib: tsybakov2009

home_objs: def:bounded-lower-pair, lem:bounded-lower-pair
## section: Appendix: Source-model transfer and comparison scope

Begin with the exact retained source restrictions supplied by the cited dependency material, then establish the fixed-cube smoothness completion before proving \cref{prop:dorn-a3-free-corollary}. Introduce appendix-local source-loss and comparison-scale notation before analyzing the fixed-family probability criterion. Present the common-known-regression calculation before the source-scope lemma so that the model-family distinction has a mathematical foundation. Separate the source upper comparison, the affine transfer, and the Gaussian strictness construction into identifiable proof components, retaining the source locators and theorem-local dependency disclosures.

objs: lem:fixed-cube-holder-completion, prop:dorn-a3-free-corollary, lem:arbitrary-family-lower-obstruction, lem:dorn-rate-scope

bib: Dorn2026GlobalOverlap

home_objs: lem:fixed-cube-holder-completion, prop:dorn-a3-free-corollary, lem:arbitrary-family-lower-obstruction, lem:dorn-rate-scope
## section: Appendix: Verification note

End the appendix with a short factual account of the Lean machine-checking scope. Consolidate the checked identification, ordered-mass, template-conditioning, selected-mesh, bounded-testing, minimax, geometry, and transfer results, and identify their assumed model restrictions and cited source inputs according to the generated verification metadata. Treat external-source transcriptions and theorem-local dependency footnotes as the trust boundary for those inputs. Keep declaration names and implementation details confined to this note when needed to resolve the verification record.

objs: none

bib: Dorn2026GlobalOverlap
home_objs: none
