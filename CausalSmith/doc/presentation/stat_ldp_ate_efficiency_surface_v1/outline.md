# Title
**Efficient estimation of binary treatment effects under local differential privacy**

**Contribution statement.** For randomized binary trials with fixed interior assignment probabilities and arm means and fixed positive privacy, the paper characterizes the exact regular local asymptotic minimax variance of the average treatment effect over once-per-subject sequential private channels with arbitrary measurable outputs, constructs an attaining private-pilot procedure conditional on a measurable strong-saddle selector, and establishes certified regions of optimal stationary output cardinality.

# Notation

env_overrides: def:pilot-estimator=algorithmv

notation_gaps: \{(Y_i(0),Y_i(1),W_i):i\ge1\}=potential-outcome and assignment notation needs a setup definition, Y_i=observed-outcome notation needs a setup definition, X_i=private record needs a setup definition, x_j=record-alphabet enumeration needs a setup definition, \pi_{\theta,j}=record-probability coordinates need an explicit setup definition, \mu_0=control-arm mean interpretation needs a setup definition, \mu_1=treatment-arm mean interpretation needs a setup definition, q=control-assignment probability needs a setup definition, c=contrast vector needs a setup definition, \tau=target treatment effect needs a setup definition, Q=stationary private-channel class needs a setup definition, I_\theta(Q)=output Fisher information needs an anchored definition, I_\theta(Q)^{+}=generalized inverse and estimability convention need an anchored definition, \kappa(Q)=output-cardinality rule for arbitrary measurable spaces needs an anchored definition, \mathcal A_\varepsilon=feasible staircase-weight set needs an anchored definition, \mathcal S=staircase-pattern index set needs an anchored definition, S_1,\ldots,S_{14}=fixed pattern enumeration needs an anchored definition, Q_\alpha=staircase-channel construction needs an anchored definition, g_S=objective vectors need an anchored definition, h_S(\theta)=objective denominators need an anchored definition, v(t)=profiling direction needs an anchored definition, F_\theta(\alpha,t)=profiled objective needs an anchored definition, \rho_S(\theta,t)=projected-score formula needs an anchored definition, H_{m_n}=pilot-history object needs an anchored definition, S_i=main-sample release indexing needs an anchored definition, \widehat V^*=variance-estimator formula needs an anchored definition, z_{1-\gamma/2}=normal critical-value convention needs an anchored definition, \mathfrak P^{\mathrm{reg}}_{\varepsilon}(\theta_0)=regular-procedure class and squared-error integrability conditions need an anchored definition, L_{\mathcal P}=common local limit law needs an anchored definition, \theta_{n,h}=local-alternative rule needs an anchored definition, \mathcal H_{n,H}(\theta_0)=admissible local-alternative set needs an anchored definition, U_{n,h}^{\mathcal P}=scaled local-error rule needs an anchored definition, \operatorname{smoothPrior}(0,R)=smooth-prior construction needs an appendix definition

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(\{(Y_i(0),Y_i(1),W_i):i\ge1\}\) | \(\{(Y_i(0),Y_i(1),W_i):i\ge1\}\) | Subject sequence of potential outcomes and treatment assignments | Notation gap; setup |
| \(Y_i(0)\) | \(Y_i(0)\) | Subject’s control potential outcome | Notation gap; setup |
| \(Y_i(1)\) | \(Y_i(1)\) | Subject’s treatment potential outcome | Notation gap; setup |
| \(W_i\) | \(W_i\) | Subject’s binary treatment assignment | Notation gap; setup |
| \(Y_i\) | \(Y_i\) | Observed outcome determined by assignment and potential outcomes | Notation gap; setup |
| \(p\) | \(p\) | Known treatment-assignment probability | Notation gap; setup |
| \(q\) | \(q\) | Control-assignment probability used in the comparator | Notation gap; setup |
| \(\mu_0\) | \(\mu_0\) | Control-arm mean coordinate | Notation gap; setup |
| \(\mu_1\) | \(\mu_1\) | Treatment-arm mean coordinate | Notation gap; setup |
| \(\theta=(\mu_0,\mu_1)^{\top}\) | \(\theta=(\mu_0,\mu_1)^{\top}\) | Interior two-coordinate model parameter | `def:binary-trial-model` |
| \(X_i\) | \(X_i\) | Private subject record whose distribution indexes the model | Notation gap; setup |
| \(x_j\) | \(x_j\) | Enumerated private-record value | Notation gap; setup |
| \(\pi_{\theta,j}\) | \(\pi_{\theta,j}\) | Probability assigned to record value \(x_j\) | Notation gap; setup |
| \(P_\theta\) | \(P_\theta\) | Subject-record law indexed by the model parameter | `def:binary-trial-model` |
| \(P_\theta^{\otimes n}\) | \(P_\theta^{\otimes n}\) | Product law of the subject records | `def:binary-trial-model` |
| \(\mathcal M\) | \(\mathcal M\) | Family of product experiments indexed by interior arm-mean coordinates | `def:binary-trial-model` |
| \(c\) | \(c\) | Vector specifying the treatment-effect contrast | Notation gap; setup |
| \(\tau\) | \(\tau\) | Average treatment effect targeted by estimation | Notation gap; setup |
| \(Q\) | \(Q\) | Stationary locally private channel on the record alphabet | Notation gap; setup |
| \(Q_i\) | \(Q_i\) | History-dependent private release rule for subject \(i\) | `def:sequential-channels` |
| \(Q^{(n)}=(Q_i)_{i=1}^n\) | \(Q^{(n)}=(Q_i)_{i=1}^n\) | Nonanticipating sequence of private release rules | `def:sequential-channels` |
| \((\mathcal Z_i,\mathcal G_i)\) | \((\mathcal Z_i,\mathcal G_i)\) | Measurable output space at release stage \(i\) | `def:sequential-channels` |
| \(\prod_{j<i}\mathcal Z_j\) | \(\prod_{j<i}\mathcal Z_j\) | Full product space of preceding releases | `def:sequential-channels` |
| \(h\in\prod_{j<i}\mathcal Z_j\) | \(h\in\prod_{j<i}\mathcal Z_j\) | History argument of the stage-specific release rule | `def:sequential-channels` |
| \(\mathfrak Q^{\mathrm{seq}}_{n,\varepsilon}\) | \(\mathfrak Q^{\mathrm{seq}}_{n,\varepsilon}\) | Class of sequential protocols satisfying the stated privacy bound at every history | `def:sequential-channels` |
| \(I_\theta(Q)\) | \(I_\theta(Q)\) | Fisher-information matrix of the channel’s output experiment | Notation gap; setup |
| \(I_\theta(Q)^{+}\) | \(I_\theta(Q)^{+}\) | Generalized inverse used to evaluate contrast variance | Notation gap; setup |
| \(\operatorname{range}(I_\theta(Q))\) | \(\operatorname{range}(I_\theta(Q))\) | Information-matrix range governing contrast estimability | Same required information definition |
| \(\kappa(Q)\) | \(\kappa(Q)\) | Active-output cardinality of a stationary channel | Notation gap; setup |
| \(\mathcal A_\varepsilon\) | \(\mathcal A_\varepsilon\) | Feasible set of staircase-channel weights | Notation gap; finite oracle |
| \(\alpha\) | \(\alpha\) | Feasible staircase-weight vector | Same required staircase definition |
| \(\alpha_S\) | \(\alpha_S\) | Weight assigned to pattern \(S\) | Same required staircase definition |
| \(\mathcal S\) | \(\mathcal S\) | Index set of staircase patterns | Notation gap; finite oracle |
| \(S_1,\ldots,S_{14}\) | \(S_1,\ldots,S_{14}\) | Fixed enumeration used to identify staircase supports | Notation gap; finite oracle |
| \(Q_\alpha\) | \(Q_\alpha\) | Stationary staircase channel associated with feasible weights | Notation gap; finite oracle |
| \(I_\theta(\alpha)\) | \(I_\theta(\alpha)\) | Fisher information of the staircase channel | Same required information and staircase definitions |
| \(\kappa(Q_\alpha)\) | \(\kappa(Q_\alpha)\) | Active-output cardinality of the staircase channel | Same required cardinality definition |
| \(g_S\) | \(g_S\) | Pattern-specific vector in the profiled objective | Notation gap; finite oracle |
| \(h_S(\theta)\) | \(h_S(\theta)\) | Pattern-specific denominator in the profiled objective | Notation gap; finite oracle |
| \(v(t)\) | \(v(t)\) | Direction indexed by the profiling coordinate | Notation gap; finite oracle |
| \(F_\theta(\alpha,t)\) | \(F_\theta(\alpha,t)\) | Objective jointly indexed by channel weights and profiling coordinate | Notation gap; finite oracle |
| \(\operatorname{vert}(\mathcal A_\varepsilon)\) | \(\operatorname{vert}(\mathcal A_\varepsilon)\) | Vertices of the feasible staircase-weight set | Same required staircase definition |
| \(J^*(\theta,p,\varepsilon)\) | \(J^*(\theta,p,\varepsilon)\) | Maximized nuisance-profiled information value | `def:staircase-saddle` |
| \(V^*(\theta,p,\varepsilon)\) | \(V^*(\theta,p,\varepsilon)\) | Reciprocal of the optimized profiled information value | `def:staircase-saddle` |
| \(\mathcal R_3\) | \(\mathcal R_3\) | Parameter set satisfying the stated three-pattern certificate | `def:support-regions` |
| \(\mathcal R_5\) | \(\mathcal R_5\) | Parameter set satisfying the stated five-pattern certificate and score-separation condition | `def:support-regions` |
| \(\rho_S(\theta,t)\) | \(\rho_S(\theta,t)\) | Projected score used to distinguish active patterns | Notation gap; finite oracle |
| \(m_n\) | \(m_n\) | Number of subjects assigned to the private pilot | `def:pilot-estimator` |
| \(R_i\) | \(R_i\) | Four-category randomized-response pilot release | `def:pilot-estimator` |
| \(\widehat u_k\) | \(\widehat u_k\) | Empirical frequency of pilot release category \(k\) | `def:pilot-estimator` |
| \(\widehat\pi_k\) | \(\widehat\pi_k\) | Inverted randomized-response estimate of a record-category probability | `def:pilot-estimator` |
| \(\delta_n\) | \(\delta_n\) | Clipping margin determined by the pilot size | `def:pilot-estimator` |
| \(\widetilde\theta_0\) | \(\widetilde\theta_0\) | Clipped control-coordinate pilot estimate | `def:pilot-estimator` |
| \(\widetilde\theta_1\) | \(\widetilde\theta_1\) | Clipped treatment-coordinate pilot estimate | `def:pilot-estimator` |
| \(\widetilde\theta\) | \(\widetilde\theta\) | Pilot parameter estimate supplied to the selector | `def:pilot-estimator` |
| \((\alpha_{\vartheta},t_{\vartheta},J_{\vartheta})\) | \((\alpha_{\vartheta},t_{\vartheta},J_{\vartheta})\) | Feasible weights, minimizing coordinate, and optimized value returned by a measurable strong-saddle selector | `def:pilot-estimator` |
| \((\widetilde\alpha,\widetilde t,\widetilde J)\) | \((\widetilde\alpha,\widetilde t,\widetilde J)\) | Selected saddle evaluated at the pilot estimate | `def:pilot-estimator` |
| \(Q_{\widetilde\alpha}\) | \(Q_{\widetilde\alpha}\) | Main-sample staircase channel selected from the pilot | `def:pilot-estimator` |
| \(S_i\) | \(S_i\) | Main-sample release identifying a selected staircase pattern | Notation gap; private-pilot inference |
| \(H_{m_n}\) | \(H_{m_n}\) | History generated by the private pilot releases | Notation gap; private-pilot inference |
| \(\widehat\tau^*\) | \(\widehat\tau^*\) | Affine treatment-effect estimator assembled from pilot and main-sample releases | `def:pilot-estimator` |
| \(\widehat V^*\) | \(\widehat V^*\) | Estimated asymptotic variance used for studentization | Notation gap; private-pilot inference |
| \(z_{1-\gamma/2}\) | \(z_{1-\gamma/2}\) | Normal critical value for the stated Wald coverage level | Notation gap; private-pilot inference |
| \(\mathfrak P^{\mathrm{reg}}_{\varepsilon}(\theta_0)\) | \(\mathfrak P^{\mathrm{reg}}_{\varepsilon}(\theta_0)\) | Class of regular sequential private procedure sequences at the interior point | Notation gap; main efficiency result |
| \(\mathcal P\) | \(\mathcal P\) | Complete sequence of private protocols and estimators | Same required regular-procedure definition |
| \(L_{\mathcal P}\) | \(L_{\mathcal P}\) | Common local limiting error law of a regular procedure | Notation gap; main efficiency result |
| \(\theta_{n,h}\) | \(\theta_{n,h}\) | Local parameter alternative indexed by sample size and perturbation | Notation gap; main efficiency result |
| \(\mathcal H_{n,H}(\theta_0)\) | \(\mathcal H_{n,H}(\theta_0)\) | Admissible local perturbations at the stated localization radius | Notation gap; main efficiency result |
| \(U_{n,h}^{\mathcal P}\) | \(U_{n,h}^{\mathcal P}\) | Scaled treatment-effect estimation error under a local alternative | Notation gap; main efficiency result |
| \(\widetilde A_i\) | \(\widetilde A_i\) | Published custom-Laplace release of the weighted observed outcome | `def:oa-release` |
| \(L_i\) | \(L_i\) | Independent Laplace noise in the comparator release | `def:oa-release` |
| \(\operatorname{Lap}(0,\Delta_A/\varepsilon)\) | \(\operatorname{Lap}(0,\Delta_A/\varepsilon)\) | Comparator’s centered Laplace noise law with the stated scale | `def:oa-release` |
| \(\Delta_A\) | \(\Delta_A\) | Sensitivity constant used to scale comparator noise | `def:oa-release` |
| \(\widehat\tau_{\mathrm{OA}}\) | \(\widehat\tau_{\mathrm{OA}}\) | Sample mean of the custom-Laplace releases | `def:oa-release` |
| \(V_{\mathrm{OA}}(\theta,p,\varepsilon)\) | \(V_{\mathrm{OA}}(\theta,p,\varepsilon)\) | Asymptotic variance constant of the published custom-Laplace sample mean | Notation gap; comparator definition should introduce the formula supplied by the frozen result |
| \(t^*\) | \(t^*\) | Minimizing selection used to construct the sequential lower-bound handle | `def:sequential-vt-handle` |
| \(v(t^*)\) | \(v(t^*)\) | Selected profiling direction in the lower-bound handle | `def:sequential-vt-handle` |
| \(w_R\) | \(w_R\) | Smooth prior selected for the lower-bound argument | `def:sequential-vt-handle` |
| \(\operatorname{smoothPrior}(0,R)\) | \(\operatorname{smoothPrior}(0,R)\) | Smooth-prior rule invoked by the lower-bound construction | Notation gap; proof appendix |
| \(\mathfrak H_{\mathrm{VT}}\) | \(\mathfrak H_{\mathrm{VT}}\) | Pair consisting of the selected direction and smooth prior | `def:sequential-vt-handle` |

# Sections

## section: Abstract

Plan a concise statement of the statistical question, the exact efficiency characterization, the attaining private-pilot inference procedure, and the certified stationary support changes. Express the domain through binary outcomes, fixed interior parameters, fixed positive privacy, and once-per-subject sequential releases. Use words for quantities requiring later definitions. Write the abstract after the main exposition and proofs have been assembled.

objs: none

bib: none

home_objs: none
## section: Introduction

Organize the introduction around estimating a randomized-trial treatment effect when both assignment and outcome are locally private. Present the exact variance characterization as the central contribution, the private-pilot procedure as its inferential realization, and stationary output cardinality as a substantive implication for release design. Explain the practical meaning of support changes and the specifically defined published sample-mean benchmark. Use a single factual sentence pointing to the verification note in \cref{sec:proofs}; develop the abstract and introduction last.

objs: none

bib: Rubin1974, Imbens2015, Warner1965, OhnishiAwan2025

home_objs: none
## section: Related work

Position the paper first against \citet[Theorems 3.3 and 3.5, Remark 3.6, and Section 4]{Steinberger2024}, distinguishing his stated sequential asymptotic framework and scalar optimization from the present finite-input contrast optimization with nuisance parameters and arbitrary measurable sequential outputs. Compare the channel objective with the utility class, finite program, and cardinality conclusion of \citet[Theorems 2 and 4]{KairouzOhViswanath2016}; explain how nuisance profiling changes the optimization problem. Identify the precise causal benchmark in \citet[Sections 3.1 and 3.3, Lemma 4, Theorem 7, and Appendix A.5]{OhnishiAwan2025}. Situate the result alongside rate bounds, information inequalities, exact scalar mechanisms, recent staircase optimization, and efficiency for specified private identifying mechanisms. Use conservative comparisons tied to the cited models and objectives.

objs: none

bib: Hahn1998, Hirano2003, DuchiJordanWainwright2018, Rohde2020, Duchi2024, BarnesChenOzgur2020, Duchi2019, Joseph2019, Steinberger2024, KalininSteinberger2025, KairouzOhViswanath2016, Amorino2025, Amorino2026, GhaziNasserCalmonIssa2026, KormosVanderVaart2026, OhnishiAwan2025, RaabEtAl2025, Elfving1952, Pukelsheim2006

home_objs: none
## section: Trial model and private releases

Introduce the potential outcomes, observed record, known assignment probability, arm means, and treatment-effect contrast before their first formal use. Group the scientific restrictions into data generation, interiority, and privacy conditions while preserving each frozen environment. Define stationary and sequential releases, emphasizing joint protection of assignment and outcome and the once-per-subject history structure. Resolve the information and output-cardinality notation needed by the main results. Keep local-asymptotic and pilot-specific definitions in their consuming sections.

objs: ass:iid-subjects, ass:random-assignment, ass:known-assignment, ass:consistency, ass:binary-outcomes, ass:interior-assignment, ass:interior-means, ass:fixed-privacy, ass:sequential-ldp, def:binary-trial-model, def:sequential-channels

bib: Rubin1974, Imbens2015, Warner1965, Dwork2006, Dwork2014

home_objs: ass:iid-subjects, ass:random-assignment, ass:known-assignment, ass:consistency, ass:binary-outcomes, ass:interior-assignment, ass:interior-means, ass:fixed-privacy, ass:sequential-ldp, def:binary-trial-model, def:sequential-channels
## section: Exact efficiency bound and finite optimization

Introduce the staircase family and its profiled information objective through grouped presentation definitions resolving the notation gaps. Explain nuisance projection and the reduction to a finite upper envelope before connecting stationary channel optimization to the sequential local asymptotic efficiency criterion. Define local alternatives, scaled errors, regular procedures, and their common limit laws immediately before the headline efficiency result. Make the distinction between the lower-bound domain and the regular attaining class explicit through the stated quantifiers, and retain the measurable-selector condition when describing attainment. Defer the staircase refinement and sequential lower-bound apparatus to \cref{sec:proofs}.

objs: synth_8, synth_4, def:staircase-saddle, thm:finite-oracle, synth_2, synth_3, synth_6, ass:pilot-diverges, ass:pilot-sublinear, synth_10, def:pilot-estimator, thm:sequential-minimax

bib: LeCam2000, VanDerVaart1998, Elfving1952, Pukelsheim2006, Sion1958

home_objs: synth_8, synth_4, def:staircase-saddle, thm:finite-oracle, synth_2, synth_3, synth_6, thm:sequential-minimax
## section: Private-pilot estimation and Wald inference

Present the central estimation construction as a boxed algorithm, with the measurable strong-saddle selector specified as its input rule. Explain how private pilot releases choose the main-sample channel and how the affine correction targets the treatment effect. Place the two pilot-size restrictions alongside the algorithm, then introduce the variance estimator and critical-value convention before the inference result. Develop the roles of conditional unbiasedness, regularity, variance consistency, and pointwise Wald coverage, including parameter points where optimal support changes. Preserve the distinction between an arbitrary admissible pilot schedule in the attainment result and the exhibited schedule used for minimax equality.

objs: synth_9, synth_1, thm:pilot-attainment

bib: Warner1965, VanDerVaart1998

home_objs: ass:pilot-diverges, ass:pilot-sublinear, synth_10, def:pilot-estimator, synth_9, synth_1, thm:pilot-attainment
## section: Optimal release cardinality

Explain output cardinality as a property of efficient stationary release design. Begin with the global existence bound, then introduce the certificate-defined regions and interpret their exact cardinality implications using the fixed pattern enumeration. Contrast the certified neighborhoods at common assignment and privacy settings, and use the balanced reduction as an interpretable special case of the general optimization. Distinguish uniqueness within the staircase family from the cardinality conclusions for arbitrary attaining stationary channels. Reserve certificate algebra and score-based nonmerger arguments for \cref{sec:proofs}.

objs: thm:five-output-upper-bound, synth_5, def:support-regions, thm:five-output-region, thm:three-output-region, thm:support-transition, thm:balanced-reduction

bib: Warner1965, Elfving1952, Pukelsheim2006

home_objs: thm:five-output-upper-bound, synth_5, def:support-regions, thm:five-output-region, thm:three-output-region, thm:support-transition, thm:balanced-reduction
## section: Interval comparison and prospective trial use

Define the published known-assignment custom-Laplace release and its sample mean before evaluating the asymptotic Wald half-length comparison. Explain the comparison through the two variance constants and the frozen numerical witness, retaining the benchmark’s estimator-specific scope. Describe a prospective binary indicator of meeting the Colombian program’s attendance threshold as a consumer of the binary-trial analysis, with design inputs and outcome construction clearly identified. Any displayed efficiency calculations should derive directly from the frozen formulas and be labelled as prospective design calculations.

objs: def:oa-release, thm:laplace-comparison

bib: Horvitz1952, OhnishiAwan2025, BarreraOsorioEtAl2011

home_objs: def:oa-release, thm:laplace-comparison
## section: Discussion, extensions, and limitations

Interpret the relationship among contrast-specific optimization, pilot adaptation, and stationary support changes. Explain how a vanishing pilot fraction realizes the local efficiency constant while preserving pointwise inference across support boundaries. Include an explicitly titled “Limitations and future work” subsection covering complete support classification, boundary arm means, changing assignment or privacy sequences, broader outcome models, repeated-user interaction, and comparisons with full-likelihood estimation under a specified release. Keep interpretation tied to the paper’s established results and present the attendance endpoint as prospective.

objs: none

bib: none

home_objs: none
## section: Proofs and verification note

Use the structural label `sec:proofs`. Start with the measurable staircase refinement and the equality condition used in cardinality arguments, then prove the finite oracle and support results. Present the pilot argument with its selector condition, local regularity, variance consistency, and support-boundary inference. Introduce the smooth-prior construction and the sequential van Trees handle immediately before their first use in the sequential lower-bound proof; develop the conditional-score martingale and uniform domination inside that proof. Include the comparator calculation and organize proof references using the anchored object labels. End with a brief verification note consolidating the machine-checking scope of the frozen results, the model and procedure restrictions supplied as assumptions or inputs, and theorem-local cited dependencies.

objs: lem:staircase-refinement, synth_7, def:sequential-vt-handle

bib: Blackwell1953, KairouzOhViswanath2016, Sion1958, VanTrees2001, Gill1995, LeCam2000, VanDerVaart1998, Steinberger2024, OhnishiAwan2025
home_objs: lem:staircase-refinement, synth_7, def:sequential-vt-handle
