# Title
**Treatment effect estimation with missing outcomes and many covariate categories**

**Contribution statement.** This paper characterizes minimax treatment-effect precision under randomized assignment and missing-at-random outcome ascertainment, establishing logarithmic complexity thresholds under rare arrival and fixed strict-interior positivity, optimal honest interval length under rare arrival, and the sharp ascertainment requirement for parametric squared-error risk uniformly over arbitrary covariate-alphabet growth.

# Notation

Notation follows the frozen layer. Homes below identify anchored definitions; an unresolved home is recorded explicitly in `notation_gaps`. Construction symbols receive definitions before their first substantive use, with the central estimator in the main body and converse-specific apparatus in the appendix.

notation_gaps: \(P\)=the finite full-data law needs an anchored definition; \((X,A,S(0),S(1),Y(0),Y(1),S,Y,R)\)=the full-data coordinates and their binary domains need an anchored definition; \(O_i\)=the observed-record map needs an anchored definition; \(\mathbf O_n\)=the observed sample needs an anchored definition; \(\mathcal J_d\)=the cell-index set is used but not defined in a frozen definition; \(p_{axs}(P)\)=the full-membership cell probability is used but not defined; \(\rho_{axs}(P)\)=the conditional arrival probability is used but not defined; \(g(a)\)=the treatment sign function is used but not defined; \(N\)=the effective sample-size quantity is introduced outside an anchored definition; \(\ell\)=the logarithmic scale is used without an anchored definition; \(m\)=the stream-intensity quantity is used without an anchored definition; \(N_0\)=the effective stream size is defined in certificate statements rather than an anchored definition; \(k\)=the estimator degree is used without its tuning rule; \(B\)=the estimator threshold is used without its tuning rule; \(M_j\)=the membership count is referenced as previously declared but its declaration is absent; \(C'_j\)=the pilot count is referenced as previously declared but its declaration is absent; \(C_j\)=the estimation count is referenced as previously declared but its declaration is absent; \(U_j\)=the intermediate count is referenced as previously declared but its declaration is absent; \(W_j\)=the cell-weight statistic is referenced without its defining formula; \(D_j\)=the elementary cell statistic is referenced without its defining formula; \(Q_k\)=the Chebyshev quantity is referenced without its defining formula; \(a_v\)=the polynomial coefficients are referenced without their defining rule; \(H_j\)=the intermediate cell statistic is referenced without its defining formula; \(G_j\)=the polynomial cell statistic is referenced without its defining formula; \(\operatorname{clip}_{[-1,1]}\)=the clipping operator needs an anchored definition; \(\Pi_{[-1,1]}\)=the projection operator needs an anchored definition and an explicit relationship to clipping; \(\mathfrak U_{n,d,q}\)=the deterministic envelope is defined in theorem bodies rather than an anchored definition; \(\gamma_0\)=the certificate constant is defined in theorem bodies rather than an anchored definition; \(b_{n,d,q}\)=the certificate quantity is defined in theorem bodies rather than an anchored definition; \(v_{n,d,q}\)=the certificate quantity is defined in theorem bodies rather than an anchored definition; \(\operatorname{length}(I^{\mathrm{mix}}_\alpha)\)=interval length needs an anchored definition; \(P_u\)=the one-cell law family is introduced in a lemma rather than an anchored definition; \(\mathbf Z_n\)=the observational sample needs an anchored definition; \(o(x,b,y;u)\)=the synthetic observation map is introduced in a lemma rather than an anchored definition; \(o_i(u_i)\)=the sample-level synthetic observation map is introduced in a theorem rather than an anchored definition; \(P_Z^*\)=the induced randomized full-data law needs an anchored construction home; \(\widehat\theta^{\mathrm{poly}}_{n,d,\epsilon}(\mathbf Z_n)\)=the observational estimation procedure is introduced in a theorem rather than an anchored definition; \(Q_\lambda\)=the generic decision-experiment law family is introduced in a lemma rather than an anchored definition; \(\vartheta(\lambda)\)=the generic decision-experiment target is introduced in a lemma rather than an anchored definition; \(b_\kappa(o)\)=the barycenter operator is introduced in a lemma rather than an anchored definition; \(Q_0,Q_1\)=the generic testing laws need an anchored experiment home; \(Q_i\ltimes\kappa\)=the joint input-action law notation is introduced in a lemma rather than an anchored definition; \(Q_i\kappa\)=the action-marginal notation is introduced in a lemma rather than an anchored definition; \(\operatorname{TV}\)=the total-variation convention is defined in a lemma rather than an anchored definition; \(\psi\)=the randomized testing rule needs an anchored decision-experiment home.

env_overrides: def:mixed-count-estimator=algorithmv, def:activation-lower-handle=algorithmv, prop:fixed-d-effective-sample-reduction=propositionv, prop:phase-boundaries=propositionv, prop:unrestricted-fixed-q-phase-boundaries=propositionv, prop:unrestricted-complete-arrival-phase-boundary=propositionv, prop:unrestricted-near-complete-phase-boundary=propositionv, prop:unrestricted-uniform-near-complete-elbow=propositionv

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(P\) | \(P\) | Full-data probability law underlying the randomized experiment | Gap; setup |
| \((X,A,S(0),S(1),Y(0),Y(1),S,Y,R)\) | \((X,A,S(0),S(1),Y(0),Y(1),S,Y,R)\) | Baseline, assignment, potential and realized surrogate and outcome, and arrival coordinates | Gap; setup |
| \(O_i\) | \(O_i\) | Observed record retaining baseline, assignment, surrogate, arrival, and arrived outcome | Gap; setup |
| \(\mathbf O_n\) | \(\mathbf O_n\) | Sample of \(n\) observed records | Gap; setup |
| \(\mathcal J_d\) | \(\mathcal J_d\) | Index set for treatment–baseline–surrogate cells | Gap; setup |
| \(p_{axs}(P)\) | \(p_{axs}(P)\) | Full-membership probability of an indexed cell | Gap; setup |
| \(\rho_{axs}(P)\) | \(\rho_{axs}(P)\) | Outcome-arrival probability within an occupied cell | Gap; setup |
| \(g(a)\) | \(g(a)\) | Treatment-arm sign used in the cell contrast | Gap; setup |
| \(\mathcal M_{n,d,q}\) | \(\mathcal M_{n,d,q}\) | Randomized MAR model satisfying the rare-arrival restriction | def:model-class |
| \(\mathcal E_{n,d,q}\) | \(\mathcal E_{n,d,q}\) | Family of observed-sample laws induced by the rare-arrival model | def:observed-experiment |
| \(\tau(P)\) | \(\tau(P)\) | Population average treatment effect | def:ate-functional |
| \(\Phi(P)\) | \(\Phi(P)\) | Total signed observed-cell functional | def:cell-functional |
| \(\mu_{axs}(P)\) | \(\mu_{axs}(P)\) | Arrived-cell outcome mean with the frozen zero convention | def:cell-functional |
| \(c_{axs}(P)\) | \(c_{axs}(P)\) | Cell membership probability times arrived-cell mean with zero contribution for null cells | def:cell-functional |
| \(r_{n,d,q}\) | \(r_{n,d,q}\) | Truncated effective-sample-size and alphabet-complexity rate expression | def:frontier-rate |
| \(\mathcal T_n\) | \(\mathcal T_n\) | Parameter-independent estimator Markov kernels with values in \([-1,1]\) | def:unrestricted-minimax-risk; def:minimax-risk |
| \(\mathsf T\) | \(\mathsf T\) | Possibly randomized estimator in the stated decision class | def:unrestricted-minimax-risk; def:minimax-risk |
| \(\mathfrak R_{n,d,q}\) | \(\mathfrak R_{n,d,q}\) | Minimax squared-error risk over the rare-arrival model | def:minimax-risk |
| \(\mathcal C_{n,d,q,\alpha}\) | \(\mathcal C_{n,d,q,\alpha}\) | Parameter-independent connected-interval procedures with uniform joint coverage | def:interval-length-risk |
| \(\mathsf I\) | \(\mathsf I\) | Randomized interval-endpoint procedure | def:interval-length-risk |
| \((l,u)\) | \((l,u)\) | Ordered interval endpoints in \([-1,1]\) | def:interval-length-risk |
| \([l,u]\) | \([l,u]\) | Realized connected confidence interval | def:interval-length-risk |
| \(\mathfrak L_{n,d,q,\alpha}\) | \(\mathfrak L_{n,d,q,\alpha}\) | Minimax maximal expected length among uniformly honest connected intervals | def:interval-length-risk |
| \(K_0\) | \(K_0\) | Independent Poisson prefix length used by the estimator | def:mixed-count-estimator |
| \(\omega\) | \(\omega\) | Auxiliary prefix and stream-assignment randomization | def:mixed-count-estimator |
| \(N\) | \(N\) | Effective sample size \(nq\) | Gap; setup |
| \(\ell\) | \(\ell\) | Logarithmic scale appearing in tuning and the rare-arrival restriction | Gap; setup |
| \(m\) | \(m\) | Stream-intensity parameter in the risk certificate | Gap; estimator construction |
| \(N_0\) | \(N_0\) | Effective stream size specified by \(mq=N/6\) | Gap; estimator construction |
| \(k\) | \(k\) | Degree parameter for the estimator’s polynomial branch | Gap; estimator construction |
| \(B\) | \(B\) | Threshold parameter for the estimator’s polynomial branch | Gap; estimator construction |
| \(M_j\) | \(M_j\) | Membership-stream count referenced by the estimator | Gap; estimator construction |
| \(C'_j\) | \(C'_j\) | Pilot-stream count referenced by the estimator | Gap; estimator construction |
| \(C_j\) | \(C_j\) | Estimation-stream count referenced by the estimator | Gap; estimator construction |
| \(U_j\) | \(U_j\) | Intermediate count referenced by the estimator | Gap; estimator construction |
| \(W_j\) | \(W_j\) | Cell-weight statistic used in the signed sum | Gap; estimator construction |
| \(D_j\) | \(D_j\) | Cell statistic used on the elementary branch | Gap; estimator construction |
| \(Q_k\) | \(Q_k\) | Chebyshev quantity used on the polynomial branch | Gap; estimator construction |
| \(a_v\) | \(a_v\) | Coefficients associated with the polynomial construction | Gap; estimator construction |
| \(H_j\) | \(H_j\) | Intermediate cell statistic used on the polynomial branch | Gap; estimator construction |
| \(G_j\) | \(G_j\) | Cell statistic entering the polynomial signed sum | Gap; estimator construction |
| \(\widetilde\tau(\mathbf O_n;\omega)\) | \(\widetilde\tau(\mathbf O_n;\omega)\) | Clipped auxiliary randomized output with the frozen branch rules | def:mixed-count-estimator |
| \(\widehat\tau^{\mathrm{mix}}_{n,d,q}(\mathbf O_n)\) | \(\widehat\tau^{\mathrm{mix}}_{n,d,q}(\mathbf O_n)\) | Conditional average of the auxiliary randomized output given the observed sample | def:mixed-count-estimator |
| \(\operatorname{clip}_{[-1,1]}\) | \(\operatorname{clip}_{[-1,1]}\) | Clipping operation used by the mixed-count construction | Gap; estimator construction |
| \(K\) | \(K\) | Moment-matching degree \(\lceil\ell\rceil\) | def:activation-lower-handle |
| \(H\) | \(H\) | Reciprocal-approximation support endpoint \(K^2\) | def:activation-lower-handle |
| \(b_0\) | \(b_0\) | Nominal rare-cell mass \(\eta/(N\ell)\) | def:activation-lower-handle |
| \(J\) | \(J\) | Number of rare baseline cells under the frozen dimension and mass cap | def:activation-lower-handle |
| \((\Pi_0,\Pi_1)\) | \((\Pi_0,\Pi_1)\) | Eligible finite prior pair with matching moments and reciprocal-mean separation | def:activation-lower-handle |
| \(Z\) | \(Z\) | Latent cell parameter drawn from an eligible prior | def:activation-lower-handle |
| \(\mathfrak H_{\mathrm{act}}\) | \(\mathfrak H_{\mathrm{act}}\) | Activated fuzzy-hypothesis experiment constructed from an eligible prior pair | def:activation-lower-handle |
| \(\mathsf B_{\mathrm{act}}\) | \(\mathsf B_{\mathrm{act}}\) | Revealed parameter-independent Bernoulli activation flag | def:activation-lower-handle |
| \(I^{\mathrm{mix}}_\alpha\) | \(I^{\mathrm{mix}}_\alpha\) | Clipped confidence interval centered on the mixed-count estimator | def:risk-envelope-interval |
| \(\mathfrak U_{n,d,q}\) | \(\mathfrak U_{n,d,q}\) | Explicit deterministic squared-error envelope | Gap; estimator construction |
| \(\operatorname{length}(I^{\mathrm{mix}}_\alpha)\) | \(\operatorname{length}(I^{\mathrm{mix}}_\alpha)\) | Upper endpoint minus lower endpoint of the realized interval | Gap; honest intervals |
| \(\mathcal M^{+}_{n,d,q}\) | \(\mathcal M^{+}_{n,d,q}\) | Randomized MAR model at an arbitrary arrival floor | def:unrestricted-arrival-model-class |
| \(P_Z\) | \(P_Z\) | One-record observational law in the discrete positivity class | def:zeng-discrete-ate-class |
| \((X,B^{\mathrm{obs}},Y)\) | \((X,B^{\mathrm{obs}},Y)\) | Observational baseline, treatment, and binary outcome record | def:zeng-discrete-ate-class |
| \(\mathcal D_{d,\epsilon}\) | \(\mathcal D_{d,\epsilon}\) | Discrete observational laws with strict-interior occupied-cell treatment positivity | def:zeng-discrete-ate-class |
| \(p_x\) | \(p_x\) | Observational baseline-category probability | def:zeng-discrete-ate-class |
| \(\pi_x\) | \(\pi_x\) | Observational treatment propensity in an occupied category | def:zeng-discrete-ate-class |
| \(\mu_{bx}\) | \(\mu_{bx}\) | Observational outcome mean within an occupied treatment–baseline category | def:zeng-discrete-ate-class |
| \(\theta_Z(P_Z)\) | \(\theta_Z(P_Z)\) | Baseline-weighted observational regression contrast with zero null-category contributions | def:zeng-ate-functional |
| \(\mathfrak R^Z_{n,d,\epsilon}\) | \(\mathfrak R^Z_{n,d,\epsilon}\) | All-estimator minimax squared risk for the observational contrast | def:zeng-minimax-risk |
| \(\widehat\theta\) | \(\widehat\theta\) | Possibly randomized estimator of the observational contrast | def:zeng-minimax-risk |
| \(\mathfrak R^{+}_{n,d,q}\) | \(\mathfrak R^{+}_{n,d,q}\) | All-estimator minimax squared risk over the unrestricted-arrival model | def:unrestricted-minimax-risk |
| \(\widehat\tau^{\mathrm{HT}}_n(\mathbf O_n)\) | \(\widehat\tau^{\mathrm{HT}}_n(\mathbf O_n)\) | Clipped observed-outcome arm contrast | def:complete-arrival-ht-estimator |
| \(\Pi_{[-1,1]}\) | \(\Pi_{[-1,1]}\) | Projection operation used by the observed-outcome contrast | Gap; main point-risk results |
| \(\gamma_0\) | \(\gamma_0\) | Prefix-tail constant \(\log 2-1/2\) | Gap; certificate appendix |
| \(b_{n,d,q}\) | \(b_{n,d,q}\) | Deterministic certificate quantity entering the squared contribution | Gap; certificate appendix |
| \(v_{n,d,q}\) | \(v_{n,d,q}\) | Deterministic certificate quantity entering the additive contribution | Gap; certificate appendix |
| \(P_u\) | \(P_u\) | One-cell randomized Bernoulli law indexed by its treated outcome mean | Gap; rare-arrival converse appendix |
| \(\mathbf Z_n\) | \(\mathbf Z_n\) | Independent sample of observational records | Gap; observational extension |
| \(o(x,b,y;u)\) | \(o(x,b,y;u)\) | Fair-coin synthetic observation map preserving matched-treatment outcomes | Gap; observational extension |
| \(o_i(u_i)\) | \(o_i(u_i)\) | Record-level synthetic observation used by the observational estimator | Gap; observational extension |
| \(P_Z^*\) | \(P_Z^*\) | Randomized MAR full-data law induced by synthetic assignment | Gap; observational extension |
| \(\widehat\theta^{\mathrm{poly}}_{n,d,\epsilon}(\mathbf Z_n)\) | \(\widehat\theta^{\mathrm{poly}}_{n,d,\epsilon}(\mathbf Z_n)\) | Conditional average of the mixed-count estimator over synthetic assignments | Gap; observational extension |
| \(Q_\lambda\) | \(Q_\lambda\) | Generic finite-sample experiment law indexed by a parameter | Gap; decision-theory appendix |
| \(\vartheta(\lambda)\) | \(\vartheta(\lambda)\) | Bounded scalar target in the generic decision experiment | Gap; decision-theory appendix |
| \(\kappa\) | \(\kappa\) | Parameter-independent Markov decision rule | Gap; decision-theory appendix |
| \(b_\kappa(o)\) | \(b_\kappa(o)\) | Conditional mean of a bounded scalar decision rule | Gap; decision-theory appendix |
| \(Q_0,Q_1\) | \(Q_0,Q_1\) | Pair of finite-sample laws in the testing comparison | Gap; decision-theory appendix |
| \(Q_i\ltimes\kappa\) | \(Q_i\ltimes\kappa\) | Joint input-action law formed from an experiment and a common decision rule | Gap; decision-theory appendix |
| \(Q_i\kappa\) | \(Q_i\kappa\) | Action marginal induced by the common decision rule | Gap; decision-theory appendix |
| \(\operatorname{TV}\) | \(\operatorname{TV}\) | Supremum of absolute probability differences over measurable events | Gap; decision-theory appendix |
| \(\psi\) | \(\psi\) | Possibly randomized binary testing rule | Gap; decision-theory appendix |

# Sections

## section: Abstract

Plan a compact account of the statistical question, the randomized MAR setting, and the complementary roles of outcome ascertainment and covariate cardinality. Prioritize the sharp requirement for parametric point risk uniformly over arbitrary alphabet growth, the logarithmic complexity thresholds in the matched rare-arrival and fixed-positivity regimes, and honest interval length within the rare-arrival regime. Express each domain affirmatively and gloss every symbol used before its formal definition. Draft the abstract last, after the body and scope boundaries are settled.

objs: none
bib: none

home_objs: none
## section: Introduction

Organize the introduction around when randomized assignment delivers precise treatment-effect estimation as outcome ascertainment becomes incomplete and the number of baseline categories grows. Explain the distinction between information from complete memberships and information from arrived outcomes, then preview the paper’s complementary precision regimes and the observational application. Present the uniform-over-alphabets ascertainment requirement as a central economic and statistical interpretation, with the rare-arrival and fixed-positivity results explaining the role of category complexity. Include a single factual sentence directing readers to the appendix verification note. Draft this section last.

objs: none
bib: Rubin1974, Imbens2015, Rubin1976

home_objs: none
## section: Related work

Make the closest rate comparison against \citet[Assumption 2, Theorems 1–2, Section 3.2, and Appendix C.5]{ZengBalakrishnanHanKennedy2026}: distinguish their fixed-positivity observational experiment and logarithmic lower-bound comparison from the constructive observational result and randomized outcome-arrival analysis developed here. Compare the finite-alphabet minimax question with the surrogate-assisted efficiency and labelled-sample asymptotics of \citet[Theorems 2.1–2.2 and 4.1–4.2]{KallusMao2025}, and with the decaying-MAR inference of \citet[Theorems 2.2 and 4.1, equation (2.3)]{ZhangChakraborttyBradic2025}, preserving their nuisance and moment conditions. Attribute polynomial approximation and moment matching to the discrete-functional literature, reciprocal approximation to its classical sources, and honest-length comparisons to the uncertainty-quantification literature. Locate the complete-arrival comparison against \citet{Sudijono2026} by distinguishing the present i.i.d. population experiment from joint design-and-estimation optimization for finite-population sample effects. Use surrogate and clinical-trial sources for motivation, and keep novelty claims tied to these exact experiment and theorem comparisons.

objs: none
bib: ZengBalakrishnanHanKennedy2026, KallusMao2025, ZhangChakraborttyBradic2025, WuYang2019, JiaoVenkatHanWeissman2015, Wu2016, Good1956, Paninski2003, Meinardus1967, https://doi.org/10.1007/s11075-026-02364-1, Donoho1994, Cai2004, ArmstrongKolesar2020, RobinsLiTchetgenVanderVaart2008, Robins2009, Hirshberg2021, Horvitz1952, Rosenbaum1983, Hahn1998, Hirano2003, Robins1994, Bang2005, Tsiatis2006, Chernozhukov2018, Kennedy2022, Crump2009, Khan2010, Rothe2017, Ma2020, Dorn2025, Prentice1989, Fleming1996, Athey2026, MarschnerBecker2001, VanLancker2020, Cheng2021, Zhang2022, Chakrabortty2024, Sudijono2026

home_objs: none
## section: Experiment, identification, and risk

Introduce the finite randomized experiment, observed records, occupied-cell probabilities, arrival probabilities, treatment sign, and effective sample-size notation before any assumptions use them. Present randomization, consistency, MAR, and occupied-cell arrival restrictions as the statistical foundation. Define the unrestricted model first, then its rare-arrival subclass and observed experiment, making the latter restriction explicit at its point of introduction. Define the causal target, total observed-cell functional, all-estimator squared-error risks, and comparison-rate expression as related object families. Explain the surrogate’s role in conditioning outcome arrival and use \cref{lem:unrestricted-cell-identification} for identification, with its proof in the appendix. Explain joint sample-and-procedure expectations and direct readers to \cref{lem:randomized-kernel-barycenter} for the squared-loss comparison.

objs: ass:iid-sampling, synth_2, synth_3, synth_4, ass:randomized-independence, ass:balanced-randomization, synth_1, ass:surrogate-consistency, ass:outcome-consistency, ass:arrival-mar, synth_6, synth_16, ass:occupied-cell-arrival, def:unrestricted-arrival-model-class, def:ate-functional, synth_19, def:cell-functional, synth_5, def:unrestricted-minimax-risk, synth_7, ass:rare-arrival-slice, def:model-class, def:observed-experiment, def:minimax-risk, def:frontier-rate
bib: Rubin1974, Rubin1976, Imbens2015, Robins1994, Tsiatis2006

home_objs: ass:iid-sampling, ass:randomized-independence, ass:balanced-randomization, ass:surrogate-consistency, ass:outcome-consistency, ass:arrival-mar, ass:occupied-cell-arrival, def:unrestricted-arrival-model-class, def:ate-functional, def:cell-functional, def:unrestricted-minimax-risk, ass:rare-arrival-slice, def:model-class, def:observed-experiment, def:minimax-risk, def:frontier-rate
## section: Point estimation across ascertainment regimes

Present the main squared-error results as a reader-facing map of ascertainment and category complexity. Start with the all-arrival risk envelope and the observed-outcome contrast, then develop the large-alphabet comparison and the exact uniform-over-alphabets near-complete-arrival criterion. Place the sufficient near-complete window and complete-arrival specialization alongside that criterion. Follow with the matched rare-arrival result and its effective-sample-size and category-growth implications, then the fixed strict-interior arrival comparison and its sequence-level thresholds. Use a compact regime table whose entries point through cleveref to their supporting environments and identify whether constants are universal or depend on a fixed arrival floor. Keep the universal envelope, the large-alphabet matched region, and the two logarithmic matched regimes distinct.

objs: def:complete-arrival-ht-estimator, synth_8, synth_18, synth_13, synth_17, synth_10, synth_15, synth_14, synth_12, synth_9, synth_11, def:mixed-count-estimator, thm:unrestricted-near-complete-arrival-envelope, thm:unrestricted-large-alphabet-deficit-lower, prop:unrestricted-uniform-near-complete-elbow, prop:unrestricted-near-complete-phase-boundary, thm:unrestricted-complete-arrival-frontier, prop:unrestricted-complete-arrival-phase-boundary, thm:matched-minimax-frontier, prop:fixed-d-effective-sample-reduction, prop:phase-boundaries, thm:unrestricted-fixed-q-minimax-frontier, prop:unrestricted-fixed-q-phase-boundaries
bib: Horvitz1952, Imbens2015

home_objs: def:complete-arrival-ht-estimator, thm:unrestricted-near-complete-arrival-envelope, thm:unrestricted-large-alphabet-deficit-lower, prop:unrestricted-uniform-near-complete-elbow, prop:unrestricted-near-complete-phase-boundary, thm:unrestricted-complete-arrival-frontier, prop:unrestricted-complete-arrival-phase-boundary, thm:matched-minimax-frontier, prop:fixed-d-effective-sample-reduction, prop:phase-boundaries, thm:unrestricted-fixed-q-minimax-frontier, prop:unrestricted-fixed-q-phase-boundaries
## section: A constructive estimator

Present \cref{def:mixed-count-estimator} as the central main-body algorithm, preceded by grouped definitions of its tuning quantities, stream counts, weights, polynomial quantities, and clipping operation. Explain how full-membership information and outcome-arrival information enter separate parts of the cell contribution, and how the elementary and polynomial branches address different complexity regimes. Distinguish the auxiliary randomized output from its deterministic conditional average and connect the construction to \cref{thm:unrestricted-mixed-count-upper}. Introduce the deterministic risk envelope sufficiently for the subsequent interval construction; place its full certificate formulas and moment calculations in the appendix. Explain the estimator as a statistical construction, with computational interpretation confined to what the frozen procedure establishes.

objs: thm:unrestricted-mixed-count-upper
bib: WuYang2019, JiaoVenkatHanWeissman2015, Wu2016

home_objs: def:mixed-count-estimator, thm:unrestricted-mixed-count-upper
## section: Honest intervals under rare outcome arrival

Define uniformly honest connected-interval procedures and their maximal expected-length criterion, including auxiliary procedure randomization in both coverage and length. Introduce the interval built from the deterministic risk envelope and present \cref{thm:connected-interval-frontier}. Explain why the fixed-coverage interval result answers an uncertainty-quantification question alongside squared-error estimation, and why the converse works with the joint sample-and-endpoint law. Keep the discussion of coverage levels explicit and connect the interval order to the previously defined comparison rate through exact internal references.

objs: def:interval-length-risk, def:risk-envelope-interval, thm:connected-interval-frontier
bib: Cai2004, ArmstrongKolesar2020

home_objs: def:interval-length-risk, def:risk-envelope-interval, thm:connected-interval-frontier
## section: An observational extension through synthetic assignment

Introduce the discrete observational law, strict-interior positivity class, total regression contrast, and associated all-estimator risk as one coherent extension. Before the first use of the synthetic maps, provide grouped presentation definitions for the fair-coin transformation and observational estimation procedure. Explain how parameter-independent synthetic assignment preserves the target and yields a constructive estimator from the randomized MAR construction. Present \cref{thm:zeng-fixed-positivity-polynomial-frontier}, with its observational causal interpretation tied to consistency and conditional exchangeability. Explain the direction of the experiment comparison supporting the earlier fixed-arrival result, citing \cref{lem:synthetic-randomization-kernel} for the formal map and the published lower-bound input with its locator.

objs: def:zeng-discrete-ate-class, def:zeng-ate-functional, def:zeng-minimax-risk, thm:zeng-fixed-positivity-polynomial-frontier
bib: ZengBalakrishnanHanKennedy2026, Rosenbaum1983, Hahn1998, Hirano2003

home_objs: def:zeng-discrete-ate-class, def:zeng-ate-functional, def:zeng-minimax-risk, thm:zeng-fixed-positivity-polynomial-frontier
## section: Discussion and extensions

Interpret the paper’s precision comparisons in terms of the number of informative outcomes, the complexity of covariate adjustment, and the ascertainment deficit. Explain the quantifier distinction between a guarantee uniform over arbitrary alphabet growth and a guarantee along a particular dimension sequence. Discuss the surrogate as an arrival-conditioning variable and the constant-surrogate specialization as a useful benchmark. Treat clinical-trial applications as prospective interpretations of the statistical model, with any Marschner–Becker example clearly identified as motivation. Direct readers to a separately titled Limitations and open questions subsection for remaining scope and priority issues.

objs: none
bib: MarschnerBecker2001, VanLancker2020

home_objs: none
## section: Limitations and open questions

Collect genuine non-coverage statements here: matching the unrestricted envelope throughout intermediate moving-arrival and alphabet regimes; extending connected-interval comparisons beyond the rare-arrival restriction; characterizing the near-complete requirement for individual smaller alphabet sequences; studying the observational positivity endpoint; and extending the model beyond MAR. Separate statistical attainment from practical evaluation of the exact conditional-average procedures. Record the unresolved theorem-level priority audit concerning the earlier discrete causal-model announcement, using the verified citation pool as the boundary for manuscript citations. Frame clinical applications as future evaluation rather than empirical validation.

objs: none
bib: none

home_objs: none
## section: Appendix A. Identification and decision-theory preliminaries

Place the generic finite decision-experiment definitions immediately before the barycenter and total-variation lemmas. Prove the squared-loss comparison over randomized procedures and the joint-law testing comparison, then give the unrestricted and rare-model identification arguments. Establish the synthetic-assignment experiment map used by the observational extension and fixed-arrival comparison. Keep generic testing laws, barycenters, action marginals, and related notation local to this appendix, with exact references from their main-body consumers.

objs: lem:randomized-kernel-barycenter, lem:randomized-kernel-tv-comparison, lem:unrestricted-cell-identification, lem:cell-identification-background, lem:synthetic-randomization-kernel
bib: Rubin1976, Robins1994, Tsiatis2006, VanderVaart1998, Tsybakov2009

home_objs: lem:randomized-kernel-barycenter, lem:randomized-kernel-tv-comparison, lem:unrestricted-cell-identification, lem:cell-identification-background, lem:synthetic-randomization-kernel
## section: Appendix B. Risk certificates for the constructive estimator

Define certificate-only quantities before displaying the full deterministic envelope. Prove \cref{thm:unrestricted-uniform-mixed-count-certificate} and connect its observed-functional risk control to the causal upper result through identification. Place the rare-model certificate and upper statement as their frozen specializations, preserving both environments while using proof references to avoid duplicated derivations. Organize the argument around polynomial bias, marked-count second moments, independently estimated membership weights, branch control, and transfer from the auxiliary prefix construction to the fixed sample. Include implementation-specific details here when they serve the exact construction or its verification.

objs: thm:unrestricted-uniform-mixed-count-certificate, thm:uniform-mixed-count-certificate, thm:mixed-count-upper
bib: WuYang2019, JiaoVenkatHanWeissman2015, Wu2016, Paninski2003

home_objs: thm:unrestricted-uniform-mixed-count-certificate, thm:uniform-mixed-count-certificate, thm:mixed-count-upper
## section: Appendix C. Lower bounds with full observed memberships

Introduce the activation construction before its first use as an appendix algorithm, with the reciprocal-approximation and moment-matching lemmas providing the supporting mathematical inputs. Define the one-cell family locally and use it for the effective-sample-size component. Develop the many-cell lower comparison in the original fixed-sample randomized experiment, preserving full observations through the parameter-independent activation comparison. Give the separate large-alphabet ascertainment-deficit argument in the same appendix, organized around its observed-law comparison and target separation. Finish with proofs of the main squared-error comparisons and their category-growth and uniform-ascertainment consequences.

objs: def:activation-lower-handle, lem:reciprocal-best-approximation, lem:moment-matched-reciprocal-priors, lem:one-cell-testing-family, thm:full-experiment-lower
bib: Meinardus1967, https://doi.org/10.1007/s11075-026-02364-1, WuYang2019, Tsybakov2009, ZengBalakrishnanHanKennedy2026

home_objs: def:activation-lower-handle, lem:reciprocal-best-approximation, lem:moment-matched-reciprocal-priors, lem:one-cell-testing-family, thm:full-experiment-lower
## section: Appendix D. Interval and observational proofs

Prove the interval upper comparison from the deterministic squared-error envelope and its lower comparison from finite testing families at each fixed coverage level. Apply the joint-law total-variation result directly to randomized endpoint procedures. Then prove the observational estimator comparison using synthetic assignment and conditional averaging, identifying the precise published lower-bound input and its role in the matched observational result. Complete the fixed-arrival transfer and associated sequence-level conclusions with explicit dependence of constants on the fixed positivity parameter.

objs: none
bib: Cai2004, Tsybakov2009, ZengBalakrishnanHanKennedy2026

home_objs: none
## section: Appendix E. Verification note

End the appendix with a consolidated account of the Lean machine-checking scope attached to the frozen results. Identify which theorem and lemma conclusions are checked, which model restrictions enter as assumptions, and which published mathematical results enter through theorem-local cited dependencies. Preserve generated verification-scope disclosures and source locators, and distinguish presentation definitions from additional mathematical claims. Describe the scope from the supplied verification metadata, without introducing new verification claims or treating machine checking as a scientific contribution.

objs: none
bib: ZengBalakrishnanHanKennedy2026, Meinardus1967, https://doi.org/10.1007/s11075-026-02364-1
home_objs: none
