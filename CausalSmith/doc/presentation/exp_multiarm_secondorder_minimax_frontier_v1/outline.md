# Title
**Second-order minimax risk in multi-arm binary randomization**

**Contribution statement.** The paper characterizes the unrestricted fixed-population binary minimax game through an exact response-type orbit reduction, establishes the first-order constant and the universal \(n^{-4/3}\) second-order rate for every fixed zero-sum contrast, and constructs scale-matched finite-program procedure and prior certificates.

# Notation
\(\mathcal A_K\) | \(\mathcal A_K\) | treatment-arm set \(\{1,\ldots,K\}\) | def:labeled-schedule-game
\(K\) | \(K\) | fixed number of treatment arms | def:labeled-schedule-game
\(n\) | \(n\) | fixed number of labeled units | def:labeled-schedule-game
\(c\) | \(c\) | nonzero zero-sum treatment contrast | def:labeled-schedule-game
\(c'\) | \(c'\) | comparison nonzero zero-sum contrast | thm:contrast-risk-continuity
\(c^\dagger\) | \(c^\dagger=(1,-1/2,-1/2)\) | three-arm diagnostic contrast | def:k3-rational-lp
\(c^{(n)}\) | \(c^{(n)}\) | rational zero-sum approximating contrast | thm:real-contrast-grid-certificate-transfer
\(\mathbb Q^K\) | \(\mathbb Q^K\) | rational \(K\)-vectors | def:rational-contrast-grid-lp
\(\mathbb R^K\) | \(\mathbb R^K\) | real \(K\)-vectors | thm:contrast-risk-continuity
\(\mathcal T_K^n\) | \(\mathcal T_K^n\) | complete labeled binary response schedules | def:labeled-schedule-game
\(z\) | \(z\) | complete labeled response schedule | def:labeled-schedule-game
\(t_i\) | \(t_i\) | unit \(i\)'s binary response type | thm:exact-response-type-game
\(t_{i,a}\) | \(t_{i,a}\) | potential binary outcome under arm \(a\) | prop:k3-scalar-score-not-minimax-preserving
\(Y_i^{\mathrm{obs}}\) | \(Y_i^{\mathrm{obs}}\) | observed outcome for unit \(i\) | def:labeled-schedule-game
\(A_i\) | \(A_i\) | assigned treatment arm for unit \(i\) | def:labeled-schedule-game
\(\mathcal D\) | \(\mathcal D\) | assignment law on \(\mathcal A_K^n\) | def:labeled-schedule-game
\(\Delta(\mathcal A_K^n)\) | \(\Delta(\mathcal A_K^n)\) | probability simplex over assignments | def:labeled-schedule-game
\(\widehat\tau\) | \(\widehat\tau\) | clipped estimator of the contrast target | def:labeled-schedule-game
\(\tau_c(z)\) | \(\tau_c(z)\) | finite-population contrast target for a labeled schedule | def:labeled-schedule-game
\(\rho_n(c)\) | \(\rho_n(c)\) | unrestricted labeled-schedule minimax risk | def:labeled-schedule-game
\(R_n(\mathcal D,\widehat\tau;z)\) | \(R_n(\mathcal D,\widehat\tau;z)\) | design-based squared-error risk at schedule \(z\) | thm:first-order-saddle
\(S_c\) | \(S_c\) | active support of the contrast | def:first-order-procedure
\(L_c\) | \(L_c\) | \(\ell_1\) norm of the contrast | def:first-order-procedure
\(C_0(c)\) | \(C_0(c)\) | first-order minimax constant | thm:first-order-saddle
\(d_n(c)\) | \(d_n(c)\) | second-order improvement \(C_0(c)/n-\rho_n(c)\) | thm:embedded-two-arm-converse
\(q_a^\star\) | \(q_a^\star\) | contrast-weighted assignment probability | def:first-order-procedure
\(q^\star\) | \(q^\star\) | vector of contrast-weighted assignment probabilities | prop:k3-scalar-score-not-minimax-preserving
\(\widehat\tau_{\mathrm{cHT}}^\star\) | \(\widehat\tau_{\mathrm{cHT}}^\star\) | projected contrast-weighted Horvitz--Thompson rule | def:first-order-procedure
\(\operatorname{proj}_{[-L_c/2,L_c/2]}\) | \(\operatorname{proj}_{[-L_c/2,L_c/2]}\) | projection onto the target interval | def:first-order-procedure
\(m\) | \(m\) | response-type count vector | thm:exact-response-type-game
\(m_t\) | \(m_t\) | count of response type \(t\) | thm:exact-response-type-game
\(\mathcal M_{n,K}\) | \(\mathcal M_{n,K}\) | response-count simplex | def:finite-orbit-game
\(\tau_c(m)\) | \(\tau_c(m)\) | orbit-level contrast target | thm:exact-response-type-game
\(r\) | \(r\) | allocation-count vector | def:orbit-likelihood
\(r_a\) | \(r_a\) | count assigned to arm \(a\) | def:orbit-likelihood
\(\mathcal R_{n,K}\) | \(\mathcal R_{n,K}\) | allocation-count simplex | def:finite-orbit-game
\(x\) | \(x\) | arm-success count vector | def:orbit-likelihood
\(h\) | \(h\) | response-type-by-arm contingency table | def:orbit-likelihood
\(\mathcal H(m,r,x)\) | \(\mathcal H(m,r,x)\) | feasible contingency-table fiber | def:orbit-likelihood
\(P_m(x\mid r)\) | \(P_m(x\mid r)\) | orbit likelihood for observation \(x\) conditional on allocation \(r\) | def:orbit-likelihood
\(\pi\) | \(\pi\) | invariant design distribution over allocation counts | def:finite-orbit-game
\(\delta\) | \(\delta\) | invariant estimator on allocation and observation counts | def:finite-orbit-game
\(G_n(c)\) | \(G_n(c)\) | finite response-type orbit minimax value | def:finite-orbit-game
\(\rho_{n,2}\) | \(\rho_{n,2}\) | unrestricted two-arm minimax risk with \(c=(1,-1)\) | thm:embedded-two-arm-converse
\(p_+\) | \(p_+\) | count of \((1,0)\) effect-class units | lem:two-arm-scalar-prior-schedule-kernel
\(p_-\) | \(p_-\) | count of \((0,1)\) effect-class units | lem:two-arm-scalar-prior-schedule-kernel
\(r_0\) | \(r_0\) | count of equal-potential-outcome units | lem:two-arm-scalar-prior-schedule-kernel
\(\vartheta\) | \(\vartheta=(p_+,p_-,r_0)\) | two-arm effect-class triple | lem:two-arm-scalar-prior-schedule-kernel
\(\nu\) | \(\nu\) | probability distribution or rational prior on count vectors | lem:two-arm-scalar-prior-schedule-kernel
\(P,N,R\) | \(P,N,R\) | ordered partition blocks for the two-arm lifted prior | lem:two-arm-scalar-prior-schedule-kernel
\(H_i\) | \(H_i\) | fair bit for equal-potential-outcome units | lem:two-arm-scalar-prior-schedule-kernel
\(S_i\) | \(S_i\) | transformed two-arm observed score | lem:two-arm-scalar-prior-schedule-kernel
\(X\) | \(X\) | scalar two-arm observation \(\sum_i S_i\) | lem:two-arm-scalar-prior-schedule-kernel
\(\operatorname{Binomial}(r_0,1/2)\) | \(\operatorname{Binomial}(r_0,1/2)\) | binomial noise in the two-arm scalar experiment | lem:two-arm-scalar-prior-schedule-kernel
\(f\) | \(f\) | scalar estimator after Rao--Blackwellization | lem:two-arm-scalar-prior-schedule-kernel
\(\Theta\) | \(\Theta=(\ell,u)\) | open scalar parameter interval | lem:bayesian-information-inequality
\(\ell,u\) | \(\ell,u\) | endpoints of the scalar parameter interval | lem:bayesian-information-inequality
\(w\) | \(w\) | compactly supported prior density | lem:bayesian-information-inequality
\(J(w)\) | \(J(w)\) | prior Fisher-information functional | lem:bayesian-information-inequality
\(P_\theta\) | \(P_\theta\) | dominated observation law at parameter \(\theta\) | lem:bayesian-information-inequality
\(p_\theta(x)\) | \(p_\theta(x)\) | density of \(P_\theta\) | lem:bayesian-information-inequality
\(I(\theta)\) | \(I(\theta)\) | Fisher information of \(P_\theta\) | lem:bayesian-information-inequality
\(g(\theta,x)\) | \(g(\theta,x)\) | observation-dependent target in the information inequality | lem:bayesian-information-inequality
\(T(x)\) | \(T(x)\) | estimator in the information inequality | lem:bayesian-information-inequality
\(h_c\) | \(h_c=L_c/2\) | half-range of the contrast target | def:rational-contrast-grid-lp
\(\Gamma_M\) | \(\Gamma_M=\{-1+j/M\}\) | three-arm estimator action grid | def:k3-rational-lp
\(\Gamma_{M,c}\) | \(\Gamma_{M,c}\) | rational contrast estimator action grid | def:rational-contrast-grid-lp
\(M\) | \(M\) | grid-resolution integer | def:rational-contrast-grid-lp
\(u\) | \(u\) | epigraph objective variable in the grid-action program | def:rational-contrast-grid-lp
\(w_{r,x,g}\) | \(w_{r,x,g}\) | joint design-action LP weight | def:rational-contrast-grid-lp
\(g\) | \(g\) | grid action value | def:rational-contrast-grid-lp
\(\Lambda_{n,M}^\dagger\) | \(\Lambda_{n,M}^\dagger\) | three-arm rational grid-action LP value | def:k3-rational-lp
\(\Lambda_{n,M}(c)\) | \(\Lambda_{n,M}(c)\) | rational contrast grid-action LP value | def:rational-contrast-grid-lp
\(\rho_n^\dagger\) | \(\rho_n^\dagger\) | three-arm minimax risk for \(c^\dagger\) | prop:k3-lp-certificate
\(Z_i\) | \(Z_i\) | three-arm scalar sign score | prop:k3-scalar-score-not-minimax-preserving
\(\mu_i\) | \(\mu_i\) | conditional mean of \(Z_i\) given response type | prop:k3-scalar-score-not-minimax-preserving
\(V_3^Z\) | \(V_3^Z\) | three-observation scalar minimax value for retained signs | prop:k3-scalar-score-not-minimax-preserving
\(M_\mu\) | \(M_\mu\) | sum of feasible sign-score means | prop:k3-scalar-score-not-minimax-preserving
\(Q_\mu\) | \(Q_\mu\) | sum of squared feasible sign-score means | prop:k3-scalar-score-not-minimax-preserving
\(\lambda_c\) | \(\lambda_c\) | smallest nonzero normalized response-type contrast magnitude | thm:universal-second-order-rate
\(W_i\) | \(W_i\) | centered contrast-weighted arm score | thm:universal-second-order-rate
\(V_i\) | \(V_i\) | normalized centered contrast-weighted arm score | thm:universal-second-order-rate
\(X_n\) | \(X_n\) | sample average of normalized centered scores | thm:universal-second-order-rate
\(b_n\) | \(b_n=n^{-1/3}\) | shrinkage clipping bandwidth | thm:universal-second-order-rate
\(\varepsilon_n\) | \(\varepsilon_n\) | shrinkage amplitude | thm:universal-second-order-rate
\(g_n(x)\) | \(g_n(x)\) | clipped identity shrinkage function | thm:universal-second-order-rate
\(\widehat\tau_n^{\mathrm{sh}}\) | \(\widehat\tau_n^{\mathrm{sh}}\) | explicit clipped-shrinkage estimator | thm:universal-second-order-rate
\(A_c\) | \(A_c\) | risk-improvement constant in the central region | thm:universal-second-order-rate
\(B_c\) | \(B_c\) | risk-improvement constant in the separated region | thm:universal-second-order-rate
\(\kappa_c\) | \(\kappa_c\) | universal second-order improvement constant | thm:universal-second-order-rate
\(N_c\) | \(N_c\) | contrast-dependent sample-size threshold | thm:universal-second-order-rate
\(\mathcal D^\star\) | \(\mathcal D^\star\) | independent \(q^\star\) design | thm:universal-second-order-rate
\(a_n\) | \(a_n\) | positive normalizing sequence | thm:universal-second-order-rate
\(\beta\) | \(\beta\) | regular-variation index | thm:universal-second-order-rate
\(\pi^{n,M,c}\) | \(\pi^{n,M,c}\) | optimal rational allocation certificate | thm:rational-contrast-grid-certificate-sandwich
\(w^{n,M,c}\) | \(w^{n,M,c}\) | optimal rational joint design-action certificate | thm:rational-contrast-grid-certificate-sandwich
\(\nu_{n,M,c}\) | \(\nu_{n,M,c}\) | response-count multiplier prior from the rational dual certificate | thm:rational-contrast-grid-certificate-sandwich
\(\kappa_{r,x}^{n,M,c}(g)\) | \(\kappa_{r,x}^{n,M,c}(g)\) | conditional grid-action distribution induced by \(w^{n,M,c}\) | thm:rational-contrast-grid-certificate-sandwich
\(\delta_{n,M,c}(r,x)\) | \(\delta_{n,M,c}(r,x)\) | barycenter estimator from the rational certificate | thm:rational-contrast-grid-certificate-sandwich
\(U_{n,M}(c)\) | \(U_{n,M}(c)\) | computable upper risk certificate | thm:rational-contrast-grid-certificate-sandwich
\(D_{r,x,c}(\nu)\) | \(D_{r,x,c}(\nu)\) | prior predictive probability for \((r,x)\) | thm:rational-contrast-grid-certificate-sandwich
\(N_{r,x,c}(\nu)\) | \(N_{r,x,c}(\nu)\) | prior predictive numerator for posterior mean | thm:rational-contrast-grid-certificate-sandwich
\(B_{n,c}(\nu)\) | \(B_{n,c}(\nu)\) | computable lower Bayes-risk certificate | thm:rational-contrast-grid-certificate-sandwich
\(M_n\) | \(M_n\) | sequence of grid resolutions | thm:rational-contrast-grid-certificate-sandwich
\(\eta(c,c')\) | \(\eta(c,c')\) | half \(\ell_1\)-distance between contrasts | thm:contrast-risk-continuity
\(\eta_n\) | \(\eta_n\) | half \(\ell_1\)-distance from real contrast to rational approximant | thm:real-contrast-grid-certificate-transfer
\(B_n\) | \(B_n\) | rational lower certificate along an approximating sequence | thm:real-contrast-grid-certificate-transfer
\(U_n\) | \(U_n\) | rational upper certificate along an approximating sequence | thm:real-contrast-grid-certificate-transfer
\(R_n^-\) | \(R_n^-\) | transferred lower endpoint for a real contrast | thm:real-contrast-grid-certificate-transfer
\(R_n^+\) | \(R_n^+\) | transferred upper endpoint for a real contrast | thm:real-contrast-grid-certificate-transfer
\(\underline d_n\) | \(\underline d_n\) | lower improvement endpoint from transferred certificates | thm:real-contrast-grid-certificate-transfer
\(\overline d_n\) | \(\overline d_n\) | upper improvement endpoint from transferred certificates | thm:real-contrast-grid-certificate-transfer
\(\pi^{n,M}\) | \(\pi^{n,M}\) | three-arm optimal rational allocation certificate | thm:k3-grid-certificate-sandwich
\(w^{n,M}\) | \(w^{n,M}\) | three-arm optimal rational joint design-action certificate | thm:k3-grid-certificate-sandwich
\(\nu_{n,M}\) | \(\nu_{n,M}\) | three-arm response-count multiplier prior | thm:k3-grid-certificate-sandwich
\(\kappa_{r,x}^{n,M}(g)\) | \(\kappa_{r,x}^{n,M}(g)\) | three-arm conditional grid-action distribution | thm:k3-grid-certificate-sandwich
\(\delta_{n,M}(r,x)\) | \(\delta_{n,M}(r,x)\) | three-arm barycenter estimator | thm:k3-grid-certificate-sandwich
\(U_{n,M}\) | \(U_{n,M}\) | three-arm computable upper certificate | thm:k3-grid-certificate-sandwich
\(D_{r,x}(\nu)\) | \(D_{r,x}(\nu)\) | three-arm prior predictive probability | thm:k3-grid-certificate-sandwich
\(N_{r,x}(\nu)\) | \(N_{r,x}(\nu)\) | three-arm posterior-mean numerator | thm:k3-grid-certificate-sandwich
\(B_n(\nu)\) | \(B_n(\nu)\) | three-arm computable lower certificate | thm:k3-grid-certificate-sandwich
\(x_n(c)\) | \(x_n(c)=n^{4/3}d_n(c)\) | normalized second-order improvement | thm:second-order-rate-and-certificate-frontier

notation_gaps: \(\mathcal H(m,r,x)\)=used in \(\cref{def:orbit-likelihood}\) without a separate anchored definition of its feasibility constraints, \(\mathcal M_{n,K}\)=used in \(\cref{def:finite-orbit-game}\) before a separate anchored definition of response-count vectors, \(\mathcal R_{n,K}\)=used in \(\cref{def:finite-orbit-game}\) before a separate anchored definition of allocation-count vectors, \(C_0(c)\)=used in theorem statements without a dedicated definition environment, \(d_n(c)\)=used in theorem statements without a dedicated definition environment, \(S_c,L_c,q_a^\star\)=used in \(\cref{def:first-order-procedure}\) without a dedicated notation definition, \(R_n(\mathcal D,\widehat\tau;z)\)=used in theorem statements without a dedicated definition environment, \(c^\dagger,\rho_n^\dagger,\Gamma_M\)=used in \(\cref{def:k3-rational-lp}\) and later statements without a general notation definition environment, exact rational primal and dual certificates=used in certificate theorems without an anchored definition of certificate data and feasibility/optimality, \(\operatorname{sign}\)=standard operator but applied to \(c_{A_i}^\dagger\) without a local convention for zero-free active arms

env_overrides: def:boundary-layer-handle=remarkv, def:attainment-handle=remarkv, prop:k3-lp-certificate=propositionv, prop:k3-scalar-score-not-minimax-preserving=propositionv

# Sections
## section: Introduction
The introduction will motivate the fixed finite-population design problem, define the reader-facing question as worst-case design-based mean squared error for a prespecified zero-sum contrast, and preview the exact orbit reduction, the first-order allocation, the \(n^{-4/3}\) second-order rate, and the finite-program certificates. It will mention that proof details and the Lean machine-checking scope are consolidated in the appendix verification note.
objs: none
bib: fisher_1935, neyman_1990, rubin_1974, holland_1986, imbens_rubin_2015, athey_imbens_2017, ding_2024

home_objs: none
## section: Related work
This section positions the paper relative to randomization-based causal inference, finite-population sampling, optimum design, information inequalities, and minimax design. The closest comparisons are \(\citet{sudijono_dobriban_tchetgen_2026_sharp}\) for the sharp two-arm binary expansion, \(\citet{hull_2026_bounded}\) for bounded two-arm potential outcomes, \(\citet{bai_2023_why}\), \(\citet{kallus_2018}\), and \(\citet{kallus_2020_optimality}\) for minimax randomization-design results, and \(\citet{aronow_lopatto_2026_minimax_unbiased}\) for finite-population minimax sampling under unbiasedness.
objs: none
bib: fisher_1935, neyman_1990, rubin_1974, rubin_1978, holland_1986, imbens_rubin_2015, imbens_wooldridge_2009, athey_imbens_2017, ding_2024, bai_2024, freedman_2008, lin_2013, dasgupta_2015, morgan_2012, li_2018, horvitz_1952, hansen_1953, sarndal_1992, gabler_1990, aronow_lopatto_2026_minimax_unbiased, wald_1950, lecam_1986, van_trees_1968, gill_1995, rao_1945, ibragimov_1981, levit_1981_second_order, smith_1918, kiefer_1959, kiefer_1974, atkinson_2007, kallus_2018, kallus_2020_optimality, harshaw_2024, basse_2023, kandiros_2026, kandiros_2024, eckles_2014, derezinski_2019, hu_2024, bickel_1981, feldman_1991, johnstone_1992, pinsker_1980, sudijono_dobriban_tchetgen_2026_sharp, hull_2026_bounded, rosenman_hunter_2026_shrinkage

home_objs: none
## section: Setup and the finite orbit game
This section introduces the labeled fixed-schedule minimax game, the response-type orbit likelihood, and the finite orbit game. It then states the exact equality between the unrestricted labeled game and the finite orbit game, including the invariant design representation, finite saddle-point existence, and the treatment-domain extension from two binary arms to every fixed \(K\ge3\).
objs: synth_1, synth_2, def:labeled-schedule-game, synth_4, synth_19, def:orbit-likelihood, def:finite-orbit-game, synth_3, synth_10, synth_20, synth_15, synth_14, thm:exact-response-type-game, synth_9, thm:multiarm-strict-extension
bib: neyman_1990, rubin_1974, holland_1986, imbens_rubin_2015, sudijono_dobriban_tchetgen_2026_sharp, hull_2026_bounded

home_objs: def:labeled-schedule-game, def:orbit-likelihood, def:finite-orbit-game, thm:exact-response-type-game, thm:multiarm-strict-extension
## section: First-order risk and the second-order rate
This section presents the contrast-weighted independent design, the projected contrast-weighted rule, the first-order constant, the embedded two-arm converse, and the explicit clipped-shrinkage construction that attains a positive second-order improvement. The section’s main message is the internally established \(n^{-4/3}\) order for every fixed nonzero zero-sum contrast.
objs: def:first-order-procedure, synth_5, thm:first-order-saddle, thm:embedded-two-arm-converse, synth_16, synth_6, thm:universal-second-order-rate, thm:coarse-two-arm-minimax-lower
bib: sudijono_dobriban_tchetgen_2026_sharp, van_trees_1968, gill_1995, rao_1945, ibragimov_1981, pinsker_1980, levit_1981_second_order, levit_1986_schrodinger

home_objs: def:first-order-procedure, thm:first-order-saddle, thm:embedded-two-arm-converse, thm:universal-second-order-rate, thm:coarse-two-arm-minimax-lower
## section: Finite-program certificates for rational and real contrasts
This section develops the rational grid-action linear programs and the resulting computable upper and lower certificates. It first gives the three-arm diagnostic program, then the general rational-contrast certificate sandwich, and finally the continuity transfer that gives matched brackets for every real contrast.
objs: def:k3-rational-lp, def:rational-contrast-grid-lp, synth_8, prop:k3-lp-certificate, synth_7, thm:rational-contrast-grid-certificate-sandwich, thm:contrast-risk-continuity, synth_12, thm:real-contrast-grid-certificate-transfer, thm:k3-grid-certificate-sandwich
bib: wald_1950, lecam_1986, kiefer_1959, kiefer_1974, atkinson_2007

home_objs: def:k3-rational-lp, def:rational-contrast-grid-lp, prop:k3-lp-certificate, thm:rational-contrast-grid-certificate-sandwich, thm:contrast-risk-continuity, thm:real-contrast-grid-certificate-transfer, thm:k3-grid-certificate-sandwich
## section: Three-arm diagnostics and support-specific conclusions
This section records the three-arm scalar-score diagnostic and the support-specific consequences of the general theory. It explains how exact value and saddle transfer work for two active arms, how the same rate and certificate conclusions apply for larger active supports, and how the finite three-arm calculations serve as within-population certificate checks.
objs: prop:k3-scalar-score-not-minimax-preserving, synth_18, synth_11, thm:second-order-rate-and-certificate-frontier, synth_17, thm:attainment-and-k3-certified-converse
bib: sudijono_dobriban_tchetgen_2026_sharp, hull_2026_bounded, hammer_et_al_1996_actg175

home_objs: prop:k3-scalar-score-not-minimax-preserving, thm:second-order-rate-and-certificate-frontier, thm:attainment-and-k3-certified-converse
## section: Discussion, limitations, and future work
This section interprets the established results as design criteria for prespecified finite-population contrasts, including an ACTG 175-style four-regimen binary-endpoint use case. A clearly labelled limitations and future-work subsection will place the boundary-layer and attainment handles as open analytic programs concerning sharp constants, subsequential limits, optimizer/prior behavior, and possible limiting equations.
objs: def:boundary-layer-handle, def:attainment-handle
bib: hammer_et_al_1996_actg175, levit_1986_schrodinger, johnstone_1992, rosenman_hunter_2026_shrinkage

home_objs: def:boundary-layer-handle, def:attainment-handle
## section: Appendix: Proofs and auxiliary lemmas
The appendix contains the proofs of the orbit reduction, first-order bounds, shrinkage analysis, sign-group embedding, rational LP certificate construction, continuity transfer, and the two-arm Bayesian-information lower bound. It also houses the auxiliary scalar-prior kernel and Bayesian-information lemmas before their proof uses.
objs: synth_13, lem:two-arm-scalar-prior-schedule-kernel, lem:bayesian-information-inequality
bib: van_trees_1968, gill_1995, rao_1945, sudijono_dobriban_tchetgen_2026_sharp

home_objs: lem:two-arm-scalar-prior-schedule-kernel, lem:bayesian-information-inequality
## section: Appendix: Verification note
This final appendix note consolidates the Lean checking scope: the finite-design substrate, orbit-game constructions, rational LP bridge, first-order and second-order inequalities, certificate sandwiches, continuity transfer, and auxiliary information arguments are machine-checked as formal inputs to the manuscript, while cited literature supplies only the bibliographic comparisons named in the related-work and proof discussions.
objs: none
bib: sudijono_dobriban_tchetgen_2026_sharp, hull_2026_bounded
home_objs: none
