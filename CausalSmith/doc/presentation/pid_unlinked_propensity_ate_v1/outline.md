# Title

**Assignment probabilities without row-level links: Identification, label design, and inference in randomized trials**

**Contribution statement.** For randomized trials with bounded outcomes and fixed overlap, the paper characterizes sharp average treatment effect ambiguity under deterministic score labels, establishes finite-label design and honest-length rates under a positive density lower bound, derives a high-resolution design constant for continuous positive score densities, and establishes the minimax excess-length order when the score law is learned from an independent log.

# Notation

The table plans where each named object in the frozen layer is introduced. Symbols defined locally inside a theorem or lemma are listed under `notation_gaps` where they lack an anchored definition environment.

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(\mathfrak P(H,g)\) | \(\mathfrak P(H,g)\) | causal laws with score law \(H\), score-based assignment, consistency, and release \(g\) | def:causal-law-class |
| \(\mathfrak M(H,g,P_{\mathrm{rel}})\) | \(\mathfrak M(H,g,P_{\mathrm{rel}})\) | causal laws compatible with a specified released law | def:compatible-law-class |
| \(p_1(e)\) | \(p_1(e)\) | treatment probability at score \(e\) | def:arm-cell-primitives |
| \(p_0(e)\) | \(p_0(e)\) | control probability at score \(e\) | def:arm-cell-primitives |
| \(C_r\) | \(C_r\) | score cell carrying label \(r\) | def:arm-cell-primitives |
| \(q_{ar}\) | \(q_{ar}\) | probability of arm \(a\) and label \(r\) | def:arm-cell-primitives |
| \(F_{ar}\) | \(F_{ar}\) | observed outcome law in a positive-mass arm-label cell | def:arm-cell-primitives |
| \(G_{ar}\) | \(G_{ar}\) | score law conditional on arm \(a\) and label \(r\) | def:arm-cell-primitives |
| \(E_{ar}\) | \(E_{ar}\) | score drawn from \(G_{ar}\) | def:arm-cell-primitives |
| \(W_{ar}\) | \(W_{ar}\) | reciprocal arm probability evaluated at \(E_{ar}\) | def:arm-cell-primitives |
| \(\underline\mu_a\) | \(\underline\mu_a\) | lower attainable mean of potential outcome \(Y_a\) | def:mean-endpoints |
| \(\overline\mu_a\) | \(\overline\mu_a\) | upper attainable mean of potential outcome \(Y_a\) | def:mean-endpoints |
| \(I(P_{\mathrm{rel}};H,g)\) | \(I(P_{\mathrm{rel}};H,g)\) | sharp average treatment effect interval for a fixed released law | def:sharp-ate-set |
| \(D_H(g)\) | \(D_H(g)\) | largest attainable interval width under release \(g\) | def:worst-case-ambiguity |
| \(\mathcal G_K\) | \(\mathcal G_K\) | measurable releases with \(K\) labels | def:k-label-releases |
| \(\Delta_K(H)\) | \(\Delta_K(H)\) | smallest worst-case ambiguity among \(K\)-label releases | def:optimal-k-ambiguity |
| \(\mathcal H^{\mathrm{lb}}_{\varepsilon,m_f}\) | \(\mathcal H^{\mathrm{lb}}_{\varepsilon,m_f}\) | score laws with density at least \(m_f\) on \(\mathcal E\) | def:score-lower-density-class |
| \(\mathcal J_{n,K,\alpha}(H)\) | \(\mathcal J_{n,K,\alpha}(H)\) | uniformly honest release–interval pairs | def:honest-procedures |
| \(\mathcal L^\star_{n,K,\alpha}(H)\) | \(\mathcal L^\star_{n,K,\alpha}(H)\) | minimax expected interval length with known \(H\) | def:minimax-honest-length |
| \(\mathfrak X(g)\) | \(\mathfrak X(g)\) | causal-law and score-law pairs under release \(g\) | def:external-law-class |
| \(\mathbb Q_{P,H}^{n,m}\) | \(\mathbb Q_{P,H}^{n,m}\) | joint law of independent trial rows and score-log draws | def:external-experiment |
| \(\mathcal J^{\mathrm{ext}}_{n,m,\alpha}(g)\) | \(\mathcal J^{\mathrm{ext}}_{n,m,\alpha}(g)\) | uniformly honest intervals in the external-log experiment | def:external-honest-procedures |
| \(\mathcal R^{\star}_{n,m,\alpha}(g)\) | \(\mathcal R^{\star}_{n,m,\alpha}(g)\) | minimax expected excess interval length | def:external-excess-risk |
| \(b_{n,m}\) | \(b_{n,m}\) | reciprocal sum of trial and log square-root sampling scales | def:external-normalized-risk |
| \(T_{n,m,\alpha}(g)\) | \(T_{n,m,\alpha}(g)\) | normalized external-log minimax excess risk | def:external-normalized-risk |
| \(\widehat\lambda_{ar}(B)\) | \(\widehat\lambda_{ar}(B)\) | empirical trial measure for an arm-label cell | def:external-projection-handle |
| \(\widehat\sigma_{ar}(B)\) | \(\widehat\sigma_{ar}(B)\) | weighted empirical score-log measure for an arm-label cell | def:external-projection-handle |
| \(r_n\) | \(r_n\) | trial empirical-ball radius | def:external-projection-handle |
| \(r_m\) | \(r_m\) | score-log empirical-ball radius | def:external-projection-handle |
| \(x(q)\) | \(x(q)\) | rational support code clamped to the outcome interval | def:external-projection-handle |
| \(e_\varepsilon(q)\) | \(e_\varepsilon(q)\) | clamped rational support code mapped to the score interval | def:external-projection-handle |
| \(\operatorname{ofReal}(w)\) | \(\operatorname{ofReal}(w)\) | nonnegative weight represented by a rational code | def:external-projection-handle |
| \(\nu_Y(L)\) | \(\nu_Y(L)\) | finitely supported outcome measure encoded by \(L\) | def:external-projection-handle |
| \(\nu_E(L)\) | \(\nu_E(L)\) | finitely supported score measure encoded by \(L\) | def:external-projection-handle |
| \(\mathcal D_{\varepsilon,J}\) | \(\mathcal D_{\varepsilon,J}\) | compatible rational-sieve arrays of outcome and score measures | def:external-projection-handle |
| \(\mathcal B_{n,m}\) | \(\mathcal B_{n,m}\) | sieve arrays inside both empirical balls | def:external-projection-handle |
| \(I(b)\) | \(I(b)\) | quantile-transport interval computed for a candidate array | def:external-projection-handle |
| \(J_{n,m}\) | \(J_{n,m}\) | clipped closed convex hull of candidate intervals | def:external-projection-handle |
| \(C_{n,m}\) | \(C_{n,m}\) | totalized external-log confidence interval | def:external-projection-handle |

notation_gaps: \(\mathcal E\)=the score interval has no anchored definition; \(\mathcal A\), \(\mathcal R_J\)=the arm and label sets have no anchored definition; \(E,Y_0,Y_1,A,Y,R\)=the causal variables have no anchored definition; \(P,H,g,P_{\mathrm{rel}}\)=the causal law, score law, release rule, and released law have no anchored definition as primitives; \(\theta(P)\)=the average treatment effect target has no anchored definition; \(Q_{F_{ar}}(u),Q_{W_{ar}}(u)\)=the generalized quantile operator has no anchored definition; \(d_{[0,1]},d_{\mathcal E}\)=the finite-measure distance has no defining formula; \(\operatorname{ProjectionCompatible}\)=the compatibility predicate has no defining formula; \(\mathsf H_{\mathrm{ext}}\)=the external-projection handle is named without an anchored definition of that name; \(\ell,\widehat T_n,B_K,R_{n,K},\operatorname{clampATE}(x),C_n\)=quantities introduced locally in theorem statements rather than anchored definitions; \(L_\alpha,S_g,c_{\mathrm{tr}}(\alpha),c_{\mathrm{log}}(g,\alpha),C_{\varepsilon,J,\alpha,g}\)=quantities introduced locally in the external-score theorem or auxiliary lemma; \(V_k,\beta_s(x,z_{js}),w(x)\)=quantities introduced locally in the auxiliary quantization lemma.

# Sections

## section: Introduction

Plan the abstract and introduction after the results sections. Lead with the observation scheme: the score distribution is available, while each treatment–outcome row carries a deterministic score label. State the average treatment effect question, then preview the sharp ambiguity formula, label-design results, known-score-law inference, and the independent score-log extension with their respective conditions. Include one factual sentence directing readers to the appendix verification note.

objs: none
bib: Rubin1974, RosenbaumRubin1983, HorvitzThompson1952

home_objs: none
## section: Related work

Position the fixed-released-law interval as the bounded-outcome, overlap specialization of \citet[Theorem 3.2 and eq. (3.1)]{FanShermanShum2014}. Compare the paper’s optimization across compatible released trial laws with data-combination and conditional-transport results. Compare deterministic loss of row-level score linkage with statistical matching, record-linkage error, and subclassification with linked person-level information. Locate the two honest-length questions within partial-identification inference.

objs: none
bib: Manski1990, HorowitzManski1995, Tamer2010, CambanisSimonsStout1976, DOrazio2006, Conti2017, FanShermanShum2014, Torgovitsky2019, FanParkPassShi2025, MarellaPfeffermann2019, Marella2023, Wortman2018, Komarova2018, Cochran1968, RosenbaumRubin1984, WangZhangRichardsonZhou2021, Wang2026, KalavasisMehrotraZampetakis2024, LeeWeidner2026, ImbensManski2004, Stoye2009, ChernozhukovHongTamer2007, KaidoMolinariStoye2019, FangSantos2019

home_objs: none
## section: Trial setup and the sharp identified interval

Define the bounded-outcome randomized population, fixed overlap, population score law, deterministic release, compatible released laws, and average treatment effect. Define generalized quantiles before the arm-label endpoint formulas that use them. Present the observable compatibility criterion and identify the fixed-law interval as the credited published baseline.

objs: ass:overlap, ass:score-marginal, ass:randomized-assignment, ass:consistency, ass:deterministic-release, ass:released-law, def:causal-law-class, def:compatible-law-class, synth_3, synth_2, def:arm-cell-primitives, def:mean-endpoints, def:sharp-ate-set, synth_4, prop:compatibility
bib: FanShermanShum2014

home_objs: ass:overlap, ass:score-marginal, ass:randomized-assignment, ass:consistency, ass:deterministic-release, ass:released-law, def:causal-law-class, def:compatible-law-class, def:arm-cell-primitives, def:mean-endpoints, def:sharp-ate-set, prop:compatibility
## section: Information retained by a score label

Define worst-case interval width and give its paired reciprocal-score absolute-deviation representation. Explain the common released outcome law that attains this width and the universal point-identification criterion: a label determines the score almost surely. State the scope for atomic score laws and disconnected cells alongside these results.

objs: def:worst-case-ambiguity, thm:all-label-ambiguity, thm:universal-point-identification
bib: none

home_objs: def:worst-case-ambiguity, thm:all-label-ambiguity, thm:universal-point-identification
## section: Designing a finite-label release

Define the release budget, optimal ambiguity, and lower-density class. Establish the uniform inverse-budget bounds over that class and record that equal-width labels give the upper bound for every score law. Present the exact high-resolution constant under a continuous strictly positive density and explain the ordered interval allocation implied by its integrand.

objs: ass:density-lower, def:k-label-releases, def:optimal-k-ambiguity, def:score-lower-density-class, thm:k-label-rate, thm:sharp-high-resolution-constant
bib: GrayNeuhoff1998, GrafLuschgy2000, LemaireMontesPages2020

home_objs: ass:density-lower, def:k-label-releases, def:optimal-k-ambiguity, def:score-lower-density-class, thm:k-label-rate, thm:sharp-high-resolution-constant
## section: Honest intervals with a known score law

Specify independent released trial rows and uniform coverage over causal laws and release choices. Present the minimax length rate over the positive lower-density class and the equal-width midpoint-weighted interval that attains its upper order. Interpret the balance between the inverse label budget and inverse square-root trial size at \(K\) of order \(\sqrt n\).

objs: ass:iid-trial-sampling, synth_1, def:honest-procedures, def:minimax-honest-length, thm:minimax-honest-length
bib: ImbensManski2004, Stoye2009

home_objs: ass:iid-trial-sampling, def:honest-procedures, def:minimax-honest-length, thm:minimax-honest-length
## section: Inference with an independent score log

Specify the external-log experiment and its excess-length criterion for a fixed finite-label release. Present the canonical rational-sieve projection as a mathematical confidence construction used to establish attainability, followed by the uniform two-sample rate theorem and its separate trial and score-log lower certificates. Explain that computation would require a specified finite approximation, and explain how both sample sizes enter the rate across the stated class, including atomic laws and rank contacts.

objs: ass:external-log-iid, ass:external-log-independent, def:external-law-class, def:external-experiment, def:external-honest-procedures, def:external-excess-risk, def:external-normalized-risk, synth_5, def:external-projection-handle, thm:external-score-root-order
bib: FanPark2012, FangSantos2019

home_objs: ass:external-log-iid, ass:external-log-independent, def:external-law-class, def:external-experiment, def:external-honest-procedures, def:external-excess-risk, def:external-normalized-risk, def:external-projection-handle, thm:external-score-root-order
## section: Discussion and open questions

Interpret the information value of linked labels and the high-resolution allocation rule within the paper’s established domains. In a clearly labelled open-questions subsection, place the sharp normalized external-log limit question, including possible regular subclasses and their honesty criterion, as a future direction.

objs: oeq:external-score-projection
bib: none

home_objs: oeq:external-score-projection
## section: Appendix: proofs and verification scope

Give the fixed-law transfer and compatibility proofs before the ambiguity arguments. Describe the high-resolution proof route in prose before the auxiliary quantization result, and place the two-source lower bound with the external-log proof. End with a brief verification note distinguishing prior-art attribution from the machine-checked formal proof.

objs: lem:released-arm-cell-masses, lem:fixed-released-law-baseline, lem:paired-high-resolution-quantization, lem:external-two-source-lower-certificate
bib: FanShermanShum2014

env_overrides: oeq:external-score-projection=remarkv
home_objs: lem:released-arm-cell-masses, lem:fixed-released-law-baseline, lem:paired-high-resolution-quantization, lem:external-two-source-lower-certificate
