# Title
**Outcome annotation and minimax risk for discrete average treatment effects**

**Contribution statement.** The paper establishes the finite-sample minimax mean-squared error for average treatment effect estimation in a finite-alphabet observational model with \(n\) outcome-labeled records and \(m\) additional treatment-covariate records, giving the sharp rate \(R_\epsilon(n,m,d)\asymp_\epsilon \min\{1,n^{-1}+d^2/((n+m)^2\log^2(en))\}\), an explicit estimator attaining it, a common-marginal converse, and the known-\(P_{XA}\) limiting benchmark.

env_overrides: def:mixed-estimator-handle=algorithmv

# Notation
notation_gaps: \(\mathcal T_{n,m,d}\)=estimator class used in `def:minimax-risk` and later statements but not anchored as its own definition, \(\mathcal T^{\mathrm{known}}_{n,d}\)=known-marginal estimator class used in `def:known-marginal-risk` but not anchored as its own definition, \(p_x,\mu_{ax},e_x,s_{ax},q_{ax}\)=cell-level primitives used throughout but not anchored as their own definition, \(h_n\)=overloaded between the binary length in `def:mixed-estimator-handle` and the local testing separation in `def:common-marginal-prior-handle`, \(\operatorname{clip}_{[-1,1]}\)=clipping operator used in `def:mixed-estimator-handle` but not anchored as its own definition, \(\|\cdot\|_1\)=coefficient norm introduced inside `lem:explicit-chebyshev-calibration` rather than a separate definition

<note symbol> | <paper notation> | <defining property in one phrase> | <home>
\(\epsilon\) | \(\epsilon\) | overlap constant with \(0<\epsilon<1/2\) | def:model-class
\(d\) | \(d\) | size of the known finite covariate alphabet with \(d\ge2\) | def:model-class
\([d]\) | \([d]\) | finite covariate alphabet \(\{1,\ldots,d\}\) | def:model-class
\(P\) | \(P\) | observed-data law on \([d]\times\{0,1\}^2\) | def:model-class
\(\mathcal M_{d,\epsilon}\) | \(\mathcal M_{d,\epsilon}\) | laws satisfying occupied-cell overlap at level \(\epsilon\) | def:model-class
\(e_x\) | \(e_x\) | treatment propensity in occupied covariate cell \(x\) | ass:overlap
\(p_x\) | \(p_x\) | covariate cell mass at \(x\) | ass:overlap
\(\tau(P)\) | \(\tau(P)\) | average treatment effect functional \(\sum_xp_x(\mu_{1x}-\mu_{0x})\) | def:ate-functional
\(\mu_{1x}\) | \(\mu_{1x}\) | treated outcome regression in cell \(x\) | def:ate-functional
\(\mu_{0x}\) | \(\mu_{0x}\) | control outcome regression in cell \(x\) | def:ate-functional
\(\mathcal L_n\) | \(\mathcal L_n\) | sample of \(n\) complete outcome-labeled records | ass:labeled-iid
\(P^{\otimes n}\) | \(P^{\otimes n}\) | product law for the labeled sample | ass:labeled-iid
\(\mathcal U_m\) | \(\mathcal U_m\) | sample of \(m\) outcome-unlabeled treatment-covariate records | ass:auxiliary-iid
\(P_{XA}\) | \(P_{XA}\) | treatment-covariate marginal law induced by \(P\) | ass:auxiliary-iid
\(P_{XA}^{\otimes m}\) | \(P_{XA}^{\otimes m}\) | product law for the auxiliary sample | ass:auxiliary-iid
\(Y\) | \(Y\) | observed binary outcome | ass:consistency
\(A\) | \(A\) | binary treatment indicator | ass:consistency
\(Y(0)\) | \(Y(0)\) | potential outcome under control | ass:consistency
\(Y(1)\) | \(Y(1)\) | potential outcome under treatment | ass:consistency
\(X\) | \(X\) | finite covariate | ass:conditional-exchangeability
\(\mathcal E_{n,m,d,\epsilon}\) | \(\mathcal E_{n,m,d,\epsilon}\) | annotation experiment with labeled and auxiliary product samples | def:annotation-experiment
\(n\) | \(n\) | number of complete outcome-labeled records | def:annotation-experiment
\(m\) | \(m\) | number of additional outcome-unlabeled treatment-covariate records | def:annotation-experiment
\(R_\epsilon(n,m,d)\) | \(R_\epsilon(n,m,d)\) | minimax mean-squared error over \(\mathcal M_{d,\epsilon}\) | def:minimax-risk
\(\mathcal T_{n,m,d}\) | \(\mathcal T_{n,m,d}\) | estimators measurable with respect to \((\mathcal L_n,\mathcal U_m)\) | def:minimax-risk
\(T\) | \(T\) | generic estimator in the annotation experiment | def:minimax-risk
\(N\) | \(N=n+m\) | total treatment-covariate information size | def:frontier-rate-handle
\(\ell_n\) | \(\ell_n=\log(en)\) | logarithmic factor based on labeled sample size | def:frontier-rate-handle
\(r_\epsilon(n,m,d)\) | \(r_\epsilon(n,m,d)\) | annotation rate \(\min\{1,n^{-1}+d^2/(N^2\ell_n^2)\}\) | def:frontier-rate-handle
\(A_\star\) | \(A_\star=7056\) | explicit Chebyshev-factorial calibration constant | def:mixed-estimator-handle
\(c^\circ\) | \(c^\circ=1/256\) | explicit logarithmic calibration constant | def:mixed-estimator-handle
\(j_\epsilon\) | \(j_\epsilon\) | least integer \(j\ge1\) with \(2^{-j}\le\epsilon\) | def:mixed-estimator-handle
\(\bar\epsilon\) | \(\bar\epsilon=2^{-j_\epsilon}\) | dyadic lower certificate for overlap | def:mixed-estimator-handle
\(H_\epsilon\) | \(H_\epsilon\) | least positive integer satisfying the calibration inequalities | def:mixed-estimator-handle
\(M_0\) | \(M_0=\lfloor n/3\rfloor\) | size of the labeled outcome block | def:mixed-estimator-handle
\(n_p\) | \(n_p=\lfloor(n-M_0)/2\rfloor\) | labeled contribution to the pilot pool | def:mixed-estimator-handle
\(n_f\) | \(n_f=n-M_0-n_p\) | labeled contribution to the factorial pool | def:mixed-estimator-handle
\(m_p\) | \(m_p=\lfloor m/2\rfloor\) | auxiliary contribution to the pilot pool | def:mixed-estimator-handle
\(m_f\) | \(m_f=m-m_p\) | auxiliary contribution to the factorial pool | def:mixed-estimator-handle
\(M_p\) | \(M_p=n_p+m_p\) | size of the pilot pool | def:mixed-estimator-handle
\(M_f\) | \(M_f=n_f+m_f\) | size of the factorial pool | def:mixed-estimator-handle
\(u\) | \(u=M_0/8\) | outcome-block Poisson prefix intensity | def:mixed-estimator-handle
\(t_p\) | \(t_p=M_p/8\) | pilot-pool Poisson prefix intensity | def:mixed-estimator-handle
\(t\) | \(t=M_f/8\) | factorial-pool Poisson prefix intensity | def:mixed-estimator-handle
\(h_n\) | \(h_n=1+\lceil\log_2 n\rceil\) | binary-length calibration quantity | def:mixed-estimator-handle
\(L\) | \(L=\max\{2,\lfloor c^\circ h_n\rfloor\}\) | polynomial degree used by the hybrid estimator | def:mixed-estimator-handle
\(B\) | \(B=H_\epsilon L/\min(t_p,t)\) | light-cell scale for the hybrid estimator | def:mixed-estimator-handle
\(k_0\) | \(k_0=\lfloor t_pB/4\rfloor\) | pilot-count threshold for light cells | def:mixed-estimator-handle
\(\mathsf C_\epsilon(n,m)\) | \(\mathsf C_\epsilon(n,m)\) | finite decidable calibration predicate | def:mixed-estimator-handle
\(\widehat\tau^{\mathrm{mix}}_{n,m,d}\) | \(\widehat\tau^{\mathrm{mix}}_{n,m,d}\) | total computable hybrid estimator | def:mixed-estimator-handle
\(D_0\) | \(D_0\sim\operatorname{Poi}(u)\) | randomized outcome prefix length | def:mixed-estimator-handle
\(D_p\) | \(D_p\sim\operatorname{Poi}(t_p)\) | randomized pilot prefix length | def:mixed-estimator-handle
\(D_f\) | \(D_f\sim\operatorname{Poi}(t)\) | randomized factorial prefix length | def:mixed-estimator-handle
\(J_x\) | \(J_x\) | pilot count in covariate cell \(x\) | def:mixed-estimator-handle
\(T_L\) | \(T_L\) | Chebyshev polynomial of degree \(L\) | def:mixed-estimator-handle
\(H_L(z)\) | \(H_L(z)=(1-T_L(1-2z))/(2L^2)\) | polynomial approximation component | def:mixed-estimator-handle
\(E_L(z)\) | \(E_L(z)=H_L(z)/z\) | polynomial continuation component | def:mixed-estimator-handle
\(G_L(z)\) | \(G_L(z)=\{1-E_L(z)\}/z\) | polynomial correction component | def:mixed-estimator-handle
\(W_{a,L}(s_0,s_1)\) | \(W_{a,L}(s_0,s_1)=((s_0+s_1)/B)G_L(s_a/B)\) | light-cell weight polynomial | def:mixed-estimator-handle
\(c_{a,r_0,r_1}\) | \(c_{a,r_0,r_1}\) | coefficient of \(s_0^{r_0}s_1^{r_1}\) in \(W_{a,L}\) | def:mixed-estimator-handle
\(K_{ax}\) | \(K_{ax}\) | factorial-pool count for treatment-covariate cell \((a,x)\) | def:mixed-estimator-handle
\(S_{ax}\) | \(S_{ax}\) | outcome-block success count for treatment-covariate cell \((a,x)\) | def:mixed-estimator-handle
\((k)_r\) | \((k)_r\) | falling factorial | def:mixed-estimator-handle
\(\widehat W_{a,L,x}\) | \(\widehat W_{a,L,x}\) | factorial lift of the light-cell polynomial weight | def:mixed-estimator-handle
\(\widehat W^H_{a,x}\) | \(\widehat W^H_{a,x}\) | inverse-count heavy-cell weight | def:mixed-estimator-handle
\(Z_x\) | \(Z_x\) | cell contribution in the hybrid statistic | def:mixed-estimator-handle
\(\Pi_0,\Pi_1\) | \(\Pi_0,\Pi_1\) | regime-dependent fuzzy hypotheses with common random \(P_{XA}\) table | def:common-marginal-prior-handle
\(h_n\) | \(h_n=c_\epsilon/\sqrt n\le1/4\) | local separation in the point-mass testing regime | def:common-marginal-prior-handle
\(\kappa\) | \(\kappa=(1-2\epsilon)/\epsilon\) | interval-shape constant in the lower-bound construction | def:common-marginal-prior-handle
\(a\) | \(a=\gamma_\epsilon B/L^2\) | lower-bound smoothing scale | def:common-marginal-prior-handle
\(I\) | \(I=[a/\kappa,B]\) | interval supporting the signed measure | def:common-marginal-prior-handle
\(\sigma\) | \(\sigma\) | finite signed measure annihilating monomials through degree \(L\) | def:common-marginal-prior-handle
\(h\) | \(h=d\sigma/d|\sigma|\) | signed density used to perturb outcome marks | def:common-marginal-prior-handle
\(\nu\) | \(\nu\) | probability law for raw rare-cell masses with an atom at zero | def:common-marginal-prior-handle
\(k\) | \(k=\min\{d-1,\lfloor c_\epsilon^\circ NL\rfloor\}\) | number of rare cells in the lower-bound construction | def:common-marginal-prior-handle
\(p_i\) | \(p_i\) | raw mass draw for rare cell \(i\) | def:common-marginal-prior-handle
\(s_i\) | \(s_i=\epsilon(p_i+a)\) | treated-arm raw mass assigned to rare cell \(i\) | def:common-marginal-prior-handle
\(p_*\) | \(p_*=1-kE_\nu[p]\) | reservoir raw mass | def:common-marginal-prior-handle
\(S\) | \(S=p_*+\sum_{i=1}^kp_i\) | normalizing raw total mass | def:common-marginal-prior-handle
\(\Pi_0^{\mathrm{small}},\Pi_1^{\mathrm{small}}\) | \(\Pi_0^{\mathrm{small}},\Pi_1^{\mathrm{small}}\) | two-point illustrative hypotheses at \(d=2,\epsilon=1/4\) | def:finite-small-instance
\(\mathfrak C_{\mathrm{small}}\) | \(\mathfrak C_{\mathrm{small}}\) | finite calculation for the illustrative two-cell instance | def:finite-small-instance
\(\mathcal E^{\mathrm{known}}_{n,d,\epsilon}\) | \(\mathcal E^{\mathrm{known}}_{n,d,\epsilon}\) | benchmark experiment observing the exact \(P_{XA}\) table | def:known-marginal-experiment
\(R_\epsilon^{\mathrm{known}}(n,d)\) | \(R_\epsilon^{\mathrm{known}}(n,d)\) | minimax risk with known treatment-covariate marginal | def:known-marginal-risk
\(\mathcal T^{\mathrm{known}}_{n,d}\) | \(\mathcal T^{\mathrm{known}}_{n,d}\) | estimators measurable with respect to \((\mathcal L_n,P_{XA})\) | def:known-marginal-risk
\(Z^H\) | \(Z^H\) | all-heavy inverse-count Poisson statistic | lem:poisson-inverse-count-risk
\(q_{ax}\) | \(q_{ax}\) | outcome-marked mass for treatment-covariate cell \((a,x)\) | lem:poisson-inverse-count-risk
\(s_{ax}\) | \(s_{ax}\) | treatment-covariate cell mass for \((a,x)\) | lem:poisson-inverse-count-risk
\(Z^{\mathrm{mix}}\) | \(Z^{\mathrm{mix}}\) | clipped hybrid statistic in the independent Poisson experiment | lem:poisson-hybrid-risk
\(\gamma_\epsilon\) | \(\gamma_\epsilon\) | positive approximation-duality constant depending on \(\epsilon\) | lem:finite-alternation-duality
\(b_\epsilon\) | \(b_\epsilon\) | positive lower-bound bandwidth constant depending on \(\epsilon\) | lem:common-marginal-poisson-prior
\(\rho_\epsilon\) | \(\rho_\epsilon\) | exponential likelihood-decay constant in the common-marginal prior | lem:common-marginal-poisson-prior
\(C_{\mathrm{fixed}}\) | \(C_{\mathrm{fixed}}\) | fixed numerical intensity-transfer constant | lem:fixed-sample-common-marginal-transfer
\(c_{\mathrm{risk}}\) | \(c_{\mathrm{risk}}\) | fixed numerical risk-transfer constant | lem:fixed-sample-common-marginal-transfer
\(c_{\epsilon,C_\epsilon}\) | \(c_{\epsilon,C_\epsilon}\) | concentration threshold for the fixed-sample lower-bound transfer | lem:fixed-sample-common-marginal-transfer
\(\Delta\) | \(\Delta\) | actual raw-center separation of a lower-bound recipe | lem:fixed-sample-common-marginal-transfer
\(T_j\) | \(T_j\) | Chebyshev polynomial indexed by \(j\) | lem:explicit-chebyshev-calibration
\(Q_j(z)\) | \(Q_j(z)=T_j(1-2z)\) | shifted Chebyshev polynomial | lem:explicit-chebyshev-calibration
\(\|\cdot\|_1\) | \(\|\cdot\|_1\) | coefficient \(\ell^1\)-norm | lem:explicit-chebyshev-calibration

# Sections
## section: Introduction
The introduction will motivate random outcome annotation as a finite-sample allocation problem for discrete covariate adjustment: outcomes are observed on \(n\) records, while treatment and covariates are observed on \(n+m\) records. It will state the main rate, explain the two terms as the label-gated outcome floor and the pooled treatment-covariate approximation term, and give a short factual pointer to the appendix verification note. The introduction will use words before symbols where possible and attach a plain-word gloss to the first uses of \(R_\epsilon(n,m,d)\), \(r_\epsilon(n,m,d)\), \(N\), and \(\ell_n\).
objs: none
bib: Rubin1974, RosenbaumRubin1983, ImbensRubin2015, ChengAnanthakrishnanCai2021

home_objs: none
## section: Related work
This section will position the paper against potential-outcomes identification, semiparametric ATE and missing-outcome efficiency theory, high-dimensional causal inference under structure, semi-supervised treatment-effect estimation, and minimax estimation of non-smooth discrete functionals. The closest comparison is to `ZengBalakrishnanHanKennedy2024`, which gives supervised discrete-covariate benchmarks, and to `ChengAnanthakrishnanCai2021`, `ChakraborttyDai2024`, `KallusMao2025`, and `Kato2025`, which study semi-supervised treatment-effect designs under regular-asymptotic or surrogate-rich conditions. The section will emphasize that the present paper characterizes the unrestricted finite-alphabet annotation experiment with separate outcome and treatment-covariate sample sizes.
objs: none
bib: Rubin1974, RosenbaumRubin1983, ImbensRubin2015, RobinsRotnitzkyZhao1994, Hahn1998, HiranoImbensRidder2003, BangRobins2005, Farrell2015, AtheyImbensWager2018, ChernozhukovChetverikovDemirerDufloHansenNeweyRobins2018, Kennedy2016, ZhangBrownCai2019, ChakraborttyCai2018, DengNingZhaoZhang2024, AngelopoulosBatesFannjiangJordanZrnic2023, ChengAnanthakrishnanCai2021, ChakraborttyLuCaiLi2019, ChakraborttyDai2024, ChakraborttyDaiCarroll2022, KallusMao2025, AnniwaerZhang2025, XuWittenShojaie2025, ZengBalakrishnanHanKennedy2024, JiaoVenkatHanWeissman2015, WuYang2016, ValiantValiant2017, OrlitskySureshWu2016

home_objs: none
## section: Model and experiment
This section will define the finite-alphabet observational model, the overlap condition, the causal identifying assumptions, the ATE functional, the two-sample annotation experiment, and its minimax risk. It will keep the main setup at the level of the statistical experiment and the identified functional, with the potential-outcome assumptions included to connect the observed-data functional to the causal estimand.
objs: synth_11, synth_16, synth_10, ass:overlap, ass:labeled-iid, synth_14, ass:auxiliary-iid, ass:sample-independence, ass:consistency, ass:conditional-exchangeability, synth_13, def:model-class, synth_17, def:ate-functional, def:annotation-experiment, synth_18, def:minimax-risk
bib: Rubin1974, RosenbaumRubin1983, ImbensRubin2015

home_objs: ass:overlap, ass:labeled-iid, ass:auxiliary-iid, ass:sample-independence, ass:consistency, ass:conditional-exchangeability, def:model-class, def:ate-functional, def:annotation-experiment, def:minimax-risk
## section: Main minimax results
This section will introduce the rate \(r_\epsilon(n,m,d)\), present the known-marginal benchmark, the upper and lower bounds, and combine them into the sharp characterization with its consistency, parametric-rate, improvement, supervised-endpoint, and known-marginal-limit consequences. The reader-facing narrative will make the sample-size separation explicit: outcome marks contribute through \(n\), while treatment-covariate frequencies contribute through \(n+m\).
objs: def:frontier-rate-handle, synth_7, synth_12, def:known-marginal-risk, thm:known-marginal-boundary, synth_8, synth_3, def:mixed-estimator-handle, thm:uniform-mixed-upper, synth_22, def:common-marginal-prior-handle, thm:common-marginal-converse, thm:sharp-annotation-frontier, thm:known-marginal-limit
bib: ZengBalakrishnanHanKennedy2024, JiaoVenkatHanWeissman2015, WuYang2016, ValiantValiant2017, OrlitskySureshWu2016

home_objs: def:frontier-rate-handle, thm:known-marginal-boundary, thm:uniform-mixed-upper, thm:common-marginal-converse, thm:sharp-annotation-frontier, thm:known-marginal-limit
## section: The hybrid estimator
This section will present the estimator as an algorithm: deterministic sample splitting, finite calibration, Poisson-prefix derandomization, light-cell polynomial weights, heavy-cell inverse-count weights, and clipping. The discussion will explain how outcome counts and treatment-covariate counts enter different pieces of the statistic and how the theorem uses the calibration to produce a uniform finite-sample bound.
objs: none
bib: JiaoVenkatHanWeissman2015, WuYang2016, ValiantValiant2017, OrlitskySureshWu2016

home_objs: def:mixed-estimator-handle
## section: Interpretation and extensions
This section will interpret the three regimes delivered by the main theorem: consistency, parametric mean-squared error, and strict improvement over the supervised endpoint. It will also present the inverse-count baseline and the binary-alphabet parametric specialization as useful comparisons inside the model, and it will include a clearly labelled limitations and future work paragraph describing the positive scope: independent random outcome labeling from a shared population, binary treatment and outcome, known finite covariate alphabet, occupied-cell overlap, and unrestricted cellwise nuisance functions.
objs: synth_5, thm:inverse-count-baseline, prop:binary-alphabet-parametric-rate
bib: ChengAnanthakrishnanCai2021, ChakraborttyDai2024, KallusMao2025

home_objs: thm:inverse-count-baseline, prop:binary-alphabet-parametric-rate
## section: Appendix A: Upper-bound ingredients
This appendix section will give the proof components behind the inverse-count and hybrid upper bounds: the Poisson inverse-count risk calculation, the Chebyshev-factorial certificate, the explicit coefficient calibration, the Poisson hybrid risk bound, and the fixed-sample transfer from Poisson prefixes to exactly \(n\) labeled and \(m\) auxiliary observations. It will place the auxiliary apparatus before its first use and keep proof-engineering details out of the main exposition.
objs: lem:poisson-inverse-marginal-energy-scalar, synth_2, synth_1, lem:poisson-inverse-count-risk, lem:poisson-prefix-count-law, synth_19, lem:inverse-count-poisson-prefix-transfer, synth_4, lem:chebyshev-factorial-certificate, lem:calibrated-envelope-absorption, lem:hybrid-light-branch-mean-bound, lem:poisson-inverse-arm-mean-formula, lem:heavy-light-second-moment-sum, lem:hybrid-heavy-branch-mean-bound, lem:calibrated-hybrid-variance-bound, lem:calibrated-hybrid-mean-bias, synth_9, lem:poisson-hybrid-risk, synth_6, lem:fixed-sample-hybrid-transfer, lem:shifted-chebyshev-quotient-coefficient-bound, lem:explicit-chebyshev-calibration
bib: JiaoVenkatHanWeissman2015, WuYang2016, ValiantValiant2017, OrlitskySureshWu2016

home_objs: lem:poisson-inverse-marginal-energy-scalar, lem:poisson-inverse-count-risk, lem:poisson-prefix-count-law, lem:inverse-count-poisson-prefix-transfer, lem:chebyshev-factorial-certificate, lem:calibrated-envelope-absorption, lem:hybrid-light-branch-mean-bound, lem:poisson-inverse-arm-mean-formula, lem:heavy-light-second-moment-sum, lem:hybrid-heavy-branch-mean-bound, lem:calibrated-hybrid-variance-bound, lem:calibrated-hybrid-mean-bias, lem:poisson-hybrid-risk, lem:fixed-sample-hybrid-transfer, lem:shifted-chebyshev-quotient-coefficient-bound, lem:explicit-chebyshev-calibration
## section: Appendix B: Common-marginal lower bounds
This appendix section will develop the approximation-duality and common-marginal prior machinery used for the converse. It will present the finite alternation measure, the rare-cell construction with identical random \(P_{XA}\), the fixed-sample transfer, the label-floor lemma, and the finite illustrative two-cell calculation.
objs: def:finite-small-instance, lem:finite-alternation-duality, synth_20, lem:common-marginal-recipe-target-concentration, synth_21, lem:common-marginal-recipe-scale-tail, lem:common-marginal-recipe-transfer, lem:fixed-sample-common-marginal-transfer, lem:parametric-label-floor, lem:finite-product-padding-identity, lem:common-marginal-uniform-intensity, lem:common-marginal-canonical-certificate-family
bib: JiaoVenkatHanWeissman2015, WuYang2016, ValiantValiant2017, OrlitskySureshWu2016, ZengBalakrishnanHanKennedy2024

home_objs: def:common-marginal-prior-handle, def:finite-small-instance, lem:finite-alternation-duality, lem:common-marginal-recipe-target-concentration, lem:common-marginal-recipe-scale-tail, lem:common-marginal-recipe-transfer, lem:fixed-sample-common-marginal-transfer, lem:parametric-label-floor, lem:finite-product-padding-identity, lem:common-marginal-uniform-intensity, lem:common-marginal-canonical-certificate-family
## section: Appendix C: Known-marginal experiment and verification note
This appendix section will record the exact known-treatment-covariate-marginal experiment and risk definitions used by the benchmark and the limit theorem, then consolidate the verification note. The verification note will state that the displayed frozen definitions, assumptions, lemmas, and theorems are the machine-checked mathematical layer, while bibliographic comparisons and econometric interpretation are reader-facing synthesis built around that layer.
objs: def:known-marginal-experiment, lem:finite-side-cover-approximate-decision, lem:finite-side-information-convergence, lem:finite-side-measurable-comparison, lem:annotation-frontier-strict-improvement
bib: ImbensRubin2015, ZengBalakrishnanHanKennedy2024
home_objs: def:known-marginal-experiment, def:known-marginal-risk, lem:finite-side-cover-approximate-decision, lem:finite-side-information-convergence, lem:finite-side-measurable-comparison, lem:annotation-frontier-strict-improvement
