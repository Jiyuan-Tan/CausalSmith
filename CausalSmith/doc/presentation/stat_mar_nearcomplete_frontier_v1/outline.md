# Title
**Minimax estimation and honest inference in randomized experiments with missing outcomes**

**Contribution statement.** For balanced randomized experiments with binary outcomes and surrogates, unrestricted baseline distributions on at most \(d\) cells, and a known cellwise outcome-arrival floor \(q\in[1/2,1]\), the paper characterizes the joint dependence of minimax squared error and fixed-coverage honest connected-interval length on sample size, baseline dimension, and outcome completeness, using matching estimation and normalized-prior bounds.

# Notation

env_overrides: def:mm-estimator=algorithmv, prop:complete-arrival-reduction=propositionv

notation_gaps: \(P\)=the full-data probability law needs an anchored definition, \(P_O\)=the observed-law image needs an anchored definition, \(O\)=the observed-record space and record tuple need an anchored definition, \(X\)=the baseline variable and its finite domain need an anchored definition, \(A\)=the binary treatment indicator needs an anchored definition, \(S(0),S(1)\)=the binary potential surrogates need an anchored definition, \(Y(0),Y(1)\)=the binary potential outcomes need an anchored definition, \(S,Y\)=the realized surrogate and outcome need an anchored definition, \(R\)=the binary outcome-arrival indicator needs an anchored definition, \(RY\)=the observed outcome mark needs an anchored definition, \(\rho_P(x,a,s)\)=the cellwise arrival probability and its null-cell convention need an anchored definition, \(\mu_P(x,a,s)\)=the arrived-outcome conditional mean needs its positive-cell defining property, \(\tau(P)\)=the population average treatment effect needs an anchored definition, \(\mathcal T_n\)=the measurable estimator class and its range need an anchored definition, \(\ell_n\)=the logarithmic sample-size factor needs an anchored definition, \(g_{n,d,q}\)=the missingness-and-dimension error scale needs an explicit anchored definition, \(\Pi_{[-1,1]}\)=the interval projection operator needs an anchored definition, \(T_k\)=the Chebyshev polynomial convention needs an anchored definition, \((C_j-1)_{v-1}\)=the falling-factorial convention needs an anchored definition, \(\operatorname{TV}\)=the total-variation convention needs an anchored definition

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(P\) | \(P\) | Finite full-data probability law | notation_gaps; setup |
| \(P_O\) | \(P_O\) | Image of the full-data law under the observation map | notation_gaps; setup |
| \(O\) | \(O\) | Observed record and its Cartesian record space, distinguished by context | notation_gaps; setup |
| \(O_1,\ldots,O_n\) | \(O_1,\ldots,O_n\) | Sample of observed records | notation_gaps; setup |
| \(O^n\) | \(O^n\) | Cartesian sample space of \(n\) observed records | notation_gaps; setup |
| \(X\) | \(X\) | Baseline category with at most \(d\) occupied labels | notation_gaps; setup |
| \(A\) | \(A\) | Binary randomized treatment indicator | notation_gaps; setup |
| \(S(0),S(1)\) | \(S(0),S(1)\) | Binary potential surrogate measurements | notation_gaps; setup |
| \(Y(0),Y(1)\) | \(Y(0),Y(1)\) | Binary potential primary outcomes | notation_gaps; setup |
| \(S,Y\) | \(S,Y\) | Realized surrogate and primary outcome | notation_gaps; setup |
| \(S(A),Y(A)\) | \(S(A),Y(A)\) | Potential measurements selected by the realized treatment | notation_gaps; setup |
| \(R\) | \(R\) | Binary primary-outcome arrival indicator | notation_gaps; setup |
| \(RY\) | \(RY\) | Observed primary-outcome mark | notation_gaps; setup |
| \(n\) | \(n\) | Positive integer sample size | notation_gaps; setup |
| \(d\) | \(d\) | Positive integer baseline-support bound | def:law-class |
| \(q\) | \(q\) | Known cellwise arrival floor in \([1/2,1]\) | def:law-class |
| \(\operatorname{supp}_P(X)\) | \(\operatorname{supp}_P(X)\) | Baseline labels with positive probability under \(P\) | def:law-class |
| \(\mathcal M(d,q)\) | \(\mathcal M(d,q)\) | Full-data laws satisfying the support and randomized-MAR restrictions | def:law-class |
| \(\rho_P(x,a,s)\) | \(\rho_P(x,a,s)\) | Arrival probability conditional on the indicated observed cell | notation_gaps; setup |
| \(\mu_P(x,a,s)\) | \(\mu_P(x,a,s)\) | Arrived-outcome conditional mean with zero on null arrived cells | def:identified-functional; positive-cell property in notation_gaps |
| \(\tau(P)\) | \(\tau(P)\) | Superpopulation mean treatment effect | notation_gaps; setup |
| \(\Psi(P_O)\) | \(\Psi(P_O)\) | Observed-law functional identifying the treatment effect | def:identified-functional |
| \(\ell_n\) | \(\ell_n\) | Logarithmic sample-size factor \(\log(e+n)\) | notation_gaps; setup |
| \(g_{n,d,q}\) | \(g_{n,d,q}\) | Arrival-deficit-weighted dimension error scale | notation_gaps; setup |
| \(r_{n,d,q}\) | \(r_{n,d,q}\) | Squared-error benchmark combining sampling and dimension terms | def:rate |
| \(\mathcal T_n\) | \(\mathcal T_n\) | Measurable estimators from \(O^n\) to \([-1,1]\) | notation_gaps; setup |
| \(T\) | \(T\) | Generic estimator in the measurable estimator class | def:point-risk |
| \(\mathfrak R^*_{n,d,q}\) | \(\mathfrak R^*_{n,d,q}\) | Minimax squared-error risk over the law class | def:point-risk |
| \(I\) | \(I\) | Measurable connected confidence-interval procedure | def:interval-class |
| \([L,U]\) | \([L,U]\) | Closed output interval contained in the treatment-effect range | def:interval-class |
| \(\mathcal C_\alpha(n,d,q)\) | \(\mathcal C_\alpha(n,d,q)\) | Interval procedures with uniform coverage at least \(1-\alpha\) | def:interval-class |
| \(\operatorname{length}\{I(O^n)\}\) | \(\operatorname{length}\{I(O^n)\}\) | Difference between the output interval's endpoints | def:length-risk |
| \(\mathfrak L^*_{n,d,q,\alpha}\) | \(\mathfrak L^*_{n,d,q,\alpha}\) | Minimax worst-law expected honest interval length | def:length-risk |
| \(\Pi_{[-1,1]}\) | \(\Pi_{[-1,1]}\) | Projection onto the treatment-effect range | notation_gaps; estimation |
| \(m\) | \(m\) | Mean stream-size parameter in the estimator construction | def:mm-estimator |
| \(k\) | \(k\) | Polynomial degree parameter in the estimator construction | def:mm-estimator |
| \(B\) | \(B\) | Polynomial approximation and cell-classification scale | def:mm-estimator |
| \(N\) | \(N\) | Auxiliary Poisson sample count | def:mm-estimator |
| \(Y_i^{\mathrm{obs}}\) | \(Y_i^{\mathrm{obs}}\) | Supplied observed-outcome coordinate of record \(i\) | def:mm-estimator |
| \((RY)_i\) | \((RY)_i\) | Fifth coordinate of record \(i\) | def:mm-estimator |
| \(j=(x,a,s)\) | \(j=(x,a,s)\) | Observed-cell index for the estimator | def:mm-estimator |
| \(M_j^{(2)}\) | \(M_j^{(2)}\) | Stream-two missing-outcome count in cell \(j\) | def:mm-estimator |
| \(V_j\) | \(V_j\) | Scaled stream-two missing-outcome count | def:mm-estimator |
| \(C'_j\) | \(C'_j\) | Stream-three arrived-outcome count | def:mm-estimator |
| \(C_j\) | \(C_j\) | Stream-four arrived-outcome count | def:mm-estimator |
| \(U_j\) | \(U_j\) | Stream-four arrived-success count on observed-law support | def:mm-estimator |
| \(T_k\) | \(T_k\) | Degree-\(k\) Chebyshev polynomial | notation_gaps; estimation |
| \(Q_k(z)\) | \(Q_k(z)\) | Polynomial approximation rule with its specified value at zero | def:mm-estimator |
| \(a_v\) | \(a_v\) | Coefficients of the polynomial correction | def:mm-estimator |
| \((C_j-1)_{v-1}\) | \((C_j-1)_{v-1}\) | Falling factorial used for unbiased polynomial terms | notation_gaps; estimation |
| \(H_j\) | \(H_j\) | Light-cell polynomial correction statistic | def:mm-estimator |
| \(D_j\) | \(D_j\) | Centered arrived-outcome ratio statistic | def:mm-estimator |
| \(G_j\) | \(G_j\) | Cell correction selected by the independent count threshold | def:mm-estimator |
| \(a_j\) | \(a_j\) | Treatment coordinate of cell \(j\) | def:mm-estimator |
| \(A_i\) | \(A_i\) | Treatment coordinate of record \(i\) | def:mm-estimator |
| \(R_i\) | \(R_i\) | Arrival coordinate of record \(i\) | def:mm-estimator |
| \(R_iY_i\) | \(R_iY_i\) | Observed outcome mark on observation-map support | def:mm-estimator |
| \(\widetilde\tau\) | \(\widetilde\tau\) | Projected estimate using auxiliary randomization | def:mm-estimator |
| \(\widehat\tau_{\mathrm{MM}}\) | \(\widehat\tau_{\mathrm{MM}}\) | Conditional-average estimator with specified endpoint and fallback branches | def:mm-estimator |
| \(Y_i\) | \(Y_i\) | Realized primary outcome in record \(i\) at complete arrival | notation_gaps; setup |
| \(C_U\) | \(C_U\) | Universal risk-bound constant used to choose the interval radius | def:mm-interval |
| \(h_{n,d,q,\alpha}\) | \(h_{n,d,q,\alpha}\) | Clipped finite-sample confidence radius | def:mm-interval |
| \(\widehat I_{\mathrm{MM},\alpha}(O^n)\) | \(\widehat I_{\mathrm{MM},\alpha}(O^n)\) | Confidence interval centered at the estimator and clipped to its target range | def:mm-interval |
| \(\delta\) | \(\delta\) | Outcome-arrival deficit \(1-q\) | def:paired-prior-handle |
| \(L\) | \(L\) | Logarithmic sample-size factor local to the prior construction | def:paired-prior-handle |
| \(K\) | \(K\) | Interpolation-order parameter | def:paired-prior-handle |
| \(h\) | \(h\) | Lower interpolation endpoint | def:paired-prior-handle |
| \(m\) | \(m\) | Number of interpolation intervals local to the prior construction | def:paired-prior-handle |
| \(B_0\) | \(B_0\) | Upper scale of latent unnormalized label masses | def:paired-prior-handle |
| \(M\) | \(M\) | Number of paired baseline labels | def:paired-prior-handle |
| \(c_0\) | \(c_0\) | Fixed outcome perturbation constant in the prior construction | def:paired-prior-handle |
| \(b\) | \(b\) | Arrival-deficit-dependent centering constant | def:paired-prior-handle |
| \(\mu_0\) | \(\mu_0\) | Treated-outcome mean at the filler label | def:paired-prior-handle |
| \(x_i\) | \(x_i\) | Interpolation nodes on the specified positive interval | def:paired-prior-handle |
| \(l_i\) | \(l_i\) | Lagrange cardinal polynomial for node \(i\) | def:paired-prior-handle |
| \(l_i(0)\) | \(l_i(0)\) | Cardinal-polynomial evaluation at zero | def:paired-prior-handle |
| \(D\) | \(D\) | Sum of absolute cardinal-polynomial evaluations at zero | def:paired-prior-handle |
| \(\nu_i\) | \(\nu_i\) | Normalized signed interpolation weight | def:paired-prior-handle |
| \((p,z)\in[0,B_0]\times\{-1,1\}\) | \((p,z)\in[0,B_0]\times\{-1,1\}\) | Latent mass-and-sign pair with the specified discrete distribution | def:paired-prior-handle |
| \(\operatorname{sign}(\nu_i)\) | \(\operatorname{sign}(\nu_i)\) | Sign assigned to the latent interpolation atom | def:paired-prior-handle |
| \((p_j,z_j)\) | \((p_j,z_j)\) | Independent latent draw for baseline pair \(j\) | def:paired-prior-handle |
| \(r_j\in\{-1,1\}\) | \(r_j\in\{-1,1\}\) | Independent fair orientation sign | def:paired-prior-handle |
| \(u\) | \(u\) | Orientation of a label within a baseline pair | def:paired-prior-handle |
| \(\rho_{\sigma,j,u}\) | \(\rho_{\sigma,j,u}\) | Treated arrival probability at the indicated prior label | def:paired-prior-handle |
| \(\mu_{\sigma,j,u}\) | \(\mu_{\sigma,j,u}\) | Treated Bernoulli outcome mean at the indicated prior label | def:paired-prior-handle |
| \(v_{\sigma}(z_j,u)\) | \(v_{\sigma}(z_j,u)\) | Four observed-atom coefficients at one orientation | def:paired-prior-handle |
| \(f\) | \(f\) | Fixed unnormalized filler-label mass | def:paired-prior-handle |
| \(v_{\mathrm{fill}}\) | \(v_{\mathrm{fill}}\) | Four observed-atom coefficients at the filler label | def:paired-prior-handle |
| \(J\) | \(J\) | Exact random total mass used for algebraic normalization | def:paired-prior-handle |
| \(P_{\sigma}\) | \(P_{\sigma}\) | Normalized causal law generated by the latent draws | def:paired-prior-handle |
| \(P_{\sigma,O}\) | \(P_{\sigma,O}\) | Observed-law image of the normalized causal law | def:paired-prior-handle |
| \(\Pi_{\sigma}\) | \(\Pi_{\sigma}\) | Distribution of the normalized causal law under latent draws | def:paired-prior-handle |
| \(P_{\sigma,O}^{\otimes n}\) | \(P_{\sigma,O}^{\otimes n}\) | Conditional iid observed-sample law for a prior draw | def:paired-prior-handle |
| \(Q_{\sigma}^{(n)}\) | \(Q_{\sigma}^{(n)}\) | Prior-predictive law of the complete observed sample | def:paired-prior-handle |
| \(\lambda\) | \(\lambda\) | Poisson intensity in the auxiliary count experiment | def:paired-prior-handle |
| \(o_{\circ}\in O\) | \(o_{\circ}\in O\) | Fixed fallback record for the count-to-sample transformation | def:paired-prior-handle |
| \(\kappa_n\) | \(\kappa_n\) | Parameter-independent count-ordering and truncation Markov kernel | def:paired-prior-handle |
| \(\Pi_-,\Pi_+\) | \(\Pi_-,\Pi_+\) | The two sign-indexed normalized priors | def:paired-prior-handle |
| \(Q_-^{(n)},Q_+^{(n)}\) | \(Q_-^{(n)},Q_+^{(n)}\) | Complete observed-sample mixtures for the two priors | def:paired-prior-handle |
| \(\operatorname{TV}\) | \(\operatorname{TV}\) | Total variation between probability laws | notation_gaps; appendix |
| \(c_\beta\) | \(c_\beta\) | Existential target-separation constant for fixed mixture tolerance | Local existential in thm:normalized-converse; appendix definition needed before lem:prior-reduction |
| \(m_0\) | \(m_0\) | Deterministic target-separation center for the constructed priors | Local existential in thm:normalized-converse |
| \(\beta_0\) | \(\beta_0\) | Fixed mixture tolerance used for the squared-risk reduction | Local choice in lem:prior-reduction |
| \(\beta_\alpha\) | \(\beta_\alpha\) | Coverage-dependent mixture tolerance used for the length reduction | Local choice in lem:prior-reduction |
| \(c_{\beta_0}\) | \(c_{\beta_0}\) | Separation constant evaluated at the squared-risk tolerance | Same appendix definition as \(c_\beta\) |
| \(c_{\beta_\alpha}\) | \(c_{\beta_\alpha}\) | Separation constant evaluated at the coverage-dependent tolerance | Same appendix definition as \(c_\beta\) |
| \(c_0\) | \(c_0\) | Existential universal constant in the parametric risk lower bound | Local existential in lem:parametric-floor-infrastructure |
| \(c_{0,\alpha}\) | \(c_{0,\alpha}\) | Existential coverage-dependent parametric length constant | Local existential in lem:parametric-floor-infrastructure |
| \(c,C\) | \(c,C\) | Existential universal comparison constants for squared risk | Local existentials in thm:point-frontier |
| \(c_\alpha,C_\alpha\) | \(c_\alpha,C_\alpha\) | Existential comparison constants depending only on fixed noncoverage | Local existentials in thm:interval-frontier |

# Sections

## section: Abstract

Plan the abstract for drafting after the body. Lead with the statistical question of how missing-outcome frequency and baseline dimension jointly determine treatment-effect precision. State the randomized finite-cell binary model, known arrival-floor range, minimax estimation result, and fixed-coverage connected-interval result. Describe attainment and the matching normalized-prior argument briefly. Use words or first-use appositives for symbols introduced before their defining environments.

objs: none

bib: none

home_objs: none
## section: Introduction

Organize the introduction around the precision cost of missing primary outcomes when baseline membership, treatment, surrogate measurements, and arrival remain observed. Explain why outcome completeness and the number of baseline cells must be considered jointly, and motivate the distinction between population identification and uniform statistical precision. Present the contribution as matching estimation and honest-inference rates, with dimension-free precision at complete arrival and an explicit attaining procedure. Draft this section last, after the interpretation and literature comparison are settled. Include one factual sentence pointing to the appendix verification note.

objs: none

bib: ImbensRubin2015, Rubin1976, Wooldridge2002

home_objs: none
## section: Related work

Make the closest comparisons explicit and experiment-specific. Compare the identification and regular-efficiency analysis of KallusMao2025, particularly Lemma 1.1 under Assumptions 1–3, Theorem 2.1, and Sections 3–4, with the present unrestricted finite-cell uniform analysis. Compare ZengBalakrishnanHanKennedy2024, Theorems 1–2 and Appendix C.5, in its complete-record treatment-positivity experiment; credit CausalSmith2026 for fixed-overlap polynomial estimation and the balanced endpoint, and distinguish the independent annotation experiment in CausalSmith2026Annotation. Use ZhangChakraborttyBradic2025, Theorem 2.2 and equation (2.4), and Theorems 4.1–4.2, as structured decaying-labeling benchmarks with their nuisance, correctness, and sparsity conditions preserved. Credit JiaoVenkatHanWeissman2015, Sections III–IV, and WuYang2016, Proposition 3 and Appendix B.2, for polynomial estimation and mixture-comparison methods. Place honest expected-length theory beside CaiLow2004, Theorem 1 and Section 5, and distinguish the conditional smoothness-based ATE procedures of Armstrong2021 and the asymptotic randomized-trial inference of DiazVanDerLaan2017, Theorem 2 under Conditions 2–3. Attribute novelty conservatively to the joint arrival-and-dimension characterization and the exactly normalized converse for the complete observed record.

objs: none

bib: KallusMao2025, ZengBalakrishnanHanKennedy2024, CausalSmith2026, CausalSmith2026Annotation, ZhangChakraborttyBradic2025, JiaoVenkatHanWeissman2015, WuYang2016, Wu2020, CaiLow2004, Donoho1994, Low1997, Armstrong2021, DiazVanDerLaan2017, Rubin1976, Tsiatis2006, Robins1994, Chernozhukov2018, Robins1997, Robins2008, Robins2009, Robins2017, Kennedy2024

home_objs: none
## section: Setup and statistical criteria

Introduce the full-data and observed-data laws, potential measurements, population treatment effect, and null-cell conventions through grouped presentation definitions resolving the setup notation gaps. Explain the observed information retained when an outcome is missing. Present the genuine sampling, randomization, consistency, MAR, and arrival-floor assumptions, followed by the law class and observed-law functional. Introduce the estimator class, honest connected intervals, squared-risk and expected-length criteria, and the common rate notation. Reserve the interpolation and count-experiment notation for the appendix. Credit identification through \cref{obj:lem:identification-infrastructure}, with the published comparison retaining its precise locator.

objs: synth_3, synth_4, synth_2, ass:iid, ass:randomized-independence, ass:balanced-randomization, ass:consistency, ass:mar, synth_1, synth_5, ass:arrival-floor, def:law-class, def:identified-functional, synth_6, def:point-risk, def:interval-class, def:length-risk, def:rate

bib: ImbensRubin2015, Rubin1974, Rubin1976, Tsiatis2006, KallusMao2025

home_objs: ass:iid, ass:randomized-independence, ass:balanced-randomization, ass:consistency, ass:mar, ass:arrival-floor, def:law-class, def:identified-functional, def:point-risk, def:interval-class, def:length-risk, def:rate
## section: Minimax estimation and honest inference

Present the central estimator as a numbered algorithm, explaining the roles of observed-outcome centering, missing-cell membership, polynomial correction for lightly populated cells, ratio correction for heavily populated cells, and conditional averaging over auxiliary randomization. Resolve the estimator's operator and polynomial notation before its first use. Define the clipped interval and explain how the uniform risk bound supplies its finite-sample coverage guarantee. Present the two headline results together and interpret their matching upper and lower bounds in the model's statistical criteria. Follow with the complete-arrival reduction as a proposition, emphasizing the standard randomized-difference estimator and dimension-free endpoint. Give short proof roadmaps pointing to the appendix risk, coverage, and converse arguments.

objs: def:mm-estimator, def:mm-interval, thm:point-frontier, thm:interval-frontier, prop:complete-arrival-reduction

bib: Horvitz1952, JiaoVenkatHanWeissman2015, CausalSmith2026, CausalSmith2026Annotation

home_objs: def:mm-estimator, def:mm-interval, thm:point-frontier, thm:interval-frontier, prop:complete-arrival-reduction
## section: Statistical implications

Interpret the balance between sampling error and the arrival-weighted dimension term, including the transition to sampling-dominated precision and the saturation of the dimension contribution. Discuss joint sequences of sample size, baseline dimension, and known arrival floor through the proved rate expressions. Explain how the honest interval criterion translates these regimes into uniform precision at fixed coverage. Describe the constant-surrogate randomized submodel as the basis for transferring the converse to broader classes containing that submodel, with the matching upper result tied affirmatively to the specified finite-cell model. Keep interpretation centered on the paper's results.

objs: none

bib: none

home_objs: none
## section: Limitations and future work

Identify arrival floors below one half, adaptation to an unknown floor, practical constants, and empirical calibration as directions for further work. Separate these questions from the established known-floor results. State the scope of the broader-class comparison precisely: the embedded submodel supports a lower-bound transfer, while matching procedures for broader models require further analysis. Discuss computational implementation of conditional averaging as a practical direction rather than an established computational guarantee.

objs: none

bib: none

home_objs: none
## section: Appendix A: Identification and estimation bounds

Place the identification lemma before the estimation arguments. Give the randomized-MAR calculation with the stated null-cell conventions, followed by the proof of the uniform estimator risk bound. Organize the estimation proof around the scientific decomposition, light-cell approximation, heavy-cell control, projection, conditional averaging, and the specified endpoint and fallback branches. Resolve auxiliary notation locally before use. Finish with the honest-interval construction lemma and its finite-sample coverage and length argument. Preserve external methodological credits and exact citation locators.

objs: lem:identification-infrastructure, lem:upper-risk, lem:honest-interval-construction

bib: KallusMao2025, JiaoVenkatHanWeissman2015, CausalSmith2026, CausalSmith2026Annotation, Wu2020

home_objs: lem:identification-infrastructure, lem:upper-risk, lem:honest-interval-construction
## section: Appendix B: Normalized priors and the dimension lower bound

Introduce the paired-prior construction before its converse theorem, keeping all interpolation, latent-distribution, normalization, and auxiliary count-experiment apparatus here. Explain how the opposite orientations, full eight-coordinate observed vector, fixed filler, and algebraic normalization produce legal randomized-MAR laws. Organize the converse proof around mixture comparison, parameter-independent count-to-sample transformation, and concentration of the treatment-effect separation. Retain the theorem's dimension-dominated regime and fixed-tolerance quantifiers. Credit the approximation and Poisson-mixture tools while identifying the same-experiment normalization and arrival-deficit attenuation as the paper's construction-specific ingredients.

objs: def:paired-prior-handle, thm:normalized-converse

bib: WuYang2016, Wu2020, ZengBalakrishnanHanKennedy2024, CausalSmith2026, CausalSmith2026Annotation

home_objs: def:paired-prior-handle, thm:normalized-converse
## section: Appendix C: Testing reductions and proofs of the main results

Establish the parametric estimation and interval-length floors, then introduce the choices of separation constants and testing tolerances needed for the prior reduction. Apply the normalized converse to squared risk and honest connected-interval length, retaining its regime gate and combining it with the parametric floors. Complete the proofs of the headline results using the estimation and coverage bounds, and give the complete-arrival proposition's projection and variance argument. Keep standard testing infrastructure credited separately from the model-specific prior construction.

objs: lem:parametric-floor-infrastructure, lem:prior-reduction

bib: Tsybakov2009, CaiLow2004, Low1997, Horvitz1952

home_objs: lem:parametric-floor-infrastructure, lem:prior-reduction
## section: Appendix D: Verification note

End the appendix with a brief consolidated account of the Lean machine-checking scope. Identify the frozen assumptions as inputs and report the verification coverage of the definitions, identification and risk lemmas, interval construction, normalized converse, reductions, and headline results from the available verification metadata. Distinguish machine-checked statements from externally cited dependencies, preserving theorem-local verification-scope disclosures. Keep declaration names and proof-engineering details here, and report bibliographic comparisons as source-based scholarship.

objs: none

bib: none
home_objs: none
