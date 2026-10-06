# Title
**Minimax excess variance with smooth pairwise interactions in randomized experiments**

**Contribution statement.** Under independent uniform covariates and an exact centered order-two prognostic specification with a pooled nonperiodic Sobolev budget, the paper characterizes minimax Horvitz–Thompson excess variance up to constants uniformly over sample size, dimension, and smoothness between zero and one, and constructs a single fair assignment procedure that attains the rate simultaneously across smoothness levels.

# Notation

env_overrides: prop:published-class-inclusion=propositionv, def:capacity-handle=algorithmv, def:ordered-boundary-rounding=algorithmv

notation_gaps: \(g_j(m)\)=canonical main-effect operator lacks an anchored defining environment, \(g_{j\ell}(m)\)=canonical pair-effect operator lacks an anchored defining environment, \(N_{1,s}(g_j(m))\)=nonperiodic component restriction norm lacks an anchored defining environment, \(N_{2,s}(g_{j\ell}(m))\)=nonperiodic component restriction norm lacks an anchored defining environment, \(N_{p,s}(g)\)=general component restriction norm lacks an anchored defining environment, \(\mathcal Z_n\)=assignment sign space lacks an anchored defining environment, \(\mathcal L_{n,d,s}(\pi,m)\)=scaled signing loss appears inside the capacity formula without an anchored definition of the named loss, \(B\)=coordinate-pair count lacks an anchored defining environment, \(m_\xi\)=prior definition refers to an absent symbol-table formula, \(V(X_1)\)=pair-cosine feature vector lacks an anchored defining environment, \(C_0\)=prior normalization constant needs an anchored definition accompanying the missing prior formula, \(b_s(n,d)\)=lower comparison scale lacks an anchored defining environment, \(F\)=reflected prognostic function lacks an anchored defining environment, \(\widehat F(k)\)=Fourier coefficients of the reflected function lack an anchored defining environment, \(t(k)\)=frequency complexity lacks an anchored defining environment, \(W\)=reflected and commonly shifted original sample lacks an anchored defining environment, \(T\)=independent common shift lacks an anchored defining environment, \(e_k(W_i)\)=torus character lacks an anchored defining environment, \(Y\)=pre-assignment potential-outcome array needs its anchored generating specification, \(A\)=treatment indicator needs its anchored assignment formula, \(\widehat\theta\)=Gaussian-completion HT estimator needs its anchored formula, \(\theta_n\)=finite-population causal target needs its anchored formula, \(\theta\)=sampling-law causal target needs its anchored formula, \(q\)=potential-outcome midpoint vector lacks an anchored defining environment, \(C_\pi(X)\)=conditional assignment covariance lacks an anchored defining environment, \(\mathcal Q_{d,s}\)=uniform zero-intercept outcome-law class lacks an anchored defining environment, \(\mathsf V(P)\)=law-specific benchmark refers to lem:published-ht-excess-identity, which is absent from the frozen inventory, \(\mathcal A_{d,s}\)=larger bounded-density comparison class is introduced inside a lemma rather than an anchored definition, \(\mathbb T_2^p\)=period-two torus lacks an anchored defining environment, \(b_p\)=coordinatewise reflection map lacks an anchored defining environment

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(m(x)\) | \(m(x)\) | Centered prognostic function evaluated at a cube point | def:sobolev-class |
| \(g_j(m)(x_j)\) | \(g_j(m)(x_j)\) | Canonical main effect evaluated at coordinate \(j\) | notation gap: canonical component family |
| \(g_{j\ell}(m)(x_j,x_\ell)\) | \(g_{j\ell}(m)(x_j,x_\ell)\) | Canonical pair effect evaluated at coordinates \(j,\ell\) | notation gap: canonical component family |
| \(N_{1,s}(g_j(m))^2\) | \(N_{1,s}(g_j(m))^2\) | Squared nonperiodic Sobolev restriction norm of a main effect | notation gap: component norm family |
| \(N_{2,s}(g_{j\ell}(m))^2\) | \(N_{2,s}(g_{j\ell}(m))^2\) | Squared nonperiodic Sobolev restriction norm of a pair effect | notation gap: component norm family |
| \(X\) | \(X\) | Full sample of independent uniform covariate vectors | notation gap: sampling and assignment family |
| \(X_1\) | \(X_1\) | First original unit's covariate vector | notation gap: sampling and assignment family |
| \(Z_i\) | \(Z_i\) | Assignment sign for original unit \(i\) | notation gap: sampling and assignment family |
| \(Z\) | \(Z\) | Vector of original-unit assignment signs | notation gap: sampling and assignment family |
| \(\pi\) | \(\pi\) | Covariate-dependent Borel assignment probability law | def:design-class |
| \(\mathcal Z_n\) | \(\mathcal Z_n\) | Space of length-\(n\) assignment sign vectors | notation gap: sampling and assignment family |
| \(\mathcal P(\mathcal Z_n)\) | \(\mathcal P(\mathcal Z_n)\) | Probability measures on the assignment sign space | notation gap: sampling and assignment family |
| \(\mathcal H_{d,s}\) | \(\mathcal H_{d,s}\) | Centered exact order-two functions satisfying the pooled component budget | def:sobolev-class |
| \(\mathcal D_{n,d,s}\) | \(\mathcal D_{n,d,s}\) | Fair outcome-independent Borel assignment laws using the original sample | def:design-class |
| \(R_s(n,d)\) | \(R_s(n,d)\) | Minimax scaled signing loss over admissible designs and prognostic functions | def:criterion |
| \(\mathcal L_{n,d,s}(\pi,m)\) | \(\mathcal L_{n,d,s}(\pi,m)\) | Scaled expected squared prognostic imbalance | notation gap: signing-loss family |
| \(\xi\) | \(\xi\) | Random coefficient signs drawn before the covariate sample | def:cosine-prior; missing formula recorded above |
| \(m_\xi\) | \(m_\xi\) | Random pair-cosine prognostic function with normalized Sobolev budget | def:cosine-prior; missing formula recorded above |
| \(L\) | \(L\) | Integer frequency cutoff for the independent coefficient prior | def:cosine-prior |
| \(B\) | \(B\) | Number of coordinate pairs | notation gap: interaction count |
| \(V(X_1)\) | \(V(X_1)\) | Pair-cosine feature vector evaluated at the first original unit | notation gap: cosine-prior family |
| \(M\) | \(M\) | Number of coordinates in the pair-cosine feature vector | notation gap: cosine-prior family |
| \(I_M\) | \(I_M\) | Identity matrix in the pair-feature dimension | notation gap: cosine-prior family |
| \(C_0=C_0(s)\) | \(C_0=C_0(s)\) | Prior normalization constant ensuring class membership | notation gap: cosine-prior family |
| \(C_0=\sqrt{48+32\pi^2}\) | \(C_0=\sqrt{48+32\pi^2}\) | Specified normalization used by the attaining comparison | notation gap: cosine-prior family |
| \(b_s(n,d)\) | \(b_s(n,d)\) | Saturated lower comparison scale | notation gap: comparison-scale family |
| \(a_s(n,d)\) | \(a_s(n,d)\) | Saturated interaction-to-sample comparison scale | def:capacity-handle; explicit formula supplied by the frozen results |
| \(a_s\) | \(a_s\) | Comparison scale in the construction triple | def:capacity-handle |
| \(\pi^\star\) | \(\pi^\star\) | Attaining assignment procedure in the construction triple | def:capacity-handle |
| \(\nu^\star\) | \(\nu^\star\) | Independent coefficient prior in the construction triple | def:capacity-handle |
| \(\pi^\star_{n,d}\) | \(\pi^\star_{n,d}\) | Smoothness-independent fair original-sample assignment procedure | def:capacity-handle |
| \(\pi^\star_{n,d,s}\) | \(\pi^\star_{n,d,s}\) | Smoothness-indexed designation of the same assignment procedure | def:capacity-handle |
| \(\nu^\star_{n,d,s}\) | \(\nu^\star_{n,d,s}\) | Law of the legal coefficient-prior prognostic function | def:cosine-prior |
| \(F\) | \(F\) | Even reflected periodic extension of the prognostic function | notation gap: spectral construction family |
| \(\widehat F(k)\) | \(\widehat F(k)\) | Fourier coefficient at integer frequency \(k\) | notation gap: spectral construction family |
| \(\widehat F(0)\) | \(\widehat F(0)\) | Constant Fourier coefficient of the reflected prognostic function | notation gap: spectral construction family |
| \(\operatorname{supp}(k)\) | \(\operatorname{supp}(k)\) | Coordinates with nonzero entries in frequency \(k\) | notation gap: spectral construction family |
| \(t(k)\) | \(t(k)\) | Squared frequency magnitude normalized by support size | notation gap: spectral construction family |
| \(W\) | \(W\) | Independently reflected and commonly shifted original covariate sample | notation gap: spectral construction family |
| \(W_i\) | \(W_i\) | Transformed covariate vector for original unit \(i\) | notation gap: spectral construction family |
| \(T\) | \(T\) | Independent common Haar shift | notation gap: spectral construction family |
| \(e_k(W_i)\) | \(e_k(W_i)\) | Integer-frequency character evaluated at transformed unit \(i\) | notation gap: spectral construction family |
| \(C_s\) | \(C_s\) | Bound constant in the spectral transfer and upper comparison | notation gap: comparison constants; preserve each frozen local use |
| \(c_s\) | \(c_s\) | Smoothness-indexed lower comparison constant | notation gap: comparison constants |
| \(c_1\) | \(c_1\) | Positive smoothness-uniform lower comparison constant | notation gap: comparison constants |
| \(d_n\) | \(d_n\) | Integer dimension sequence indexed by sample size | notation gap: asymptotic comparison family |
| \(Y\) | \(Y\) | Realized full pre-assignment potential-outcome schedule | def:causal-completion; generating specification missing |
| \(A\) | \(A\) | Treatment indicator induced by assignment signs | def:causal-completion; formula missing |
| \(\widehat\theta\) | \(\widehat\theta\) | Actual HT estimator under the Gaussian causal completion | def:causal-completion; formula missing |
| \(\theta_n\) | \(\theta_n\) | Average realized potential-outcome contrast | def:causal-completion; formula missing |
| \(\theta\) | \(\theta\) | Sampling-law mean of the finite-population contrast | def:causal-completion; formula missing |
| \(q\) | \(q\) | Vector of potential-outcome midpoints | notation gap: causal-completion family |
| \(C_\pi(X)\) | \(C_\pi(X)\) | Conditional covariance matrix of assignment signs | notation gap: causal-completion family |
| \(V^*\) | \(V^*\) | Gaussian-completion scaled variance benchmark equal to \(4.01\) | notation gap: causal-completion family |
| \(\mathcal Q_{d,s}\) | \(\mathcal Q_{d,s}\) | Uniform-covariate square-integrable outcome laws with the centered pooled prognostic class | notation gap: outcome-law family |
| \(P\) | \(P\) | Single-unit joint law of covariates and potential outcomes | notation gap: outcome-law family |
| \(U\) | \(U\) | Covariate under the single-unit outcome law | notation gap: outcome-law family |
| \(O(0),O(1)\) | \(O(0),O(1)\) | Single-unit potential outcomes | notation gap: outcome-law family |
| \(\vartheta(P)\) | \(\vartheta(P)\) | Mean potential-outcome contrast under law \(P\) | notation gap: outcome-law family |
| \(m_P(u)\) | \(m_P(u)\) | Conditional mean potential-outcome midpoint at covariate \(u\) | notation gap: outcome-law family |
| \(\widehat T_P\) | \(\widehat T_P\) | Actual HT estimator from independent original-unit copies under law \(P\) | notation gap: outcome-law family |
| \(O_i((Z_i+1)/2)\) | \(O_i((Z_i+1)/2)\) | Observed potential outcome selected by original unit \(i\)'s sign | notation gap: outcome-law family |
| \(\mathcal V_n(\pi,P)\) | \(\mathcal V_n(\pi,P)\) | Scaled actual HT variance above the law-specific benchmark | notation gap: outcome-law family |
| \(\mathsf V(P)\) | \(\mathsf V(P)\) | Conditional-variance benchmark for law \(P\) | notation gap: absent benchmark definition |
| \(\mathcal A_{d,s}\) | \(\mathcal A_{d,s}\) | Larger correctly specified order-two bounded-density comparison class | notation gap: comparison outcome-law family |
| \(f(u)\) | \(f(u)\) | Covariate density in the larger comparison class | notation gap: comparison outcome-law family |
| \(a\in\mathbb R^{K\times n}\) | \(a\in\mathbb R^{K\times n}\) | Input matrix of ordered balancing rows | def:ordered-boundary-rounding |
| \(K=\lfloor n/4\rfloor\) | \(K=\lfloor n/4\rfloor\) | Number of input rows supplied to rounding | def:ordered-boundary-rounding |
| \(u\in[-1,1]^n\) | \(u\in[-1,1]^n\) | Fractional assignment state initialized at zero | def:ordered-boundary-rounding |
| \(u_i\) | \(u_i\) | Fractional assignment coordinate for unit \(i\) | def:ordered-boundary-rounding |
| \(r\) | \(r\) | Active-coordinate count at the start of a rounding phase | def:ordered-boundary-rounding |
| \(q_1=\lfloor r/4\rfloor\) | \(q_1=\lfloor r/4\rfloor\) | Number of ordered row constraints retained within a phase | def:ordered-boundary-rounding |
| \(P\) | \(P\) | Local orthogonal projection onto the active constrained subspace | def:ordered-boundary-rounding; distinguish from the outcome law by context |
| \(e_1,\ldots,e_n\) | \(e_1,\ldots,e_n\) | Standard coordinate vectors used in ordered orthonormalization | def:ordered-boundary-rounding |
| \(v_1,\ldots,v_h\) | \(v_1,\ldots,v_h\) | Ordered orthonormal basis of the active constrained subspace | def:ordered-boundary-rounding |
| \(h\) | \(h\) | Local number of basis vectors in a rounding move | def:ordered-boundary-rounding |
| \((v_b)_i\) | \((v_b)_i\) | Coordinate \(i\) of rounding basis vector \(b\) | def:ordered-boundary-rounding |
| \(\delta_b^+\) | \(\delta_b^+\) | Maximum positive step along basis vector \(b\) before a boundary hit | def:ordered-boundary-rounding |
| \(\delta_b^-\) | \(\delta_b^-\) | Maximum negative step along basis vector \(b\) before a boundary hit | def:ordered-boundary-rounding |
| \(t_b=\delta_b^+\delta_b^-\) | \(t_b=\delta_b^+\delta_b^-\) | Product of the two boundary step lengths | def:ordered-boundary-rounding |
| \(S=\sum_{b=1}^h t_b^{-1}\) | \(S=\sum_{b=1}^h t_b^{-1}\) | Normalizing sum for basis-vector selection probabilities | def:ordered-boundary-rounding |
| \(a_1,a_2,\ldots\in\mathbb R^n\) | \(a_1,a_2,\ldots\in\mathbb R^n\) | Ordered deterministic balancing rows | def:ordered-boundary-rounding |
| \((a_h)_i\) | \((a_h)_i\) | Entry for unit \(i\) in balancing row \(h\) | def:ordered-boundary-rounding |
| \(a_h^{\mathsf T}Z\) | \(a_h^{\mathsf T}Z\) | Signed imbalance of balancing row \(h\) | def:ordered-boundary-rounding |
| \(r_0\) | \(r_0\) | Local dimension of the isotropic signing vector | notation gap: appendix isotropic-vector family |
| \(v\in\mathbb R^{r_0}\) | \(v\in\mathbb R^{r_0}\) | Random vector with identity second-moment matrix | notation gap: appendix isotropic-vector family |
| \(v_1,\ldots,v_n\) | \(v_1,\ldots,v_n\) | Independent copies of the isotropic vector | notation gap: appendix isotropic-vector family |
| \(I_{r_0}\) | \(I_{r_0}\) | Identity matrix in the local isotropic-vector dimension | notation gap: appendix isotropic-vector family |
| \(z\in\{-1,1\}^n\) | \(z\in\{-1,1\}^n\) | Candidate original-sample sign vector in the signing minimum | notation gap: appendix isotropic-vector family |
| \(N_{p,s}(g)\) | \(N_{p,s}(g)\) | Nonperiodic Sobolev restriction norm of a \(p\)-dimensional cube function | notation gap: component norm family |
| \(g\in L^2([0,1]^p)\) | \(g\in L^2([0,1]^p)\) | Local square-integrable cube function for the reflection argument | notation gap: appendix reflection family |
| \(h=g\circ b_p\) | \(h=g\circ b_p\) | Even reflected period-two extension of the local cube function | notation gap: appendix reflection family |
| \(\mathbb T_2^p\) | \(\mathbb T_2^p\) | \(p\)-dimensional period-two torus | notation gap: spectral construction family |
| \(b_p\) | \(b_p\) | Coordinatewise fold from the period-two torus onto the cube | notation gap: spectral construction family |
| \(a\in\mathbb Z^p\) | \(a\in\mathbb Z^p\) | Local integer frequency for the component reflection argument | notation gap: appendix reflection family |
| \(\widehat h(a)\) | \(\widehat h(a)\) | Normalized torus Fourier coefficient of the reflected component | notation gap: appendix reflection family |

# Sections

## section: Abstract

Plan a compact account of the econometric question, the exact uniform-covariate and pooled order-two specification, the matched excess-variance scale, the single smoothness-independent assignment procedure, and the fixed-smoothness dimension condition. Write this section last. Introduce symbols through plain-word glosses or use words throughout; distinguish the rate characterization from equality of the prognostic and outcome-law minimax criteria.

objs: none

bib: none

home_objs: none
## section: Introduction

Organize the introduction around how many smooth pairwise prognostic interactions randomization can accommodate while attaining vanishing worst-case HT excess variance. Explain the scientific role of pooled component regularity, growing dimension, and assignment based on the observed original covariates. Preview the matched rate, simultaneous attainment across smoothness levels, and exact outcome-law interpretation under uniform sampling. Include a single factual sentence directing readers to the appendix verification note. Write the introduction after the substantive sections.

objs: none

bib: Horvitz1952, Imbens2015, Armstrong2022

home_objs: none
## section: Related work

Lead with the closest econometric comparison: \citet[Proposition 2.3, equation (2.4), Theorem B.8(ii), Lemma B.9, and Theorem 4.9]{Cytrynbaum2026Limits}. Compare its prognostic excess-variance identity, structured GSW upper rate, and fixed-dimensional lower exponent with the present all-dimension matched characterization under the specified uniform pooled class. Give the precise one-frequency saturation comparison supported by \citet[Theorem 1.2(2a)]{KoganNandyHuang2024Extremal}, then identify frequency-rich subcritical behavior and simultaneous smoothness attainment as the relevant additional scope. Situate the criterion within minimax experimental design and the construction within randomized balancing. Compare discrepancy-based integration results using their stated input-pool, retained-sample, function-class, and error criteria, and distinguish the joint design-and-estimator problem studied by Sudijono, Dobriban, and Tchetgen from the fixed HT criterion. Keep all novelty language tied to these particular comparisons.

objs: none

bib: Cytrynbaum2026Limits, KoganNandyHuang2024Extremal, Kallus2018, Kallus2020, HarshawSavjeSpielmanZhang2024GSW, LovettMeka2015EdgeWalk, BansalJiang2024QMC, ChenJiangKirk2025HighDimensionalQMC, EzeunalaJhaJiang2026QMCII, Dwivedi2019, Dwivedi2024, SudijonoDobribanTchetgen2026Minimax, Bai2022b, Bai2023

home_objs: none
## section: Setup and assumptions

Introduce the original-unit sampling and assignment family, canonical main and pair effects, and nonperiodic component restriction norms before their first formal use. Group the missing presentation definitions by sampling, component regularity, signing loss, and outcome-law interpretation. Explain centering, exact order-two specification, the pooled budget, conditional fairness, and outcome-independent assignment. Establish the order of the design optimization, fixed-function supremum, and sampling expectation. Define the law-specific causal criterion and benchmark sufficiently to make the main results independently readable, resolving the absent benchmark reference before drafting. Place the published-class inclusion result after both outcome-law classes have been introduced.

objs: ass:uniform-draw, synth_1, ass:order-two, ass:pooled-budget, ass:fair, ass:assignment-independence, def:sobolev-class, def:design-class, def:criterion, synth_5, synth_3, prop:published-class-inclusion

bib: Horvitz1952, Hoeffding1948, Sobol1993, Cytrynbaum2026Limits

home_objs: ass:uniform-draw, ass:order-two, ass:pooled-budget, ass:fair, ass:assignment-independence, def:sobolev-class, def:design-class, def:criterion, prop:published-class-inclusion
## section: Main results

Lead with the log-free capacity and dimension-frontier theorem as the single main-text headline. Organize interpretation around the subcritical regime, saturation, endpoint smoothness, and vanishing excess along arbitrary integer dimension sequences at fixed smoothness. Follow it with focused explanations of attainment, the independent-prior converse, and causal transfer. Place the full-design lower bound directly in the converse subsection. Keep the expanded capstone theorem in Appendix D with its anchor and verified content preserved. Explain exact equality of the prognostic and uniform outcome-law minimax criteria, and state the larger bounded-density class's inherited converse and necessary dimension condition affirmatively. Avoid repeating the omnibus characterization in narrative prose.

objs: synth_4, synth_2, thm:log-free-bivariate-capacity, thm:full-design-lower

bib: none

home_objs: thm:log-free-bivariate-capacity, thm:full-design-lower
## section: A smoothness-independent assignment procedure

Present the central assignment construction in the main body. Introduce the reflected sample, common shift, prescribed frequency ordering, and corresponding real features as one spectral-construction family before the procedure uses them. Give the reader an intuitive account of protecting successive low-frequency rows while preserving fair assignment probabilities, followed by the boxed ordered boundary-rounding procedure. Explain the independent-sign branch at saturation, retention of every original unit with its original HT weight, and the finite exact-real move guarantee. Connect the row-imbalance bound and spectral budget to simultaneous smoothness attainment through appendix cross-references; reserve proof details and measurable realization arguments for the appendix.

objs: def:cosine-prior, def:capacity-handle, def:ordered-boundary-rounding

bib: HarshawSavjeSpielmanZhang2024GSW, LovettMeka2015EdgeWalk

home_objs: def:capacity-handle, def:ordered-boundary-rounding
## section: Discussion and extensions

Interpret the paper's variance characterization as an interaction-count sample-size benchmark under the specified uniform sampling law. Use the Gaussian causal completion as a concrete calibration of actual HT excess above its stated benchmark, placing its complete potential-outcome, treatment, estimator, and target definitions before use. Explain the sufficient and necessary relative-excess sample-size inequalities as constant-factor implications of the main result. Interpret the broader bounded-density converse as a necessary condition for precision on that class. Include a clearly titled “Limitations and future work” subsection for nonuniform-density attainment, extensions beyond exact centered order-two prognosis, and finite-precision certification and bit complexity. Frame these as future directions rather than additional delivered results.

objs: def:causal-completion

bib: Horvitz1952

home_objs: def:causal-completion
## section: Appendix A: Causal variance identities and class transfer

Prove the conditional unbiasedness and covariance identity for the realized full schedule, then derive the Gaussian sampling-law excess identity. Establish the arbitrary square-integrable outcome-law identity, equality of attainable prognostic functions, equality of the minimax criteria, and the larger-class converse. Make the law-specific benchmark and the inclusion argument explicit. Keep the Gaussian completion's illustrative role distinct from the full uniform outcome-law transfer.

objs: lem:ht-transfer, lem:published-prognostic-capacity

bib: Cytrynbaum2026Limits, Horvitz1952

home_objs: lem:ht-transfer, lem:published-prognostic-capacity
## section: Appendix B: Spectral budget and assignment bounds

Prove the exact nonperiodic reflection-budget inequality before using it in the broader reflection-and-shift transfer. Introduce appendix-local component Fourier notation immediately before use. Develop the common-shift diagonalization and its extension to the allowed Borel representatives. Prove the rounding procedure's measurability, termination, marginal fairness, and ordered-row second-moment bounds, then assemble the attaining-design bound. Keep local projection, basis, and boundary-step calculations subordinate to the mathematical argument.

objs: lem:exact-reflection-budget, lem:reflection-transfer, lem:ordered-prefix-rounding

bib: ChandlerWildeHewettMoiola2015Interpolation, LovettMeka2015EdgeWalk, HarshawSavjeSpielmanZhang2024GSW

home_objs: lem:exact-reflection-budget, lem:reflection-transfer, lem:ordered-prefix-rounding
## section: Appendix C: Independent-prior converse

Introduce the full pair-cosine feature and coefficient-prior family, including its normalization and dimension, immediately before the frozen prior definition. Prove prior legality and feature isotropy, including pairs sharing an original coordinate. Introduce the appendix-local isotropic-vector family before the signing lemma, then derive the expected sign-minimum bound and apply it to the prior. Complete the lower-bound argument with the function drawn independently before sampling and the supremum taken over fixed functions.

objs: lem:cosine-prior, lem:isotropic-row-signing

bib: BartlettMendelson2002Complexities

home_objs: def:cosine-prior, lem:cosine-prior, lem:isotropic-row-signing
## section: Appendix D: Proof assembly and verification note

State the expanded complete-capacity capstone theorem here, preserving its anchor and verified content, after the focused main-text result. Collect the remaining deductions connecting the two bounds, the fixed-smoothness dimension equivalence, the outcome-law capacity equality, and the relative-excess sample-size implications without restating the capstone. End with a brief verification note consolidating the Lean machine-checking scope for the frozen results, distinguishing stipulated model assumptions from proved conclusions, and recording cited dependencies according to their theorem-local verification disclosures. Keep declaration names and other proof-engineering material within this note. The note should report the supplied verification scope without adding claims about checks performed during manuscript planning.

objs: thm:capacity-answer

bib: none
home_objs: thm:capacity-answer
