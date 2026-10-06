# Title
**Parametric rates for stationary policy evaluation with binary hidden states**

**Contribution statement.** For a single stationary trajectory with binary observed states, hidden states, and actions, known policies randomized through the observed state, bounded action likelihood ratios, and contracting behavior and target transitions, the paper establishes the minimax mean-squared-error rate through a stable seven-moment value characterization and a finite observed-data estimator.

# Notation

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(T\) | \(T\) | Observed trajectory length | Notation gap |
| \(S_t\) | \(S_t\) | Joint observed and hidden state at time \(t\) | Notation gap |
| \(S_{t+1}\) | \(S_{t+1}\) | Joint state following the action at time \(t\) | Notation gap |
| \(S_1\) | \(S_1\) | Initial joint state | Notation gap |
| \(X_t\) | \(X_t\) | Observed state at time \(t\) | Notation gap |
| \(A_t\) | \(A_t\) | Action at time \(t\) | Notation gap |
| \(Y_t\) | \(Y_t\) | Bounded reward at time \(t\) | Notation gap |
| \(\mathcal F_t^-\) | \(\mathcal F_t^-\) | Full pre-action history information | Notation gap |
| \(\mathcal S\) | \(\mathcal S\) | Four-point joint-state space | Notation gap |
| \(\mathcal Y\) | \(\mathcal Y\) | Reward space \([0,1]\) | def:binary-pomdp-class |
| \(K(\cdot\mid S_t,A_t)\) | \(K(\cdot\mid S_t,A_t)\) | Conditional joint reward and next-state distribution | Notation gap |
| \(K(dy,s'\mid s,a)\) | \(K(dy,s'\mid s,a)\) | Joint reward and next-state transition law | Notation gap |
| \(b(a\mid X_t)\) | \(b(a\mid X_t)\) | Known behavior action probability at the observed state | Notation gap |
| \(b(a\mid x)\) | \(b(a\mid x)\) | Known behavior action probability in observed state \(x\) | Notation gap |
| \(e(a\mid x)\) | \(e(a\mid x)\) | Known target action probability in observed state \(x\) | Notation gap |
| \(P_b\) | \(P_b\) | Joint-state transition matrix induced by the behavior policy | Notation gap |
| \(P_e\) | \(P_e\) | Joint-state transition matrix induced by the target policy | Notation gap |
| \(d_b\) | \(d_b\) | Stationary joint-state law under the behavior policy | Notation gap |
| \(d_e\) | \(d_e\) | Stationary joint-state law under the target policy | Notation gap |
| \(r_e\) | \(r_e\) | Joint-state vector of target-policy conditional mean rewards | Notation gap |
| \(\mathsf O_T\) | \(\mathsf O_T\) | Observed state, action, and reward trajectory | Notation gap |
| \(t_0\) | \(t_0\) | Fixed mixing-scale parameter | Notation gap |
| \(\zeta\) | \(\zeta\) | Fixed logarithmic action likelihood-ratio bound | Notation gap |
| \(\alpha\) | \(\alpha\) | Contraction bound associated with the mixing scale | Notation gap |
| \(L\) | \(L\) | Action likelihood-ratio bound associated with \(\zeta\) | Notation gap |
| \(\Delta(\mathcal S)\) | \(\Delta(\mathcal S)\) | Probability simplex on the joint-state space | Notation gap |
| \(\|\mu P_b-\mu'P_b\|_{\mathrm{TV}}\) | \(\|\mu P_b-\mu'P_b\|_{\mathrm{TV}}\) | Total variation distance between behavior-transition images | Notation gap |
| \(\|\mu P_e-\mu'P_e\|_{\mathrm{TV}}\) | \(\|\mu P_e-\mu'P_e\|_{\mathrm{TV}}\) | Total variation distance between target-transition images | Notation gap |
| \(\mathcal M_T^{(2)}(t_0,\zeta)\) | \(\mathcal M_T^{(2)}(t_0,\zeta)\) | Binary-state and binary-action experiments satisfying the six law conditions | def:binary-pomdp-class |
| \(\mathrm A_{\mathrm{kernel}}\) | \(\mathrm A_{\mathrm{kernel}}\) | Predicate for the joint reward and next-state law condition | Notation gap |
| \(\mathrm A_{\mathrm{ign}}\) | \(\mathrm A_{\mathrm{ign}}\) | Predicate for observed-state sequential assignment | Notation gap |
| \(\mathrm A_{\mathrm{start}}\) | \(\mathrm A_{\mathrm{start}}\) | Predicate for a stationary behavior-policy start | Notation gap |
| \(\mathrm A_{\mathrm{overlap}}\) | \(\mathrm A_{\mathrm{overlap}}\) | Predicate for bounded action likelihood ratios | Notation gap |
| \(\mathrm A_{b\text{-}\mathrm{mix}}\) | \(\mathrm A_{b\text{-}\mathrm{mix}}\) | Predicate for behavior-transition contraction | Notation gap |
| \(\mathrm A_{e\text{-}\mathrm{mix}}\) | \(\mathrm A_{e\text{-}\mathrm{mix}}\) | Predicate for target-transition contraction | Notation gap |
| \(\theta(K,e)\) | \(\theta(K,e)\) | Target-policy stationary mean reward | def:target-value |
| \(\theta\) | \(\theta\) | Stationary target value with the experiment and target policy understood | def:target-value |
| \(\rho_j\) | \(\rho_j\) | Observed action likelihood ratio at time \(j\), including its zero-cell convention | Notation gap |
| \(Z_t(k)\) | \(Z_t(k)\) | Reward weighted by the action likelihood ratios from \(t-k\) through \(t\) | def:observable-moments |
| \(m_k\) | \(m_k\) | Behavior-law expectation of the weighted reward score | def:observable-moments |
| \(\widehat m_k\) | \(\widehat m_k\) | Common-window empirical weighted reward moment | def:observable-moments |
| \(\mathbb E_b\) | \(\mathbb E_b\) | Expectation under the stationary behavior experiment | Notation gap |
| \(M\) | \(M\) | Grid resolution selected from trajectory length and contraction | def:stable-grid-estimator |
| \(\mathcal G_M\) | \(\mathcal G_M\) | Four-simplex grid with coordinates that are integer multiples of \(M^{-1}\) | def:stable-grid-estimator |
| \(\mathbf1\) | \(\mathbf1\) | Four-dimensional vector of ones | Notation gap |
| \(U\) | \(U\) | Four-state uniform transition matrix | def:stable-grid-estimator |
| \(\lambda\) | \(\lambda\) | Mixing weight that contracts the gridded transition matrix toward \(U\) | def:stable-grid-estimator |
| \(\nu\) | \(\nu\) | Initial probability vector in a four-state scalar realization | Notation gap |
| \(\nu'\) | \(\nu'\) | Initial probability vector in the comparison realization | Notation gap |
| \(R\) | \(R\) | Row-stochastic grid candidate before stabilization | def:stable-grid-estimator |
| \(P\) | \(P\) | Contracting four-state transition matrix, specialized to the stabilized candidate in the estimator | Notation gap |
| \(P'\) | \(P'\) | Contracting four-state transition matrix in the comparison realization | Notation gap |
| \(r\) | \(r\) | Four-state reward vector with entries in \([0,1]\) | Notation gap |
| \(r'\) | \(r'\) | Reward vector of the comparison realization | Notation gap |
| \(\delta(R)\) | \(\delta(R)\) | Dobrushin contraction coefficient of the grid candidate | Notation gap |
| \(\delta(P)\) | \(\delta(P)\) | Dobrushin contraction coefficient of a transition matrix | Notation gap |
| \(\delta(P')\) | \(\delta(P')\) | Dobrushin contraction coefficient of the comparison transition matrix | Notation gap |
| \(\pi(P)\) | \(\pi(P)\) | Stationary probability vector of the stabilized transition matrix | def:stable-grid-estimator |
| \(\pi\) | \(\pi\) | Stationary probability vector of \(P\) in the comparison lemma | Notation gap |
| \(\pi'\) | \(\pi'\) | Stationary probability vector of \(P'\) in the comparison lemma | Notation gap |
| \(\widehat\theta_T\) | \(\widehat\theta_T\) | Stationary reward of the lexicographically selected stable moment fit | def:stable-grid-estimator |
| \(R_T^{(2)}(t_0,\zeta)\) | \(R_T^{(2)}(t_0,\zeta)\) | Worst-case mean-squared error minimized over observed-data estimators | def:minimax-risk |
| \(\widetilde\theta\) | \(\widetilde\theta\) | Arbitrary measurable estimator in the observed-data decision problem | def:minimax-risk |
| \(\sigma(\mathsf O_T,b,e,t_0,\zeta)\) | \(\sigma(\mathsf O_T,b,e,t_0,\zeta)\) | Information available to an estimator from the trajectory and supplied inputs | Notation gap |
| \(\mathbb E_M\) | \(\mathbb E_M\) | Expectation under an experiment indexed by \(M\) | Notation gap |
| \(v_T\) | \(v_T\) | Testing perturbation amplitude indexed by trajectory length | Notation gap |
| \(v\in\{-v_T,+v_T\}\) | \(v\in\{-v_T,+v_T\}\) | Signed perturbation indexing the two testing experiments | def:four-state-testing-family |
| \(E(x\mid h)\) | \(E(x\mid h)\) | Binary observation probabilities conditional on the hidden state | def:four-state-testing-family |
| \(q_v(h)\) | \(q_v(h)\) | Hidden-state-dependent Bernoulli reward probability | def:four-state-testing-family |
| \(p(a)\) | \(p(a)\) | Action-dependent probability of the next hidden state being one | def:four-state-testing-family |
| \(\operatorname{Ber}_{q_v(h)}(y)\) | \(\operatorname{Ber}_{q_v(h)}(y)\) | Bernoulli mass at \(y\) with reward probability \(q_v(h)\) | Notation gap |
| \(\operatorname{Ber}_{p(a)}(h')\) | \(\operatorname{Ber}_{p(a)}(h')\) | Bernoulli mass at \(h'\) with transition probability \(p(a)\) | Notation gap |
| \(K_v^{(T)}(y,x',h'\mid x,h,a)\) | \(K_v^{(T)}(y,x',h'\mid x,h,a)\) | Positive joint reward and next-state law in the testing family | def:four-state-testing-family |
| \(\mathfrak H_{\mathrm{poly}}\) | \(\mathfrak H_{\mathrm{poly}}\) | Cost-certified rank-adaptive stable fitting problem | def:polynomial-time-handle |
| \(\widehat m_{i+j+1}-\widehat m_{i+j}\) | \(\widehat m_{i+j+1}-\widehat m_{i+j}\) | Entries of the empirical moment-difference Hankel matrix | def:polynomial-time-handle |
| \(Q_{P,P'}(1)\) | \(Q_{P,P'}(1)\) | Pair transient characteristic polynomial evaluated at one | Notation gap |
| \(Q_k\) | \(Q_k\) | Degree-\(k\) coefficient of the pair transient characteristic polynomial | Notation gap |
| \(B_\alpha\) | \(B_\alpha\) | Uniform stationary-value modulus constant | Notation gap |
| \(V_{\alpha,L}\) | \(V_{\alpha,L}\) | Moment variance bound constant | Notation gap |
| \(\mathbb P_{+}^{\mathsf O_T}\) | \(\mathbb P_{+}^{\mathsf O_T}\) | Observed trajectory law under the positive testing perturbation | Notation gap |
| \(\mathbb P_{-}^{\mathsf O_T}\) | \(\mathbb P_{-}^{\mathsf O_T}\) | Observed trajectory law under the negative testing perturbation | Notation gap |
| \(\operatorname{KL}(\mathbb P_{+}^{\mathsf O_T}\Vert\mathbb P_{-}^{\mathsf O_T})\) | \(\operatorname{KL}(\mathbb P_{+}^{\mathsf O_T}\Vert\mathbb P_{-}^{\mathsf O_T})\) | Relative entropy between the two observed trajectory laws | Notation gap |
| \(C\) | \(C\) | Stationary occupancy-ratio bound in the comparator class | Notation gap |
| \(\beta\) | \(\beta\) | Cardinality-uniform rate exponent defined in the minimax statement | Notation gap |
| \(q_C\) | \(q_C\) | Stationary-overlap radius appearing in the cited comparator rate | Notation gap |
| \(Q\) | \(Q\) | Depth index of the cited growing-hidden-state lower construction | Notation gap |

notation_gaps: \(T\)=trajectory length lacks an anchored introduction; \(S_t,S_{t+1},S_1,X_t,A_t,Y_t,\mathcal F_t^-,\mathcal S,\mathsf O_T\)=experiment variables and information structure lack an anchored definition; \(K(\cdot\mid S_t,A_t),K(dy,s'\mid s,a)\)=the joint transition law is restricted by an assumption but lacks a defining environment; \(b(a\mid X_t),b(a\mid x),e(a\mid x),P_b,P_e,d_b,d_e,r_e\)=policy probabilities and induced transition, stationary-law, and reward objects lack anchored definitions; \(t_0,\zeta,\alpha,L\)=the regime convention and parameter relations lack a defining environment; \(\Delta(\mathcal S),\|\mu P_b-\mu'P_b\|_{\mathrm{TV}},\|\mu P_e-\mu'P_e\|_{\mathrm{TV}}\)=simplex and total variation conventions lack an anchored home; \(\mathrm A_{\mathrm{kernel}},\mathrm A_{\mathrm{ign}},\mathrm A_{\mathrm{start}},\mathrm A_{\mathrm{overlap}},\mathrm A_{b\text{-}\mathrm{mix}},\mathrm A_{e\text{-}\mathrm{mix}}\)=the class definition names predicates whose mathematical restrictions reside in assumption environments; \(\rho_j\)=the likelihood ratio and its zero-behavior-cell convention lack a definition; \(\mathbb E_b,\mathbb E_M\)=behavior-law and experiment-indexed expectation conventions lack an anchored introduction; \(\mathbf1\)=the vector dimension lacks an explicit definition; \(\nu,\nu',P,P',r,r',\pi,\pi'\)=the general four-state realization objects used by the modulus lemma lack a defining environment; \(\delta(R),\delta(P),\delta(P')\)=the Dobrushin coefficient lacks a definition; \(\sigma(\mathsf O_T,b,e,t_0,\zeta)\)=the measurable-estimator information convention lacks a defining environment; \(v_T\)=the testing amplitude lacks a definition; \(\operatorname{Ber}_{q_v(h)}(y),\operatorname{Ber}_{p(a)}(h')\)=the Bernoulli mass convention lacks an anchored home; \(Q_{P,P'}(1),Q_k,B_\alpha\)=the pair polynomial, its coefficients, and the modulus constant lack definitions; \(V_{\alpha,L}\)=the upper-bound variance constant lacks a definition; \(\mathbb P_{+}^{\mathsf O_T},\mathbb P_{-}^{\mathsf O_T},\operatorname{KL}(\mathbb P_{+}^{\mathsf O_T}\Vert\mathbb P_{-}^{\mathsf O_T})\)=testing-law and relative-entropy conventions lack an anchored definition; \(C,\beta,q_C,Q\)=the cited-comparison notation lacks a presentation definition, although the exponent formula appears in the minimax statement.

env_overrides: def:stable-grid-estimator=algorithmv, prop:coincident-policy-reduction=propositionv, prop:exhaustive-grid-arithmetic-complexity=propositionv, oeq:polynomial-time-attainment=remarkv

# Sections

## section: Abstract

Plan the abstract around stationary policy evaluation from one logged trajectory, the fixed binary experiment, the seven-moment mechanism, and the matched minimax characterization. State the policy-assignment, action-overlap, contraction, and stationary-start conditions in words. Describe the estimator as a finite stable moment fit and distinguish its statistical guarantee from candidate-list cardinality through affirmative scope. Use words for quantities whose formal definitions occur later. Draft this section after the body and proofs.

objs: none

bib: none

home_objs: none
## section: Introduction

Organize the introduction around the scientific question: how fixed hidden-state dimension affects estimation of a long-run policy value under partial observation. Explain the distinction between recovering latent parameters and estimating a stationary scalar value, then preview the observable-moment route and the matched statistical rate for the specified binary experiment. Highlight uniformity across emission degeneracy and small stationary cells as features of the value characterization. Include one factual sentence directing readers to the appendix verification note. Reserve detailed literature comparisons for the immediately following section, and draft the introduction last.

objs: none

bib: Puterman1994, Robins1986, Murphy2003

home_objs: none
## section: Related work

Lead with the closest stationary-trajectory comparisons: \citet[Theorem 2.1, Corollary 2.2, and Theorem 3.1]{HuWager2023} and \citet[Theorem 1 and the signed-depth lower-bound construction]{CausalSmithLatentOverlap2026}. Identify the latter explicitly as a nonarchival public manuscript whose cited conclusion is an external premise, rather than peer-reviewed or independently formalized evidence. Make fixed versus growing hidden cardinality the precise comparison between their minimax experiments and this paper’s binary experiment. Compare the sampling schemes and information conditions of \citet[Section 4, Assumptions 2--4, and Theorems 2--4]{NairJiang2021} and \citet[Section 4 and Theorems 7--8]{ShiUeharaHuangJiang2022} with observed-state randomization and uniform scalar-value stability here. Connect the finite-moment mechanism to realization theory and the distinction between functional estimation and latent-parameter learning. Use the fully observed stationary and weak-overlap results as benchmarks with their estimands, overlap conditions, and nuisance requirements stated precisely. Frame novelty as the particular matched fixed-binary characterization established by this paper. Use only the verified bibliography keys listed for this section.

objs: none

bib: HuWager2023, CausalSmithLatentOverlap2026, NairJiang2021, ShiUeharaHuangJiang2022, BennettKallus2023, KallusUehara2022, Mehrabi2024, Ho1966, Carlyle1971, HsuKakadeZhang2012, AbrahamGassiatNaulet2023, Donoho1991, Uehara2023, Zhang2024

home_objs: none
## section: Setup and assumptions

Introduce the observed trajectory, joint-state representation, known behavior and target policies, joint reward and next-state distribution, induced transitions, and stationary reward target before presenting their restrictions. Group the missing experiment and regime notation into presentation definitions immediately before first use. Explain observed-state randomization, stationary initialization, action likelihood-ratio control, and contraction as distinct conditions. Establish the binary experiment class and its stationary estimand. Keep generic comparison realizations and testing-family apparatus in the appendix.

objs: ass:pomdp-kernel, ass:sequential-ignorability, ass:stationary-start, ass:policy-overlap, ass:behavior-contraction, ass:target-contraction, def:binary-pomdp-class, def:target-value

bib: Puterman1994, Robins1986, Precup2000

home_objs: ass:pomdp-kernel, ass:sequential-ignorability, ass:stationary-start, ass:policy-overlap, ass:behavior-contraction, ass:target-contraction, def:binary-pomdp-class, def:target-value
## section: Main results

Start with the observable weighted moments and their action-window convention, then introduce the central stable-grid procedure in a numbered algorithm. Define the observed-data minimax decision problem and present the estimator guarantee and matched minimax result. Develop intuition for the proof through finite-state recurrence, stable extrapolation to the stationary value, and control of empirical moments from overlapping windows, with references to \cref{lem:pair-polynomial-modulus,lem:observable-intervention-moments}. Present the coincident-policy reduction as a familiar special case that clarifies the estimand and the role of the lower-bound experiment. Define the constants and external-comparison notation immediately before their first appearance. State explicitly that the cardinality-uniform comparator conclusion is an external premise supplied by \citet{CausalSmithLatentOverlap2026}; do not present it as a Lean-proved or unconditional conclusion of this paper. Explain the fixed-cardinality comparison with exact citation locators at its theorem consumer.

objs: def:observable-moments, def:stable-grid-estimator, def:minimax-risk, thm:stable-grid-upper, def:four-state-testing-family, thm:fixed-binary-minimax, prop:coincident-policy-reduction

bib: HuWager2023, CausalSmithLatentOverlap2026, Seneta1981, Tsybakov2009

home_objs: def:observable-moments, def:stable-grid-estimator, def:minimax-risk, thm:stable-grid-upper, def:four-state-testing-family, thm:fixed-binary-minimax, prop:coincident-policy-reduction
## section: Discussion

Interpret the statistical characterization in terms of the stability of a stationary functional across latent-model degeneracies. Explain how fixed joint-state dimension supplies a bounded recurrence and how action weighting connects that recurrence to observed data. Place the exact candidate-list count here to quantify the scale of the displayed estimator, treating cardinality as the established computational descriptor. Discuss the scope across stationary-overlap subclasses and the on-policy reduction through references to the paper’s own results.

objs: prop:exhaustive-grid-arithmetic-complexity

bib: none

home_objs: prop:exhaustive-grid-arithmetic-complexity
## section: Limitations and future work

Separate the proved statistical and candidate-cardinality conclusions from runtime, arithmetic cost, bit complexity, and precision guarantees. Introduce the cost-certified rank-adaptive fitting problem and its open-question formulation, emphasizing global objective certification across rank-deficient strata. Record the additional open directions identified by the research scope: the minimal sufficient window, limit distributions, confidence intervals, and application-specific calibration. Identify broader hidden-cardinality models as a further statistical extension while preserving the conditions of the fixed-binary results.

objs: def:polynomial-time-handle, oeq:polynomial-time-attainment

bib: none

home_objs: def:polynomial-time-handle, oeq:polynomial-time-attainment
## section: Appendix: Proofs and verification scope

Organize proofs by their mathematical dependencies: define the generic four-state realization and pair-polynomial apparatus before the value-modulus lemma; prove the intervention-moment identity and dependence bounds; develop rounding and fitting arguments for the estimator guarantee; introduce the positive testing family and its notation immediately before membership and testing calculations; then assemble the minimax proof and prove the coincident-policy and candidate-cardinality results. Keep the testing construction and generic linear-algebra apparatus here because their detailed content serves the proofs. End with a brief verification note consolidating which internal mathematical results are Lean-checked, which data-generating restrictions are assumed, and which published comparison inputs remain cited dependencies, preserving generated theorem-local trust-boundary disclosures.

objs: lem:pair-polynomial-modulus, lem:observable-intervention-moments, lem:testing-family-membership

bib: Seneta1981, Tsybakov2009, HuWager2023, CausalSmithLatentOverlap2026
home_objs: lem:pair-polynomial-modulus, lem:observable-intervention-moments, lem:testing-family-membership
