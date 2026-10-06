# Title
**Optimal treatment welfare under local privacy: Minimax estimation and honest inference**

**Contribution statement.** For binary randomized trials with known uniform stratum probabilities, fair assignment, and bounded interior arm means, the paper characterizes finite-resource minimax squared error and globally honest connected-interval length for first-best welfare under pure local privacy, establishes matching orders for noninteractive and one-message sequential protocols, and derives matching paired-uniform total-variation orders and full-simplex lower bounds.

env_overrides: def:frontier-handle=algorithmv, prop:signed-causal-bridge=propositionv

notation_gaps: \(\mathcal P_d\)=ambient full-data law class lacks an anchored definition, \(X,A,Y,Y^0,Y^1,Y^{\mathrm{pot}}_A\)=record and potential-outcome variables lack an anchored definition, \(O,P_O,\mathbf O\)=observed record and sample lack an anchored definition, \(\mu_{aj}(P),\tau_j(P),\tau(P),B(P),V(P)\)=causal means contrasts baseline and optimal welfare lack an anchored definition, \(S,P_\theta,\mathsf U_{2d},F(\theta),F(\tau(P))\)=signed statistic signed law uniform reference and absolute-contrast functional lack a complete anchored definition, \(R,U,\lambda,\mathbf Z,\mathcal H_i,\mathcal Z_i,T,I\)=protocol spaces randomness transcript and decision domains lack an anchored definition, \(\mathfrak Q_{\mathcal C}\)=class selector lacks an anchored definition, \(\delta,b,W_{ij},W\)=privacy attenuation scale and scaled messages lack an anchored definition, \(p^Q(\theta,r),\beta,\nu_0,\nu_1,\mathsf M_0^Q,\mathsf M_1^Q\)=converse density scale moment-matching measures and mixture laws lack an anchored definition, \(T_j^{\mathrm{col}}\)=deterministic column-statistic family lacks an anchored definition, \(r_{\mathcal C}(n,d,\varepsilon),h_{\mathcal C}(n,d,\varepsilon)\)=rate functions are introduced in a theorem rather than an anchored definition, \(q_D(x),a_{Dv}\)=approximation polynomial and coefficients are introduced in a cited-result environment rather than an anchored definition, \(p_{a,D}(x),\widehat p_{a,D,j},H_j\)=calibration polynomial and statistics are introduced in a lemma rather than an anchored definition, \(\xi_0,\xi_1,e_K\)=moment-duality measures and approximation error lack an anchored definition, \(N_0,N_1,v_0,v_1,\Delta,\eta_0,\omega\)=decision-reduction mixtures centers separation and error bounds lack an anchored definition, \(H,Z,K,L,f\)=measurable-kernel auxiliary spaces kernels and density are local to a cited-result environment, \(H_1,\ldots,H_m\)=bounded concentration variables are local to a cited-result environment

# Notation

The plan preserves frozen mathematical notation. “Gap” refers to the corresponding entry above; synthesis should introduce related objects together immediately before their first use. Local bound indices and ordinary scalar parameters retain their frozen meanings.

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(\mathcal P_d\) | \(\mathcal P_d\) | Full-data probability laws on the declared finite causal record space | Gap; setup |
| \(P\) | \(P\) | A full-data law in the ambient causal model | Gap; setup |
| \(X\) | \(X\) | Participant stratum in \([d]\) | Gap; setup |
| \(A\) | \(A\) | Binary randomized treatment assignment | Gap; setup |
| \(Y\) | \(Y\) | Binary observed outcome | Gap; setup |
| \(Y^0\) | \(Y^0\) | Binary potential outcome under treatment zero | Gap; setup |
| \(Y^1\) | \(Y^1\) | Binary potential outcome under treatment one | Gap; setup |
| \(Y^{\mathrm{pot}}_A\) | \(Y^{\mathrm{pot}}_A\) | Potential outcome selected by the realized assignment | Gap; setup |
| \(O=(j,A,Y)\) | \(O=(j,A,Y)\) | Observed participant record with realized stratum \(j\) | Gap; setup |
| \(P_O\) | \(P_O\) | Observed-record marginal law induced by \(P\) | Gap; setup |
| \(\mathbf O\) | \(\mathbf O\) | Vector of independent observed participant records | Gap; setup |
| \(\mu_{aj}(P)\) | \(\mu_{aj}(P)\) | Conditional potential-outcome mean for arm \(a\) and stratum \(j\) | Gap; setup |
| \(\tau_j(P)\) | \(\tau_j(P)\) | Difference between the two arm means in stratum \(j\) | Gap; setup |
| \(\tau(P)\) | \(\tau(P)\) | Vector of stratum-specific arm-mean differences | Gap; setup |
| \(B(P)\) | \(B(P)\) | Population mean observed outcome under fair assignment | Gap; setup |
| \(V(P)\) | \(V(P)\) | Average of the larger arm mean in each stratum | Gap; setup |
| \(\mathcal V_d\) | \(\mathcal V_d\) | Full-data laws satisfying uniform strata, fair assignment, consistency, and interior means | def:causal-model |
| \(S\) | \(S\) | Signed treatment-outcome statistic \((2A-1)(2Y-1)\) | Gap; setup |
| \(P_\theta\) | \(P_\theta\) | Paired signed law with probabilities \((1+s\theta_j)/(2d)\) | Gap; setup |
| \(\mathsf U_{2d}\) | \(\mathsf U_{2d}\) | Uniform reference law on the paired \(2d\)-symbol alphabet | Gap; setup |
| \(F(\theta)\) | \(F(\theta)\) | Average absolute coordinate magnitude of the contrast vector | Gap; setup |
| \(F(\tau(P))\) | \(F(\tau(P))\) | Average absolute treatment contrast under \(P\) | Gap; setup |
| \(G_\theta\) | \(G_\theta\) | Symmetric causal law generated by the specified potential outcomes and fair assignment | def:symmetric-law |
| \(V(G_\theta)\) | \(V(G_\theta)\) | First-best welfare evaluated at the symmetric causal law | Gap for \(V\); def:symmetric-law for \(G_\theta\) |
| \(Q=(Q_i)_{i=1}^n\) | \(Q=(Q_i)_{i=1}^n\) | Sequence of participant-specific private message kernels | def:sequential-class |
| \(Q_i\) | \(Q_i\) | Participant message kernel conditional on record, history, and public seed | def:sequential-class; domain gap |
| \(\mathcal H_i\) | \(\mathcal H_i\) | Product space of messages preceding participant \(i\) | Gap; setup |
| \(\mathcal Z_i\) | \(\mathcal Z_i\) | Standard-Borel message space for participant \(i\) | Gap; setup |
| \(R\) | \(R\) | Shared public seed independent of the records | Gap; setup |
| \(\lambda\) | \(\lambda\) | Probability law of the public seed | Gap; setup |
| \(U\) | \(U\) | Independent uniform analyst randomizer | Gap; setup |
| \(\mathbf Z\) | \(\mathbf Z\) | Vector of private participant messages | Gap; setup |
| \(\mathfrak Q_{\mathrm{SI}}(n,d,\varepsilon)\) | \(\mathfrak Q_{\mathrm{SI}}(n,d,\varepsilon)\) | One-message sequential protocols satisfying pure full-record local privacy | def:sequential-class |
| \(\mathfrak Q_{\mathrm{NI}}(n,d,\varepsilon)\) | \(\mathfrak Q_{\mathrm{NI}}(n,d,\varepsilon)\) | Sequential-class protocols whose kernels are constant in message history | def:noninteractive-class |
| \(\mathfrak Q_{\mathcal C}\) | \(\mathfrak Q_{\mathcal C}\) | Protocol class selected by \(\mathcal C\in\{\mathrm{NI},\mathrm{SI}\}\) | Gap; setup |
| \(T(\mathbf Z,R,U)\) | \(T(\mathbf Z,R,U)\) | Borel real-valued welfare estimate based on the transcript and randomizers | Gap; setup |
| \(I(\mathbf Z,R,U)\) | \(I(\mathbf Z,R,U)\) | Connected closed welfare interval with ordered Borel endpoints in \([1/4,3/4]\) | Gap; setup |
| \(\mathfrak R_{\mathcal C}(n,d,\varepsilon)\) | \(\mathfrak R_{\mathcal C}(n,d,\varepsilon)\) | Minimax squared-error risk over admissible protocols and welfare estimates | def:risk |
| \(\mathfrak H_{\mathcal C}(n,d,\varepsilon)\) | \(\mathfrak H_{\mathcal C}(n,d,\varepsilon)\) | Minimax worst-law expected interval length under global coverage \(0.90\) | def:honest-length |
| \(\delta\) | \(\delta\) | Privacy attenuation \(\tanh(\varepsilon/2)\) | Gap; attaining procedure |
| \(b\) | \(b\) | Scaled-message magnitude \(d/\delta\) | Gap; attaining procedure |
| \(Q^{\mathrm{vec}}(z\mid O=(j,A,Y))\) | \(Q^{\mathrm{vec}}(z\mid O=(j,A,Y))\) | Sign-vector message law with density tilt \(\delta S z_j\) | def:vector-kernel |
| \(W_{ij}\) | \(W_{ij}\) | Coordinate \(j\) of participant \(i\)'s sign-vector message multiplied by \(b\) | Gap; attaining procedure |
| \(W\) | \(W\) | Matrix of scaled sign-vector messages | Gap; attaining procedure |
| \(\mathsf U_{kj}\) | \(\mathsf U_{kj}\) | Average product of scaled coordinate messages over distinct-person subsets of size \(k\) | def:private-moments |
| \(\mathsf U_{0j}\) | \(\mathsf U_{0j}\) | Zeroth-order private moment equal to one | def:private-moments |
| \(\mathscr H\) | \(\mathscr H\) | Fixed public-resource welfare procedure and specified converse tuning choices | def:frontier-handle |
| \(\eta_*\) | \(\eta_*\) | Fixed numerical polynomial-degree calibration constant \(1/1024\) | def:frontier-handle |
| \(L_0\) | \(L_0\) | Fixed log-dimension threshold \(4096\) | def:frontier-handle |
| \(t\) | \(t\) | Effective private resource \(n\varepsilon^2\) | def:frontier-handle |
| \(L\) | \(L\) | Log-dimension factor \(\log(ed)\) | def:frontier-handle |
| \(z_*\) | \(z_*\) | Resource ratio \(d^2L/t\) | def:frontier-handle |
| \(w\) | \(w\) | Logarithmic resource-ratio transform \(\log(e+z_*)\) | def:frontier-handle |
| \(\rho(t,d)\) | \(\rho(t,d)\) | Evaluated piecewise squared-error rate as a function of resource and dimension | def:frontier-handle |
| \(m\) | \(m\) | Size \(\lfloor n/3\rfloor\) of each vector-message block when \(n>2\) | def:frontier-handle |
| \(m_0\) | \(m_0\) | Baseline-message block size \(n-2m\) | def:frontier-handle |
| \(\mathsf H_i\) | \(\mathsf H_i\) | Binary randomized-response message for baseline-block participant \(i\) | def:frontier-handle |
| \(\widehat B\) | \(\widehat B\) | Baseline mean estimate formed from binary private messages | def:frontier-handle |
| \(W^{\mathrm{pil}}\) | \(W^{\mathrm{pil}}\) | Scaled-message matrix from the pilot block | def:frontier-handle |
| \(W^{\mathrm{ev}}\) | \(W^{\mathrm{ev}}\) | Scaled-message matrix from the evaluation block | def:frontier-handle |
| \(W^{\mathrm{pil}}_{ij}\) | \(W^{\mathrm{pil}}_{ij}\) | Pilot-block scaled message for participant \(i\) and coordinate \(j\) | def:frontier-handle |
| \(W^{\mathrm{ev}}_{ij}\) | \(W^{\mathrm{ev}}_{ij}\) | Evaluation-block scaled message for participant \(i\) and coordinate \(j\) | def:frontier-handle |
| \(\sigma^2\) | \(\sigma^2\) | Coordinate mean noise scale \(b^2/m\) | def:frontier-handle |
| \(\sigma\) | \(\sigma\) | Positive square root of the coordinate mean noise scale | def:frontier-handle |
| \(H\) | \(H\) | Polynomial variance calibration factor \(\log(e+\sigma^2L)\) | def:frontier-handle |
| \(M_j\) | \(M_j\) | Pilot-block average of scaled coordinate messages | def:frontier-handle |
| \(\overline W_j\) | \(\overline W_j\) | Evaluation-block average of scaled coordinate messages | def:frontier-handle |
| \(D\) | \(D\) | Even polynomial degree selected by the procedure's applicable branch | def:frontier-handle |
| \(\mathcal T_0(x)\) | \(\mathcal T_0(x)\) | Zeroth Chebyshev polynomial equal to one | def:frontier-handle |
| \(\mathcal T_1(x)\) | \(\mathcal T_1(x)\) | First Chebyshev polynomial equal to its argument | def:frontier-handle |
| \(\mathcal T_{v+1}(x)\) | \(\mathcal T_{v+1}(x)\) | Chebyshev polynomial generated by the displayed recurrence | def:frontier-handle |
| \(p_D^{\mathrm{abs}}(x)\) | \(p_D^{\mathrm{abs}}(x)\) | Explicit even-degree Chebyshev approximation to absolute value | def:frontier-handle |
| \(c_{D,v}\) | \(c_{D,v}\) | Monomial coefficient of the procedure's absolute-value polynomial | def:frontier-handle |
| \(a_{\mathrm{rad}}\) | \(a_{\mathrm{rad}}\) | Positive approximation radius selected by the applicable procedure branch | def:frontier-handle |
| \(\mathsf U_{vj}\) | \(\mathsf U_{vj}\) | Evaluation-block distinct-person moment of degree \(v\) | def:private-moments; block specified in def:frontier-handle |
| \(\widehat p_{a_{\mathrm{rad}},D,j}\) | \(\widehat p_{a_{\mathrm{rad}},D,j}\) | Polynomial estimate assembled from evaluation-block private moments | def:frontier-handle |
| \(T_*\) | \(T_*\) | Pilot threshold \(4\sigma\sqrt L\) in the hybrid branch | def:frontier-handle |
| \(\widehat F\) | \(\widehat F\) | Branch-selected estimate of the average absolute treatment contrast | def:frontier-handle |
| \(\operatorname{sign}(M_j)\) | \(\operatorname{sign}(M_j)\) | Sign of the pilot mean with zero assigned sign zero | def:frontier-handle |
| \(\widetilde V\) | \(\widetilde V\) | Baseline estimate plus one half of the absolute-contrast estimate | def:frontier-handle |
| \(\widehat V\) | \(\widehat V\) | Welfare estimate clipped to \([1/4,3/4]\), with the specified \(n=2\) branch | def:frontier-handle |
| \(q_*\) | \(q_*\) | Interval radius \(\sqrt{10^{17}\rho(t,d)}\) | def:frontier-handle |
| \((\alpha,k)\) | \((\alpha,k)\) | Resource-dependent amplitude and odd moment-contraction degree for the converse | def:frontier-handle |
| \(K=k-1\) | \(K=k-1\) | Even moment-matching degree determined by the converse tuning | def:frontier-handle |
| \(r_{\mathcal C}(n,d,\varepsilon)\) | \(r_{\mathcal C}(n,d,\varepsilon)\) | Squared-error rate equal to \(\rho(n\varepsilon^2,d)\) in either protocol class | Gap; main results |
| \(h_{\mathcal C}(n,d,\varepsilon)\) | \(h_{\mathcal C}(n,d,\varepsilon)\) | Honest-length rate equal to the square root of the squared-error rate | Gap; main results |
| \(\mathcal A_d\) | \(\mathcal A_d\) | Finite paired alphabet \([d]\times\{-1,1\}\) | def:tv-corollary-models |
| \(\Delta_{2d}\) | \(\Delta_{2d}\) | Probability simplex on the paired \(2d\)-symbol alphabet | def:tv-corollary-models |
| \(\mathsf p\) | \(\mathsf p\) | A probability law on the paired finite alphabet | def:tv-corollary-models |
| \(\mathsf p(j,s)\) | \(\mathsf p(j,s)\) | Probability assigned to paired symbol \((j,s)\) | def:tv-corollary-models |
| \(\mathcal P_d^{\mathrm{pair}}\) | \(\mathcal P_d^{\mathrm{pair}}\) | Paired signed laws indexed by contrasts in \([-1/2,1/2]^d\) | def:tv-corollary-models |
| \(D_{\mathrm{TV}}(\mathsf p)\) | \(D_{\mathrm{TV}}(\mathsf p)\) | Total-variation distance from the public uniform reference | def:tv-corollary-models |
| \(D_{\mathrm{TV}}(P_\theta)\) | \(D_{\mathrm{TV}}(P_\theta)\) | Uniform-reference total-variation distance evaluated on a paired signed law | def:tv-corollary-models |
| \(\mathcal M\) | \(\mathcal M\) | Selected paired-family or full-simplex statistical model | def:tv-corollary-models |
| \(\mathfrak K_{\mathcal C}(n,d,\varepsilon)\) | \(\mathfrak K_{\mathcal C}(n,d,\varepsilon)\) | Pure-local one-message protocol class for paired-alphabet inputs | def:tv-private-decision-values |
| \(\mathsf K\) | \(\mathsf K\) | A paired-alphabet private protocol with the declared seed and message spaces | def:tv-private-decision-values |
| \(\mathsf K_i\) | \(\mathsf K_i\) | Participant-specific private kernel on paired-alphabet inputs | def:tv-private-decision-values |
| \(\mathbf Z^{\mathsf K}\) | \(\mathbf Z^{\mathsf K}\) | Message vector generated by the paired-alphabet protocol | def:tv-private-decision-values |
| \(\widehat D\) | \(\widehat D\) | Borel transcript-based estimate of uniform-reference total variation | def:tv-private-decision-values |
| \(J_{\mathrm{TV}}\) | \(J_{\mathrm{TV}}\) | Connected closed total-variation interval with Borel endpoints in \([0,1]\) | def:tv-private-decision-values |
| \(\mathfrak R^{\mathrm{TV}}_{\mathcal C}(\mathcal M;n,d,\varepsilon)\) | \(\mathfrak R^{\mathrm{TV}}_{\mathcal C}(\mathcal M;n,d,\varepsilon)\) | Minimax squared-error risk for total variation on the selected model | def:tv-private-decision-values |
| \(\mathfrak H^{\mathrm{TV}}_{\mathcal C}(\mathcal M;n,d,\varepsilon)\) | \(\mathfrak H^{\mathrm{TV}}_{\mathcal C}(\mathcal M;n,d,\varepsilon)\) | Minimax worst-law expected connected length under global coverage \(0.90\) | def:tv-private-decision-values |
| \(\mathfrak R^{\mathrm{TV}}_{\mathcal C}(\mathcal P_d^{\mathrm{pair}};n,d,\varepsilon)\) | \(\mathfrak R^{\mathrm{TV}}_{\mathcal C}(\mathcal P_d^{\mathrm{pair}};n,d,\varepsilon)\) | Total-variation minimax risk restricted to the paired family | def:tv-private-decision-values |
| \(\mathfrak H^{\mathrm{TV}}_{\mathcal C}(\mathcal P_d^{\mathrm{pair}};n,d,\varepsilon)\) | \(\mathfrak H^{\mathrm{TV}}_{\mathcal C}(\mathcal P_d^{\mathrm{pair}};n,d,\varepsilon)\) | Honest total-variation interval length on the paired family | def:tv-private-decision-values |
| \(\mathfrak R^{\mathrm{TV}}_{\mathcal C}(\Delta_{2d};n,d,\varepsilon)\) | \(\mathfrak R^{\mathrm{TV}}_{\mathcal C}(\Delta_{2d};n,d,\varepsilon)\) | Total-variation minimax risk on the full probability simplex | def:tv-private-decision-values |
| \(\mathfrak H^{\mathrm{TV}}_{\mathcal C}(\Delta_{2d};n,d,\varepsilon)\) | \(\mathfrak H^{\mathrm{TV}}_{\mathcal C}(\Delta_{2d};n,d,\varepsilon)\) | Globally honest total-variation interval length on the full simplex | def:tv-private-decision-values |
| \(p^Q(\theta,r)\) | \(p^Q(\theta,r)\) | Conditional transcript density for the symmetric law relative to its zero-contrast reference | Gap; converse appendix |
| \(\beta\) | \(\beta\) | Privacy contraction scale \((e^\varepsilon-1)/(2d)\) | Gap; converse appendix |
| \(\nu_0\) | \(\nu_0\) | First amplitude-supported coordinate prior with the declared matched moments | Gap; converse appendix |
| \(\nu_1\) | \(\nu_1\) | Second amplitude-supported coordinate prior with the declared matched moments | Gap; converse appendix |
| \(\mathsf M_0^Q\) | \(\mathsf M_0^Q\) | Seed-transcript mixture induced by the first independent-coordinate prior | Gap; converse appendix |
| \(\mathsf M_1^Q\) | \(\mathsf M_1^Q\) | Seed-transcript mixture induced by the second independent-coordinate prior | Gap; converse appendix |
| \(T_j^{\mathrm{col}}\) | \(T_j^{\mathrm{col}}\) | Deterministic statistic of the scaled messages in coordinate \(j\) | Gap; attainment appendix |
| \(T_{j\prime}^{\mathrm{col}}\) | \(T_{j\prime}^{\mathrm{col}}\) | Deterministic statistic of the scaled messages in the distinct coordinate \(j\prime\) | Gap; attainment appendix |
| \(q_D(x)\) | \(q_D(x)\) | Explicit even-degree Chebyshev approximation used in calibration | Gap; approximation appendix |
| \(a_{Dv}\) | \(a_{Dv}\) | Monomial coefficient of the calibration polynomial \(q_D\) | Gap; approximation appendix |
| \(p_{a,D}(x)\) | \(p_{a,D}(x)\) | Radius-\(a\) rescaling \(a q_D(x/a)\) of the approximation polynomial | Gap; attainment appendix |
| \(\widehat p_{a,D,j}\) | \(\widehat p_{a,D,j}\) | Radius-\(a\), degree-\(D\) coordinate estimate using unbiased private moments | Gap; attainment appendix |
| \(H_j\) | \(H_j\) | Pilot-selected combination of a polynomial estimate and signed evaluation mean | Gap; attainment appendix |
| \(\xi_0\) | \(\xi_0\) | First symmetric probability measure in the approximation-duality pair | Gap; approximation appendix |
| \(\xi_1\) | \(\xi_1\) | Second symmetric probability measure in the approximation-duality pair | Gap; approximation appendix |
| \(e_K\) | \(e_K\) | Best degree-\(K\) uniform polynomial approximation error for absolute value on \([-1,1]\) | Gap; approximation appendix |
| \(N_0\) | \(N_0\) | Joint seed-transcript mixture from the first causal prior | Gap; converse appendix |
| \(N_1\) | \(N_1\) | Joint seed-transcript mixture from the second causal prior | Gap; converse appendix |
| \(v_0\) | \(v_0\) | Welfare center of the first prior | Gap; converse appendix |
| \(v_1\) | \(v_1\) | Larger welfare center of the second prior | Gap; converse appendix |
| \(\Delta=v_1-v_0\) | \(\Delta=v_1-v_0\) | Separation between the two welfare centers | Gap; converse appendix |
| \(\eta_0\) | \(\eta_0\) | Upper bound on each prior's target-concentration failure probability | Gap; converse appendix |
| \(\omega\) | \(\omega\) | Upper bound on total variation between the two transcript mixtures | Gap; converse appendix |
| \(H\) in the measurable-density result | \(H\) | Measurable parameter space for the auxiliary kernels | Gap; measure-theoretic appendix |
| \(Z\) | \(Z\) | Standard-Borel output space for the auxiliary kernels | Gap; measure-theoretic appendix |
| \(K\) in the measurable-density result | \(K\) | Finite kernel absolutely continuous with respect to the reference kernel | Gap; measure-theoretic appendix |
| \(L\) in the measurable-density result | \(L\) | Finite reference kernel for the measurable density | Gap; measure-theoretic appendix |
| \(f:H\times Z\to[0,\infty]\) | \(f:H\times Z\to[0,\infty]\) | Jointly measurable Radon–Nikodym density of the auxiliary kernels | Gap; measure-theoretic appendix |
| \(H_1,\ldots,H_m\) | \(H_1,\ldots,H_m\) | Independent real variables supported on \([-b,b]\) in the concentration result | Gap; concentration appendix |
| \(\operatorname{TV}\) | \(\operatorname{TV}\) | Standard total-variation distance between probability measures | def:tv-corollary-models for the finite uniform-reference instance; standard ambient operator elsewhere |
| \(\operatorname{length}\) | \(\operatorname{length}\) | Difference between the ordered endpoints of a connected closed interval | def:honest-length; def:tv-private-decision-values |
| \(\operatorname{Var}\) | \(\operatorname{Var}\) | Standard variance of a real random variable | Standard ambient operator |
| \(\operatorname{Cov}\) | \(\operatorname{Cov}\) | Standard covariance of two real random variables | Standard ambient operator |
| \(\mathbf1_{\{|M_j|\le T_*\}}\) | \(\mathbf1_{\{|M_j|\le T_*\}}\) | Indicator selecting the polynomial branch for coordinate \(j\) | def:frontier-handle |
| \(\mathbf1_{\{|M_j|>T_*\}}\) | \(\mathbf1_{\{|M_j|>T_*\}}\) | Indicator selecting the signed-mean branch for coordinate \(j\) | def:frontier-handle |
| \((1-\omega-2\eta_0)_+\) | \((1-\omega-2\eta_0)_+\) | Positive part of the testing-separation factor for squared error | Standard positive-part operation; operands resolved in converse appendix |
| \((0.80-2\eta_0-\omega)_+\) | \((0.80-2\eta_0-\omega)_+\) | Positive part of the coverage-separation factor for interval length | Standard positive-part operation; operands resolved in converse appendix |

# Sections

## section: Abstract

Plan the abstract for drafting after the body: identify first-best binary treatment welfare, the known uniform randomized design, and confidentiality of each complete realized record; summarize the dimension-dependent minimax estimation and globally honest connected-length orders, matching noninteractive attainment and sequential converses, and the paired-uniform total-variation consequence. Use verbal descriptions or first-use glosses for every symbol introduced before setup. Present the full-simplex implication as a lower-bound result.

objs: none

bib: none

home_objs: none
## section: Introduction

Organize the introduction around the precision with which a confidential randomized trial can report the population welfare attainable by choosing the better treatment in each stratum. Plan a reader-first account of how heterogeneous treatment contrasts and exact ties generate the nonsmooth estimation problem, followed by the finite-resource precision characterization, honest inference, and interaction comparison. Explain that stratum probabilities and assignment are known while realized participant records satisfy full-record local privacy. Include a single factual sentence directing readers to the appendix verification note. Draft this section after the mathematical and interpretive sections.

objs: none

bib: none

home_objs: none
## section: Related work

Position the contribution against the closest results through three focused comparisons. For the estimand, compare unrestricted binary welfare in Cerulli2026OptimalPolicy, Section 2, equations (3)–(7), with statistical treatment choice and policy learning, then compare finite-resource global precision over categorical laws with exact ties against the condition-specific asymptotic optimal-value inference of LuedtkeVanDerLaan2016OptimalValue, WhitehouseChenAusternSyrgkanis2026Softmax, Theorem 3.3, Chen2025, Theorem 1 and its listed assumptions, Feng2026, Sections 3.2 and 4, and Xu2026, Theorems 2.2 and 3.1 under Assumptions 1–8. For the statistical method, compare private distinct-person moments and sequential transcript contraction with Gaussian absolute-mean estimation in CaiLow2011Nonsmooth, Theorem 1 and Sections 3–5, and raw-sample distance estimation in JiaoHanWeissman2018L1, Theorems 2–4. For confidentiality and interaction, compare the absolute signed-contrast target with positive power sums in ButuceaIssartel2021Functionals, Theorems 2.4–2.7, quadratic density functionals in ButuceaRohdeSteinberger2023Quadratic, Theorems 3.2–3.3 and 4.1–4.2, bounded-score ATE estimation in OhnishiAwan2025Randomized, Lemma 4 and Theorem 7, public-coin identity testing in AcharyaCanonneFreitagTyagi2019TestWithoutTrust and Acharya2021, and approximate item-private empirical sketches in CormodeTing2025FederatedShift, Theorems 4.6, 4.10, and 4.13. Keep comparisons attached to the supplied locators and state the novelty boundary as the joint finite-resource estimation, connected honesty, and all-sequential converse for the specified causal and paired models.

objs: none

bib: Cerulli2026OptimalPolicy, Manski2004, Kitagawa2018, Athey2021, LuedtkeVanDerLaan2016OptimalValue, WhitehouseChenAusternSyrgkanis2026Softmax, Chen2025, Feng2026, Xu2026, CaiLow2011Nonsmooth, JiaoHanWeissman2018L1, Jiao2015, Wu2016, ButuceaIssartel2021Functionals, ButuceaRohdeSteinberger2023Quadratic, OhnishiAwan2025Randomized, AcharyaCanonneFreitagTyagi2019TestWithoutTrust, Acharya2021, CormodeTing2025FederatedShift, DuchiJordanWainwright2018Minimax, Low1997, CaiLow2004AdaptationCI, ArmstrongKolesar2020HonestCI

home_objs: none
## section: Randomized trials, local privacy, and welfare

Introduce the full-data and observed-record notation, the first-best cellwise welfare target, and the baseline and absolute-contrast components. Group the causal restrictions into the design and outcome model, followed by independent sampling. Define the public seed, message spaces, histories, transcript, and analyst randomization before imposing full-record pure local privacy and distinguishing noninteractive from one-message sequential collection. Define squared-error minimax precision and worst-law expected connected-interval length under global coverage \(0.90\). Introduce the signed experiment and symmetric causal family before the bridge result, using that result to explain why the absolute-contrast component is the statistical object driving the analysis. Resolve setup notation gaps through grouped presentation definitions before their first use.

objs: ass:uniform-covariates, ass:fair-randomization, ass:consistency, ass:interior-means, ass:iid-people, synth_1, def:causal-model, ass:independent-randomness, ass:full-record-privacy, synth_2, ass:noninteraction, def:sequential-class, def:noninteractive-class, def:risk, def:honest-length, synth_3, def:symmetric-law, synth_6, synth_5, synth_4, prop:signed-causal-bridge

bib: Rubin1974, Warner1965, Dwork2014, Manski2004

home_objs: ass:uniform-covariates, ass:fair-randomization, ass:consistency, ass:interior-means, ass:iid-people, def:causal-model, ass:independent-randomness, ass:full-record-privacy, ass:noninteraction, def:sequential-class, def:noninteractive-class, def:risk, def:honest-length, def:symmetric-law, prop:signed-causal-bridge
## section: Minimax precision and an attaining private procedure

Place the central procedure in the main body, preceded by the grouped definitions of privacy attenuation, scaled vector messages, and distinct-person moments. Present its binary baseline messages, independent pilot and evaluation blocks, resource-dependent polynomial choices, clipped welfare estimate, and connected interval as a numbered algorithm. Follow it with the headline minimax result and a reader-facing interpretation of the resource regimes, consistency criterion, bounded-dimension private-parametric boundary, and growing-dimension logarithmic behavior. Present the two-cell result as a calibration of the general characterization. Explain the proof strategy through approximation bias, aggregate private-moment variance, and indistinguishable sequential transcript mixtures, with detailed calculations assigned to the appendix. Distinguish equality of statistical orders from optimization of leading constants.

objs: def:vector-kernel, def:private-moments, def:frontier-handle, thm:uniform-private-value-frontiers, thm:two-cell-calibration

bib: CaiLow2011Nonsmooth, Hoeffding1948, Hoeffding1963Bounded

home_objs: def:vector-kernel, def:private-moments, def:frontier-handle, thm:uniform-private-value-frontiers, thm:two-cell-calibration
## section: Total-variation estimation and interpretation

Define the paired-alphabet models and their private estimation and connected-interval criteria immediately before the statistical corollaries. Present the paired-family matching precision characterization and the full-simplex converse as separate results with their respective model domains. Interpret the causal result as a precision benchmark for reporting a fixed population's first-best welfare, and interpret the interaction comparison within the declared one-person-one-message protocol classes. Connect the paired-family result to the signed experiment and explain how inclusion transfers lower bounds to the simplex. Include a clearly titled “Limitations and future work” subsection for unknown stratum probabilities or propensities, repeated records per participant, leading constants, learned-policy regret, design-based finite-population inference, and matching full-simplex upper bounds. Keep literature positioning in the related-work section.

objs: def:tv-corollary-models, def:tv-private-decision-values, thm:paired-uniform-tv-frontier, thm:full-simplex-tv-converse

bib: none

home_objs: def:tv-corollary-models, def:tv-private-decision-values, thm:paired-uniform-tv-frontier, thm:full-simplex-tv-converse
## section: Appendix: Approximation and private-moment bounds

Collect the approximation, moment-duality, and bounded-summand concentration inputs, with their local notation resolved before use. Establish the vector-channel privacy, unbiased distinct-person moments, second-moment bounds, and cross-coordinate dependence control, followed by global and pilot-selected polynomial calibration. Organize the calculations around the statistical roles of approximation error, polynomial variance, and threshold mistakes. Preserve the source-specific locators and theorem-local verification-scope disclosures for cited inputs.

objs: lem:bounded-mean-concentration, lem:cai-low-chebyshev-approximation, lem:cai-low-moment-duality, lem:private-moment-and-dependence, lem:finite-private-polynomial-calibration

bib: Hoeffding1963Bounded, CaiLow2011Nonsmooth, Hoeffding1948

home_objs: lem:bounded-mean-concentration, lem:cai-low-chebyshev-approximation, lem:cai-low-moment-duality, lem:private-moment-and-dependence, lem:finite-private-polynomial-calibration
## section: Appendix: Sequential contraction and decision lower bounds

Introduce the appendix-specific transcript densities, reference experiments, moment-matching priors, mixture laws, and target-separation notation before their first use. Place the measurable-density input before the higher-order sequential contraction argument. Develop the contraction calculation with arbitrary independent public seeds and adaptive histories, then the conversion of separated target priors into squared-error and connected-length lower bounds. Include the dimension-free two-point argument and explain its role in finite-resource calibration. Treat connectedness and finite global coverage directly in the interval reduction.

objs: lem:measurable-kernel-radon-nikodym, lem:adaptive-moment-contraction, lem:separated-value-mixtures, lem:dimension-free-private-two-point

bib: Kallenberg2017RandomMeasures, VakarOng2018SFinite, CaiLow2011Nonsmooth, DuchiJordanWainwright2018Minimax, Tsybakov2009, Low1997

home_objs: lem:measurable-kernel-radon-nikodym, lem:adaptive-moment-contraction, lem:separated-value-mixtures, lem:dimension-free-private-two-point
## section: Appendix: Guide to the main proofs and verification scope

Give a brief guide to the proof dependency chain, then state the precise Lean checking scope, data-generating and privacy assumptions, and the cited Bernstein premise carried through theorem-local verification-scope disclosures. Leave the detailed proofs to the assembled proof appendix and avoid repeating theorem clauses or rate consequences.

objs: none

bib: CaiLow2011Nonsmooth, Hoeffding1963Bounded, Kallenberg2017RandomMeasures, VakarOng2018SFinite
home_objs: none
