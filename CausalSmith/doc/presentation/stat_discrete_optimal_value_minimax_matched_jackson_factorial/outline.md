# Title
**Minimax estimation of optimal treatment values with discrete covariates**

**Contribution statement.** Under fixed overlap for binary treatment and a growing finite covariate alphabet, the paper constructs an explicit all-data estimator and proves the finite-sample minimax mean-squared risk order \(\min\{1,d/[n\log(ed)]\}\) for the scalar optimal-treatment value, with the same order applying to causal completions identified by consistency and conditional exchangeability.

# Notation

env_overrides: def:jackson-factorial-estimator=algorithmv, prop:equal-propensity-l1-reduction=propositionv, prop:parent-reduction=propositionv, prop:identification-and-extension=propositionv, prop:causal-optimal-value-corollary=propositionv, oeq:sharp-overlap-constant=remarkv

notation_gaps: \(\mathcal J\)=four outcome-arm coordinate set used in the Jackson polynomial and estimator but absent from an anchored frozen definition, \(D_0\)=universal cutoff used in the estimator, dense lower bound, and parent comparison but absent from an anchored frozen definition, \(\kappa\)=Jackson-degree tuning constant used in the estimator but absent from an anchored frozen definition, \(H_0\)=pilot-radius tuning constant used in the estimator and pilot lemma but absent from an anchored frozen definition, \(\Pi_{[a,b]}\)=projection onto an interval used in the estimator but absent from an anchored frozen definition, \(\operatorname{TV}\)=total-variation distance used in the dense lower bound but absent from an anchored frozen definition

`<note symbol>` | `<paper notation>` | `<defining property in one phrase>` | `<home>`
\([d]\) | \([d]:=\{1,\ldots,d\}\) | finite covariate alphabet of size \(d\) | ass:fixed-overlap
\(d\) | \(d\) | covariate alphabet size with \(d\ge2\) | def:observed-model-class
\(n\) | \(n\) | number of fixed-sample observations | ass:iid-sampling
\(O_i\) | \(O_i=(X_i,A_i,Y_i)\) | observed triple for unit \(i\) | ass:iid-sampling
\(X_i\) | \(X_i\) | covariate component of the observed triple | ass:iid-sampling
\(A_i\) | \(A_i\) | binary treatment component of the observed triple | ass:iid-sampling
\(Y_i\) | \(Y_i\) | binary outcome component of the observed triple | ass:iid-sampling
\(\mathbb P\) | \(\mathbb P\) | observed law on \([d]\times\{0,1\}^2\) | def:observed-model-class
\(P\) | \(P\) | full-data law for \((X,A,Y,Y(0),Y(1))\) | def:observed-margin
\(X\) | \(X\) | covariate under an observed or full-data law | def:observed-model-class
\(A\) | \(A\) | binary treatment under an observed or full-data law | def:observed-model-class
\(Y\) | \(Y\) | binary observed outcome under an observed or full-data law | def:observed-model-class
\(Y(0)\) | \(Y(0)\) | potential outcome under treatment arm \(0\) | ass:conditional-exchangeability
\(Y(1)\) | \(Y(1)\) | potential outcome under treatment arm \(1\) | ass:conditional-exchangeability
\(Y(a)\) | \(Y(a)\) | potential outcome under arm \(a\) | ass:conditional-exchangeability
\(a\) | \(a\in\{0,1\}\) | binary treatment-arm index | def:observed-model-class
\(y\) | \(y\in\{0,1\}\) | binary outcome index | def:observed-model-class
\(x\) | \(x\in[d]\) | covariate-cell index | def:observed-model-class
\(\epsilon\) | \(\epsilon\in(0,1/2)\) | fixed overlap constant | ass:fixed-overlap
\(p_x\) | \(p_x\) | marginal mass of covariate cell \(x\) | def:observed-model-class
\(\pi_x\) | \(\pi_x\) | treatment propensity in covariate cell \(x\) | def:observed-model-class
\(\mu_{ax}\) | \(\mu_{ax}\) | arm-specific outcome mean in cell \(x\) | def:observed-model-class
\(\Delta_d\) | \(\Delta_d:=\{p\in[0,1]^d:\sum_{x=1}^d p_x=1\}\) | \(d\)-point probability simplex | def:observed-model-class
\(\mathcal D_{d,\epsilon}^{\mathrm{obs}}\) | \(\mathcal D_{d,\epsilon}^{\mathrm{obs}}\) | observed-law model class with fixed overlap | def:observed-model-class
\(q_{ay,x}\) | \(q_{ay,x}=\mathbb P(X=x,A=a,Y=y)\) | observed atom mass for arm \(a\), outcome \(y\), and cell \(x\) | def:observed-model-class
\(q_{a1,x}\) | \(q_{a1,x}\) | observed success atom mass for arm \(a\) in cell \(x\) | def:observed-model-class
\(q_{a0,x}\) | \(q_{a0,x}\) | observed failure atom mass for arm \(a\) in cell \(x\) | def:observed-model-class
\(q_x\) | \(q_x=(q_{00,x},q_{01,x},q_{10,x},q_{11,x})\) | four-vector of observed atom masses in cell \(x\) | def:observed-model-class
\(q_{00,x}\) | \(q_{00,x}\) | observed atom mass in cell \(x\), arm \(0\), outcome \(0\) | def:observed-model-class
\(q_{01,x}\) | \(q_{01,x}\) | observed atom mass in cell \(x\), arm \(0\), outcome \(1\) | def:observed-model-class
\(q_{10,x}\) | \(q_{10,x}\) | observed atom mass in cell \(x\), arm \(1\), outcome \(0\) | def:observed-model-class
\(q_{11,x}\) | \(q_{11,x}\) | observed atom mass in cell \(x\), arm \(1\), outcome \(1\) | def:observed-model-class
\(\operatorname{Obs}(P)\) | \(\operatorname{Obs}(P)\) | observed margin of a full-data law | def:observed-margin
\(\Psi(\mathbb P)\) | \(\Psi(\mathbb P)\) | observed-law optimal-regression value | def:observed-optimal-value
\(\Psi(\mathbf q)\) | \(\Psi(\mathbf q)\) | table representation of the observed-law optimal-regression value | def:observed-optimal-value
\(\mathbf q\) | \(\mathbf q=(q_x)_{x=1}^d\) | observed table of four-vectors across cells | def:observed-optimal-value
\(\mathfrak R_{n,d,\epsilon}\) | \(\mathfrak R_{n,d,\epsilon}\) | fixed-sample minimax squared risk over \(\mathcal D_{d,\epsilon}^{\mathrm{obs}}\) | def:minimax-risk
\(\widehat V\) | \(\widehat V\) | measurable estimator of the observed-law optimal-regression value | def:minimax-risk
\(\mathcal C_\epsilon\) | \(\mathcal C_\epsilon\) | four-cell overlap cone in \(\mathbb R_+^4\) | def:overlap-cone
\(u\) | \(u\in\mathbb R_+^4\) | four-coordinate nonnegative cell vector | def:overlap-cone
\(s_a(u)\) | \(s_a(u)=u_{a0}+u_{a1}\) | arm-\(a\) mass of a four-cell vector | def:overlap-cone
\(s(u)\) | \(s(u)=s_0(u)+s_1(u)\) | total mass of a four-cell vector | def:overlap-cone
\(g_{a,\epsilon}(u)\) | \(g_{a,\epsilon}(u)\) | overlap-stabilized arm contribution on the orthant | def:global-extension
\(\bar f_\epsilon(u)\) | \(\bar f_\epsilon(u)\) | globally defined cellwise maximum contribution | def:global-extension
\(V^\star(P)\) | \(V^\star(P):=E_P[\max_{a\in\{0,1\}}E_P\{Y(a)\mid X\}]\) | full-data causal optimal-treatment value | def:oracle-value
\(\overline N_x\) | \(\overline N_x=\sum_{i=1}^n\mathbf 1\{X_i=x\}\) | sample count in covariate cell \(x\) | def:empirical-ratio-estimator
\(\overline N_{ax}\) | \(\overline N_{ax}=\sum_{i=1}^n\mathbf 1\{X_i=x,A_i=a\}\) | sample count in covariate cell \(x\) and arm \(a\) | def:empirical-ratio-estimator
\(\overline S_{ax}\) | \(\overline S_{ax}=\sum_{i=1}^n\mathbf 1\{X_i=x,A_i=a,Y_i=1\}\) | sample success count in cell \(x\) and arm \(a\) | def:empirical-ratio-estimator
\(\widehat p_x\) | \(\widehat p_x=\overline N_x/n\) | empirical covariate-cell mass | def:empirical-ratio-estimator
\(\widehat\mu_{ax}\) | \(\widehat\mu_{ax}=\overline S_{ax}/\overline N_{ax}\) with \(0/0=0\) | empirical arm-specific outcome mean | def:empirical-ratio-estimator
\(\widehat V_{n,d}^{\mathrm{ER}}\) | \(\widehat V_{n,d}^{\mathrm{ER}}=\sum_{x=1}^d\widehat p_x\max_a\widehat\mu_{ax}\) | empirical-ratio optimal-value estimator | def:empirical-ratio-estimator
\(K_d\) | \(K_d\) | Jackson approximation order used by the estimator | def:jackson-kernel
\(K_d\geq2\) | \(K_d\geq2\) | integer order supplied to the Jackson polynomial construction | def:jackson-kernel
\(J_{K_d}(t)\) | \(J_{K_d}(t)=c_{K_d}[\sin(K_dt/2)/\sin(t/2)]^4\) | order-four Jackson smoothing polynomial on \([-\pi,\pi]\) | def:jackson-kernel
\(c_{K_d}\) | \(c_{K_d}\) | normalizing constant for \(J_{K_d}\) | def:jackson-kernel
\(Q_x\) | \(Q_x=\prod_{\jmath\in\mathcal J}[\ell_{\jmath,x},u_{\jmath,x}]\) | pilot-local four-coordinate rectangle for cell \(x\) | def:jackson-kernel
\(\ell_{\jmath,x}\) | \(\ell_{\jmath,x}\) | lower endpoint of coordinate \(\jmath\) in \(Q_x\) | def:jackson-kernel
\(u_{\jmath,x}\) | \(u_{\jmath,x}\) | upper endpoint of coordinate \(\jmath\) in \(Q_x\) | def:jackson-kernel
\(b_{\jmath,x}\) | \(b_{\jmath,x}=(\ell_{\jmath,x}+u_{\jmath,x})/2\) | center coordinate of \(Q_x\) | def:jackson-kernel
\(r_{\jmath,x}\) | \(r_{\jmath,x}=(u_{\jmath,x}-\ell_{\jmath,x})/2\) | radius coordinate of \(Q_x\) | def:jackson-kernel
\(b_x\) | \(b_x\) | vector of rectangle centers in cell \(x\) | def:jackson-kernel
\(r_x\) | \(r_x\) | vector of rectangle radii in cell \(x\) | def:jackson-kernel
\(P_{x,K_d}\) | \(P_{x,K_d}\) | tensor polynomial associated with \(Q_x\) | def:jackson-kernel
\(\theta\) | \(\theta\) | angle vector used to parametrize \(Q_x\) in the Jackson construction | def:jackson-kernel
\(t\) | \(t\) | integration variable on \([-\pi,\pi]\) in the Jackson construction | def:jackson-kernel
\(L_d\) | \(L_d=\log(ed)\) | logarithmic alphabet scale | def:jackson-factorial-estimator
\(m\) | \(m=n/8\) | Poissonized pilot/evaluation scale | def:jackson-factorial-estimator
\(M\) | \(M\sim\operatorname{Pois}(n/4)\) | auxiliary Poisson inclusion count | def:jackson-factorial-estimator
\(B_i\) | \(B_i\) | independent Bernoulli mark for pilot/evaluation splitting | def:jackson-factorial-estimator
\(N'_{\jmath,x}\) | \(N'_{\jmath,x}\) | pilot count for coordinate \(\jmath\) and cell \(x\) | def:jackson-factorial-estimator
\(N_{\jmath,x}\) | \(N_{\jmath,x}\) | evaluation count for coordinate \(\jmath\) and cell \(x\) | def:jackson-factorial-estimator
\(c_{\jmath,x}\) | \(c_{\jmath,x}=N'_{\jmath,x}/m\) | pilot frequency for coordinate \(\jmath\) and cell \(x\) | def:jackson-factorial-estimator
\(h_{\jmath,x}\) | \(h_{\jmath,x}=H_0\{\sqrt{c_{\jmath,x}L_d/m}+L_d/m\}\) | pilot rectangle half-width inflation | def:jackson-factorial-estimator
\(b_{x,\alpha}\) | \(b_{x,\alpha}\) | local polynomial coefficient indexed by multi-index \(\alpha\) | def:jackson-factorial-estimator
\(\alpha\) | \(\alpha\) | multi-index in the centered local polynomial expansion | def:jackson-factorial-estimator
\(U_h(N;z)\) | \(U_h(N;z)=\sum_{t=0}^h\binom ht(-z)^{h-t}(N)_t/m^t\) | centered factorial lift of a monomial | def:jackson-factorial-estimator
\(S_x\) | \(S_x=(1+\epsilon^{-1})\sum_{\jmath}r_{\jmath,x}\) | clipping scale for cell \(x\) | def:jackson-factorial-estimator
\(Z_x\) | \(Z_x\) | unprojected cell estimate | def:jackson-factorial-estimator
\(T_x^{\mathrm{JF}}\) | \(T_x^{\mathrm{JF}}\) | clipped cell estimate | def:jackson-factorial-estimator
\(\widetilde V\) | \(\widetilde V\) | randomized projected aggregate estimator before Rao--Blackwellization | def:jackson-factorial-estimator
\(\widehat V_{n,d}^{\mathrm{JF}}\) | \(\widehat V_{n,d}^{\mathrm{JF}}\) | all-data Rao--Blackwellized estimator | def:jackson-factorial-estimator
\((\mathbf P,\mathbf Q)\) | \((\mathbf P,\mathbf Q)\in\Delta_d^2\) | pair of \(d\)-point distributions for the \(L_1\) embedding | def:l1-embedding
\(\mathbf P\) | \(\mathbf P\in\Delta_d\) | first \(d\)-point distribution in the \(L_1\) embedding | def:l1-embedding
\(\mathbf Q\) | \(\mathbf Q\in\Delta_d\) | second \(d\)-point distribution in the \(L_1\) embedding | def:l1-embedding
\(P_x\) | \(P_x\) | coordinate \(x\) of \(\mathbf P\) | def:l1-embedding
\(Q_x\) | \(Q_x\) | coordinate \(x\) of \(\mathbf Q\) in the \(L_1\) embedding | def:l1-embedding
\(K\) | \(K\) | polynomial degree for moment matching or Jackson approximation | def:dense-moment-matching-construction
\(P_\theta^{\mathrm{dense}}\) | \(P_\theta^{\mathrm{dense}}\) | dense equal-mass contrast submodel | synth_15
\(\theta\in[-1/2,1/2]^d\) | \(\theta\in[-1/2,1/2]^d\) | dense submodel treatment-effect contrast vector | synth_15
\(\theta_x\) | \(\theta_x\) | cell \(x\) contrast in the dense submodel | synth_15
\(E_K\) | \(E_K=\inf_{p:\deg(p)\leq K}\sup_{t\in[-1,1]}\lvert\lvert t\rvert-p(t)\rvert\) | best degree-\(K\) uniform approximation error for \(|t|\) | def:dense-moment-matching-construction
\(\nu_{0,K}\) | \(\nu_{0,K}\) | first symmetric moment-matching probability measure | def:dense-moment-matching-construction
\(\nu_{1,K}\) | \(\nu_{1,K}\) | second symmetric moment-matching probability measure | def:dense-moment-matching-construction
\(K_d^{\mathrm{lb}}\) | \(K_d^{\mathrm{lb}}=2\lceil4L_d\rceil\) | lower-bound moment-matching degree | def:dense-moment-matching-construction
\(\lambda_{n,d}\) | \(\lambda_{n,d}=2n/d\) | one-cell Poisson intensity scale | def:dense-moment-matching-construction
\(a_{n,d}\) | \(a_{n,d}=\sqrt{K_d^{\mathrm{lb}}/(64\lambda_{n,d})}\) | lower-bound contrast amplitude | def:dense-moment-matching-construction
\(\Pi_{0,n,d}\) | \(\Pi_{0,n,d}\) | first product prior on dense contrasts | def:dense-moment-matching-construction
\(\Pi_{1,n,d}\) | \(\Pi_{1,n,d}\) | second product prior on dense contrasts | def:dense-moment-matching-construction
\(\mathbb M_{0,n,d}\) | \(\mathbb M_{0,n,d}\) | first Poissonized observation mixture | def:dense-moment-matching-construction
\(\mathbb M_{1,n,d}\) | \(\mathbb M_{1,n,d}\) | second Poissonized observation mixture | def:dense-moment-matching-construction
\(\mathfrak R^{\mathrm{Pois}}_{2n,d,\epsilon}\) | \(\mathfrak R^{\mathrm{Pois}}_{2n,d,\epsilon}\) | Poissonized minimax squared risk | def:dense-moment-matching-construction
\(\Delta_{n,d}^{\mathrm{dense}}\) | \(\Delta_{n,d}^{\mathrm{dense}}\) | separation between dense prior mean targets | def:dense-moment-matching-construction
\(P_{x,K}\) | \(P_{x,K}\) | four-coordinate Jackson tensor polynomial on \(Q_x\) | lem:jackson-tensor-extraction
\(\mathcal R_{x,K}\) | \(\mathcal R_{x,K}\) | centered normalized polynomial associated with \(P_{x,K}\) | lem:jackson-tensor-extraction
\(\beta\) | \(\beta\in\operatorname{supp}(\mathcal R_{x,K})\) | multi-index in the normalized polynomial support | lem:jackson-tensor-extraction
\(\omega\) | \(\omega\) | coordinate index in \(\mathcal J\) for multi-indices | lem:jackson-tensor-extraction
\(v\) | \(v\) | four-coordinate evaluation point for a cell polynomial | def:jackson-factorial-estimator
\(\vartheta\) | \(\vartheta:\mathcal J\to\mathbb R\) | angle vector used in the Jackson tensor certificate | lem:jackson-tensor-extraction
\(f\) | \(f\) | continuous function on the normalized cube in the convolution lemma | synth_20
\(D\) | \(D\) | dimension of the normalized cube in the convolution lemma | synth_20
\(L\) | \(L\) | Lipschitz-modulus multiplier or logarithmic pilot level | lem:jackson-convolution-modulus
\(a_i\) | \(a_i\) | first-order coordinate modulus coefficient in the convolution lemma | lem:jackson-convolution-modulus
\(b_i\) | \(b_i\) | second-order coordinate modulus coefficient in the convolution lemma | lem:jackson-convolution-modulus
\(\varphi\) | \(\varphi\in\mathbb R^D\) | angle vector at which the tensor convolution is evaluated | lem:jackson-convolution-modulus
\(\tau\) | \(\tau\in\mathbb R^D\) | shift vector integrated by the tensor Jackson convolution | lem:jackson-convolution-modulus
\((\mathcal J_Kf)(\varphi)\) | \((\mathcal J_Kf)(\varphi)\) | order-\(K\) tensor Jackson convolution of \(f\) at \(\varphi\) | synth_20
\(J_K\) | \(J_K\) | order-four Jackson kernel used in the convolution lemma | lem:jackson-convolution-modulus
\(A\) | \(A<\infty\) | universal coefficient-envelope base in the simultaneous Jackson certificate | lem:simultaneous-jackson-certificate
\(q_\jmath\) | \(q_\jmath\) | coordinate intensity for the pilot-count lemmas | lem:canonical-pilot-bad-moment
\(\Gamma_x(N')\) | \(\Gamma_x(N')\) | normalized aggregate pilot score | lem:canonical-pilot-bad-moment
\(\mathsf G_x^c\) | \(\mathsf G_x^c\) | self-normalized bad-pilot event | lem:canonical-pilot-bad-moment
\(C_t\) | \(C_t=10^{80(t+1)}\) | explicit universal constant in the pilot bad-moment bound | lem:canonical-pilot-bad-moment
\(\mathsf G_x\) | \(\mathsf G_x\) | good-pilot event controlling pilot rectangle radii | lem:good-pilot-radius-sum
\(\{b_{x,\alpha}\}_{\alpha\in\mathcal A_x}\) | \(\{b_{x,\alpha}\}_{\alpha\in\mathcal A_x}\) | coefficient family in the centered normalized Jackson expansion | lem:jackson-normalized-coefficient-envelope
\(\mathcal A_x\) | \(\mathcal A_x\) | multi-index set for the centered normalized Jackson expansion | lem:jackson-normalized-coefficient-envelope
\(h\) | \(h\) | order of a centered factorial lift | def:jackson-factorial-estimator
\(N\) | \(N\) | evaluation count argument in a centered factorial lift | def:jackson-factorial-estimator
\(z\) | \(z\) | centering argument in a centered factorial lift | def:jackson-factorial-estimator
\(q\) | \(q\) | Poisson count intensity in the factorial moment identities | lem:centered-factorial-pilot-control
\(\ell\) | \(\ell\) | summation index in the second-moment identity for factorial lifts | lem:centered-factorial-pilot-control
\(L_{\theta_x}\) | \(L_{\theta_x}\) | one-cell likelihood ratio at contrast \(\theta_x\) against baseline \(0\) | lem:dense-moment-matching-lower
\(E_0\) | \(E_0\) | expectation under the baseline one-cell law | lem:dense-moment-matching-lower
\(c_\epsilon\) | \(c_\epsilon\) | positive lower-bound constant depending on \(\epsilon\) | thm:all-estimator-lower
\(C_\epsilon\) | \(C_\epsilon\) | finite upper-bound constant depending on \(\epsilon\) | thm:jackson-factorial-upper
\(d_n\) | \(d=d_n\) | alphabet-size sequence indexed by \(n\) | thm:consistency-and-parametric-boundaries
\(\mathscr H_\epsilon^{\mathrm{const}}\) | \(\mathscr H_\epsilon^{\mathrm{const}}\) | sharp-constant derivation route for the nonsaturated risk scale | def:constant-handle
\(\mathcal P_{d,\epsilon}\) | \(\mathcal P_{d,\epsilon}\) | full-data causal completion class with observed margin in \(\mathcal D_{d,\epsilon}^{\mathrm{obs}}\) | def:model-class

# Sections

## section: Introduction
The introduction motivates estimation of the population value attained by choosing the better binary treatment within each observed categorical covariate cell. It presents the fixed-overlap, growing-alphabet problem, states the minimax mean-squared risk order \(\min\{1,d/[n\log(ed)]\}\), and previews the two ingredients behind the result: a polynomial-lifted all-data estimator and matching lower bounds for all measurable estimators. It closes with a single factual pointer to the appendix verification note for the machine-checked formal layer and theorem-local cited analytic inputs.
objs: none
bib:

home_objs: none
## section: Related work
This section positions the paper relative to causal identification, treatment-choice analysis, nonregular optimal-value inference, and large-alphabet nonsmooth functional estimation. It compares the scalar optimal-value question with rule-learning and welfare-regret results in \cite{Manski2004,Murphy2003,Hirano2009,Kitagawa2018,Qian2011,Athey2021}; with identification and targeted-learning analyses of optimal values in \cite{Robins1986,Rosenbaum1983,vanDerLaan2015,LuedtkeVanderLaan2016OptimalValue}; with nonregularity and smoothing results in \cite{Chakraborty2010,Hirano2012,Chen2023,WhitehouseChenAusternSyrgkanis2025,Wei2025}; and with large-alphabet approximation and moment-matching methods in \cite{CaiLow2011L1,JiaoVenkatHanWeissman2015Functionals,Wu2016,HanJiaoWeissman2018Local,JiaoHanWeissman2018L1,Valiant2017}. The closest rate comparisons are the normalized two-sample \(L_1\) distance results of \cite{JiaoHanWeissman2018L1} and the high-dimensional categorical-covariate linear treatment-mean rates of \cite{ZengBalakrishnanHanKennedy2024Discrete}; the section explains that the present problem concerns the cellwise maximum in the scalar optimal value under fixed overlap.
objs: none
bib: Robins1986, Rosenbaum1983, Manski2004, Murphy2003, Hirano2009, Kitagawa2018, Qian2011, Athey2021, Chakraborty2010, Hirano2012, vanDerLaan2015, LuedtkeVanderLaan2016OptimalValue, Chen2023, WhitehouseChenAusternSyrgkanis2025, Wei2025, CaiLow2011L1, JiaoVenkatHanWeissman2015Functionals, Wu2016, HanJiaoWeissman2018Local, JiaoHanWeissman2018L1, Valiant2017, ZengBalakrishnanHanKennedy2024Discrete, LeCam1986, Tsybakov2009, DeVore1993

home_objs: none
## section: Setup and assumptions
This section defines the observed sampling experiment, the fixed-overlap observed-law model, the observed optimal-regression value, minimax risk, and the full-data causal completion class. It introduces the four-cell overlap cone and the globally Lipschitz cell contribution, then states the identification and extension result showing that the observed value decomposes cellwise and that the causal optimal-treatment value agrees with the observed-law value under consistency and conditional exchangeability.
objs: synth_13, ass:iid-sampling, ass:consistency, ass:conditional-exchangeability, ass:fixed-overlap, def:observed-margin, def:observed-model-class, def:observed-optimal-value, def:minimax-risk, def:model-class, def:overlap-cone, def:global-extension, def:oracle-value, prop:identification-and-extension, prop:causal-optimal-value-corollary
bib: Robins1986, Rosenbaum1983

home_objs: ass:iid-sampling, ass:consistency, ass:conditional-exchangeability, ass:fixed-overlap, def:observed-margin, def:observed-model-class, def:observed-optimal-value, def:minimax-risk, def:model-class, def:overlap-cone, def:global-extension, def:oracle-value, prop:identification-and-extension, prop:causal-optimal-value-corollary
## section: Main results
This section states the estimation procedure and the minimax risk results. It first records the empirical-ratio estimator for bounded alphabets, then presents the Jackson-factorial estimator built from pilot rectangles, polynomial approximation of the Lipschitz cell contribution, centered factorial lifts, clipping, projection, and Rao--Blackwellization. It states the uniform finite-sample upper bound, the equal-propensity \(L_1\) embedding, the all-regime lower bound, the matched two-sided minimax rate, and the resulting uniform-consistency and parametric-rate characterizations for both the observed-law and causal-completion formulations.
objs: def:empirical-ratio-estimator, synth_18, def:jackson-kernel, def:jackson-factorial-estimator, synth_3, thm:jackson-factorial-upper, def:l1-embedding, synth_7, synth_6, prop:equal-propensity-l1-reduction, thm:all-estimator-lower, thm:matched-minimax-frontier, synth_4, thm:consistency-and-parametric-boundaries
bib: DeVore1993, JiaoVenkatHanWeissman2015Functionals, CaiLow2011L1, JiaoHanWeissman2018L1, LeCam1986, Tsybakov2009

home_objs: def:empirical-ratio-estimator, def:jackson-kernel, def:jackson-factorial-estimator, thm:jackson-factorial-upper, def:l1-embedding, prop:equal-propensity-l1-reduction, thm:all-estimator-lower, thm:matched-minimax-frontier, thm:consistency-and-parametric-boundaries
## section: Discussion and limitations
This section interprets the matched rate in terms of alphabet growth, exact treatment-effect ties, unequal propensities, null cells, boundary outcome means, and bounded-alphabet behavior. It records the lineage comparison with the archived predecessor on the same formal class. In its limitations and future-work discussion, it presents the sharp-overlap-constant problem as an open question for nonsaturated sequences through the constant-derivation route.
objs: prop:parent-reduction, def:constant-handle, oeq:sharp-overlap-constant
bib:

home_objs: prop:parent-reduction, def:constant-handle, oeq:sharp-overlap-constant
## section: Appendix: Analytic ingredients for the upper bound
This appendix proves the simultaneous Jackson certificate and the centered-factorial pilot-control lemma used by the upper bound. It develops the polynomial approximation and coefficient-envelope estimates on pilot-local rectangles, including rectangles touching the cone vertex, coordinate faces, and tie surfaces, and then derives the local bias and variance controls for the clipped cell estimates, including the self-normalized pilot bad-moment bound.
objs: lem:tensor-jackson-coefficient-envelope, lem:jackson-tensor-extraction, synth_20, lem:jackson-convolution-modulus, lem:simultaneous-jackson-certificate, lem:canonical-pilot-bad-moment, synth_12, lem:good-pilot-radius-sum, lem:jackson-normalized-coefficient-envelope, synth_5, lem:centered-factorial-pilot-control
bib: DeVore1993, JiaoVenkatHanWeissman2015Functionals

home_objs: lem:tensor-jackson-coefficient-envelope, lem:jackson-tensor-extraction, lem:jackson-convolution-modulus, lem:simultaneous-jackson-certificate, lem:canonical-pilot-bad-moment, lem:good-pilot-radius-sum, lem:jackson-normalized-coefficient-envelope, lem:centered-factorial-pilot-control
## section: Appendix: Moment matching and lower-bound details
This appendix contains the dense lower-bound construction and its proof. It defines the dense contrast submodel, the best-approximation moment-matched priors for \(|t|\), the Poissonized mixtures, and the target separation, then proves the amplitude, total-variation, prior-concentration, fuzzy-hypothesis, and depoissonization steps that feed the all-estimator lower bound.
objs: synth_16, synth_15, def:dense-moment-matching-construction, lem:dense-amplitude-range, synth_14, synth_11, synth_9, lem:dense-moment-matching-lower
bib: CaiLow2011L1, LeCam1986, Tsybakov2009, JiaoHanWeissman2018L1

home_objs: def:dense-moment-matching-construction, lem:dense-amplitude-range, lem:dense-moment-matching-lower
## section: Appendix: Verification note
This appendix consolidates the Lean verification scope for the frozen layer. It states that the displayed assumptions, definitions, algorithms, lemmas, propositions, and theorems are the machine-checked mathematical objects for the paper, while published approximation and moment-matching inputs are cited at their theorem-local use sites through the verified citation pool.
objs: none
bib: CaiLow2011L1, DeVore1993, LeCam1986, Tsybakov2009
home_objs: none
