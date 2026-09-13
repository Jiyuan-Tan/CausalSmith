# Title
**Quotient-law inference with latent treatment-effect collisions**

**Contribution statement.** The paper establishes a gap-free \(W_1\) modulus for quotient latent-effect laws in a uniformly conditioned finite proxy causal model with fixed known dimensions, derives collision-uniform root-\(n\) law estimation and honest cluster-adaptive confidence reporting, and characterizes the matching inverse-gap behavior of effect-ordered latent weights on the stated gap-local strata.

# Notation
notation_gaps: \(D_{\mathrm{KL}}(\mu\Vert\nu)\)=Kullback--Leibler divergence appears in frozen assumptions and theorem statements and needs an anchored definition environment, full-data record space for \((U,T,X,Z,Y(0),Y(1),Y)\)=full-data laws and model-class restrictions appear before an anchored full-data record-space definition

env_overrides: def:summary-space-repair=algorithmv, def:structured-lattice-program=algorithmv, def:finite-net-program=algorithmv, def:wasserstein-confidence-set=algorithmv, def:cluster-report=algorithmv, def:labeled-weight-estimator=algorithmv, def:constructive-repair-handle=algorithmv, def:finite-net-law-estimator=algorithmv, oeq:constructive-total-repair=remarkv, prop:observed-vmw-margin-inclusion=propositionv, prop:summary-closure-compact=propositionv, prop:summary-repair-total-borel=propositionv, prop:two-class-witness-valid=propositionv, prop:same-class-quotient-minimax=propositionv, prop:same-class-labeled-minimax=propositionv, prop:polynomial-net-law-estimator=propositionv

\(C_0\) | \(C_0\) | simultaneous-concentration constant | def:concentration-constant
\(\widehat M_{t,n}\) | \(\widehat M_{t,n}\) | empirical armwise \(ZX^\top\) moment with total empty-arm convention | def:empirical-summary-primitives
\(\widehat N_{t,n}\) | \(\widehat N_{t,n}\) | empirical armwise \(YZX^\top\) moment with total empty-arm convention | def:empirical-summary-primitives
\(\widehat m_{X,n}\) | \(\widehat m_{X,n}\) | empirical target-proxy mean | def:empirical-summary-primitives
\(\widehat S_n\) | \(\widehat S_n\) | empirical five-block observable summary | def:empirical-summary-primitives
\(e_1\in\mathbb R^{d_x}\) | \(e_1\in\mathbb R^{d_x}\) | first canonical basis vector | def:first-basis
\(c_{\mathrm{loc}}\) | \(c_{\mathrm{loc}}\) | local Kullback--Leibler radius constant in \((0,1)\) | def:local-kl-radius
\(O_{d_x,d_z}\) | \(O_{d_x,d_z}\) | observed-record space of quadruples \(O=(T,X,Z,Y)\) | def:observed-record-space
\(O=(T,X,Z,Y)\) | \(O=(T,X,Z,Y)\) | observed record | def:observed-margin
\(T\) | \(T\) | binary treatment | def:observed-record-space
\(X\in\mathbb R^{d_x}\) | \(X\in\mathbb R^{d_x}\) | target-proxy vector | def:observed-record-space
\(Z\in\mathbb R^{d_z}\) | \(Z\in\mathbb R^{d_z}\) | reference-proxy vector | def:observed-record-space
\(Y\in\mathbb R\) | \(Y\in\mathbb R\) | observed outcome | def:observed-record-space
\(d_x\) | \(d_x\) | fixed target-proxy dimension | def:observed-record-space
\(d_z\) | \(d_z\) | fixed reference-proxy dimension | def:observed-record-space
\(W_1(\nu,\xi)\) | \(W_1(\nu,\xi)\) | minimum transport cost between represented atomic laws | def:wasserstein-distance
\(\nu\) | \(\nu\) | represented atomic law in the transport metric | def:wasserstein-distance
\(\xi\) | \(\xi\) | represented atomic law in the transport metric and confidence class | def:wasserstein-distance
\(\gamma_{ij}\) | \(\gamma_{ij}\) | nonnegative transport coupling between represented atoms | def:wasserstein-distance
\(x_i\) | \(x_i\) | atom location in the first represented atomic law | def:wasserstein-distance
\(y_j\) | \(y_j\) | atom location in the second represented atomic law | def:wasserstein-distance
\(P\) | \(P\) | full-data probability law carrying \((U,T,X,Z,Y(0),Y(1),Y)\) | def:observed-margin
\(P_O:=P\circ O^{-1}\) | \(P_O:=P\circ O^{-1}\) | observed-data marginal of a full-data law | def:observed-margin
\(U\) | \(U\) | latent class taking values in \(\{1,\ldots,k\}\) | def:model-class
\(Y(0),Y(1)\) | \(Y(0),Y(1)\) | potential outcomes under the two treatment arms | def:model-class
\(k\) | \(k\) | fixed latent cardinality | def:model-class
\(p_u:=P(U=u)\) | \(p_u:=P(U=u)\) | latent-class mass | def:latent-mass
\(\mu_{tu}:=E_P[Y(t)\mid U=u]\) | \(\mu_{tu}:=E_P[Y(t)\mid U=u]\) | latent conditional potential-outcome mean | def:latent-mean
\(\tau_u:=\mu_{1u}-\mu_{0u}\) | \(\tau_u:=\mu_{1u}-\mu_{0u}\) | latent-class treatment effect | def:latent-effect
\(A_t\in\mathbb R^{d_z\times k}\) | \(A_t\in\mathbb R^{d_z\times k}\) | reference-proxy feature matrix | def:reference-feature
\(A_t(i,u):=E_P[Z_i\mid U=u,T=t]\) | \(A_t(i,u):=E_P[Z_i\mid U=u,T=t]\) | reference-proxy feature entry | def:reference-feature
\(B\in\mathbb R^{d_x\times k}\) | \(B\in\mathbb R^{d_x\times k}\) | target-proxy feature matrix | def:target-feature
\(B(i,u):=E_P[X_i\mid U=u]\) | \(B(i,u):=E_P[X_i\mid U=u]\) | target-proxy feature entry | def:target-feature
\(L_\tau:=4L\sqrt{d_z}/\sigma_0\) | \(L_\tau:=4L\sqrt{d_z}/\sigma_0\) | derived effect-support radius | def:effect-radius
\(\delta(P)\) | \(\delta(P)\) | smallest strictly positive distance between two positive-mass latent effects, with \(+\infty\) for a singleton quotient law | def:effect-gap
\(M_t(P):=E_P[ZX^\top\mid T=t]\) | \(M_t(P):=E_P[ZX^\top\mid T=t]\) | observable armwise \(ZX^\top\) population moment | def:observable-population-moments
\(N_t(P):=E_P[YZX^\top\mid T=t]\) | \(N_t(P):=E_P[YZX^\top\mid T=t]\) | observable armwise \(YZX^\top\) population moment | def:observable-population-moments
\(m_X(P):=E_P[X]\) | \(m_X(P):=E_P[X]\) | observable target-proxy population mean | def:observable-population-moments
\(r_{n,\alpha}:=C_0L\sqrt{\log(C_0/\alpha)/n}\) | \(r_{n,\alpha}:=C_0L\sqrt{\log(C_0/\alpha)/n}\) | simultaneous concentration radius | def:summary-radius
\(\mathcal P_{\le k}([-L_\tau,L_\tau])\) | \(\mathcal P_{\le k}([-L_\tau,L_\tau])\) | probability laws on \([-L_\tau,L_\tau]\) with at most \(k\) distinct atoms | def:atomic-law-class
\(\mathcal P_k([-L_\tau,L_\tau])\) | \(\mathcal P_k([-L_\tau,L_\tau])\) | abbreviation for the at-most-\(k\) atomic-law class | def:atomic-law-class
\(\nu_\xi\) | \(\nu_\xi\) | probability law obtained by aggregating repeated atom slots of \(\xi\) | def:atomic-law-class
\(p^{\uparrow}(P)\) | \(p^{\uparrow}(P)\) | effect-ordered latent masses with barycentric collision fallback | def:ordered-mass-target
\(P_{g,h}\) | \(P_{g,h}\) | factorization-preserving two-class path law | def:path-law-family
\(\operatorname{AtomFloor}(m,\xi)\) | \(\operatorname{AtomFloor}(m,\xi)\) | aggregate distinct-atom mass floor | def:atom-floor
\(m\) | \(m\) | mass threshold argument in the atom-floor predicate | def:atom-floor
\(C_{\mathrm{lat}}\) | \(C_{\mathrm{lat}}\) | prescribed structured-lattice stability constant | def:structured-lattice-constant
\(H_n\) | \(H_n\) | structured-lattice scale integer | def:structured-lattice-program
\(q_n\) | \(q_n\) | structured-lattice mesh width | def:structured-lattice-program
\(s_0\) | \(s_0\) | singular-value threshold scale \(\pi_0\sigma_0^2\) | def:structured-lattice-program
\(\operatorname{stack}(M_0,M_1):=[M_0^\top,M_1^\top]^\top\) | \(\operatorname{stack}(M_0,M_1):=[M_0^\top,M_1^\top]^\top\) | vertical matrix stacking operation | def:structured-lattice-program
\(\widehat D_n(s)\) | \(\widehat D_n(s)\) | thresholded empirical compressed operator at summary \(s\) | def:structured-lattice-program
\(\mathcal V_n\) | \(\mathcal V_n\) | structured lattice of polar factors | def:structured-lattice-program
\(\mathcal R_n\) | \(\mathcal R_n\) | structured lattice of invertible conditioning matrices | def:structured-lattice-program
\(\mathcal P_n\) | \(\mathcal P_n\) | simplex grid with coordinate lower bound \(\pi_0\) | def:structured-lattice-program
\(\mathcal T_n\) | \(\mathcal T_n\) | clipped effect grid in \([-L_\tau,L_\tau]^k\) | def:structured-lattice-program
\(\mathcal A_n:=\mathcal V_n\times\mathcal R_n\times\mathcal P_n\times\mathcal T_n\) | \(\mathcal A_n:=\mathcal V_n\times\mathcal R_n\times\mathcal P_n\times\mathcal T_n\) | product of the structured lattice factor grids | def:structured-lattice-program
\(\vartheta=(V,R,p,\tau)\) | \(\vartheta=(V,R,p,\tau)\) | structured-lattice candidate | def:structured-lattice-program
\(D_\vartheta:=VR^{-1}\operatorname{diag}(\tau)RV^\top\) | \(D_\vartheta:=VR^{-1}\operatorname{diag}(\tau)RV^\top\) | model-implied compressed operator for candidate \(\vartheta\) | def:structured-lattice-program
\(m_\vartheta:=VR^\top p\) | \(m_\vartheta:=VR^\top p\) | model-implied target-proxy mean for candidate \(\vartheta\) | def:structured-lattice-program
\(b_\vartheta:=RV^\top e_1\) | \(b_\vartheta:=RV^\top e_1\) | model-implied anchor vector for candidate \(\vartheta\) | def:structured-lattice-program
\(\lambda_\vartheta:=\sum_up_u\delta_{\tau_u}\) | \(\lambda_\vartheta:=\sum_up_u\delta_{\tau_u}\) | atomic law attached to candidate \(\vartheta\) | def:structured-lattice-program
\(J_n(\vartheta;s)\) | \(J_n(\vartheta;s)\) | structured-lattice objective evaluated at summary \(s\) | def:structured-lattice-program
\(\widehat\lambda_n\) | \(\widehat\lambda_n\) | structured-lattice quotient-law estimator | def:structured-lattice-program
\(\mathbf1_k\) | \(\mathbf1_k\) | \(k\)-vector of ones used in the anchor criterion | def:structured-lattice-program
\(A=(A_i)_i\) | \(A=(A_i)_i\) | stored representative library | def:finite-net-program
\(S_i\) | \(S_i\) | five-block summary stored in representative \(A_i\) | def:finite-net-program
\(\operatorname{rank}_{\mathrm{lex}}(i)\) | \(\operatorname{rank}_{\mathrm{lex}}(i)\) | lexicographic candidate rank | def:finite-net-program
\(\lambda^{\mathrm{spec}}(A_i)\) | \(\lambda^{\mathrm{spec}}(A_i)\) | real atomic effect law returned by the thresholded spectral run | def:finite-net-program
\(\omega\) | \(\omega\) | observed sample input | def:finite-net-program
\(\operatorname{NetProgram}(A,\omega)\) | \(\operatorname{NetProgram}(A,\omega)\) | finite-library spectral program | def:finite-net-program
\(\operatorname{law}(\operatorname{NetProgram}(A,\omega))\) | \(\operatorname{law}(\operatorname{NetProgram}(A,\omega))\) | returned effect-law component of the finite-library program | def:finite-net-program
\(\mathcal M\) | \(\mathcal M\) | uniformly conditioned proxy causal model class | def:model-class
\(L\) | \(L\) | uniform boundedness radius in the model assumptions | ass:bounded-x
\(\pi_0\) | \(\pi_0\) | latent-arm positivity margin | ass:latent-arm-positivity
\(\sigma_0\) | \(\sigma_0\) | proxy-rank singular-value margin | ass:proxy-rank-margin
\(S(P)\) | \(S(P)\) | observable conditional moment summary | def:observable-summary
\(d_S(s,s')\) | \(d_S(s,s')\) | metric on observable moment summaries | def:observable-summary
\(N_{t,n}\) | \(N_{t,n}\) | armwise treatment count in an \(n\)-sample | def:empirical-summary
\(V(P)\) | \(V(P)\) | orthonormal basis for the stacked row space | def:compressed-operator
\(\Delta Q(P)\) | \(\Delta Q(P)\) | compressed effect operator | def:compressed-operator
\(a(P)^\top\) | \(a(P)^\top\) | left spectral anchor | def:compressed-operator
\(c(P):=V(P)^\top e_1\) | \(c(P):=V(P)^\top e_1\) | right spectral anchor | def:compressed-operator
\(\nu_P\) | \(\nu_P\) | quotient latent-effect probability law | def:quotient-law
\(\mathcal M(g)\) | \(\mathcal M(g)\) | gap-local stratum with distinct effects | def:gap-stratum
\(g\) | \(g\) | local effect-gap scale | ass:gap-window
\(\mathcal E_n\) | \(\mathcal E_n\) | observed i.i.d. proxy experiment | def:sample-experiment
\(Q_P^{(n)}=P_O^{\otimes n}\) | \(Q_P^{(n)}=P_O^{\otimes n}\) | \(n\)-fold observed sample law | def:sample-experiment
\(n\) | \(n\) | observed sample size | def:sample-experiment
\(\mathscr S:=S(\mathcal M)\) | \(\mathscr S:=S(\mathcal M)\) | admissible summary image | def:summary-closure
\(\mathcal K:=\overline{\mathscr S}\) | \(\mathcal K:=\overline{\mathscr S}\) | \(d_S\)-closure of the admissible summary image | def:summary-closure
\(F:\mathscr S\to\mathcal P_k([-L_{\tau},L_{\tau}])\) | \(F:\mathscr S\to\mathcal P_k([-L_{\tau},L_{\tau}])\) | summary-to-quotient-law functional on admissible summaries | def:summary-closure
\(\tau_\star\) | \(\tau_\star\) | common homogeneous latent-class effect | def:summary-closure
\(\overline F:\mathcal K\to\mathcal P_k([-L_{\tau},L_{\tau}])\) | \(\overline F:\mathcal K\to\mathcal P_k([-L_{\tau},L_{\tau}])\) | continuous extension of \(F\) to \(\mathcal K\) | def:summary-space-repair
\(\Pi(s)\) | \(\Pi(s)\) | Borel nearest-summary selector with fallback | def:summary-space-repair
\(\widehat\nu_n\) | \(\widehat\nu_n\) | theoretical nearest-summary quotient-law estimator | def:summary-space-repair
\(\alpha\) | \(\alpha\) | confidence miscoverage level | def:summary-radius
\(\mathcal C_{n,\alpha}\) | \(\mathcal C_{n,\alpha}\) | original summary-inversion confidence set | def:wasserstein-confidence-set
\(m_\star:=\pi_0\) | \(m_\star:=\pi_0\) | atom-floor constant | def:wasserstein-confidence-set
\(R_{n,\alpha}:=C_{\mathrm{lat}}(r_{n,\alpha}+(\sqrt n)^{-1})\) | \(R_{n,\alpha}:=C_{\mathrm{lat}}(r_{n,\alpha}+(\sqrt n)^{-1})\) | computable confidence-set radius | def:wasserstein-confidence-set
\(\mathcal P_{\le k,m_\star}([-L_\tau,L_\tau])\) | \(\mathcal P_{\le k,m_\star}([-L_\tau,L_\tau])\) | \(k\)-atomic laws with distinct-atom mass at least \(m_\star\) | def:wasserstein-confidence-set
\(\mathcal C^{\mathrm{alg}}_{n,\alpha}\) | \(\mathcal C^{\mathrm{alg}}_{n,\alpha}\) | computable \(W_1\) confidence set centered at \(\widehat\lambda_n\) | def:wasserstein-confidence-set
\(E_P:=\{d_S(\widehat S_n,S(P))\le r_{n,\alpha}\}\) | \(E_P:=\{d_S(\widehat S_n,S(P))\le r_{n,\alpha}\}\) | simultaneous concentration event | def:cluster-report
\(\rho_{n,\alpha}:=R_{n,\alpha}/m_\star\) | \(\rho_{n,\alpha}:=R_{n,\alpha}/m_\star\) | cluster association radius | def:cluster-report
\(\widehat{\mathscr K}_{n,\alpha}\) | \(\widehat{\mathscr K}_{n,\alpha}\) | empirical support components | def:cluster-report
\(C\in\widehat{\mathscr K}_{n,\alpha}\) | \(C\in\widehat{\mathscr K}_{n,\alpha}\) | empirical support component in the cluster report | def:cluster-report
\(K_C(P)\) | \(K_C(P)\) | true atoms associated with component \(C\) | def:cluster-report
\(K_C(\xi)\) | \(K_C(\xi)\) | candidate atoms associated with component \(C\) | def:cluster-report
\(I_C\) | \(I_C\) | computable mass interval for component \(C\) | def:cluster-report
\(z_a\) | \(z_a\) | binary support-association variable in the cluster program | def:cluster-report
\(\mathfrak R_{n,\alpha}\) | \(\mathfrak R_{n,\alpha}\) | cluster report of support and mass intervals | def:cluster-report
\(\Delta_C(P)\) | \(\Delta_C(P)\) | external gap of true atoms associated with component \(C\) | def:cluster-report
\(\widehat s_n\) | \(\widehat s_n\) | number of atoms in \(\widehat\nu_n\) | def:labeled-weight-estimator
\(\widehat w_{\ell,n}\) | \(\widehat w_{\ell,n}\) | ordered atom mass of \(\widehat\nu_n\) | def:labeled-weight-estimator
\(\widehat\tau_{\ell,n}\) | \(\widehat\tau_{\ell,n}\) | ordered atom location of \(\widehat\nu_n\) | def:labeled-weight-estimator
\(\widehat p_n^{\uparrow}\) | \(\widehat p_n^{\uparrow}\) | ordered-weight estimator | def:labeled-weight-estimator
\(P_{\varepsilon}^{\mathrm{wit}}\) | \(P_{\varepsilon}^{\mathrm{wit}}\) | explicit two-class Bernoulli proxy witness law | def:two-class-witness
\(P_0^{\mathrm{wit}}\) | \(P_0^{\mathrm{wit}}\) | zero-perturbation two-class Bernoulli proxy witness law | def:two-class-witness
\(P_{a/\sqrt n}^{\mathrm{wit}}\) | \(P_{a/\sqrt n}^{\mathrm{wit}}\) | two-class Bernoulli proxy witness law at perturbation \(a/\sqrt n\) | def:two-class-witness
\(\varepsilon\) | \(\varepsilon\) | collision-witness effect displacement | def:two-class-witness
\(\mathcal L_n^\nu\) | \(\mathcal L_n^\nu\) | local quotient-law KL experiment | def:local-quotient-experiment
\(\mathcal L_{n,g}^p\) | \(\mathcal L_{n,g}^p\) | local labeled-weight KL experiment | def:local-weight-experiment
\(m=(m_j)_{0\le j<2k}\) | \(m=(m_j)_{0\le j<2k}\) | first \(2k\) spectral moments at the realized empirical summary | def:constructive-repair-handle
\(m_j\) | \(m_j\) | \(j\)th spectral moment at the realized empirical summary | def:constructive-repair-handle
\(\widehat\nu_n^{\mathrm{net}}\) | \(\widehat\nu_n^{\mathrm{net}}\) | class-advised finite-net quotient-law estimator | def:finite-net-law-estimator
\(D:=4d_zd_x+d_x\) | \(D:=4d_zd_x+d_x\) | dimension of the observable summary coordinate box | def:finite-net-law-estimator
\(b:=4\sqrt{d_zd_x}+\sqrt{d_x}\) | \(b:=4\sqrt{d_zd_x}+\sqrt{d_x}\) | grid side-length normalizer | def:finite-net-law-estimator
\(\epsilon_n:=n^{-1/2}\) | \(\epsilon_n:=n^{-1/2}\) | finite-net mesh scale | def:finite-net-law-estimator
\(q_{n,\ell}\) | \(q_{n,\ell}\) | admissible-summary representative selected from a grid cube | def:finite-net-law-estimator
\(\widehat q_n\) | \(\widehat q_n\) | nearest finite-net representative summary | def:finite-net-law-estimator
\(\Delta\) | \(\Delta\) | compressed effect operator formed at the selected finite-net representative | def:finite-net-law-estimator
\(a\) | \(a\) | theorem-local lower-bound amplitude or finite-net left anchor, according to context | def:finite-net-law-estimator
\(c\) | \(c\) | theorem-local lower-bound constant or finite-net right anchor, according to context | def:finite-net-law-estimator
\(\lambda\) | \(\lambda\) | eigenvalue in the finite-net spectral construction | def:finite-net-law-estimator
\(E_\lambda\) | \(E_\lambda\) | spectral projector polynomial for eigenvalue \(\lambda\) | def:finite-net-law-estimator
\(\eta\) | \(\eta\) | generic tail probability | lem:uniform-summary-concentration
\(\mathcal V_n^\nu\) | \(\mathcal V_n^\nu\) | published-VMW comparator class for quotient-law lower bounds | thm:published-vmw-converse-transfer
\(h(n,g)\) | \(h(n,g)\) | calibrated labeled-path displacement rule | thm:published-vmw-converse-transfer
\(P_{g,0}\) | \(P_{g,0}\) | zero-displacement endpoint of the factorization-preserving path law | def:path-law-family
\(P_{g,h(n,g)}\) | \(P_{g,h(n,g)}\) | calibrated endpoint of the factorization-preserving path law | def:path-law-family
\(\mathcal V_{n,g}^p\) | \(\mathcal V_{n,g}^p\) | published-VMW comparator class for labeled-weight lower bounds | thm:published-vmw-converse-transfer
\(\ell_n\) | \(\ell_n\) | integer mass-floor threshold in the structured lattice | prop:polynomial-net-law-estimator
\(G\) | \(G\) | rectangular matrix in the thresholded pseudoinverse definition | prop:polynomial-net-law-estimator
\(\sigma_j\) | \(\sigma_j\) | singular value of \(G\) | prop:polynomial-net-law-estimator
\(u_j\) | \(u_j\) | left singular vector of \(G\) | prop:polynomial-net-law-estimator
\(v_j\) | \(v_j\) | right singular vector of \(G\) | prop:polynomial-net-law-estimator
\(G^\dagger_{\ge s_0/2}\) | \(G^\dagger_{\ge s_0/2}\) | thresholded rectangular pseudoinverse | prop:polynomial-net-law-estimator
\(\widehat D_n\) | \(\widehat D_n\) | thresholded empirical compressed operator formed from empirical moments | prop:polynomial-net-law-estimator
\(c_V\) | \(c_V\) | displayed structured-lattice grid constant | prop:polynomial-net-law-estimator
\(K_D\) | \(K_D\) | displayed structured-lattice operator constant | prop:polynomial-net-law-estimator
\(A_D\) | \(A_D\) | displayed structured-lattice perturbation constant | prop:polynomial-net-law-estimator
\(K_f\) | \(K_f\) | displayed structured-lattice feature constant | prop:polynomial-net-law-estimator
\(c_D\) | \(c_D\) | displayed structured-lattice compressed-operator approximation constant | prop:polynomial-net-law-estimator
\(c_m\) | \(c_m\) | displayed structured-lattice mean approximation constant | prop:polynomial-net-law-estimator
\(c_b\) | \(c_b\) | displayed structured-lattice anchor approximation constant | prop:polynomial-net-law-estimator
\(c_{\mathrm{grid}}\) | \(c_{\mathrm{grid}}\) | aggregate structured-lattice grid constant | prop:polynomial-net-law-estimator
\(B_{\mathrm{lat}}\) | \(B_{\mathrm{lat}}\) | aggregate structured-lattice stability constant | prop:polynomial-net-law-estimator

# Sections
## section: Introduction
The introduction will motivate proxy causal inference for latent treatment-effect heterogeneity and introduce \(\nu_P\), the quotient latent-effect law, as the regular inferential target when latent classes can share an effect value. It will preview the paper's positive scope: a gap-free \(W_1\) stability theorem from observable proxy moments to \(\nu_P\), collision-uniform root-\(n\) law estimation, honest confidence sets, cluster-adaptive reports, and inverse-gap rates for effect-ordered weights on the stated uniformly conditioned and gap-local classes. A single factual sentence will direct readers to the appendix verification note for the machine-checked theorem scope.
objs: none
bib: VirkMazaheriWu2026, MazaheriSquiresUhler2025, MiaoGengTchetgen2018

home_objs: none
## section: Related work
This section will position the paper in proxy causal identification, finite-mixture and spectral identification, and Wasserstein inference for singular mixtures. The closest comparison is \cite{VirkMazaheriWu2026}, which supplies the compressed observable operator and separated recovery theory; the section will compare the present quotient-law \(W_1\) guarantees with finite-mixture collision rates in \cite{HeinrichKahn2018}, moment-projection methods in \cite{WuYang2020}, and Wasserstein confidence-set constructions in \cite{DeoRandrianarisoa2023}.
objs: none
bib: Neyman1990, Rubin1974, Holland1986, ImbensRubin2015, RosenbaumRubin1983, Pearl2009, Robins1986, Pearson1894, Hansen1982, LeCam1986, PolyanskiyWu2019, MiaoGengTchetgen2018, TchetgenTchetgen2024, ShiMiaoNelsonTchetgen2020, CuiPuShiMiaoTchetgen2024, MiaoHuOgburnZhou2023, QiMiaoZhang2024, LiuParkLiTchetgen2024, LiLindermanShiTchetgen2024, AiShan2025, SahaBatesShah2026, VanAmsterdamEtAl2022, Teicher1963, Lindsay1995, AllmanMatiasRhodes2009, Hu2008, HuSchennach2008, KasaharaShimotsu2009, BonhommeJochmansRobin2016, HsuKakadeZhang2009, Anandkumar2014, SidiropoulosBro2000, BauerFike1960, Kato1995, DavisKahan1970, StewartSun1990, MazaheriSquiresUhler2025, VirkMazaheriWu2026, Nguyen2013, HoNguyenWeak2016, HeinrichKahn2018, HoNguyen2016, WuYang2020, DossWuYangZhou2023, ManoleHo2022, NguyenLeRinaldoHo2026, DeoRandrianarisoa2023, RobinsVanDerVaart2006, BingBuneaNilesWeed2025, NilesWeedRigollet2022

home_objs: none
## section: Setup and assumptions
This section will introduce the observed record and observed margin, the full-data proxy causal model, the conditional-independence restrictions, boundedness restrictions, uniform latent-arm positivity and proxy-rank margins, observable summaries, the compressed operator, the atomic \(W_1\) target space, the quotient latent-effect law, the gap-local stratum for ordered weights, and the observed i.i.d. experiment. It will record the derived embedding into the VMW moment structure and compactness of the admissible summary closure, which together provide the population domain for the main stability result.
objs: synth_8, synth_10, synth_18, synth_19, synth_21, synth_28, synth_29, synth_30, synth_33, synth_24, synth_35, synth_36, synth_32, synth_34, synth_7, synth_37, synth_9, def:observed-record-space, def:wasserstein-distance, def:observed-margin, def:latent-mass, def:latent-mean, def:latent-effect, def:reference-feature, def:target-feature, def:effect-radius, def:effect-gap, def:observable-population-moments, def:atomic-law-class, def:ordered-mass-target, def:atom-floor, ass:reference-proxy-separation, ass:target-proxy-separation, ass:consistency, ass:latent-ignorability, ass:anchor, ass:bounded-x, ass:bounded-proxy-product, ass:bounded-outcome-proxy-product, ass:latent-arm-positivity, ass:proxy-rank-margin, ass:gap-window, ass:distinct-effects, def:model-class, def:observable-summary, def:empirical-summary-primitives, def:empirical-summary, def:first-basis, synth_1, synth_25, def:compressed-operator, def:quotient-law, def:gap-stratum, def:sample-experiment, def:summary-closure, prop:observed-vmw-margin-inclusion, prop:summary-closure-compact
bib: VirkMazaheriWu2026, BrownPurves1973

home_objs: def:observed-record-space, def:wasserstein-distance, def:observed-margin, def:latent-mass, def:latent-mean, def:latent-effect, def:reference-feature, def:target-feature, def:effect-radius, def:effect-gap, def:observable-population-moments, def:atomic-law-class, def:ordered-mass-target, def:atom-floor, ass:reference-proxy-separation, ass:target-proxy-separation, ass:consistency, ass:latent-ignorability, ass:anchor, ass:bounded-x, ass:bounded-proxy-product, ass:bounded-outcome-proxy-product, ass:latent-arm-positivity, ass:proxy-rank-margin, ass:gap-window, ass:distinct-effects, def:model-class, def:observable-summary, def:empirical-summary-primitives, def:empirical-summary, def:first-basis, def:compressed-operator, def:quotient-law, def:gap-stratum, def:sample-experiment, def:summary-closure, prop:observed-vmw-margin-inclusion, prop:summary-closure-compact
## section: Main results: law stability and estimation
This section will present the \(W_1\) modulus as the central population result and then build the two law estimators used in the paper: the closure-based nearest-summary estimator and the sample-evaluable structured-lattice estimator. The section will state the collision-uniform root-\(n\) theorem for both estimators and explain the role of the lattice construction as the operative computational estimator for the quotient law.
objs: def:concentration-constant, def:summary-radius, synth_27, def:summary-space-repair, def:structured-lattice-constant, def:structured-lattice-program, lem:uniform-summary-concentration, thm:gap-free-positive-measure-modulus, prop:summary-repair-total-borel, synth_16, prop:polynomial-net-law-estimator, thm:collision-uniform-root-n
bib: VirkMazaheriWu2026, BrownPurves1973, Kato1995, BauerFike1960, WuYang2020

home_objs: def:concentration-constant, def:summary-radius, def:summary-space-repair, def:structured-lattice-constant, def:structured-lattice-program, lem:uniform-summary-concentration, thm:gap-free-positive-measure-modulus, prop:summary-repair-total-borel, prop:polynomial-net-law-estimator, thm:collision-uniform-root-n
## section: Confidence sets, cluster reports, and ordered weights
This section will present the original summary-inversion confidence set, the computable \(W_1\) confidence set centered at \(\widehat\lambda_n\), and the report that converts law-level uncertainty into support intervals and component mass intervals. It will then state the ordered-weight estimator and its clipped inverse-gap guarantee on the gap-local stratum, using the preceding law-level results to separate regular quotient-law inference from label-sensitive weight recovery.
objs: def:wasserstein-confidence-set, def:cluster-report, def:labeled-weight-estimator, thm:honest-root-n-confidence, thm:cluster-adaptive-report, thm:labeled-weight-upper
bib: DeoRandrianarisoa2023, RobinsVanDerVaart2006, Nguyen2013, HeinrichKahn2018, HoNguyen2016, ManoleHo2022, NguyenLeRinaldoHo2026

home_objs: def:wasserstein-confidence-set, def:cluster-report, def:labeled-weight-estimator, thm:honest-root-n-confidence, thm:cluster-adaptive-report, thm:labeled-weight-upper
## section: Lower bounds and sharp rates
This section will introduce the explicit two-class Bernoulli witness, the local quotient-law and labeled-weight KL experiments, and the Le Cam two-point arguments that match the upper rates on the stated classes. It will also state the witness-pair transfer principle for published-VMW comparator classes and keep the transfer scope tied to the displayed two-point containments.
objs: def:local-kl-radius, synth_14, def:path-law-family, def:published-vmw-regimes, synth_6, synth_15, ass:local-quotient-neighborhood, ass:local-weight-neighborhood, def:two-class-witness, def:local-quotient-experiment, def:local-weight-experiment, prop:two-class-witness-valid, thm:matching-local-lower-bounds, prop:same-class-quotient-minimax, prop:same-class-labeled-minimax, synth_31, synth_12, synth_11, synth_13, thm:published-vmw-converse-transfer
bib: LeCam1986, PolyanskiyWu2019, VirkMazaheriWu2026, MiaoGengTchetgen2018

home_objs: def:local-kl-radius, def:path-law-family, def:published-vmw-regimes, ass:local-quotient-neighborhood, ass:local-weight-neighborhood, def:two-class-witness, def:local-quotient-experiment, def:local-weight-experiment, prop:two-class-witness-valid, thm:matching-local-lower-bounds, prop:same-class-quotient-minimax, prop:same-class-labeled-minimax, thm:published-vmw-converse-transfer
## section: Discussion, extensions, and open questions
This section will interpret the paper's law-level regularity, the role of cluster reports when effects are resolved at the confidence radius, and the computational status of the two confidence constructions. In a clearly labelled open-questions discussion, it will present exact polynomial-time computation of the original sharp summary-inversion image, unknown \(k\), and application-specific mapping conditions as future work.
objs: oeq:constructive-total-repair
bib: VirkMazaheriWu2026, VanAmsterdamEtAl2022

home_objs: oeq:constructive-total-repair
## section: Appendix A: probability, selection, and concentration
This appendix section will supply the auxiliary probability and measurability material behind the observed i.i.d. experiment, nearest-summary selection, simultaneous summary concentration, moment factorization, envelope derivations, atomic-law comparisons, and witness/path bookkeeping. These lemmas will appear before the proof sections that use them.
objs: lem:borel-nearest-point-selector, lem:arm-mass-lower-bound, lem:observed-proxy-moment-factorization, lem:proxy-coordinate-envelopes, lem:latent-mean-envelope, lem:latent-effect-envelope, lem:witness-latent-mass, lem:witness-latent-effect, lem:witness-observed-arm-mass, lem:witness-target-feature-determinant, lem:witness-reference-feature-determinant, lem:path-proxy-rank-margin, lem:path-model-membership, lem:path-gap-stratum-membership, lem:path-local-weight-experiment, synth_26, lem:ordered-masses-measure-invariance, lem:observed-outcome-proxy-moment-factorization, lem:latent-arm-weight-invertibility, lem:moore-penrose-product-cancellation, lem:kantorovich-rubinstein-attaining-potential, lem:summary-metric-coordinate-comparison, lem:summary-metric-continuity, lem:stacked-proxy-moment-signal-margin, lem:model-compressed-spectral-certificate, lem:diagonalization-condition-number-bound
bib: BrownPurves1973

home_objs: lem:borel-nearest-point-selector, lem:arm-mass-lower-bound, lem:observed-proxy-moment-factorization, lem:proxy-coordinate-envelopes, lem:latent-mean-envelope, lem:latent-effect-envelope, lem:witness-latent-mass, lem:witness-latent-effect, lem:witness-observed-arm-mass, lem:witness-target-feature-determinant, lem:witness-reference-feature-determinant, lem:path-proxy-rank-margin, lem:path-model-membership, lem:path-gap-stratum-membership, lem:path-local-weight-experiment, lem:ordered-masses-measure-invariance, lem:observed-outcome-proxy-moment-factorization, lem:latent-arm-weight-invertibility, lem:moore-penrose-product-cancellation, lem:kantorovich-rubinstein-attaining-potential, lem:summary-metric-coordinate-comparison, lem:summary-metric-continuity, lem:stacked-proxy-moment-signal-margin, lem:model-compressed-spectral-certificate, lem:diagonalization-condition-number-bound
## section: Appendix B: spectral repair and finite-net benchmark
This appendix section will collect the spectral-repair handle and the class-advised finite-net benchmark used as auxiliary apparatus for the modulus-to-estimation route. It will treat these constructions as technical support for positive real-law repair and for summaries whose raw compressed operator yields a difficult empirical spectrum.
objs: def:constructive-repair-handle, def:finite-net-program, def:finite-net-law-estimator, thm:polynomial-net-law-estimator
bib: BauerFike1960, Kato1995, DavisKahan1970, StewartSun1990, WuYang2020

home_objs: def:constructive-repair-handle, def:finite-net-program, def:finite-net-law-estimator, thm:polynomial-net-law-estimator
## section: Appendix C: proofs and verification note
This appendix section will contain the proofs of the main results and end with a verification note consolidating the Lean machine-checking scope: the frozen assumptions, definitions, lemmas, propositions, and theorems are verified against the stated formal layer, while cited published inputs enter through theorem-local citation boundaries.
objs: none
bib: VirkMazaheriWu2026, BrownPurves1973, LeCam1986, PolyanskiyWu2019
home_objs: none
