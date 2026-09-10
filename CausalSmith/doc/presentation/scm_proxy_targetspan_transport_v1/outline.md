# Title
**Target-span identification with proxy transport**

**Contribution statement.** In a finite latent-shift structural causal model with a full-column-rank shared proxy channel, the paper characterizes the exact observable target-span condition for identifying a target interventional probability, constructs a strictly positive rank-deficient identified example, gives a finite-sample projection confidence set with uniform coverage, and explains the behavior of uniformly covering sets on an unrestricted changing-rank array class.

# Notation
notation_gaps: \(\mathcal E\)=finite environment state space, \(\mathcal U\)=finite latent state space, \(\mathcal W\)=finite proxy state space, \(\mathcal X\)=finite treatment state space, \(\mathcal Y\)=finite outcome state space, \(r=\lvert\mathcal U\rvert\)=latent cardinality, \(m=\lvert\mathcal W\rvert\)=proxy cardinality, \(\mathcal G\)=causal graph, \(\mathcal M\)=latent-shift SCM, \(\pi\)=environment law, \(S\)=latent channel given environment, \(M\)=proxy channel, \(a_x(u)\)=treatment kernel, \(f_{x,y}(u,w)\)=outcome kernel, \(q\)=target latent mixture, \(P_{\mathcal M}\)=source full-data law, \(Q_{\mathcal M}\)=target law, \(P_O\)=observed source law, \(b\)=target proxy law, \(\mathcal D=(P_O,b)\)=supplied observed and target-proxy data, \(\rho_x(e)\)=source treatment probability by environment, \(R_x(u,e)\)=latent posterior matrix given \(E=e,X=x\), \(B_x\)=source conditional proxy matrix \(P_O(W\mid E,x)\), \(c_{x,y}\)=source conditional outcome vector \(P_O(Y=y\mid E,x)\), \(g_{x,y}\)=latent-proxy averaged outcome vector, \(\theta_{x,y}\)=target interventional probability, \(h\)=observed separator vector, \(v=M^\top h\)=lifted latent direction, \(w_{\star}\)=perturbed proxy value, \(y^\circ\)=offsetting outcome value, \(\varepsilon\)=perturbation radius or Wald-localization slack depending on statement, \(n_s\)=source sample size, \(n_t\)=target-proxy sample size, \(O_i^s\)=source observation, \(W_j^t\)=target proxy observation, \(\mathbb P_{\mathcal M}^{\,n_s,n_t}\)=two-sample product law, \(\widehat H_x\)=empirical source moment matrix, \(\widehat z_{x,y}\)=empirical source outcome-moment vector, \(\widehat b\)=empirical target proxy vector, \(\alpha\)=error level, \(p\)=source allocation limit, \(n_s(n)\)=row-\(n\) source sample size, \(n_t(n)\)=row-\(n\) target sample size, \(\mathcal M_n\)=row-\(n\) SCM, \(P_{O,n}\)=row-\(n\) observed source law, \(b_n\)=row-\(n\) target proxy law, \(B_{x,n}\)=row-\(n\) conditional proxy matrix, \(H_{x,n}\)=row-\(n\) source moment matrix, \(z_{x,y,n}\)=row-\(n\) outcome-moment vector, \(\theta_{x,y,n}\)=row-\(n\) target interventional probability, \(\Omega_n\)=row-\(n\) finite product sample space, \(\mathcal C_n\)=row-\(n\) confidence-set rule, \(d_{x,n}\)=minimum balancing-weight norm, \(r_0\)=regular rank index, \(c\)=regular singular-value floor, \(\eta\)=cell and variance floor, \(\sigma_{r_0}(H_x)\)=retained singular value, \(V_{r_0,x,y}(\mathcal M;p)\)=population delta-method variance, \(\Phi\)=standard-normal distribution function, \(z_{1-\alpha/2}\)=standard-normal quantile

\(P_O\) | \(P_O\) | observed source marginal law induced by the latent-shift SCM | ass:source-iid-sampling
\(\mathcal M\) | \(\mathcal M\) | finite latent-shift structural causal model and its component kernels | ass:latent-shift-factorization
\(m\) | \(m\) | proxy-state cardinality \(\lvert\mathcal W\rvert\) | def:failure-separator
\(r\) | \(r\) | latent-state cardinality \(\lvert\mathcal U\rvert\) | ass:proxy-channel-injectivity
\(\pi\) | \(\pi\) | environment probability mass function | ass:latent-shift-factorization
\(S\) | \(S\) | latent-state channel conditional on environment | ass:latent-shift-factorization
\(M\) | \(M\) | proxy channel conditional on the latent state | ass:latent-shift-factorization
\(q\) | \(q\) | target latent-state probability mass function | ass:target-mechanism-invariance
\(b\) | \(b\) | target proxy marginal law induced by the latent-shift SCM | ass:target-iid-sampling
\(B_x\) | \(B_x\) | conditional proxy matrix with entries \(P_O(W=w\mid E=e,X=x)\) | def:balancing-fiber
\(R_x\) | \(R_x\) | latent posterior matrix given environment and treatment | lem:observable-factorization
\(\rho_x(e)\) | \(\rho_x(e)\) | source probability of treatment \(x\) in environment \(e\) | lem:observable-factorization
\(g_{x,y}\) | \(g_{x,y}\) | latent-indexed proxy-averaged outcome vector | lem:observable-factorization
\(c_{x,y}\) | \(c_{x,y}\) | source conditional outcome vector by environment | lem:observable-factorization
\(\theta_{x,y}\) | \(\theta_{x,y}\) | target interventional probability | lem:observable-factorization
\(V_{r_0,x,y}(\mathcal M;p)\) | \(V_{r_0,x,y}(\mathcal M;p)\) | population delta-method variance of the retained-rank Wald functional | ass:regular-positive-variance
\(z_{x,y}\) | \(z_{x,y}\) | unconditional source outcome-moment vector | ass:regular-positive-variance
\(\phi_{r_0}\) | \(\phi_{r_0}\) | retained-rank Wald functional | ass:regular-positive-variance
\(\widehat H_x\) | \(\widehat H_x\) | empirical source joint-moment matrix | def:concentration-projection-set
\(\widehat z_{x,y}\) | \(\widehat z_{x,y}\) | empirical source outcome-moment vector | def:concentration-projection-set
\(\widehat b\) | \(\widehat b\) | empirical target proxy frequency vector | def:concentration-projection-set
\(P_{O,n}\) | \(P_{O,n}\) | observed source marginal law in row \(n\) | ass:triangular-source-iid-sampling
\(\Omega_n\) | \(\Omega_n\) | row-\(n\) finite two-sample product space | ass:triangular-source-iid-sampling
\(b_n\) | \(b_n\) | target proxy marginal law in row \(n\) | ass:triangular-source-iid-sampling
\(B_{x,n}\) | \(B_{x,n}\) | row-\(n\) conditional proxy matrix | ass:array-target-span
\(d_{x,n}\) | \(d_{x,n}\) | minimum norm of a row-\(n\) balancing weight | def:studentized-array-class
\(H^{\star}_{r_0}\) | \(H^{\star}_{r_0}\) | selector-based Gram-spectral rank-\(r_0\) truncation | def:regular-wald-functional
\(\widehat H_{x,n}\) | \(\widehat H_{x,n}\) | row-\(n\) empirical source moment matrix | def:regular-wald-estimator
\(\widehat z_{x,y,n}\) | \(\widehat z_{x,y,n}\) | row-\(n\) empirical source outcome-moment vector | def:regular-wald-estimator
\(\widehat b_n\) | \(\widehat b_n\) | row-\(n\) empirical target proxy vector | def:regular-wald-estimator
\(\theta_{x,y,n}\) | \(\theta_{x,y,n}\) | row-\(n\) target interventional probability | thm:no-uniform-studentized-wald-adaptation
\(\mathbb P_{\mathcal M}^{\,n_s,n_t}\) | \(\mathbb P_{\mathcal M}^{\,n_s,n_t}\) | independent source/target-proxy two-sample product law | thm:finite-sample-projection-coverage
\(\Omega(n_s,n_t)\) | \(\Omega(n_s,n_t)\) | finite product sample space for the two sample blocks | ass:triangular-source-iid-sampling
\(z_{1-\alpha/2}\) | \(z_{1-\alpha/2}\) | standard-normal \((1-\alpha/2)\)-quantile | def:regular-wald-interval
\(\operatorname{Fin}(2)\) | \(\{0,1\}\) | two-element treatment and environment state space in the witness | def:rank-deficient-success-witness
\(\operatorname{Fin}(3)\) | \(\{0,1,2\}\) | three-element latent and proxy state space in the witness | def:rank-deficient-success-witness

\(\mathfrak M_{+}\) | \(\mathfrak M_{+}\) | strictly positive latent-shift SCMs with full-column-rank proxy channel | def:positive-latent-shift-class
\(\mathfrak F(\mathcal D)\) | \(\mathfrak F(\mathcal D)\) | compatible SCM fiber inducing the supplied \(P_O\) and \(b\) | def:compatible-fiber
\(\Lambda_x(\mathcal D)\) | \(\Lambda_x(\mathcal D)\) | affine set of environment weights solving \(B_x\lambda=b\) | def:balancing-fiber
\(\mathcal H_x(\mathcal D)\) | \(\mathcal H_x(\mathcal D)\) | observed separators annihilating \(B_x\) and detecting \(b\) | def:failure-separator
\(f^{(t)}_{x,y}(u,w_{\star})\) | \(f^{(t)}_{x,y}(u,w_{\star})\) | perturbed outcome probability at outcome \(y\) and proxy \(w_{\star}\) | def:outcome-null-perturbation
\(f^{(t)}_{x,y^{\circ}}(u,w_{\star})\) | \(f^{(t)}_{x,y^{\circ}}(u,w_{\star})\) | offsetting perturbed outcome probability at \(y^\circ\) and proxy \(w_{\star}\) | def:outcome-null-perturbation
\(\mathcal M^{\star}\) | \(\mathcal M^{\star}\) | explicit rational rank-deficient identified SCM | def:rank-deficient-success-witness
\(H_x\) | \(H_x\) | unconditional source moment matrix with entries \(P_O(E=e,W=w,X=x)\) | ass:regular-fixed-rank
\(z_{x,y}(e)\) | \(z_{x,y}(e)\) | unconditional source outcome moment \(P_O(E=e,X=x,Y=y)\) | def:unconditional-balancing-moments
\(\kappa(e)\) | \(\kappa(e)\) | unconditional balancing weight induced by \(\lambda\) | def:unconditional-weight-map
\(L=m\lvert\mathcal E\rvert+\lvert\mathcal E\rvert+m\) | \(L=m\lvert\mathcal E\rvert+\lvert\mathcal E\rvert+m\) | number of empirical coordinates in the concentration event | def:concentration-projection-set
\(r_s=\sqrt{\log(2L/\alpha)/(2n_s)}\) | \(r_s=\sqrt{\log(2L/\alpha)/(2n_s)}\) | source Hoeffding radius | def:concentration-projection-set
\(r_t=\sqrt{\log(2L/\alpha)/(2n_t)}\) | \(r_t=\sqrt{\log(2L/\alpha)/(2n_t)}\) | target-proxy Hoeffding radius | def:concentration-projection-set
\(\widehat C_{x,y,1-\alpha}\) | \(\widehat C_{x,y,1-\alpha}\) | concentration-calibrated projection confidence set | def:concentration-projection-set
\(\mathcal A_p\) | \(\mathcal A_p\) | fixed-allocation changing-rank array class satisfying row-wise target span | def:studentized-array-class
\(\mathcal R_{r_0,c,\eta}\) | \(\mathcal R_{r_0,c,\eta}\) | strongly identified regular submodel with rank, span, cell, and variance floors | def:strongly-identified-submodel
\(\phi_{r_0}(H,z,b)\) | \(\phi_{r_0}(H,z,b)\) | rank-\(r_0\) truncated-SVD Wald functional | def:regular-wald-functional
\(H_{r_0}=H^{\star}_{r_0}\) | \(H_{r_0}=H^{\star}_{r_0}\) | selector-based Gram-spectral truncation of \(H\) | def:regular-wald-functional
\(H_{r_0}^{\dagger}\) | \(H_{r_0}^{\dagger}\) | Moore-Penrose inverse of the retained-rank truncation | def:regular-wald-functional
\(\widehat\theta^{\,W}_{x,y,n}\) | \(\widehat\theta^{\,W}_{x,y,n}\) | truncated-SVD Wald estimator | def:regular-wald-estimator
\(\widehat T_n=(\widehat H_{x,n},\widehat z_{x,y,n},\widehat b_n)\) | \(\widehat T_n=(\widehat H_{x,n},\widehat z_{x,y,n},\widehat b_n)\) | empirical moment tuple for the Wald variance | def:regular-wald-variance
\(\widehat\Gamma_n\) | \(\widehat\Gamma_n\) | plug-in covariance matrix of \(\sqrt n\,\widehat T_n\) | def:regular-wald-variance
\(\widehat V_n\) | \(\widehat V_n\) | totalized plug-in Wald variance | def:regular-wald-variance
\(D\phi_{r_0}(\widehat T_n)\) | \(D\phi_{r_0}(\widehat T_n)\) | derivative of the strict-gap Wald functional at empirical moments | def:regular-wald-variance
\(\sigma_{\bar q+1}=0\) | \(\sigma_{\bar q+1}=0\) | terminal singular-value convention for \(\bar q=\min(m,\lvert\mathcal E\rvert)\) | def:regular-wald-variance
\(I^W_{n,1-\alpha}\) | \(I^W_{n,1-\alpha}\) | truncated-SVD Wald interval intersected with \([0,1]\) | def:regular-wald-interval
\(\operatorname{diam}_2(C)\) | \(\operatorname{diam}_2(C)\) | Euclidean diameter of a subset of \([0,1]\), totalized at the empty set | def:euclidean-diameter
\(d_H(C,D)\) | \(d_H(C,D)\) | Euclidean Hausdorff distance between nonempty subsets of \([0,1]\) | def:euclidean-hausdorff-distance

# Sections
env_overrides: prop:strict-fullrank-extension=propositionv

## section: Introduction
The introduction will motivate target-domain causal transport with source observations of \((E,W,X,Y)\) and target observations of \(W\), state the target-span contribution in reader-facing terms, and preview the three deliverables: exact identification, finite-sample projection coverage, and the changing-rank array interpretation. It will include one factual sentence directing readers to the appendix verification note for the machine-checked scope.
objs:
bib: IglesiasAlonsoEtAl2025, Pearl2009, PearlBareinboim2011, BareinboimPearl2016, TchetgenTchetgen2024, MiaoGengTchetgen2018

## section: Related work
This section positions the paper against the closest causal transport and proxy-identification results. It will compare \(\cref{thm:target-span-iff}\) and \(\cref{prop:strict-fullrank-extension}\) with the full source-rank transport formula in \cite{IglesiasAlonsoEtAl2025}, the bridge-functional constancy criterion in \cite{ZhangLiMiaoTchetgen2023}, and proxy-equivalence transport for prediction in \cite{RahiminasabEtAl2026}; it will then place \(\cref{thm:finite-sample-projection-coverage}\) within projection and weak-identification inference.
objs:
bib: IglesiasAlonsoEtAl2025, ZhangLiMiaoTchetgen2023, RahiminasabEtAl2026, MiaoGengTchetgen2018, TchetgenTchetgen2024, Shi2020, Cui2024, Ying2023, AndersonRubin1949, StockWrightYogo2002, Moreira2003, Kleibergen2005, DufourTaamouti2005, AndrewsCheng2012, AndrewsCheng2014, AndrewsGuggenberger2019, NeweyPowell2003, CarrascoFlorensRenault2007, Santos2011, ChernozhukovNeweySantos2023, BennettEtAl2023, Manski2003, Tamer2010, ChernozhukovHongTamer2007, BeresteanuMolinari2008, GhassamiShpitserTchetgen2023, DuarteEtAl2024, Ursu2018

## section: Setup and target-span geometry
This section introduces the finite latent-shift SCM, the compatible fiber, the observable target-span equation, and the unconditional balancing moments used throughout the paper. It will present the structural and positivity assumptions as the baseline model conditions, define \(\mathfrak M_{+}\), \(\mathfrak F(\mathcal D)\), \(\Lambda_x(\mathcal D)\), \(H_x\), \(z_{x,y}\), and \(\kappa\), and use \(\cref{lem:observable-factorization}\) only as a previewed algebraic identity whose proof appears in the appendix.
objs: synth_2, ass:latent-shift-factorization, ass:target-mechanism-invariance, ass:strict-primitive-positivity, ass:proxy-channel-injectivity, synth_3, def:positive-latent-shift-class, def:compatible-fiber, def:balancing-fiber, def:unconditional-balancing-moments, def:unconditional-weight-map
bib: Pearl2009, RosenbaumRubin1983, Robins1986

## section: Identification by target span
This section states the exact identification theorem and its rank-deficient extension. It will present \(\cref{thm:target-span-iff}\) as the main identification result, interpret every solution of \(B_x\lambda=b\) as yielding the same target interventional probability, and then give \(\cref{prop:strict-fullrank-extension}\) with \(\cref{def:rank-deficient-success-witness}\) to show how target-span identification covers a strictly rank-deficient source design under an injective proxy channel.
objs: def:rank-deficient-success-witness, thm:target-span-iff, synth_1, synth_4, prop:strict-fullrank-extension
bib: IglesiasAlonsoEtAl2025, ZhangLiMiaoTchetgen2023, RahiminasabEtAl2026, MiaoGengTchetgen2018

## section: Finite-sample projection inference
This section develops the two-sample multinomial experiment and the concentration projection set. It will introduce the source and target sampling assumptions, define \(\widehat C_{x,y,1-\alpha}\), and state \(\cref{thm:finite-sample-projection-coverage}\) as finite-sample coverage over the positive latent-shift fiber under target span, including arbitrary ranks, cell probabilities, singular values, and balancing-vector magnitudes.
objs: ass:source-iid-sampling, ass:target-iid-sampling, def:concentration-projection-set, thm:finite-sample-projection-coverage
bib: AndersonRubin1949, Hansen1982, StockWrightYogo2002, Moreira2003, Kleibergen2005, DufourTaamouti2005, AndrewsGuggenberger2019, ChernozhukovNeweySantos2023, BennettEtAl2023

## section: Regular Wald comparison and changing-rank arrays
This section defines the regular submodel, the truncated-SVD Wald objects, and the fixed-allocation array class used to compare uniform coverage with regular-submodel localization. It will present the array and regularity assumptions, define \(\mathcal A_p\), \(\mathcal R_{r_0,c,\eta}\), \(\phi_{r_0}\), \(\widehat\theta^{\,W}_{x,y,n}\), \(\widehat V_n\), \(I^W_{n,1-\alpha}\), \(\operatorname{diam}_2\), and \(d_H\), and then state \(\cref{thm:no-uniform-studentized-wald-adaptation}\) as an interpretation of this unrestricted changing-rank class.
objs: ass:triangular-allocation, ass:triangular-source-iid-sampling, ass:triangular-target-iid-sampling, ass:array-target-span, ass:regular-fixed-rank, ass:regular-singular-gap, ass:regular-target-span, ass:regular-cell-floor, ass:regular-positive-variance, def:studentized-array-class, def:strongly-identified-submodel, def:regular-wald-functional, def:regular-wald-estimator, def:regular-wald-variance, def:regular-wald-interval, def:euclidean-diameter, def:euclidean-hausdorff-distance, thm:no-uniform-studentized-wald-adaptation
bib: AndrewsCheng2012, AndrewsCheng2014, AndrewsGuggenberger2019, Hansen1982, NeweyPowell2003, CarrascoFlorensRenault2007, Santos2011

## section: Discussion, limitations, and extensions
This section will interpret the paper’s positive scope and conditions: finite state spaces, a full-column-rank shared proxy channel, source observations of \((E,W,X,Y)\), target observations of \(W\), and target-span identification of the interventional law. In a clearly labelled limitations and future-work portion, it will separate open directions such as sharp off-span bounds, continuous proxy variables, and incomplete proxy channels from the delivered finite and changing-rank results.
objs:
bib: BalkePearl1997, Manski2003, Tamer2010, GhassamiShpitserTchetgen2023, DuarteEtAl2024

## section: Appendix: Proofs and verification note
The appendix will contain the algebraic proof of the observable factorization, the separator perturbation proof for the positive full-law converse, the concentration and total-variation arguments, and the regular-Wald auxiliary derivations. It will end with a concise verification note stating that the displayed assumptions, definitions, lemma, proposition, and theorems are the machine-checked objects, while literature comparisons and bibliographic context are manuscript exposition.
objs: def:failure-separator, def:outcome-null-perturbation, lem:observable-factorization, thm:positive-full-law-converse
bib: IglesiasAlonsoEtAl2025, ZhangLiMiaoTchetgen2023, AndersonRubin1949, AndrewsGuggenberger2019, Pearl2009