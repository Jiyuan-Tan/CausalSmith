# Title
**Minimax inference for threshold modified treatment policies with continuous treatments**

**Contribution statement.** The paper establishes matched minimax absolute-risk and uniformly honest expected-length rates for the exact lower-threshold clamp mean under polynomial treatment thinning, characterizes the moving-threshold regimes, transports the statistical statements to a declared full-data causal class, and derives the corresponding continuity-only rate and elbow.

# Notation
env_overrides: def:total-gram-estimator=algorithmv, def:honest-interval=algorithmv, def:continuity-fallback-estimator=algorithmv, def:continuity-honest-interval=algorithmv, prop:pushforward-setup=propositionv, prop:policy-support=propositionv, prop:causal-bridge=propositionv, prop:one-cell-calibration=propositionv, prop:observed-margin-surjectivity=propositionv, prop:continuity-causal-bridge=propositionv, prop:continuity-observed-margin-surjectivity=propositionv, oeq:sharp-constant=remarkv

notation_gaps: \(\ell\)=local-polynomial degree used before an anchored definition, \(\delta_{\mathrm{crit},n}\)=phase boundary used in \(\cref{thm:phase-diagram,oeq:sharp-constant}\) requires an anchored definition, \(\delta_{\mathrm{edge},n}\)=bandwidth boundary used in \(\cref{lem:bandwidth-phases,thm:phase-diagram}\) requires an anchored definition, \(m_x^{\mathrm F}(a)\)=full-data response mean used in \(\cref{ass:full-data-response-continuity,prop:causal-bridge,prop:continuity-causal-bridge}\) requires an anchored definition, \(\mu_{x,\mathrm{cont}}^P\)=continuity-only regression extension used in \(\cref{def:continuity-clamp-functional,lem:continuity-regression-extension-unique,prop:continuity-causal-bridge}\) requires an anchored definition, \(\operatorname{len}(C_n)\)=interval length used in minimax expected-length criteria requires an anchored definition, \(P^{\otimes n}\)=observed product sampling law used in risk and coverage statements requires an anchored definition, \((P^{\mathrm F})^{\otimes n}\)=full-data product sampling law used in causal risk and coverage statements requires an anchored definition, \(P_{X,A}^{\otimes n}\)=observed-design product law used in \(\cref{def:exact-modulus-handle}\) requires an anchored definition, \(R_n^\star\)=observed minimax absolute-error risk used in \(\cref{thm:minimax-risk,prop:observed-margin-surjectivity,oeq:sharp-constant}\) requires an anchored definition, \(L_n^\star\)=observed minimax honest expected length used in \(\cref{thm:honest-length,prop:observed-margin-surjectivity,oeq:sharp-constant}\) requires an anchored definition

\(O_1,\ldots,O_n\) | \(O_1,\ldots,O_n\) | independent observed units from \(P\) | ass:iid-sampling  
\(P\) | \(P\) | observed-data law on \(\mathcal X\times[0,1]\times[0,1]\) | def:model-class  
\(X\) | \(X\) | finite baseline stratum | def:model-class  
\(A\) | \(A\) | continuous treatment in \([0,1]\) | def:model-class  
\(Y\) | \(Y\) | bounded outcome in \([0,1]\) | def:model-class  
\(\pi_x(a)\) | \(\pi_x(a)\) | conditional treatment density in stratum \(x\) | ass:conditional-density-law  
\(p_x\) | \(p_x\) | stratum mass in stratum \(x\) | ass:stratum-mass  
\(\mu_x^P\) | \(\mu_x^P\) | Hölder continuous extension of the conditional outcome regression in stratum \(x\) | ass:holder-regression  
\(\mathcal M\) | \(\mathcal M\) | observed laws satisfying density, stratum-mass, thinning, and Hölder member conditions | def:model-class  
\(d_\delta(a)\) | \(d_\delta(a)\) | lower-threshold clamp map \(\max\{a,\delta\}\) | def:clamp-policy  
\(A^\delta\) | \(A^\delta\) | clamped treatment \(d_\delta(A)\) | def:clamp-policy  
\(q_x(\delta)\) | \(q_x(\delta)\) | conditional mass collapsed by the clamp in stratum \(x\) | def:clamp-functional  
\(\nu_\delta(P)\) | \(\nu_\delta(P)\) | retained natural-course mean above the threshold | def:clamp-functional  
\(\theta_\delta(P)\) | \(\theta_\delta(P)\) | unsmoothed observed-data clamp target | def:clamp-functional  
\(h_n\) | \(h_n\) | information-balance bandwidth for \(\delta_n\) | def:bandwidth  
\(r_n\) | \(r_n\) | Hölder rate \(n^{-1/2}+\delta_n^{\kappa+1}h_n^\beta\) | def:frontier  
\(z=(O_1,\ldots,O_n)\) | \(z=(O_1,\ldots,O_n)\) | realized observed sample | def:local-design-notation  
\(I_0,I_1,I_2\) | \(I_0,I_1,I_2\) | deterministic split blocks | synth_8  
\(U_i\) | \(U_i\) | rescaled treatment coordinate \((A_i-\delta_n)/h_n\) | def:local-design-notation  
\(v_\ell(u)\) | \(v_\ell(u)\) | monomial vector through degree \(\ell\) | def:local-design-notation  
\(N_x\) | \(N_x\) | local count in stratum \(x\) and the threshold window | def:local-design-notation  
\(G_x\) | \(G_x\) | local total Gram matrix | def:local-design-notation  
\(M_{\ell,\kappa,\rho}\) | \(M_{\ell,\kappa,\rho}\) | normalized population reference moment matrix | def:local-design-notation  
\(\lambda_\star\) | \(\lambda_\star\) | uniform population Gram lower-bound constant | def:local-design-notation  
\(\Omega_x\) | \(\Omega_x\) | good-design event for stratum \(x\) | def:local-design-notation  
\(w_{ix}\) | \(w_{ix}\) | exact local-polynomial intercept weight | def:local-design-notation  
\(\widehat\nu_n\) | \(\widehat\nu_n\) | retained-course empirical mean | def:total-gram-estimator  
\(\widehat b_x\) | \(\widehat b_x\) | empirical lower-threshold atom mass in stratum \(x\) | def:total-gram-estimator  
\(\widetilde\mu_x\) | \(\widetilde\mu_x\) | clipped local-polynomial threshold estimate with fallback | def:total-gram-estimator  
\(\widehat\theta_n\) | \(\widehat\theta_n\) | total-Gram clamp-target estimator | def:total-gram-estimator  
\(\mathrm{CI}_n\) | \(\mathrm{CI}_n\) | bias-aware honest interval for \(\theta_{\delta_n}(P)\) | def:honest-interval  
\(t_\alpha\) | \(t_\alpha\) | Hoeffding calibration multiplier \(\sqrt{\log(12J/\alpha)/2}\) | def:honest-interval  
\(b_0,b_1\) | \(b_0,b_1\) | split-block stochastic-error radii | def:honest-interval  
\(B_x\) | \(B_x\) | local regression bias-plus-noise radius in stratum \(x\) | def:honest-interval  
\(D_x\) | \(D_x\) | atom-weighted interval contribution in stratum \(x\) | def:honest-interval  
\(u_i\) | \(u_i\) | realized rescaled treatment coordinate | def:exact-modulus-handle  
\(S_{z,x}\) | \(S_{z,x}\) | realized local window in stratum \(x\) | def:exact-modulus-handle  
\(\mathcal W_{z,x}\) | \(\mathcal W_{z,x}\) | affine weights reproducing monomials at the threshold | def:exact-modulus-handle  
\(V_{z,x}\) | \(V_{z,x}\) | realized local monomial design matrix | def:exact-modulus-handle  
\(\mathcal H_{\beta,L}\) | \(\mathcal H_{\beta,L}\) | bounded Hölder functions with exponent \(\beta\) and radius \(L\) | def:exact-modulus-handle  
\(\operatorname{exactHolderBias}_{z,x}(w)\) | \(\operatorname{exactHolderBias}_{z,x}(w)\) | worst realized Hölder bias for affine weight \(w\) | def:exact-modulus-handle  
\(\mathcal Q_{z,x,t}(w)\) | \(\mathcal Q_{z,x,t}(w)\) | exact-bias plus weighted-noise radius objective | def:exact-modulus-handle  
\(\operatorname{realizedExactModulus}_{z,x}(t)\) | \(\operatorname{realizedExactModulus}_{z,x}(t)\) | realized affine-modulus radius | def:exact-modulus-handle  
\(\operatorname{exactModulusHandle}(P,I_2,x,\ell,\beta,\kappa,L,c_-,c_+,p_{\min},\delta_n,h_n,t)\) | \(\operatorname{exactModulusHandle}(P,I_2,x,\ell,\beta,\kappa,L,c_-,c_+,p_{\min},\delta_n,h_n,t)\) | integrated realized exact-modulus radius | def:exact-modulus-handle  
\(\operatorname{worstExactModulus}_n(t_\alpha)\) | \(\operatorname{worstExactModulus}_n(t_\alpha)\) | worst integrated exact-modulus radius over \(\mathcal M\) and strata | def:exact-modulus-handle  
\(\mathcal M^{\mathrm F}\) | \(\mathcal M^{\mathrm F}\) | full-data causal law packages with observed margin in \(\mathcal M\) | def:full-data-model-class  
\(P^{\mathrm F}\) | \(P^{\mathrm F}\) | full-data law package | synth_16  
\(\mathcal U\) | \(\mathcal U\) | memberwise standard Borel latent-response space | ass:consistency  
\(U\) | \(U\) | latent response variable | ass:consistency  
\(g_x\) | \(g_x\) | stratum-specific structural response map | ass:consistency  
\(\{Y(a):a\in[0,1]\}\) | \(\{Y(a):a\in[0,1]\}\) | potential-outcome process | ass:consistency  
\(\psi_\delta(P^{\mathrm F})\) | \(\psi_\delta(P^{\mathrm F})\) | causal clamp mean | def:causal-clamp-mean  
\(R_{n,\mathrm F}^\star\) | \(R_{n,\mathrm F}^\star\) | causal minimax absolute-error risk | def:causal-frontier-criteria  
\(L_{n,\mathrm F}^\star\) | \(L_{n,\mathrm F}^\star\) | causal minimax honest expected length | def:causal-frontier-criteria  
\(\mathcal M_{\mathrm{cont}}\) | \(\mathcal M_{\mathrm{cont}}\) | continuity-only observed clamp model | synth_18  
\(\theta_{\delta,\mathrm{cont}}(P)\) | \(\theta_{\delta,\mathrm{cont}}(P)\) | continuity-only observed clamp target | def:continuity-clamp-functional  
\(s_n\) | \(s_n\) | continuity-only rate \(n^{-1/2}+\delta_n^{\kappa+1}\) | def:continuity-frontier  
\(\widehat\theta_{n,\mathrm{cont}}\) | \(\widehat\theta_{n,\mathrm{cont}}\) | continuity-only fixed-regression-fallback estimator | def:continuity-fallback-estimator  
\(t_{j,\alpha}\) | \(t_{j,\alpha}\) | split-specific Hoeffding radius | def:continuity-honest-interval  
\(\widehat B_n\) | \(\widehat B_n\) | empirical total lower-threshold atom mass | def:continuity-honest-interval  
\(\mathrm{CI}_{n,\mathrm{cont}}\) | \(\mathrm{CI}_{n,\mathrm{cont}}\) | continuity-only Hoeffding interval | def:continuity-honest-interval  
\(\mathcal M_{\mathrm{cont}}^{\mathrm F}\) | \(\mathcal M_{\mathrm{cont}}^{\mathrm F}\) | continuity-only full-data causal class | def:continuity-full-data-model-class  
\(R_{n,\mathrm{cont}}^\star\) | \(R_{n,\mathrm{cont}}^\star\) | continuity-only observed minimax risk | def:continuity-frontier-criteria  
\(L_{n,\mathrm{cont}}^\star\) | \(L_{n,\mathrm{cont}}^\star\) | continuity-only observed minimax honest expected length | def:continuity-frontier-criteria  
\(R_{n,\mathrm{cont},\mathrm F}^\star\) | \(R_{n,\mathrm{cont},\mathrm F}^\star\) | continuity-only causal minimax risk | def:continuity-frontier-criteria  
\(L_{n,\mathrm{cont},\mathrm F}^\star\) | \(L_{n,\mathrm{cont},\mathrm F}^\star\) | continuity-only causal minimax honest expected length | def:continuity-frontier-criteria  
\(B_{\bullet}=(B_n)_{n\geq1}\) | \(B_{\bullet}=(B_n)_{n\geq1}\) | deterministic sequence of admissible three-way split blocks | oeq:sharp-constant  
\(\widehat\theta^{\mathrm{TG}}_{n,B_n}(z)\) | \(\widehat\theta^{\mathrm{TG}}_{n,B_n}(z)\) | total-Gram estimator formed with split \(B_n\) | oeq:sharp-constant  
\(R_{n,B_n}(z)\) | \(R_{n,B_n}(z)\) | realized supremum exact-modulus radius | oeq:sharp-constant  
\(C^{\mathrm{mod}}_{n,B_n}(z)\) | \(C^{\mathrm{mod}}_{n,B_n}(z)\) | candidate exact-modulus interval | oeq:sharp-constant  
\(\ell^{\mathrm{mod}}_{n,B_n}\) | \(\ell^{\mathrm{mod}}_{n,B_n}\) | worst-case expected length of the candidate exact-modulus interval | oeq:sharp-constant  
\(W_{n,B_n}\) | \(W_{n,B_n}\) | worst integrated exact-modulus radius for split \(B_n\) | oeq:sharp-constant  
\(P_0,P_{\mathrm{reg}},P_{\mathrm{loc}}:\mathbb N\to\mathcal M\) | \(P_0,P_{\mathrm{reg}},P_{\mathrm{loc}}:\mathbb N\to\mathcal M\) | candidate least-favorable law sequences for regular and localized perturbations | oeq:sharp-constant  
\(\Delta_n^{\mathrm{mix}}\) | \(\Delta_n^{\mathrm{mix}}\) | combined regular and localized target separation | oeq:sharp-constant  

# Sections

## section: Introduction
The introduction motivates lower-threshold modified treatment policies for continuous treatments and presents the atom generated by the exact clamp as the central source of sampling difficulty. It previews the rate \(r_n\), the regular, critical, atom-dominated, and fixed-threshold regimes, the transport of the statistical statements to the declared full-data causal class, and the separate continuity-only rate \(s_n\). It includes one factual sentence directing readers to the appendix verification note for the machine-checked scope.
objs: none
bib: DiazWilliamsHoffmanSchenck2023, WilliamsDiaz2023lmtp, HoffmanSalazarBarretoWilliamsRudolphDiaz2024

home_objs: none
## section: Related work
This section positions the paper against causal intervention theory for natural-value-dependent policies, continuous-treatment dose-response inference, degenerate-design nonparametric regression, and honest confidence intervals. The closest comparisons are Low's expected-length lower-bound theory, Armstrong and Kolesár's bias-aware intervals, Gaïffas's degenerate-design rates, and McCoy et al.'s mixed-measure treatment of clipping mass; the section explains that the present results characterize the exact deterministic clamp under polynomial thinning and moving thresholds.
objs: none
bib: Rosenbaum1983, Pearl2009, Robins2000, vanderLaan2003, vanderLaan2011, Imbens2000, Hirano2005, Imai2004, Diaz2012, Haneuse2013, Young2014, DiazWilliamsHoffmanSchenck2023, WilliamsDiaz2023lmtp, HoffmanSalazarBarretoWilliamsRudolphDiaz2024, Diaz2024, Gilbert2024, Diaz2026, Koo2026, Pal2026, Jiang2026, Sarvet2026, KennedyMaMcHughSmall2017, BonviniKennedy2026, vanderLaanZhangGilbert2023, McCoyZhangHubbardvanderLaanSchuler2026, Gaiffas2005DegenerateDesign, Low1997NonparametricConfidenceIntervals, Cai2004, ArmstrongKolesar2018OptimalInference, ArmstrongKolesar2020, Stone1982, Fan1996, Donoho1991, Crippa2024ThresholdRegret

home_objs: none
## section: Setup and assumptions
This section defines the observed-data experiment, the lower-threshold clamp policy, the observed clamp target, the polynomial thinning and Hölder conditions, and the bandwidth and rate used in the main statistical statements. It anchors the observed model, sampling law, and clamp functional before the procedures and theorems that use them.
objs: synth_8, synth_16, ass:iid-sampling, ass:conditional-density-law, ass:stratum-mass, ass:polynomial-thinning, synth_19, ass:holder-regression, synth_18, def:model-class, def:clamp-policy, def:clamp-functional, def:bandwidth, def:frontier, synth_6, synth_2
bib: Fan1996, Gaiffas2005DegenerateDesign

home_objs: synth_8, synth_16, ass:iid-sampling, ass:conditional-density-law, ass:stratum-mass, ass:polynomial-thinning, synth_19, ass:holder-regression, synth_18, def:model-class, def:clamp-policy, def:clamp-functional, def:bandwidth, def:frontier, synth_6, synth_2
## section: Estimation and honest intervals
This section presents the local design notation, the total-Gram estimator, and the bias-aware confidence interval as the main procedures. The exposition emphasizes sample splitting, atom-mass estimation, local-polynomial threshold regression, total-Gram stabilization, and the fallback branch that preserves uniform honesty on singular-design realizations.
objs: def:local-design-notation, def:total-gram-estimator, def:honest-interval, synth_4, synth_12, synth_17, synth_5
bib: ArmstrongKolesar2018OptimalInference, ArmstrongKolesar2020, Fan1996, Hoeffding1963

home_objs: def:local-design-notation, def:total-gram-estimator, def:honest-interval, synth_4, synth_12, synth_17, synth_5
## section: Main statistical results
This section states the matched minimax absolute-risk and uniformly honest expected-length results for the observed-data clamp target and translates \(r_n\) into the regular, critical, atom-dominated, and fixed-threshold regimes. The one-cell calibration gives a concrete exponent check when \(\beta=\kappa=1\) and \(\pi(a)=2a\).
objs: synth_10, synth_3, thm:minimax-risk, thm:honest-length, thm:phase-diagram, prop:one-cell-calibration
bib: Low1997NonparametricConfidenceIntervals, ArmstrongKolesar2018OptimalInference, ArmstrongKolesar2020, Gaiffas2005DegenerateDesign, Stone1982, Donoho1991

home_objs: synth_10, synth_3, thm:minimax-risk, thm:honest-length, thm:phase-diagram, prop:one-cell-calibration
## section: Causal interpretation through full-data lifts
This section introduces the full-data causal class and causal clamp mean, proves the bridge between the structural clamp mean and the observed clamp target, and records the surjective observed-margin construction. The causal minimax and honest-length statements then follow on the declared class with the same estimator, interval, risks, and expected lengths as the observed experiment.
objs: ass:consistency, ass:exchangeability, synth_1, ass:full-data-response-continuity, def:full-data-model-class, def:causal-clamp-mean, def:causal-frontier-criteria, prop:causal-bridge, prop:observed-margin-surjectivity, synth_11, thm:causal-frontier-lift
bib: Rosenbaum1983, Pearl2009, DiazWilliamsHoffmanSchenck2023, Diaz2012, Haneuse2013, Young2014

home_objs: ass:consistency, ass:exchangeability, synth_1, ass:full-data-response-continuity, def:full-data-model-class, def:causal-clamp-mean, def:causal-frontier-criteria, prop:causal-bridge, prop:observed-margin-surjectivity, synth_11, thm:causal-frontier-lift
## section: Continuity-only clamp inference
This section studies the enlarged continuity-only class, defines the corresponding target, fallback estimator, interval, and criteria, and proves the matched rate \(s_n=n^{-1/2}+\delta_n^{\kappa+1}\). The section interprets the elbow \(\delta_n\asymp n^{-1/[2(\kappa+1)]}\), the bounded-mean endpoint at \(\delta_n=0\), and the fixed-positive-threshold conclusion within that model.
objs: def:continuity-model-class, def:continuity-clamp-functional, def:continuity-frontier, def:continuity-fallback-estimator, def:continuity-honest-interval, def:continuity-full-data-model-class, def:continuity-frontier-criteria, prop:continuity-causal-bridge, prop:continuity-observed-margin-surjectivity, synth_13, thm:continuity-only-frontier
bib: Low1997NonparametricConfidenceIntervals, Hoeffding1963

home_objs: def:continuity-model-class, def:continuity-clamp-functional, def:continuity-frontier, def:continuity-fallback-estimator, def:continuity-honest-interval, def:continuity-full-data-model-class, def:continuity-frontier-criteria, prop:continuity-causal-bridge, prop:continuity-observed-margin-surjectivity, synth_13, thm:continuity-only-frontier
## section: Discussion, limitations, and open questions
This section synthesizes what the Hölder and continuity-only rates say about quantitative smoothness, atom mass, and moving-threshold inference. A clearly labelled limitations paragraph records the fixed finite-stratum, bounded-outcome, known-smoothness-radius, known-thinning-exponent, declared full-data-class, and continuity-only-class scope. A clearly labelled open-questions paragraph introduces the exact-modulus handle and states the sharp-constant exact-modulus problem as future work.
objs: def:exact-modulus-handle, synth_21, synth_20, oeq:sharp-constant
bib: ArmstrongKolesar2018OptimalInference, ArmstrongKolesar2020, Cai2004

home_objs: def:exact-modulus-handle, synth_21, synth_20, oeq:sharp-constant
## section: Appendix: Proofs and verification note
The appendix contains the detailed proofs of the auxiliary lemmas and propositions, including the clamp pushforward calculation, policy-support argument, bandwidth algebra, product-law sampling arguments, concentration steps, local-polynomial algebra, lower-bound experiments, and the continuity-only regression-extension uniqueness proof. It ends with a verification note stating affirmatively that Lean 4 machine-checks every delivered displayed theorem and proof under its exact displayed assumptions; the note separately catalogs the sharp-constant item as an open question and identifies the theorem-local cited inputs.
objs: prop:pushforward-setup, prop:policy-support, lem:shifted-moment-coercivity, lem:lambda-star-positive, lem:power-window-integral-lower, lem:local-window-mass, lem:local-gram-entry-integral, lem:scaled-window-coercivity, lem:intercept-weight-formula, lem:good-gram-reproduction, lem:intercept-weight-pointwise, lem:bandwidth-balance, lem:local-gram-coercivity, lem:good-gram-weights, lem:weight-energy-balance, lem:stabilized-interval-honesty, lem:stabilized-risk-upper, lem:bandwidth-phases, lem:total-gram, lem:continuity-regression-extension-unique
bib: Kallenberg2002Foundations, Hoeffding1963, Low1997NonparametricConfidenceIntervals, ArmstrongKolesar2018OptimalInference, ArmstrongKolesar2020
home_objs: prop:pushforward-setup, prop:policy-support, lem:shifted-moment-coercivity, lem:lambda-star-positive, lem:power-window-integral-lower, lem:local-window-mass, lem:local-gram-entry-integral, lem:scaled-window-coercivity, lem:intercept-weight-formula, lem:good-gram-reproduction, lem:intercept-weight-pointwise, lem:bandwidth-balance, lem:local-gram-coercivity, lem:good-gram-weights, lem:weight-energy-balance, lem:stabilized-interval-honesty, lem:stabilized-risk-upper, lem:bandwidth-phases, lem:total-gram, lem:continuity-regression-extension-unique
