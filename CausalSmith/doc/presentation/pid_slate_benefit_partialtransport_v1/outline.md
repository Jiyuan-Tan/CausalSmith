# Title
**Sharp ordinal benefit bounds for survivor compliers under selection and noncompliance**

**Contribution statement.** The paper characterizes the sharp identified interval for the same-unit strict-benefit probability among survivor compliers with finite ordered outcomes, binary instrumental assignment, noncompliance, treatment-induced selection, and covariate-specific weak selection monotonicity; it gives closed branch-free threshold formulas, endpoint-attaining latent laws, linear-time sparse endpoint constructions, a fixed-law directional limit for a projected screened plug-in estimator, and a conservative deterministic guard for uniform whole-interval containment.

# Notation
\(D_0,D_1\) | \(D_0,D_1\) | potential treatments under the two instrument states | notation_gaps
\(S_0,S_1\) | \(S_0,S_1\) | potential selection indicators under the two treatment states | notation_gaps
\(Y_0,Y_1\) | \(Y_0,Y_1\) | potential ordered outcomes under the two treatment states | notation_gaps
\(Z\) | \(Z\) | binary instrument | notation_gaps
\(X\) | \(X\) | covariate cell | notation_gaps
\(D\) | \(D\) | observed treatment receipt | notation_gaps
\(S\) | \(S\) | observed selection indicator | notation_gaps
\(Y\) | \(Y\) | observed outcome on selected units | notation_gaps
\(C\) | \(C\) | complier event | notation_gaps
\(\varepsilon_Z\) | \(\varepsilon_Z\) | instrument-overlap constant | ass:instrument-overlap
\(\pi(x)\) | \(\pi(x)\) | conditional instrument propensity in cell \(x\) | ass:instrument-overlap
\(p_x\) | \(p_x\) | probability of covariate cell \(x\) | def:identified-interval
\(d(x)\) | \(d(x)\) | covariate-specific weak selection-monotonicity direction | ass:weak-selection-monotonicity
\(\Delta q(x)\) | \(\Delta q(x)\) | difference \(q_1(x)-q_0(x)\) between selected-complier capacity totals | def:observable-capacities
\(\kappa_{\sigma}\) | \(\kappa_{\sigma}\) | direction-margin constant | ass:direction-margin
\(m(x)\) | \(m(x)\) | exact survivor-complier mass in cell \(x\) | def:observable-capacities
\(M\) | \(M\) | aggregate survivor-complier mass | def:identified-interval
\(m_{\star}\) | \(m_{\star}\) | uniform lower bound for aggregate survivor-complier mass | ass:uniform-aggregate-survivor-bound
\(O_1,\ldots,O_n\) | \(O_1,\ldots,O_n\) | independent observations from the observed-data law | ass:iid-sampling
\(P_{\mathrm{obs}}\) | \(P_{\mathrm{obs}}\) | observed-data law | ass:iid-sampling
\(\mathcal M\) | \(\mathcal M\) | latent laws satisfying the structural restrictions and positive aggregate survivor-complier mass | def:structural-law-class
\(\mathcal P_n\) | \(\mathcal P_n\) | uniform law class at index \(n\) | def:uniform-law-class
\(\ell_i(x)\) | \(\ell_i(x)\) | lower-arm selected-complier outcome capacity for level \(i\) in cell \(x\) | def:observable-capacities
\(h_j(x)\) | \(h_j(x)\) | upper-arm selected-complier outcome capacity for level \(j\) in cell \(x\) | def:observable-capacities
\(q_0(x)\) | \(q_0(x)\) | total lower-arm selected-complier capacity in cell \(x\) | def:observable-capacities
\(q_1(x)\) | \(q_1(x)\) | total upper-arm selected-complier capacity in cell \(x\) | def:observable-capacities
\(\Gamma_x^{\ast}\) | \(\Gamma_x^{\ast}\) | exact-mass partial-transport polytope in cell \(x\) | def:partial-transport-polytope
\(\Gamma_x^{+}\) | \(\Gamma_x^{+}\) | row-exact partial-transport comparison polytope | def:partial-transport-polytope
\(\Gamma_x^{-}\) | \(\Gamma_x^{-}\) | column-exact partial-transport comparison polytope | def:partial-transport-polytope
\(\Gamma_x^{0}\) | \(\Gamma_x^{0}\) | doubly exact comparison polytope | def:partial-transport-polytope
\(\Gamma_x\) | \(\Gamma_x\) | paper's cellwise survivor-complier coupling polytope | def:partial-transport-polytope
\(\gamma_x\) | \(\gamma_x\) | cellwise survivor-complier coupling array | def:partial-transport-polytope
\(B_L(x)\) | \(B_L(x)\) | lower threshold-cut value for benefit mass in cell \(x\) | def:threshold-cuts
\(B_U(x)\) | \(B_U(x)\) | upper threshold-cut value for benefit mass in cell \(x\) | def:threshold-cuts
\(\ell_{\le t}(x)\) | \(\ell_{\le t}(x)\) | prefix sum of lower-arm capacities through threshold \(t\) | def:threshold-cuts
\(h_{\le t}(x)\) | \(h_{\le t}(x)\) | prefix sum of upper-arm capacities through threshold \(t\) | def:threshold-cuts
\(\ell_{<t}(x)\) | \(\ell_{<t}(x)\) | strict prefix sum of lower-arm capacities below threshold \(t\) | def:threshold-cuts
\(h_{>t}(x)\) | \(h_{>t}(x)\) | tail sum of upper-arm capacities above threshold \(t\) | def:threshold-cuts
\(\Psi(P_{\mathrm{obs}})\) | \(\Psi(P_{\mathrm{obs}})\) | endpoint map for the sharp identified interval | def:identified-interval
\((\theta_L,\theta_U)\) | \((\theta_L,\theta_U)\) | lower and upper endpoints of the sharp identified interval | def:identified-interval
\(\Theta_I(P_{\mathrm{obs}})\) | \(\Theta_I(P_{\mathrm{obs}})\) | sharp identified interval for the benefit probability | def:identified-interval
\(P^L,P^U\) | \(P^L,P^U\) | lower- and upper-endpoint attaining latent laws | def:threshold-flow-construction
\(x^{\star}\) | \(x^{\star}\) | single covariate cell in the three-level witness | def:three-level-witness
\(P_{\mathrm{obs}}^{\star}\) | \(P_{\mathrm{obs}}^{\star}\) | observed law in the three-level witness | def:three-level-witness
\(P^{\star}\) | \(P^{\star}\) | latent law in the three-level witness | def:three-level-witness
\(\widetilde c_n\) | \(\widetilde c_n\) | raw empirical capacity vector | def:plugin-endpoint-estimator
\(\mathfrak C\) | \(\mathfrak C\) | nonnegative capacity cone | def:plugin-endpoint-estimator
\(\widehat c_n\) | \(\widehat c_n\) | projected empirical capacity vector | def:plugin-endpoint-estimator
\(\Pi_{\mathfrak C}\) | \(\Pi_{\mathfrak C}\) | Euclidean projection onto the nonnegative capacity cone | def:plugin-endpoint-estimator
\(\widehat\ell_i(x)\) | \(\widehat\ell_i(x)\) | projected empirical lower-arm capacity | def:plugin-endpoint-estimator
\(\widehat h_j(x)\) | \(\widehat h_j(x)\) | projected empirical upper-arm capacity | def:plugin-endpoint-estimator
\(\widehat q_0(x)\) | \(\widehat q_0(x)\) | empirical lower-arm capacity total | def:plugin-endpoint-estimator
\(\widehat q_1(x)\) | \(\widehat q_1(x)\) | empirical upper-arm capacity total | def:plugin-endpoint-estimator
\(\widehat{\Delta q}(x)\) | \(\widehat{\Delta q}(x)\) | empirical capacity-total gap | def:plugin-endpoint-estimator
\(\widehat m(x)\) | \(\widehat m(x)\) | empirical exact mass | def:plugin-endpoint-estimator
\(\widehat B_L(x)\) | \(\widehat B_L(x)\) | empirical lower threshold-cut value | def:plugin-endpoint-estimator
\(\widehat B_U(x)\) | \(\widehat B_U(x)\) | empirical upper threshold-cut value | def:plugin-endpoint-estimator
\(\widehat r_x\) | \(\widehat r_x\) | empirical retained-cell mass score | def:plugin-endpoint-estimator
\(\widehat p_x\) | \(\widehat p_x\) | empirical covariate-cell probability | def:plugin-endpoint-estimator
\(\eta_n\) | \(\eta_n\) | screening threshold sequence | def:plugin-endpoint-estimator
\(\widehat M_n\) | \(\widehat M_n\) | screened empirical aggregate mass | def:plugin-endpoint-estimator
\(\widehat N_{L,n}\) | \(\widehat N_{L,n}\) | screened empirical lower numerator | def:plugin-endpoint-estimator
\(\widehat N_{U,n}\) | \(\widehat N_{U,n}\) | screened empirical upper numerator | def:plugin-endpoint-estimator
\(\widehat\Psi_n\) | \(\widehat\Psi_n\) | projected screened plug-in endpoint estimator | def:plugin-endpoint-estimator
\(a_n\) | \(a_n\) | near-active-face localization tolerance | def:face-aware-inference-handle
\(\mathbb G_n^\xi\) | \(\mathbb G_n^\xi\) | multiplier process used for the diagnostic face envelope | def:face-aware-inference-handle
\(\mathcal E\) | \(\mathcal E\) | finite observable event collection for the deterministic guard | def:face-aware-inference-handle
\(\delta_n\) | \(\delta_n\) | maximal empirical deviation over \(\mathcal E\) | def:face-aware-inference-handle
\(b_{n,\alpha}\) | \(b_{n,\alpha}\) | union-bound empirical-deviation threshold | def:face-aware-inference-handle
\(A_{n,\alpha}\) | \(A_{n,\alpha}\) | capacity-and-screening deterministic error envelope | def:face-aware-inference-handle
\(g_{n,\alpha}\) | \(g_{n,\alpha}\) | deterministic endpoint-padding guard | def:face-aware-inference-handle
\(\mathcal C_{1-\alpha,n}\) | \(\mathcal C_{1-\alpha,n}\) | guarded confidence set for the whole identified interval | def:face-aware-inference-handle
\(b_x(\gamma_x)\) | \(b_x(\gamma_x)\) | benefit mass of a cellwise coupling | notation_gaps
\(\mathcal X_+(P)\) | \(\mathcal X_+(P)\) | positive-survivor support under law \(P\) | notation_gaps
\(\mathbb Z_{P_{\mathrm{obs}}}\) | \(\mathbb Z_{P_{\mathrm{obs}}}\) | finite-dimensional Gaussian limit of the empirical observed law | thm:branch-free-pointwise-directional-limit
\(L_n\) | \(L_n\) | deterministic sequence used to instantiate the screening threshold | thm:uniform-deterministic-guard

notation_gaps: \(D_0,D_1,S_0,S_1,Y_0,Y_1,Z,X,D,S,Y,C\)=ambient potential-outcome variables need a setup definition before the assumptions; \(b_x(\gamma_x)\)=benefit functional first used in `thm:sharp-exact-mass-threshold-interval` without an anchored definition; \(\mathcal X_+(P)\)=positive-survivor support first used in `thm:branch-free-pointwise-directional-limit` without an anchored definition.

env_overrides: def:threshold-flow-construction=algorithmv, def:plugin-endpoint-estimator=algorithmv, def:face-aware-inference-handle=algorithmv, oeq:uniform-face-multiplier=remarkv

# Sections
## section: Abstract
The abstract will be drafted after the main text and will state the estimand, the finite ordered-outcome IV-selection design, the exact-mass partial-transport characterization, the endpoint-attaining construction, the computational result, and the two inferential deliverables in direct reader-facing terms.

objs: none

bib: none

home_objs: none
## section: Introduction
The introduction motivates the survivor-complier strict-benefit probability for ordered outcomes observed under treatment-induced selection, using the Job Corps-style offer, receipt, employment, and wage-category interpretation as a running example. It will preview how conditional IV contrasts identify unequal selected-complier capacities, how weak selection monotonicity converts their smaller total into survivor-complier mass, and how exact-mass partial transport yields sharp benefit bounds and estimable endpoints. A single factual sentence will direct readers to the appendix verification note for the machine-checked scope.

objs: none

bib: AngristImbensRubin1996, KennedyHarrisKeele2019, ChenFlores2015, DongHeiler2026, LuDingDasgupta2018

home_objs: none
## section: Related work
This section positions the paper against IV and principal-stratification work on survivor-complier effects, Lee-style selection bounds, and ordinal benefit bounds. The closest comparisons are \citet{DongHeiler2026} for covariate-specific weak selection monotonicity and selected-complier outcome distributions, \citet{LuDingDasgupta2018} for complete-marginal ordinal benefit formulas, \citet{GabrielSachsJensen2024} and \citet{deAguasEtAl2025} for sharp ordinal benefit bounds under different observable restrictions, and \citet{ChenLi2026} for principal generalized causal effects under treatment unconfoundedness and ignorability conditions.

objs: none

bib: Rubin1974, RosenbaumRubin1983, Holland1986, Pearl2009, ImbensAngrist1994, AngristImbensRubin1996, BalkePearl1997, Manski1990, Manski1997, ManskiPepper2000, Manski2003, FrangakisRubin2002, Heckman1979, Lee2009, KennedyHarrisKeele2019, ChenFlores2015, BlancoFloresFloresLagunes2013, ChenFloresFloresLagunes2018, DongHeiler2026, Semenova2025, Makarov1982, WilliamsonDowns1990, FanPark2010, Villani2009, AgrestiKateri2017, HuangEtAl2017, FayEtAl2018, LuDingDasgupta2018, LuZhangDing2020, TianPearl2000, SachsEtAl2023, DuarteEtAl2023, GabrielSachsJensen2024, deAguasEtAl2025, ChenLi2026, vanDerVaart1998, ImbensManski2004, ChernozhukovHongTamer2007, RomanoShaikh2010, Tamer2010, Molinari2020, ChernozhukovLeeRosen2013, FangSantos2019, HongLi2018, Russell2021, LevisEtAl2025, BenMichael2025, KhandamiryanSemenova2026, Noack2026, LeeLiu2024, ZhangRichardson2024

home_objs: none
## section: Setup and assumptions
This section introduces the finite ordered-outcome IV-selection model, the survivor-complier benefit estimand, the observed-data law, and the maintained structural law class. It states the conditional independence, consistency, exclusion, overlap, no-defier, weak selection-monotonicity, and positive survivor-mass conditions, then defines the observable selected-complier capacities that drive the rest of the paper.

objs: synth_13, synth_11, synth_10, synth_9, synth_8, synth_7, synth_12, ass:iv-independence, ass:treatment-consistency, ass:selection-exclusion-consistency, ass:outcome-exclusion-consistency, synth_17, synth_14, synth_1, synth_22, synth_16, ass:instrument-overlap, ass:no-defiers, ass:weak-selection-monotonicity, ass:positive-aggregate-survivors, def:structural-law-class, def:observable-capacities, prop:capacity-identification

bib: ImbensAngrist1994, AngristImbensRubin1996, KennedyHarrisKeele2019, DongHeiler2026

home_objs: ass:iv-independence, ass:treatment-consistency, ass:selection-exclusion-consistency, ass:outcome-exclusion-consistency, ass:instrument-overlap, ass:no-defiers, ass:weak-selection-monotonicity, ass:positive-aggregate-survivors, def:structural-law-class, def:observable-capacities, prop:capacity-identification
## section: Sharp benefit bounds
This section develops the exact-mass partial-transport problem cell by cell, defines the threshold cuts, aggregates the endpoint map, and proves sharpness of the resulting interval. It emphasizes the branch-free formulas, the projection of compatible latent laws onto the partial-transport polytope, endpoint attainment through full latent laws, and the collapse to complete-marginal ordinal benefit bounds on the no-selection face.

objs: def:partial-transport-polytope, def:threshold-cuts, def:identified-interval, synth_4, prop:tie-face-collapse, def:threshold-flow-construction, thm:full-law-endpoint-attainment, thm:no-selection-reduction, synth_5, thm:sharp-exact-mass-threshold-interval

bib: LuDingDasgupta2018, FanPark2010, Villani2009, WilliamsonDowns1990, Makarov1982

home_objs: def:partial-transport-polytope, def:threshold-cuts, def:identified-interval, prop:tie-face-collapse, thm:full-law-endpoint-attainment, thm:no-selection-reduction, thm:sharp-exact-mass-threshold-interval
## section: Computation and witness
This section presents the threshold-flow construction as a reader-facing algorithm and records its sparse linear-time operation count. It also works through the three-level synthetic law to show how unequal selected-complier capacities produce the sharp interval \([0,0.7]\) in a concrete compatible IV-selection model.

objs: def:three-level-witness, prop:three-level-witness, synth_20, synth_21, thm:linear-sparse-threshold-flow

bib: none

home_objs: def:threshold-flow-construction, def:three-level-witness, prop:three-level-witness, thm:linear-sparse-threshold-flow
## section: Estimation and guarded inference
This section defines the projected screened plug-in endpoint estimator, the retained-cell rule, the diagnostic face-aware multiplier handle, and the deterministic guarded confidence set. It states the fixed-law Hadamard directional limit under fixed finite support and the finite-sample uniform containment result under overlap and an aggregate survivor-mass lower bound.

objs: ass:uniform-aggregate-survivor-bound, ass:iid-sampling, def:uniform-law-class, synth_15, def:plugin-endpoint-estimator, synth_18, synth_2, synth_3, def:face-aware-inference-handle, thm:branch-free-pointwise-directional-limit, lem:weighted-capacity-mass-homogeneity, lem:weighted-capacity-lower-cut-homogeneity, lem:weighted-capacity-upper-cut-homogeneity, synth_19, synth_6, thm:uniform-deterministic-guard

bib: vanDerVaart1998, ImbensManski2004, ChernozhukovHongTamer2007, RomanoShaikh2010, Tamer2010, Molinari2020, ChernozhukovLeeRosen2013, FangSantos2019, HongLi2018

home_objs: ass:uniform-aggregate-survivor-bound, ass:iid-sampling, def:uniform-law-class, def:plugin-endpoint-estimator, def:face-aware-inference-handle, thm:branch-free-pointwise-directional-limit, lem:weighted-capacity-mass-homogeneity, lem:weighted-capacity-lower-cut-homogeneity, lem:weighted-capacity-upper-cut-homogeneity, thm:uniform-deterministic-guard
## section: Limitations and future work
This section collects the open calibrated-inference question and the model-scope limitations in one clearly labelled place. It frames the near-active-face multiplier construction as a future direction for first-order calibrated uniform inference under direction-separated triangular arrays with changing retained support, and it records that empirical reanalysis, continuous outcomes, sensitivity analysis for weak selection monotonicity, and additional concordance restrictions are future extensions.

objs: ass:direction-margin, oeq:uniform-face-multiplier

bib: Noack2026, LeeLiu2024, BartalottiKedagniPossebom2023, DeySarkarDasgupta2026

home_objs: ass:direction-margin, oeq:uniform-face-multiplier
## section: Appendix
The appendix contains the proofs, auxiliary algebra for the Ferrers threshold cuts and residual completion, details behind the no-selection reduction, concentration calculations for the deterministic guard, and the verification note. The final verification note will consolidate the Lean machine-checking scope for the frozen assumptions, definitions, propositions, algorithms, theorem statements, and proof dependencies, while identifying external citation inputs as bibliographic dependencies.

objs: none

bib: LuDingDasgupta2018, DongHeiler2026, FangSantos2019, vanDerVaart1998
home_objs: none
