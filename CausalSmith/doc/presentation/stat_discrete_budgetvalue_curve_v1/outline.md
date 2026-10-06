# Title
**Minimax estimation of budgeted treatment value curves with discrete covariates**

**Contribution statement.** For a known \(d\)-cell covariate alphabet and fixed overlap, the paper establishes the all-procedure expected squared supremum risk of order \(\min\{1,d/[n\log(ed)]\}\) for the budget-value curve on every fixed interval \([b_0,1-b_0]\), \(b_0\in[0,1/2]\), using a specified estimator and a lower bound with binding capacity.

# Notation

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(n\) | \(n\) | Number of observed records | — |
| \(d\) | \(d\) | Size of the known covariate alphabet | — |
| \(O_i\) | \(O_i=(X_i,A_i,Y_i)\) | Observed covariate, treatment, and outcome record | — |
| \(P\) | \(P\) | Full-data causal law and its observed margin | — |
| \(p_j\) | \(p_j\) | Probability mass of covariate cell \(j\) | — |
| \(e_j\) | \(e_j\) | Treatment propensity in occupied cell \(j\) | — |
| \(\mu_{aj}\) | \(\mu_{aj}\) | Potential-outcome mean for arm \(a\) in cell \(j\) | — |
| \(\tau_j\) | \(\tau_j\) | Treatment-effect difference between cell means | — |
| \(B(P)\) | \(B(P)\) | Value of the control policy | — |
| \(\epsilon\) | \(\epsilon\) | Fixed overlap parameter | ass:overlap |
| \(\mathcal M_{d,\epsilon}\) | \(\mathcal M_{d,\epsilon}\) | Causal laws on the \(d\)-cell alphabet satisfying the stated identification conditions | def:model-class |
| \(\pi\) | \(\pi\in[0,1]^d\) | Cellwise randomized treatment policy | def:budget-policy-class |
| \(b\) | \(b\) | Population treatment-capacity budget | def:budget-policy-class |
| \(\Pi_b(P)\) | \(\Pi_b(P)\) | Policies with population treatment share at most \(b\) | def:budget-policy-class |
| \(V_b(P)\) | \(V_b(P)\) | Maximum population value at budget \(b\) | def:budget-value |
| \(V(P)\) | \(V(P)\) | Budget-indexed oracle-value curve on \(I\) | def:budget-value |
| \(q_j\) | \(q_j\in\mathbb R_+^4\) | Observed treatment-outcome four-mass vector in cell \(j\) | — |
| \(q_{\zeta j}\) | \(q_{\zeta j}\) | Component of the observed four-mass vector indexed by \(\zeta\) | — |
| \(s_a(u)\) | \(s_a(u)\) | Arm-\(a\) mass of a four-vector | — |
| \(s(u)\) | \(s(u)\) | Total mass of a four-vector | — |
| \(g_a(u)\) | \(g_a(u)\) | Overlap-stabilized arm contribution from a four-vector | def:dual-process |
| \(f_\lambda(u)\) | \(f_\lambda(u)\) | Cell contribution at shadow price \(\lambda\) | def:dual-process |
| \(F_P(\lambda)\) | \(F_P(\lambda)\) | Sum of cell contributions at shadow price \(\lambda\) | def:dual-process |
| \(b_0\) | \(b_0\in[0,1/2]\) | Fixed endpoint parameter for the budget interval | def:curve-risk |
| \(I\) | \(I=[b_0,1-b_0]\) | Interval over which curve risk is assessed | def:curve-risk |
| \(\mathfrak R_{n,d,\epsilon,b_0}^{\mathrm{curve}}\) | \(\mathfrak R_{n,d,\epsilon,b_0}^{\mathrm{curve}}\) | All-procedure expected squared supremum risk | def:curve-risk |
| \(\widehat V\) | \(\widehat V\) | Generic measurable bounded-function-valued curve estimator | def:curve-risk |
| \(\widehat V_b^{\mathrm{JF}}\) | \(\widehat V_b^{\mathrm{JF}}\) | Reported Jackson–factorial budget-value estimator | def:jf-estimator |
| \(H_0\) | \(H_0=4096\) | Fixed pilot-width tuning constant | def:jf-estimator |
| \(\kappa\) | \(\kappa=1/512\) | Fixed degree tuning constant | def:jf-estimator |
| \(D_0\) | \(D_0=16\) | Fixed small-alphabet branch threshold | def:jf-estimator |
| \(L\) | \(L=\log(ed)\) | Logarithmic alphabet factor | def:jf-estimator |
| \(m\) | \(m=n/8\) | Poisson count scale for each marked sample | def:jf-estimator |
| \(K\) | \(K=\max\{2,\lfloor L/512\rfloor\}\) | Order parameter of the positive Jackson construction | def:jf-estimator |
| \(\mathcal Z\) | \(\mathcal Z=\{0,1\}^2\) | Treatment-outcome category set | def:jf-estimator |
| \(\zeta\) | \(\zeta=(a,y)\) | Treatment-outcome category index | def:jf-estimator |
| \(\widehat q_{\zeta j}\) | \(\widehat q_{\zeta j}\) | Empirical category-cell mass in the small-alphabet branch | def:jf-estimator |
| \(\widehat F(\lambda)\) | \(\widehat F(\lambda)\) | Estimated dual threshold process | def:jf-estimator |
| \(M\) | \(M\) | Auxiliary Poisson number of retained records | def:jf-estimator |
| \(N'_{\zeta j}\) | \(N'_{\zeta j}\) | Pilot count in category \(\zeta\) and cell \(j\) | def:jf-estimator |
| \(N_{\zeta j}\) | \(N_{\zeta j}\) | Evaluation count in category \(\zeta\) and cell \(j\) | def:jf-estimator |
| \(\delta\) | \(\delta=L/m\) | Pilot-width scale | def:jf-estimator |
| \(c_{\zeta j}\) | \(c_{\zeta j}\) | Scaled pilot count | def:jf-estimator |
| \(h_{\zeta j}\) | \(h_{\zeta j}\) | Pilot localization width | def:jf-estimator |
| \(\ell_{\zeta j}\) | \(\ell_{\zeta j}\) | Truncated lower localization endpoint | def:jf-estimator |
| \(u_{\zeta j}\) | \(u_{\zeta j}\) | Upper localization endpoint | def:jf-estimator |
| \(c^0_{\zeta j}\) | \(c^0_{\zeta j}\) | Center of the localization interval | def:jf-estimator |
| \(R_{\zeta j}\) | \(R_{\zeta j}\) | Radius of the localization interval | def:jf-estimator |
| \(S_j\) | \(S_j\) | Sum of the four pilot radii in cell \(j\) | def:jf-estimator |
| \(J_K(t)\) | \(J_K(t)\) | Normalized positive order-four Jackson function | def:jf-estimator |
| \(C_K\) | \(C_K\) | Positive constant normalizing \(J_K\) to integrate to one | def:jf-estimator |
| \(D\) | \(D=2(K-1)\) | Coordinatewise polynomial degree bound | def:jf-estimator |
| \(P_{j,\lambda}\) | \(P_{j,\lambda}\) | Pilot-local tensor polynomial for the cell contribution | def:jf-estimator |
| \(\beta_{j,\alpha}(\lambda)\) | \(\beta_{j,\alpha}(\lambda)\) | Coefficient in the centered monomial expansion | def:jf-estimator |
| \(U_h(N;z)\) | \(U_h(N;z)\) | Factorial-moment statistic for a centered power | def:jf-estimator |
| \((N)_t\) | \((N)_t\) | Falling factorial of the evaluation count | def:jf-estimator |
| \(Z_j(\lambda)\) | \(Z_j(\lambda)\) | Unclipped polynomial estimate of a cell contribution | def:jf-estimator |
| \(\Pi_{[r,s]}(x)\) | \(\Pi_{[r,s]}(x)\) | Projection of \(x\) onto the interval \([r,s]\) | def:jf-estimator |
| \(T_j(\lambda)\) | \(T_j(\lambda)\) | Clipped estimate of a cell contribution | def:jf-estimator |
| \(\widetilde F^{\mathrm{cap}}(\lambda)\) | \(\widetilde F^{\mathrm{cap}}(\lambda)\) | Capped auxiliary threshold process | def:jf-estimator |
| \(\mathsf H_\epsilon\) | \(\mathsf H_\epsilon\) | Set of constants satisfying the five uniform process-bound groups | def:process-handle |
| \(G_j\) | \(G_j\) | Quarter-halfwidth pilot event for cell \(j\) | def:process-handle |
| \(v_j\) | \(v_j\) | Pilot-error scale \(\sqrt{p_jL/m}+L/m\) | def:process-handle |
| \(\|h\|_{BV([0,1])}\) | \(\|h\|_{BV([0,1])}\) | Endpoint magnitude plus total variation | def:process-handle |
| \(k\) | \(k\) | Number of cell pairs in the lower-bound family | def:paired-family |
| \(r=(r_1,\ldots,r_k)\) | \(r=(r_1,\ldots,r_k)\) | Simplex vector of pair masses | def:paired-family |
| \(\theta_i\) | \(\theta_i\in[-1/8,1/8]\) | Within-pair treatment-mean contrast | def:paired-family |
| \((i,+),(i,-)\) | \((i,+),(i,-)\) | Two cells in pair \(i\) | def:paired-family |
| \(\mathcal P^{\mathrm{pair}}_k\) | \(\mathcal P^{\mathrm{pair}}_k\) | Paired causal lower-bound family | def:paired-family |
| \(R,S\) | \(R,S\in\Delta_k\) | Two discrete laws in the normalized lower-bound embedding | — |

notation_gaps: \(P\)=no anchored environment defines the full-data law and its observed margin; \(p_j,e_j,\mu_{aj},\tau_j,B(P)\)=cell masses, propensities, potential-outcome means, effects, and control value are used without anchored definitions; \(q_j,q_{\zeta j},s_a(u),s(u)\)=the observed four-mass vector and its mass operators lack anchored definitions; \(R,S,\Delta_k\)=the two-sample laws and simplex notation lack an anchored definition.

env_overrides: def:jf-estimator=algorithmv, prop:dual-representation=propositionv, prop:paired-capacity-identity=propositionv, prop:fixed-alphabet-reduction=propositionv

# Sections

## section: Introduction

Plan the question as simultaneous estimation of the population oracle value across treatment-capacity budgets when the known covariate alphabet may grow. State the fixed-overlap, binary-treatment scope and the matched squared supremum-risk rate in words, with a plain-word gloss at each symbol’s first use. Explain the scientific role of the binding half-population comparison and the full-curve case \(b_0=0\). Point in one factual sentence to the appendix verification note. Draft the abstract and introduction after the mathematical sections.

objs: none
bib: none

home_objs: none
## section: Related work

Position the oracle-value curve against the constrained value-process asymptotics of \citet[Section 4 and Theorem 4.1.1]{FengHongNekipelov2026}, optimized-value uniform inference in \citet{FirpoGalvaoParker2023}, and Qini-value analysis in \citet{SverdrupWuAtheyWager2025}. Distinguish the paper’s finite-sample squared supremum-risk target for a growing known discrete alphabet from policy-welfare regret and constrained allocation results, and relate its polynomial and moment-matching tools to large-alphabet functional estimation. Explain that \citet{CausalSmithUnrestricted2026} treats the unrestricted scalar target, which is the full curve’s \(b=1\) coordinate.

objs: none
bib: FengHongNekipelov2026, FirpoGalvaoParker2023, SverdrupWuAtheyWager2025, LuedtkeVanDerLaan2016, BhattacharyaDupas2012, KitagawaTetenov2018, AtheyWager2021, Pellatt2023, Sun2026, Sakaguchi2025, Wu2016, JiaoVenkatHanWeissman2015, JiaoHanWeissman2018, CaiLow2011, CausalSmithUnrestricted2026

home_objs: none
## section: Setup and assumptions

Introduce the observed records, full-data law, fixed-overlap model, randomized budget-feasible policies, and population budget-value curve. Define the four-mass representation and shadow-price process before presenting the dual identity and its supremum-error contraction. Close with the all-procedure curve-risk criterion, including the endpoint-inclusive interval convention.

objs: ass:iid-sampling, ass:consistency, ass:conditional-exchangeability, synth_1, synth_2, synth_3, ass:overlap, def:model-class, def:budget-policy-class, synth_7, synth_4, synth_5, def:budget-value, synth_9, synth_6, def:dual-process, synth_12, prop:dual-representation, synth_11, def:curve-risk
bib: Rubin1974, RosenbaumRubin1983

home_objs: ass:iid-sampling, ass:consistency, ass:conditional-exchangeability, ass:overlap, def:model-class, def:budget-policy-class, def:budget-value, def:dual-process, prop:dual-representation, def:curve-risk
## section: Minimax risk for the budget-value curve

State the matched risk theorem first and explain how one shadow-price process controls every budget through the dual identity. Give a concise estimator overview, then state the half-population lower bound with positive occupied-cell effects, binding capacity, and constant unrestricted value. Give the fixed-alphabet and equal-effect special cases after the general result. Place the complete estimator specification and its technical upper-bound theorem with the process bounds in the appendix.

objs: thm:matched-curve-frontier, thm:capacity-active-lower, prop:fixed-alphabet-reduction
bib: CausalSmithUnrestricted2026, JiaoHanWeissman2018

home_objs: thm:matched-curve-frontier, thm:capacity-active-lower, prop:fixed-alphabet-reduction
## section: Discussion and limitations

Interpret the rate as a simultaneous budget-curve guarantee, including the full interval when \(b_0=0\), and explain why the half-population experiment isolates capacity as the source of lower-bound difficulty. In a clearly titled limitations subsection, identify shrinking-budget limits, adaptive bands, policy regret, computational complexity, learned alphabets, and multi-arm allocation as future directions. Keep literature discussion tied to interpretation of the established results.

objs: none
bib: none

home_objs: none
## section: Appendix: Proofs and verification scope

Give the complete Jackson–factorial construction and its uniform upper-bound theorem, followed by the bounded-variation property, pilot-local process criterion, and integrated bounds. Introduce the paired family immediately before its capacity identity and exact two-sample reduction; place the two-sample \(L_1\) lemma before its lower-bound use. Supply proofs for the main propositions and the matched theorem. End with a brief verification note identifying the machine-checked statements and distinguishing them from model assumptions and cited mathematical inputs.

objs: synth_8, def:jf-estimator, thm:curve-upper, lem:bv-lipschitz, def:process-handle, lem:pilot-radius-second-moment, lem:jackson-boundary-adaptive, lem:pilot-bad-score-moment, lem:bv-maximal-cell-paths, lem:capped-marked-count-identity, thm:integrated-process-certificate, lem:empirical-threshold-process-bounded, lem:averaged-threshold-process-bounded, def:paired-family, synth_10, prop:paired-capacity-identity, lem:two-sample-l1-lower
bib: CaiLow2011, JiaoHanWeissman2018, Wu2016, JiaoVenkatHanWeissman2015
home_objs: def:jf-estimator, thm:curve-upper, lem:bv-lipschitz, def:process-handle, lem:pilot-radius-second-moment, lem:jackson-boundary-adaptive, lem:pilot-bad-score-moment, lem:bv-maximal-cell-paths, lem:capped-marked-count-identity, thm:integrated-process-certificate, lem:empirical-threshold-process-bounded, lem:averaged-threshold-process-bounded, def:paired-family, prop:paired-capacity-identity, lem:two-sample-l1-lower
