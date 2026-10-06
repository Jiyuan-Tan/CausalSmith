# Title
**Minimax precision for total treatment effects with partially observed interference networks**

**Contribution statement.** For bounded heterogeneous additive responses in a fixed population, the paper characterizes the minimax squared risk of estimating the total treatment effect from one half-Bernoulli experiment with independently retained interference edges, constructs an observable estimator attaining that order, and identifies the exact conditions for uniform consistency.

env_overrides: lem:published-model=propositionv

# Notation

notation_gaps: \(V\)=population and indexing convention lack an anchored definition; \(n\)=population size lacks an anchored definition; \(Y_i(z)\)=additive potential-outcome map lacks an anchored definition; \(z\)=assignment argument lacks an anchored definition; \(\tau(\theta)\)=all-treated-versus-all-control population contrast lacks an anchored definition; \(Z\)=assignment vector lacks an anchored definition; \(W\)=audit-mark array lacks an anchored definition; \(W_{ij}\)=individual audit marks lack an anchored definition; \(H\)=retained graph lacks an anchored definition; \(X_i\)=centered own-treatment sign lacks an anchored definition; \(X_j\)=centered source-treatment sign lacks an anchored definition; \(O\)=complete observed record lacks an anchored definition; \(P_{\theta,q}\)=fixed-schedule experiment law lacks an anchored definition; \(B\)=block count lacks an anchored construction definition; \(C_\ell\)=recipient blocks lack an anchored construction definition; \(f\)=baseline density lacks an anchored specification; \(p\)=association-revelation probability is introduced outside an anchored definition; \(r_\ell\)=not present in the frozen layer and requires no notation row; \(u_\ell\)=remaining block capacities lack an anchored definition; \(A_\ell\)=revealed sign sums lack an anchored definition; \(M\)=total remaining capacity lacks an anchored definition; \(K\)=observed global hidden treated-source count lacks an anchored definition; \(y\)=distinct block-response vector lacks an anchored definition; \(y_\ell\)=block-response coordinate lacks an anchored definition; \(\lambda_{\sigma,h}(y\mid H,Z)\)=conditional density is introduced by a lemma rather than an anchored definition; \([x^K]\)=coefficient-extraction convention lacks an anchored definition; \(\operatorname{TV}\)=total-variation convention lacks an anchored definition; \(\varphi\)=square-root density is introduced by a lemma rather than an anchored definition; \(F_\varepsilon(w)\)=translated density family is introduced by a lemma rather than an anchored definition; \(g_d(w)\)=sign-mixture density is introduced by a lemma rather than an anchored definition; \(a_{|E|}(w)\)=Walsh coefficient functions are introduced by a lemma rather than an anchored definition; \(a_0\)=constant Walsh coefficient is introduced by a lemma rather than an anchored definition; \(a_s(w)\)=order-indexed Walsh coefficient functions lack an anchored definition; \(\gamma_s\)=integrated Walsh energies are introduced by a lemma rather than an anchored definition; \(\eta\)=aggregate Walsh energy is introduced by a lemma rather than an anchored definition; \(\eta_1\)=degree-weighted Walsh energy is introduced by a lemma rather than an anchored definition; \(Q_H\)=conditional reference law is introduced by a lemma rather than an anchored definition; \(L_+\)=conditional density ratio is introduced by a lemma rather than an anchored definition; \(\chi_H^2\)=conditional chi-squared divergence is introduced by a lemma rather than an anchored definition; \(\mathsf Q_+,\mathsf Q_-\)=two-prior record mixture laws are introduced by a lemma rather than an anchored definition; \(s(B,d,q)\)=testing scale is introduced by a theorem rather than an anchored definition; \(\kappa\)=testing constant is introduced by a theorem rather than an anchored definition; \(\bar h(B,d,q)\)=testing radius is introduced by a theorem rather than an anchored definition; \(s\)=local testing-scale notation is introduced by a theorem rather than an anchored definition; \(\bar h\)=local testing-radius notation is introduced by a theorem rather than an anchored definition; \(\widetilde G\)=augmented graph is introduced by a lemma rather than an anchored definition; \(c^{\mathrm{pub}}_{i,\varnothing}\)=published baseline coefficient is introduced by a lemma rather than an anchored definition; \(c^{\mathrm{pub}}_{i,\{i\}}\)=published own-treatment coefficient is introduced by a lemma rather than an anchored definition; \(c^{\mathrm{pub}}_{i,\{j\}}\)=published spillover coefficient is introduced by a lemma rather than an anchored definition; \(\beta\)=published interaction-order convention lacks an anchored definition; \(Y_{\max}\)=published coefficient-mass convention lacks an anchored definition; \(d_n,q_n\)=admissible population-sequence convention lacks an anchored definition.

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(V\) | \(V\) | Fixed finite population | notation gap |
| \(n\) | \(n\) | Population size, with \(n\ge4\) | notation gap |
| \(d\) | \(d\) | Common off-diagonal in-degree and out-degree bound | def:model |
| \(q\) | \(q\) | Known edge-retention probability | notation gap: introduce with audit design |
| \(\theta=(G,a,t,b)\) | \(\theta=(G,a,t,b)\) | Fixed graph-and-coefficient schedule | def:model |
| \(G\) | \(G\) | Simple directed off-diagonal interference graph | def:model |
| \(a\) | \(a\) | Vector of schedule baseline coefficients | def:model; coordinate meanings require the outcome-map gap |
| \(t\) | \(t\) | Vector of own-treatment coefficients | def:model; coordinate meanings require the outcome-map gap |
| \(b\) | \(b\) | Array of edge spillover coefficients | def:model; coordinate meanings require the outcome-map gap |
| \(a_i\) | \(a_i\) | Unit baseline coefficient | def:model; coordinate meanings require the outcome-map gap |
| \(t_i\) | \(t_i\) | Unit own-treatment coefficient | def:model; coordinate meanings require the outcome-map gap |
| \(b_{ij}\) | \(b_{ij}\) | Source-to-recipient spillover coefficient | def:model; coordinate meanings require the outcome-map gap |
| \(\mathcal M_{n,d}\) | \(\mathcal M_{n,d}\) | Schedules satisfying both degree bounds and unit coefficient-mass bound | def:model |
| \(Y_i(z)\) | \(Y_i(z)\) | Additive potential outcome at assignment \(z\) | notation gap |
| \(z\) | \(z\) | Binary assignment argument of the potential-outcome map | notation gap |
| \(Y_i(Z)\) | \(Y_i(Z)\) | Realized outcome under the experimental assignment | notation gap: outcome map and assignment |
| \(Y(Z)\) | \(Y(Z)\) | Vector of realized outcomes | notation gap: outcome map and assignment |
| \(\tau(\theta)\) | \(\tau(\theta)\) | Population all-treated-versus-all-control contrast | notation gap |
| \(Z\) | \(Z\) | Random treatment-assignment vector | notation gap |
| \(W\) | \(W\) | Random off-diagonal audit-mark array | notation gap |
| \(W_{ij}\) | \(W_{ij}\) | Audit mark for an ordered off-diagonal pair | notation gap |
| \(H\) | \(H\) | Recorded retained-edge graph | notation gap |
| \(X_i\) | \(X_i\) | Centered own-treatment sign | notation gap |
| \(X_j\) | \(X_j\) | Centered source-treatment sign | notation gap |
| \(O\) | \(O\) | Complete graph, assignment, and realized-outcome record | notation gap |
| \(\xi\) | \(\xi\) | Independent uniform estimator-randomization seed | def:risk |
| \(P_{\theta,q}\) | \(P_{\theta,q}\) | Experiment law for a fixed schedule and retention probability | notation gap |
| \(T(O,\xi)\) | \(T(O,\xi)\) | Measurable randomized estimator of the causal target | def:risk; estimator domain requires the record gap |
| \(\mathcal L(T;\theta,q)\) | \(\mathcal L(T;\theta,q)\) | Expected squared estimation loss | def:risk |
| \(R_{n,d}(q)\) | \(R_{n,d}(q)\) | Minimax squared risk over the declared schedule class | def:risk |
| \(T_q\) | \(T_q\) | Observable inverse-inclusion score at positive retention | def:audit-score |
| \(T_q(O)\) | \(T_q(O)\) | Inverse-inclusion score evaluated on the observed record | def:audit-score |
| \(T_G\) | \(T_G\) | Score using the supplied true graph | def:oracle-score |
| \(u(n,d,q)\) | \(u(n,d,q)\) | Explicit upper-risk envelope, infinite at zero retention | def:upper-envelope |
| \(T^{\mathrm{up}}\) | \(T^{\mathrm{up}}\) | Clipped inverse-inclusion score or zero according to the envelope | def:upper-rule |
| \(T^{\mathrm{up}}(O)\) | \(T^{\mathrm{up}}(O)\) | Total observable upper rule evaluated on a record | def:upper-rule |
| \(F(n,d,q)\) | \(F(n,d,q)\) | Explicit bounded positive risk scale | def:frontier-scale |
| \(F\) | \(F\) | Explicit risk-scale function | def:frontier-scale |
| \(T^\star_{n,d,q}\) | \(T^\star_{n,d,q}\) | Named total observable attaining rule | def:frontier-rule |
| \(T^\star_{n,d,q}(O)\) | \(T^\star_{n,d,q}(O)\) | Attaining rule evaluated on the observed record | def:frontier-rule |
| \(T^\star\) | \(T^\star\) | Local shorthand for the attaining rule in the explicit-constant statement | def:frontier-rule |
| \(d_n,q_n\) | \(d_n,q_n\) | Admissible degree and retention sequences indexed by population size | notation gap |
| \(R^G_{n,d}(q)\) | \(R^G_{n,d}(q)\) | Minimax squared risk with the true graph supplied | def:supplied-risk |
| \(G(\theta)\) | \(G(\theta)\) | True graph component of a fixed schedule | def:supplied-risk |
| \(T^G\) | \(T^G\) | Borel-measurable randomized rule with the true graph supplied | def:supplied-risk |
| \(T^G(O,G(\theta),\xi)\) | \(T^G(O,G(\theta),\xi)\) | Supplied-graph rule evaluated on its complete inputs | def:supplied-risk |
| \(\operatorname{range}(O)\) | \(\operatorname{range}(O)\) | Record domain inherited from graph, assignment, and outcome coordinates | def:supplied-risk; underlying record requires the record gap |
| \(B\) | \(B\) | Number of blocks in the auxiliary experiment | notation gap |
| \(m=Bd\) | \(m=Bd\) | Number of sources in the block construction | def:testing-handle |
| \(S\) | \(S\) | Uniform ordered source partition | def:block-prior; partition domain requires construction context |
| \(S_\ell\) | \(S_\ell\) | Source block in the ordered partition | def:block-prior; partition domain requires construction context |
| \(C_\ell\) | \(C_\ell\) | Recipient block in the auxiliary experiment | notation gap |
| \(U_1,\ldots,U_B\) | \(U_1,\ldots,U_B\) | Independent pre-experiment block baselines with density \(f\) | def:block-prior |
| \(U_\ell\) | \(U_\ell\) | Baseline for block \(\ell\) | def:block-prior |
| \(f\) | \(f\) | Baseline density invoked by the block construction | notation gap |
| \(\sigma\) | \(\sigma\) | Sign indexing the two block priors | def:block-prior; parameter domain requires construction context |
| \(h\) | \(h\) | Amplitude indexing the block priors | def:block-prior; parameter domain requires construction context |
| \(\Pi_{\sigma,h}\) | \(\Pi_{\sigma,h}\) | Distribution over fixed block schedules | def:block-prior |
| \(P_{\sigma,h}\) | \(P_{\sigma,h}\) | Complete-record mixture law under the block prior | def:block-prior |
| \(p=1-(1-q)^d\) | \(p=1-(1-q)^d\) | Probability that a source association is revealed | notation gap |
| \(h_\circ(B,d,q)\) | \(h_\circ(B,d,q)\) | Explicit testing amplitude | def:testing-handle |
| \((\Pi_{+1,h_\circ},\Pi_{-1,h_\circ})\) | \((\Pi_{+1,h_\circ},\Pi_{-1,h_\circ})\) | Pair of opposite-sign priors at the testing amplitude | def:testing-handle |
| \((P_{+1,h_\circ},P_{-1,h_\circ})\) | \((P_{+1,h_\circ},P_{-1,h_\circ})\) | Corresponding complete-record mixture-law pair | def:testing-handle |
| \(P_{+1,h},P_{-1,h}\) | \(P_{+1,h},P_{-1,h}\) | Opposite-sign complete-record laws at amplitude \(h\) | def:block-prior |
| \(u_\ell\) | \(u_\ell\) | Remaining source capacity of a block | notation gap |
| \(A_\ell\) | \(A_\ell\) | Revealed source-sign sum for a block | notation gap |
| \(M\) | \(M\) | Total remaining source capacity | notation gap |
| \(K\) | \(K\) | Observed global hidden treated-source count | notation gap |
| \(y\) | \(y\) | Vector of distinct block responses | notation gap |
| \(y_\ell\) | \(y_\ell\) | Distinct response of block \(\ell\) | notation gap |
| \(\lambda_{\sigma,h}(y\mid H,Z)\) | \(\lambda_{\sigma,h}(y\mid H,Z)\) | Conditional block-response density given the complete graph and assignment | notation gap |
| \([x^K]\) | \([x^K]\) | Coefficient extraction at the observed count | notation gap |
| \(x\) | \(x\) | Polynomial indeterminate in the conditional likelihood | notation gap: coefficient-extraction convention |
| \(\operatorname{TV}\) | \(\operatorname{TV}\) | Total-variation distance between probability laws | notation gap |
| \(s(B,d,q)\) | \(s(B,d,q)\) | Bounded testing-amplitude scale | notation gap |
| \(\kappa\) | \(\kappa\) | Universal constant in the testing-amplitude bound | notation gap |
| \(\bar h(B,d,q)\) | \(\bar h(B,d,q)\) | Supremum amplitude with total variation at most one half | notation gap |
| \(s\) | \(s\) | Local testing-scale notation in the consolidated testing statement | notation gap |
| \(\bar h\) | \(\bar h\) | Local testing-radius notation in the consolidated testing statement | notation gap |
| \(\varphi=\sqrt f\) | \(\varphi=\sqrt f\) | Square root of the baseline density | notation gap |
| \(\varphi'(w)\) | \(\varphi'(w)\) | Derivative of the square-root density | notation gap: square-root-density family |
| \(\varepsilon\in\{-1,1\}^d\) | \(\varepsilon\in\{-1,1\}^d\) | Sign vector indexing translated densities | notation gap: translated-density family |
| \(F_\varepsilon(w)\) | \(F_\varepsilon(w)\) | Baseline density translated by the scaled sign sum | notation gap |
| \(g_d(w)\) | \(g_d(w)\) | Uniform sign mixture of translated densities | notation gap |
| \(E\subseteq\{1,\ldots,d\}\) | \(E\subseteq\{1,\ldots,d\}\) | Subset indexing a Walsh character | notation gap: Walsh expansion |
| \(a_{|E|}(w)\) | \(a_{|E|}(w)\) | Walsh coefficient function indexed by subset size | notation gap |
| \(a_0\) | \(a_0\) | Constant coefficient of the normalized likelihood expansion | notation gap |
| \(a_s(w)\) | \(a_s(w)\) | Walsh coefficient function of order \(s\) | notation gap |
| \(\gamma_s\) | \(\gamma_s\) | Integrated squared Walsh coefficient of order \(s\) | notation gap |
| \(\eta\) | \(\eta\) | Sum of Walsh energies weighted by subset multiplicities | notation gap |
| \(\eta_1\) | \(\eta_1\) | Sum of Walsh energies additionally weighted by order | notation gap |
| \(Q_H\) | \(Q_H\) | Conditional reference law with actual assignments and independent mixture responses | notation gap |
| \(L_+\) | \(L_+\) | Positive-prior conditional density ratio relative to the reference law | notation gap |
| \(\chi_H^2\) | \(\chi_H^2\) | Conditional squared density-ratio discrepancy | notation gap |
| \(\mathbf1\{M\ge m/4\}\) | \(\mathbf1\{M\ge m/4\}\) | Indicator of the remaining-capacity event | notation gap: block-capacity family |
| \(\mathsf Q_+,\mathsf Q_-\) | \(\mathsf Q_+,\mathsf Q_-\) | Full-record mixtures of the two priors in the risk reduction | notation gap |
| \(\Delta\) | \(\Delta\) | Positive magnitude of the two constant causal targets | notation gap: two-prior reduction |
| \(\widetilde G\) | \(\widetilde G\) | True graph augmented with all diagonal arrows | notation gap |
| \(c^{\mathrm{pub}}_{i,\varnothing}\) | \(c^{\mathrm{pub}}_{i,\varnothing}\) | Published-model baseline coefficient | notation gap |
| \(c^{\mathrm{pub}}_{i,\{i\}}\) | \(c^{\mathrm{pub}}_{i,\{i\}}\) | Published-model own-treatment coefficient | notation gap |
| \(c^{\mathrm{pub}}_{i,\{j\}}\) | \(c^{\mathrm{pub}}_{i,\{j\}}\) | Published-model source-treatment coefficient | notation gap |
| \(\beta=1\) | \(\beta=1\) | Published interaction-order-one specialization | notation gap |
| \(Y_{\max}\) | \(Y_{\max}\) | Published coefficient-mass bound | notation gap |

# Sections

## section: Abstract

Plan a compact statement of the causal question, fixed-population additive model, half-Bernoulli assignment, and calibrated independent edge retention. Emphasize the sharp squared-risk order, observable attaining rule, consistency characterization, and collection threshold. Use words or first-use appositives for symbols appearing before their definitions. Draft this material after the body and proofs.

objs: none

bib: none

home_objs: none
## section: Introduction

Lead with how much interference-network information one experiment needs to estimate the population all-treated-versus-all-control contrast precisely. Establish the statistical relevance of observing retained edges together with assignments and contemporaneous noiseless outcomes, then organize the contribution around precision, attainable estimation, and population-sequence consistency. Preview the degree–retention interaction and the prospective use of calibrated edge collection. Include one factual sentence directing readers to the appendix verification note. Draft the introduction last.

objs: none

bib: JiangDengWangWang2024ApproximateNetworks

home_objs: none
## section: Related work

Position the contribution against the closest results by comparing estimands, response classes, assignment mechanisms, information supplied to estimators, and the type of precision guarantee. Compare known-neighborhood SNIPE and its published variance and minimax statements with the present order-one specialization and augmented degree convention, using \citep[Sections 3--5; Theorems 1--2]{CortezRodriguezEichhornYu2023SNIPE}. Compare supplied-network design optimization under its own envelope with \citep[Corollary 5.4]{KandirosHarshawSavje2026DesignBasedMinimax}. Credit known-error-rate exposure correction through \citep[Section 3; Theorems 4--7]{LiSussmanKolaczyk2021NetworkNoise}, supplied-supergraph estimation through \citep[Theorems 1, 4, and 8; Appendix B.1]{ShankarEtAl2024UNITE}, and graph-free additive estimation with an observed baseline through \citep[Corollary 3]{YuAiroldiBorgsChayes2022}. Distinguish the unrestricted squared-risk characterization from the surrogate-network estimator variance and omitted-influence bias guarantees in \citep[Assumptions 1--3; Theorems 1--2; Lemma 2]{JiangDengWangWang2024ApproximateNetworks}. Use the broader design-based and linear-functional literature selectively. Attribute the sharper supplied-graph benchmark to the disclosed supplied research note in prose; its citation awaits a verified pool key.

objs: none

bib: CortezRodriguezEichhornYu2023SNIPE, KandirosHarshawSavje2026DesignBasedMinimax, LiSussmanKolaczyk2021NetworkNoise, ShankarEtAl2024UNITE, YuAiroldiBorgsChayes2022, JiangDengWangWang2024ApproximateNetworks, HarshawSavjeWang2022GeneralDesignFramework, KungSussman2022AdditiveExposure, Sussman2017, Aronow2017, Rubin1974, Horvitz1952

home_objs: none
## section: Population, causal target, and observation design

Introduce the fixed population, directed source-to-recipient convention, additive potential outcomes, causal population contrast, and bounded schedule class. Resolve the main-text notation gaps in coherent population-and-outcome and assignment-and-record definition families immediately before use. Present the degree and coefficient restrictions together, followed by independent half-Bernoulli assignment and the independent audit design. Define the complete observed record, estimator randomization, experiment law, squared loss, and minimax risk. Explain the compulsory own-treatment coordinates and the published augmented degree convention, pointing to \cref{lem:published-model} for the correspondence.

objs: synth_1, ass:in-degree, ass:out-degree, ass:coefficient-mass, def:model, ass:assignment, ass:audit, ass:design-independence, synth_3, def:risk

bib: CortezRodriguezEichhornYu2023SNIPE

home_objs: synth_1, ass:in-degree, ass:out-degree, ass:coefficient-mass, def:model, ass:assignment, ass:audit, ass:design-independence, synth_3, def:risk
## section: Minimax precision and attainable estimation

Introduce the observable inverse-inclusion score, the supplied-graph comparison score, the upper envelope, and the total clipped-or-zero rule before presenting the headline minimax characterization. Place the explicit risk scale and named attaining rule immediately before \cref{thm:observed-record-precision-frontier}. Develop the statistical interpretation of the degree and edge-collection components, the saturation of worst-case squared risk, and the exact uniform-consistency conditions. Explain the audit variance decomposition through \cref{lem:score-audit}, and give a short proof roadmap connecting the observable upper bound to complete-record block testing. Keep the main exposition centered on the causal estimation problem; place overlapping endpoint and explicit-constant statements with the proof consolidation.

objs: synth_2, def:audit-score, def:oracle-score, def:upper-envelope, def:upper-rule, def:frontier-scale, def:frontier-rule, thm:observable-upper, thm:observed-record-precision-frontier

bib: Horvitz1952

home_objs: def:audit-score, def:oracle-score, def:upper-envelope, def:upper-rule, def:frontier-scale, def:frontier-rule, thm:observable-upper, thm:observed-record-precision-frontier
## section: Edge collection and the supplied-graph benchmark

Interpret calibrated retention as a prospective data-collection choice. Explain how the retention threshold interacts with degree and population size, how the consistency conditions translate into collection requirements, and how the supplied-graph comparison isolates the intrinsic degree component of precision. Introduce the supplied-graph decision problem here and use \cref{lem:supplied-block-record-lower,lem:score-audit} to explain its benchmark under the same schedule class and assignment law. Connect this interpretation to the platform workflow using its stated sampling and influence conditions.

objs: def:supplied-risk

bib: JiangDengWangWang2024ApproximateNetworks

home_objs: def:supplied-risk
## section: Limitations and future work

Collect genuine scope boundaries in this explicitly labelled section. Discuss extensions to estimated retention rates, false-positive edges, alternative assignments, repeated experiments, richer response models, and uncertainty quantification. Distinguish uniform squared-risk precision from exact minimax constants and confidence-interval coverage. State the conditions required to connect calibrated independent sampling to a platform collection mechanism, and identify graph-recovery questions as a separate future direction.

objs: none

bib: JiangDengWangWang2024ApproximateNetworks

home_objs: none
## section: Appendix A: Observable estimation and supplied-graph comparison

Give the proof of \cref{lem:score-audit} and the observable upper guarantee, including unbiasedness, the variance decomposition, coefficient-mass control, clipping, and measurability. Present the supplied-graph lower comparison and consolidate the endpoint statements after their required arguments. Place the published-model correspondence here, preserving augmented degree indexing and the same-channel condition for class-inclusion transfer. Define any proof-specific notation before its first use.

objs: lem:score-audit, lem:supplied-block-record-lower, lem:published-model, thm:supported-boundaries

bib: CortezRodriguezEichhornYu2023SNIPE

home_objs: lem:score-audit, lem:supplied-block-record-lower, lem:published-model, thm:supported-boundaries
## section: Appendix B: Complete-record block experiments

Introduce the auxiliary construction parameters, source partitions, recipient blocks, baseline density, and observable block statistics in grouped anchored definitions before the block prior. Present the prior, testing handle, support and target calculations, and exact conditional likelihood. Explain how the likelihood preserves retained-edge labels, detailed audit subsets, treatment coordinates, repeated response information, and the global count constraint. Keep the pre-experiment baseline randomization explicit as a prior over fixed schedules.

objs: synth_4, def:block-prior, def:testing-handle, lem:block-law

bib: none

home_objs: def:block-prior, def:testing-handle, lem:block-law
## section: Appendix C: Translation bounds and hidden-allocation contraction

Introduce the square-root-density, translated-density, Walsh-energy, and conditional-reference-law families in anchored definitions before their first uses. Develop the translation-affinity bound, the all-degree channel-energy calculation, and the hidden-allocation contraction. Organize the argument around information in the complete observation experiment and the averaging over its actual retained-edge marginal.

objs: lem:baseline-translation-affinity, lem:walsh-channel-energy, lem:hidden-allocation-contraction

bib: none

home_objs: lem:baseline-translation-affinity, lem:walsh-channel-energy, lem:hidden-allocation-contraction
## section: Appendix D: Testing bounds and minimax proofs

Define total variation, the testing scale and radius, and the generic two-prior mixture notation before use. Prove the uniform block-testing comparison and its radius characterization, then give the testing-to-estimation reduction and combine the block and supplied-graph comparisons across admissible degrees and retention probabilities. Include the consolidated testing statement, the precision handle, and the explicit-constant precision statement after the arguments they summarize. Complete the scale comparison and both directions of the population-sequence consistency characterization.

objs: thm:block-testing-scale, thm:nonlocal-testing-answer, lem:full-record-two-prior-risk, def:frontier-handle, thm:frontier-answer

bib: Tsybakov2009

home_objs: thm:block-testing-scale, thm:nonlocal-testing-answer, lem:full-record-two-prior-risk, def:frontier-handle, thm:frontier-answer
## section: Appendix E: Verification note

Consolidate the Lean machine-checking scope using the available theorem-local verification metadata. Identify the checked results by their anchored references and distinguish the population-model restrictions, experimental laws, and any cited dependency inputs from conclusions established within the checked development. Preserve generated trust-boundary disclosures and their source locators. Keep this note factual and separate from the paper’s scientific contribution; prepare it from verification records without inferring a broader checked scope from the mathematical statements alone.

objs: none

bib: none
home_objs: none
