# Title
**Treatment effect estimation with auxiliary records and diminishing overlap**

**Contribution statement.** The paper establishes the minimax squared-error rate for a discrete average treatment effect uniformly over the public overlap floor and the numbers of complete and auxiliary treatment–covariate records, constructs an attaining estimator, and characterizes the resulting consistency and auxiliary-data gains.

# Notation

The table specifies definition homes for notation appearing in the frozen environments. Local indices, generic numerical comparison constants, standard arithmetic and probability operators, and conventional asymptotic relations retain their standard meanings. Rows marked “gap” require an anchored presentation definition before first use. Repeated notation with different mathematical roles receives separate rows.

env_overrides: def:estimator-handle=algorithmv, def:prior-handle=algorithmv, def:baseline=algorithmv, prop:benchmark-recovery=propositionv

notation_gaps: \(X,A,Y\)=the observation coordinates need an anchored definition, \(P\)=the observable probability law needs an anchored definition, \(p_j(P),s_{aj}(P),q_{aj}(P),e_j(P),\mu_{aj}(P)\)=the population cell quantities and their null-cell conventions need an anchored definition, \(P_{XA}\)=the treatment–covariate marginal and its table representation need an anchored definition, \(\mathcal D,\mathcal L,U,\mathrm{Uniform}[0,1]\)=the observed records and independent randomization seed need an anchored definition, \(H,Y_0,Y_1\)=the potential-outcome extension and compatibility need an anchored definition, \(T^{\mathrm K}\)=the exact-marginal rule domain needs an anchored definition, \(b(n,\epsilon),f(n,m,d)\)=the benchmark functions are used without frozen definition homes, \(\mathbf v\)=the domain of allowed experiment sequences needs an anchored definition, \(\operatorname{clip}_{[-1,1]}\)=the clipping operator needs an anchored definition, \(\operatorname{TV}(\nu,\nu'),D(\nu\Vert\nu'),\|\sigma\|_{\mathrm{TV}}\)=the finite testing quantities and signed-measure norm need an anchored definition, \(g(K),H_j,\psi_a\)=the inverse-count proof quantities are introduced inside lemmas and need an appendix definition home, \(C_L(z),D,\widehat G\)=the polynomial-certificate quantities are introduced inside a lemma and need an appendix definition home, \(Z_j,K_j,W_j\)=the independent Poisson counts used in the arm-risk calculation need an appendix definition home, \(h_i,J_i,A,\vartheta\)=the generic prefix-transfer experiment and risk-bound quantities need an appendix definition home, \(C_0,H_0\)=the named proof constants need an appendix definition home, \(\operatorname{Poi}(\lambda)\)=the Poisson law used by the auxiliary calculations needs an appendix definition home

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(X\) | \(X\) | Covariate coordinate on the finite alphabet | gap; setup |
| \(A\) | \(A\) | Binary treatment coordinate | gap; setup |
| \(Y\) | \(Y\) | Binary observed outcome coordinate | gap; setup |
| \(P\) | \(P\) | Probability law of the complete observation | gap; setup |
| \(p_j(P)\) | \(p_j(P)\) | Covariate-cell probability | gap; setup |
| \(s_{aj}(P)\) | \(s_{aj}(P)\) | Joint treatment–covariate cell probability | gap; setup |
| \(q_{aj}(P)\) | \(q_{aj}(P)\) | Outcome-success probability in a treatment–covariate cell | gap; setup |
| \(e_j(P)\) | \(e_j(P)\) | Treatment propensity in an occupied covariate cell | gap; setup |
| \(\mu_{aj}(P)\) | \(\mu_{aj}(P)\) | Outcome-success conditional mean with the null-arm convention | gap; setup |
| \(P_{XA}\) | \(P_{XA}\) | Treatment–covariate marginal represented by its cell-probability table | gap; setup |
| \(\mathcal M_{d,\epsilon}\) | \(\mathcal M_{d,\epsilon}\) | Observable laws satisfying the public overlap restriction | def:model |
| \(\tau(P)\) | \(\tau(P)\) | Covariate-weighted contrast of the two outcome regressions | def:target |
| \(\mathcal D\) | \(\mathcal D\) | Complete and auxiliary records forming the two-channel data | gap; setup |
| \(\mathcal L\) | \(\mathcal L\) | Complete-record component of the observed data | gap; setup |
| \(U\) | \(U\) | Independent uniform randomization seed | gap; setup |
| \(\mathrm{Uniform}[0,1]\) | \(\mathrm{Uniform}[0,1]\) | Probability law of the independent seed | gap; setup |
| \(T\) | \(T\) | Original-record Borel estimation rule permitted in the minimax infimum | def:risk |
| \(R(n,m,d,\epsilon)\) | \(R(n,m,d,\epsilon)\) | Minimax squared-error risk in the two-channel experiment | def:risk |
| \(H\) | \(H\) | Extension of the observable law carrying binary potential outcomes | gap; setup |
| \(Y_0\) | \(Y_0\) | Potential outcome under control in the extension | gap; setup |
| \(Y_1\) | \(Y_1\) | Potential outcome under treatment in the extension | gap; setup |
| \(T^{\mathrm K}\) | \(T^{\mathrm K}\) | Borel estimation rule receiving complete records and the exact marginal table | gap; setup |
| \(R^{\mathrm K}(n,d,\epsilon)\) | \(R^{\mathrm K}(n,d,\epsilon)\) | Minimax squared-error risk with the exact treatment–covariate marginal supplied | def:known-risk |
| \(N\) | \(N\) | Total number of records carrying treatment–covariate information | def:rate-handle |
| \(S\) | \(S\) | Complete-record sample size multiplied by the public overlap floor | def:rate-handle |
| \(\ell\) | \(\ell\) | Regularized logarithm of the rare-arm information scale | def:rate-handle |
| \(r(n,m,d,\epsilon)\) | \(r(n,m,d,\epsilon)\) | Capped numerical rate function evaluated by the main comparison | def:rate-handle |
| \(b(n,\epsilon)\) | \(b(n,\epsilon)\) | Capped rare-label benchmark function | gap; setup |
| \(f(n,m,d)\) | \(f(n,m,d)\) | Fixed-overlap annotation benchmark function | gap; setup |
| \(\widehat\tau(\mathcal D,U)\) | \(\widehat\tau(\mathcal D,U)\) | Deterministic finite prefix-average estimator | def:estimator-handle |
| \(h_0\) | \(h_0\) | Number of complete records assigned to the outcome pool | def:estimator-handle |
| \(h_p\) | \(h_p\) | Number of complete-record projections assigned to the pilot pool | def:estimator-handle |
| \(h_f\) | \(h_f\) | Number of complete-record projections assigned to the factorial pool | def:estimator-handle |
| \(M_p\) | \(M_p\) | Total pilot-pool length after adding auxiliary records | def:estimator-handle |
| \(M_f\) | \(M_f\) | Total factorial-pool length after adding auxiliary records | def:estimator-handle |
| \(u\) | \(u\) | Outcome-prefix Poisson mean in the attaining construction | def:estimator-handle |
| \(t_p\) | \(t_p\) | Pilot-prefix Poisson mean in the attaining construction | def:estimator-handle |
| \(t\) | \(t\) | Factorial-prefix Poisson mean in the attaining construction | def:estimator-handle |
| \(L\) | \(L\) | Polynomial degree parameter chosen from the rare-arm information scale | def:estimator-handle |
| \(B\) | \(B\) | Arm-mass localization scale in the attaining construction | def:estimator-handle |
| \(k_0\) | \(k_0\) | Pilot-count threshold selecting the polynomial contribution | def:estimator-handle |
| \(T_0(x)\) | \(T_0(x)\) | Initial constant Chebyshev polynomial | def:estimator-handle |
| \(T_1(x)\) | \(T_1(x)\) | Initial linear Chebyshev polynomial | def:estimator-handle |
| \(T_{h+1}(x)\) | \(T_{h+1}(x)\) | Successive Chebyshev polynomial specified by the recurrence | def:estimator-handle |
| \(E_L(z)\) | \(E_L(z)\) | Removably extended Chebyshev residual polynomial | def:estimator-handle |
| \(G_L(z)\) | \(G_L(z)\) | Removably extended reciprocal-approximation polynomial | def:estimator-handle |
| \(g_h\) | \(g_h\) | Monomial coefficient of the reciprocal-approximation polynomial | def:estimator-handle |
| \(Z_{aj}\) | \(Z_{aj}\) | Outcome-success count in an arm-cell of an outcome prefix | def:estimator-handle |
| \(J_{aj}\) | \(J_{aj}\) | Arm-cell count in a pilot prefix | def:estimator-handle |
| \(K_{aj}\) | \(K_{aj}\) | Arm-cell count in a factorial prefix | def:estimator-handle |
| \((x)_0\) | \((x)_0\) | Zeroth falling factorial of an integer count | def:estimator-handle |
| \((x)_h\) | \((x)_h\) | Order-\(h\) falling factorial of an integer count | def:estimator-handle |
| \(\widehat G_{aj}\) | \(\widehat G_{aj}\) | Factorial-moment estimator of the localized reciprocal polynomial | def:estimator-handle |
| \(P_{aj}^{\mathrm{pol}}\) | \(P_{aj}^{\mathrm{pol}}\) | Polynomial estimate of an arm-cell contribution | def:estimator-handle |
| \(H_{aj}\) | \(H_{aj}\) | Inverse-count estimate of an arm-cell contribution | def:estimator-handle |
| \(V_{aj}\) | \(V_{aj}\) | Pilot-selected polynomial or inverse-count contribution | def:estimator-handle |
| \(F(h',h'',h''';\mathcal D)\) | \(F(h',h'',h''';\mathcal D)\) | Clipped treatment contrast for a fixed prefix triple | def:estimator-handle |
| \(\operatorname{clip}_{[-1,1]}\) | \(\operatorname{clip}_{[-1,1]}\) | Projection of a real number onto the target interval | gap; setup |
| \(T^{\mathrm B}\) | \(T^{\mathrm B}\) | Deterministic finite prefix-average inverse-count baseline | def:baseline |
| \(\mathbf v\) | \(\mathbf v\) | Arbitrary sequence of allowed public experiment indices | gap; resource section |
| \(S_k\) | \(S_k\) | Rare-arm information scale at the \(k\)-th experiment | def:phases; introduce alongside the sequence |
| \(N_k\) | \(N_k\) | Total marginal-information sample size at the \(k\)-th experiment | def:phases; introduce alongside the sequence |
| \(\ell_k\) | \(\ell_k\) | Regularized logarithm of the \(k\)-th rare-arm information scale | def:phases; introduce alongside the sequence |
| \(\mathcal C\) | \(\mathcal C\) | Experiment sequences with minimax consistency | def:phases |
| \(\mathcal O\) | \(\mathcal O\) | Experiment sequences attaining rare-label oracle order | def:phases |
| \(\mathcal I\) | \(\mathcal I\) | Experiment sequences with strict relative auxiliary improvement | def:phases |
| \(x\) | \(x\) | Normalized many-cell difficulty used to select the lower-bound construction | def:prior-handle |
| \(u\) | \(u\) | Complete-record intensity in the lower-bound construction | def:prior-handle |
| \(w\) | \(w\) | Total marginal-information intensity in the lower-bound construction | def:prior-handle |
| \(M\) | \(M\) | Sum of the two lower-bound intensities | def:prior-handle |
| \(L\) | \(L\) | Moment-matching degree in the lower-bound construction | def:prior-handle |
| \(B\) | \(B\) | Upper endpoint of the lower-bound latent interval | def:prior-handle |
| \(\alpha\) | \(\alpha\) | Reciprocal-function scale in the lower-bound construction | def:prior-handle |
| \(b_0\) | \(b_0\) | Raw baseline covariate mass determined by overlap | def:prior-handle |
| \(K_*\) | \(K_*\) | Number of rare cells used by the lower-bound priors | def:prior-handle |
| \(\sigma\) | \(\sigma\) | Finite signed moment-annihilating measure selected by approximation duality | def:prior-handle |
| \(|\sigma|\) | \(|\sigma|\) | Variation measure of the selected finite signed measure | def:prior-handle |
| \(w_*(v)\) | \(w_*(v)\) | Raw covariate mass as a function of the latent coordinate | def:prior-handle |
| \(S_1(v)\) | \(S_1(v)\) | Raw treated-arm mass as a function of the latent coordinate | def:prior-handle |
| \(S_0(v)\) | \(S_0(v)\) | Raw control-arm mass as a function of the latent coordinate | def:prior-handle |
| \(h(v)\) | \(h(v)\) | Polar sign of the signed measure at its atoms | def:prior-handle |
| \(V\) | \(V\) | Rare-cell latent coordinate under the common branch mixture | def:prior-handle |
| \(V_i\) | \(V_i\) | Latent coordinate for the \(i\)-th rare cell | def:prior-handle |
| \(\bar w\) | \(\bar w\) | Expected raw rare-cell covariate mass | def:prior-handle |
| \(p_*\) | \(p_*\) | Raw covariate mass of the reservoir cell | def:prior-handle |
| \(Q\) | \(Q\) | Total raw mass used to normalize the complete-record table | def:prior-handle |
| \(\Pi_1\) | \(\Pi_1\) | Pushforward prior with the first core outcome assignment | def:prior-handle |
| \(\Pi_0\) | \(\Pi_0\) | Pushforward prior with the opposite core outcome assignment | def:prior-handle |
| \(\operatorname{TV}(\nu,\nu')\) | \(\operatorname{TV}(\nu,\nu')\) | Total variation distance between finite probability laws | gap; testing appendix |
| \(D(\nu\Vert\nu')\) | \(D(\nu\Vert\nu')\) | Finite-law Kullback–Leibler divergence using natural logarithms | gap; testing appendix |
| \(\|\sigma\|_{\mathrm{TV}}\) | \(\|\sigma\|_{\mathrm{TV}}\) | Total mass of a finite signed measure’s variation measure | gap; approximation appendix |
| \(\operatorname{Poi}(\lambda)\) | \(\operatorname{Poi}(\lambda)\) | Poisson probability law with the stated mean | gap; upper-bound appendix |
| \(g(K)\) | \(g(K)\) | Reciprocal of a Poisson count plus one | gap; upper-bound appendix |
| \(C_0\) | \(C_0\) | Numerical constant in the inverse-count moment certificate | gap; upper-bound appendix |
| \(Z_j\) | \(Z_j\) | Independent Poisson outcome-success count for the fixed arm | gap; upper-bound appendix |
| \(K_j\) | \(K_j\) | Independent Poisson marginal count for the fixed arm | gap; upper-bound appendix |
| \(W_j\) | \(W_j\) | Independent Poisson marginal count for the opposite arm | gap; upper-bound appendix |
| \(H_j\) | \(H_j\) | Inverse-count contribution for a fixed arm and cell | gap; upper-bound appendix |
| \(\psi_a\) | \(\psi_a\) | Covariate-weighted mean outcome for the fixed arm | gap; upper-bound appendix |
| \(h_i\) | \(h_i\) | Length of the \(i\)-th ordered pool in the generic transfer argument | gap; upper-bound appendix |
| \(J_i\) | \(J_i\) | Independent Poisson prefix length for the \(i\)-th generic pool | gap; upper-bound appendix |
| \(A\) | \(A\) | Risk bound in the generic prefix-transfer argument | gap; upper-bound appendix |
| \(\vartheta\) | \(\vartheta\) | Bounded target in the generic prefix-transfer argument | gap; upper-bound appendix |
| \(C_L(z)\) | \(C_L(z)\) | Chebyshev polynomial after the affine change of variable | gap; upper-bound appendix |
| \(D\) | \(D\) | Product of factorial-pool intensity and localization scale | gap; upper-bound appendix |
| \(\widehat G\) | \(\widehat G\) | Scalar factorial-moment estimator in the polynomial certificate | gap; upper-bound appendix |
| \((K)_0\) | \((K)_0\) | Zeroth falling factorial of the scalar Poisson count | def:estimator-handle |
| \((K)_h\) | \((K)_h\) | Order-\(h\) falling factorial of the scalar Poisson count | def:estimator-handle |
| \(H_0\) | \(H_0\) | Numerical localization multiplier in the hybrid arm-risk bound | gap; upper-bound appendix |

The sequence quantities \(S_k,N_k,\ell_k\) require explicit introduction in the presentation definition accompanying `def:phases`; their formulas currently occur in the resource theorem. The distinct uses of \(A,u,L,B\) remain local to their respective contexts. Generic probability laws, approximation polynomials, polynomial arguments, summation indices, and scalar parameters introduced by local quantification retain that local scope.

# Sections

## section: Abstract

Plan the abstract around the statistical question, the two observation channels, the uniform minimax comparison, and its implications for outcome annotation. Identify binary treatment and outcomes, finite discrete adjustment cells, and a public overlap floor as the positive scope. Describe the attaining construction and the resource characterization at the level needed to understand the result. Draft this material last, after the substantive sections, using words or first-use glosses for notation.

objs: none

bib: none

home_objs: none
## section: Introduction

Organize the introduction around how complete outcomes and additional treatment–covariate records jointly determine the precision of population treatment-effect estimation as treatment arms become rare. Lead with the distinction between outcome information and marginal information, then explain the scientific value of a comparison uniform over the overlap floor and arbitrary sample ratios. Preview the main risk comparison, attainable precision, and resource implications under the stated discrete binary experiment. Include one factual sentence directing readers to the appendix verification note. Draft the introduction last.

objs: none

bib: none

home_objs: none
## section: Related work

Position the contribution first against the nearest results: the supervised unrestricted discrete model in \citet[model (3), Theorems 1--2]{ZengBalakrishnanHanKennedy2026Discrete}, the credited fixed-interior supervised matching result in \citet{InternalDiscreteATEPolynomialUpperMatch}, and the fixed-overlap two-channel comparison in \citet[Theorem 4]{CausalSmith2026Annotation}. Make the specific comparison in terms of overlap-uniform numerical constants, unequal information budgets, and the resulting resource characterizations. Give the reciprocal-polynomial antecedent in \citet[Section 3.3, Theorems 5--6]{MaZhuJiaoWainwright2022OPE} methodological credit while distinguishing supplied target weights and global action-probability floors from unknown population cell weights and conditional treatment overlap. Place the passive experiment alongside semi-supervised treatment-effect inference and the annotation-allocation results of \citet[Theorems 4.2 and 5.1 of the arXiv manuscript]{NwankwoGoldkindZhou2026Annotations}, preserving their design and nuisance conditions. Use a concise final literature paragraph to connect weak-overlap precision and discrete functional estimation to the paper’s squared-error question.

objs: none

bib: ZengBalakrishnanHanKennedy2026Discrete, InternalDiscreteATEPolynomialUpperMatch, CausalSmith2026Annotation, MaZhuJiaoWainwright2022OPE, NwankwoGoldkindZhou2026Annotations, ChakraborttyDai2024Semisupervised, ZhangChakraborttyBradic2023DecayingOverlap, Rothe2017LimitedOverlap, ArmstrongKolesar2021ATEInference, MaWang2020RobustIPW, Khan2010, Crump2009, DAmour2021, Dorn2025, Paninski2003, JiaoVenkatHanWeissman2015Functionals, WuYang2016Entropy

home_objs: none
## section: Experiment, target, and causal interpretation

Introduce the complete-record coordinates, cell probabilities, outcome regressions, and treatment–covariate marginal in one grouped presentation definition before the overlap assumption. Define the independent complete and auxiliary samples and the seed before specifying the experiment and admissible estimation rules. Establish the observable model, target, and minimax criterion, then introduce compatible potential-outcome extensions before the consistency and exchangeability assumptions. Explain the causal interpretation through \cref{lem:causal-realization}, including existence for every model law and identification under every compatible extension. Finish by defining the exact-marginal benchmark and the benchmark functions needed by the main results. Keep proof-specific counts, approximation measures, and normalization constructions in the appendix.

objs: synth_2, ass:overlap, synth_1, ass:data-product, synth_5, def:model, def:target, synth_3, def:risk, ass:consistency, ass:exchangeability, def:known-risk

bib: SplawaNeyman1990, Rubin1974, Rosenbaum1983, Imbens2004, Imbens2015

home_objs: ass:overlap, ass:data-product, def:model, def:target, def:risk, ass:consistency, ass:exchangeability, def:known-risk
## section: Minimax precision with two information budgets

Introduce the rate notation and place \cref{thm:uniform-annotation-frontier} first among the substantive results. Explain how the rare-arm outcome scale and the total marginal-information budget govern different parts of precision, with the public overlap floor appearing in both. Follow with \cref{thm:rare-label-floor} to explain the outcome-information benchmark and with \cref{prop:benchmark-recovery} to relate the comparison to fixed overlap, two cells, and exact marginal information. Distinguish the uniform order comparison from the fixed-\((n,d,\epsilon)\) experiment limit. Refer forward to the attaining algorithm and backward to the causal interpretation; reserve the technical lower-bound construction for the appendix.

objs: def:rate-handle, synth_4, def:estimator-handle, thm:uniform-annotation-frontier, thm:rare-label-floor, prop:benchmark-recovery

bib: none

home_objs: def:rate-handle, thm:uniform-annotation-frontier, thm:rare-label-floor, prop:benchmark-recovery
## section: An attaining estimator

Present the central estimator as the numbered procedure in \cref{def:estimator-handle}, preceded by intuition for the outcome, pilot, and factorial pools. Explain why arm-specific localization combines polynomial correction in sparse cells with inverse-count estimation in more populated cells. Keep the complete frozen procedure in the main body, including its tuning, clipping, finite averaging, and treatment of overflow. Present the simpler procedure in \cref{def:baseline} together with \cref{thm:uniform-baseline} as a transparent comparison that motivates the polynomial correction. Direct readers to the appendix for the moment bounds and transfer argument supporting original-record attainment.

objs: def:baseline, thm:uniform-baseline

bib: Horvitz1952, JiaoVenkatHanWeissman2015Functionals, MaZhuJiaoWainwright2022OPE

home_objs: def:estimator-handle, def:baseline, thm:uniform-baseline
## section: Consistency and the value of auxiliary records

Introduce the domain of arbitrary experiment sequences and the phase definitions immediately before \cref{thm:annotation-resource-phases}. Organize interpretation around three practical questions: the budgets supporting consistency, the marginal budget attaining rare-label oracle order, and the sequences supporting strict relative improvement from auxiliary records. Use the theorem’s saturation and order-plateau conditions to organize a compact resource table or schematic. Discuss the supervised slice within the same interpretation and preserve the exact logarithmic dependence and capped benchmark. Define every displayed shorthand before its use.

objs: synth_8, def:phases, thm:annotation-resource-phases

bib: none

home_objs: def:phases, thm:annotation-resource-phases
## section: Discussion and limitations

Interpret the paper’s own results as a population benchmark for passive outcome annotation from a common distribution. Connect the marginal-budget plateau and the exact-marginal experiment to the distinction between observing treatment–covariate frequencies and observing rare-arm outcomes. Place genuine scope boundaries in an explicitly titled “Limitations and future work” subsection: computationally practical tuning, adaptive allocation, interval estimation, policy objectives, empirical overlap, and extensions beyond the binary finite-alphabet experiment. Keep the exact-marginal limit attached to its fixed-parameter conditions. Where annotation planning needs context, cite the allocation work already introduced in related work.

objs: none

bib: NwankwoGoldkindZhou2026Annotations

home_objs: none
## section: Appendix: Causal interpretation and benchmark proofs

Prove the compatible-extension statement and the identifying equality in \cref{lem:causal-realization}, distinguishing the existence witness from identification for every compatible extension. Supply the proofs of the two-cell and exact-marginal comparisons and the fixed-parameter experiment limit in \cref{prop:benchmark-recovery}. Resolve any benchmark-proof notation immediately before its first use. Keep identification assumptions tied to the extension and the observable class tied to the public overlap restriction.

objs: synth_7, lem:causal-realization

bib: Rosenbaum1983, Imbens2015

home_objs: lem:causal-realization
## section: Appendix: Estimator risk bounds

Introduce grouped appendix definitions for the independent Poisson counts, inverse-count contributions, generic prefix-transfer experiment, and scalar polynomial certificate before their first uses. Present the inverse-count moment and arm-risk calculations, the finite-prefix transfer, and the Chebyshev factorial certificate in the order needed for the baseline and attaining-estimator proofs. Use \cref{lem:uniform-hybrid-arm-risk} to assemble the localized arm bound and complete the upper-bound proof in the original finite experiment. Explain the roles of localization, count moments, and finite averaging without incorporating verification machinery into the mathematical exposition.

objs: lem:poisson-inverse-moments, lem:inverse-count-arm-risk, lem:finite-prefix-transfer, lem:chebyshev-factorial-certificate, lem:uniform-hybrid-arm-risk

bib: JiaoVenkatHanWeissman2015Functionals, MaZhuJiaoWainwright2022OPE

home_objs: lem:poisson-inverse-moments, lem:inverse-count-arm-risk, lem:finite-prefix-transfer, lem:chebyshev-factorial-certificate, lem:uniform-hybrid-arm-risk
## section: Appendix: Testing and approximation lower bounds

Define the finite testing quantities and signed-measure norm before the auxiliary inequalities. Present \cref{lem:pinsker-finite,lem:markov-polynomial,lem:finite-polynomial-duality}, then establish the shrinking-cone approximation certificate. Place the numbered prior construction in \cref{def:prior-handle} after that certificate and before \cref{lem:normalized-affine-testing}. Explain the common marginal distribution, reservoir normalization, target separation, and joint observation comparison within their proved conditions. Complete the rare-label and many-cell lower-bound arguments and combine them for the main comparison. Treat the same distribution of normalized marginals as a property of the two priors, preserving the distinction between a shared prior marginal distribution and an identical marginal table at every draw.

objs: lem:pinsker-finite, lem:markov-polynomial, lem:finite-polynomial-duality, lem:shrinking-cone-dual, synth_9, synth_6, def:prior-handle, lem:normalized-affine-testing

bib: WuYang2016Entropy, MaZhuJiaoWainwright2022OPE, Pierzchala2016Polynomial

home_objs: lem:pinsker-finite, lem:markov-polynomial, lem:finite-polynomial-duality, lem:shrinking-cone-dual, def:prior-handle, lem:normalized-affine-testing
## section: Appendix: Resource characterizations and verification note

Derive the consistency, oracle-order, strict-improvement, saturation, and plateau conclusions from the uniform risk comparison, preserving the quantification over arbitrary allowed sequences. End the appendix with a brief verification note that consolidates the Lean machine-checking scope for the frozen results, the model and extension assumptions, and any theorem-local cited dependencies identified by generated verification-scope disclosures. Report the checked mathematical scope and assumed inputs from the verification metadata; keep declaration names and other proof-engineering details confined to this note.

objs: none

bib: none
home_objs: none
