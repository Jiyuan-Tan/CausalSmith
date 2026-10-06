# Title
**Uniform estimation and honest inference in regression discontinuity with a mismeasured score**

**Contribution statement.** Under recorded assignment by the latent cutoff, known Gaussian measurement error, known bounded latent support, a continuous bounded score density, and full-domain Hölder restrictions on binary potential-outcome means, the paper characterizes and attains matching minimax absolute-risk and \(90\%\)-honest connected-interval expected-length rates uniformly over every sample size and noise scale in the stated ranges.

# Notation

The table plans definitions for reader-facing notation. An unresolved home requires an anchored presentation definition immediately before first use. Rows sharing a missing home should be grouped by object family. Existing environment arguments remain unchanged.

notation_gaps: \(P\)=ambient latent law and coordinates require an anchored definition; \(X,Y^0,Y^1,\varepsilon\)=latent coordinates require an anchored definition; \(D,Y,W,P_{\mathrm{obs}}\)=observation map and induced law require an anchored definition; \(f(P,x),\mu_d(P,x)\)=density and continuous conditional-mean versions require an anchored definition; \(\theta(P)\)=causal target requires an anchored definition; \([\mu_d(P,\cdot)]_\beta\)=Hölder seminorm requires an anchored definition; \(S_n,U,\mathbb P_{P,n}\)=sample and randomized experiment require an anchored definition; \(R_\beta(n,\sigma),\mathcal L_\beta(n,\sigma)\)=benchmark decision criteria require anchored definitions of their decision classes and objectives; \(T_L\)=Chebyshev normalization requires an anchored definition; \(m_L\)=polynomial degree requires an anchored definition; \(s_d\)=arm-reflection convention requires an anchored definition; \(M_{L,\beta},V_L(\sigma)\)=bias moment and second-moment bound require anchored definitions; \(A_{d,L}(P),B_{d,L}(P)\)=population weighted averages require anchored definitions; \(\widehat\theta_L,\rho_L,I_L\)=effect estimate and interval construction require anchored definitions including index-zero values; \(L_{\max}\)=finite degree cap requires an anchored definition; \(g_m,N_m,\kappa\)=cancellation polynomial and normalization constants require anchored definitions; \(q_\sigma(w),u_{b,m,\sigma}(w),\lambda_{b,\sigma}\)=likelihood-comparison quantities require anchored definitions; \(v_h^{\mathrm{dir}}(x)\)=direct witness profile requires an anchored definition; \(\chi^2,\operatorname{TV}\)=probability-distance conventions require an anchored definition; \(P_j^{\mathrm{Leg}}(t),R_j(t)\)=normalized and shifted Legendre polynomials require anchored definitions; \(H_j(z)\)=probabilists' Hermite polynomials require an anchored definition; \(\mathcal G(\sigma),Q,Z,V^0,V^1,E,a,v_d(z),A,B,R,\vartheta(Q),\mathcal R_{\mathcal G}(n,\sigma),\mathcal L_{\mathcal G}(n,\sigma)\)=larger-class notation is introduced inside a theorem and requires an anchored presentation definition before its use.

env_overrides: def:ratio=algorithmv, def:public-selection=algorithmv, def:frontier-handle=remarkv, prop:published-class-converse-transfer=propositionv, thm:uniform-frontier-resolution=propositionv

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(P\) | \(P\) | Ambient latent probability law | Gap: latent experiment family |
| \(X\) | \(X\) | Latent running variable | Gap: latent experiment family |
| \(Y^0\) | \(Y^0\) | Binary untreated potential outcome | Gap: latent experiment family |
| \(Y^1\) | \(Y^1\) | Binary treated potential outcome | Gap: latent experiment family |
| \(\varepsilon\) | \(\varepsilon\) | Standardized measurement error | Gap: latent experiment family |
| \(f(P,x)\) | \(f(P,x)\) | Continuous latent-score density under the law | Gap: latent experiment family |
| \(\mu_d(P,x)\) | \(\mu_d(P,x)\) | Continuous conditional potential-outcome mean | Gap: latent experiment family |
| \([\mu_d(P,\cdot)]_\beta\) | \([\mu_d(P,\cdot)]_\beta\) | Hölder seminorm on the full latent interval | Gap: smoothness family |
| \(\mathcal M_\beta(\sigma)\) | \(\mathcal M_\beta(\sigma)\) | Benchmark class with the displayed law restrictions | `def:model` |
| \(W\) | \(W\) | Gaussian-contaminated observed running variable | Gap: observation family |
| \(D\) | \(D\) | Recorded indicator of the latent cutoff side | Gap: observation family |
| \(Y\) | \(Y\) | Observed outcome selected by treatment assignment | Gap: observation family |
| \(P_{\mathrm{obs}}\) | \(P_{\mathrm{obs}}\) | Law induced by the observed triple | Gap: observation family |
| \(\theta(P)\) | \(\theta(P)\) | Difference between potential-outcome means at the cutoff | Gap: target family |
| \(S_n\) | \(S_n\) | Independent observed sample of size \(n\) | Gap: decision experiment family |
| \(U\) | \(U\) | Independent uniform procedure seed | Gap: decision experiment family |
| \(\mathbb P_{P,n}\) | \(\mathbb P_{P,n}\) | Joint probability law of sample and procedure seed | Gap: decision experiment family |
| \(\mathcal I_{\beta,n,\sigma}\) | \(\mathcal I_{\beta,n,\sigma}\) | Measurable connected closed intervals with uniform \(0.9\) coverage | `def:honest-class` |
| \(\ell\) | \(\ell\) | Locally bound lower interval endpoint | `def:honest-class` |
| \(\upsilon\) | \(\upsilon\) | Locally bound upper interval endpoint | `def:honest-class` |
| \(R_\beta(n,\sigma)\) | \(R_\beta(n,\sigma)\) | Minimax absolute estimation risk on the benchmark class | Gap: decision criteria family |
| \(\mathcal L_\beta(n,\sigma)\) | \(\mathcal L_\beta(n,\sigma)\) | Minimax worst expected length of honest connected intervals | Gap: decision criteria family |
| \(T_L\) | \(T_L\) | Chebyshev polynomial with the required normalization | Gap: endpoint polynomial family |
| \(K_L(x)\) | \(K_L(x)\) | Normalized endpoint polynomial weight with continuous removable values | `def:endpoint-kernel` |
| \(m_L\) | \(m_L\) | Degree of the endpoint polynomial | Gap: endpoint polynomial family |
| \(K_L^{(2k)}(w)\) | \(K_L^{(2k)}(w)\) | Even-order derivative evaluated at the observed-score argument | `def:endpoint-kernel` |
| \(K_L^{(j)}(x)\) | \(K_L^{(j)}(x)\) | Order-\(j\) derivative evaluated at the latent-score argument | `def:endpoint-kernel` |
| \(Q_{L,\sigma}(w)\) | \(Q_{L,\sigma}(w)\) | Finite inverse-heat transform of the endpoint polynomial | `def:inverse-heat` |
| \(s_d\) | \(s_d\) | Sign reflecting each treatment arm onto the positive latent interval | Gap: arm averages family |
| \(\widehat A_{d,L}\) | \(\widehat A_{d,L}\) | Outcome-marked empirical inverse-heat average | `def:ratio` |
| \(\widehat B_{d,L}\) | \(\widehat B_{d,L}\) | Unmarked empirical inverse-heat average | `def:ratio` |
| \(\widehat\mu_{d,L}\) | \(\widehat\mu_{d,L}\) | Projected arm ratio with a denominator floor | `def:ratio` |
| \(\Pi_{[1/4,3/4]}\) | \(\Pi_{[1/4,3/4]}\) | Ordinary projection onto the displayed outcome-mean interval | `def:ratio` |
| \(A_{d,L}(P)\) | \(A_{d,L}(P)\) | Population counterpart of the marked average | Gap: arm averages family |
| \(B_{d,L}(P)\) | \(B_{d,L}(P)\) | Population counterpart of the unmarked average | Gap: arm averages family |
| \(M_{L,\beta}\) | \(M_{L,\beta}\) | Endpoint moment controlling Hölder approximation bias | Gap: certificate family |
| \(V_L(\sigma)\) | \(V_L(\sigma)\) | Integrated derivative expression bounding Gaussian second moments | Gap: certificate family |
| \(\widehat\theta_L\) | \(\widehat\theta_L\) | Effect estimate assembled from the two arm estimates | Gap: certificate family |
| \(\rho_L\) | \(\rho_L\) | Public radius used for estimation and interval guarantees | Gap: certificate family |
| \(I_L\) | \(I_L\) | Connected interval assembled from the estimate and public radius | Gap: certificate family |
| \(L_{\max}\) | \(L_{\max}\) | Public upper limit of the candidate index set | Gap: selection family |
| \(L_\star\) | \(L_\star\) | Smallest minimizer of the public radius over the finite candidate set | `def:public-selection` |
| \(E_\beta(n,\sigma)\) | \(E_\beta(n,\sigma)\) | Public radius evaluated at the selected index | `def:public-selection` |
| \(\widehat\theta_{L_\star}\) | \(\widehat\theta_{L_\star}\) | Selected effect estimate | `def:public-selection` |
| \(I_{L_\star}\) | \(I_{L_\star}\) | Selected honest connected interval | `def:public-selection` |
| \(\nu\) | \(\nu\) | Local abbreviation for \(2\beta+1\) | `def:uniform-rate` |
| \(h_0\) | \(h_0\) | Direct-experiment resolution \(n^{-1/\nu}\) | `def:uniform-rate` |
| \(\Psi(h,\sigma)\) | \(\Psi(h,\sigma)\) | Piecewise noise cost as a function of resolution and noise scale | `def:uniform-rate` |
| \(h_\star(n,\sigma)\) | \(h_\star(n,\sigma)\) | Root of the displayed balance equation on the direct-to-unit interval | `def:uniform-rate` |
| \(r_\beta(n,\sigma)\) | \(r_\beta(n,\sigma)\) | Hölder power of the balance-equation resolution | `def:uniform-rate` |
| \(\widetilde\theta_{\beta,n,\sigma}\) | \(\widetilde\theta_{\beta,n,\sigma}\) | Selected observable effect estimator | `def:uniform-rate` |
| \(\widetilde I_{\beta,n,\sigma}\) | \(\widetilde I_{\beta,n,\sigma}\) | Selected observable honest connected interval | `def:uniform-rate` |
| \(z\) | \(z\) | Locally bound intermediate-branch scalar solving the displayed equation | `def:uniform-rate`; local binding in `thm:uniform-frontier` |
| \(\tau\) | \(\tau\) | Locally bound compact-branch scalar solving the displayed equation | `def:uniform-rate`; local binding in `thm:uniform-frontier` |
| \(g_m(x/b)\) | \(g_m(x/b)\) | Rescaled cancellation polynomial used in the witness extension | Gap: cancellation family |
| \(g_m(t)\) | \(g_m(t)\) | Cancellation polynomial on the unit interval | Gap: cancellation family |
| \(g_m^{(1)}\) | \(g_m^{(1)}\) | First derivative of the cancellation polynomial | Gap: cancellation family |
| \(N_m\) | \(N_m\) | Normalization entering the cancellation bounds | Gap: cancellation family |
| \(v_{b,m}(x)\) | \(v_{b,m}(x)\) | Piecewise full-interval extension of the rescaled cancellation polynomial | `def:legal-extension` |
| \([v_{b,m}]_\beta\) | \([v_{b,m}]_\beta\) | Full-interval Hölder seminorm of the witness extension | `def:legal-extension`; seminorm convention in smoothness gap |
| \(\kappa\) | \(\kappa\) | Fixed witness-amplitude constant | Gap: cancellation family |
| \(P^{\pm}_{b,m}\) | \(P^{\pm}_{b,m}\) | Uniform-score Bernoulli-marked latent alternative laws | `def:alternatives` |
| \(P^+_{b,m}\) | \(P^+_{b,m}\) | Positive-sign member of the alternative pair | `def:alternatives` |
| \(P^-_{b,m}\) | \(P^-_{b,m}\) | Negative-sign member of the alternative pair | `def:alternatives` |
| \((P^+_{b,m})_{\mathrm{obs}}\) | \((P^+_{b,m})_{\mathrm{obs}}\) | Observed law induced by the positive latent alternative | `def:alternatives`; observation map in observation gap |
| \((P^-_{b,m})_{\mathrm{obs}}\) | \((P^-_{b,m})_{\mathrm{obs}}\) | Observed law induced by the negative latent alternative | `def:alternatives`; observation map in observation gap |
| \(b_m(\sigma)\) | \(b_m(\sigma)\) | Noise-dependent witness support scale capped at one | `def:noise-support` |
| \(h_m(\sigma)\) | \(h_m(\sigma)\) | Witness endpoint resolution obtained from support and polynomial order | `def:noise-support` |
| \(P^{\pm}_{b_m(\sigma),m}\) | \(P^{\pm}_{b_m(\sigma),m}\) | Alternative pair at the noise-dependent support scale | `def:noise-support` |
| \(v_h^{\mathrm{dir}}(x)\) | \(v_h^{\mathrm{dir}}(x)\) | Direct-experiment witness profile | Gap: direct alternatives family |
| \(P_h^{\mathrm{dir},\pm}\) | \(P_h^{\mathrm{dir},\pm}\) | Uniform-score Bernoulli latent alternatives using the direct profile | `def:direct-alternatives` |
| \(\mu_0(P_h^{\mathrm{dir},\pm},x)\) | \(\mu_0(P_h^{\mathrm{dir},\pm},x)\) | Untreated conditional mean in the direct alternatives | `def:direct-alternatives` |
| \(\mu_1(P_h^{\mathrm{dir},\pm},x)\) | \(\mu_1(P_h^{\mathrm{dir},\pm},x)\) | Treated conditional mean in the direct alternatives | `def:direct-alternatives` |
| \(q_\sigma(w)\) | \(q_\sigma(w)\) | Reference convolution quantity in the marked-likelihood denominator | Gap: likelihood comparison family |
| \(u_{b,m,\sigma}(w)\) | \(u_{b,m,\sigma}(w)\) | Convolved witness quantity in the marked-likelihood numerator | Gap: likelihood comparison family |
| \(\lambda_{b,\sigma}\) | \(\lambda_{b,\sigma}\) | Scalar governing the factorial likelihood tail | Gap: likelihood comparison family |
| \(\chi^2\) | \(\chi^2\) | Chi-squared divergence between probability laws | Gap: probability distances family |
| \(\operatorname{TV}\) | \(\operatorname{TV}\) | Total variation distance between probability laws | Gap: probability distances family |
| \(P_j^{\mathrm{Leg}}(t)\) | \(P_j^{\mathrm{Leg}}(t)\) | Normalized degree-\(j\) Legendre polynomial | Gap: classical polynomial family |
| \(P_k^{\mathrm{Leg}}(t)\) | \(P_k^{\mathrm{Leg}}(t)\) | Normalized degree-\(k\) member of the same Legendre family | Gap: classical polynomial family |
| \(R_j(t)\) | \(R_j(t)\) | Legendre polynomial shifted to the unit interval | Gap: classical polynomial family |
| \(R_k(t)\) | \(R_k(t)\) | Degree-\(k\) member of the shifted Legendre family | Gap: classical polynomial family |
| \(R_j'(t)\) | \(R_j'(t)\) | Derivative of the shifted Legendre polynomial | Gap: classical polynomial family |
| \(H_j(z)\) | \(H_j(z)\) | Probabilists' Hermite polynomial defined by the displayed generating function | Gap: classical polynomial family |
| \(H_j(Z)\) | \(H_j(Z)\) | Hermite polynomial evaluated at a locally bound standard Gaussian variable | Gap: classical polynomial family |
| \(H_k(Z)\) | \(H_k(Z)\) | Degree-\(k\) Hermite polynomial evaluated at that Gaussian variable | Gap: classical polynomial family |
| \(H_0\) | \(H_0\) | Constant member of the probabilists' Hermite family | Gap: classical polynomial family |
| \(\mathcal G(\sigma)\) | \(\mathcal G(\sigma)\) | Larger Gaussian observed-treatment class defined by local density and mean conditions | Gap: larger-class family |
| \(Q\) | \(Q\) | Latent probability law in the larger class | Gap: larger-class family |
| \(Z\) | \(Z\) | Latent score coordinate in the larger class; separately a locally bound Gaussian variable in the Hermite result | Gap: larger-class family; local Gaussian binding in `lem:classical-hermite-facts` |
| \(V^0\) | \(V^0\) | Untreated binary potential outcome in the larger class | Gap: larger-class family |
| \(V^1\) | \(V^1\) | Treated binary potential outcome in the larger class | Gap: larger-class family |
| \(E\) | \(E\) | Standard Gaussian error coordinate in the larger class | Gap: larger-class family |
| \(a\) | \(a\) | Larger-class score density continuous and positive near zero | Gap: larger-class family |
| \(v_d(z)\) | \(v_d(z)\) | Continuous conditional potential-outcome mean near zero in the larger class | Gap: larger-class family |
| \(A\) | \(A\) | Indicator of the larger-class latent cutoff side | Gap: larger-class family |
| \(B\) | \(B\) | Observed outcome selected by larger-class assignment | Gap: larger-class family |
| \(R\) | \(R\) | Gaussian-contaminated observed score in the larger class | Gap: larger-class family |
| \(\vartheta(Q)\) | \(\vartheta(Q)\) | Larger-class cutoff treatment contrast | Gap: larger-class family |
| \(\mathcal R_{\mathcal G}(n,\sigma)\) | \(\mathcal R_{\mathcal G}(n,\sigma)\) | Larger-class minimax absolute estimation risk | Gap: larger-class family |
| \(\mathcal L_{\mathcal G}(n,\sigma)\) | \(\mathcal L_{\mathcal G}(n,\sigma)\) | Larger-class minimax worst expected honest connected-interval length | Gap: larger-class family |

Standard mathematical operators, dummy integration variables, generic polynomial arguments, derivative orders, and locally quantified constants retain their usual meanings. Local witness parameters retain the exact argument conventions displayed in their anchored definitions.

# Sections

## section: Introduction

Plan the abstract and introduction for drafting after the body. Lead with the precision of a causal cutoff contrast when an administrative treatment record reveals the latent cutoff side and the running variable is observed with Gaussian error. Present the joint characterization of estimation risk and honest interval length, the observable attaining procedure, and the connection among direct, intermediate, and compact-support regimes. State known noise calibration, bounded latent support, continuous bounded density, and full-domain outcome-mean restrictions as the contribution's affirmative domain. Use words or first-use glosses for symbols preceding their definitions. Include one factual sentence pointing to the appendix verification note. Keep the proof constructions and verification inventory in the appendix.

objs: none
bib: Hahn2001, CattaneoTitiunik2022Survey, PeiShen2017DevilTails

home_objs: none
## section: Related work

Organize positioning around three decision-problem comparisons. First, compare the observed-treatment identification result of \citet[Assumptions 1Y, 2C, and 7; Proposition 4(b)]{PeiShen2017DevilTails} and Dong's Chapter 2 observed-treatment local-linear inference result under Assumptions 8, 9, 11, and 13 and Theorem 6 with the present benchmark's minimax absolute risk and finite-sample honest expected length. Resolve Dong's bibliography entry before drafting a citation: the supplied source has no key in the permitted pool. Second, compare \citet[Theorem 1(a), fixed-support case]{Meister2007CompactSupport}, boundary deconvolution density estimation, and Gaussian denoised moments through their targets, losses, support information, and error assumptions. Third, compare shrinking-noise density estimation and \citet[Section 2, Theorems 2.4–2.6]{DurotMukherjee2026VanishingNoise} with the present endpoint criterion and uniform noise-scale analysis. Locate honest inference within the optimal-recovery and smoothness-based regression literature. Explain the assignment and target distinctions for noisy-score assignment, auxiliary-data fuzzy designs, and observed-score interpretations. Preserve each supplied theorem locator and source boundary; use theorem-level comparisons supported by the verified evidence.

objs: none
bib: PeiShen2017DevilTails, DaveziesLeBarbanchon2017ContinuousError, Meister2007CompactSupport, ZhangKarunamuni2009Boundary, WuYang2020DenoisedMoments, HallQiu2005DiscreteTransform, Delaigle2008ShrinkingNoise, DurotMukherjee2026VanishingNoise, ArmstrongKolesar2018OptimalInference, ArmstrongKolesar2020SimpleHonest, Donoho1994, Low1997, Kamat2018, Gao2018, Tuvaandorj2020, Fan1993, Delaigle2009, DongKolesar2023IgnoreMeasurementError, Eckles2025, KatoSasaki2018DeconvolutionBands, KatoSasaki2019EIVBands, CattaneoTitiunik2022Survey

home_objs: none
## section: Experiment, assumptions, and decision criteria

Introduce the latent law, recorded true-side assignment, observed outcome and score, causal cutoff target, and independent randomized sampling experiment before their first formal use. Place grouped presentation definitions for the latent and observation families before the assumptions. Present the five law restrictions and the exact benchmark class, distinguishing density continuity and global bounds from the full-domain Hölder restriction on potential-outcome means. Define the unrestricted measurable estimator decision class and minimax absolute-risk objective, then introduce the honest connected-interval class and its minimax worst expected-length objective. Explain known calibration, known support, and fixed public smoothness as inputs to the benchmark. Keep witness constructions and probability-distance machinery in the appendix.

objs: ass:gaussian, ass:error-independence, synth_2, synth_1, ass:density-bounds, ass:mean-bounds, synth_3, ass:mean-holder, def:model, def:honest-class
bib: Hahn2001, Tsybakov2009, ArmstrongKolesar2020SimpleHonest

home_objs: ass:gaussian, ass:error-independence, ass:density-bounds, ass:mean-bounds, ass:mean-holder, def:model, def:honest-class
## section: Observable estimation and finite-sample inference

Present the central procedure before the rate theorem. Introduce the normalized endpoint polynomial and its finite inverse-heat transform, then show how the observed assignment partitions the sample into reflected arm averages. Place the arm-sign and population-average presentation definitions before the ratio algorithm. Place the effect estimate, public radius, interval, fallback values, and candidate cap in grouped presentation definitions before public selection. Explain the procedure through positive latent endpoint averaging, observable Gaussian correction, denominator stabilization, and deterministic selection using public inputs. Place \cref{thm:finite-certificate} after the complete procedure so the reader can resolve every output and certificate. Reserve polynomial inequalities and covariance calculations for the appendix.

objs: synth_4, def:endpoint-kernel, def:inverse-heat, synth_5, def:ratio, synth_6, def:public-selection, thm:finite-certificate
bib: Fan1993, Delaigle2009, WuYang2020DenoisedMoments, ArmstrongKolesar2020SimpleHonest

home_objs: def:endpoint-kernel, def:inverse-heat, def:ratio, def:public-selection, thm:finite-certificate
## section: Uniform minimax rates across noise scales

Introduce the noise cost and scalar balance equation through \cref{def:uniform-rate}, then present \cref{thm:uniform-frontier} as the single central characterization of both decision criteria. Plan an accompanying regime table or schematic organized by the exact branch conditions, with both interface equalities and constants uniform in sample size and noise scale. Interpret the direct regime, the intermediate endpoint resolution, and the compact-support regime through the balance between approximation bias and Gaussian inversion cost. Refer concisely to the direct-experiment specialization in the verification appendix. Use the proved polynomially shrinking-noise sequences, fixed-positive-noise order, and specified Lipschitz example to clarify how the uniform characterization serves different asymptotic paths. Keep the distinction between rate comparison and exact constants explicit.

objs: def:uniform-rate, thm:uniform-frontier
bib: Tsybakov2009

home_objs: def:uniform-rate, thm:uniform-frontier
## section: Interpretation and extensions

Interpret the paper's own results through the information supplied by recorded latent-side assignment, bounded support, and known Gaussian calibration. Introduce the larger-class presentation definition immediately before \cref{prop:published-class-converse-transfer}, and explain its embedding-based lower-bound implication with the benchmark as the domain of the matched attaining procedures. Plan a prospective eligibility-effect benchmark motivated by Dong's Chapter 2, Section 2.6 setting, with administrative assignment linkage, externally justified Gaussian calibration, bounded latent range, and maintained global density and outcome-mean restrictions stated as the proposed design conditions. Add a clearly titled “Limitations and future work” subsection for estimated calibration, adaptation to unknown smoothness, empirical membership assessment, additional outcome models, and the incomplete boundary-deconvolution and priority comparison. Resolve the unavailable Dong citation key before drafting source-dependent application prose.

objs: prop:published-class-converse-transfer
bib: PeiShen2017DevilTails

home_objs: prop:published-class-converse-transfer
## section: Appendix: Polynomial construction and the finite-sample certificate

Give the achievability proofs in reader-facing mathematical order. Introduce the anchored Hermite presentation definition before the classical Gaussian identity, and develop endpoint positivity and concentration, the factorial derivative inequality, and exact inverse-heat second moments before proving \cref{thm:finite-certificate}. Explain how the density bounds and potential-mean smoothness enter different steps of the ratio argument. Verify interval coverage, the stabilized denominator, the finite public selection, and the fallback within the declared experiment. Keep any representation records or execution details in the final verification note.

objs: lem:classical-hermite-facts, lem:positive-endpoint, lem:factorial-derivatives, lem:exact-covariance
bib: WuYang2020DenoisedMoments, ArmstrongKolesar2020SimpleHonest

home_objs: lem:classical-hermite-facts, lem:positive-endpoint, lem:factorial-derivatives, lem:exact-covariance
## section: Appendix: Lower bounds for the observed experiment

Introduce the anchored Legendre presentation definition before its classical identities and shifted derivative formula. Display the cancellation polynomial, normalization, and amplitude together with the full-interval extension before the Bernoulli alternative laws, then state their legality and separation properties. Introduce the likelihood quantities and probability-distance conventions before the marked-law comparison and two-point transfer. Place the direct witness profile immediately before the direct alternative laws and use them for the direct lower-bound argument. Introduce the noise-dependent support rule before its first use in the noisy lower bound. Organize the proofs around full observed-law indistinguishability, target separation, honest-length transfer, and arbitrary independent procedure randomization.

objs: lem:classical-legendre-facts, lem:shifted-legendre-derivative, def:legal-extension, def:alternatives, lem:legal-cancellation, lem:full-marked-likelihood, lem:two-point-transfer, synth_7, def:direct-alternatives, def:noise-support
bib: Tsybakov2009, Low1997, Meister2007CompactSupport

home_objs: lem:classical-legendre-facts, lem:shifted-legendre-derivative, def:legal-extension, def:alternatives, lem:legal-cancellation, lem:full-marked-likelihood, lem:two-point-transfer, def:direct-alternatives, def:noise-support
## section: Appendix: Rate comparison, branch formulas, and verification scope

Prove the noise-cost scaling properties, the variance envelope, and the cancellation-information envelope before assembling the uniform upper and lower comparisons. Handle the finite degree cap, integer choices, low-degree cases, zero noise, and both interfaces in the proof of \cref{thm:uniform-frontier}. Derive the scalar branch equations and sequence specializations, then prove the larger-class embedding and converse transfer. Place the direct-experiment specialization, the interpretive precision-handle object, and the consolidated resolution proposition after these arguments. Make clear that Lean definitions are total on their ambient types while statistical guarantees use their stated admissible sample, noise, and positive-index domains. End with a brief verification note identifying the machine-checked statements, maintained model assumptions, and theorem-local cited dependencies from the supplied verification metadata; consolidate representation and proof-engineering information there.

objs: lem:noise-cost-scaling, lem:variance-cost-envelope, lem:cancellation-information-envelope, thm:direct-reduction, def:frontier-handle, thm:uniform-frontier-resolution
bib: Tsybakov2009, PeiShen2017DevilTails
home_objs: lem:noise-cost-scaling, lem:variance-cost-envelope, lem:cancellation-information-envelope, thm:direct-reduction, def:frontier-handle, thm:uniform-frontier-resolution
