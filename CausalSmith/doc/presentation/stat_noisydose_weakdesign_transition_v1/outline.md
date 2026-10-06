# Title
**Pointwise causal estimation with weak dose support and Gaussian measurement error**

**Contribution statement.** For a prespecified latent dose in a two-stratum, conditionally exchangeable model with bounded potential outcomes, compact dose support, fixed Hölder smoothness and polynomial design decay, the paper establishes matching minimax absolute-error and honest connected-interval-length orders uniformly over known Gaussian error scales, with an observable estimator and finite-sample coverage (1-\alpha) for every noncoverage level \(\alpha\in(0,1)\).

env_overrides: def:total-estimator=algorithmv, prop:identification=propositionv, prop:error-free-reduction=propositionv

notation_gaps: \(\mathcal X\)=the two-stratum domain needs an anchored setup definition, \(P\)=the structural law and its coordinate spaces need an anchored setup definition, \(X\)=the observed stratum coordinate needs an anchored setup definition, \(A\)=the latent dose coordinate needs an anchored setup definition, \(Z\)=the standardized measurement-error coordinate needs an anchored setup definition, \(Y\)=the realized outcome coordinate needs an anchored setup definition, \(W\)=the contaminated-dose coordinate needs an anchored setup definition, \(O_1,\ldots,O_n\)=the observed-record coordinates need an anchored definition before the observed experiment, \(p_x\)=the stratum probability needs an anchored definition, \(a_0\)=the evaluation dose needs an anchored definition, \(t\)=the centered latent-dose argument needs an anchored definition, \(V\)=the centered observed dose needs an anchored definition, \(g_x(t)\)=the conditional centered-dose density needs an anchored definition, \(\theta(P)\)=the causal evaluation functional needs an anchored definition, \(\alpha\)=the fixed honesty level needs an anchored definition, \(\mathcal H^\beta([0,1])\)=the increment-seminorm class needs an anchored definition preserving the separate mean-range restriction, \([\mu_x]_\beta\)=the increment seminorm needs an anchored definition, \(q\)=the public nonnegative latent weight needs an anchored definition, \(\ell_q\)=the exact Gaussian inverse weight needs an anchored definition, \(I_\kappa(q)\)=the weighted moment needs an anchored formula, \(b_q\)=the public denominator certificate needs an anchored formula, \(B_q\)=the public bias certificate needs an anchored formula, \(V_q\)=the public second-moment certificate needs an anchored formula, \(A_q\)=the public expected-error score needs an anchored definition before dictionary selection, \(m_{x,q}\)=the localized population ratio needs an anchored definition, \(q_h^{\mathrm F}\)=the Fourier weight family needs an anchored formula, \(\ell_h^{\mathrm F}\)=the Fourier inverse family needs an anchored formula, \(q_m^{\mathrm M}\)=the polynomial weight family needs an anchored formula, \(\ell_m^{\mathrm M}\)=the polynomial inverse family needs an anchored formula, \(\widehat p_x\)=the split stratum-frequency formula is referenced but undeclared in the frozen definitions, \(\widehat D_x(q)\)=the split denominator formula is referenced but undeclared in the frozen definitions, \(\widehat M_x(q)\)=the split numerator formula is referenced but undeclared in the frozen definitions, \(\widehat\mu_x(q)\)=the clipping and denominator-handling formula is referenced but undeclared in the frozen definitions, \(\widehat\theta_q\)=the weight-indexed output formula is referenced but undeclared in the frozen definitions, \(\Phi_\sigma\)=the Gaussian convolution measure needs an anchored definition, \(\Phi_0\)=the zero-scale convolution measure needs an anchored definition, \(P_j^{(a,b)}(z)\)=the relation between this Jacobi notation and the packet handle's Jacobi notation needs an anchored definition, \(\binom{v}{i}\)=the generalized binomial coefficient needs an anchored definition, \(U\)=the lower-witness rank coordinate needs an anchored definition, \(P_\star\)=the reference structural law needs an anchored proof definition, \(P_\pm\)=the alternative structural laws need an anchored proof definition, \(\mu_\star\)=the reference conditional mean needs an anchored proof definition, \(\mu_\pm(a_0+t)\)=the alternative conditional means need an anchored proof definition, \(\delta(t)\)=the regime-specific perturbation needs an anchored proof definition, \(h_0\)=the direct-regime bandwidth needs an anchored tuning definition, \(h\)=the dictionary bandwidth and inverse-regime localization width require explicit contextual definitions, \(\ell\)=the inverse-regime support radius needs an anchored tuning definition, \(m\)=the polynomial index and packet degree require explicit contextual definitions, \(J\)=the cancellation cutoff needs an anchored tuning definition, \(c_p\)=the cancellation-order constant needs an anchored tuning definition, \(\chi^2(P_\pm,P_\star)\)=the observed-law divergence and its experiment need an anchored definition, \(a_n\)=the first transition scale needs an anchored definition, \(b_n\)=the second transition scale needs an anchored definition, \(D_n\)=the direct comparison scale needs an anchored definition, \(F_n(\sigma)\)=the intermediate comparison scale needs an anchored definition, \(P_n(\sigma)\)=the compact-support comparison scale needs an anchored definition

# Notation

The table records definition homes. A gap entry requires a presentation definition immediately before first use; its mathematical content must come from the established construction. Generic bound constants, dummy summation indices, integration variables, and standard mathematical operations are ambient notation.

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(\mathcal X\) | \(\mathcal X\) | The two observed strata | Gap: setup coordinates |
| \(P\) | \(P\) | Structural probability law on the declared coordinate spaces | Gap: structural law |
| \(X\) | \(X\) | Observed stratum coordinate | Gap: setup coordinates |
| \(A\) | \(A\) | Latent dose coordinate | Gap: setup coordinates |
| \(Z\) | \(Z\) | Standardized classical Gaussian error coordinate | Gap: setup coordinates |
| \(Y\) | \(Y\) | Realized outcome coordinate | Gap: setup coordinates |
| \(W\) | \(W\) | Contaminated dose obtained from the latent dose and scaled error | Gap: setup coordinates |
| \(O_1,\ldots,O_n\) | \(O_1,\ldots,O_n\) | Sample of observed stratum, contaminated-dose and outcome records | Gap: observed records |
| \(p_x\) | \(p_x\) | Probability of stratum \(x\) under the structural law | Gap: stratum probabilities |
| \(a_0\) | \(a_0\) | Prespecified latent evaluation dose | Gap: target and centering |
| \(t\) | \(t\) | Latent-dose displacement from the evaluation dose | Gap: target and centering |
| \(V\) | \(V\) | Observed-dose displacement from the evaluation dose | Gap: target and centering |
| \(g_x(t)\) | \(g_x(t)\) | Conditional density of the centered latent dose in stratum \(x\) | Gap: conditional design |
| \((\mathcal S,\mathcal E)\) | \((\mathcal S,\mathcal E)\) | Public measurable space of Borel potential-outcome schedules | def:potential-path-space |
| \(e\) | \(e\) | Jointly measurable schedule-evaluation map | def:potential-path-space |
| \(e(f,a)\) | \(e(f,a)\) | Value of schedule \(f\) at dose \(a\) | def:potential-path-space |
| \(\mathcal E\otimes\mathcal B([0,1])\) | \(\mathcal E\otimes\mathcal B([0,1])\) | Product sigma algebra for schedule evaluation | def:potential-path-space |
| \(C([0,1],[0,1])\) | \(C([0,1],[0,1])\) | Continuous unit-interval-valued functions with uniform-norm Borel structure | def:potential-path-space |
| \(\iota\) | \(\iota\) | Measurable map from a continuous mean function and rank to a threshold schedule | def:potential-path-space |
| \(\iota(f,u)(a)\) | \(\iota(f,u)(a)\) | Threshold-schedule value at dose \(a\) | def:potential-path-space |
| \(Y(\cdot)\) | \(Y(\cdot)\) | Measurable random potential-outcome schedule | def:potential-path-space |
| \(Y(a)\) | \(Y(a)\) | Potential outcome obtained by evaluating the random schedule | def:potential-path-space |
| \(\mu_x(a)\) | \(\mu_x(a)\) | Conditional potential-outcome mean in stratum \(x\) at dose \(a\) | def:conditional-potential-mean |
| \(\mu_x\) | \(\mu_x\) | Conditional potential-outcome mean function on the dose interval | def:conditional-potential-mean |
| \(\mu_X(A)\) | \(\mu_X(A)\) | Conditional potential-mean function evaluated at the realized stratum and dose | def:conditional-potential-mean |
| \(\mu_x(a_0)\) | \(\mu_x(a_0)\) | Stratum-specific causal mean at the evaluation dose | def:conditional-potential-mean |
| \(\mu_x(t+a_0)\) | \(\mu_x(t+a_0)\) | Conditional potential mean expressed in centered-dose coordinates | def:conditional-potential-mean |
| \(\theta(P)\) | \(\theta(P)\) | Population causal mean at the prespecified latent dose | Gap: causal target |
| \(\mathcal H^\beta([0,1])\) | \(\mathcal H^\beta([0,1])\) | Functions on the dose interval with radius-one Hölder increment seminorm | Gap: smoothness class |
| \([\mu_x]_\beta\) | \([\mu_x]_\beta\) | Hölder increment seminorm of the conditional mean | Gap: smoothness class |
| \(\mathcal P_{\beta,\kappa,\sigma}\) | \(\mathcal P_{\beta,\kappa,\sigma}\) | Structural laws satisfying the displayed bounded-outcome model restrictions | def:model-class |
| \(Q_P^n\) | \(Q_P^n\) | Sample observed-law experiment induced by the structural law | def:observed-experiment |
| \(R_n(\sigma)\) | \(R_n(\sigma)\) | Minimax expected absolute error for causal evaluation | def:minimax-risk |
| \(\alpha\) | \(\alpha\) | Fixed noncoverage probability for honest intervals | Gap: honesty level |
| \(H_n(\sigma)\) | \(H_n(\sigma)\) | Minimum worst-law expected length among honest connected intervals | def:honest-length |
| \(d\) | \(d\) | Effective exponent combining mean smoothness and design decay | def:frontier-rate |
| \(L_n\) | \(L_n\) | Logarithmic sample-size quantity | def:frontier-rate |
| \(b_{n,\sigma}\) | \(b_{n,\sigma}\) | Piecewise localization scale indexed by sample size and error scale | def:frontier-rate |
| \(\rho_{n,\sigma}\) | \(\rho_{n,\sigma}\) | Localization scale raised to the mean-smoothness exponent | def:frontier-rate |
| \(a_n\) | \(a_n\) | First noise-scale transition threshold | Gap: transition comparisons |
| \(b_n\) | \(b_n\) | Second noise-scale transition threshold | Gap: transition comparisons |
| \(D_n\) | \(D_n\) | Direct-regime scale for transition comparisons | Gap: transition comparisons |
| \(F_n(\sigma)\) | \(F_n(\sigma)\) | Intermediate Gaussian scale for transition comparisons | Gap: transition comparisons |
| \(P_n(\sigma)\) | \(P_n(\sigma)\) | Compact-support scale for transition comparisons | Gap: transition comparisons |
| \(q\) | \(q\) | Public nonnegative weight on the centered latent-dose interval | Gap: inverse-weight family |
| \(\ell_q\) | \(\ell_q\) | Borel inverse weight satisfying the pointwise Gaussian expectation identity | Gap: inverse-weight family |
| \(I_\kappa(q)\) | \(I_\kappa(q)\) | Design-weighted moment of the latent weight | Gap: public weight certificates |
| \(b_q\) | \(b_q\) | Public lower bound for a weighted stratum denominator | Gap: public weight certificates |
| \(B_q\) | \(B_q\) | Public bound for localized-ratio approximation error | Gap: public weight certificates |
| \(V_q\) | \(V_q\) | Public second-moment bound for observable inverse-weight estimation | Gap: public weight certificates |
| \(A_q\) | \(A_q\) | Public finite-sample expected-error score | Gap: public weight certificates |
| \(m_{x,q}\) | \(m_{x,q}\) | Population ratio of weighted outcome and weighted stratum moments | Gap: localized population ratio |
| \(q_h^{\mathrm F}\) | \(q_h^{\mathrm F}\) | Positive Fourier comparison weight indexed by bandwidth | Gap: Fourier inverse pair |
| \(\ell_h^{\mathrm F}\) | \(\ell_h^{\mathrm F}\) | Exact Gaussian inverse of the Fourier comparison weight | Gap: Fourier inverse pair |
| \(q_m^{\mathrm M}\) | \(q_m^{\mathrm M}\) | Positive polynomial comparison weight indexed by degree | Gap: polynomial inverse pair |
| \(\ell_m^{\mathrm M}\) | \(\ell_m^{\mathrm M}\) | Polynomial inverse-heat weight paired with the polynomial comparison weight | Gap: polynomial inverse pair |
| \(h\) | \(h\) | Fourier bandwidth in estimation and localization width in inverse-regime proofs | Gap: contextual tuning definitions |
| \(m\) | \(m\) | Polynomial dictionary index or filtered-packet degree according to context | Gap: contextual tuning definitions |
| \(\mathcal D_{n,\sigma}\) | \(\mathcal D_{n,\sigma}\) | Finite public dictionary of inverse pairs and scores | def:weight-dictionary |
| \(\mathcal I_r\) | \(\mathcal I_r\) | Deterministic modulo-three sample block | def:total-estimator |
| \(\widehat p_x\) | \(\widehat p_x\) | Split-sample stratum-frequency estimate | def:total-estimator; formula gap |
| \(\widehat D_x(q)\) | \(\widehat D_x(q)\) | Split-sample inverse-weight denominator estimate | def:total-estimator; formula gap |
| \(\widehat M_x(q)\) | \(\widehat M_x(q)\) | Split-sample inverse-weight outcome numerator estimate | def:total-estimator; formula gap |
| \(\widehat\mu_x(q)\) | \(\widehat\mu_x(q)\) | Clipped stratum-specific weighted ratio estimate | def:total-estimator; formula gap |
| \(\widehat\theta_q\) | \(\widehat\theta_q\) | Causal-mean estimate assembled for a specified weight | def:total-estimator; formula gap |
| \(\widehat q\) | \(\widehat q\) | First public-score minimizer in the fixed dictionary order | def:total-estimator |
| \(A_{\widehat q}\) | \(A_{\widehat q}\) | Public expected-error score of the selected dictionary weight | Gap: public weight certificates; def:total-estimator |
| \(\widehat\theta\) | \(\widehat\theta\) | Selected-weight causal-mean estimator with the declared fallback | def:total-estimator |
| \(\widehat\theta_{\widehat q}\) | \(\widehat\theta_{\widehat q}\) | Weight-indexed estimator evaluated at the public selected weight | def:total-estimator |
| \(C_{n,\sigma}\) | \(C_{n,\sigma}\) | Connected score-based interval intersected with the target range | def:honest-interval |
| \(\Phi_\sigma\) | \(\Phi_\sigma\) | Centered Gaussian convolution measure at the known error scale | Gap: convolution measures |
| \(\Phi_0\) | \(\Phi_0\) | Point-mass convolution measure at zero error scale | Gap: convolution measures |
| \(\delta_0\) | \(\delta_0\) | Unit point mass at zero | Gap: convolution measures |
| \(\eta(s)\) | \(\eta(s)\) | Fixed smooth spectral filter used in the packet construction | def:packet-handle |
| \(r\) | \(r\) | Fixed boundary-taper parameter in the packet construction; sample-block index in the estimator context | def:packet-handle; def:total-estimator |
| \(b\) | \(b\) | Jacobi endpoint parameter associated with the positive design-decay exponent | def:packet-handle |
| \(\mathsf J_j^{(a,b)}\) | \(\mathsf J_j^{(a,b)}\) | Standard Jacobi polynomial of degree \(j\) with parameters \(a,b\) | def:packet-handle |
| \(H_j^{a,b}\) | \(H_j^{a,b}\) | Squared Jacobi norm under the specified weighted interval measure | def:packet-handle |
| \(K_m(z)\) | \(K_m(z)\) | Filtered Jacobi sum evaluated relative to the endpoint | def:packet-handle |
| \(K_m(-1)\) | \(K_m(-1)\) | Endpoint normalizing value of the filtered Jacobi sum | def:packet-handle |
| \(\widetilde K_m(u)\) | \(\widetilde K_m(u)\) | Symmetric filtered Jacobi sum evaluated relative to the interior point | def:packet-handle |
| \(\widetilde K_m(0)\) | \(\widetilde K_m(0)\) | Interior normalizing value of the symmetric filtered Jacobi sum | def:packet-handle |
| \(\psi_m(u)\) | \(\psi_m(u)\) | Normalized, tapered and zero-extended filtered Jacobi packet | def:packet-handle |
| \((\psi_m)_{m\ge4}\) | \((\psi_m)_{m\ge4}\) | Packet sequence indexed by integer degree | def:packet-handle |
| \(\psi_m'\) | \(\psi_m'\) | Derivative of the zero-extended packet | def:packet-handle |
| \(P_j^{(a,b)}(z)\) | \(P_j^{(a,b)}(z)\) | Standard Jacobi polynomial in the binomial-identity notation | Gap: Jacobi notation reconciliation |
| \(\binom{v}{i}\) | \(\binom{v}{i}\) | Generalized binomial coefficient defined by a falling factorial | Gap: generalized binomial coefficients |
| \(U\) | \(U\) | Uniform-rank coordinate for the explicit lower-bound subclass | Gap: witness coordinates |
| \(P_\star\) | \(P_\star\) | Reference threshold structural law used in the lower-bound comparison | Gap: witness laws |
| \(P_\pm\) | \(P_\pm\) | Pair of perturbed threshold structural laws used in the lower bound | Gap: witness laws |
| \(\mu_\star\) | \(\mu_\star\) | Constant reference conditional mean for the witness law | Gap: witness means |
| \(\mu_\pm(a_0+t)\) | \(\mu_\pm(a_0+t)\) | Conditional means formed by opposite perturbations of the reference mean | Gap: witness means |
| \(\delta(t)\) | \(\delta(t)\) | Regime-specific localized mean perturbation | Gap: witness perturbations |
| \(h_0\) | \(h_0\) | Direct-regime perturbation bandwidth | Gap: lower-bound tuning |
| \(\ell\) | \(\ell\) | Support radius of an inverse-regime packet perturbation | Gap: lower-bound tuning |
| \(J\) | \(J\) | Integer cutoff for the cancelled moment series | Gap: lower-bound tuning |
| \(c_p\) | \(c_p\) | Constant linking packet degree to cancellation order | Gap: lower-bound tuning |
| \(\chi^2(P_\pm,P_\star)\) | \(\chi^2(P_\pm,P_\star)\) | Chi-squared comparison of the witness-induced observed laws | Gap: observed divergence |

# Sections

## section: Abstract

Plan a concise abstract written after the main text. Lead with evaluation of a causal mean at a weakly supported latent dose measured with known Gaussian error. Summarize the matching estimation and connected-interval-length orders, the three measurement-error regimes, the observable construction, and finite-sample coverage. Express early references to smoothness, design decay and error scale in words, with the exact bounded-outcome, compact-support and two-stratum scope.

objs: none

bib: none

home_objs: none
## section: Introduction

Organize the introduction around how measurement precision and local dose support jointly determine the difficulty of causal evaluation at a prespecified dose. Present the uniform rate characterization as the principal contribution, followed by its constructive estimator and honest interval, and explain why compact support becomes consequential at larger error scales. Plan one factual sentence pointing to the appendix verification note, with an internal reference supplied by its eventual structural label. Write the introduction after the results and proofs, retaining affirmative scope and first-use glosses.

objs: none

bib: none

home_objs: none
## section: Related work

Position the paper first against Huang and Zhang's contaminated-treatment causal dose-response estimator, preserving the conditions and expansion locator in their Theorem 4.4, arXiv version 2. Compare the direct endpoint with Gaiffas's Definition 2 and Theorem 1 as an exponent comparison across experiments, and the intermediate inversion mechanism with Fan and Truong's Sections 3–4 under their positive-design and regularity conditions. Compare the compact-support branch with Meister's Theorems 1–2 under integrated squared density loss and Jiang, Ma and Carroll's Theorem 2 under conditions (C2)–(C4) and (D1)–(D5), including their operator and nonsingularity premises. Place the interval result alongside Armstrong and Kolesar's bias-aware direct-regression inference and Kato and Sasaki's ordinary-smooth errors-in-variables bands. Use continuous-treatment causal estimation and vanishing-noise regression as supporting context. State the paper's contribution as the same-class pointwise absolute-risk and honest-length characterization uniformly across known Gaussian scales; keep every comparison tied to its source's target, loss and conditions.

objs: none

bib: HuangZhang2023, Gaiffas2005, FanTruong1993, Meister2007, JiangMaCarroll2026, ArmstrongKolesar2020, KatoSasaki2019, Hirano2004, Imai2004, Kennedy2017, Colangelo2026, Bonvini2026, DurotMukherjee2026

home_objs: none
## section: Setup and assumptions

Introduce the structural coordinates, observed records, evaluation target and centered-dose notation through grouped presentation definitions that resolve the setup gaps. Define the measurable potential-outcome schedule and its conditional mean before imposing structural restrictions. Explain fixed smoothness, polynomially declining latent-dose density, compact support, known classical Gaussian error, schedule-level conditional exchangeability, consistency and bounded potential outcomes. Place the model class after its defining assumptions and the observed experiment after the sampling restriction. Establish causal identification with \cref{obj:prop:identification}, reserving the realized-dose identity and convolution argument for the appendix.

objs: def:potential-path-space, def:conditional-potential-mean, ass:stratum-overlap, ass:latent-support, ass:weak-design, ass:holder-mean, ass:mean-range, ass:gaussian-channel, ass:error-independence, ass:conditional-unconfoundedness, ass:bounded-potential-outcomes, ass:consistency, ass:rank-uniform, ass:rank-treatment-independence, ass:structural-threshold, ass:binary-potential-outcomes, def:model-class, ass:iid, def:observed-experiment, prop:identification

bib: Rubin1974, Rosenbaum1983, Imbens2015

home_objs: def:potential-path-space, def:conditional-potential-mean, ass:stratum-overlap, ass:latent-support, ass:weak-design, ass:holder-mean, ass:mean-range, ass:gaussian-channel, ass:error-independence, ass:conditional-unconfoundedness, ass:bounded-potential-outcomes, ass:consistency, def:model-class, ass:iid, def:observed-experiment, prop:identification
## section: Optimal estimation and interval length

Define the minimax absolute-error criterion and honest connected-interval-length criterion, including the fixed coverage level, before introducing the rate scale. Lead the formal results with \cref{obj:thm:uniform-frontier}. Explain the direct, intermediate Gaussian and compact-support regimes through measurement precision and local support, then interpret the two transition windows and the fixed-positive-error consequence. Present \cref{obj:prop:error-free-reduction} as the direct endpoint of the paper's own characterization. Use an eventual figure or table to display the branches and thresholds, with its exact structural label referenced through cleveref. Give the proof strategy through observable localization and observed-law indistinguishability, keeping packet machinery in the appendix.

objs: def:minimax-risk, def:honest-length, def:frontier-rate, thm:uniform-frontier, prop:error-free-reduction

bib: Tsybakov2009, Donoho1994, Low1997

home_objs: def:minimax-risk, def:honest-length, def:frontier-rate, thm:uniform-frontier, prop:error-free-reduction
## section: Observable estimation and honest intervals

Introduce grouped definitions for the latent weights, exact Gaussian inverses, public certificates, Fourier and polynomial families, and intermediate estimator formulas before their first use. Present the central estimator as the numbered procedure in \cref{obj:def:total-estimator}, preceded by its finite public dictionary. Explain that the score selection is public and that Fourier and polynomial candidates provide the comparisons needed in the respective regimes. Present the estimator's rate and the connected interval's coverage and length results through \cref{obj:thm:observable-upper,obj:thm:finite-honesty}. Distinguish coverage at each positive sample size from the uniform sufficiently-large-sample rate guarantees, and explain the declared small-sample and empty-block fallbacks as part of the total construction.

objs: synth_4, synth_2, synth_1, def:weight-dictionary, synth_6, synth_3, def:total-estimator, thm:observable-upper, def:honest-interval, thm:finite-honesty

bib: Masry1992

home_objs: def:weight-dictionary, def:total-estimator, thm:observable-upper, def:honest-interval, thm:finite-honesty
## section: Observed-law lower bounds

Present \cref{obj:thm:observed-lower} as the converse establishing the statistical difficulty of the actual contaminated-dose experiment. Explain how a shared latent design and bounded Bernoulli witness subclass connect target separation to indistinguishability of observed records. Describe weighted moment cancellation as the scientific mechanism behind the two inverse-regime comparisons, referring to its appendix construction through \cref{obj:thm:weighted-packet-construction}. Keep rank coordinates, threshold construction assumptions, packet formulas and regime-specific tuning in the appendix before their first proof use. Plan exact equation labels for the witness construction and comparison steps so later reader-facing references use cleveref.

objs: none

bib: Tsybakov2009, ChenNilesWeed2021

home_objs: none
## section: Discussion

Interpret the value of improving measurement precision at a prespecified dose when compact support and the weak-design envelope are substantively justified. Explain how the design-decay exponent affects the direct and intermediate regimes and how known compact support governs the eventual fixed-error order. Relate the matching interval-length and absolute-error orders to uncertainty about the same scalar causal target. Keep this section centered on the paper's results and their conditional application meaning.

objs: none

bib: none

home_objs: none
## section: Limitations and future work

Separate future directions from the established fixed-parameter characterization. Plan discussion of adaptation over mean smoothness and design decay, unknown error scale, richer covariates, simultaneous dose inference, and empirical validation of the support and density envelopes. Identify the additional statistical questions each extension introduces. Treat dietary-intake applications as a direction requiring application-specific validation and analysis.

objs: none

bib: Delaigle2008, Schennach2004a, Schennach2004b, HuangZhang2023

home_objs: none
## section: Appendix: Identification and observable risk certificates

Prove the derived random-dose mean identity before the positive-ratio argument and identification proof. Place the grouped convolution-measure definition before its injectivity lemma. Develop the population localization argument, split-sample error certificate and dictionary comparison bounds in their logical order, followed by proofs of observable achievability and interval honesty. Preserve the distinction between latent nonnegative weights and their observable inverses, and between the uniform large-sample rate threshold and finite-sample coverage.

objs: lem:realized-dose-mean, lem:compact-gaussian-convolution-injective, lem:positive-ratio, lem:public-error-certificate, lem:dictionary-score-rate

bib: FanTruong1993, Masry1992, Meister2009, ArmstrongKolesar2020

home_objs: lem:realized-dose-mean, lem:compact-gaussian-convolution-injective, lem:positive-ratio, lem:public-error-certificate, lem:dictionary-score-rate
## section: Appendix: Weighted packets and observed-experiment converse

Introduce the appendix-only rank coordinate and witness construction, placing the uniform-rank, rank–dose independence, threshold-schedule and binary-outcome assumptions before their first use. Define the witness laws, reference and perturbed means, tuning quantities and observed-law divergence through grouped presentation definitions. Introduce the filtered-Jacobi handle before its construction theorem, with the Jacobi notation reconciliation and generalized binomial definition preceding the auxiliary identity. Develop the normalization, localization, derivative control and weighted cancellation arguments, including the separate interior construction at zero design decay. Complete the regime-specific observed-law comparison, then derive the minimax risk and honest-length converse, transition-window comparisons and endpoint consequences. End the appendix with a brief verification note consolidating the machine-checking scope of the frozen results and the status of model assumptions and cited analytic inputs, preserving theorem-local dependency disclosures.

objs: def:packet-handle, lem:jacobi-binomial, thm:weighted-packet-construction, synth_5, synth_7, synth_8, thm:observed-lower

bib: PetrushevXu2005, https://people.math.sc.edu/pencho/Publications/kpx-06-28-06-web.pdf, https://dlmf.nist.gov/18.3, https://dlmf.nist.gov/5.11.E12, ChenNilesWeed2021, Wu2020, Tsybakov2009
home_objs: ass:rank-uniform, ass:rank-treatment-independence, ass:structural-threshold, ass:binary-potential-outcomes, def:packet-handle, lem:jacobi-binomial, thm:weighted-packet-construction, thm:observed-lower
