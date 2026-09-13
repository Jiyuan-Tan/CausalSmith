# Quotient-Law Inference for Latent-Class Mean Effects at Collisions

We estimate the population-weighted distribution of latent-class average treatment effects uniformly at the root-\(n\) rate, including configurations where several classes share the same mean effect. This estimand is distinct from the distribution of individual contrasts \(Y(1)-Y(0)\).

---

## Overview

- Our target is the quotient law \(\nu_P\), the population-weighted distribution of latent-class average treatment effects after aggregating classes with the same mean effect.
- In the one-Wasserstein transport distance \(W_1\), observable proxy moments determine this law through a gap-free Lipschitz map.
- Law estimation and honest confidence reporting attain uniform root-\(n\) accuracy.
- Effect-ordered class masses incur the sharp inverse-gap cost on separated two-class configurations.

---

## Motivation

- Think of an observational treatment study where an unobserved response type affects treatment and outcomes.
- Two proxy measurements carry complementary information about that latent type.
- In our two-class benchmark, the class-average effects are \(0.25-\varepsilon\) and \(0.25+\varepsilon\), where \(\varepsilon\) is their displacement from a collision.
- The population masses are \(0.4\) and \(0.6\).
- At \(\varepsilon=0\), both types contribute to one treatment-effect value; for \(\varepsilon>0\), the law has two nearby atoms.
- Can one infer the law of class-average effects continuously across this transition?

---

## Target

- The quotient law places each latent-class mass at its class-average treatment effect and adds the masses of coincident mean effects.
- \(W_1\) is the minimum distance-weighted mass required to transport one effect law into another.
- In the benchmark, the quotient law moves continuously from two atoms to one aggregate atom as \(\varepsilon\) approaches zero.
- It does not identify the distribution of individual contrasts \(Y(1)-Y(0)\); its atoms are conditional class means.

@figure quotient-collision: Two latent-class boxes labeled by their masses point to class-average-effect boxes, and coincident mean-effect values merge into one quotient-law atom carrying the aggregate mass.

---

## Model

- We observe treatment, two proxy vectors, and the realized outcome for independent units.
- The analyst supplies the fixed class cardinality \(k\) and uniform bounds \(L,\pi_0,\sigma_0\); consistency and latent ignorability give each class a causal mean treatment contrast.
- Conditional separation makes one proxy a class measurement and the other an arm-specific class measurement.
- Observable contributions are bounded.
- The latent-arm positivity margin \(\pi_0\) and proxy-rank margin \(\sigma_0\) remain fixed across the model class.
- In our benchmark, the proxy matrices remain nonsingular at \(\varepsilon=0\), and every latent class–treatment arm has positive mass.

@formal ass:latent-arm-positivity

@formal ass:proxy-rank-margin

---

## Observable moments

- The five-block summary \(S(P)\) consists of arm-specific proxy moments, outcome-weighted proxy moments, and the target-proxy mean.
- Its empirical version \(\widehat S_n\) is formed by sample averaging within treatment arms.
- A compressed operator built from these moments has the latent treatment effects as eigenvalues.
- Spectral anchors recover the masses attached to the corresponding eigenspaces.
- The summary distance \(d_S\) adds the operator-norm errors of the four matrix blocks and the Euclidean error of the proxy mean.

@informal prop:observed-vmw-margin-inclusion: Under the fixed model restrictions, treatment arms have positive probability, the observable proxy moments have stable factorizations and singular-value margins, and latent effects remain within a fixed bounded interval.

@informal prop:summary-closure-compact: Under fixed dimensions and margins, the closure of feasible five-block summaries is compact, with nonemptiness equivalent to nonemptiness of the model class.

---

## Related literature

- Miao et al. (2018) identify causal effects using conditionally independent proxies and rank conditions.
- Mazaheri et al. (2025) and Virk et al. (2026) develop finite latent-effect identification and separated spectral recovery.
- Heinrich and Kahn (2018) and Wu and Yang (2020) show how collision geometry shapes rates in ordinary finite mixtures.
- Deo and Randrianarisoa (2023) develop honest Wasserstein confidence sets for mixture uncertainty.
- Our contribution uses the proxy operator to obtain regular inference for the aggregated effect law across homogeneous, partially colliding, and separated configurations.

---

## Key idea

- A direct plug-in eigendecomposition tracks individual eigenvectors and amplifies perturbations by the inverse effect gap.
- Near a collision, individual eigendirections can rotate sharply while their combined spectral subspace remains stable.
- We aggregate the anchor mass over each colliding eigenspace and transport that mass across the cluster diameter.
- The aggregation absorbs simultaneous merges and splits into the \(W_1\) geometry.
- Uniform proxy conditioning controls the compressed operator; positivity controls the mass carried by each distinct atom.
- Together these facts convert observable-moment error into law-level transport error without an effect-gap factor.

---

## Main result

@informal thm:gap-free-positive-measure-modulus: Under fixed dimensions, bounded contributions, latent-arm positivity, and proxy-rank margins, the \(W_1\) distance between two quotient laws is at most a constant times the distance between their observable summaries, uniformly across collisions.

@formal thm:gap-free-positive-measure-modulus

The same Lipschitz law map covers the one-atom benchmark at \(\varepsilon=0\) and its two-atom neighbors.

---

## Estimation

- Uniform concentration controls all five empirical-summary blocks at the usual sampling scale.
- Our repair estimator selects the nearest feasible summary and applies the Lipschitz law map.
- Our lattice estimator searches a finite constrained representation of discretized signal bases, conditioning matrices, masses, and effect locations for the best exact-real match to the empirical moments.
- Both mechanisms return positive atomic effect laws.

@informal lem:uniform-summary-concentration: Uniformly over the model class, the empirical summary exceeds \(C_0L\sqrt{\log(C_0/\eta)/n}\) error with probability at most the tail probability \(\eta\).

@informal thm:collision-uniform-root-n: With fixed dimensions and margins, both law estimators have \(W_1\) error at most \(C\sqrt{\log(C/\eta)/n}\) simultaneously with probability at least \(1-\eta\), uniformly over the model class.

@formal thm:collision-uniform-root-n

---

## Estimator pipeline

- Thresholding extracts the \(k\)-dimensional proxy signal space at the fixed scale \(\pi_0\sigma_0^2/2\).
- The lattice compares candidate effect operators, proxy means, and anchor equations.
- The first minimizing candidate supplies the estimated atomic law \(\widehat\lambda_n\).
- The mesh contributes \(1/\sqrt n\), matching the sampling scale.

@informal prop:polynomial-net-law-estimator: For fixed dimensions and margins, the structured-lattice estimator has \(W_1\) error at most \(C_{\mathrm{lat}}\{d_S(\widehat S_n,S(P))+1/\sqrt n\}\), a polynomial-size candidate list, and the stated uniform root-\(n\) tail bound.

@informal thm:polynomial-net-law-estimator: For fixed dimensions and supplied exact-real primitives, a finite-library estimator is Borel, uses at most \(C\{n+n^{(4d_zd_x+d_x)/2}\}\) operations, and attains the stated uniform root-\(n\) tail bound.

@figure estimator-pipeline: Observed treatment, proxies, and outcome flow to the empirical five-block summary, then to structured-lattice matching, and finally to an atomic quotient-law estimate and its Wasserstein confidence report.

---

## Confidence sets

- For miscoverage level \(\alpha\), the summary radius \(r_{n,\alpha}\) describes simultaneous moment uncertainty.
- The exact-real radius \(R_{n,\alpha}\) adds the lattice approximation scale.
- Our finite constrained exact-real set contains atomic laws with aggregate atom mass at least \(\pi_0\) and transport distance at most \(R_{n,\alpha}\) from \(\widehat\lambda_n\).
- A companion set maps nearby feasible summaries through the repaired law functional.

@informal thm:honest-root-n-confidence: Under fixed dimensions, boundedness, positivity, and rank margins, both nonempty confidence sets cover \(\nu_P\) jointly with probability at least \(1-\alpha\) and have \(W_1\) diameter at most their stated root-\(n\) radii.

@formal thm:honest-root-n-confidence

@informal prop:summary-repair-total-borel: The repaired estimator is total and Borel, and its exact repaired-image confidence set is nonempty for every sample.

---

## Cluster report

- The association radius \(\rho_{n,\alpha}\) is the confidence radius divided by the atom-mass floor.
- We connect estimated support points within \(4\rho_{n,\alpha}\); each connected component is an empirically unresolved effect cluster.
- Each cluster receives a support interval and the range of compatible aggregate masses over the confidence set.
- In the benchmark collision, the single effect cluster carries aggregate mass one.
- External separation sharpens the mass interval for an isolated cluster.

@informal thm:cluster-adaptive-report: With probability at least \(1-\alpha\), the empirical clusters uniquely cover the true support, their intervals cover the associated atoms and aggregate masses, and their mass-interval widths are at most the stated inverse-external-gap bounds.

@formal thm:cluster-adaptive-report

---

## Ordered weights

- The ordered target \(p^{\uparrow}(P)\) lists latent masses by increasing treatment effect when all \(k\) effects are distinct.
- The effect-gap scale \(g\) places the smallest positive gap between \(g/2\) and \(2g\).
- Converting \(W_1\) error into individual mass error divides by the distance available to transport misallocated mass.
- Wider gaps support precise labeling; shrinking gaps increase the cost of resolving effect order.

@informal thm:labeled-weight-upper: On the gap-local stratum, our ordered-weight estimator has expected \(\ell_1\) error at most \(C\min\{1,(\sqrt n\,g)^{-1}\}\).

@formal thm:labeled-weight-upper

---

## Lower bounds

- Our explicit two-class Bernoulli witness retains strict positivity and full proxy rank as its two effects collide.
- For quotient laws, we compare the collision with an effect displacement of \(a/\sqrt n\).
- For ordered weights, a factorization-preserving path changes masses by a displacement \(h\) while the observed Kullback–Leibler divergence scales as \(g^2h^2\).
- Le Cam (1986) and Polyanskiy and Wu (2019) then convert these close observed experiments into risk lower bounds.

@informal prop:two-class-witness-valid: For \(0\le\varepsilon\le1/8\), the two-class witness belongs to the uniformly conditioned model with the stated margins and has quotient law \(0.4\,\delta_{0.25-\varepsilon}+0.6\,\delta_{0.25+\varepsilon}\), including a nonsingular collision at \(\varepsilon=0\).

@informal thm:matching-local-lower-bounds: On the explicit two-class local experiments, every estimator has quotient-law risk at least \(c/\sqrt n\) and ordered-weight risk at least \(c\min\{1,1/(\sqrt n\,g)\}\), with the stated observed-divergence certificates.

@formal thm:matching-local-lower-bounds

@informal prop:same-class-quotient-minimax: On the explicit two-class model, quotient-law minimax risk is bounded above and below by constant multiples of \(1/\sqrt n\).

@informal prop:same-class-labeled-minimax: On the explicit two-class gap stratum, ordered-weight minimax risk is bounded above and below by constant multiples of \(\min\{1,1/(\sqrt n\,g)\}\).

@informal thm:published-vmw-converse-transfer: A published-VMW comparator class inherits the applicable lower bound whenever it contains the displayed witness pair.

---

## Scope of the guarantees

- The estimand is the population-weighted law of latent-class mean effects, rather than the law of individual treatment effects.
- The procedures use supplied values of \(k,L,\pi_0,\sigma_0\); the guarantees are uniform over the resulting fixed class.
- The computational theorem gives a finite constrained representation and a fixed-dimensional exact-real operation bound. It does not claim polynomial bit complexity or a numerical implementation.
- Matching minimax rates are proved on the explicit uniformly conditioned two-class specialization; the general model-class results are upper bounds.

---

## Takeaways

- Aggregating coincident class-average effects makes their population-weighted law a stable target for proxy-based causal inference.
- Observable proxy moments determine this quotient law through a gap-free \(W_1\) modulus.
- Structured estimation and honest confidence reporting achieve uniform root-\(n\) accuracy under fixed boundedness, positivity, and proxy-rank margins.
- Cluster reports express uncertainty at the support resolution available in the sample.
- Effect-ordered masses have the sharp clipped inverse-gap rate on the stated separated two-class configurations.
