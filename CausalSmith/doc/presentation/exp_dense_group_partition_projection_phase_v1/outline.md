# Title
**Random group formation and the equal-group CR2 variance in finite populations**

**Contribution statement.** The paper characterizes exact and asymptotic design-based variance under homogeneous random partitioning, identifies the Johnson degree-one correction that governs equal-group CR2 behavior, and proves a positive-density lower bound for one-realization exact-variance ratio estimation over the dense bounded-schedule class.

# Notation
notation_gaps: \(n\)=population index/size is used throughout but has no anchored definition, \(M\)=common group size is used throughout but has no anchored definition, \(\mathcal U_n\)=finite population is used in \(\widehat S_n(\mathcal O_n)\) context but has no anchored definition, \(\mathcal Z\)=treatment-arm set is used in \(\cref{def:group-table}\) but has no anchored definition, \(\Omega_{n,M}\)=uniform \(M\)-slice is used in multiple definitions but has no anchored definition, \(\mathbb E_n\)=uniform-slice averaging operator is used in \(\cref{def:pame-estimator}\) but has no anchored definition, \(L^2(\Omega_{n,M})\)=slice function space is used in \(\cref{def:johnson-decomposition}\) but has no anchored definition, \(\langle\cdot,\cdot\rangle_n\)=uniform-slice inner product is used in \(\cref{def:johnson-decomposition}\) and \(\cref{def:kneser-covariance}\) but has no anchored definition, \(\|\cdot\|_n\)=uniform-slice norm is used in \(\cref{def:dense-correction}\) but has no anchored definition, \(V_{z,n}\)=uniform-slice arm variance is used in theorems but has no anchored definition, \(\sigma_n^2\)=exact design variance is constrained before being named in an anchored definition, \(\mathcal O_n\)=one-realization observation is used in \(\cref{thm:qv-diagonal-impossibility}\) but has no anchored definition, \(\mathbb H_n^{\mathrm{same}}\)=same-sign randomized schedule prior is used in \(\cref{prop:rademacher-mixture-separation}\) but has no anchored definition, \(\mathbb H_n^{\mathrm{ind}}\)=independent-sign randomized schedule prior is used in \(\cref{prop:rademacher-mixture-separation}\) but has no anchored definition

\(G_n\) | \(G_n\) | number of realized groups | ass:group-count-growth
\(p_n\) | \(p_n\) | treated-group fraction | ass:stable-treatment-fraction
\(p\) | \(p\) | limiting treated-group fraction | ass:stable-treatment-fraction
\(N_n/n\) | \(N_n/n\) | grouped-unit sampling fraction | ass:sampling-fraction
\(\rho\) | \(\rho\) | limiting grouped-unit sampling fraction | ass:sampling-fraction
\(Y_{i,n}(z,A)\) | \(Y_{i,n}(z,A)\) | deterministic potential outcome for unit \(i\), arm \(z\), and group \(A\) | ass:bounded-potential-outcomes
\(B\) | \(B\) | uniform envelope for potential outcomes | ass:bounded-potential-outcomes
\(c_\sigma\) | \(c_\sigma\) | scaled-variance lower-bound constant | ass:scaled-variance-nondegeneracy
\(\mathbf A_n\) | \(\mathbf A_n\) | ordered tuple of pairwise-disjoint groups | def:random-partition-design
\(\mathbf Z_n\) | \(\mathbf Z_n\) | balanced group-treatment assignment vector | def:random-partition-design
\(G_{1n}\) | \(G_{1n}\) | number of treated groups | def:random-partition-design
\(G_{0n}\) | \(G_{0n}\) | number of control groups | def:random-partition-design
\(h_{z,n}(A)\) | \(h_{z,n}(A)\) | group-level arm table | def:group-table
\(\tau_n\) | \(\tau_n\) | uniform-slice average arm contrast | def:pame-estimator
\(\widehat\tau_n\) | \(\widehat\tau_n\) | group-level difference-in-means estimator | def:pame-estimator
\(\Pi_{n,k}f\) | \(\Pi_{n,k}f\) | Johnson harmonic degree-\(k\) projection of \(f\) | def:johnson-decomposition
\(\mathcal H_{n,k}\) | \(\mathcal H_{n,k}\) | Johnson harmonic degree-\(k\) subspace | def:johnson-decomposition
\(\mathsf K_n\) | \(\mathsf K_n\) | normalized Kneser disjointness operator | def:kneser-covariance
\(C_{ab,n}\) | \(C_{ab,n}\) | ordered-disjoint covariance between arm tables \(a\) and \(b\) | def:kneser-covariance
\(h_{a,n}^{\circ}\) | \(h_{a,n}^{\circ}\) | centered arm-\(a\) group table | def:kneser-covariance
\(E_{\tau,1,n}\) | \(E_{\tau,1,n}\) | degree-one Johnson energy of the arm-difference table | def:dense-correction
\(R_n\) | \(R_n\) | independent-group leading variance scale | def:dense-correction
\(s_{z,n}^2\) | \(s_{z,n}^2\) | within-arm sample variance among realized groups | def:cr2-statistic
\(\widehat V_{\mathrm{CR2},n}\) | \(\widehat V_{\mathrm{CR2},n}\) | scalar equal-group CR2 variance statistic | def:cr2-statistic
\(\mathcal C_{\mathrm{dense}}\) | \(\mathcal C_{\mathrm{dense}}\) | bounded dense triangular-array schedule class with growth, fraction, and scaled-variance conditions | def:dense-schedule-class
\(\mathbf a_8\) | \(\mathbf a_8\) | balanced eight-unit sign vector | def:eight-unit-witness
\(\lambda_{n,k}\) | \(\lambda_{n,k}\) | normalized Kneser eigenvalue on Johnson degree \(k\) | thm:exact-kneser-identity
\(C_{\tau\tau,n}\) | \(C_{\tau\tau,n}\) | ordered-disjoint covariance contrast for the arm difference | thm:exact-kneser-identity
\({\tt fit}\) | \({\tt fit}\) | unweighted intercept-plus-treatment least-squares fit | prop:clubsandwich-consumer
\({\tt lm}(Y^{\mathrm{obs}}\sim Z)\) | \({\tt lm}(Y^{\mathrm{obs}}\sim Z)\) | software regression call for observed group outcomes on treatment | prop:clubsandwich-consumer
\({\tt clubSandwich::vcovCR}({\tt fit},\ {\tt cluster}={\tt group},\ {\tt type}={\tt 'CR2'})\) | \({\tt clubSandwich::vcovCR}({\tt fit},\ {\tt cluster}={\tt group},\ {\tt type}={\tt 'CR2'})\) | versioned software CR2 covariance calculation | prop:clubsandwich-consumer
\(d_{\mathrm{same}}\) | \(d_{\mathrm{same}}\) | scaled-variance limit under the same-sign prior | thm:qv-diagonal-impossibility
\(d_{\mathrm{ind}}\) | \(d_{\mathrm{ind}}\) | scaled-variance limit under the independent-sign prior | thm:qv-diagonal-impossibility
\(\widehat S_n(\mathcal O_n)\) | \(\widehat S_n(\mathcal O_n)\) | arbitrary one-realization variance statistic | thm:qv-diagonal-impossibility

env_overrides: prop:clubsandwich-consumer=propositionv, prop:eight-unit-witness=propositionv, prop:rademacher-mixture-separation=propositionv

# Sections
## section: Introduction
The introduction will motivate random group formation as a design-based source of dependence among realized groups when a nonvanishing fraction of the population is partitioned. It will state the paper's positive scope: exact finite-sample variance identities, a dense asymptotic expansion, the CR2 probability limit and ratio criterion, the zero-density variance-estimation result, a software identity for the equal-group scalar CR2 statistic, and the one-realization lower bound. A single factual sentence will direct readers to the appendix verification note for the machine-checked scope.
objs: none
bib:

home_objs: none
## section: Related work
This section will position the paper within design-based causal inference, survey-sampling asymptotics, cluster-robust variance estimation, interference and group-formation experiments, and variance nonidentification. The closest theorem-level comparison is \(\citet{FuSamiiWang2026}\), whose sparse whole-tuple condition \(N_n^2/n\to0\) is compared with the present homogeneous fixed-\(M\) random-partition analysis through the exact Kneser variance identity, the dense correction \(G_n\sigma_n^2=R_n-\rho E_{\tau,1,n}+o(1)\), and the zero-density CR2 ratio result under \(N_n/n\to0\). The section will also relate the scalar software consumer result to \(\citet{PustejovskyTipton2018}\) and the \texttt{clubSandwich}/\texttt{sandwich} implementation line, and it will connect the lower bound to finite-population variance nonidentification and conservative variance-estimation work.
objs: none
bib: Neyman1923, Fisher1935, Cox1958, Rubin1974, Holland1986, Hajek1960, Cochran1977, Ohlsson1989, Fuller2009, LiDing2017, Delsarte1973, BrouwerCohenNeumaier1989, Filmus2016, BrouwerEtAl2018, White1980, LiangZeger1986, BellMcCaffrey2002, PustejovskyTipton2018, CameronMiller2015, Abadie2023, SuDing2021, ClubSandwich2026, Sandwich2026, Zeileis2004, Zeileis2006, ZeileisKollGraham2020, Sobel2006, HudgensHalloran2008, TchetgenTchetgen2012, Manski2013, LiuHudgens2014, AronowSamii2017, Ugander2013, Eckles2017, Athey2018, Li2019, Xu2021, Wang2025, Samii2023, Gao2025, BasseDingFellerToulis2024, PuelzBasseFellerToulis2022, AronowGreenLee2014, BasseAiroldi2018, HarshawMiddletonSavje2026, ParkWager2026, FuSamiiWang2026

home_objs: none
## section: Setup and assumptions
This section will define the homogeneous random-partition design, the group-level outcome tables, the PAME estimand and estimator, the Johnson decomposition, the Kneser covariance quantities, the dense correction terms, the scalar CR2 statistic, and the dense schedule class. The assumptions will be presented as the growth, treatment-fraction, sampling-fraction, boundedness, and scaled-variance conditions used by the asymptotic results.
objs: ass:group-count-growth, synth_11, ass:stable-treatment-fraction, ass:sampling-fraction, ass:bounded-potential-outcomes, ass:scaled-variance-nondegeneracy, synth_2, synth_1, def:random-partition-design, def:group-table, synth_3, def:pame-estimator, synth_12, def:johnson-decomposition, def:kneser-covariance, def:dense-correction, def:cr2-statistic, def:dense-schedule-class
bib: Filmus2016, BrouwerEtAl2018, FuSamiiWang2026

home_objs: ass:group-count-growth, ass:stable-treatment-fraction, ass:sampling-fraction, ass:bounded-potential-outcomes, ass:scaled-variance-nondegeneracy, def:random-partition-design, def:group-table, def:pame-estimator, def:johnson-decomposition, def:kneser-covariance, def:dense-correction, def:cr2-statistic, def:dense-schedule-class
## section: Exact variance geometry
This section will develop the finite-sample algebra behind random disjoint groups. It will state the normalized Kneser spectral identity, use it to express ordered-disjoint covariances degree by degree, and then give the exact finite-sample variance of \(\widehat\tau_n\) together with the exact expectation of the scalar CR2 statistic.
objs: synth_9, synth_5, synth_4, thm:exact-kneser-identity, thm:exact-pame-variance
bib: Delsarte1973, BrouwerCohenNeumaier1989, Filmus2016, BrouwerEtAl2018

home_objs: thm:exact-kneser-identity, thm:exact-pame-variance
## section: Dense and sparse variance behavior
This section will state the asymptotic projection expansion and interpret the degree-one Johnson energy as the first-order dense correction to the independent-group variance. It will then give the CR2 probability limit, its asymptotic conservativeness statement, its ratio-consistency criterion, and the zero-density ratio result under \(N_n/n\to0\), including the \(N_n=M\lfloor n^{3/4}/M\rfloor\) regime named in the frozen result.
objs: thm:dense-projection-limit, thm:cr2-phase-frontier, thm:sparse-beyond-birthday
bib: FuSamiiWang2026, PustejovskyTipton2018

home_objs: thm:dense-projection-limit, thm:cr2-phase-frontier, thm:sparse-beyond-birthday
## section: Software identity and finite witness
This section will connect the scalar statistic analyzed in the paper to the stated equal-group \texttt{clubSandwich} call, then present the balanced eight-unit witness as a finite design calculation where the exact variance and expected CR2 differ by a factor of two. The witness will serve as a concrete check on the finite-sample formulas before the paper turns to asymptotic impossibility.
objs: def:eight-unit-witness, prop:clubsandwich-consumer, prop:eight-unit-witness
bib: ClubSandwich2026, Sandwich2026, Zeileis2004, Zeileis2006, ZeileisKollGraham2020, PustejovskyTipton2018

home_objs: def:eight-unit-witness, prop:clubsandwich-consumer, prop:eight-unit-witness
## section: One-realization lower bound
This section will present the Rademacher mixture separation and the diagonal lower bound. The argument will be framed as a positive-density result: observationally equal one-realization mixture laws can carry separated scaled exact-variance limits on high-probability deterministic supports inside \(\mathcal C_{\mathrm{dense}}\), yielding a uniform lower bound for any measurable variance statistic based on \(\mathcal O_n\).
objs: synth_8, synth_7, synth_6, prop:rademacher-mixture-separation, thm:qv-diagonal-impossibility
bib: AronowGreenLee2014, BasseAiroldi2018, HarshawMiddletonSavje2026, ParkWager2026

home_objs: prop:rademacher-mixture-separation, thm:qv-diagonal-impossibility
## section: Discussion, scope, and extensions
This section will synthesize what the exact identities and asymptotic results imply for variance estimation after random group formation. In a clearly labelled limitations and future-work part, it will state that the paper leaves Gaussian approximation, studentized testing, Wald coverage, finite-sample CR2 conservativeness, and variable-group-size extensions as separate questions.
objs: none
bib: FuSamiiWang2026, PustejovskyTipton2018

home_objs: none
## section: Appendix: Proofs and auxiliary lemmas
The appendix will collect proofs of the formal results, beginning with the classical Johnson and Kneser inputs used by the spectral identity and then proceeding through the finite-sample variance algebra, dense projection limits, CR2 convergence, software identity, finite witness, and lower-bound construction. It will end with a verification note consolidating the Lean machine-checking scope: the frozen definitions, assumptions, theorems, propositions, and internal algebra are verified, while cited external Johnson/Kneser facts and bibliographic inputs enter as stated published dependencies.
objs: synth_10, lem:johnson-kneser-adjacency-eigenvalue, lem:classical-kneser-spectrum, lem:classical-johnson-decomposition
bib: Delsarte1973, BrouwerCohenNeumaier1989, Filmus2016, BrouwerEtAl2018, FuSamiiWang2026, ClubSandwich2026, Sandwich2026
home_objs: lem:johnson-kneser-adjacency-eigenvalue, lem:classical-kneser-spectrum, lem:classical-johnson-decomposition
