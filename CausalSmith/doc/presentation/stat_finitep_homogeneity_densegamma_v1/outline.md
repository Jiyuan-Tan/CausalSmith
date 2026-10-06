# Title
**Testing treatment effect homogeneity under finite conditional moments**

**Contribution statement.** The paper establishes sharp minimax separation rates for constancy of the conditional mean treatment effect under known uniform design, fixed overlap, independently specified Hölder smoothness, and conditional moments of order between one and two, and characterizes their comparison with bounded outcomes and supplied propensity scores.

env_overrides: prop:bounded-submodel-comparison=propositionv, def:explicit-score-ledger=algorithmv, def:calibration-handle=algorithmv, def:mean-handle=algorithmv, def:converse-handle=algorithmv, def:oracle-handle=algorithmv, def:copula-frame-priors=algorithmv

notation_gaps: \lambda=the frozen definitions use Lebesgue measure without an anchored introduction, \mathcal H^\alpha(20)=the Hölder ball needs an anchored definition with a consistent radius convention, \mathcal H^\beta(20)=the same Hölder-ball family needs its baseline instance resolved, \mathcal H^\gamma(20)=the same Hölder-ball family needs its effect instance resolved, [f]_\lambda=the almost-everywhere equivalence-class notation needs an anchored introduction, \mathcal E_P=the propensity equivalence class needs an anchored introduction, \mathcal G_{0,P}=the baseline arm-mean equivalence class needs an anchored introduction, \mathcal G_{1,P}=the treated arm-mean equivalence class needs an anchored introduction, Q_{a,P}(dy\mid x)=the conditional arm outcome kernels need an anchored introduction, \mathcal V=the public exponent domain needs an anchored definition, \mathcal W=the matched smoothness domain needs an anchored definition, d(P)=the population distance from the unknown-constant null needs an anchored definition, D_v=the original model maximum needs an anchored definition, D_w^{\mathrm b}=the bounded model maximum needs an anchored definition, D_w^{\mathrm{bin}}=the signed-binary model maximum needs an anchored definition, d_0=the fixed positive witness-distance constant needs an anchored definition, \mathcal D_n=the original-record sample needs an anchored introduction, U=the independent public uniform seed needs an anchored introduction, \mathsf R_n(P,\phi)=the rejection expectation needs an anchored introduction preceding its use in risk definitions, \phi^{\mathrm e}=the admissible supplied-continuous-function test carrier needs an anchored definition, \mathsf R_n^{\mathrm e}(P,\phi^{\mathrm e})=the supplied-propensity rejection expectation needs an anchored introduction before the same-class risk, \ell_T(Y_i)=the clipping operator needs an anchored definition, \theta_P(c)=the score expectation needs an anchored definition, g_{r,1}=the singleton projection of the symmetric pair kernel needs an anchored definition, \operatorname{TV}=the total-variation convention needs an anchored definition, \chi^2=the directed chi-square-divergence convention needs an anchored definition, \pi_0=the generic null-prior shorthand needs an anchored introduction, \pi_1=the generic alternative-prior shorthand needs an anchored introduction, P_0=the conditional augmented null-mixture law needs an anchored introduction distinguishing it from the paired-tent null law, P_1=the conditional augmented alternative-mixture law needs an anchored introduction, Q=the normalized intermediate law needs an anchored introduction, \mathcal A=the conditional first-component likelihood budget needs an anchored introduction, \mathcal B=the conditional second-component likelihood budget needs an anchored introduction, \mathcal D_{\partial}=the boundary disclosure needs an anchored introduction, \overline P_1^{(n)}=the paired-tent alternative mixture needs an anchored introduction, P_0^{\mathrm b}=the signed-binary paired-tent null needs an anchored introduction, \pi_1^{\mathrm b}=the signed-binary paired-tent alternative prior needs an anchored introduction, \overline P_{1,\mathrm b}^{(n)}=the signed-binary paired-tent mixture needs an anchored introduction, \psi_{n,v}=the calibration-theorem rule name needs an anchored identification with the explicit rule, R_{\mathrm{att}}(n,v)=the attainable separation formula has a theorem-only introduction, C^{\mathrm{att}}_v=the explicit attainment multiplier has a theorem-only introduction, N^{\mathrm{att}}_v=the explicit attainment threshold has a theorem-only introduction, B_*=the attainment bias constant has a theorem-only introduction, D_*=the attainment summation constant has a theorem-only introduction, L_*=the attainment singleton constant has a theorem-only introduction, G_*=the attainment pair constant has a theorem-only introduction, A_*=the attainment covariance constant has a theorem-only introduction, A(x)=the geometric-sum factor has a theorem-only introduction, s_0=the minimum smoothness has a theorem-only introduction, \eta_0=the increment summability exponent has a theorem-only introduction, E_{\mathrm b}=the bounded separation exponent has a theorem-only introduction, c^{\mathrm e}_v=the supplied-propensity lower multiplier needs an anchored introduction reconciling its superscript placement with c_v^{\mathrm e}, C^{\mathrm e}_v=the supplied-propensity upper multiplier needs an anchored introduction reconciling its superscript placement with C_v^{\mathrm e}, c_v^{\mathrm e}=the broader supplied-propensity lower multiplier has a theorem-only introduction, C_v^{\mathrm e}=the broader supplied-propensity upper multiplier has a theorem-only introduction, N^{\mathrm e}_v=the supplied-propensity nonempty-power threshold has a theorem-only introduction, N_v^{\mathrm e}=the broader supplied-propensity threshold has a theorem-only introduction, u=the constant histogram direction has a theorem-only introduction, C_J=the constant-removing projection matrix has a theorem-only introduction, R_i(f)=the supplied-function inverse-propensity score has a theorem-only introduction, V_b(f)=the supplied-function block vector has a theorem-only introduction, b_T=the broader supplied-propensity clipping-bias bound has a theorem-only introduction, G(v)=the same-class radius-ratio exponent has a theorem-only introduction, \pi^{\mathrm b}_{0,n,v}=the branchwise bounded null prior needs an anchored introduction, \pi^{\mathrm b}_{1,n,v}=the branchwise bounded alternative prior needs an anchored introduction, \mathbb P^{\mathrm b}_{\nu,n,v}=the bounded complete-record mixture needs an anchored introduction, \mathbb P_{\pi,n}=the generic finite-prior complete-record mixture needs an anchored introduction, \operatorname{supp}_+(\pi)=positive-weight finite-prior support needs an anchored definition, N(v)=the tuple-dependent bounded-prior exclusion threshold needs an anchored introduction, Y(0)=the potential-outcome coordinate needs an anchored introduction consistent with dy_0, Y(1)=the potential-outcome coordinate needs an anchored introduction consistent with dy_1

# Notation

Rows marked “Gap” require a presentation definition immediately before their first use. Named local construction quantities resolve through their containing anchored definition; theorem-only introductions remain explicit gaps.

| Note symbol | Paper notation | Defining property in one phrase | Home |
|---|---|---|---|
| \(P\) | \(P\) | Original-record probability law belonging to the stipulated model | def:model |
| \(P_X\) | \(P_X\) | Covariate marginal of the original-record law | def:model |
| \(X\) | \(X\) | Covariate coordinate on the unit interval | def:original-record-experiment |
| \(A\) | \(A\) | Binary treatment coordinate | def:original-record-experiment |
| \(Y\) | \(Y\) | Observed real outcome coordinate | def:original-record-experiment |
| \(\lambda\) | \(\lambda\) | Lebesgue probability measure on the unit interval | Gap |
| \(\mathcal H^\alpha(20)\) | \(\mathcal H^\alpha(20)\) | Continuous functions with sup norm and \(\alpha\)-Hölder constant at most twenty | Gap |
| \(\mathcal H^\beta(20)\) | \(\mathcal H^\beta(20)\) | Continuous functions with sup norm and \(\beta\)-Hölder constant at most twenty | Gap |
| \(\mathcal H^\gamma(20)\) | \(\mathcal H^\gamma(20)\) | Continuous functions with sup norm and \(\gamma\)-Hölder constant at most twenty | Gap |
| \([f]_\lambda\) | \([f]_\lambda\) | Equivalence class of a function under Lebesgue almost-everywhere equality | Gap |
| \([g]_\lambda\) | \([g]_\lambda\) | Equivalence class under the same Lebesgue convention | Gap |
| \([g_0]_\lambda\) | \([g_0]_\lambda\) | Equivalence class of the baseline mean representative | Gap |
| \([g_1]_\lambda\) | \([g_1]_\lambda\) | Equivalence class of the treated mean representative | Gap |
| \([m_{0,P}+t]_\lambda\) | \([m_{0,P}+t]_\lambda\) | Equivalence class of the baseline mean plus an effect function | Gap |
| \(\mathcal E_P\) | \(\mathcal E_P\) | Propensity function equivalence class | Gap |
| \(\mathcal G_{0,P}\) | \(\mathcal G_{0,P}\) | Baseline conditional arm-mean equivalence class | Gap |
| \(\mathcal G_{1,P}\) | \(\mathcal G_{1,P}\) | Treated conditional arm-mean equivalence class | Gap |
| \(Q_{a,P}(dy\mid x)\) | \(Q_{a,P}(dy\mid x)\) | Conditional outcome probability kernel in arm \(a\) | Gap |
| \(e_P\) | \(e_P\) | Continuous representative of the propensity class | def:model |
| \(m_{0,P}\) | \(m_{0,P}\) | Continuous representative of the baseline arm mean | def:model |
| \(m_{1,P}\) | \(m_{1,P}\) | Continuous representative of the treated arm mean | def:model |
| \(\tau_P\) | \(\tau_P\) | Canonical difference between treated and baseline mean representatives | def:model |
| \(v=(p,\alpha,\beta,\gamma)\) | \(v=(p,\alpha,\beta,\gamma)\) | Public tuple of moment and primitive smoothness exponents | def:model |
| \(w=(\alpha,\beta,\gamma)\) | \(w=(\alpha,\beta,\gamma)\) | Matched primitive smoothness tuple | def:bounded-model |
| \(\mathcal V\) | \(\mathcal V\) | Admissible domain of public moment and smoothness tuples | Gap |
| \(\mathcal W\) | \(\mathcal W\) | Admissible domain of matched smoothness tuples | Gap |
| \(C([0,1])\) | \(C([0,1])\) | Continuous real functions on the unit interval with the uniform topology | def:model |
| \(\mathcal M_v\) | \(\mathcal M_v\) | Original-record laws satisfying the stipulated primitive restrictions | def:model |
| \(\mathbb Q_P(dx,dy_0,dy_1,da)\) | \(\mathbb Q_P(dx,dy_0,dy_1,da)\) | Potential-outcome completion with conditionally independent assignment and outcomes | def:causal-completion |
| \(Y(0)\) | \(Y(0)\) | Baseline potential outcome in the causal completion | Gap |
| \(Y(1)\) | \(Y(1)\) | Treated potential outcome in the causal completion | Gap |
| \(H_0(v)\) | \(H_0(v)\) | Original-model laws with an unknown constant mean effect | def:null |
| \(d(P)\) | \(d(P)\) | Population Lebesgue \(L_2\) distance of the effect from its average | Gap |
| \(D_v\) | \(D_v\) | Supremum of the distance over the original model | Gap |
| \(d_0\) | \(d_0\) | Fixed positive distance supplied by a legal model witness | Gap |
| \(\mathcal M^{\mathrm b}_w\) | \(\mathcal M^{\mathrm b}_w\) | Matched model with outcomes bounded in absolute value by one | def:bounded-model |
| \(\mathcal M^{\mathrm{bin}}_w\) | \(\mathcal M^{\mathrm{bin}}_w\) | Matched model with signed-binary outcomes | def:binary-model |
| \(\mathcal M_w^{\mathrm b}\) | \(\mathcal M_w^{\mathrm b}\) | Frozen alternative placement of the bounded-model index | def:bounded-model |
| \(\mathcal M_w^{\mathrm{bin}}\) | \(\mathcal M_w^{\mathrm{bin}}\) | Frozen alternative placement of the signed-binary model index | def:binary-model |
| \(H_0^{\mathrm b}(w)\) | \(H_0^{\mathrm b}(w)\) | Bounded-model laws with an unknown constant mean effect | def:bounded-null |
| \(H_0^{\mathrm{bin}}(w)\) | \(H_0^{\mathrm{bin}}(w)\) | Signed-binary laws with an unknown constant mean effect | def:binary-null |
| \(D_w^{\mathrm b}\) | \(D_w^{\mathrm b}\) | Maximum distance over the bounded model | Gap |
| \(D_w^{\mathrm{bin}}\) | \(D_w^{\mathrm{bin}}\) | Maximum distance over the signed-binary model | Gap |
| \(\phi\) | \(\phi\) | Original-record randomized rejection-probability map | def:testing-risk |
| \(\mathcal D_n\) | \(\mathcal D_n\) | Sample of independent original records | Gap |
| \(U\) | \(U\) | Independent public uniform randomization variable | Gap |
| \(\mathsf S_{n,P}\) | \(\mathsf S_{n,P}\) | Product experiment combining the independent sample and public seed | def:original-record-experiment |
| \(\mathsf R_n(P,\phi)\) | \(\mathsf R_n(P,\phi)\) | Expected rejection probability in the original-record experiment | Gap |
| \(B_n(v,r)\) | \(B_n(v,r)\) | Minimax type-II error at separation \(r\) under the stipulated size constraint | def:testing-risk |
| \(B_n^{\mathrm b}(w,r)\) | \(B_n^{\mathrm b}(w,r)\) | Corresponding bounded-model minimax type-II error | def:bounded-risk |
| \(B_n^{\mathrm{bin}}(w,r)\) | \(B_n^{\mathrm{bin}}(w,r)\) | Corresponding signed-binary minimax type-II error | def:binary-risk |
| \(r_n^*(v)\) | \(r_n^*(v)\) | Capped original-model critical separation radius | def:critical-radius |
| \(r_n^{*,\mathrm b}(w)\) | \(r_n^{*,\mathrm b}(w)\) | Capped bounded-model critical separation radius | def:bounded-radius |
| \(r_n^{*,\mathrm{bin}}(w)\) | \(r_n^{*,\mathrm{bin}}(w)\) | Capped signed-binary critical separation radius | def:binary-radius |
| \(\Delta_n(v)\) | \(\Delta_n(v)\) | Original-to-bounded capped-radius ratio at matched smoothness | def:comparison-handle |
| \(\mathcal T\) | \(\mathcal T\) | Tuples below moment order two with diverging original-to-bounded radius ratio | def:tail-region |
| \(\mathcal E\) | \(\mathcal E\) | Tuples with uniformly bounded original-to-bounded radius ratio | def:equality-region |
| \(\phi^{\mathrm e}\) | \(\phi^{\mathrm e}\) | Randomized test receiving the whole true continuous propensity | Gap |
| \(\mathsf R_n^{\mathrm e}(P,\phi^{\mathrm e})\) | \(\mathsf R_n^{\mathrm e}(P,\phi^{\mathrm e})\) | Rejection expectation with the true propensity supplied | Gap |
| \(B_n^{\mathrm e}(v,r)\) | \(B_n^{\mathrm e}(v,r)\) | Supplied-propensity minimax type-II error on the original shared class | def:oracle-risk |
| \(r_n^{*,\mathrm e}(v)\) | \(r_n^{*,\mathrm e}(v)\) | Supplied-propensity capped radius on the original shared class | def:oracle-radius |
| \(\mathcal R\) | \(\mathcal R\) | Tuples with uniformly bounded unknown-to-supplied propensity radius ratio | def:preservation-region |
| \(\mathcal M_v^{\mathrm{e,br}}\) | \(\mathcal M_v^{\mathrm{e,br}}\) | Supplied-propensity comparison class retaining continuous nuisance carriers and the listed primitive restrictions | def:oracle-broad-model |
| \(D_v^{\mathrm{e,br}}\) | \(D_v^{\mathrm{e,br}}\) | Maximum distance over the broader continuous-carrier class | def:oracle-broad-model |
| \(H_0^{\mathrm{e,br}}(v)\) | \(H_0^{\mathrm{e,br}}(v)\) | Broader-class laws with an unknown constant mean effect | def:oracle-broad-null |
| \(B_n^{\mathrm{e,br}}(v,r)\) | \(B_n^{\mathrm{e,br}}(v,r)\) | Broader-class supplied-propensity minimax type-II error | def:oracle-broad-risk |
| \(r_n^{*,\mathrm{e,br}}(v)\) | \(r_n^{*,\mathrm{e,br}}(v)\) | Broader-class supplied-propensity capped critical radius | def:oracle-broad-radius |
| \(q\) | \(q\) | Moment-dependent exponent \((p-1)/p\) | def:sharp-frontier-scales |
| \(S\) | \(S\) | Sum of propensity and baseline smoothness exponents | def:sharp-frontier-scales |
| \(D_p\) | \(D_p\) | Denominator defining the rough-confounding separation exponent | def:sharp-frontier-scales |
| \(E_0(p)\) | \(E_0(p)\) | Supplied-propensity separation exponent at fixed smoothness tuple | def:sharp-frontier-scales |
| \(E_4(p)\) | \(E_4(p)\) | Rough-confounding separation exponent at fixed smoothness tuple | def:sharp-frontier-scales |
| \(F(p)\) | \(F(p)\) | Scalar identifying the comparison of the two separation exponents | def:sharp-frontier-scales |
| \(E(p)\) | \(E(p)\) | Minimum of the two separation exponents | def:sharp-frontier-scales |
| \(E_0\) | \(E_0\) | Local version of the supplied-propensity exponent | def:explicit-score-ledger |
| \(E_4\) | \(E_4\) | Local version of the rough-confounding exponent | def:explicit-score-ledger |
| \(E\) | \(E\) | Local minimum exponent used for public tuning | def:explicit-score-ledger |
| \(t\) | \(t\) | Moment-dependent variance-growth exponent \((2-p)/(p-1)\) | def:explicit-score-ledger |
| \(\rho_n(v)\) | \(\rho_n(v)\) | Original-model power separation scale | def:sharp-frontier-scales |
| \(\rho_n^{\mathrm b}(w)\) | \(\rho_n^{\mathrm b}(w)\) | Matched bounded power separation scale | def:sharp-frontier-scales |
| \(\rho_n^{\mathrm e}(v)\) | \(\rho_n^{\mathrm e}(v)\) | Supplied-propensity power separation scale | def:oracle-handle |
| \(H_{\mathrm{fine}}\) | \(H_{\mathrm{fine}}\) | Fixed multiplier for the converse fine rank | def:sharp-frontier-scales |
| \(N_{\mathrm{low}}(v)\) | \(N_{\mathrm{low}}(v)\) | Public threshold for the rough lower-bound construction | def:sharp-frontier-scales |
| \(k_v\) | \(k_v\) | Public rough-converse distance multiplier | def:sharp-frontier-scales |
| \(c_0^{\mathrm e}\) | \(c_0^{\mathrm e}\) | Public paired-tent lower-distance multiplier | def:sharp-frontier-scales |
| \(c_v\) | \(c_v\) | Branchwise original-model lower-radius multiplier | def:sharp-frontier-scales |
| \(c_w^{\mathrm b}\) | \(c_w^{\mathrm b}\) | Matched bounded-model lower-radius multiplier | def:sharp-frontier-scales |
| \(c_{(2,w)}\) | \(c_{(2,w)}\) | Original lower multiplier evaluated at moment order two | def:sharp-frontier-scales |
| \(C_v\) | \(C_v\) | Original-model upper-radius multiplier selected from attainment | def:sharp-frontier-scales |
| \(C_w^{\mathrm b}\) | \(C_w^{\mathrm b}\) | Matched bounded-model upper-radius multiplier | def:sharp-frontier-scales |
| \(N_v\) | \(N_v\) | Public original-model nonempty-power threshold | def:sharp-frontier-scales |
| \(N_w^{\mathrm b}\) | \(N_w^{\mathrm b}\) | Public bounded-model nonempty-power threshold | def:sharp-frontier-scales |
| \(\phi^*_{n,v}\) | \(\phi^*_{n,v}\) | Total calibrated original-record test | def:sharp-frontier-scales |
| \(\phi^{*,\mathrm b}_{n,w}\) | \(\phi^{*,\mathrm b}_{n,w}\) | Same total test evaluated at moment order two | def:sharp-frontier-scales |
| \(I_{j,J}\) | \(I_{j,J}\) | Histogram cells with the final cell containing the right endpoint | def:projection |
| \(F_J(x)\) | \(F_J(x)\) | Normalized histogram feature vector | def:projection |
| \(\Pi_J(x,z)\) | \(\Pi_J(x,z)\) | Histogram projection kernel | def:projection |
| \((\Pi_J f)(x)\) | \((\Pi_J f)(x)\) | Histogram projection of a function | def:projection |
| \(J_{\mathrm c}\) | \(J_{\mathrm c}\) | Public coarse histogram rank | def:explicit-score-ledger |
| \(J_{\mathrm f}\) | \(J_{\mathrm f}\) | Public fine histogram rank | def:explicit-score-ledger |
| \(s_n\) | \(s_n\) | Size of each evaluation block | def:blocks |
| \(\mathcal I_1\) | \(\mathcal I_1\) | First evaluation block | def:blocks |
| \(\mathcal I_2\) | \(\mathcal I_2\) | Second evaluation block | def:blocks |
| \(\ell_T(Y_i)\) | \(\ell_T(Y_i)\) | Outcome clipped to the interval with endpoints minus and plus \(T\) | Gap |
| \(H_{b,T}(c)\) | \(H_{b,T}(c)\) | Blockwise single-record histogram score | def:score-family |
| \(U_{b,G,T}(c)\) | \(U_{b,G,T}(c)\) | Blockwise ordered-pair correction score | def:score-family |
| \(G:[0,1]^2\to\mathbb R\) | \(G:[0,1]^2\to\mathbb R\) | Pair-score kernel supplied to the correction family | def:score-family |
| \(M\) | \(M\) | Local notation for the coarse rank | def:explicit-score-ledger |
| \(K\) | \(K\) | Local notation for the fine rank | def:explicit-score-ledger |
| \(s\) | \(s\) | Local notation for evaluation-block size | def:explicit-score-ledger |
| \(a\) | \(a\) | Public target scale used in the attainment tuning | def:explicit-score-ledger |
| \(\mathcal R(x)\) | \(\mathcal R(x)\) | Upper dyadic rounding of a positive number | def:explicit-score-ledger |
| \(T_0\) | \(T_0\) | Main public clipping cutoff | def:explicit-score-ledger |
| \(V_0\) | \(V_0\) | Main clipping second-moment bound | def:explicit-score-ledger |
| \(\lambda_0\) | \(\lambda_0\) | Public exponent allocating multiresolution clipping bias | def:explicit-score-ledger |
| \(L\) | \(L\) | Number of dyadic increments in the score construction | def:explicit-score-ledger |
| \(R_j\) | \(R_j\) | Rank at dyadic increment \(j\) | def:explicit-score-ledger |
| \(D_j\) | \(D_j\) | Difference between successive histogram projections | def:explicit-score-ledger |
| \(T_j\) | \(T_j\) | Public clipping cutoff for increment \(j\) | def:explicit-score-ledger |
| \(V_j\) | \(V_j\) | Increment-specific clipping second-moment bound | def:explicit-score-ledger |
| \(a_j\) | \(a_j\) | Propensity approximation bound for increment \(j\) | def:explicit-score-ledger |
| \(d_j\) | \(d_j\) | Increment-specific smoothness and clipping bound | def:explicit-score-ledger |
| \(Z_b(c)\) | \(Z_b(c)\) | Affine corrected block score indexed by the candidate constant | def:explicit-score-ledger |
| \(Z_{b,0}\) | \(Z_{b,0}\) | Outcome coefficient of the affine block score | def:calibration-handle |
| \(Z_{b,A}\) | \(Z_{b,A}\) | Constant-effect coefficient of the affine block score | def:calibration-handle |
| \(B\) | \(B\) | Public deterministic original-mean bias bound | def:explicit-score-ledger |
| \(L_1\) | \(L_1\) | Public singleton-projection covariance bound | def:explicit-score-ledger |
| \(L_2\) | \(L_2\) | Public canonical-pair covariance bound | def:explicit-score-ledger |
| \(\mathfrak b_{n,v}\) | \(\mathfrak b_{n,v}\) | Named public bias ledger | def:explicit-score-ledger |
| \(\Lambda_{n,v}\) | \(\Lambda_{n,v}\) | Named public covariance ledger | def:explicit-score-ledger |
| \(h_{n,v}\) | \(h_{n,v}\) | Upper-dyadic public rejection cutoff | def:explicit-score-ledger |
| \(W(c)\) | \(W(c)\) | Inner product of independent block scores | def:explicit-score-ledger |
| \(\theta_P(c)\) | \(\theta_P(c)\) | Population expectation of the corrected block score | Gap |
| \(e_K\) | \(e_K\) | Fine-rank histogram projection of the propensity | def:mean-handle |
| \(w_K\) | \(w_K\) | Propensity weight formed from the true and projected propensities | def:mean-handle |
| \(h_r\) | \(h_r\) | Raw single-record kernel for affine coefficient \(r\) | def:mean-handle |
| \(g_r\) | \(g_r\) | Raw symmetric pair kernel for affine coefficient \(r\) | def:mean-handle |
| \(g_{r,1}\) | \(g_{r,1}\) | Singleton projection of the raw symmetric pair kernel | Gap |
| \(h_r\!\times h_{r'}\) | \(h_r\!\times h_{r'}\) | Population inner-product contraction of two single-record kernels | def:mean-handle |
| \(h_r\!\times g_{r'}\) | \(h_r\!\times g_{r'}\) | Population contraction of a single-record and pair kernel | def:mean-handle |
| \(g_r\!\times h_{r'}\) | \(g_r\!\times h_{r'}\) | Population contraction of a pair and single-record kernel | def:mean-handle |
| \(g_r\!\times g_{r'}\) | \(g_r\!\times g_{r'}\) | Population contraction of two pair kernels | def:mean-handle |
| \(h_c\) | \(h_c\) | Candidate-constant combination of single-record affine kernels | def:mean-handle |
| \(g_c\) | \(g_c\) | Candidate-constant combination of pair affine kernels | def:mean-handle |
| \(Z_0(c)\) | \(Z_0(c)\) | First-block score under the mean-handle indexing convention | def:mean-handle |
| \(Z_1(c)\) | \(Z_1(c)\) | Block score under the containing definition’s indexing convention | def:mean-handle |
| \(Z_2(c)\) | \(Z_2(c)\) | Second-block score under the explicit-rule indexing convention | def:explicit-score-ledger |
| \(C\) | \(C\) | Fixed simultaneous profiling-bound multiplier | Gap |
| \(\psi_{n,v}\) | \(\psi_{n,v}\) | Calibration-theorem name for the explicit original-record rule | Gap |
| \(R_{\mathrm{att}}(n,v)\) | \(R_{\mathrm{att}}(n,v)\) | Separation assembled from projection bias and covariance bounds | Gap |
| \(s_0\) | \(s_0\) | Minimum of the three primitive smoothness exponents | Gap |
| \(\eta_0\) | \(\eta_0\) | Moment-dependent increment summability exponent | Gap |
| \(A(x)\) | \(A(x)\) | Reciprocal geometric-series denominator | Gap |
| \(B_*\) | \(B_*\) | Explicit attainment bias constant | Gap |
| \(D_*\) | \(D_*\) | Explicit attainment summation constant | Gap |
| \(L_*\) | \(L_*\) | Explicit attainment singleton constant | Gap |
| \(G_*\) | \(G_*\) | Explicit attainment canonical-pair constant | Gap |
| \(A_*\) | \(A_*\) | Explicit attainment covariance constant | Gap |
| \(C^{\mathrm{att}}_v\) | \(C^{\mathrm{att}}_v\) | Fully evaluable attainment multiplier | Gap |
| \(N^{\mathrm{att}}_v\) | \(N^{\mathrm{att}}_v\) | Fully evaluable attainment nonempty-power threshold | Gap |
| \(C^{\mathrm{att}}_{(2,w)}\) | \(C^{\mathrm{att}}_{(2,w)}\) | Attainment multiplier evaluated at the bounded tuple | Gap |
| \(N^{\mathrm{att}}_{(2,w)}\) | \(N^{\mathrm{att}}_{(2,w)}\) | Attainment threshold evaluated at the bounded tuple | Gap |
| \(E_{\mathrm b}\) | \(E_{\mathrm b}\) | Minimum bounded-model separation exponent | Gap |
| \(\mathsf T\) | \(\mathsf T\) | Normalized six-category conditional original-record table | def:marked-table |
| \(\xi\) | \(\xi\) | Table coordinate governing treatment probabilities | def:marked-table |
| \(\upsilon\) | \(\upsilon\) | Table coordinate governing marked outcome signs | def:marked-table |
| \(\zeta\) | \(\zeta\) | Table coordinate coupling treatment and marked outcome signs | def:marked-table |
| \(\varepsilon\) | \(\varepsilon\) | Rare-mark probability in the conditional record table | def:marked-table |
| \(L>0\) | \(L>0\) | Positive mark magnitude in the conditional record table | def:marked-table |
| \(f_i(x)\) | \(f_i(x)\) | Continuous sine-cosine frame coordinate with adjacent-cell support | def:frame-handle |
| \(a=(a_0,\ldots,a_K)\) | \(a=(a_0,\ldots,a_K)\) | Coefficient vector defining a frame field | def:frame-handle |
| \(a_i\) | \(a_i\) | Coordinate of the frame coefficient vector | def:frame-handle |
| \(\kappa\) | \(\kappa\) | Fixed copula-coupling amplitude | def:copula-frame-priors |
| \(b_\triangle(t)\) | \(b_\triangle(t)\) | Unit-interval triangular tent function | def:copula-frame-priors |
| \(\sigma_j\) | \(\sigma_j\) | Independent fair coarse-cell signs | def:copula-frame-priors |
| \(g_\sigma\) | \(g_\sigma\) | Oppositely signed tent field on paired coarse cells | def:copula-frame-priors |
| \(\widetilde g_\sigma(x)\) | \(\widetilde g_\sigma(x)\) | Squared-frame interpolation of the coarse tent field | def:copula-frame-priors |
| \(\lambda_i\) | \(\lambda_i\) | Propensity frame coefficient sign | def:copula-frame-priors |
| \(\eta_i\) | \(\eta_i\) | Marked-outcome frame coefficient sign | def:copula-frame-priors |
| \(u\) | \(u\) | Marked-outcome coefficient amplitude in the copula construction | def:copula-frame-priors |
| \(t_\nu(x)\) | \(t_\nu(x)\) | Branch-specific deterministic correction to the table interaction | def:copula-frame-priors |
| \(\pi^{K,M}_{\nu;v,a,u,\varepsilon,L}\) | \(\pi^{K,M}_{\nu;v,a,u,\varepsilon,L}\) | Finite prior obtained by pushing coefficient draws into original-record laws | def:copula-frame-priors |
| \(b\) | \(b\) | Baseline amplitude used in the legality tuning | Gap |
| \(\pi_0\) | \(\pi_0\) | Null branch of a generic copula-frame prior pair | Gap |
| \(\pi_1\) | \(\pi_1\) | Alternative branch of a generic copula-frame prior pair | Gap |
| \(\varepsilon_{n,v}\) | \(\varepsilon_{n,v}\) | Selected branchwise rare-mark probability | def:converse-handle |
| \(L_{n,v}\) | \(L_{n,v}\) | Selected branchwise outcome mark magnitude | def:converse-handle |
| \(N\) | \(N\) | Even paired-tent rank in the fallback converse | def:converse-handle |
| \(h\) | \(h\) | Paired-tent cell width | def:converse-handle |
| \(\pi_{0,n,v}\) | \(\pi_{0,n,v}\) | Selected finite null mixing law | def:converse-handle |
| \(\pi_{1,n,v}\) | \(\pi_{1,n,v}\) | Selected finite alternative mixing law | def:converse-handle |
| \(\mathbb P_{0,n,v}\) | \(\mathbb P_{0,n,v}\) | Complete independent-record null mixture | def:converse-handle |
| \(\mathbb P_{1,n,v}\) | \(\mathbb P_{1,n,v}\) | Complete independent-record alternative mixture | def:converse-handle |
| \(\operatorname{TV}\) | \(\operatorname{TV}\) | Supremum event-probability difference between probability laws | Gap |
| \(\chi^2\) | \(\chi^2\) | Directed chi-square divergence between probability laws | Gap |
| \(Q\) | \(Q\) | Normalized intermediate augmented probability law | Gap |
| \(P_0\) | \(P_0\) | Null law in the local lower-bound comparison | Gap |
| \(P_1\) | \(P_1\) | Alternative augmented mixture law in the component comparison | Gap |
| \(\mathcal A\) | \(\mathcal A\) | Conditional first-component chi-square exponent budget | Gap |
| \(\mathcal B\) | \(\mathcal B\) | Conditional second-component chi-square exponent budget | Gap |
| \(B_i\) | \(B_i\) | Indicator that record \(i\) has a nonzero outcome mark | Gap |
| \(\mathcal D_{\partial}\) | \(\mathcal D_{\partial}\) | Disclosure of coefficient pairs at coarse-cell boundary nodes | Gap |
| \(\mathbb P_0\) | \(\mathbb P_0\) | Complete-record null mixture in the rough lower comparison | Gap |
| \(\mathbb P_1\) | \(\mathbb P_1\) | Complete-record alternative mixture in the rough lower comparison | Gap |
| \(\overline P_1^{(n)}\) | \(\overline P_1^{(n)}\) | Complete-record paired-tent alternative mixture | Gap |
| \(P_0^{\mathrm b}\) | \(P_0^{\mathrm b}\) | Signed-binary paired-tent null law | Gap |
| \(\pi_1^{\mathrm b}\) | \(\pi_1^{\mathrm b}\) | Normalized finite signed-binary alternative prior | Gap |
| \(\overline P_{1,\mathrm b}^{(n)}\) | \(\overline P_{1,\mathrm b}^{(n)}\) | Complete-record signed-binary alternative mixture | Gap |
| \(\pi=\sum_{j=1}^{k}\omega_j\delta_{P_j}\) | \(\pi=\sum_{j=1}^{k}\omega_j\delta_{P_j}\) | Normalized finite probability prior on original-record laws | Gap |
| \(\omega_j\) | \(\omega_j\) | Nonnegative prior weight attached to support law \(P_j\) | Gap |
| \(P_j\) | \(P_j\) | Original-record law in a finite prior’s support | Gap |
| \(\operatorname{supp}_+(\pi)\) | \(\operatorname{supp}_+(\pi)\) | Support laws receiving strictly positive prior weight | Gap |
| \(\mathbb P_{\pi,n}\) | \(\mathbb P_{\pi,n}\) | Complete-record mixture induced by a finite probability prior | Gap |
| \(N(v)\) | \(N(v)\) | Tuple-dependent threshold for bounded-prior total-variation separation | Gap |
| \(\pi^{\mathrm b}_{0,n,v}\) | \(\pi^{\mathrm b}_{0,n,v}\) | Selected normalized bounded null prior | Gap |
| \(\pi^{\mathrm b}_{1,n,v}\) | \(\pi^{\mathrm b}_{1,n,v}\) | Selected normalized bounded alternative prior | Gap |
| \(\pi^{\mathrm b}_{\nu,n,v}\) | \(\pi^{\mathrm b}_{\nu,n,v}\) | Branch-indexed selected bounded prior | Gap |
| \(\mathbb P^{\mathrm b}_{\nu,n,v}\) | \(\mathbb P^{\mathrm b}_{\nu,n,v}\) | Complete-record mixture of the selected bounded prior | Gap |
| \(\widetilde e\) | \(\widetilde e\) | Supplied continuous propensity clipped to the overlap interval | def:oracle-handle |
| \(R_i\) | \(R_i\) | Clipped inverse-propensity original-record score | def:oracle-handle |
| \(V_b\) | \(V_b\) | Constant-centered histogram score averaged within block \(b\) | def:oracle-handle |
| \(b\) | \(b\) | Public clipping-bias bound in the supplied-propensity construction | def:oracle-handle |
| \(\Lambda\) | \(\Lambda\) | Public supplied-propensity covariance bound | def:oracle-handle |
| \(\phi^{*,\mathrm e}_{n,v}\) | \(\phi^{*,\mathrm e}_{n,v}\) | Total calibrated supplied-propensity test | def:oracle-handle |
| \(c^{\mathrm e}_v\) | \(c^{\mathrm e}_v\) | Same-class supplied-propensity lower-radius multiplier | Gap |
| \(C^{\mathrm e}_v\) | \(C^{\mathrm e}_v\) | Same-class supplied-propensity upper-radius multiplier | Gap |
| \(N^{\mathrm e}_v\) | \(N^{\mathrm e}_v\) | Same-class supplied-propensity nonempty-power threshold | Gap |
| \(c_v^{\mathrm e}\) | \(c_v^{\mathrm e}\) | Broader-class supplied-propensity lower-radius multiplier | Gap |
| \(C_v^{\mathrm e}\) | \(C_v^{\mathrm e}\) | Broader-class supplied-propensity upper-radius multiplier | Gap |
| \(N_v^{\mathrm e}\) | \(N_v^{\mathrm e}\) | Broader-class supplied-propensity nonempty-power threshold | Gap |
| \(u=J^{-1/2}(1,\ldots,1)^T\) | \(u=J^{-1/2}(1,\ldots,1)^T\) | Unit histogram direction representing constant functions | Gap |
| \(C_J\) | \(C_J\) | Orthogonal matrix projection removing the constant direction | Gap |
| \(\widetilde f(x)\) | \(\widetilde f(x)\) | Supplied continuous function clipped to the overlap interval | Gap |
| \(R_i(f)\) | \(R_i(f)\) | Clipped inverse-propensity score evaluated at supplied function \(f\) | Gap |
| \(V_b(f)\) | \(V_b(f)\) | Constant-centered block vector evaluated at supplied function \(f\) | Gap |
| \(b_T\) | \(b_T\) | Public clipping-bias bound for the broader-class test | Gap |
| \(G(v)\) | \(G(v)\) | Nonnegative exponent governing the same-class unknown-to-supplied radius ratio | Gap |

# Sections

## section: Introduction

Plan the abstract and introduction for the final drafting stage. Lead with the econometric question of detecting departures from a constant conditional mean treatment effect when outcome distributions satisfy a public conditional moment envelope. Present the contribution through matched population separation rates, the bounded-outcome comparison, and the value of supplying the assignment function. State the one-dimensional uniform-design, overlap, smoothness, and moment domain affirmatively, and explain the distinction between a whole-null size guarantee and power at a nonempty separated alternative. Include one factual sentence directing readers to the appendix verification note. Introduce early symbols through plain-word glosses or use words.

objs: none

bib: none

home_objs: none
## section: Related work

Position the paper first against direct mean-effect homogeneity tests: Crump–Hotz–Imbens–Mitnik’s sieve Wald analysis, Lu–Song’s orthogonal marked empirical process, Lapenta–Strittmatter–Vergara’s integrated conditional moments, Yu’s split-sample zero-variance test, and Dhawan–Guo–Shah’s directional procedure. Compare their stated asymptotic calibration, nuisance-learning, moment, and alternative conditions with this paper’s finite-sample whole-null guarantees and uniform population separation criterion, preserving the supplied source locators. Then connect the quadratic-testing analysis to Ingster–Sapatinas and Comminges–Dalalyan, the projection corrections to higher-order causal estimation through the available Kennedy–Balakrishnan–Robins–Wasserman comparator, and tail handling to robust U-statistics. Distinguish estimation, policy-relevant homogeneity, distributional contrasts, and predictive comparisons by their targets and guarantees. Use the verified bibliography conservatively, with precise source-scope comparisons and a proportionate account of novelty.

objs: none

bib: CrumpHotzImbensMitnik2008Homogeneity, LuSong2026OrthogonalICM, LapentaStrittmatterVergara2026Omnibus, Yu2026VarianceHTE, DhawanGuoShah2026Directional, SantAnna2021DurationHomogeneity, DaiStern2022Rank, DaiShenStern2023Observational, DukesStensrudBrioschiHudson2026Homogeneity, JainLuedtke2026Distributional, AshouriHenderson2026Predictive, IngsterSapatinas2009GoodnessOfFit, CommingesDalalyan2013QuadraticNull, KennedyBalakrishnanRobinsWasserman2024MinimaxCATE, JolyLugosi2016RobustU, Hoeffding1948, Chernozhukov2018, Robinson1988, Levy2021, SanchezBecerra2023, Imai2025, Li2023, CausalSmith2026a

home_objs: none
## section: Setup and assumptions

Define the original records, canonical conditional means, public exponent domains, Hölder convention, and population distance before their first use. Organize the primitive restrictions into design and overlap, independent smoothness, mean caps, and conditional moments. Introduce the unknown-constant null, the original-record randomized experiment, and the capped minimax radius. Place bounded and signed-binary models together with their nulls, risks, and radii as a matched benchmark family. Explain the causal interpretation through the potential-outcome completion, with its auxiliary justification located in the appendix. Resolve notation gaps through grouped presentation definitions immediately before the consuming objects.

objs: ass:uniform, ass:overlap, ass:propensity-smoothness, ass:baseline-smoothness, ass:effect-smoothness, ass:baseline-cap, ass:effect-cap, ass:raw-moment, def:model, ass:null-constancy, def:null, def:causal-completion, def:original-record-experiment, def:testing-risk, def:critical-radius, ass:bounded-outcome, def:bounded-model, ass:binary-outcome, def:binary-model, def:bounded-null, def:binary-null, def:bounded-risk, def:binary-risk, def:bounded-radius, def:binary-radius

bib: Rubin1974, Rosenbaum1983, Imbens2015, Hahn1998

home_objs: ass:uniform, ass:overlap, ass:propensity-smoothness, ass:baseline-smoothness, ass:effect-smoothness, ass:baseline-cap, ass:effect-cap, ass:raw-moment, def:model, ass:null-constancy, def:null, def:causal-completion, def:original-record-experiment, def:testing-risk, def:critical-radius, ass:bounded-outcome, def:bounded-model, ass:binary-outcome, def:binary-model, def:bounded-null, def:binary-null, def:bounded-risk, def:binary-risk, def:bounded-radius, def:binary-radius
## section: Separation rates and the cost of outcome tails

Introduce the public scales and comparison objects as one connected result family, then present the headline matched-rate result and the bounded-to-signed-binary equivalence. Organize the interpretation around the effect-smoothness and rough-confounding regimes, their equality boundary, the original-to-bounded radius ratio, and the moment-order-two face. Give a compact planned regime table using the frozen exponent formulas and their conditions. Keep the finite-sample cap, local uniformity of constants, and nonempty-power thresholds attached to the claims they qualify. Explain the statistical role of tail-essential lower witnesses, with their full construction and quantified finite-prior statement placed in the proof appendix.

objs: def:sharp-frontier-scales, def:comparison-handle, def:tail-region, def:equality-region, prop:bounded-submodel-comparison

bib: none

home_objs: def:sharp-frontier-scales, def:comparison-handle, def:tail-region, def:equality-region, prop:bounded-submodel-comparison
## section: A calibrated test from the original records

Present the central observable procedure in the main body: histogram projection, independent evaluation blocks, corrected affine scores, public rank and clipping selections, and minimization over the unknown constant. Place the explicit procedure in a numbered algorithm box after its score ingredients. Explain how original-mean bias, covariance control, and profiling connect the procedure to whole-null calibration and the attainable separation result, referring to their appendix proofs. Preserve the distinction between the statistical regime boundary and the procedure’s computational branch condition. Include the small-sample zero rule, bin-endpoint convention, and finite public calculations as parts of the specified procedure.

objs: def:projection, def:blocks, def:score-family, def:explicit-score-ledger, thm:whole-null-calibration-resolved

bib: Hoeffding1948, Robinson1988

home_objs: def:projection, def:blocks, def:score-family, def:explicit-score-ledger, thm:whole-null-calibration-resolved
## section: Supplied propensity scores and assignment information

Introduce the supplied-function test carrier and the broader continuous-carrier model before its risk and radius. Present the broader-class supplied-propensity result as the primary result for this experiment, retaining uniform design, overlap, effect smoothness, mean caps, continuous representatives, and the conditional moment envelope. Place its attaining inverse-propensity procedure in the main body. Then introduce the original shared-class risk and radius and use the compatibility result to present the exact same-class preservation boundary as a consequence of the matched rates. Keep broader-class attainment and shared-class radius comparison distinct throughout, including equality regimes and finite-sample saturation.

objs: def:oracle-broad-model, def:oracle-broad-null, def:oracle-broad-risk, def:oracle-broad-radius, def:oracle-handle, def:oracle-risk, def:oracle-radius, def:preservation-region

bib: Horvitz1952, Hirano2003

home_objs: def:oracle-broad-model, def:oracle-broad-null, def:oracle-broad-risk, def:oracle-broad-radius, def:oracle-handle, def:oracle-risk, def:oracle-radius, def:preservation-region
## section: Discussion and extensions

Interpret the paper’s own separation comparisons as benchmarks for sensitivity to outcome tails and assignment information. Explain how matched primitive smoothness distinguishes effect complexity from nuisance complexity, how the supplied-function result supports a broader nuisance scope, and how public finite-sample thresholds translate rate statements into calibrated tests with nonempty power domains. Relate the population target to treatment-effect variance where useful. Include a clearly titled “Limitations and future work” subsection for extensions to unknown covariate design, higher-dimensional covariates, adaptive exponent selection, and estimated supplied functions; frame these as research directions. Keep literature positioning in the related-work section.

objs: none

bib: Levy2021, SanchezBecerra2023

home_objs: none
## section: Appendix: Causal interpretation and benchmark equivalence

Supply the justification for canonical representatives, version invariance, the causal completion, and legal null and separated witnesses. Prove the bounded and signed-binary comparison through mean-preserving randomization, with the original-record test carrier and public randomization made explicit. Introduce any appendix-specific randomization notation immediately before its use. Refer to the main-body benchmark environments through cleveref.

objs: lem:causal-nonempty

bib: Rubin1974, Rosenbaum1983

home_objs: lem:causal-nonempty
## section: Appendix: Bias, covariance, profiling, and attainment

Place the calibration and population-decomposition apparatus before the auxiliary lemmas that consume it. Develop the original-mean bias calculation, singleton and canonical pair projections, all retained contractions, cross-level covariance bounds, and simultaneous affine profiling. Then prove whole-null calibration and the explicit attainable rate, resolving theorem-only constants through grouped presentation definitions before use. Keep the exact public computations and the relation between the two block-index conventions explicit in this technical appendix.

objs: def:calibration-handle, def:mean-handle, lem:original-score-mean-ledger, lem:original-score-covariance-ledger, lem:uniform-affine-profile-bound, thm:original-record-attainable-rate

bib: Hoeffding1948, JolyLugosi2016RobustU

home_objs: def:calibration-handle, def:mean-handle, lem:original-score-mean-ledger, lem:original-score-covariance-ledger, lem:uniform-affine-profile-bound, thm:original-record-attainable-rate
## section: Appendix: Full-record lower bounds and tail essentiality

Introduce divergence conventions and the paired-tent mixture notation before the paired-tent lower bound. Place the normalized marked table, continuous frame, and copula-frame prior algorithm before their legality and complete-record component bounds. Develop the common augmentation, boundary disclosure, intermediate normalized law, occupancy accounting, and likelihood budgets in the order required by the proof. Present the selected converse algorithm after its construction ingredients, then assemble the rough lower bound and the tail-essential result. Resolve finite-prior support and mixture notation before the quantified bounded-prior separation statement, preserving its tuple-dependent threshold and the separate bounded constructions on the moment-order-two face.

objs: lem:paired-tent-full-record-lower, def:marked-table, def:frame-handle, def:copula-frame-priors, lem:copula-frame-legality, lem:full-record-copula-component-bound, def:converse-handle, synth_1, lem:rough-full-record-sharp-lower, thm:tail-essential-full-record-converse

bib: Ingster2003, Tsybakov2009

home_objs: lem:paired-tent-full-record-lower, def:marked-table, def:frame-handle, def:copula-frame-priors, lem:copula-frame-legality, lem:full-record-copula-component-bound, def:converse-handle, synth_1, lem:rough-full-record-sharp-lower, thm:tail-essential-full-record-converse
## section: Appendix: Supplied-propensity proofs and comparison algebra

Prove the supplied-propensity bias and covariance calculations, constant-removing quadratic statistic, finite-sample calibration, and attainment on the broader continuous-carrier class. Connect the common-propensity lower witnesses to both supplied experiments by class inclusion. Complete the algebra for the same-class preservation boundary and the finite-moment versus bounded comparison, including equality points and local uniformity. Use exact internal cleveref targets and preserve external source locators when discussing the familiar quadratic-testing exponent.

objs: thm:heavy-tail-comparison, thm:oracle-frontier-broad-class, thm:oracle-frontier-resolved, thm:exact-propensity-preservation-boundary

bib: IngsterSapatinas2009GoodnessOfFit, Horvitz1952

home_objs: thm:heavy-tail-comparison, thm:oracle-frontier-broad-class, thm:oracle-frontier-resolved, thm:exact-propensity-preservation-boundary
## section: Appendix: Verification note

End the appendix with a concise factual account of the Lean machine-checking scope for the frozen results, separating proved conclusions, stipulated model restrictions, and any cited dependencies identified by theorem-local verification-scope metadata. Describe the connection between anchored mathematical environments and checked results at the level needed to understand the verification boundary. Consolidate verification disclosures here and preserve the frozen mathematical statements.

objs: none

bib: none
home_objs: none
