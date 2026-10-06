# Long-Run Policy Evaluation With Binary Hidden States

Seven short weighted reward histories let us recover a policy’s long-run reward from one logged trajectory with inverse-length mean-squared error.

---

## Motivation

We observe one trajectory of length \(T\): recorded states \(X_t\), actions \(A_t\), and rewards \(Y_t\).

- A hidden state affects rewards and transitions.
- The behavior policy \(b\) generated the actions.
- The target policy \(e\) specifies the action probabilities we want to evaluate.
- Both policies are known and depend only on the recorded state.

Our target is the **stationary mean reward**: expected reward per period after the target policy’s state distribution has settled.

Changing the policy changes both actions and long-run state frequencies. How can we account for state frequencies we never observe?

---

## Standard approach

Partial-history importance weighting multiplies a reward by target-to-behavior action probabilities over a preceding window.

- Longer windows move the state distribution closer to target stationarity.
- Longer products of action ratios increase sampling variability.
- Window choice balances initialization bias against weighting variance.

Hu and Wager (2023) obtain the matched mean-squared-error rate \(T^{-2/(2+t_0\zeta)}\), where \(t_0>0\) measures mixing and \(\zeta\geq0\) bounds logarithmic action ratios. Their minimax class permits hidden-state cardinality to grow with \(T\).

Can fixed binary recorded states, hidden states, and actions support faster estimation?

---

## Key idea

Binary recorded and hidden states give only **four joint states**.

Their expected reward sequence obeys a fixed linear recurrence: later rewards are constrained by finitely many earlier rewards.

Seven short weighted moments determine the stationary reward stably, even when they do not determine the hidden dynamics uniquely.

With known observed-state randomization, stationary behavior sampling, bounded rewards and action ratios, and fixed strict contraction under both policies, we obtain minimax mean-squared error of order \(T^{-1}\).

The method fits a contracting four-state model to those seven moments and reports its stationary reward.

---

## Example

Consider equal fair policies:

\[
b(a\mid x)=e(a\mid x)=\frac12,
\qquad x,a\in\{0,1\}.
\]

Each action has probability one half at either recorded state. Every target-to-behavior action ratio is one.

\[
m_0=\mathbb E_b[Y_t]=\theta,
\qquad t=1,\ldots,T,
\]

Here \(m_0\) is the reward moment using only the current action weight, \(\mathbb E_b\) is expectation under behavior sampling, and \(\theta\) is the stationary target reward.

The behavior stationary distribution is already the target distribution. Under stationary sampling and contracting dynamics, ordinary reward averaging is unbiased and has inverse-length mean-squared error.

When policies differ, the short moments instead start from the wrong state distribution. That is the discrepancy the moment fit must remove.

---

## Model

The joint state is \(S_t=(X_t,H_t)\), where the recorded state \(X_t\) and hidden state \(H_t\) are binary. The joint-state space \(\mathcal S\) has four points; actions are binary and rewards lie in \([0,1]\).

\[
\mathcal L(Y_t,S_{t+1}\mid\mathcal F_t^-,A_t)
=
K(\cdot\mid S_t,A_t),
\qquad t=1,\ldots,T,
\]

The full pre-action history is \(\mathcal F_t^-\). The law \(K\) makes the current joint state and action sufficient for the reward and successor state; reward and successor state may be dependent.

Averaging successor probabilities under the two policies gives transition matrices \(P_b,P_e\), with stationary distributions \(d_b,d_e\). The vector \(r_e\) contains each joint state’s target-policy mean reward.

\[
\theta(K,e)
:=
d_e r_e
=
\sum_{s=(x,h)\in\mathcal S}
d_e(s)
\sum_{a\in\mathcal A}
e(a\mid x)
\sum_{s'\in\mathcal S}
\int_{\mathcal Y}
y\,K(dy,s'\mid s,a),
\]

This averages target conditional rewards under target stationary frequencies. Here \(\mathcal A\) is the binary action space, \(\mathcal Y=[0,1]\) is the reward space, and \(s'\) is the successor joint state.

---

## Sampling and overlap

- **Observed-state randomization:** \(\Pr(A_t=a\mid\mathcal F_t^-)=b(a\mid X_t)\). Even conditional on hidden history, assignment uses only the recorded state.
- **Stationary start:** \(S_1\sim d_b\). Every sampled joint state has the behavior stationary distribution.
- **Action overlap:** \(e(a\mid x)\le Lb(a\mid x)\). Every target action is supported by behavior sampling, with target-to-behavior ratio at most \(L\).

Randomization makes action weighting valid. Stationarity gives a common starting distribution for every weighted window. Overlap controls the size of the weights.

In the equal-policy example, all weights are one and the starting distribution is already the desired one.

---

## Contraction

Both behavior and target transitions shrink differences between state distributions by at most \(\alpha<1\) per step.

For the target transition:

\[
\|\mu P_e-\mu'P_e\|_{\mathrm{TV}}
\le
\alpha\|\mu-\mu'\|_{\mathrm{TV}},
\qquad \mu,\mu'\in\Delta(\mathcal S),
\]

Here \(\mu,\mu'\) are probability distributions, \(\Delta(\mathcal S)\) is their simplex, and total variation is half the sum of absolute probability differences. The same condition holds for \(P_b\).

- **Behavior contraction** controls dependence in the observed trajectory.
- **Target contraction** controls convergence to the reward we want and the stability of extrapolating to it.

Keep \(\alpha=\exp(-1/t_0)\) and \(L=\exp(\zeta)\) fixed, with \(t_0>0,\zeta\geq0\).

Write \(\mathcal M_T^{(2)}(t_0,\zeta)\) for the binary experiments satisfying the model, randomization, stationary-start, overlap, and two contraction conditions.

---

## Main result

The minimax risk \(R_T^{(2)}(t_0,\zeta)\) is the smallest worst-case mean-squared error among estimators using the recorded trajectory and supplied policies and bounds.

@informal thm:fixed-binary-minimax: For the binary class \(\mathcal M_T^{(2)}(t_0,\zeta)\), fixed \(t_0>0,\zeta\geq0\) and \(T\geq12\) give minimax mean-squared error of order \(T^{-1}\), attained by a finite contracting moment fit.

\[
\frac{1}{1024T}
\leq R_T^{(2)}(t_0,\zeta)
\leq \frac{B_\alpha^2(112V_{\alpha,L}+2)}{T}.
\]

Every estimator faces the lower bound; our moment fit attains the upper bound. The constants are

\[
B_\alpha=\left(\frac{1+\alpha}{1-\alpha}\right)^6,
\qquad
V_{\alpha,L}=13L^7+\frac{2}{1-\alpha}.
\]

\(B_\alpha\) controls amplification of moment errors; \(V_{\alpha,L}\) controls their sampling error.

The order matches ordinary reward averaging in the equal-policy example. With different policies, fitting replaces the growing weighting window. Slow contraction or large action ratios can still make the constants large.

---

## Observable moments

For each recorded action, compute the likelihood ratio \(\rho_j=e(A_j\mid X_j)/b(A_j\mid X_j)\).

For depths \(k=0,\ldots,6\):

\[
Z_t(k)
:=
Y_t\prod_{j=t-k}^{t}\rho_j,
\qquad
m_k
:=
\mathbb E_b[Z_t(k)],
\qquad
\widehat m_k
:=
\frac{1}{T-6}
\sum_{t=7}^{T}Z_t(k).
\]

The score \(Z_t(k)\) weights a reward using the current action and \(k\) preceding actions. Its population mean is \(m_k\); its observed average is \(\widehat m_k\).

All seven averages use the same terminal observations. The longest window contains seven action weights, regardless of trajectory length.

What policy intervention does each weighted moment represent?

---

## Intervention identity

Observed-state randomization lets each action ratio replace a behavior action probability with its target counterpart.

\[
m_k=d_bP_e^k r_e,\qquad k=0,\ldots,6,
\]

This computes the expected target reward after \(k\) target transitions, starting from behavior stationary frequencies \(d_b\).

- The **current action weight** supplies the target reward vector \(r_e\).
- The **preceding \(k\) weights** supply \(k\) target transitions \(P_e\).
- The **starting distribution** remains \(d_b\), rather than \(d_e\).

Thus \(m_0=d_b r_e\) corrects the reward rule but generally retains a state-distribution mismatch.

Longer windows reduce that mismatch through contraction. Our method instead uses the structure shared by seven short moments to extract their stationary limit.

---

## Finite dimension

A contracting four-state transition matrix has one stationary eigenvalue, equal to one, and three remaining eigenvalues, counted with multiplicity.

The remaining eigenvalues describe **transient behavior**: dependence on the starting distribution that disappears over time. Their absolute values are at most \(\alpha\).

Comparing two four-state reward sequences requires cancelling the transient behavior of both matrices. A polynomial of degree six does this, using moments at depths zero through six.

This is why seven moments suffice for stationary-value comparison.

Nair and Jiang (2021) use observable matrices with rank equal to hidden-state cardinality for finite-horizon evaluation. Here the stationary-value comparison remains stable even when fewer transient components are present.

---

## Stationary extraction

Compare two four-state models with initial distributions \(\nu,\nu'\), contracting transitions \(P,P'\), and reward vectors \(r,r'\) in \([0,1]\). Their stationary distributions are \(\pi,\pi'\).

Their moments are \(\nu P^k r\) and \(\nu'P'^k r'\); their stationary rewards are \(\pi r\) and \(\pi'r'\).

Let \(Q_{P,P'}\) be the degree-six polynomial containing both matrices’ transient eigenvalues as roots, with multiplicities. Its coefficients are \(Q_k\).

\[
Q_{P,P'}(1)(\pi r-\pi'r')
=\sum_{k=0}^{6}Q_k\bigl(\nu P^k r-\nu'P'^k r'\bigr)
\]

The right-hand combination cancels the dependence on both starting distributions. Only the stationary reward difference remains, multiplied by \(Q_{P,P'}(1)\).

For policy evaluation, one model is \((d_b,P_e,r_e)\); the other is our fitted model. This cancellation removes the behavior-start discrepancy even when \(d_b\ne d_e\).

In the equal-policy example, that discrepancy is absent from the outset.

---

## Stable extrapolation

Cancellation must also resist sampling error. For any two four-state models with probability initial distributions, rewards in \([0,1]\), and contraction at most \(\alpha\):

\[
|\pi r-\pi'r'|
\le B_\alpha
 \max_{0\le k\le6}\bigl|\nu P^k r-\nu'P'^k r'\bigr|.
\]

The largest discrepancy among the seven moments bounds the stationary reward discrepancy, multiplied by the previously defined \(B_\alpha\).

Contraction keeps every transient root away from one. The stationary component can therefore be separated without arbitrarily amplifying moment errors.

- Exact moment agreement gives exact stationary-value agreement.
- Approximate agreement gives a proportional value bound.
- Repeated eigenvalues and disappearing transient components are covered by the same bound.

We can estimate the stationary reward accurately even when the fitted hidden dynamics are ambiguous.

---

## Stable candidates

Search a finite grid of initial distributions \(\nu\), transition matrices \(R\), and reward vectors \(r\in[0,1]^4\). The grid becomes finer as \(T\) increases.

Rounding a contracting transition matrix can slightly weaken its contraction. Repair each retained candidate by mixing it with a common uniform transition:

\[
P(R):=\lambda R+(1-\lambda)U.
\]

Here \(U\) sends every state to the uniform four-state distribution. The weight \(\lambda\) is chosen close to one to restore contraction at most \(\alpha\).

Because all rows of \(U\) agree, mixing with \(U\) shrinks differences between the rows of \(R\). The finer grid requires a smaller correction.

The candidate moments approximate the target moments while every candidate remains eligible for the stable-extrapolation bound.

---

## Estimator

Let \(\mathcal C_M\) be the finite candidate set at grid resolution \(M\). Choose the candidate minimizing its largest discrepancy from the seven empirical moments:

\[
(\nu_*,R_*,r_*)
\in
\operatorname*{arg\,min}_{(\nu,R,r)\in\mathcal C_M}
\max_{0\le k\le6}
\left|\widehat m_k-\nu P(R)^k r\right|.
\]

The candidate prediction \(\nu P(R)^k r\) is its reward after \(k\) transitions. Stars denote the selected candidate; a fixed ordering resolves ties.

\[
P_*:=P(R_*),
\qquad
\widehat\theta_T:=\pi(P_*)r_*,
\]

The estimate \(\widehat\theta_T\) is the fitted stationary reward; \(\pi(P_*)\) is the selected transition matrix’s stationary distribution.

A close grid approximation ensures that a good fit exists. Minimization finds a fit at least as good. Stable extrapolation then transfers moment accuracy to stationary-value accuracy.

---

## Risk guarantee

Action overlap gives \(\mathbb E_b[Z_t(k)^2]\le L^{k+1}\). Since \(k\le6\), the weighting cost stays fixed as \(T\) grows.

Windows overlap locally. Once they separate, behavior contraction makes their covariance decay geometrically.

Consequently, empirical moment mean-squared errors have inverse-length order. Grid approximation contributes a smaller error; stable extrapolation converts the combined moment error into value error.

@informal thm:stable-grid-upper: For every experiment in \(\mathcal M_T^{(2)}(t_0,\zeta)\), fixed \(t_0>0,\zeta\geq0\) and \(T\geq12\) give the stable-grid estimator mean-squared error at most \(B_\alpha^2(112V_{\alpha,L}+2)/T\).

\[
\mathbb E_M\!\left[(\widehat\theta_T-\theta)^2\right]
\leq
\frac{B_\alpha^2\bigl(112V_{\alpha,L}+2\bigr)}{T},
\]

Here \(\mathbb E_M\) is expectation under any experiment \(M\) in the binary class.

The fixed windows estimate biased intervention moments accurately; the moment fit removes their initialization discrepancy.

---

## Lower bound

Return to equal fair policies. Two experiments share transitions and noisy observations but perturb hidden-state reward probabilities.

Their Bernoulli reward probabilities are \(q_v(h)=\frac12+\frac{2h-1}{8}+v\), where \(h\) is the hidden state and \(v=\pm v_T\), with \(v_T=\frac{1}{16\sqrt T}\).

The stationary rewards are \(1/2+v\). Writing \(K_v^{(T)}\) for the corresponding joint reward and transition law:

\[
\left|\theta(K_{+v_T}^{(T)},e)-\theta(K_{-v_T}^{(T)},e)\right|
=\frac{1}{8\sqrt T}.
\]

The values differ at the ordinary sampling scale, while the recorded-trajectory laws remain close:

\[
\operatorname{KL}\!\left(
\mathbb P_{+}^{\mathsf O_T}\Vert\mathbb P_{-}^{\mathsf O_T}
\right)\leq\frac1{12}.
\]

Here \(\mathsf O_T\) is the recorded trajectory, \(\mathbb P_\pm^{\mathsf O_T}\) are its two laws, and relative entropy \(\operatorname{KL}\) measures statistical distinguishability.

Both experiments satisfy all class conditions. Two-point testing forces every estimator to incur mean-squared error at least \(1/(1024T)\) in one of them.

---

## Further results

- **Stationary occupancy restriction:** for any fixed \(C>1\), adding \(d_e(s)\leq C\,d_b(s)\) preserves the matched \(T^{-1}\) order; the lower-bound pair has identical stationary laws.
- **Candidate count:** at fixed \(t_0>0\), the finite fitting list has size \(O(T^{19})\), quantifying the search space.

The occupancy restriction bounds target-to-behavior long-run state frequencies. It is distinct from the action-ratio bound used to weight rewards.

---

## Open questions

- Can fitting certify a global objective gap within \(T^{-1}\) with explicit runtime and precision guarantees, including when transient components disappear?
- What is the minimal sufficient observable window, and how can we obtain limit distributions and confidence intervals?
- How should mixing and overlap bounds be calibrated in applications, and how do the required moments and risk change with larger hidden-state alphabets?

---

## Takeaways

- Under known observed-state randomization, stationary behavior sampling, bounded rewards and action ratios, and fixed contraction under both policies, the binary experiment has minimax mean-squared error of order \(T^{-1}\).
- Seven short weighted moments describe target transitions from the behavior stationary distribution. Four-state structure cancels the starting-distribution discrepancy; contraction makes that cancellation stable.
- Fitting contracting candidates attains the upper bound. Ordinary reward uncertainty under equal policies supplies the matching lower bound.

---

## Appendix: Uniform stable-grid risk bound

The stable-grid estimator has a uniform inverse-length mean-squared-error bound over the specified binary experiment.

@formal thm:stable-grid-upper

---

## Appendix: Fixed binary minimax rate

The fixed-binary bounds match; the growing-cardinality comparison uses CausalSmith (2026), a nonarchival public manuscript, as an external premise.

@formal thm:fixed-binary-minimax

---

## Appendix: Stable-grid estimator

This procedure specifies the numerical grid, rounding allowance, uniform-mixture weight, fitting criterion, and stationary-reward output.

@formal def:stable-grid-estimator
