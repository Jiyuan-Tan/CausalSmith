# Hidden-State Overlap in POMDP Policy Evaluation

We characterize the minimax risk for stationary off-policy evaluation from one finite POMDP trajectory, and a radius-calibrated partial-history estimator attains the full overlap frontier.

---

## Overview

- We observe one stationary behavior trajectory with observed state, action, and reward.
- The Markov state has an unobserved component.
- Behavior and target policies are known functions of the observed state.
- We study the stationary target-policy mean reward.
- The key population control is latent stationary overlap: target occupancy is bounded by behavior occupancy on the full observed-latent state.
- The risk surface depends on the overlap-distance radius \(q_C\), mixing scale \(t_0\), and log-overlap scale \(\zeta\).

@informal thm:uniform-overlap-frontier: Uniformly over finite observed and latent alphabets, the minimax risk is comparable to the all-radius frontier, and a radius-calibrated PHIW estimator attains the upper bound.

---

## Motivation

- In mobile health and treatment-policy evaluation, we often observe a coarse context but miss clinically relevant latent state.
- A target policy may change the long-run mix of latent states, even when actions are randomized with known probabilities.
- Current-action weighting corrects the action choice at the current observed state.
- Longer observable histories can partially recover the latent occupancy shift created by the target policy.
- The central question is: how much history is statistically worth using?

---

## Running example

- Think of an insulin policy that treats when observed glucose exceeds a threshold.
- Diet history is latent, but it affects future glucose and treatment needs.
- The behavior policy randomizes treatment, while the target policy follows the glucose threshold.
- One-step policy overlap controls action probabilities at observed glucose levels.
- Latent stationary overlap controls how far the target policy can move the stationary diet-glucose distribution.
- The theory chooses history length from that stationary-overlap radius.

---

## Setup

- The joint state is \(S_t=(X_t,H_t)\): observed state \(X_t\) and latent state \(H_t\).
- The behavior policy \(b\) generates the data; the target policy \(e\) defines the counterfactual value.
- We observe \((X_t,A_t,Y_t)\) for \(t=0,\ldots,T-1\).
- Rewards are bounded, and the trajectory starts in the behavior stationary law.
- The target estimand is the stationary mean reward under the target policy.

@formal def:target-value

---

## Assumptions

- The process is a finite POMDP with a time-homogeneous reward-transition kernel.
- Sequential ignorability holds at the observed state: actions are drawn from \(b(\cdot\mid X_t)\).
- One-step policy overlap bounds \(e(a\mid x)/b(a\mid x)\) by \(L=\exp(\zeta)\).
- Uniform contraction gives geometric forgetting under both behavior and target policies.
- Latent stationary overlap bounds the target stationary law \(d_e\) by \(C d_b\) on the full joint state.

@formal ass:latent-stationary-overlap

---

## Estimator

- Partial-history importance weighting uses only the last \(k+1\) observable policy ratios.
- Larger \(k\) reduces latent-history bias through mixing.
- Larger \(k\) increases variance through products of one-step ratios.
- Clipping keeps the estimate on the reward scale.

@formal def:phiw-estimator

---

## Radius calibration

- The normalized overlap-distance radius is \(q_C=(C-1)/C\).
- At \(q_C=0\), target and behavior stationary occupancies coincide.
- As \(q_C\) grows, longer observable histories become useful.
- The supplied radius \(C\) determines the depth used by the estimator.

@formal def:overlap-distance-radius

@formal def:radius-adaptive-history-depth

---

## Main result

- The frontier has a parametric term and a hidden-state term.
- The elbow occurs when the overlap-distance radius is on the \(T^{-1/2}\) scale.
- The constants depend on \(t_0\) and \(\zeta\), while the statement is uniform over finite alphabets.

@formal thm:uniform-overlap-frontier

---

## Fixed-radius slice

@informal thm:fixed-c-minimax: For every fixed \(C>1\), the minimax risk is between constants times \(T^{-\beta}\), and clipped PHIW at the balanced depth attains the upper bound.

@formal thm:fixed-c-minimax

---

## Boundary slice

@informal prop:unit-overlap-boundary: At unit latent overlap, the behavior and target stationary laws coincide, immediate weighting has at most order \(T^{-1}\) risk, and the minimax risk is on the \(T^{-1}\) scale.

@formal prop:unit-overlap-boundary

---

## Local slice

@informal thm:shrinking-overlap-frontier: Along shrinking radii \(C_T=1+\delta_T\), the minimax risk is comparable to the local frontier, and immediate weighting attains a parametric bound when \(T\delta_T^2\) stays bounded.

@formal thm:shrinking-overlap-frontier

---

## Related literature

- Hu and Wager (2023) give the closest POMDP baseline: partial-history weighting with the hidden-state exponent \(\beta=2/(2+t_0\zeta)\).
- We keep the same finite POMDP, known-policy, bounded-reward, mixing, and one-step-overlap setting.
- Our additional population control is latent stationary overlap on the full observed-latent state.
- Mehrabi and Wager (2025) provide the closest fully observed overlap comparator through stationary density-ratio control.
- Proxy and bridge approaches impose additional observability structure; our results quantify the partial-history route under latent stationary overlap.

---

## Key idea

@figure estimator-pipeline: Box-and-arrow schematic showing observed trajectory and known policies feeding partial-history weighting, radius-calibrated depth selection, clipped averaging, and the stationary target-value estimate.

- The estimator balances two forces.
- Bias shrinks because contraction makes remote latent history less relevant after a length-\(k\) observed window.
- Variance grows because each extra step multiplies another observable policy ratio.
- Latent stationary overlap scales the bias by \(q_C\).
- The calibrated depth sets the window length from the effective radius \(Tq_C^2\).

---

## Lower-bound idea

@figure signed-depth-alternatives: Box-and-arrow schematic showing a constant observed state, hidden depth and sign coordinates, rare action histories leading to terminal depth, and two reward-sign alternatives.

- The hard pair has one observed state, so the econometrician sees actions and rewards but not latent depth.
- Rare action histories move the latent state toward a terminal depth.
- The target value differs through the terminal sign.
- The observed laws remain close because the terminal state is hard to detect from the observed path.
- The reset-sign perturbation keeps latent stationary overlap within the prescribed radius.

---

## Insulin demonstration

- The finite grid has 360 joint states with latent diet coordinates.
- The behavior policy treats with probability \(0.3\).
- The target policy treats when glucose is at least \(125\).
- The refresh component gives one-half contraction.
- The certified stationary overlap constant is \(C=720\).
- Immediate weighting has a strictly negative certified stationary bias interval.

@informal prop:finite-insulin-demonstration: In the refreshed insulin grid, the structural constants satisfy the theorem’s contraction, action-overlap, and stationary-overlap conditions, while immediate weighting has certified negative bias.

@formal prop:finite-insulin-demonstration

---

## Takeaways

- Latent stationary overlap gives a quantitative radius for stationary POMDP off-policy evaluation.
- The all-radius frontier is \(T^{-1}\) plus the hidden-state partial-history term scaled by \(q_C\).
- Fixed positive radius recovers the Hu-Wager partial-history exponent.
- Unit overlap and sufficiently small local radii yield the parametric scale.
- Radius-calibrated PHIW is the constructive estimator matched to this frontier.
