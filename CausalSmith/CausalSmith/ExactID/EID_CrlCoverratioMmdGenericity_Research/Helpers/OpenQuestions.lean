import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.BoundedSubclass

/-!
# Generated-rank frontier

The second-stage procedure and sharp remainder criterion are intentionally left
undefined by the paper, so the complete question is preserved as text.
-/

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: oeq:generated-rank-frontier
/-- @realizes \(\widehat U_i\)(open cross-fitted conditional-CDF estimator)
@realizes \(\mathfrak H_{\mathrm{rank}}\)(named nonassertive construction handle) -/
def generatedRankFrontierQuestion : _root_.String :=
  "Open, nonassertive generated-rank frontier. Regime: shared C2 diffeomorphic mixing; one \
  distinct unknown-target parent-independent perfect intervention per latent node; fixed \
  own-coordinate derivative signs; independent sampling within environments and independent \
  training/evaluation folds; and the bounded Holder subclass Theta^beta_{G,s}(c,M,K,rho). \
  Assume inf_theta Pr_theta{E_N^infty(b_N)} >= 1-eta_N. Let h_N -> 0, b_N = o(h_N), \
  and Nbar*h_N^dstar/log(Nbar) -> infinity. Question: using H_rank, can one construct \
  cross-fitted conditional-CDF estimators Uhat_i with max_i \
  ||Uhat_i-U_i||_{infinity,K} = O_Pr(r_N), where \
  r_N = h_N^2 + sqrt(log(Nbar)/(Nbar*h_N^dstar)) + b_N/h_N? Under an additional \
  uniform asymptotically linear first-stage log-ratio representation on K, derive an expansion \
  separating generated-threshold indicator boundary crossings, generated-conditioning \
  local-design perturbations, oracle conditional-CDF variance, and smoothing bias, and \
  characterize the weakest sufficient first-stage remainder. This payload asserts neither \
  construction nor attainment nor sharpness of the rate, and asserts no sufficient or necessary \
  remainder bound; the influence representation and second-stage weight convention remain \
  unspecified."

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
