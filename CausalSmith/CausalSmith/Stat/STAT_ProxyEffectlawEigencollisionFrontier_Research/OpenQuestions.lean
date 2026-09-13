import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Inference

/-! The unresolved exact/sharp computation question, recorded as descriptive non-Prop data. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open Set

/-- Can the original sharp summary-inversion image and its support-dependent extrema be evaluated
by one fixed-dimensional exact-real algorithm, uniform in the sample size and polynomial in it,
without compact nearest-summary optimization or black-box `Fbar` evaluation?  The unresolved
alternative also allows a sharp representation rather than direct exact evaluation.  This payload
is deliberately nonassertive because the note leaves the exact-real operation and forbidden-oracle
criteria undefined.  For the ambient setting, [the defined object](goal) is given by [its defining clause](step:1). -/
-- @node: oeq:constructive-total-repair
def ConstructiveTotalRepairQuestion : _root_.String :=
  "Open: in the fixed-dimensional exact-real model, construct one algorithm uniform for every " ++
  "n >= 1 that computes exactly, or gives a sharp representation of, the original image " ++
  "C_{n,alpha} = { Fbar(q) : q in K and d_S(q, Pi(S_hat_n)) <= 2*r_{n,alpha} } and its exact " ++
  "support-dependent cluster extrema, with runtime polynomial in n, without compact " ++
  "nearest-summary optimization or black-box evaluation of Fbar. The positive real law " ++
  "estimator lambda_hat_n, the honest outer set C_alg_{n,alpha}, and every interval in its " ++
  "report R_{n,alpha} already have explicit fixed-dimensional constrained representations, " ++
  "including when the raw empirical operator has nonreal eigenpairs. Thus the remaining " ++
  "question is only exact computation or sharp polynomial-time representation of the original " ++
  "summary-inversion image and its extrema; it is not the existence of an evaluable confidence " ++
  "set or report."

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
