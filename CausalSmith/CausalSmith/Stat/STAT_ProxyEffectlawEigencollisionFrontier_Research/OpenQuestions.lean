import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Inference

/-! The unresolved exact/sharp computation question, recorded as descriptive non-Prop data. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open Set

/-- Can the original sharp summary-inversion image and its support-dependent extrema be evaluated
by one exact-real algorithm uniform in the sample size, in polynomially many arithmetic,
comparison, singular-value, and fixed-degree root-isolation operations, without nearest-summary
optimization or black-box `Fbar` evaluation?  This payload is deliberately nonassertive because
the note does not define an exact-real complexity semantics for those forbidden operations. -/
-- @node: oeq:constructive-total-repair
def ConstructiveTotalRepairQuestion : _root_.String :=
  "Open: construct one exact-real algorithm, uniform for every n >= 1, that returns the " ++
  "original sharp summary-inversion image and its exact support-dependent cluster extrema, has " ++
  "a proved polynomial bound in n for arithmetic, comparison, singular-value, and fixed-degree " ++
  "root-isolation operations, and uses neither compact nearest-summary optimization nor " ++
  "black-box evaluation of the continuous extension. The explicit lattice estimator is a total " ++
  "positive real-law rule even when the raw empirical compressed operator has nonreal " ++
  "eigenpairs. Its computable outer confidence set is honest, and that set and every reported " ++
  "support or mass interval have explicit ordered-support, atom-floor, simplex, transport-plan, " ++
  "and interval-level constrained representations. Those evaluable outer objects are already " ++
  "available and are not part of this unresolved question."

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
