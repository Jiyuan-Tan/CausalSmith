module
public import Causalean.Stat.Concentration.VC.Cover
public import Causalean.Stat.Concentration.VC.Geometry
public import Causalean.Stat.Concentration.VC.Score
public import Causalean.Stat.Concentration.VC.Trace

/-!
# Euclidean radial-polynomial VC-subgraph classes

This barrel exports finite-trace pseudo-dimension bounds and uniform polynomial
`L²` covering certificates for compactly supported radial monomials with a
moving finite-dimensional Euclidean center.  It also exports finite signed-arm,
shared-center polynomial, and bounded residual-score closure certificates.

All covering statements are uniform over arbitrary probability measures, so
they remain valid for atomic laws charging moving kernel boundaries.
-/
