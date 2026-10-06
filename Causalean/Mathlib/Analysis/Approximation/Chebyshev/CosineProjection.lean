module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Approximation
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Convolution
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Definitions
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Fold
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.JacksonError
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Main
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Moments
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Norms
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Orthogonality
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Seminorm
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection.Span

/-!
# Sharp Hölder approximation by finite cosine projections

This package supplies the normalized cosine basis on the unit interval, its finite
uniform-measure projection, an even Jackson approximant, and the constant-five
Hölder L² error bound. The construction is purely analytic and can be used by
series estimators independently of a particular statistical model.
-/

public section

