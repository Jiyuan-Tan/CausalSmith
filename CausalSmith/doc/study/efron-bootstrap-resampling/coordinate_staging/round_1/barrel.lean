module
public import Causalean.Stat.Bootstrap.EfronResampling.Basic
public import Causalean.Stat.Bootstrap.EfronResampling.FiniteRepresentation
public import Causalean.Stat.Bootstrap.EfronResampling.IIDSampleLink
public import Causalean.Stat.Bootstrap.EfronResampling.Measurability
public import Causalean.Stat.Bootstrap.EfronResampling.Moments

/-!
# Efron bootstrap resampling

This directory provides the nonparametric bootstrap as an actual conditional resampling law:
the empirical measure of a finite data vector, the product law for draws with replacement, exact
finite representations and moments, the bridge to the library's plug-in variance, and measurable
bootstrap distribution and quantile maps.
-/
