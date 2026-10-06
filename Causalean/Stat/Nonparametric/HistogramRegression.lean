module
public import Causalean.Stat.Nonparametric.HistogramRegression.Basic
public import Causalean.Stat.Nonparametric.HistogramRegression.CellVariance
public import Causalean.Stat.Nonparametric.HistogramRegression.Centered
public import Causalean.Stat.Nonparametric.HistogramRegression.Counts
public import Causalean.Stat.Nonparametric.HistogramRegression.CubicalRisk
public import Causalean.Stat.Nonparametric.HistogramRegression.EstimatorComparison
public import Causalean.Stat.Nonparametric.HistogramRegression.Geometry
public import Causalean.Stat.Nonparametric.HistogramRegression.IIDTransfer
public import Causalean.Stat.Nonparametric.HistogramRegression.Mesh
public import Causalean.Stat.Nonparametric.HistogramRegression.PartitionTotals
public import Causalean.Stat.Nonparametric.HistogramRegression.PatternMeans
public import Causalean.Stat.Nonparametric.HistogramRegression.PatternMoments
public import Causalean.Stat.Nonparametric.HistogramRegression.Population
public import Causalean.Stat.Nonparametric.HistogramRegression.Risk

/-!
# Finite-partition histogram regression

This roll-up exports totalized finite-partition regression histograms, their
integrated iid squared-risk bound, and the Hölder cubical specialization with
an optimized ceiling-mesh rate. The generic results use only a measurable
finite partition, bounded responses, and an explicit conditional-mean premise.
-/
