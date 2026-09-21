/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Weighted.AdditiveSpan
public import Causalean.Stat.Weighted.FWL
public import Causalean.Stat.Weighted.IndicatorSpan
public import Causalean.Stat.Weighted.InnerProduct
public import Causalean.Stat.Weighted.NormalizedWeights
public import Causalean.Stat.Weighted.OfProbabilityMeasure
public import Causalean.Stat.Weighted.ScalarFWL
public import Causalean.Stat.Weighted.Subspace
public import Causalean.Stat.Weighted.Support
public import Causalean.Stat.Weighted.WLS

/-!
Weighted least squares as linear algebra: the geometry that underlies estimators built from
nonuniform observation weights.

Provides the weighted inner product and its matrix form, weighted supports and normalised
weights, orthogonal projection onto a weighted subspace, scalar normal-equation and general
minimizer-to-coefficient implications from Frisch-Waugh-Lovell, and the span constructions
(indicator/cell spans, two-axis additive spans) that fixed-effect designs are expressed in.

The two-way panel application lives in `Causalean.Panel`; nothing here depends on a panel
structure.
-/
