/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.Basic
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.FixedRisk
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.PairingLaw
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.Risk

/-!
# Paired Poisson-histogram Rao--Blackwell transfer

This roll-up module exports parameter-independent count estimation from paired fixed samples,
the law identity for pairing independent iid arrays, general and twice-sample-size risk bounds,
and parameter-free reconstruction of ordered Poisson samples from their histograms.
-/
