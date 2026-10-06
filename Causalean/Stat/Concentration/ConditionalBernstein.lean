module
public import Causalean.Stat.Concentration.ConditionalBernstein.Basic
public import Causalean.Stat.Concentration.ConditionalBernstein.Bernoulli
public import Causalean.Stat.Concentration.ConditionalBernstein.Disintegration
public import Causalean.Stat.Concentration.ConditionalBernstein.Fibre
public import Causalean.Stat.Concentration.ConditionalBernstein.Integrated
public import Causalean.Stat.Concentration.ConditionalBernstein.Simultaneous
public import Causalean.Stat.Concentration.ConditionalBernstein.TotalVariance

/-!
# Finite-partition conditional Bernstein tails

This module provides finite-family Bernstein bounds for outcome-bin counts conditional
on an IID design vector.  It retains the realized design-cell count in the variance
factor, then integrates the fibrewise result under an arbitrary Markov outcome kernel.
-/

public section
