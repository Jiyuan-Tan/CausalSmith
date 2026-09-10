import Causalean.Graph.FiniteDensity.Positive.Basic
import Causalean.Graph.FiniteDensity.Positive.Edge
import Causalean.Graph.FiniteDensity.Positive.Witness
import Causalean.Graph.FiniteDensity.Positive.Finite
import Causalean.Graph.FiniteDensity.Positive.FiniteWitness
import Causalean.Graph.FiniteDensity.Positive.Examples
import Causalean.Mathlib.Analysis.LogRatioStability

/-!
# Positive-mechanism stability interfaces

This roll-up module exports reusable finite-DAG interfaces for characterizing edgewise causal
minimality by local-factor contrasts, retaining finite witnesses under uniform perturbations, and
preserving fixed signs of positive log-ratio derivatives on compact intervals.
-/
