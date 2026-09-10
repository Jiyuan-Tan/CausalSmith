import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.Basic
import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.ScalarMixture
import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.BoundaryPrior
import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.ApproximateBridge
import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.ApproximateConstruction
import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.FuzzyConstruction
import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.Reduction
import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.Rate

/-!
# API for the large-alphabet `L₁` Poisson minimax lower bound

This umbrella exports the two-unknown-distribution Poisson experiment and
risk, scalar moment-matching and mixed-Poisson closeness, normalization and
fuzzy-prior construction, the all-estimator reduction, the growing-alphabet
minimax rate theorem, and exact intensity-rescaling bridges.
-/
