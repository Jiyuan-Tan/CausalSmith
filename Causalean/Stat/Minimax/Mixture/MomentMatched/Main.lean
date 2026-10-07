module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson

/-!
# Finite signed moment marked-Poisson mixtures

Entry point for the marked-Poisson moment-matching theory of
`Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson`: a finite signed measure with total
absolute mass one and vanishing moments through degree `K` yields two Jordan priors with matched
moments (and zero-inflated variants), and the predictive mixtures of the label-gated four-count
marked-Poisson experiment under these priors are geometrically close in total variation
(`exists_geometric_markedPoisson_tv_bound`), with a conditional tensorization over finitely many
independent coordinates
(`markedPoissonProductPredictive_geometric_tv_le_of_one_coordinate_bound`).

This file declares nothing itself; it imports that module only.
-/

public section
