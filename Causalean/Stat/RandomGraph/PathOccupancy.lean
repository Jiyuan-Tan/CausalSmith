module
public import Causalean.Stat.RandomGraph.PathOccupancy.Arithmetic
public import Causalean.Stat.RandomGraph.PathOccupancy.Bounds
public import Causalean.Stat.RandomGraph.PathOccupancy.CoarsePairs
public import Causalean.Stat.RandomGraph.PathOccupancy.Components
public import Causalean.Stat.RandomGraph.PathOccupancy.ConnectedAssignments
public import Causalean.Stat.RandomGraph.PathOccupancy.Counting
public import Causalean.Stat.RandomGraph.PathOccupancy.PairClasses
public import Causalean.Stat.RandomGraph.PathOccupancy.PairEvents
public import Causalean.Stat.RandomGraph.PathOccupancy.PairedExpectation
public import Causalean.Stat.RandomGraph.PathOccupancy.Path
public import Causalean.Stat.RandomGraph.PathOccupancy.Probability
public import Causalean.Stat.RandomGraph.PathOccupancy.ScoreMeasurability
public import Causalean.Stat.RandomGraph.PathOccupancy.SingleEvents
public import Causalean.Stat.RandomGraph.PathOccupancy.SingleExpectation

/-!
# Marked path-component occupancy bounds

This topic gives finite-sample occupancy bounds for connected components of uniform
fine-cell draws on a finite path with independent Bernoulli marks.  It covers arbitrary
local subrelations, so consumers may refine equality-or-neighbor connectivity without
assuming that every eligible edge is present.
-/
