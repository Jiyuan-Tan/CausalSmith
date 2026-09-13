node observed-counts | Observed treatment–outcome counts
node split-counts | Independent counts | pilot and evaluation
node rectangles | Pilot-local rectangles
node jackson | Jackson polynomial
node cell-estimates | Factorial-moment cell estimates
node aggregate | Clipped aggregate | summed and projected
node all-data | All-data estimator
edge observed-counts -> split-counts
edge split-counts -> rectangles
edge split-counts -> cell-estimates
edge rectangles -> jackson
edge jackson -> cell-estimates
edge cell-estimates -> aggregate
edge aggregate -> all-data
