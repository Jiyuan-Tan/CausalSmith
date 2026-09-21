node labeled-split | Labeled split | outcome block | pilot + factorial blocks
node auxiliary-split | Auxiliary split | pilot block | factorial block
node outcome-masses | Outcome masses | outcome-marked | estimates
node pilot-decision | Pilot decision | light vs heavy | covariate cell
node light-weights | Light weights | Chebyshev degree L | polynomial correction
node heavy-weights | Heavy weights | stabilized | inverse counts
node cell-weights | Cell weights | selected by | pilot decision
node ate-estimate | Clipped ATE | final sum | natural range
edge labeled-split -> outcome-masses
edge labeled-split -> pilot-decision
edge labeled-split -> light-weights
edge labeled-split -> heavy-weights
edge auxiliary-split -> pilot-decision
edge auxiliary-split -> light-weights
edge auxiliary-split -> heavy-weights
edge pilot-decision -> cell-weights
edge light-weights -> cell-weights
edge heavy-weights -> cell-weights
edge outcome-masses -> ate-estimate
edge cell-weights -> ate-estimate
