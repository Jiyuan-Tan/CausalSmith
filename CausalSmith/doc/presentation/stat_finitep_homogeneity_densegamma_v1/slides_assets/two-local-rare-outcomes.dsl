node coarse-cell | Coarse cell | containing both fine cells
node fine-left | Adjacent fine cell | left
node fine-right | Adjacent fine cell | right
node outcome-left | Nonzero outcome
node outcome-right | Nonzero outcome
node shared-signs | Shared interior node | signs (λᵢ, ηᵢ) at i/K | unrevealed sign
edge coarse-cell -> fine-left
edge coarse-cell -> fine-right
edge fine-left -> outcome-left
edge fine-right -> outcome-right
edge shared-signs -> outcome-left
edge shared-signs -> outcome-right
