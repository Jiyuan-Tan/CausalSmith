node contrast-weighted-assignment | Contrast-weighted | assignment
node centered-arm-score | Centered score | arm
node normalized-average | Normalized average
node clipped-shrinkage | Clipped shrinkage
node projected-estimator | Projected estimator
edge contrast-weighted-assignment -> centered-arm-score
edge centered-arm-score -> normalized-average
edge normalized-average -> clipped-shrinkage
edge clipped-shrinkage -> projected-estimator
