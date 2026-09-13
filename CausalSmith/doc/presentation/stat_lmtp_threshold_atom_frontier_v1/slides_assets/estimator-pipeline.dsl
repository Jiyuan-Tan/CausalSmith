node sample | Sample | observed data
node split | Three blocks | deterministic split
node retained-mean | Retained mean | Block 1 | above δ_n
node atom-masses | Atom masses | Block 2 | lower threshold
node gram-check | Gram check | realized local Gram | bounded fallback
node boundary-regression | Boundary regression | Block 3 | [δ_n, δ_n+h_n]
node total-gram | Total-Gram | estimator | components combine
node interval | Interval | Hoeffding radii | bias-aware radii
edge sample -> split
edge split -> retained-mean
edge split -> atom-masses
edge split -> gram-check
edge gram-check -> boundary-regression
edge retained-mean -> total-gram
edge atom-masses -> total-gram
edge boundary-regression -> total-gram
edge total-gram -> interval
