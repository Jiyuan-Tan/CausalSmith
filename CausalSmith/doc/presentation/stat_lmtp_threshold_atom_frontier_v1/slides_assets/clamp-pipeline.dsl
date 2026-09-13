node natural-a | Natural A | continuous exposure
node threshold | Threshold | δ_n minimum level
node split | Split | below δ_n | above δ_n
node lower-tail | Lower tail | below threshold
node retained | Retained course | observed dose kept
node atom | Atom | same dose δ_n
node boundary | Boundary response | at δ_n
node clamp-mean | Clamp mean | averages both parts
edge natural-a -> split
edge threshold -> split
edge split -> lower-tail
edge split -> retained
edge lower-tail -> atom
edge threshold -> atom
edge atom -> boundary
edge retained -> clamp-mean
edge boundary -> clamp-mean
