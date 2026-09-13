node observed | Observed sample | treatment, proxies, outcome
node summary | Five-block summary | empirical Ŝₙ
node signal | Proxy signal | threshold π₀σ₀²/2 | k dimensions
node mesh | Lattice mesh | 1/√n sampling scale
node lattice | Structured lattice | operators, means, anchors | polynomial candidate list
node estimate | Atomic quotient law | first minimizing λ̂ₙ
node report | Wasserstein report | C_lat{d_S+1/√n} | uniform root-n tail
edge observed -> summary
edge summary -> signal
edge summary -> lattice
edge signal -> lattice
edge mesh -> lattice
edge lattice -> estimate
edge estimate -> report
