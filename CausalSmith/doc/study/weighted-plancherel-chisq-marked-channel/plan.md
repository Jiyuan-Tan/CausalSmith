## Done
- Ground-truth scan: exactly two `sorry`s remain: `WeightedPlancherel.lean:exists_uniform_weightedPlancherel` and `Main.lean:exists_uniform_chiSq_markedChannel_bridge`.
- `ReplicateConvolutionRegularity.lean` is closed; all three previously reported declarations are proved.
- Targeted `lake build CausalSmith.Substrate.WeightedPlancherelChisqMarkedChannel.Main` succeeds with only the two expected `sorry` warnings.
- No research imports, new axioms, `admit`, or other proof bypasses were found.
- Library searches found standard L² Plancherel, Fourier differentiation, support-restriction, and convolution results, but no theorem supplying the requested uniform weighted coercivity. No primary paper/source was named.

## Remaining
- `WeightedPlancherel.lean`: `exists_uniform_weightedPlancherel`.
- `Main.lean`: `exists_uniform_chiSq_markedChannel_bridge`.

## Blocked
- The generic uniform-in-`k` weighted Plancherel statement is false under `CompactMomentPacketFamily`'s current hypotheses; consequently the χ² headline is also false.

## Decisions
- Concrete counterexample family: take one stratum, a compact density `f` bounded below on an interval, and a nonzero smooth bump `φ` supported strictly inside it. Set `h_k = ε_k φ^(2k)`, scaling each nonzero derivative so `|h_k| ≤ f/2`. Integration by parts gives every required moment cancellation below `2k`, while all support, measurability, and integrability clauses hold.
- Fourier factorization gives `Fourier(d_k)(s,t) = c_k (s+t)^(2k) Fourier(φ)(s+t) E₁(s)E₂(t)`. On the fixed error-frequency square these functions concentrate increasingly near an extreme of `|s+t|`. Their frequency-derivative L² norm divided by their L² norm is unbounded in `k`; by Plancherel this is an unbounded polynomially weighted spatial L² ratio.
- The existing two-sided sinc envelopes and compact latent support also give `b(z) ≤ C/((1+|z₁|)^4(1+|z₂|)^4)`, so `∫d_k²/b` dominates that unbounded weighted spatial energy. Enlarging the protected square can supply at most the total unweighted Fourier energy. Hence no finite `D` can work for this admissible family.
- Repair requires a genuine uniform packet regularity/coercivity hypothesis or specializing the theorem to the intended constructed packet; either changes the stated contract and cannot be done by scaffolding.