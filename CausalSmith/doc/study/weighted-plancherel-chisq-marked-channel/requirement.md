# Substrate requirement: weighted Plancherel χ² marked-channel bridge

## Goal

Build reusable Causalean substrate for Bernoulli-marked convolution experiments with two fixed shifted/scaled sinc-fourth error densities. The study module must not import any `CausalSmith/*_Research` module; main will extract the minimal generic density, channel, and observed-law prerequisites first.

For a finite stratum type, a compact latent density `f`, fixed sinc-fourth-mixture error densities `e1,e2`, and a compactly supported signed perturbation `h` with ordinary moments zero through order `2*k-1`, define the common unmarked convolution density `b_x`, the marked convolution perturbation `d_x`, and the two Bernoulli-marked observed laws `mu0,mu1` with conditional mark probabilities `1/2` and `1/2+h/f`.

## Provides (API contract)

Prove a constant `D > 0`, chosen independently of `k`, for which every admissible order satisfies:

`mu1 << mu0`, integrability under `mu0` of `((mu1.rnDeriv mu0).toReal - 1)^2`, and

`chiSqDiv mu1 mu0 <= D * sum x, integral over the protected frequency square of ‖markedChannel1 x s t - markedChannel0 x s t‖^2`.

It must also expose the map/product support facts needed to prove equality of complete unmarked observed laws when latent and error laws coincide.

## Statement / milestones

The analytic core must prove the uniform inverse-density weighted Plancherel inequality `integral d_x^2 / b_x <= D * integral_C ‖Fourier d_x‖^2`, using the sinc-fourth two-sided tail/lower-envelope bounds, compact Fourier support, convolution-density formulas, L2 regularity, and the packet moment cancellations. Then connect this inequality through Radon–Nikodym identities to the χ² bound and prove the unmarked-law equality from common latent and error laws.

## Standard reference

Use standard Fourier-Plancherel theory, convolution identities, Radon–Nikodym calculus, and χ² divergence. Existing Causalean and Mathlib declarations listed below are the preferred formal reference points; do not introduce paper-specific assumptions.

## Intended reuse

This should be reusable for finite-stratum Bernoulli-marked convolution experiments whenever a compactly supported moment-annihilating perturbation is observed through fixed errors with a suitable two-sided convolution-density envelope. It will first serve the blind-replicate ADRF lower-bound packet, but its public API must remain paper-neutral.

## May assume / must derive

May assume explicitly stated measurability, integrability, compact support, moment cancellation, Fourier support, probability-density, and two-sided tail/lower-envelope hypotheses on generic inputs. Must derive absolute continuity, RN-square integrability, the χ² comparison, and unmarked observed-law equality. For the sinc-fourth specialization, derive the needed envelope, convolution, Fourier-support, and L2 facts rather than postulating the final weighted Plancherel or χ² conclusion.

## Known building blocks and proposed imports

Prefer and extend existing imports `Mathlib.Analysis.Fourier.LpSpace`, `Mathlib.Analysis.Fourier.Convolution`, `Causalean.Stat.Minimax.ChiSquaredKernel`, `Causalean.Mathlib.MeasureTheory.SupportRnDerivTransport`, and, if required, `Causalean.Mathlib.MeasureTheory.RnDerivCompProdSigmaFinite`. Reuse `Causalean.Stat.one_add_chiSqDiv_attachKernel`, `chiSqDiv_eq`, product/map RN transport, and Mathlib L2 Plancherel. Deliver zero `sorry`, zero new axioms, focused builds, and `#print axioms` receipts.

## Extraction boundary

After promotion, paper-specific wiring remains: instantiate the bridge with `lowerHandle`; take `c = amplitude`, `C = D * attenuationC`, `C0 = attenuationC0`; discharge model, nuisance, centering/moment, Bernoulli, and ADRF clauses from its fields; use paired channel factorization for probability-channel equality; transfer density nonidentity/asymmetry from measure certificates; and unfold the packet maps to obtain unmarked-law equality. Consumers are `lem:fixed-kernel-bernoulli-packet`, `thm:fixed-nuisance-marked-pair`, `thm:paired-protected-inverse`, and transitively `thm:minimax-width-frontier`.
