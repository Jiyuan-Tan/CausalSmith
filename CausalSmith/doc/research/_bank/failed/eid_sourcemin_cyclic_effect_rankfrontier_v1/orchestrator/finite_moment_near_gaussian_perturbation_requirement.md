# Finite-moment near-Gaussian perturbation

Develop a reusable, axiom-clean Lean theorem constructing non-Gaussian probability measures arbitrarily close to the standard Gaussian while matching any prescribed finite initial segment of its moments.

For every natural `K ≥ 3` and every `rho > 0`, construct a Borel probability measure `F` on `ℝ` such that:

- `F` has mean zero and variance one;
- `F` is not the standard Gaussian law;
- the total-variation distance from `F` to the standard Gaussian is less than `rho`;
- every raw moment of order `k ≤ K` agrees with the standard Gaussian;
- `F` has finite moments of every order and satisfies an explicit Carleman divergence bound, hence is moment determinate after applying the existing Carleman criterion.

The construction should expose enough API to transfer finite raw-moment equality to equality of source cumulants through order `K`. A natural route is a bounded signed density perturbation orthogonal to the monomials through degree `K`, chosen small enough to keep the perturbed Gaussian density nonnegative and normalize its mass, with tail control inherited from the Gaussian to establish all moments and Carleman divergence.

Use only Mathlib, Causalean, and study-local prerequisites. Do not import any `CausalSmith/*_Research` module. Existing `Causalean.Mathlib.MeasureTheory.exists_moment_perturbation` preserves only mass, mean, and second moment; the new result must work for arbitrary finite `K` and additionally provide total-variation and moment-determinacy/Carleman control.
