## Done

- `Core.lean`: uniform joint/statistic masses, guarded full-data conditional design, normalization, atomwise factorization, and finite-sum disintegration remain proved.
- `RaoBlackwell.lean`: retained the state-indexed conditional mean only as a fiberwise analytic lemma; moved the primary statewise/prior/worst-case/minimax API to one `Statistic → ℝ` estimator derived from `SufficientFactorization`.
- `KernelBridge.lean`: added factorization-derived common and finite-prior posterior Markov kernels, singleton-real identities, and a real posterior `kernelAverageLoss` sum bridge.
- Ground truth: direct elaboration and targeted `lake build ...KernelBridge` succeed; the only proof gaps are the 16 listed below.

## Remaining

- `Sufficiency.lean` (6): `fiberCarrierMass_nonneg`, `statisticMass_eq_factor_mul_fiberCarrierMass`, `fiberCarrierMass_pos_of_statisticMass_pos`, `commonConditionalWeight_nonneg`, `commonConditionalWeight_sum`, `commonConditionalWeight_eq_conditionalWeight`.
- `Posterior.lean` (10): `priorJointStatisticMass_nonneg`, `priorJointStatisticMass_sum`, `priorStatisticMass_nonneg`, `priorStatisticMass_sum`, `posteriorWeight_of_pos`, `posteriorWeight_of_eq_zero`, `posteriorWeight_nonneg`, `posteriorWeight_sum`, `priorStatisticMass_mul_posteriorWeight`, `posterior_disintegrate_sum`.

## Blocked

- None.

## Decisions

- Model sufficiency by the finite Fisher--Neyman factorization `jointMass θ z = statisticFactor θ (T z) * carrierWeight z`, with both factors nonnegative; derive the common conditional law by normalizing carrier weights on each statistic fiber.
- Keep null common-conditionals normalized with `fallbackSample`; keep null posterior fibers normalized with the original finite prior. Both choices disappear after multiplication by their zero marginal.
- `CommonConditionalKernel` is now a low-level derived-law interface; primary Rao--Blackwell theorems accept `SufficientFactorization`, preventing a state-dependent conditional mean from being presented as one usable estimator.
- Add the prior state--statistic joint/marginal/posterior API because `conditionalKernel θ` conditions full data at fixed state, not latent state given statistic.
- Library search found no matching finite sufficiency/posterior substrate. Blackwell (1947) grounds the conditional-expectation contraction; the Fisher--Neyman factorization criterion grounds the new factorization hypothesis.
