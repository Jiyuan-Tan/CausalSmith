## Done
- Round-3 ground-truth audit: forced `lake env lean` source checks passed for all five modules; umbrella `lake build CausalSmith.Substrate.CommonDesignMarkedLaws.Main` completed successfully (3097 jobs).
- Source grep finds no `sorry`, `admit`, or declared `axiom`.
- `#print axioms` for every public API theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `ConditionalExpectation.lean`: `condExp_eq_of_integral_preimage_eq` proves conditional-expectation uniqueness from all measurable design-preimage integrals.
- `WeightedProduct.lean`: both weighted L² and L¹ bounds are proved for arbitrary measurable design spaces and full-design-vector-dependent measurable weights; cross terms and the `1/4` variance factor are derived.
- `KernelChiSquared.lean`: `attachKernel`, its probability instance, exact shared-base χ² disintegration, and measurable-equivalence invariance are proved.
- `TwoPoint.lean`: centered Bernoulli and signed two-point χ² formulas are proved and have the orientation needed for iid tensorization.
- Re-ran the required Causalean searches; reused canonical conditional-expectation, finite-product/Fubini, χ²-invariance/tensorization, and L¹-from-L² infrastructure. No external paper was named, so no primary-paper fetch applied.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Preserve the genuine arbitrary-measurable-space APIs and explicit square-integrability premises permitted by the requirement.
- Accept the joint RN-derivative integrability premise for exact kernel disintegration; it is a real finiteness condition, not the desired identity in disguise.
- Advance to review with no filler agents because the verified source contains zero remaining proof placeholders.