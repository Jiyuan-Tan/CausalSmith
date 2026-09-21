## Done
- Ground-truth audit: `Basic.lean`, `Duality.lean`, `Fejer.lean`, `Rate.lean`, and `API.lean` contain no `sorry`, `admit`, or declared `axiom`.
- `Basic.lean` proves the intrinsic compact-interval error formulation, attainment, nonnegativity, antitonicity, and odd/even parity reduction.
- `Duality.lean` proves the Hahn--Banach/Riesz extremal decomposition, symmetric supported probability priors, exact moment matching through `K`, exact `2 E_K` gap, and projection API.
- `Rate.lean` proves `bestUniformApproxErrorAbs_upper`, `bestUniformApproxErrorAbs_lower`, and `bestUniformApproxErrorAbs_order` with constants `c = 1/100`, `C = 1`; `Fejer.lean` supplies the explicit Fejér/de la Vallée--Poussin lower-bound certificate.
- Re-searched Causalean before finalization; no existing absolute-value approximation/duality result subsumes this module. Re-fetched and checked arXiv:1105.3039 LaTeX for the degree convention, Lemma 1 normalization, and `1/K` asymptotics.
- Added the missing `Fejer.lean` module/declaration docstrings and corrected the `Rate.lean` overview to describe the proof actually used.
- Fresh direct `lake env lean` checks passed for every source file, and `lake build CausalSmith.Substrate.AbsoluteValueMomentPriorDuality.API` passed. Axiom checks for both headline theorems show only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Preserve the genuine intrinsic API, exact `2 E_K` prior gap, and universal constants `c = 1/100`, `C = 1`.
- Keep the stronger extremal decomposition valid for every `K`; the requested positive-even prior theorem is its direct consumer and does not weaken the result.
- Use the truncated Chebyshev series for the upper bound and the bounded de la Vallée--Poussin cusp functional for the lower bound; single-frequency, Markov-only, and shifted-grid routes were rejected because they give only order `K⁻²`.
- No filler subagent is needed: the dependency-clean module is fully proved and ready for review.