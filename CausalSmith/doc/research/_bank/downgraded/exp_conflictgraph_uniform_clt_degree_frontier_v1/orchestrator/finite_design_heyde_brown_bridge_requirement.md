# Study requirement: finite-design Heyde--Brown bridge

Slug: `finite-design-heyde-brown-bridge`

## Required reusable result

Build a paper-independent adapter from the existing finite product-design API to
the already-cited measure-theoretic Heyde--Brown fourth-moment interface.  The
adapter must not reprove Heyde--Brown.  It should accept the cited theorem as an
argument and specialize it to a finite family of coordinate designs, a reveal
permutation, and prefix-centered increments.

For finite `Fin N`-indexed coordinate types `alpha i`, coordinate designs
`D : forall i, FiniteDesign (alpha i)`, a permutation `pi`, and increments
`X : Fin N -> (forall i, alpha i) -> R`, expose a theorem of the following
semantic shape:

1. `prefixCondE D (prefixRankSet pi s.val) (X s) = 0` for every `s`;
2. the sum of finite-design second moments is one;
3. the finite fourth moments exist automatically;
4. therefore the Kolmogorov distance of `sum_s X_s` from standard normal is
   bounded by the cited constant times the one-fifth power of
   `sum_s E |X_s|^4 + E |Q-1|^2`, where `Q` is the prefix predictable
   variation built from the same `prefixCondE`.

The theorem must identify, rather than merely compare, all four interfaces used
by the citation: the product-design probability measure, conditional
expectation along the reveal filtration, predictable variation, and the CDF /
Kolmogorov-distance expression.

## Proposed topical home and imports

Preferred home: a reusable Causalean design-based probability module near
`Experimentation/DesignBased/ProductMeasure.lean`, with any narrower helper
modules split by measure/filtration topic.  It may use Mathlib's finite discrete
measurable space and martingale/conditional-expectation APIs, plus the existing
`FiniteDesign.toMeasure`, `prodDesign_toMeasure_eq_pi`, and expectation/integral
bridges.

The reusable substrate must not import the current research module.  If the
existing run-local `prefixCondE` / `prefixRankSet` definitions are too
paper-local, first extract equivalent generic definitions to Causalean and prove
the run-local definitions are thin wrappers.

## Citation boundary

`HeydeBrownMartingaleFourthMoment` remains a cited logical premise under the
standing citation ruling.  This study implements only the generic
finite-design-to-measure instantiation bridge.  It must neither assert nor prove
the published inequality independently.

## Run-local work left after relay

The current run remains responsible for instantiating the reusable adapter with
`coordinateDesign`, the Perron reveal order, `revealIncrement`, the exact Doob
decomposition, and the already-proved spectral fourth-moment / predictable-
variation bounds in `uniform_normal_bound`.

## Verification

Require a targeted build of every new Causalean module, a source scan with no
`sorry`, `admit`, or new `axiom`, and `#print axioms` for the headline adapter.
Its axiom report may contain the cited Heyde--Brown premise only as an explicit
theorem argument, never as a new declaration-level axiom.
