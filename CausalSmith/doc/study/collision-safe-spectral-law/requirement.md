# Substrate requirement: collision-safe-spectral-law

## Goal

Build a reusable finite-dimensional stability closure that turns perturbations of bounded real-diagonalizable operators and their anchors into one-dimensional finite-atomic Wasserstein bounds without a spectral gap. The closure consists of three standard primitives: ambient equal-rank Moore--Penrose perturbation, two-diagonalizer divided-difference functional calculus through repeated eigenvalues, and finite-atomic Kantorovich--Rubinstein dual attainment on the real line.

The result must be independent of any statistical model or paper. It must not import a `CausalSmith/*_Research` module and must not encode the proxy-effect-law headline as a substrate theorem.

## Provides (API contract)

### 1. Ambient Moore--Penrose perturbation

For finite-dimensional real Euclidean spaces, provide a Moore--Penrose inverse for rectangular linear maps or matrices and prove the equal-rank perturbation identity

```text
B† - A† = -B† (B-A) A†
          + B† (B†)ᵀ (B-A)ᵀ (I-AA†)
          + (I-B†B) (B-A)ᵀ (A†)ᵀ A†.
```

Prove that the Penrose products occurring here are orthogonal projections and derive an operator-norm corollary of the form

```text
‖A† - B†‖ ≤ 3 * max ‖A†‖² ‖B†‖² * ‖A-B‖,
```

with the maximum expressed unambiguously, together with the singular-margin specialization

```text
rank A = rank B = r,
σ_r(A) ≥ s, σ_r(B) ≥ s, 0 < s
⊢ ‖A† - B†‖ ≤ 3 * s⁻² * ‖A-B‖.
```

The theorem must allow the row and column spaces of `A` and `B` to move. A full-column-rank special case is useful but is not an adequate replacement for the ambient equal-rank statement.

### 2. Collision-safe two-diagonalizer functional calculus

For real square operators `A` and `B`, each diagonalizable over `ℝ` but not necessarily normal, assume separate diagonalization certificates

```text
A = S diag(α) S⁻¹,    B = T diag(β) T⁻¹,
‖S‖ * ‖S⁻¹‖ ≤ κA,    ‖T‖ * ‖T⁻¹‖ ≤ κB.
```

Allow repeated eigenvalues and unrelated diagonalizers. Define `f(A)` and `f(B)` representation-independently by grouping equal eigenvalues into their aggregate spectral projectors. For every one-Lipschitz `f : ℝ → ℝ`, prove the cross-projector identity

```text
E_λ (A-B) F_γ = (λ-γ) E_λ F_γ
```

and the collision-safe divided-difference expansion, with the `λ = γ` terms shown to vanish rather than divided by zero. Derive a bound such as

```text
‖f(A)-f(B)‖ ≤ (#spec A) * (#spec B) * κA * κB * ‖A-B‖,
```

or the corresponding dimension-squared bound. Also provide `f(0)=0` and bounded-spectrum corollaries controlling `‖f(A)‖` and left-right anchor evaluations

```text
|aᵀ f(A) c - bᵀ f(B) d|
```

by operator and anchor perturbations. No eigengap, eigenvalue matching, common invariant subspace, common diagonalizer, or perturbation bound on `S-T` may be assumed.

### 3. Finite-atomic one-dimensional W1 dual attainment

For two finite atomic probability measures on `ℝ`, define or reuse the finite transport-polytope primal cost with cost `|x-y|`. Prove both weak duality and exact Kantorovich--Rubinstein duality, with attainment by a one-Lipschitz real function. An acceptable concrete construction is the piecewise-linear primitive of the sign of the difference of the two atomic CDFs. Provide a theorem in the form

```text
W1(μ,ν) = sup { |∫ f dμ - ∫ f dν| : LipschitzWith 1 f }
```

and an attaining `f`, plus a direct corollary

```text
(∀ f, LipschitzWith 1 f → |∫ f dμ - ∫ f dν| ≤ ε) ⊢ W1(μ,ν) ≤ ε.
```

The API must be invariant under permutations, zero-weight slots, and splitting or merging atoms at the same location. It may expose an equivalent monotone-coupling/CDF formula, but primal attainment alone or weak duality alone is insufficient.

## Statement / milestones

1. Establish a paper-independent rectangular Moore--Penrose carrier, the Penrose equations, projection facts, the exact equal-rank difference identity, and the singular-margin norm bound.
2. Establish aggregate spectral projectors for separately diagonalized real operators, independence from the chosen eigenbasis inside repeated eigenspaces, the cross-projector identity, and the divided-difference norm estimate.
3. Add anchor-evaluation corollaries for one-Lipschitz functions normalized by `f 0 = 0` and spectra contained in a compact interval.
4. Establish finite-atomic one-dimensional transport/CDF/dual equivalence and construct a maximizing one-Lipschitz potential.
5. Provide a final generic composition theorem: if two positive finite atomic laws are represented by bounded left-right evaluations of `f(A)` and `f(B)`, then their W1 distance is bounded by the operator and anchor perturbations, uniformly through arbitrary eigenvalue collisions.

## May assume / must derive

May assume finite-dimensional real inner-product spaces, finite index types, equal finite rank, a positive lower bound on the smallest positive singular value, real diagonalizability certificates, bounded diagonalizer condition numbers, bounded real spectra, finite nonnegative atomic weights of mass one, and standard measurability/integrability facts for finite sums.

Must derive the ambient pseudoinverse perturbation estimate for moving ranges; aggregate-projector representation independence; cancellation at common eigenvalues; the two-diagonalizer divided-difference estimate; the finite-atomic CDF/monotone-coupling identity or equivalent transport optimality; exact one-dimensional W1 duality and dual attainment; and the generic operator-to-law composition bound.

## Frozen-consumer fidelity

The immediate paper wrapper has a frozen conclusion asserting a finite constant depending only on fixed dimensions, envelopes, positivity, and singular-value margins, with no inverse effect gap, uniformly over every multiplicity pattern. This study preserves that conclusion precisely because its reusable hypotheses are consequences already present in the model construction: equal rank and positive singular margins for observable rectangular maps, bounded condition numbers for each population diagonalizer, bounded spectra, and positive normalized atomic weights.

The study must not require simple spectrum, separated effects, matched labels, a common eigenbasis, a fixed row space, normality, or closeness of chosen diagonalizers. Adding any such premise would fail to discharge the frozen modulus. The paper remains responsible for deriving operator/anchor perturbation from its summaries, proving its factorization and positivity identities, instantiating the generic composition theorem, and extending the law map to its compact summary closure. Thus the study does not prove or assume the paper headline.

## Non-goals

- Do not import or mention paper-specific structures such as `ModelLaw`, `Summary`, `SignalBasis`, `AtomicLaw.LawModulo`, `quotientLaw`, or `gap_free_positive_measure_modulus` in promoted Lean code.
- Do not formalize proxy causal factorization, observed-moment identities, summary closure, nearest-point selection, statistical estimators, confidence sets, or root-n consequences.
- Do not replace the two-diagonalizer theorem by a bound involving coordinatewise eigenvalue matching or `‖S-T‖`/`‖S⁻¹-T⁻¹‖`.
- Do not replace exact finite-atomic W1 duality by only a transport upper bound, primal compactness, or weak duality.
- Do not choose a final Causalean target module in this requirement; the coordinator owns placement and deduplication.

## Known building blocks / proposed imports

Proposed reusable imports include:

- `Mathlib.Analysis.InnerProductSpace.SingularValues`, matrix/continuous-linear-map operator norms, adjoints, finite-dimensional spectral theory, and compact finite-dimensional optimization;
- `Causalean.Mathlib.Analysis.SingularValueWeyl` and `Causalean.Mathlib.Analysis.RectangularSignalSingularValues` for singular-value perturbation and rectangular compression facts;
- `Causalean.Stat.Concentration.Matrix.InversePerturbation` as the square-inverse perturbation analogue;
- finite sums, `Real.exp`/absolute value as needed, finite measures, interval integration, and Lipschitz APIs;
- `Causalean.Stat.Coupling.ProductLossMonotoneCoupling` for coupling, quantile, and rearrangement infrastructure, adapting its bilinear-cost optimality to the cost `|x-y|`.

Search and merge with existing Causalean declarations before introducing new definitions. Prefer linear-map statements with matrix corollaries when that gives the narrowest reusable API.

## Standard reference

Use the standard finite-dimensional Moore--Penrose equal-rank perturbation identity, the spectral-projector divided-difference formula for separately diagonalizable operators, and one-dimensional Kantorovich--Rubinstein duality for finite atomic probability measures. The study must prove the required Lean statements from repository-accepted foundations; these named standard results identify the mathematical target and do not authorize an opaque citation axiom.

## Intended reuse

The immediate consumer is the frozen collision-uniform latent-effect-law modulus in `stat_proxy_effectlaw_eigencollision_frontier`, after paper-local code derives operator and anchor perturbations from observable summaries. The same APIs are intended for future finite-dimensional spectral estimands whose eigenvalues may collide, for moving-range pseudoinverse stability, and for finite-atomic Wasserstein comparisons. Final promoted declarations must remain independent of that consumer and import only Mathlib/Causalean modules.

## Research-folder prerequisites and extraction boundary

The following verified paper-local files are evidence and compatibility-wrapper prototypes only; the study must not import them:

- `Helpers/SpectralSubstrate.lean`: full-column-rank Penrose formula and perturbation bound;
- `Helpers/SubspaceAlignment.lean`: exact equal-range Procrustes algebra, insufficient for moving ranges;
- `Helpers/QuotientFunctionalCalculus.lean`: labelled-coordinate operator/anchor estimate that still carries diagonalizer perturbations;
- `Helpers/AtomicLaw.lean`: finite transport primal attainment, weak dual bound, quotient invariance, metric, topology, and completeness.

If any of these definitions are needed during staging, first generalize the relevant carrier into `CausalSmith/CausalSmith/Substrate/collision-safe-spectral-law/`, leave thin paper compatibility wrappers, and promote the whole neutral dependency closure together. The final promoted modules must import only Mathlib/Causalean and must not duplicate incompatible notions already in Causalean.

## Verification

Require targeted and aggregate builds to pass, source scans to contain no `sorry`, `admit`, `axiom`, or unsafe proof shortcuts, and `#print axioms` on each public endpoint to report only the standard logical axioms accepted by the repository. Verify the public statements byte-for-byte after proof filling and verify that the promoted dependency closure contains no import matching `CausalSmith.*_Research`.
