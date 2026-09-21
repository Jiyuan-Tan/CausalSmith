# Substrate requirement: finite-cell-conditional-moment-bridge

## Goal
Build reusable finite-cell conditional-moment factorization and almost-sure support-transfer theorems for normalized restricted measures.

## Provides (API contract)
- A componentwise factorization theorem: for a probability measure `P`, measurable positive finite-mass event `C`, and measurable/integrable finite-dimensional random variables, a bounded-test conditional factorization identity implies coordinatewise first/cross-moment factorization and composes into finite matrix/outer-product equality.
- A support-transfer theorem: inside a positive cell `C`, if a measurable arm event `A` has positive conditional mass, `Ypot` is conditionally independent of `A`, `Yobs = Ypot` almost surely on `C ∩ A`, and `|Yobs| ≤ R` there, then `|Ypot| ≤ R` almost surely under `P.restrict C`.
- An adapter from bounded-test normalized-integral factorization to `CondIndepFun` is acceptable if both requested consequences follow.

## Statement / milestones
For factorization, support finite Euclidean coordinate types and normalized restricted integrals without globally bounded sample spaces. For support transfer, expose measurability, integrability, cell/arm positivity, conditional independence, consistency, and observed-arm bounds explicitly. Prove the conclusion outside the observed arm from independence and positivity; do not assume it.

## Standard reference
Standard conditional-independence consequences: factorization of integrable coordinate products, and transport of an almost-sure support restriction across a conditionally independent positive-probability binary arm within a conditioning cell.

## Intended reuse
`stat_proxy_effectlaw_eigencollision_frontier/v1` uses bounded-test normalized-restriction identities to assemble proxy-moment matrices coordinatewise and to transfer an observed outcome-product bound to latent potential outcomes. The result should be reusable for finite latent cells, proxy models, missing-data arms, and discrete conditioning strata.

## May assume / must derive
May assume a probability measure, measurable positive finite-mass cells/events, and the standard integrability/measurability hypotheses needed for restricted integrals. Must derive coordinatewise/matrix factorization and the almost-everywhere latent support conclusion. Standard axioms only.

## Non-goals
Do not import or mention any `*_Research` module, `FullData`, `UCVMWModel`, proxy matrices, latent class names, or paper effect radii. Do not require globally bounded sample spaces or assume the desired support bound outside the observed arm.

## Known building blocks
Use Mathlib restricted-measure, conditional independence, indicator/truncation, finite-coordinate, and almost-everywhere lemmas where available. The consumer has its own `conditionalMean` notation and will supply thin wrappers after promotion.

Verification: targeted build green, zero `sorry`/`admit`/custom axioms, and `#print axioms` limited to standard Lean axioms.
