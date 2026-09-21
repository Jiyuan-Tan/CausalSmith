import { readFileSync, writeFileSync } from 'node:fs';

const root = '<repo-root>';
const out = `${root}/CausalSmith/doc/study/absolute-value-moment-prior-duality/coordinate_staging/round_1`;

const area = JSON.parse(readFileSync(`${root}/doc/library_review/Mathlib.json`, 'utf8'));
for (const decl of [
  'Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.exists_bestPolynomialAbs',
  'Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate.exists_fourierPoly_sinDouble',
  'Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.exists_symmetric_momentMatched_absGap',
  'Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs_order'
]) if (!area.headline_theorems.includes(decl)) area.headline_theorems.push(decl);
area.namespace_intros['Analysis.AbsoluteValueMomentPriorDuality'] =
  'Best uniform polynomial approximation of absolute value on the unit interval, its finite-dimensional measure duality, symmetric moment-matched probability priors, and universal inverse-degree bounds.';
area.namespace_intros['Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate'] =
  'Fourier-analytic Fejér and de la Vallée--Poussin certificate machinery for the inverse-degree lower bound in absolute-value approximation.';
writeFileSync(`${out}/mathlib.json`, `${JSON.stringify(area, null, 2)}\n`);

let api = readFileSync(`${root}/doc/API.md`, 'utf8');
api += `

## 10a''''''''. \`Mathlib/Analysis/AbsoluteValueMomentPriorDuality/\` — absolute-value approximation and moment-prior duality

Reusable approximation-theory infrastructure for the nonsmooth function x ↦ |x| on the unit interval. It defines the intrinsic best uniform polynomial error, proves the exact dual construction of symmetric probability measures with matched polynomial moments, and establishes universal inverse-degree upper and lower bounds. The Fourier certificate is kept in a separate support module; the API module is the consumer-facing import.

### Basic approximation facts

<!-- GEN:Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Basic -->
<!-- /GEN -->

### Fourier certificate

<!-- GEN:Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Fejer -->
<!-- /GEN -->

### Measure duality and prior projections

<!-- GEN:Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Duality -->
<!-- /GEN -->

### Inverse-degree approximation rate

<!-- GEN:Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Rate -->
<!-- /GEN -->

<!-- GEN:Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality -->
<!-- /GEN -->
`;
writeFileSync(`${out}/API.md`, api);
