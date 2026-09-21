import fs from 'node:fs';
import path from 'node:path';

const root = '<repo-root>';
const source = path.join(root, 'CausalSmith/CausalSmith/Substrate/FinitePerronFrobeniusPositiveEigenvector');
const out = path.join(root, 'CausalSmith/doc/study/finite-perron-frobenius-positive-eigenvector/coordinate_staging/round_2');
const oldNs = 'CausalSmith.Substrate.FinitePerronFrobeniusPositiveEigenvector';
const newNs = 'Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector';

const docs = {
  Basic: {
    EVec: 'A Euclidean real vector [indexed by a finite coordinate type](hyp:ι), called [a finite real coordinate vector](goal), [is given by the Euclidean space on that coordinate type](step:1).',
    absVec: 'The Euclidean vector obtained from [a finite real vector](hyp:x) by [taking the absolute value of every coordinate](goal) [is given coordinate by coordinate](step:1).',
    rayleighForm: 'The quadratic form associated with [a finite real matrix](hyp:A) and [a Euclidean coordinate vector](hyp:x), called [its Rayleigh form](goal), [is given by the vector-matrix-vector quadratic sum](step:1).',
    sphereRayleighValue: 'The greatest quadratic Rayleigh-form value among [the Euclidean unit vectors for a finite real matrix](hyp:A), called [the Euclidean-sphere top Rayleigh value](goal), [is given by a supremum](step:1).',
    coordinateSphereRayleighValue: 'The greatest quadratic Rayleigh-form value among [the coordinate vectors whose squared coordinates sum to one for a finite real matrix](hyp:A), called [the coordinate-sphere top Rayleigh value](goal), [is given by a supremum](step:1).',
    iSupRayleighValue: "Mathlib's supremum Rayleigh quotient for [a finite real matrix](hyp:A), called [the nonzero-vector top Rayleigh value](goal), [is given by the matrix's Euclidean linear map](step:1).",
    coordinateSphereRayleighValue_eq_sphereRayleighValue: 'With [a finite real matrix](hyp:A), [the coordinate and Euclidean unit-sphere top Rayleigh values agree](goal).',
    sphereRayleighValue_eq_iSupRayleighValue: "On a nonempty finite coordinate space, [a real matrix](hyp:A) has [its Euclidean unit-sphere top value equal to Mathlib's supremum Rayleigh quotient](goal).",
    coordinateSphereRayleighValue_eq_iSupRayleighValue: "On a nonempty finite coordinate space, [a real matrix](hyp:A) has [its coordinate unit-sphere top value equal to Mathlib's supremum Rayleigh quotient](goal).",
    exists_unit_isMaxOn_rayleighForm: 'On a nonempty finite coordinate space, [a real symmetric matrix](hyp:A,hA) has [a unit vector attaining its Euclidean-sphere top Rayleigh value](goal).',
    exists_unit_eigenvector_sphereRayleighValue: 'On a nonempty finite coordinate space, [a real symmetric matrix](hyp:A,hA) has [a unit eigenvector at its Euclidean-sphere top Rayleigh value](goal).'
  },
  AbsoluteValue: {
    norm_absVec: 'With [a Euclidean coordinate vector](hyp:x), [coordinatewise absolute value preserves its Euclidean norm](goal).',
    absVec_nonneg: 'With [a Euclidean coordinate vector](hyp:x) and [a coordinate](hyp:i), [the corresponding coordinatewise absolute value is nonnegative](goal).',
    rayleighForm_le_absVec: 'An [entrywise nonnegative finite real matrix](hyp:A,hA) and [a Euclidean coordinate vector](hyp:x) satisfy [that taking coordinatewise absolute values cannot lower the Rayleigh form](goal).',
    absVec_mem_sphere: 'A [radius](hyp:r) and [a Euclidean coordinate vector on the sphere of that radius](hyp:x,hx) satisfy [that coordinatewise absolute value remains on the same sphere](goal).',
    rayleighForm_absVec_eq_of_isMaxOn: 'An [entrywise nonnegative finite real matrix](hyp:A,hA), [a unit-sphere vector](hyp:x,hx), and [its Rayleigh-form maximality](hyp:hmax) ensure [that taking coordinatewise absolute values preserves the Rayleigh-form value](goal).',
    absVec_isMaxOn: 'An [entrywise nonnegative finite real matrix](hyp:A,hA), [a unit-sphere vector](hyp:x,hx), and [its Rayleigh-form maximality](hyp:hmax) ensure [that coordinatewise absolute value is another unit-sphere maximizer](goal).',
    absVec_eigenvector_of_isMaxOn: 'On a nonempty finite coordinate space, an [entrywise nonnegative symmetric real matrix](hyp:A,hA_symm,hA_nonneg), [a unit-sphere vector](hyp:x,hx), and [its Rayleigh-form maximality](hyp:hmax) ensure [that the coordinatewise absolute vector is an eigenvector at the top Rayleigh value](goal).',
    absVec_preserves_top_eigenvector: 'On a nonempty finite coordinate space, an [entrywise nonnegative symmetric real matrix](hyp:A,hA_symm,hA_nonneg) and [a normalized top eigenvector](hyp:x,hx_norm,hx_eigen,hx_top) ensure [that coordinatewise absolute value is a normalized nonnegative top eigenvector with the same top value](goal).'
  },
  Positivity: {
    zero_coordinate_propagates_across_positive_entry: 'An [entrywise nonnegative matrix](hyp:A,hA_nonneg), [a nonnegative eigenvector](hyp:x,hx_nonneg,hx_eigen), [a row coordinate where it vanishes](hyp:i,hxi), and [a strictly positive matrix entry from that row](hyp:j,hAij) ensure [that the eigenvector also vanishes at the entry’s target coordinate](goal).',
    'IsIrreducible.eigenvector_pos': 'An [irreducible finite matrix](hyp:hA) and [a nonnegative nonzero eigenvector](hyp:x,hx_nonneg,hx_ne,hx_eigen) ensure [that every coordinate is strictly positive](goal).',
    'IsIrreducible.unit_eigenvector_pos': 'An [irreducible finite matrix](hyp:hA) and [a normalized nonnegative eigenvector](hyp:x,hx_nonneg,hx_norm,hx_eigen) ensure [that every coordinate is strictly positive](goal).'
  },
  Restriction: {
    restrictMatrix: 'The principal submatrix of [a finite real matrix](hyp:A) on [a finite set of coordinates](hyp:s), called [its restricted matrix](goal), [is given by selecting those rows and columns](step:1).',
    restrictVec: 'The Euclidean vector obtained by restricting [a finite real vector](hyp:x) to [a finite coordinate set](hyp:s), called [its restricted vector](goal), [is given by retaining those coordinates](step:1).',
    zeroExtendVec: 'The Euclidean vector obtained by extending [a vector on a finite coordinate subtype](hyp:x) by zero outside [that finite coordinate set](hyp:s), called [its zero extension](goal), [is given coordinate by coordinate](step:1).',
    zeroExtendMatrix: 'The matrix obtained by extending [a matrix on a finite coordinate subtype](hyp:B) by zero outside [that coordinate set](hyp:s), called [its zero extension](goal), [is given entry by entry](step:1).',
    restrictVec_zeroExtendVec: 'A [finite coordinate set](hyp:s) and [a vector on its subtype](hyp:x) satisfy [that restricting its zero extension recovers the original subtype vector](goal).',
    norm_zeroExtendVec: 'A [finite coordinate set](hyp:s) and [a vector on its subtype](hyp:x) satisfy [that zero extension preserves Euclidean norm](goal).',
    zeroExtendMatrix_mulVec_zeroExtendVec: 'A [finite coordinate set](hyp:s), [a subtype matrix](hyp:B), and [a subtype vector](hyp:x) satisfy [that applying the zero-extended matrix to the zero-extended vector equals the zero extension of the subtype action](goal).',
    rayleighForm_zeroExtendMatrix_zeroExtendVec: 'A [finite coordinate set](hyp:s), [a subtype matrix](hyp:B), and [a subtype vector](hyp:x) satisfy [that zero extension preserves their Rayleigh form](goal).',
    sphereRayleighValue_zeroExtendMatrix: 'On a nonempty finite coordinate space, [a nonempty finite coordinate set](hyp:s) and [an entrywise nonnegative subtype matrix](hyp:B,hB) satisfy [that zero extension preserves its top Rayleigh value](goal).',
    restrictMatrix_isSymm: 'A [symmetric finite matrix](hyp:hA) and [a finite coordinate set](hyp:s) ensure [that the principal restricted matrix remains symmetric](goal).',
    restrictMatrix_nonneg: 'An [entrywise nonnegative finite matrix](hyp:hA) and [a finite coordinate set](hyp:s) ensure [that the principal restricted matrix remains entrywise nonnegative](goal).',
    restrictMatrix_mulVec_restrictVec_of_zero_off: 'A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), and [a vector](hyp:x) that [vanishes outside the set](hyp:hx) ensure [that restriction commutes with applying the matrix](goal).',
    mulVec_zeroExtendVec_of_closed: 'A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), and [block closure from outside rows into the set](hyp:hclosed) ensure [that applying the original matrix to a zero extension equals the zero extension of the restricted action](goal).',
    zeroExtendVec_eigenvector_of_closed: 'A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), [block closure from outside rows into the set](hyp:hclosed), and [a restricted eigen-equation](hyp:x,hx) ensure [that zero extension satisfies the corresponding global eigen-equation](goal).',
    rayleighForm_restrictVec_of_zero_off: 'A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), and [a vector that vanishes outside that set](hyp:x,hx) ensure [that restriction preserves its Rayleigh form](goal).',
    sphereRayleighValue_restrictMatrix_le: 'On a nonempty finite coordinate space, [a finite matrix](hyp:A) and [a nonempty finite coordinate set](hyp:s) satisfy [that the restricted top Rayleigh value is at most the global top Rayleigh value](goal).',
    sphereRayleighValue_restrictMatrix_eq_of_supported_maximizer: 'On a nonempty finite coordinate space, [a finite matrix](hyp:A), [a nonempty finite coordinate set](hyp:s), and [a global unit maximizer supported on that set](hyp:x,hx_norm,hx_support,hx_top) ensure [that the restricted and global top Rayleigh values agree](goal).'
  },
  Main: {
    finite_positive_perron_eigenvector: 'A [real symmetric irreducible finite matrix](hyp:A,hA_symm,hA_irred) has [a strictly positive unit eigenvector whose eigenvalue is simultaneously the coordinate-sphere, Euclidean-sphere, and nonzero-vector top Rayleigh value](goal).',
    finite_positive_perron_eigenvector_on_restriction: 'A [symmetric finite matrix](hyp:A,hA_symm), [a nonempty finite coordinate set](hyp:s), [an irreducible restricted block](hyp:hA_irred), and [block closure from outside rows into that set](hyp:hclosed) ensure [that the block’s strictly positive unit Perron vector zero-extends to a global eigenvector](goal).'
  }
};

for (const file of Object.keys(docs)) {
  let text = fs.readFileSync(path.join(source, `${file}.lean`), 'utf8')
    .replaceAll(oldNs, newNs);
  text = text.replace(/\/--[\s\S]*?-\//g, (old, offset) => {
    const rest = text.slice(offset + old.length);
    const match = rest.match(/(?:@\[[^\]]+\]\s*)?(?:abbrev|def|theorem)\s+([A-Za-z0-9_.]+)/);
    if (!match || !docs[file][match[1]]) return old;
    return `/-- ${docs[file][match[1]]} -/`;
  });
  fs.writeFileSync(path.join(out, `${file.toLowerCase()}.lean`), text);
}

const combined = ['basic', 'absolutevalue', 'positivity', 'restriction', 'main']
  .map((file, i) => {
    const text = fs.readFileSync(path.join(out, `${file}.lean`), 'utf8');
    return i === 0 ? text : text.replace(/^import Causalean[^\n]*\n/gm, '');
  })
  .join('\n');
fs.writeFileSync(path.join(out, 'all.lean'), combined);

const reviewPath = path.join(root, 'doc/library_review/Mathlib.json');
const review = JSON.parse(fs.readFileSync(reviewPath, 'utf8'));
const headlines = [
  'Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.exists_unit_eigenvector_sphereRayleighValue',
  'Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.absVec_eigenvector_of_isMaxOn',
  'Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.IsIrreducible.eigenvector_pos',
  'Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.sphereRayleighValue_zeroExtendMatrix',
  'Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.finite_positive_perron_eigenvector'
];
for (const name of headlines) if (!review.headline_theorems.includes(name)) review.headline_theorems.push(name);
review.namespace_intros['LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector'] =
  'Finite-dimensional Perron--Frobenius infrastructure for symmetric entrywise-nonnegative irreducible real matrices: Rayleigh maxima, absolute-value maximizers, positivity propagation, and restriction/zero-extension bridges.';
fs.writeFileSync(path.join(out, 'mathlib.json'), `${JSON.stringify(review, null, 2)}\n`);

const apiPath = path.join(root, 'doc/API.md');
let api = fs.readFileSync(apiPath, 'utf8');
const apiSection = `## Mathlib/LinearAlgebra/FinitePerronFrobeniusPositiveEigenvector — finite positive Perron eigenvectors

This finite-dimensional Perron--Frobenius substrate supplies a strictly positive, unit-norm top eigenvector for a symmetric, entrywise-nonnegative irreducible real matrix. It also exposes interchangeable Rayleigh-value presentations and component restriction/zero-extension bridges for finite graph and network arguments.

### Rayleigh-value interface

<!-- GEN:Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Basic -->
<!-- /GEN -->

### Absolute-value maximizers

<!-- GEN:Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.AbsoluteValue -->
<!-- /GEN -->

### Irreducible positivity

<!-- GEN:Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Positivity -->
<!-- /GEN -->

### Restriction and zero extension

<!-- GEN:Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Restriction -->
<!-- /GEN -->

### Perron--Frobenius theorem

<!-- GEN:Causalean.Mathlib.LinearAlgebra.FinitePerronFrobeniusPositiveEigenvector.Main -->
<!-- /GEN -->

`;
const apiAnchor = '## Mathlib/Algorithms/MonotoneWindowDeque — verified finite sliding-window maxima';
if (!api.includes(apiSection)) {
  if (!api.includes(apiAnchor)) throw new Error(`missing API anchor: ${apiAnchor}`);
  api = api.replace(apiAnchor, `${apiSection}${apiAnchor}`);
}
fs.writeFileSync(path.join(out, 'api.md'), api);
