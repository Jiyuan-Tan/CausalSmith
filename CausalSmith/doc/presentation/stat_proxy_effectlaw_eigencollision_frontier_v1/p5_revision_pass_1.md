# Holistic revision pass 1

- mode: reframe
- source digest before: `6792ad38d1cf6d0eb099b7c6e9de3c344b2daafe26f09b5a92482cbf2908fda6`
- source digest after: `c87fc7808c6c58e96a5c984a77ef3d32429c4c07c6c1ffadc0c2944dbc9dba31`

## Reviser report

Completed the P5 reframe revision in the authored sources.

Changed:
`front_matter.tex`, all `sections/01` through `sections/09`, and `proofs/lem:witness-observed-arm-mass.tex`.

Addressed the routed rewrite findings by:
- Reframing `\nu_P` as the population-weighted law of latent-class average treatment effects, with an explicit distinction from unit-level contrasts.
- Scoping computation claims to the fixed-dimensional unit-cost exact-real model and separating data-facing reports from theorem-side validity quantities.
- Clarifying raw coordinates, valid represented probability laws, and quotient laws in setup prose.
- Adding a dependency roadmap and known/supplied conditioning-input discussion.
- Qualifying lower-bound sharpness as proved on the explicit two-class specialization.
- Removing reader-facing `\leanref` references and stale external-dependency language.
- Replacing “sharp summary-inversion set” in ordinary prose with exact repaired-image terminology.

Declined/left to upstream where P5 forbids the requested edit:
- Moving/deleting/reordering duplicate frozen formal environments for `definition-order-and-duplication`.
- Renaming or changing formal environment bodies for `atomic-law-validity-typing`, `computational-report-scope`, and remaining formal/open-question “sharp” terminology. I repaired the surrounding prose instead.

Verification:
- Temporary authored-source PDF build with `latexmk` succeeded.
- Final build log has no unresolved references or citations.
- Scans found no `\leanref`, `\ref`, `\eqref`, or `\autoref` in editable sources.
- Targeted prose scan found no remaining routed prohibited phrases outside frozen/open-question contexts.

I did not attempt the out-of-scope citation research, artifact metadata/source-change work, or simulation finding.
