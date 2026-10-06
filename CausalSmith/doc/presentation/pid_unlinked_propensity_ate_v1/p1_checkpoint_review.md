# P1 checkpoint review

- `thm:k-label-rate` / `def:optimal-k-ambiguity`: accepted. The theorem uses the defined symbol `\Delta_K(H)` directly and is placed immediately after its definition in the same section; an additional cross-reference would duplicate that local definition.
- `thm:k-label-rate` / `def:worst-case-ambiguity`: accepted. The theorem's phrase “ambiguity” and `\Delta_K(H)` inherit `D_H(g)` through the immediately preceding optimal-ambiguity definition; the mathematical dependency is visible without a second cross-reference in the theorem block.
- `synth_4` visibility note: retained. The generalized-quantile definition is visibly consumed by `def:mean-endpoints`, `lem:fixed-released-law-baseline`, and their displayed `Q_{F_{ar}}` and `Q_{W_{ar}}` formulas. The “no visible user” state note is a notation-spelling false advisory rather than ballast.

All P1 frozen bodies passed the Lean equivalence judge after these advisories were reviewed.
