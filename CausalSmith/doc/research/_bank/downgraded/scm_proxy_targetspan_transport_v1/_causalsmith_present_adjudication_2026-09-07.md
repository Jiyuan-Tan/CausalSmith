# Presentation adjudication — 2026-09-07

Authoritative scope: `internal/mill/needs_user/scm_proxy_targetspan_transport.resolved.md`.

## Theorem-level citation comparison

- Iglesias-Alonso, Schur, von Kügelgen, and Peters, *Transferring Causal Effects using Proxies*, NeurIPS 2025, arXiv:2510.25924v2. Their Assumption 1 requires `rank P(W | E,x) ≥ |U|` for every treatment value; Theorem 1 identifies the target interventional law by `P(y | E,x) P(W | E,x)^† Q(W)`. Their reduced estimator has a pointwise asymptotic-normality result under that full-rank regime. The manuscript now distinguishes that formula and inference result from the present coverage-only projection theorem.
- Zhang, Li, Miao, and Tchetgen Tchetgen, *Proximal Causal Inference without Uniqueness Assumptions*, Statistics & Probability Letters 198 (2023), 109836, DOI 10.1016/j.spl.2023.109836, arXiv:2303.10134v4. Proposition 2.3 identifies a linear functional over a nonunique outcome-bridge fiber exactly under membership in the orthogonal complement of the operator null space; Lemma 2.4 makes adjoint-range membership necessary for root-n estimability under its additional regularity condition.
- Rahiminasab, Soumi, Klami, and Kaski, *Point-Identification of a Robust Predictor Under Latent Shift with Imperfect Proxies*, arXiv:2603.15158v3. Definition 3 imposes full column rank on the source-environment mixture matrix over proxy-induced latent equivalent classes; Theorem 3 identifies the target predictor because the target operator is a linear combination of the distinguishing source operators, subject to the paper's bridge-existence and LEC-spanning conditions.

The novelty language is confined to the SCM-specific exact criterion over the compatible full-joint-law fiber, its strictly positive full-law converse, and the weak-rank coverage/separation results. The manuscript expressly does not claim abstract span, null-space, or cross-domain operator geometry as new.

## Frozen-layer adjudications

- **Proxy matrix index order.** Lean defines `condProxyMatrixOfObservedLaw` as `Matrix W E ℝ` with entry function `fun w e => ...`; proxy states are rows and environments are columns. The frozen `ass:array-target-span` display writes `B_{x,n}(e,w)` even though its probability expression and all downstream matrix products use the Lean `B_{x,n}(w,e)` convention. Per supervisor direction, the frozen body and Lean source were not edited. Surrounding prose now states the verified convention and discloses the typographical reversal in the frozen display.
- **Identified interval versus identified set.** Lean's `Causalean.PartialID.IdentifiedInterval` is definitionally `Set.range` over feasible parameters. `target_span_iff` proves `Set.Subsingleton` of that set, while the converse proves inclusion of an open interval; neither proves global interval geometry. Per supervisor direction, the frozen theorem displays and Lean source were not edited. Surrounding prose now uses “identified-value set” and explains the Lean name.

## Referee finding disposition

- Fixed in authored prose: theorem-level competitor positioning, Wald-scope overclaim, model-definition order, signed balancing weights, projection-generality wording, structural cross-references, affirmative contribution framing, and verification-scope disclosure.
- Declined by supervisor: a new finite-sample simulation study. The limitations section explicitly states that the paper proves coverage rather than informativeness or shrinkage, and that the proposed simulation study is outside the verified scope and is not reported.
- Frozen formal/Lean edits: none.

## Single authorized P5 re-review

- Score trajectory: 6.4/10 (initial review, 11 findings) to 5.7/10 (single authorized re-review, 9 findings).
- The re-review credits the exact identification frontier, the SCM-compatible full-law converse, the positive weak-rank witness, faithful finite-sample coverage statement, changing-rank separation, and theorem-level related-work comparison.
- Its three central residual requests are a new informativeness/diameter theorem, an endpoint solver and reproducible implementation, and a simulation study. These are new research/implementation scope rather than presentation repairs. The supervisor declined the simulation expansion and directed no further P5 loop when the score remained controlled by that absent empirical/informativeness program.
- The residual request to rewrite the frozen proxy-index display is dismissed under the authoritative no-frozen-layer-edit instruction; Lean establishes the `W × E` order and the prose discloses it.
- No second P5 re-entry was run. The bundle proceeds to P6 with the declined finding visible in the paper and in this adjudication record.
