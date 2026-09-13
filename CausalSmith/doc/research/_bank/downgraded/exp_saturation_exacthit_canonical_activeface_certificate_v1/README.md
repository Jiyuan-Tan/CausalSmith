---
qid: exp_saturation_exacthit_canonical_activeface_certificate
spec: v1
topic: "Canonical active-face certificates for exact-hit saturation-policy design. This is a new attempt at parent exp_saturation_exacthit_deficiency_design, not a retry of its nonmeasurable full-open-simplex scaffold. Fix K>=3, cluster size n0, distinct rational interior counts m_k, unrestricted binary within-cluster potential-outcome schedules, and exact-slice welfare U_k. Compare exact-count allocation a with nominal-label Bernoulli assignment p, whose exact-hit rates are q=Bp with B_kl=Pr{Bin(n0,m_l/n0)=m_k}. For each active face define the all-Borel randomized-selector Gaussian simple-regret value G_A(v,r), with singleton value zero and infinity at action-relevant zero information. Construct a terminating rational certificate that analytically prunes the exact-count boundary, partitions only closed positive-rate and covariance cells, returns outward epsilon brackets and all-minimizer cells for inf_a G_K(v,a) and inf_p G_K(v,Bp), and chooses lexicographically first designs only on an explicit finite certified grid. Realize every finite selector by a fixed inverse-CDF map jointly Borel in pilot covariance, screening and decision statistics, and an auxiliary uniform; covariance partitions apply only when |A|>=2. For primitive transfer, work at attainable binary full-tie baselines with v in a declared positive domain and O(C^-1/2) covariance neighborhoods, not exact membership in arbitrary singleton variance boxes. Prove a uniform calibrated three-way-split LAN risk sandwich over deterministic allocation sequences, including a vanishing-share converse and partial-tie subfaces. Return certified regret and cluster-count ratios; decide strict loss from the rational total-hit condition and provide finite certificates for positive excess over the mass floor, without claiming a total numerical equality oracle. Use the n0=6 menu m=(1,2,4), legal variance box [1/8,1/4]^3, and Egger et al.'s Kenya saturation design as the worked consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived G_K(v,a)>=kappa sqrt(v_i/a_i), giving the explicit uniform prune eta=1/1024 on [1/8,1/4]^3, and realized every variance there at a full tie using W in {0,1/2,1}. Ordered finite cells plus inverse-CDF weights give a canonical Borel evaluator. A vanishing allocation share makes local alternatives indistinguishable and forces divergent scaled regret. For the three-label menu on active face {1,2}, exact rational interval arithmetic gives p3*=0, p1*=0.289596897074... and regret ratio in [1.296043143254,1.296043143255]. Destructive checks rejected the parent's illegal [1,2]^3 binary witness, exact covariance membership in arbitrary V, global least-rational choices, and a purported total equality decision; the corrected statements preserve the model and target. UNRESOLVED BOTTLENECK: Prove the quantitatively uniform primitive risk sandwich for the finite canonical receipt family, combining calibrated ratio errors, screening tails, enlarged covariance cells, finite-prior uniform LAN, and one computable diagonal schedule. EARLY KILL TEST: Build a fixed-tolerance n0=6,K=3 receipt on [1/8,1/4]^3 with eta=1/1024, exact singleton branches, boundary-safe inverse-CDF decoding, a full-observation finite-prior lower bound, and independent-screen upper risk; reproduce the solved active-pair interval and one full-tie three-arm covariance before attempting the general theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_saturation_exacthit_canonical_activeface_certificate.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No uniform finite-prior lower transfer, selector upper transfer, computable diagonal schedule, finite effective encoding for arbitrary f, or all-minimizer certification; 461/250 is exact only for the pairwise surrogate and its derived regret bound."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The proposal's terminating all-Borel Gaussian simple-regret certificate (including outward brackets and all-minimizer cells) remains open; the delivered H/KKT and empirical-best pairwise-regret surrogate is a strictly weaker object and must be reframed as the contribution or completed."
  - "The note proves a sharp covariance image and certified optimization of the worst compatible pairwise variance H, but it does not solve the advertised exact all-selector minimax-regret design problem, which remains explicitly open."
  - "The regret theorem is only an upper bound for the empirical-best selector, with no matching converse showing that H determines minimax regret or that the reported designs minimize actual policy-selection risk."
reusable_artifacts:
  - discovery/core.json
  - discovery/proto_core_angle0_rejected.json
  - discovery/solve_thm_design_based_regret_bound.json
  - discovery/solve_tex/solve_thm_design_based_regret_bound.tex
  - discovery/writeup.tex
seeds_burned: [0, 1]
proof_attempt_summary: |
  The run first repaired the parent's illegal diagonal covariance model, then pivoted to a sharp
  covariance-image theorem and exact pairwise-H/KKT allocation certificates for the balanced
  six-unit design. The finite-population covariance analysis and the 461/250 pairwise-surrogate
  ratio survived, but the promised terminating all-Borel minimax-regret certificate collapsed:
  arbitrary real marginal tables lack an effective input representation, and no uniform Gaussian-game
  approximation or all-minimizer certification theorem was established. A future re-raise should reuse
  the covariance and KKT artifacts while treating that Gaussian decision-theory layer as new substrate.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 33270870
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-08"
---

# exp_saturation_exacthit_canonical_activeface_certificate / v1 — Downgraded

**Topic.** Canonical active-face certificates for exact-hit saturation-policy design. This is a new attempt at parent exp_saturation_exacthit_deficiency_design, not a retry of its nonmeasurable full-open-simplex scaffold. Fix K>=3, cluster size n0, distinct rational interior counts m_k, unrestricted binary within-cluster potential-outcome schedules, and exact-slice welfare U_k. Compare exact-count allocation a with nominal-label Bernoulli assignment p, whose exact-hit rates are q=Bp with B_kl=Pr{Bin(n0,m_l/n0)=m_k}. For each active face define the all-Borel randomized-selector Gaussian simple-regret value G_A(v,r), with singleton value zero and infinity at action-relevant zero information. Construct a terminating rational certificate that analytically prunes the exact-count boundary, partitions only closed positive-rate and covariance cells, returns outward epsilon brackets and all-minimizer cells for inf_a G_K(v,a) and inf_p G_K(v,Bp), and chooses lexicographically first designs only on an explicit finite certified grid. Realize every finite selector by a fixed inverse-CDF map jointly Borel in pilot covariance, screening and decision statistics, and an auxiliary uniform; covariance partitions apply only when |A|>=2. For primitive transfer, work at attainable binary full-tie baselines with v in a declared positive domain and O(C^-1/2) covariance neighborhoods, not exact membership in arbitrary singleton variance boxes. Prove a uniform calibrated three-way-split LAN risk sandwich over deterministic allocation sequences, including a vanishing-share converse and partial-tie subfaces. Return certified regret and cluster-count ratios; decide strict loss from the rational total-hit condition and provide finite certificates for positive excess over the mass floor, without claiming a total numerical equality oracle. Use the n0=6 menu m=(1,2,4), legal variance box [1/8,1/4]^3, and Egger et al.'s Kenya saturation design as the worked consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived G_K(v,a)>=kappa sqrt(v_i/a_i), giving the explicit uniform prune eta=1/1024 on [1/8,1/4]^3, and realized every variance there at a full tie using W in {0,1/2,1}. Ordered finite cells plus inverse-CDF weights give a canonical Borel evaluator. A vanishing allocation share makes local alternatives indistinguishable and forces divergent scaled regret. For the three-label menu on active face {1,2}, exact rational interval arithmetic gives p3*=0, p1*=0.289596897074... and regret ratio in [1.296043143254,1.296043143255]. Destructive checks rejected the parent's illegal [1,2]^3 binary witness, exact covariance membership in arbitrary V, global least-rational choices, and a purported total equality decision; the corrected statements preserve the model and target. UNRESOLVED BOTTLENECK: Prove the quantitatively uniform primitive risk sandwich for the finite canonical receipt family, combining calibrated ratio errors, screening tails, enlarged covariance cells, finite-prior uniform LAN, and one computable diagonal schedule. EARLY KILL TEST: Build a fixed-tolerance n0=6,K=3 receipt on [1/8,1/4]^3 with eta=1/1024, exact singleton branches, boundary-safe inverse-CDF decoding, a full-observation finite-prior lower bound, and independent-screen upper risk; reproduce the solved active-pair interval and one full-tie three-arm covariance before attempting the general theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_saturation_exacthit_canonical_activeface_certificate.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The proposal's terminating all-Borel Gaussian simple-regret certificate remains open; the delivered sharp covariance image and pairwise-H/KKT surrogate is sound but graded subfield below the field floor.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
