# Referee review

**Recommendation:** major_revision
**Overall score:** 6.4/10 — The verified all-radius minimax frontier is a substantial contribution, but the manuscript requires major restructuring and several foundational clarifications before its scope and argument are publication-ready.

The paper characterizes a cardinality-uniform minimax risk surface for stationary off-policy evaluation in finite POMDPs under action overlap, contraction, and latent stationary overlap, with matching PHIW upper bounds and signed-depth lower bounds. The all-radius formula and its unit, fixed-radius, and local slices are strong and faithfully supported by the verification contract. Publication is presently hindered by an internally unclear definition of the statistical experiment, premature stationary-law notation, an excessively mechanical proof presentation, and several smaller scope and framing issues.

## Strengths
- The master theorem gives a sharp, uniform-in-C risk surface with constants independent of both state-space cardinalities and the stationary-overlap radius.
- The upper and lower bounds are tied to explicit constructions: a radius-calibrated PHIW estimator, signed-depth alternatives, and a separate parametric subexperiment.
- The manuscript distinguishes fixed-radius, unit-overlap, and shrinking-radius regimes and accurately identifies the T^{-1/2} overlap-distance elbow.
- The limitations section candidly records the growing hidden alphabet, unknown-radius adaptation, inference, and empirical testability issues.
- The related-work section engages Hu--Wager and Mehrabi--Wager at the level of rates, overlap objects, observation structures, and inferential targets rather than through citations alone.
- The verification contract supports the displayed formal statements and proofs, including the headline theorem and the finite insulin certificates.

## Findings
- **[major·statement] Setup and estimands** — The statistical experiment is not coherently specified in the manuscript. The model-class tuple contains “L(O_T),” an observed-data law, while the Markov, sequential-ignorability, and stationary-start restrictions are statements about the latent full trajectory. Later the appendix separately introduces a full law and observation map, but those objects are needed to understand the model class itself.
  - *Fix:* Define the primitive experiment from the outset using the full trajectory law, then define the observed law as its pushforward under the observation map. Rewrite the model-class and risk definitions accordingly while preserving that estimators receive only the observed trajectory and revealed policies.
- **[major·statement] Setup and estimands** — The presentation-level definition “Behavior and target stationary joint-state laws” defines P_p as a Markov kernel and d_p as its stationary law before b and e have been required to be probability vectors and before contraction has supplied existence and uniqueness. For a raw policy carrier, P_p need not yet be stochastic, so the definition is logically premature as written.
  - *Fix:* Move this definition after the policy-vector and contraction conditions, or explicitly condition it on models satisfying those restrictions. State that contraction gives a unique stationary probability law for each of b and e.
- **[major·structure] Proofs and auxiliary constructions** — The appendix reproduces lengthy, mechanically structured proof transcripts whose local bookkeeping overwhelms the econometric argument. The central ideas—radius-sensitive bias, window covariance control, terminal-depth filtering, KL calibration, and two-point reduction—are difficult to recover, despite the formal correctness of the statements.
  - *Fix:* Provide a conventional proof roadmap and concise human-oriented proofs of the main intermediate results. Move declaration-level proof transcriptions and detailed finite-index bookkeeping to a formal supplement, retaining precise links from each manuscript result to its verified declaration.
- **[minor·prose] Main results** — The sentence “Cref{obj:thm:uniform-overlap-frontier} gives a single observable estimator” can suggest one estimator independent of the radius, whereas the displayed estimator uses the supplied value of C through its history depth.
  - *Fix:* Call it a radius-indexed or radius-calibrated estimator family and state immediately that (t_0, ζ, C) are tuning inputs.
- **[minor·structure] A finite insulin-policy adaptation** — The section initially reads like an application of the minimax theory, while the crucial fact that the construction certifies four structural constants and a bias diagnostic—but not the complete model-class predicate or a theorem-level rate application—appears much later. The extensive interval-certificate detail is also disproportionate to the example's interpretive role.
  - *Fix:* State the exact five-part evidentiary scope at the beginning of the section and move most interval-arithmetic machinery to the appendix or formal supplement. Keep the main text focused on the occupancy-bias mechanism.
- **[minor·citation] Related work** — The exact reconstruction of the Hu--Wager hard instance, including the asserted stationary terminal masses and their ratio, is central to the novelty claim but is attributed only broadly to their Theorem 3.1. It is unclear whether those formulas are stated there or derived by the present authors from the construction.
  - *Fix:* Add an exact appendix, page, or equation locator if the formulas appear in Hu--Wager; otherwise label the calculation explicitly as the authors' derivation from that paper's construction and provide enough detail to verify the indexing and reset convention.
- **[minor·prose] Related work** — The sentence “It keeps the single stationary trajectory, known memoryless policies, bounded rewards, finite but cardinality-unrestricted latent state, and no proxy-informativeness or emission-rank assumptions” frames the contribution partly through absent assumptions outside a limitations section, contrary to the affirmative contribution contract.
  - *Fix:* Rewrite affirmatively, for example: “It studies the finite-POMDP experiment class defined by sequential ignorability, bounded rewards, contraction, action overlap, and latent stationary overlap, uniformly over finite cardinalities.”
- **[minor·prose] abstract** — At first use, T and C appear in formulas without plain-language appositives identifying them as the trajectory horizon and stationary-overlap constant. This violates the first-use gloss requirement even though later prose explains them.
  - *Fix:* Introduce “the trajectory horizon T” and “the stationary-overlap constant C” at their first appearances in the abstract.
- **[minor·prose] global** — The notation alternates among θ(K,e), θ(M), and θ_m, and among E_M, E_obs, and expectations under explicitly named observed laws. Although local explanations are sometimes supplied, the changes obscure which law and model representation are in force.
  - *Fix:* Adopt one model-indexed target notation and one observed-law expectation notation throughout theorem statements and surrounding prose; reserve kernel-policy notation for the estimand definition.
- **[minor·structure] Discussion and limitations** — The manuscript explains the frontier repeatedly in prose but provides no compact visual or table showing the unit, local, and fixed-radius regimes, the governing term, and the corresponding PHIW depth. This makes the main contribution harder to absorb than necessary.
  - *Fix:* Add a small regime table or schematic plot summarizing q_C=0, q_C of order at most T^{-1/2}, intermediate shrinking radii, and fixed C>1, together with risk and depth orders.
- **[minor·other] Verification note** — The title footnote says that the appendix records the artifact commit, but the verification note lists the Lean toolchain and mathlib revision without giving the paper artifact commit from the verification contract.
  - *Fix:* Add the artifact commit f2e7e979167a2f3f9242e93c680c7ba1667b6dcc and explain how readers obtain the corresponding source tree and run the checks.
- **[nit·statement] Main results** — The shrinking-frontier theorem labels t_0 and ζ as “Fixed smoothness,” although they are introduced elsewhere as mixing and log-overlap scales.
  - *Fix:* Rename the item “Fixed mixing and overlap scales” for terminological consistency.
- **[nit·prose] Verification note** — The sentence “It belongs to the same verified library and compile under the same toolchain” has a subject–verb agreement error.
  - *Fix:* Change “compile” to “compiles.”

## Questions for authors
- Is the intended primitive model object a full latent trajectory law whose observed law is a pushforward, or an observed law accompanied by an implicit generative extension?
- Are the stationary-mass formulas attributed to the Hu--Wager lower-bound construction explicitly stated in that source, or are they a new calculation by the authors?
- Will the declaration-level proof transcriptions and interval-certificate details be distributed as a separate formal supplement?

