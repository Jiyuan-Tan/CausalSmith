# Presentation adjudication — 2026-09-08

## P1 post-resolver checkpoint

The repaired declaration resolver completed the pending P1 delta pass and audited all 125 formal environments. The newly promoted diagonalization condition-number lemma resolves to its Lean declaration, is rendered faithfully, and sits in the proof-ledger appendix before the theorem proofs that consume it.

The notation-home advisory for \(h(n,g)\) was repaired: the Lean-backed `synth_31` environment defines `calibratedDisplacement(a,n,g)`, now precedes the first lower-bound use, and owns the notation-table row. The five remaining `notation-mutual-definition` advisories are accepted as conservative dependency cycles over ambient or locally bound symbols: model positivity/model-class packaging, generic atomic support points in Wasserstein notation, the paired finite-dimensional matrix-action conversions, the parameterized path-law family, and KL notation with its ambient law arguments. Each semantic object has a reader-facing definition; no undefined scientific term is introduced by these cycles.

The 61 `xref-missing` advisories are graph `statement-uses` edges. The corresponding statements already spell out their mathematical hypotheses or conclusions; citations to promoted derivation lemmas belong in the proof bodies and remain enforced by the P2 proof audit and P4 isolated-lemma gate. They do not justify adding proof-engineering cross-references to the frozen theorem statements.

Bank edits: this adjudication receipt only. Presentation edits: `outline.md` re-homed and moved `synth_31`. No Lean source, accepted research statement, pipeline source, or prompt changed.

## P2 source-grounded proof adjudication - gap-free modulus

The final candidate for thm:gap-free-positive-measure-modulus was reviewed independently by the Sol-medium presentation controller and by the root controller against the actual sources. Both reviews found it mathematically sound and faithful.

Step 5 maps representative independence and control to TGapFreePositiveMeasureModulus.lean:78-105. Step 6 derives the elementary reverse comparison between the ambient max-product Euclidean metric and d_S from Basic.lean:359-363 and Helpers/SummaryMetric.lean:19-30,93-136. It then uses the dense-set extension construction from Helpers/GapFreeModulusBridge.lean:95-132 and uses sequences only to transfer d_S control, as Helpers/GapFreeClosureAssembly.lean:58-100 and TGapFreePositiveMeasureModulus.lean:106-125 do. Step 7 follows TGapFreePositiveMeasureModulus.lean:126-148. Both internal equation references use numbered environments and \cref.

The terminal model verdict was adjudicated because the audit gate requires the prose to justify its closure implication but rejected the valid elementary norm comparison solely because Lean packages that connection behind its ambient topology and extension helpers. No mathematical gap, new claim, mapping change, or promotion is involved.

Production runProofAudit computed current key 87210f3dacf5b5ca16fffdeab7d79f67b5acb00fbac284800194afd0e0276600 for proof SHA-256 2a3fb5656029c4a73fef17c959ef21f1419c2a61831df613d538336e00bb3873, formal-layer TeX SHA-256 6640613a39a756150331dcf314d545061dcaf4da707277b21be4c87fed32d77f, and outline SHA-256 1461ca07164c79e4013116958db3a60d6cc79c360fb478805a666e05d23279f3. The operator supplied the reviewed faithful verdict locally; no configured model was called. Immediate unchanged replay made zero dispatches. All 40 other proof-cache entries were preserved.

Evidence: /tmp/proxy-gap-target-adjudication.json, /tmp/proxy-gap-target-adjudication.diff, and /tmp/proxy-gap-operator-adjudication-run.json.

## P4 source-grounded bibliography adjudication

A read-only production-verifier scan of all 48 cited entries found 33 exact registry matches, 10 transiently unreachable entries, and five registry/provider gaps. The root controller independently checked the version-of-record sources: Royal Society DOI 10.1098/rsta.1894.0003 for Pearson1894; JSTOR IMS volume i395791 for Lindsay1995; Wiley DOI 10.3982/ECTA6763 for KasaharaShimotsu2009; Wiley DOI 10.1002/1099-128X(200005/06)14:3<229::AID-CEM587>3.0.CO;2-N for SidiropoulosBro2000; and Elsevier's first-edition Matrix Perturbation Theory page for StewartSun1990. The Sol-medium presentation controller independently checked the exact current parsed entries and production verifyEntry behavior.

Pearson1894 alone required a metadata edit: both bibliography artifacts now use the version-of-record title “III. Contributions to the Mathematical Theory of Evolution.” Exact before-copies and the one-line diffs are preserved in the presentation orchestrator logs. The other four entries already matched their primary records; their default lookup failures arose from missing authors, malformed registry typography, or irrelevant title-query fallbacks.

The P4 continuation uses a run-specific PaperDeps.lookup fixture only for these five exact, hash-bound entries. Any whole-bibliography or parsed-entry change stops before pipeline entry. All other citations use defaultLookup, and stageP4 still applies its ordinary verifyEntry and authoritative canonicalization gates. The harness retains the production worker configuration, auth resolution, model wrappers, agent-call log, token ledger, and single-writer heartbeat. No citation verdict is bypassed or pre-written.

Evidence: presentation logs/orchestrator/proxy-all-cited-verification.json; proxy-cited-primary-records-20260908.json; proxy-Pearson1894-title-repair.json; and proxy-source-verified-p4-through-p5.mts.

## P4 mechanical compile and JMLR metadata recovery

The first source-verified P4 attempt made zero model calls and halted at compilation. All ten concrete TeX errors came from the undefined control sequence \mesh in the proof of thm:polynomial-net-law-estimator. The authored proof now uses the ordinary local symbol \delta_n in the same definition and ten occurrences; no equation, bound, claim, or Lean mapping changed. The root controller approved that exact replacement, and the Sol-medium controller verified both an isolated compile and the live post-reassembly compile. Production runProofAudit computed the new content key through a single local operator-faithful review, followed by an unchanged zero-dispatch replay; all 40 sibling entries remained byte-equivalent. No configured model was called.

During that failed P4 attempt, the normal arXiv canonicalizer replaced the Anandkumar2014 journal year with the 2012 preprint year, creating a hybrid entry. The official JMLR record identifies volume 15(80), pages 2773–2832, as 2014. The journal entry was restored exactly from references_raw.bib and added as a sixth exact, hash-bound primary record; ordinary P4 verifyEntry remains active. Shared citations.ts was not edited by this recovery.

Evidence: presentation logs/orchestrator/thm-polynomial-net.before-mesh-symbol-fix.tex; thm-polynomial-net-mesh-symbol-fix.diff; proxy-polynomial-net-mesh-operator-adjudication.json; proxy-post-mesh-live-latexmk.log; references.after-failed-P4-Anand2012.bib; proxy-Anandkumar2014-jmlr-repair.json; and proxy-cited-primary-records-20260908.json.



### P3 local validation disclosure 2026-09-08

The guarded reassembly attempted two P3 citation-support dispatches, and zero-model runners stopped both before any external model call. Token-ledger rows 249–250 record zero-duration failures with no usage. These checks were unavailable, not newly passed citation reviews. All 41 proof audits reused. Existing citation judgments remain applicable because the exact compiler repair is solely an alpha-renaming of a locally defined proof symbol and changes no mathematical claim or citation.
