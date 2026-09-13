# Presentation adjudications — exp_dense_group_partition_projection_phase / v1 (2026-09-10)

## Bank edits

1. **`graph.json` → `def:johnson-decomposition` → `lean.supporting_decls`** (backup: `graph.json.bak`).
   P1 halted `lean-coverage`: the frozen body's centered-decomposition + cross-degree-orthogonality
   clause is certified by `JohnsonOrthogonalDecomposition` / `canonicalJohnsonOrthogonalDecomposition`
   (`Helpers/Kneser.lean:339,361`), which the node's `decl_name` + `statement-uses` edges did not
   enumerate. Added both fully-qualified names to `lean.supporting_decls`, per the skill's named
   remedy. Authored body unchanged. P1 then converged and judged the env faithful.

## Bundle edits (authored sources)

2. **`references_raw.bib`** (backup: `references_raw.bib.bak`). P0 dropped 8 correct entries.
   Repairs, each re-swept with `verifyEntry(entry, defaultLookup)` before re-running P0:
   - `Neyman1923` — author corrected to the article's actual authorship
     (Splawa-Neyman / Dabrowska / Speed, Statist. Sci. 5(4), 1990) and the title to the registry's
     punctuation. Now `exact`.
   - `Sobel2006` — title restored to the printed JASA form with the colon before the subtitle.
     Now `minor` (id-confirmed; Crossref stores only the pre-colon short title).
   - `Filmus2016` — added the journal DOI `10.37236/4567` (the arXiv record drops the leading
     "An"). Now `exact`.
   - `Fisher1935`, `Cochran1977`, `Hajek1960` — genuinely unindexed under their own identity;
     confirmed by hand and kept with `verifiedby`:
     Open Library (Fisher, *The Design of Experiments*, Oliver and Boyd, Edinburgh, 1935),
     Open Library (Cochran, *Sampling Techniques*, 3rd ed., Wiley, 1977),
     zbMATH Zbl 0102.15001 (Hájek, Publ. Math. Inst. Hung. Acad. Sci. Ser. A 5, 361–374, 1960).
   - `Savje2021` and `GodsilMeagher2016` — NOT restored. Both are correct AND registry-indexed
     (Crossref `10.1214/20-AOS1973`, `10.1017/cbo9781316414958`); the matcher fails only because
     `norm()` deletes non-ASCII letters, so the record's "Sävje" → "svje" and "Erdős" → "erds"
     cannot meet the entry's LaTeX-escaped "savje" / "erdhos". Reported as a lookup defect; the
     citations are dropped rather than laundered through `verifiedby`.

3. **`related_work_brief.md`** (backup: `.bak`) — removed the two clauses citing the two
   unrestorable keys, so the outline planner is not offered keys outside the pool.

## Accepted with reason (not fixed)

4. P1 note: "3 synthesized definitions have no visible user … synth_4, synth_5, synth_9".
   - `synth_4` (\|\cdot\|_n) and `synth_5` (h_{z,n}^\circ) are FALSE orphans: both are used, at
     `formal_layer.tex` 156/292/708 and 147/312/703, but with substituted arguments
     (`\|\Pi_{n,1}(\cdot)\|_n`, `h_{a,n}^\circ`), which the literal symbol matcher cannot see.
     Consequence: both land after `def:kneser-covariance` / `def:dense-correction` instead of
     before them — a one-section forward reference. Accepted for now; re-open at P1 if P3's
     rubric or the P5 referee flags notation-used-before-definition.
   - `synth_9` (G_{z,n}) is a genuine orphan (used only inside its own body) but is a harmless
     three-line notational remark that also pins G_{1n}/G_{0n}. Kept.
5. `V_{z,n}` (uniform-slice arm variance) carries no anchored definition in the frozen layer.
   Flagged to check in the P2 draft prose.

## Ballast gate (P2)

6. `ballast_review.json` acknowledges all 7 unconsumed frozen statements. Four are terminal
   contributions (`thm:sparse-beyond-birthday`, `thm:qv-diagonal-impossibility`,
   `prop:clubsandwich-consumer`, `prop:eight-unit-witness`); `def:eight-unit-witness` is the object
   the benchmark evaluates; the two classical spectral lemmas are the hypothesis packages that
   `thm:exact-kneser-identity` spells out inline (hence no statement-graph edge) and that the
   appendix proofs cite. Nothing was excised.

## Promotion round (P2, round 1)

7. `lem:johnson-kneser-adjacency-eigenvalue` was added by the promotion agent and REVIEWED AND
   APPROVED: it maps to the real, sorry-free Causalean library theorem
   `Causalean.Mathlib.Combinatorics.JohnsonKneser.kneserAdjacency_eigen`
   (`Causalean/Mathlib/Combinatorics/JohnsonKneser/Kneser.lean:280`), supplies the citable step the
   proof of `lem:classical-kneser-spectrum` was missing, and is cited by that proof.

## P3 hard gate

8. The overclaim loop gave up after 2 rounds without writing its last patch to disk. I applied the
   reviewer's own replacement by hand in `sections/07_discussion_scope_and_extensions.tex`
   (partition variance "governed by the first Johnson harmonic" → "the scaled variance expansion
   contains the degree-one Johnson correction alongside the independent-group leading scale"), and
   P3 then passed. Rounds 0 and 1 of that loop HAD been honoured on disk.

## P5 referee passes (3 total) and what remains

Score trajectory 6.5 → 6.8 → 6.8 (`major_revision` throughout). Two hand rounds were spent; the
skill's three-pass budget is exhausted. Fixed by hand: the full-partition misdescription (the design
is a disjoint packing, `MG_n ≤ n`); prose definitions for `N_n`, `σ_n²`, `h°_{z,n}`, `V_{z,n}` at
first use; a reading note explaining that the projection/spectrum clauses in the asymptotic theorems
are automatic for the canonical projections; the stale verification-note trust boundary, twice; the
title, narrowed to the equal-group CR2 statistic actually delivered; `\cref` section pointers and
section labels; abstract glosses and the lower bound's parameter conditions; the `a_8` coordinates;
the Boolean-to-±1 schedule map behind the Rademacher priors; a deeper Fu–Samii–Wang / Su–Ding /
Pustejovsky–Tipton comparison; affirmative reframing of two contrastive passages.

Unresolved at the budget's end (recorded, not fixed):

- **Adjudication items — frozen Lean-backed statements, the user's call.**
  (a) `prop:rademacher-mixture-separation` writes `E_{H_n}E_{Z_n}{φ(O_n)}` although `O_n` also
  carries the group tuple `A_n`; the referee reads the display as leaving it unclear whether the
  partition randomness is integrated out. (b) `thm:qv-diagonal-impossibility` takes a supremum over
  `Y ∈ C_dense` while the construction starts from a fixed design skeleton. (c) The centered-
  decomposition clause of `thm:exact-kneser-identity` writes `f(A) − E_n f(A)`, readable as applying
  the slice mean to a scalar. (d) `synth_1`'s schedule domain uses `{0,…,n_r−1}` while the slice
  definitions use `{1,…,n}`. Each is a rendering/packaging question about a Lean-backed body; none
  is a mathematical defect of the verified statement.
- **Structural, owned by P1's deterministic ordering.** `synth_4` (‖·‖_n) and `synth_5` (h°) are
  placed after their first users because `insertSynths` matches symbol spellings literally and the
  uses substitute arguments; prose glosses now cover the gap. `synth_9` (G_{z,n}) is genuinely
  unused. Section 5 displays `def:eight-unit-witness` before `prop:clubsandwich-consumer`.
- **Prose nits not reached.** Proof steps are named in prose ("Using Step 6") rather than by
  cleveref; "balanced" is used for fixed-count complete assignment; citation locators are attached
  as prose rather than to the `\citet` command.
- **User scope.** The referee asks for an executable replication artifact pinning the
  `clubSandwich`/`sandwich` versions behind `prop:clubsandwich-consumer`. That is new work.

## Bibliography lookup defect (reported, not worked around)

`Savje2021` and `GodsilMeagher2016` are correct and registry-indexed but cannot pass
`verifyEntry`: `norm()` in `src/presentation/citations.ts:231` strips non-ASCII letters, so the
Crossref records' "Sävje" → "svje" and "Erdős" → "erds" can never match the entries' LaTeX-escaped
"savje" / "erdhos". Two adjacent gaps surfaced with them: `titleCore` splits a subtitle only on
`:`/`–`/`—`, so the JASA title "…Demonstrate? Causal Inference…" failed, and a leading article ("An
Orthogonal Basis…" vs the arXiv "Orthogonal basis…") also defeats `titleRelated`. Both of those were
repairable inside the entries; the accent folding is not.
