## Done
- `CondExp.lean`: proved `condExp_comp_of_map_eq` and `condExpInd_preimage_of_map_eq`.
- `AeEq.lean`: proved `eventuallyEq_of_comp_aeRetraction`.
- `CondIndep.lean`: proved `condIndep_comap_of_map_eq`; scaffolded both iff theorems.
- `Examples.lean`: genuine-equivalence specialization and non-surjective `Unit → Bool` Dirac-support example compile.
- Ground-truth LSP diagnostics and direct `lake env lean` checks confirm zero errors and exactly one `sorry`.

## Remaining
- `CondIndep.lean`: prove `condIndep_of_comap_aeRetraction` (the sole remaining `sorry`).
- Final gate after closure: rebuild live sources, scan for `sorry`/`admit`/`axiom`, and run `#print axioms` for both directional and both iff theorems.

## Blocked
- None.

## Decisions
- Dispatch one filler because the sole obligation and its helpers share one import closure.
- Descend the pulled-back conditional-expectation factorization using `eventuallyEq_of_comp_aeRetraction`; use `condExpInd_preimage_of_map_eq` for all three event indicators.
- Keep both AE inverse hypotheses in the symmetric public API; only `r ∘ s = id` μ'-a.e. is needed by this oriented descent theorem.
- Keep this staging tree dependent only on Mathlib and its own modules; the prior genuine-equivalence implementation was inspected only as proof guidance.
- No external primary paper was named; the requirement states the standard measure-algebra invariance principle, so no source fetch was applicable.