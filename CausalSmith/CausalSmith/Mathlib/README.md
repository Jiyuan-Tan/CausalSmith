Staging folder for Mathlib-shaped helper lemmas produced during CausalSmith research F3
proof-fill. Each file in this folder must be **pure Mathlib types** — no
references to CausalSmith- or Causalean-cluster symbols (no `Cells`, `tildeX`,
`POManskiIVSystem`, `Backdoor`, etc.). Promotion to `Causalean/Mathlib/` is a
separate human step gated on (a) ≥2 independent call sites or a fully general
statement, and (b) no CausalSmith-specific dependencies; see the `causalsmith`
skill's "Mathlib helper staging" section (`.claude/skills/causalsmith/SKILL.md`).
