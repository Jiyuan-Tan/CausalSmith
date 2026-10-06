module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialPastScoreIntegral

/-! # Canonical successor history index -/

@[expose] public section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- The successor index is the canonical `Fin n` value with numeral part `k`.
Rewriting by this equality before forming a dependent `History` also aligns its
measurable-space instance; the remaining bound proofs are propositionally
irrelevant. For [the displayed inputs and conditions](hyp:hk), [the stated result](goal) follows. -/
abbrev canonicalNextIndex {n k : ℕ} (hk : k + 1 ≤ n) : Fin n :=
  ⟨k, Nat.lt_of_succ_le hk⟩

/-- Under [the supplied quantities and conditions](hyp:hk), [the next index eq canonical next index assertion](goal) holds. -/
lemma nextIndex_eq_canonicalNextIndex {n k : ℕ} (hk : k + 1 ≤ n) :
    nextIndex hk = canonicalNextIndex hk := by
  apply Fin.ext
  rfl

/-- Under [the stated assumptions](hyp:hk), [the canonical next index has natural-number value equal to the current history length](goal). -/
@[simp] lemma canonicalNextIndex_val {n k : ℕ} (hk : k + 1 ≤ n) :
    (canonicalNextIndex hk).val = k := rfl

end CausalSmith.Stat.LdpAteEfficiencySurface
