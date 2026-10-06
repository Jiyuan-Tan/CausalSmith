module
public import Causalean.Mathlib.Probability.Birthday.Concentration

/-!
# The least positive birthday threshold at finite parameters

The averaged collision probability eventually falls below every positive
tolerance as the alphabet grows. This gives a least positive threshold and
its monotone characterization.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability.Birthday

/-- For a [trial count](hyp:T), [success probability](hyp:eta), and
[collision tolerance](hyp:delta), the [least positive threshold](goal) is the
[given by the infimum of positive alphabet sizes whose averaged repeat
probability is at most the tolerance](step:1). -/
noncomputable def mStar (T : ℕ) (eta delta : ℝ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ birthdayRepeat T m eta ≤ delta}

/-- For a [valid success probability](hyp:heta) and
[positive tolerance](hyp:hdelta), [some positive alphabet size](goal) has
averaged repeat probability at most the tolerance. -/
theorem threshold_set_nonempty (T : ℕ) (eta delta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hdelta : 0 < delta) :
    ∃ m : ℕ, 0 < m ∧ birthdayRepeat T m eta ≤ delta := by
  -- Use `repeat_le_pairScale_div`; choose a natural m larger than A/delta.
  obtain ⟨n, hn⟩ := exists_nat_gt (pairScale T eta / delta)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have hA : pairScale T eta < (n : ℝ) * delta :=
    (div_lt_iff₀ hdelta).mp hn
  have hpos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hdiv : pairScale T eta / (↑(n + 1) : ℝ) ≤ delta := by
    apply (div_le_iff₀ hpos).mpr
    push_cast
    nlinarith
  exact (repeat_le_pairScale_div T (n + 1) eta (Nat.succ_pos n) heta).trans hdiv

/-- For a [valid success probability](hyp:heta) and
[positive tolerance](hyp:hdelta), the [least threshold is positive](goal). -/
theorem mStar_pos (T : ℕ) (eta delta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hdelta : 0 < delta) :
    0 < mStar T eta delta := by
  -- Apply `Nat.sInf_mem` to `threshold_set_nonempty`.
  obtain ⟨m, hm, hle⟩ := threshold_set_nonempty T eta delta heta hdelta
  have hs : 0 < mStar T eta delta ∧
      birthdayRepeat T (mStar T eta delta) eta ≤ delta := by
    simpa only [mStar, Set.mem_ofPred_eq] using
      (Nat.sInf_mem (s := {m : ℕ | 0 < m ∧ birthdayRepeat T m eta ≤ delta})
        ⟨m, hm, hle⟩)
  exact hs.1

/-- For a [valid success probability](hyp:heta),
[positive tolerance](hyp:hdelta), and [positive alphabet](hyp:hm), the
[tolerance is met exactly above the least threshold](goal). -/
theorem repeat_le_iff_mStar_le (T m : ℕ) (eta delta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hdelta : 0 < delta) (hm : 0 < m) :
    birthdayRepeat T m eta ≤ delta ↔ mStar T eta delta ≤ m := by
  -- Forward: `Nat.sInf_le`; reverse: `Nat.sInf_mem` and `repeat_antitone`.
  constructor
  · intro hle
    exact Nat.sInf_le (s := {n : ℕ | 0 < n ∧ birthdayRepeat T n eta ≤ delta})
      ⟨hm, hle⟩
  · intro hle
    obtain ⟨n, hn, hbound⟩ := threshold_set_nonempty T eta delta heta hdelta
    have hs : 0 < mStar T eta delta ∧
        birthdayRepeat T (mStar T eta delta) eta ≤ delta := by
      simpa only [mStar, Set.mem_ofPred_eq] using
        (Nat.sInf_mem (s := {k : ℕ | 0 < k ∧ birthdayRepeat T k eta ≤ delta})
          ⟨n, hn, hbound⟩)
    exact (repeat_antitone T eta hs.1 hle heta).trans hs.2

end Causalean.Mathlib.Probability.Birthday
