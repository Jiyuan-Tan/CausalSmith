module
public import Causalean.Stat.RecurrentEvent.CountingProcess.Basic

/-!
Elementary history invariance for the observed event processes. These
lemmas isolate the pathwise nonanticipation step used when a latent event
time is integrated out of the iid sample law.
-/

public section

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- If [a process is left predictable](hyp:hH) and, at time s, [one subject's current censor
time](hyp:hOld) and [a replacement censor time](hyp:hNew) are both at or after s, then [the
process at s is unchanged when that subject's censor time is replaced](goal), with the subject's
failure time and every other subject's record held fixed. -/
theorem leftPredictable_censor_tail_invariant {n : ℕ}
    (H : ℝ → Sample n → ℝ) (hH : LeftPredictable H)
    (s : ℝ) (x : Sample n) (i : Fin n) (c : ℝ)
    (hOld : s ≤ (x i).2) (hNew : s ≤ c) :
    H s x = H s (Function.update x i ((x i).1, c)) := by
  /- For each t < s, neither censor time can have generated a censor
     event. A failure before t is observed under both censor times. Apply
     `hH` to the resulting equality of earlier event histories. -/
  apply hH s x (Function.update x i ((x i).1, c))
  intro j t ht
  by_cases hji : j = i
  · subst j
    have htOld : t < (x i).2 := lt_of_lt_of_le ht hOld
    have htNew : t < c := lt_of_lt_of_le ht hNew
    have hcOld : ¬ (x i).2 ≤ t := not_le.mpr htOld
    have hcNew : ¬ c ≤ t := not_le.mpr htNew
    constructor
    · simp [censorCount, Function.update_self, hcOld, hcNew]
    · by_cases hf : (x i).1 ≤ t
      · have hfOld : (x i).1 ≤ (x i).2 := le_trans hf (le_of_lt htOld)
        have hfNew : (x i).1 ≤ c := le_trans hf (le_of_lt htNew)
        simp [failureCount, Function.update_self, hf, hfOld, hfNew]
      · simp [failureCount, Function.update_self, hf]
  · have hu := Function.update_of_ne hji ((x i).1, c) x
    simp [censorCount, failureCount, hu]

/-- If [a process is left predictable](hyp:hH) and, at time s, [one subject's current failure
time](hyp:hOld) and [a replacement failure time](hyp:hNew) are both at or after s, then [the
process at s is unchanged when that subject's failure time is replaced](goal), with the subject's
censor time and every other subject's record held fixed. -/
theorem leftPredictable_failure_tail_invariant {n : ℕ}
    (H : ℝ → Sample n → ℝ) (hH : LeftPredictable H)
    (s : ℝ) (x : Sample n) (i : Fin n) (f : ℝ)
    (hOld : s ≤ (x i).1) (hNew : s ≤ f) :
    H s x = H s (Function.update x i (f, (x i).2)) := by
  /- Before s, neither failure time can have generated a failure event.
     A censor event before s is observed under both failure times. -/
  apply hH s x (Function.update x i (f, (x i).2))
  intro j t ht
  by_cases hji : j = i
  · subst j
    have htOld : t < (x i).1 := lt_of_lt_of_le ht hOld
    have htNew : t < f := lt_of_lt_of_le ht hNew
    have hfOld : ¬ (x i).1 ≤ t := not_le.mpr htOld
    have hfNew : ¬ f ≤ t := not_le.mpr htNew
    constructor
    · by_cases hc : (x i).2 ≤ t
      · have hcOld : (x i).2 < (x i).1 := lt_of_le_of_lt hc htOld
        have hcNew : (x i).2 < f := lt_of_le_of_lt hc htNew
        simp [censorCount, Function.update_self, hc, hcOld, hcNew]
      · simp [censorCount, Function.update_self, hc]
    · simp [failureCount, Function.update_self, hfOld, hfNew]
  · have hu := Function.update_of_ne hji (f, (x i).2) x
    simp [censorCount, failureCount, hu]

end Causalean.Stat.RecurrentEvent.CountingProcess
