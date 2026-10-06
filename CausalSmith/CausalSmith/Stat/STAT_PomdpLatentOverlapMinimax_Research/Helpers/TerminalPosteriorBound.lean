module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepthFilterInvariant

set_option linter.style.longLine false

/-! # One-step identities for the signed-depth terminal posterior -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open scoped BigOperators

/-- Total unnormalized hidden-filter mass after an observed prefix. -/
noncomputable def signedDepthTotalMass (N : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) : ℝ :=
  ∑ h : Fin (2 * (Q + 1)), signedDepthFilterMass N t0 zeta C Q v o h

/-- Summing one raw filter update over all target states removes the normalized transition
kernel and leaves the behavior weight times the predictive reward likelihood. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthTotalMass_succ {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin (k + 1) → Bool × Fin 2) :
    signedDepthTotalMass N t0 zeta C Q v o =
      signedDepthBehaviourWeight zeta (o (Fin.last k)).1 *
        ∑ h : Fin (2 * (Q + 1)),
          signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc) h *
            signedDepthRewardWeight t0 Q v h (o (Fin.last k)).2 := by
  unfold signedDepthTotalMass
  simp_rw [signedDepthFilterMass_succ_raw ht0 hzeta hC]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have hfac :
      (∑ h' : Fin (2 * (Q + 1)),
        signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc) h *
          signedDepthRewardWeight t0 Q v h (o (Fin.last k)).2 *
            signedDepthStateWeight t0 C Q h (o (Fin.last k)).1 h') =
        (signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc) h *
          signedDepthRewardWeight t0 Q v h (o (Fin.last k)).2) *
            ∑ h' : Fin (2 * (Q + 1)),
              signedDepthStateWeight t0 C Q h (o (Fin.last k)).1 h' := by
    rw [Finset.mul_sum]
  rw [← Finset.mul_sum, hfac, sum_signedDepthStateWeight, mul_one]

/-- The predictive reward likelihood is one half times total mass plus the observed reward sign
times the signed terminal-depth mass. [the stated conclusion](goal). -/
lemma sum_filter_mul_signedDepthRewardWeight
    (N : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) (r : Fin 2) :
    (∑ h : Fin (2 * (Q + 1)),
      signedDepthFilterMass N t0 zeta C Q v o h * signedDepthRewardWeight t0 Q v h r) =
      (1 / 2) * (signedDepthTotalMass N t0 zeta C Q v o +
        (if r = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0 *
          ∑ h : Fin (2 * (Q + 1)),
            if latentDepth Q h = Q then
              signedValue (latentSign Q h) * signedDepthFilterMass N t0 zeta C Q v o h
            else 0) := by
  unfold signedDepthTotalMass
  calc
    _ = ∑ h : Fin (2 * (Q + 1)), (
        (1 / 2) * signedDepthFilterMass N t0 zeta C Q v o h +
          (1 / 2) * ((if r = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0 *
            (if latentDepth Q h = Q then
              signedValue (latentSign Q h) * signedDepthFilterMass N t0 zeta C Q v o h
            else 0))) := by
      apply Finset.sum_congr rfl
      intro h _
      by_cases hQ : latentDepth Q h = Q <;>
        by_cases hr : r = 0 <;> simp [signedDepthRewardWeight, hQ, hr] <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib]
      have hhalf :
          (∑ h : Fin (2 * (Q + 1)),
            (1 / 2) * signedDepthFilterMass N t0 zeta C Q v o h) =
            (1 / 2) * ∑ h : Fin (2 * (Q + 1)),
              signedDepthFilterMass N t0 zeta C Q v o h := by
        rw [Finset.mul_sum]
      have hcoeff :
          (∑ h : Fin (2 * (Q + 1)),
            (if r = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0 *
              (if latentDepth Q h = Q then
                signedValue (latentSign Q h) * signedDepthFilterMass N t0 zeta C Q v o h
              else 0)) =
            ((if r = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0) *
              ∑ h : Fin (2 * (Q + 1)),
                if latentDepth Q h = Q then
                  signedValue (latentSign Q h) * signedDepthFilterMass N t0 zeta C Q v o h
                else 0 := by
        rw [Finset.mul_sum]
      have hhalf2 :
          (∑ h : Fin (2 * (Q + 1)),
            (1 / 2) * ((if r = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0 *
              (if latentDepth Q h = Q then
                signedValue (latentSign Q h) * signedDepthFilterMass N t0 zeta C Q v o h
              else 0))) =
            (1 / 2) * ∑ h : Fin (2 * (Q + 1)),
              (if r = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0 *
                (if latentDepth Q h = Q then
                  signedValue (latentSign Q h) * signedDepthFilterMass N t0 zeta C Q v o h
                else 0) := by
        rw [Finset.mul_sum]
      rw [hhalf, hhalf2, hcoeff]
      ring

/-- The exact one-step observed reward likelihood uses the already-proved terminal sign
invariant. This is the denominator factor iterated in manuscript equation (14). [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthTotalMass_succ_invariant {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin (k + 1) → Bool × Fin 2) :
    signedDepthTotalMass N t0 zeta C Q v o =
      signedDepthBehaviourWeight zeta (o (Fin.last k)).1 * (1 / 2) *
        (signedDepthTotalMass N t0 zeta C Q v (fun i ↦ o i.castSucc) +
          (if (o (Fin.last k)).2 = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0 *
            epsC C * signedDepthActionFactor zeta Q (fun i ↦ o i.castSucc) *
              ∑ h : Fin (2 * (Q + 1)),
                if latentDepth Q h = Q then
                  signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc) h else 0) := by
  rw [signedDepthTotalMass_succ ht0 hzeta hC,
    sum_filter_mul_signedDepthRewardWeight]
  rw [signedDepth_terminalMass_invariant ht0 hzeta hC]
  ring

/-- Restrict an observed word to its first `m` coordinates. -/
def observedPrefixTake {k : Nat} (o : Fin k → Bool × Fin 2) (m : Nat) (hm : m ≤ k) :
    Fin m → Bool × Fin 2 :=
  fun i ↦ o ⟨i.val, lt_of_lt_of_le i.isLt hm⟩

/-- Product of behavior-action and fair-reward weights over the last `d` coordinates of an
observed word. The identities below use it only when `d ≤ k`. -/
noncomputable def signedDepthFairWindowWeight (zeta : ℝ) {k : Nat}
    (o : Fin k → Bool × Fin 2) (d : Nat) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin k ↦ k - d ≤ i.val),
    signedDepthBehaviourWeight zeta (o i).1 * (1 / 2)

/-- Restricting to all coordinates returns the original observed word. [the stated conclusion](goal). -/
lemma observedPrefixTake_self {k : Nat} (o : Fin k → Bool × Fin 2) :
    observedPrefixTake o k le_rfl = o := by
  funext i
  rfl

/-- Peeling the last coordinate commutes with restricting to a shorter prefix. [the hm condition](hyp:hm). [the stated conclusion](goal). -/
lemma observedPrefixTake_castSucc {k m : Nat} (hm : m ≤ k)
    (o : Fin (k + 1) → Bool × Fin 2) :
    observedPrefixTake (fun i ↦ o i.castSucc) m hm =
      observedPrefixTake o m (by omega) := by
  funext i
  rfl

/-- The last-`d+1` fair window is the last-`d` window before the final coordinate, followed by
the final behavior/fair-reward factor. [the hd condition](hyp:hd). [the stated conclusion](goal). -/
lemma signedDepthFairWindowWeight_succ (zeta : ℝ) {k d : Nat} (hd : d ≤ k)
    (o : Fin (k + 1) → Bool × Fin 2) :
    signedDepthFairWindowWeight zeta o (d + 1) =
      signedDepthFairWindowWeight zeta (fun i ↦ o i.castSucc) d *
        (signedDepthBehaviourWeight zeta (o (Fin.last k)).1 * (1 / 2)) := by
  unfold signedDepthFairWindowWeight
  simp_rw [Finset.prod_filter]
  rw [Fin.prod_univ_castSucc]
  have hthreshold : (k + 1) - (d + 1) = k - d := by omega
  simp only [hthreshold]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i _
    simp
  · simp

/-- Advancing `d` times through a fixed observed suffix gives the exact unnormalized depth-`d`
mass: `alpha^d`, the behavior/fair-reward window, and the depth-zero mass before the window. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the hsd Q condition](hyp:hsdQ); and [the hdk condition](hyp:hdk). [the stated conclusion](goal). -/
lemma signedDepthUnsignedMass_eq_fairWindow_from {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k d s : Nat} (hsdQ : s + d ≤ Q) (hdk : d ≤ k) (o : Fin k → Bool × Fin 2) :
    signedDepthUnsignedMass N t0 zeta C Q v o ⟨s + d, by omega⟩ =
      mixingAlpha t0 ^ d * signedDepthFairWindowWeight zeta o d *
        signedDepthUnsignedMass N t0 zeta C Q v
          (observedPrefixTake o (k - d) (Nat.sub_le k d)) ⟨s, by omega⟩ := by
  induction d generalizing k with
  | zero =>
      simp [signedDepthFairWindowWeight, Nat.not_le_of_lt, observedPrefixTake_self]
  | succ d ih =>
      cases k with
      | zero => omega
      | succ k =>
          have hdQ' : s + d < Q := by omega
          have hdk' : d ≤ k := by omega
          let opre : Fin k → Bool × Fin 2 := fun i ↦ o i.castSucc
          change signedDepthUnsignedMass N t0 zeta C Q v o ⟨(s + d) + 1, by omega⟩ = _
          rw [signedDepthUnsignedMass_advance ht0 hzeta hC v hdQ']
          rw [ih (Nat.le_of_succ_le hsdQ) hdk' opre]
          rw [signedDepthFairWindowWeight_succ zeta hdk' o]
          have htake :
              observedPrefixTake opre (k - d) (Nat.sub_le k d) =
                observedPrefixTake o (k - d) (by omega) := by
            simpa [opre] using observedPrefixTake_castSucc (Nat.sub_le k d) o
          rw [htake]
          have hlen : k - d = (k + 1) - (d + 1) := by omega
          have hpref :
              observedPrefixTake o (k - d) (by omega) ≍
                observedPrefixTake o ((k + 1) - (d + 1)) (by omega) := by
            apply (Fin.heq_fun_iff hlen).2
            intro i
            rfl
          have hmass :
              signedDepthUnsignedMass N t0 zeta C Q v
                  (observedPrefixTake o (k - d) (by omega)) ⟨s, by omega⟩ =
                signedDepthUnsignedMass N t0 zeta C Q v
                  (observedPrefixTake o ((k + 1) - (d + 1)) (by omega)) ⟨s, by omega⟩ := by
            congr 1
          rw [hmass]
          simp [opre, pow_succ]
          ring

/-- The depth-zero specialization of the general fair-window advance identity. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the hd Q condition](hyp:hdQ); and [the hdk condition](hyp:hdk). [the stated conclusion](goal). -/
lemma signedDepthUnsignedMass_eq_fairWindow {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k d : Nat} (hdQ : d ≤ Q) (hdk : d ≤ k) (o : Fin k → Bool × Fin 2) :
    signedDepthUnsignedMass N t0 zeta C Q v o ⟨d, by omega⟩ =
      mixingAlpha t0 ^ d * signedDepthFairWindowWeight zeta o d *
        signedDepthUnsignedMass N t0 zeta C Q v
          (observedPrefixTake o (k - d) (Nat.sub_le k d)) 0 := by
  simpa using signedDepthUnsignedMass_eq_fairWindow_from
    (s := 0) ht0 hzeta hC v (by omega) hdk o

/-- At an empty observed history, unsigned mass at a decoded depth is its stationary depth
mass. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthUnsignedMass_zero_eq_depthMass {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (o : Fin 0 → Bool × Fin 2) (j : Fin (Q + 1)) :
    signedDepthUnsignedMass N t0 zeta C Q v o j = depthMass t0 Q j.val := by
  unfold signedDepthUnsignedMass
  simp_rw [signedDepthFilterMass_zero ht0 hzeta hC]
  exact sum_signedDepthInitWeight_at_depth t0 zeta C Q j

/-- A prefix whose length is propositionally zero has the stationary unsigned depth mass.
This transport wrapper avoids exposing clients to dependent `Fin 0` casts. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the hk condition](hyp:hk). [the stated conclusion](goal). -/
lemma signedDepthUnsignedMass_eq_depthMass_of_length_eq_zero {N Q : Nat}
    {t0 zeta C : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (hk : k = 0) (o : Fin k → Bool × Fin 2) (j : Fin (Q + 1)) :
    signedDepthUnsignedMass N t0 zeta C Q v o j = depthMass t0 Q j.val := by
  subst k
  exact signedDepthUnsignedMass_zero_eq_depthMass (N := N) ht0 hzeta hC v o j

/-- Multiplying the stationary depth `Q-k` mass by `k` advances gives the terminal stationary
depth mass. [the hk condition](hyp:hk). [the stated conclusion](goal). -/
lemma pow_mul_depthMass_sub (t0 : ℝ) (Q k : Nat) (hk : k ≤ Q) :
    mixingAlpha t0 ^ k * depthMass t0 Q (Q - k) = depthMass t0 Q Q := by
  have hp : mixingAlpha t0 ^ (Q - k) * mixingAlpha t0 ^ k = mixingAlpha t0 ^ Q := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  unfold depthMass
  calc
    mixingAlpha t0 ^ k *
        ((1 - mixingAlpha t0) * mixingAlpha t0 ^ (Q - k) /
          (1 - mixingAlpha t0 ^ (Q + 1))) =
      (1 - mixingAlpha t0) *
          (mixingAlpha t0 ^ (Q - k) * mixingAlpha t0 ^ k) /
            (1 - mixingAlpha t0 ^ (Q + 1)) := by ring
    _ = _ := by rw [hp]

/-- The stationary terminal-depth mass is at most `alpha^Q`, which supplies the numerator bound
in the initial-window case. [the ht0 condition](hyp:ht0). [the stated conclusion](goal). -/
lemma depthMass_terminal_le_pow {t0 : ℝ} (ht0 : 0 < t0) (Q : Nat) :
    depthMass t0 Q Q ≤ mixingAlpha t0 ^ Q := by
  let a := mixingAlpha t0
  have ha0 : 0 ≤ a := (mixingAlpha_pos ht0).le
  have ha1 : a < 1 := mixingAlpha_lt_one ht0
  have hpowQ : 0 ≤ a ^ Q := pow_nonneg ha0 _
  have hpow_le : a ^ Q ≤ 1 := pow_le_one₀ ha0 ha1.le
  have hnext : a ^ (Q + 1) ≤ a := by
    rw [pow_succ]
    simpa [mul_comm] using mul_le_of_le_one_right ha0 hpow_le
  have hden : 0 < 1 - a ^ (Q + 1) := by
    have hp := pow_lt_one₀ ha0 ha1 (by omega : Q + 1 ≠ 0)
    linarith
  unfold depthMass
  change (1 - a) * a ^ Q / (1 - a ^ (Q + 1)) ≤ a ^ Q
  apply (div_le_iff₀ hden).2
  nlinarith [mul_nonneg hpowQ (sub_nonneg.mpr hnext)]

/-- Mature-window terminal numerator: terminal mass is `alpha^Q`, the last-`Q`
behavior/fair-reward product, and the depth-zero mass before that window. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the h Qk condition](hyp:hQk). [the stated conclusion](goal). -/
lemma terminalFilterMass_eq_fairWindow_of_le {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (hQk : Q ≤ k) (o : Fin k → Bool × Fin 2) :
    (∑ h : Fin (2 * (Q + 1)),
      if latentDepth Q h = Q then signedDepthFilterMass N t0 zeta C Q v o h else 0) =
      mixingAlpha t0 ^ Q * signedDepthFairWindowWeight zeta o Q *
        signedDepthUnsignedMass N t0 zeta C Q v
          (observedPrefixTake o (k - Q) (Nat.sub_le k Q)) 0 := by
  rw [sum_terminalFilterMass_eq_unsignedMass]
  rw [show (Fin.last Q : Fin (Q + 1)) = ⟨Q, by omega⟩ by
    apply Fin.ext
    simp]
  exact signedDepthUnsignedMass_eq_fairWindow ht0 hzeta hC v le_rfl hQk o

/-- Stationary initial-window terminal numerator: before `Q` observations, the missing
pre-sample advances are exactly absorbed by the stationary terminal depth mass. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the hk Q condition](hyp:hkQ). [the stated conclusion](goal). -/
lemma terminalFilterMass_eq_fairWindow_of_lt {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (hkQ : k < Q) (o : Fin k → Bool × Fin 2) :
    (∑ h : Fin (2 * (Q + 1)),
      if latentDepth Q h = Q then signedDepthFilterMass N t0 zeta C Q v o h else 0) =
      depthMass t0 Q Q * signedDepthFairWindowWeight zeta o k := by
  rw [sum_terminalFilterMass_eq_unsignedMass]
  have hwalk := signedDepthUnsignedMass_eq_fairWindow_from
    (N := N) (Q := Q) (s := Q - k) ht0 hzeta hC v (by omega) le_rfl o
  rw [show (Fin.last Q : Fin (Q + 1)) = ⟨(Q - k) + k, by omega⟩ by
    apply Fin.ext
    simp [Nat.sub_add_cancel (Nat.le_of_lt hkQ)]]
  rw [hwalk]
  have hzero :
      signedDepthUnsignedMass N t0 zeta C Q v
          (observedPrefixTake o (k - k) (Nat.sub_le k k))
            ⟨Q - k, Nat.lt_succ_of_le (Nat.sub_le Q k)⟩ =
        depthMass t0 Q (Q - k) := by
    exact signedDepthUnsignedMass_eq_depthMass_of_length_eq_zero
      (N := N) ht0 hzeta hC v (Nat.sub_self k) _ _
  rw [hzero]
  have hpow := pow_mul_depthMass_sub t0 Q k (Nat.le_of_lt hkQ)
  calc
    mixingAlpha t0 ^ k * signedDepthFairWindowWeight zeta o k *
        depthMass t0 Q (Q - k) =
      (mixingAlpha t0 ^ k * depthMass t0 Q (Q - k)) *
        signedDepthFairWindowWeight zeta o k := by ring
    _ = _ := by rw [hpow]

/-- Every raw behavior action has strictly positive probability under positive overlap scale. [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
lemma signedDepthBehaviourWeight_pos {zeta : ℝ} (hzeta : 0 < zeta) (a : Bool) :
    0 < signedDepthBehaviourWeight zeta a := by
  have hL : 1 < policyFactor zeta := by
    rw [policyFactor, Real.one_lt_exp_iff]
    exact hzeta
  cases a
  · change 0 < 1 - 1 / policyFactor zeta
    exact sub_pos.mpr ((div_lt_one (by positivity : 0 < policyFactor zeta)).2 hL)
  · change 0 < 1 / policyFactor zeta
    positivity

/-- Every reward symbol has weight at least `(1-c0)/2`, uniformly in depth and sign. [the ht0 condition](hyp:ht0). [the stated conclusion](goal). -/
lemma signedDepthRewardWeight_lower {t0 : ℝ} (ht0 : 0 < t0) (Q : Nat) (v : Bool)
    (h : Fin (2 * (Q + 1))) (r : Fin 2) :
    (1 - c0 t0) / 2 ≤ signedDepthRewardWeight t0 Q v h r := by
  have hc0 : 0 ≤ c0 t0 := by
    unfold c0
    exact div_nonneg (sub_nonneg.mpr (mixingAlpha_lt_one ht0).le) (by norm_num)
  by_cases hQ : latentDepth Q h = Q <;>
    cases v <;> cases hs : latentSign Q h <;>
    fin_cases r <;>
    simp [signedDepthRewardWeight, signedValue, hQ, hs] <;> linarith

/-- Unnormalized hidden-filter masses are nonnegative. [the stated conclusion](goal). -/
lemma signedDepthFilterMass_nonneg (N : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) (h : Fin (2 * (Q + 1))) :
    0 ≤ signedDepthFilterMass N t0 zeta C Q v o h := by
  unfold signedDepthFilterMass finiteTerminalStatePrefixMass
  apply Finset.sum_nonneg
  intro sigma _
  split_ifs
  · unfold finiteFixedPrefixWeight
    apply mul_nonneg (by positivity)
    apply Finset.prod_nonneg
    intro i _
    exact mul_nonneg (by positivity) (by positivity)
  · exact le_rfl

/-- Every observed prefix has strictly positive total raw filter mass. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthTotalMass_pos {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) :
    0 < signedDepthTotalMass N t0 zeta C Q v o := by
  induction k with
  | zero =>
      unfold signedDepthTotalMass
      simp_rw [signedDepthFilterMass_zero ht0 hzeta hC]
      rw [sum_signedDepthInitWeight ht0]
      norm_num
  | succ k ih =>
      rw [signedDepthTotalMass_succ ht0 hzeta hC]
      apply mul_pos (signedDepthBehaviourWeight_pos hzeta _)
      let delta : ℝ := (1 - c0 t0) / 2
      have hc0lt : c0 t0 < 1 := by
        unfold c0
        have ha0 := (mixingAlpha_pos ht0).le
        have ha1 := mixingAlpha_lt_one ht0
        linarith
      have hdelta : 0 < delta := div_pos (sub_pos.mpr hc0lt) (by norm_num)
      have hlower :
          delta * signedDepthTotalMass N t0 zeta C Q v (fun i ↦ o i.castSucc) ≤
            ∑ h : Fin (2 * (Q + 1)),
              signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc) h *
                signedDepthRewardWeight t0 Q v h (o (Fin.last k)).2 := by
        unfold signedDepthTotalMass
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro h _
        change ((1 - c0 t0) / 2) *
            signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc) h ≤ _
        calc
          _ = signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc) h *
              ((1 - c0 t0) / 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (signedDepthRewardWeight_lower ht0 Q v h (o (Fin.last k)).2)
            (signedDepthFilterMass_nonneg N t0 zeta C Q v _ h)
      exact lt_of_lt_of_le (mul_pos hdelta (ih (fun i ↦ o i.castSucc))) hlower

/-- The action-history factor is nonnegative. [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
lemma signedDepthActionFactor_nonneg {zeta : ℝ} (hzeta : 0 < zeta) (Q : Nat)
    {k : Nat} (o : Fin k → Bool × Fin 2) :
    0 ≤ signedDepthActionFactor zeta Q o := by
  unfold signedDepthActionFactor
  apply mul_nonneg (zpow_nonneg (Real.exp_pos zeta).le _)
  apply Finset.prod_nonneg
  intro i _
  split <;> norm_num

/-- The action-history factor never exceeds one. [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
lemma signedDepthActionFactor_le_one {zeta : ℝ} (hzeta : 0 < zeta) (Q : Nat)
    {k : Nat} (o : Fin k → Bool × Fin 2) :
    signedDepthActionFactor zeta Q o ≤ 1 := by
  have hLpos : 0 < policyFactor zeta := by
    exact Real.exp_pos zeta
  have hL : 1 ≤ policyFactor zeta := by
    rw [policyFactor, Real.one_le_exp_iff]
    exact hzeta.le
  have hpow : policyFactor zeta ^ (-(Q - min Q k : ℤ)) ≤ 1 := by
    have hn : ((Q - min Q k : Nat) : ℤ) = (Q : ℤ) - (min Q k : Nat) :=
      Nat.cast_sub (Nat.min_le_left Q k)
    rw [zpow_neg, ← hn, zpow_natCast]
    exact (inv_le_one₀ (pow_pos hLpos _)).2 (one_le_pow₀ hL)
  unfold signedDepthActionFactor
  apply mul_le_one₀ hpow
  · apply Finset.prod_nonneg
    intro i _
    split <;> norm_num
  · apply Finset.prod_le_one
    · intro i _
      split <;> norm_num
    · intro i _
      split <;> norm_num

/-- The occupancy-bias/action-history coefficient has absolute value at most one. [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma abs_epsC_mul_signedDepthActionFactor_le_one {zeta C : ℝ}
    (hzeta : 0 < zeta) (hC : 1 < C) (Q : Nat)
    {k : Nat} (o : Fin k → Bool × Fin 2) :
    |epsC C * signedDepthActionFactor zeta Q o| ≤ 1 := by
  have he0 := epsC_nonneg hC.le
  have he1 : epsC C ≤ 1 := le_trans (epsC_le_half C) (by norm_num)
  have ha0 := signedDepthActionFactor_nonneg hzeta Q o
  have ha1 := signedDepthActionFactor_le_one hzeta Q o
  rw [abs_of_nonneg (mul_nonneg he0 ha0)]
  exact mul_le_one₀ he1 ha0 ha1

/-- The multiplicative reward-likelihood correction at the next observed coordinate. -/
noncomputable def signedDepthRewardCorrection (N : Nat) (t0 zeta C : ℝ) (Q : Nat)
    (v : Bool) {k : Nat} (o : Fin k → Bool × Fin 2) (next : Bool × Fin 2) : ℝ :=
  1 + (if next.2 = 0 then (-1 : ℝ) else 1) * signedValue v * c0 t0 * epsC C *
    signedDepthActionFactor zeta Q o *
      ((∑ h : Fin (2 * (Q + 1)),
          if latentDepth Q h = Q then signedDepthFilterMass N t0 zeta C Q v o h else 0) /
        signedDepthTotalMass N t0 zeta C Q v o)

/-- Terminal-depth mass is bounded by total filter mass. [the stated conclusion](goal). -/
lemma signedDepthTerminalMass_le_totalMass (N : Nat) (t0 zeta C : ℝ) (Q : Nat)
    (v : Bool) {k : Nat} (o : Fin k → Bool × Fin 2) :
    (∑ h : Fin (2 * (Q + 1)),
        if latentDepth Q h = Q then signedDepthFilterMass N t0 zeta C Q v o h else 0) ≤
      signedDepthTotalMass N t0 zeta C Q v o := by
  unfold signedDepthTotalMass
  apply Finset.sum_le_sum
  intro h _
  split_ifs
  · exact le_rfl
  · exact signedDepthFilterMass_nonneg N t0 zeta C Q v o h

/-- Unsigned mass at a fixed decoded depth is bounded by total filter mass. [the stated conclusion](goal). -/
lemma signedDepthUnsignedMass_le_totalMass (N : Nat) (t0 zeta C : ℝ) (Q : Nat)
    (v : Bool) {k : Nat} (o : Fin k → Bool × Fin 2) (j : Fin (Q + 1)) :
    signedDepthUnsignedMass N t0 zeta C Q v o j ≤
      signedDepthTotalMass N t0 zeta C Q v o := by
  unfold signedDepthUnsignedMass signedDepthTotalMass
  rw [← (depthSignEquiv Q).sum_comp, Fintype.sum_prod_type]
  let f : Fin (Q + 1) → ℝ := fun d ↦ ∑ u : Fin 2,
    signedDepthFilterMass N t0 zeta C Q v o (depthSignEquiv Q (d, u))
  have hsingle := Finset.single_le_sum (f := f) (s := Finset.univ)
    (fun d _ ↦ Finset.sum_nonneg fun u _ ↦
      signedDepthFilterMass_nonneg N t0 zeta C Q v o (depthSignEquiv Q (d, u)))
    (Finset.mem_univ j)
  simpa [f] using hsingle

/-- Terminal posterior represented directly by the run-local unnormalized filter. -/
noncomputable def signedDepthRawPosterior (N : Nat) (t0 zeta C : ℝ) (Q : Nat)
    (v : Bool) {k : Nat} (o : Fin k → Bool × Fin 2) : ℝ :=
  (∑ h : Fin (2 * (Q + 1)),
      if latentDepth Q h = Q then signedDepthFilterMass N t0 zeta C Q v o h else 0) /
    signedDepthTotalMass N t0 zeta C Q v o

/-- The raw terminal posterior lies in `[0,1]`. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthRawPosterior_mem_Icc {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) :
    signedDepthRawPosterior N t0 zeta C Q v o ∈ Set.Icc (0 : ℝ) 1 := by
  unfold signedDepthRawPosterior
  constructor
  · exact div_nonneg
      (Finset.sum_nonneg fun h _ ↦ by
        by_cases hh : latentDepth Q h = Q
        · simp [hh, signedDepthFilterMass_nonneg N t0 zeta C Q v o h]
        · simp [hh])
      (signedDepthTotalMass_pos ht0 hzeta hC v o).le
  · exact (div_le_one (signedDepthTotalMass_pos ht0 hzeta hC v o)).2
      (signedDepthTerminalMass_le_totalMass N t0 zeta C Q v o)

/-- Each observed-reward correction is bounded below by `1-c0*q`, where `q` is the
terminal-depth posterior represented by raw filter masses. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthRewardCorrection_lower {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) (next : Bool × Fin 2) :
    1 - c0 t0 *
        ((∑ h : Fin (2 * (Q + 1)),
            if latentDepth Q h = Q then signedDepthFilterMass N t0 zeta C Q v o h else 0) /
          signedDepthTotalMass N t0 zeta C Q v o) ≤
      signedDepthRewardCorrection N t0 zeta C Q v o next := by
  let q := (∑ h : Fin (2 * (Q + 1)),
      if latentDepth Q h = Q then signedDepthFilterMass N t0 zeta C Q v o h else 0) /
        signedDepthTotalMass N t0 zeta C Q v o
  let coeff := (if next.2 = 0 then (-1 : ℝ) else 1) * signedValue v *
    (epsC C * signedDepthActionFactor zeta Q o)
  change 1 - c0 t0 * q ≤ signedDepthRewardCorrection N t0 zeta C Q v o next
  have hq : 0 ≤ q := div_nonneg
    (Finset.sum_nonneg fun h _ ↦ by
      by_cases hh : latentDepth Q h = Q
      · simp [hh, signedDepthFilterMass_nonneg N t0 zeta C Q v o h]
      · simp [hh])
    (signedDepthTotalMass_pos ht0 hzeta hC v o).le
  have habs := abs_epsC_mul_signedDepthActionFactor_le_one hzeta hC Q o
  rw [abs_mul] at habs
  have habsCoeff : |coeff| ≤ 1 := by
    unfold coeff
    cases v <;> by_cases hr : next.2 = 0 <;>
      simp [signedValue, hr] <;> exact habs
  have hc : 0 ≤ c0 t0 := by
    unfold c0
    exact div_nonneg (sub_nonneg.mpr (mixingAlpha_lt_one ht0).le) (by norm_num)
  have hcoeff : 0 ≤ coeff + 1 := by
    linarith [neg_le_of_abs_le habsCoeff]
  have hprod : 0 ≤ c0 t0 * q * (coeff + 1) :=
    mul_nonneg (mul_nonneg hc hq) hcoeff
  unfold signedDepthRewardCorrection
  dsimp [coeff, q] at hprod ⊢
  nlinarith

/-- The exact one-step total-mass update factored into fair likelihood, previous mass, and
the posterior-dependent reward correction. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthTotalMass_succ_factored {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin (k + 1) → Bool × Fin 2) :
    signedDepthTotalMass N t0 zeta C Q v o =
      signedDepthBehaviourWeight zeta (o (Fin.last k)).1 * (1 / 2) *
        signedDepthTotalMass N t0 zeta C Q v (fun i ↦ o i.castSucc) *
          signedDepthRewardCorrection N t0 zeta C Q v
            (fun i ↦ o i.castSucc) (o (Fin.last k)) := by
  rw [signedDepthTotalMass_succ_invariant ht0 hzeta hC]
  unfold signedDepthRewardCorrection
  have hne : signedDepthTotalMass N t0 zeta C Q v (fun i ↦ o i.castSucc) ≠ 0 :=
    ne_of_gt (signedDepthTotalMass_pos ht0 hzeta hC v _)
  field_simp

/-- Product of posterior-dependent likelihood corrections over the last `d` coordinates. -/
noncomputable def signedDepthCorrectionWindow (N : Nat) (t0 zeta C : ℝ) (Q : Nat)
    (v : Bool) {k : Nat} (o : Fin k → Bool × Fin 2) (d : Nat) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin k ↦ k - d ≤ i.val),
    signedDepthRewardCorrection N t0 zeta C Q v
      (observedPrefixTake o i.val (Nat.le_of_lt i.isLt)) (o i)

/-- Product of the equation-(15) lower factors over the last `d` prefixes. -/
noncomputable def signedDepthPosteriorLowerWindow (N : Nat) (t0 zeta C : ℝ) (Q : Nat)
    (v : Bool) {k : Nat} (o : Fin k → Bool × Fin 2) (d : Nat) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin k ↦ k - d ≤ i.val),
    (1 - c0 t0 * signedDepthRawPosterior N t0 zeta C Q v
      (observedPrefixTake o i.val (Nat.le_of_lt i.isLt)))

/-- The equation-(15) lower-factor product is positive and bounded by the exact correction
product. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthPosteriorLowerWindow_pos_le_correction {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k d : Nat} (o : Fin k → Bool × Fin 2) :
    0 < signedDepthPosteriorLowerWindow N t0 zeta C Q v o d ∧
      signedDepthPosteriorLowerWindow N t0 zeta C Q v o d ≤
        signedDepthCorrectionWindow N t0 zeta C Q v o d := by
  have hc0lt : c0 t0 < 1 := by
    unfold c0
    have ha0 := (mixingAlpha_pos ht0).le
    have ha1 := mixingAlpha_lt_one ht0
    linarith
  constructor
  · unfold signedDepthPosteriorLowerWindow
    apply Finset.prod_pos
    intro i hi
    have hq := (signedDepthRawPosterior_mem_Icc (N := N) (Q := Q) ht0 hzeta hC v
      (observedPrefixTake o i.val (Nat.le_of_lt i.isLt))).2
    have hc0 : 0 ≤ c0 t0 := by
      unfold c0
      exact div_nonneg (sub_nonneg.mpr (mixingAlpha_lt_one ht0).le) (by norm_num)
    exact sub_pos.mpr (lt_of_le_of_lt (by
      simpa using mul_le_mul_of_nonneg_left hq hc0) hc0lt)
  · unfold signedDepthPosteriorLowerWindow signedDepthCorrectionWindow
    apply Finset.prod_le_prod
    · intro i hi
      exact (sub_pos.mpr (by
        have hq := (signedDepthRawPosterior_mem_Icc (N := N) (Q := Q) ht0 hzeta hC v
          (observedPrefixTake o i.val (Nat.le_of_lt i.isLt))).2
        have hc0 : 0 ≤ c0 t0 := by
          unfold c0
          exact div_nonneg (sub_nonneg.mpr (mixingAlpha_lt_one ht0).le) (by norm_num)
        exact lt_of_le_of_lt (by
          simpa using mul_le_mul_of_nonneg_left hq hc0) hc0lt)).le
    · intro i hi
      simpa [signedDepthRawPosterior] using
        signedDepthRewardCorrection_lower ht0 hzeta hC v
          (observedPrefixTake o i.val (Nat.le_of_lt i.isLt)) (o i)

/-- Appending a coordinate appends the lower posterior factor. [the hd condition](hyp:hd). [the stated conclusion](goal). -/
lemma signedDepthPosteriorLowerWindow_succ (N : Nat) (t0 zeta C : ℝ) (Q : Nat)
    (v : Bool) {k d : Nat} (hd : d ≤ k) (o : Fin (k + 1) → Bool × Fin 2) :
    signedDepthPosteriorLowerWindow N t0 zeta C Q v o (d + 1) =
      signedDepthPosteriorLowerWindow N t0 zeta C Q v (fun i ↦ o i.castSucc) d *
        (1 - c0 t0 * signedDepthRawPosterior N t0 zeta C Q v
          (fun i ↦ o i.castSucc)) := by
  unfold signedDepthPosteriorLowerWindow
  simp_rw [Finset.prod_filter]
  rw [Fin.prod_univ_castSucc]
  have hthreshold : (k + 1) - (d + 1) = k - d := by omega
  simp only [hthreshold]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i _
    congr 2
  · rw [if_pos (by simp)]
    congr 2

/-- A uniform posterior upper bound `b` over all strict prefixes gives a power lower bound
for a final likelihood-factor window. [the hc0 condition](hyp:hc0); and [the hbase condition](hyp:hbase); and [the hdk condition](hyp:hdk); and [the hq condition](hyp:hq). [the stated conclusion](goal). -/
lemma pow_one_sub_le_signedDepthPosteriorLowerWindow {N Q : Nat} {t0 zeta C b : ℝ}
    (hc0 : 0 ≤ c0 t0) (hbase : 0 ≤ 1 - c0 t0 * b)
    (v : Bool) {k d : Nat} (hdk : d ≤ k)
    (o : Fin k → Bool × Fin 2)
    (hq : ∀ (i : Fin k), signedDepthRawPosterior N t0 zeta C Q v
      (observedPrefixTake o i.val (Nat.le_of_lt i.isLt)) ≤ b) :
    (1 - c0 t0 * b) ^ d ≤ signedDepthPosteriorLowerWindow N t0 zeta C Q v o d := by
  induction d generalizing k with
  | zero => simp [signedDepthPosteriorLowerWindow, Nat.not_le_of_lt]
  | succ d ih =>
      cases k with
      | zero => omega
      | succ k =>
          have hdk' : d ≤ k := by omega
          let opre : Fin k → Bool × Fin 2 := fun i ↦ o i.castSucc
          have hqpre : ∀ (i : Fin k), signedDepthRawPosterior N t0 zeta C Q v
              (observedPrefixTake opre i.val (Nat.le_of_lt i.isLt)) ≤ b := by
            intro i
            rw [show observedPrefixTake opre i.val (Nat.le_of_lt i.isLt) =
                observedPrefixTake o i.val (by omega) by
              simpa [opre] using observedPrefixTake_castSucc (Nat.le_of_lt i.isLt) o]
            exact hq i.castSucc
          have hind := ih hdk' opre hqpre
          rw [signedDepthPosteriorLowerWindow_succ N t0 zeta C Q v hdk' o, pow_succ]
          apply mul_le_mul
          · exact hind
          · exact sub_le_sub_left (mul_le_mul_of_nonneg_left
              (hq (Fin.last k)) hc0) 1
          · exact hbase
          · exact le_trans (pow_nonneg hbase d) hind

/-- Appending one coordinate appends its likelihood correction to the correction window. [the hd condition](hyp:hd). [the stated conclusion](goal). -/
lemma signedDepthCorrectionWindow_succ (N : Nat) (t0 zeta C : ℝ) (Q : Nat)
    (v : Bool) {k d : Nat} (hd : d ≤ k) (o : Fin (k + 1) → Bool × Fin 2) :
    signedDepthCorrectionWindow N t0 zeta C Q v o (d + 1) =
      signedDepthCorrectionWindow N t0 zeta C Q v (fun i ↦ o i.castSucc) d *
        signedDepthRewardCorrection N t0 zeta C Q v
          (fun i ↦ o i.castSucc) (o (Fin.last k)) := by
  unfold signedDepthCorrectionWindow
  simp_rw [Finset.prod_filter]
  rw [Fin.prod_univ_castSucc]
  have hthreshold : (k + 1) - (d + 1) = k - d := by omega
  simp only [hthreshold]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i _
    congr 2
  · rw [if_pos (by simp)]
    congr 2

/-- Exact iteration of the one-step likelihood update over an arbitrary final window. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the hdk condition](hyp:hdk). [the stated conclusion](goal). -/
lemma signedDepthTotalMass_eq_windows {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k d : Nat} (hdk : d ≤ k) (o : Fin k → Bool × Fin 2) :
    signedDepthTotalMass N t0 zeta C Q v o =
      signedDepthFairWindowWeight zeta o d *
        signedDepthTotalMass N t0 zeta C Q v
          (observedPrefixTake o (k - d) (Nat.sub_le k d)) *
        signedDepthCorrectionWindow N t0 zeta C Q v o d := by
  induction d generalizing k with
  | zero =>
      simp [signedDepthFairWindowWeight, signedDepthCorrectionWindow,
        Nat.not_le_of_lt, observedPrefixTake_self]
  | succ d ih =>
      cases k with
      | zero => omega
      | succ k =>
          have hdk' : d ≤ k := by omega
          let opre : Fin k → Bool × Fin 2 := fun i ↦ o i.castSucc
          rw [signedDepthTotalMass_succ_factored ht0 hzeta hC]
          rw [ih hdk' opre]
          rw [signedDepthFairWindowWeight_succ zeta hdk' o]
          rw [signedDepthCorrectionWindow_succ N t0 zeta C Q v hdk' o]
          have htake :
              observedPrefixTake opre (k - d) (Nat.sub_le k d) =
                observedPrefixTake o (k - d) (by omega) := by
            simpa [opre] using observedPrefixTake_castSucc (Nat.sub_le k d) o
          rw [htake]
          have hlen : k - d = (k + 1) - (d + 1) := by omega
          have hpref :
              observedPrefixTake o (k - d) (by omega) ≍
                observedPrefixTake o ((k + 1) - (d + 1)) (by omega) := by
            apply (Fin.heq_fun_iff hlen).2
            intro i
            rfl
          have hmass :
              signedDepthTotalMass N t0 zeta C Q v
                  (observedPrefixTake o (k - d) (by omega)) =
                signedDepthTotalMass N t0 zeta C Q v
                  (observedPrefixTake o ((k + 1) - (d + 1)) (by omega)) := by
            congr 1
          rw [hmass]
          simp [opre]
          ring

/-- A fair observed-window likelihood is strictly positive. [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
lemma signedDepthFairWindowWeight_pos {zeta : ℝ} (hzeta : 0 < zeta)
    {k d : Nat} (o : Fin k → Bool × Fin 2) :
    0 < signedDepthFairWindowWeight zeta o d := by
  unfold signedDepthFairWindowWeight
  apply Finset.prod_pos
  intro i hi
  exact mul_pos (signedDepthBehaviourWeight_pos hzeta _) (by norm_num)

/-- Equation (15), mature-window form: the terminal posterior is bounded by `alpha^Q`
divided by the product of the last `Q` lower likelihood factors. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the h Qk condition](hyp:hQk). [the stated conclusion](goal). -/
lemma signedDepthRawPosterior_le_product_of_le {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (hQk : Q ≤ k) (o : Fin k → Bool × Fin 2) :
    signedDepthRawPosterior N t0 zeta C Q v o ≤
      mixingAlpha t0 ^ Q /
        signedDepthPosteriorLowerWindow N t0 zeta C Q v o Q := by
  let pre := observedPrefixTake o (k - Q) (Nat.sub_le k Q)
  let F := signedDepthFairWindowWeight zeta o Q
  let B := signedDepthTotalMass N t0 zeta C Q v pre
  let U := signedDepthUnsignedMass N t0 zeta C Q v pre 0
  let R := signedDepthCorrectionWindow N t0 zeta C Q v o Q
  let P := signedDepthPosteriorLowerWindow N t0 zeta C Q v o Q
  have hnum := terminalFilterMass_eq_fairWindow_of_le
    (N := N) ht0 hzeta hC v hQk o
  have hden := signedDepthTotalMass_eq_windows (N := N) (Q := Q)
    ht0 hzeta hC v hQk o
  have hUB : U ≤ B := signedDepthUnsignedMass_le_totalMass N t0 zeta C Q v pre 0
  have hPpos : 0 < P :=
    (signedDepthPosteriorLowerWindow_pos_le_correction ht0 hzeta hC v o).1
  have hPR : P ≤ R :=
    (signedDepthPosteriorLowerWindow_pos_le_correction ht0 hzeta hC v o).2
  have hFpos : 0 < F := signedDepthFairWindowWeight_pos hzeta o
  have hBpos : 0 < B := signedDepthTotalMass_pos ht0 hzeta hC v pre
  have hRpos : 0 < R := lt_of_lt_of_le hPpos hPR
  have hU0 : 0 ≤ U := by
    unfold U signedDepthUnsignedMass
    exact Finset.sum_nonneg fun u _ ↦
      signedDepthFilterMass_nonneg N t0 zeta C Q v pre (depthSignEquiv Q (0, u))
  have hprod : U * P ≤ B * R :=
    mul_le_mul hUB hPR hPpos.le hBpos.le
  unfold signedDepthRawPosterior
  apply (div_le_div_iff₀ (signedDepthTotalMass_pos ht0 hzeta hC v o) hPpos).2
  dsimp [pre, F, B, U, R, P] at hnum hden hprod ⊢
  rw [hnum, hden]
  have ha : 0 ≤ mixingAlpha t0 ^ Q := pow_nonneg (mixingAlpha_pos ht0).le _
  have hscale := mul_le_mul_of_nonneg_left hprod (mul_nonneg ha hFpos.le)
  nlinarith

/-- The total raw filter mass of an empty prefix is one. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthTotalMass_zero {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (o : Fin 0 → Bool × Fin 2) :
    signedDepthTotalMass N t0 zeta C Q v o = 1 := by
  unfold signedDepthTotalMass
  simp_rw [signedDepthFilterMass_zero ht0 hzeta hC]
  exact sum_signedDepthInitWeight ht0 Q

/-- Propositionally empty prefixes also have total mass one. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the hk condition](hyp:hk). [the stated conclusion](goal). -/
lemma signedDepthTotalMass_of_length_eq_zero {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (hk : k = 0) (o : Fin k → Bool × Fin 2) :
    signedDepthTotalMass N t0 zeta C Q v o = 1 := by
  subst k
  exact signedDepthTotalMass_zero ht0 hzeta hC v o

/-- Equation (15), stationary initial-window form. The product contains all `k<Q`
available observed prefixes. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the hk Q condition](hyp:hkQ). [the stated conclusion](goal). -/
lemma signedDepthRawPosterior_le_product_of_lt {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (hkQ : k < Q) (o : Fin k → Bool × Fin 2) :
    signedDepthRawPosterior N t0 zeta C Q v o ≤
      mixingAlpha t0 ^ Q /
        signedDepthPosteriorLowerWindow N t0 zeta C Q v o k := by
  let pre := observedPrefixTake o (k - k) (Nat.sub_le k k)
  let F := signedDepthFairWindowWeight zeta o k
  let B := signedDepthTotalMass N t0 zeta C Q v pre
  let R := signedDepthCorrectionWindow N t0 zeta C Q v o k
  let P := signedDepthPosteriorLowerWindow N t0 zeta C Q v o k
  have hnum := terminalFilterMass_eq_fairWindow_of_lt
    (N := N) ht0 hzeta hC v hkQ o
  have hden := signedDepthTotalMass_eq_windows (N := N) (Q := Q)
    ht0 hzeta hC v le_rfl o
  have hB : B = 1 := signedDepthTotalMass_of_length_eq_zero
    ht0 hzeta hC v (Nat.sub_self k) pre
  have hPpos : 0 < P :=
    (signedDepthPosteriorLowerWindow_pos_le_correction ht0 hzeta hC v o).1
  have hPR : P ≤ R :=
    (signedDepthPosteriorLowerWindow_pos_le_correction ht0 hzeta hC v o).2
  have hFpos : 0 < F := signedDepthFairWindowWeight_pos hzeta o
  have hdepth := depthMass_terminal_le_pow ht0 Q
  have ha : 0 ≤ mixingAlpha t0 ^ Q := pow_nonneg (mixingAlpha_pos ht0).le _
  have hprod : depthMass t0 Q Q * P ≤ mixingAlpha t0 ^ Q * R :=
    mul_le_mul hdepth hPR hPpos.le ha
  unfold signedDepthRawPosterior
  apply (div_le_div_iff₀ (signedDepthTotalMass_pos ht0 hzeta hC v o) hPpos).2
  dsimp [pre, F, B, R, P] at hnum hden hB hprod ⊢
  rw [hnum, hden, hB]
  have hscale := mul_le_mul_of_nonneg_left hprod hFpos.le
  nlinarith

/-- The first bootstrap bound from equation (15). [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthRawPosterior_le_ratio_pow {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) :
    signedDepthRawPosterior N t0 zeta C Q v o ≤
      (mixingAlpha t0 / (1 - c0 t0)) ^ Q := by
  have hc0 : 0 ≤ c0 t0 := by
    unfold c0
    exact div_nonneg (sub_nonneg.mpr (mixingAlpha_lt_one ht0).le) (by norm_num)
  have hc0lt : c0 t0 < 1 := by
    unfold c0
    have ha0 := (mixingAlpha_pos ht0).le
    have ha1 := mixingAlpha_lt_one ht0
    linarith
  have hbase : 0 < 1 - c0 t0 := sub_pos.mpr hc0lt
  have hbaseOne : 0 ≤ 1 - c0 t0 * (1 : ℝ) := by simpa using hbase.le
  by_cases hQk : Q ≤ k
  · have hEq15 := signedDepthRawPosterior_le_product_of_le
      (N := N) ht0 hzeta hC v hQk o
    have hpow := pow_one_sub_le_signedDepthPosteriorLowerWindow
      (N := N) (Q := Q) hc0 hbaseOne v hQk o
      (fun i ↦ (signedDepthRawPosterior_mem_Icc
        (N := N) (Q := Q) ht0 hzeta hC v _).2)
    calc
      _ ≤ mixingAlpha t0 ^ Q /
          signedDepthPosteriorLowerWindow N t0 zeta C Q v o Q := hEq15
      _ ≤ mixingAlpha t0 ^ Q / (1 - c0 t0) ^ Q :=
        div_le_div_of_nonneg_left (pow_nonneg (mixingAlpha_pos ht0).le _)
          (pow_pos hbase _) (by simpa using hpow)
      _ = _ := by rw [div_pow]
  · have hkQ : k < Q := by omega
    have hEq15 := signedDepthRawPosterior_le_product_of_lt
      (N := N) ht0 hzeta hC v hkQ o
    have hpow := pow_one_sub_le_signedDepthPosteriorLowerWindow
      (N := N) (Q := Q) hc0 hbaseOne v le_rfl o
      (fun i ↦ (signedDepthRawPosterior_mem_Icc
        (N := N) (Q := Q) ht0 hzeta hC v _).2)
    have hpowers : (1 - c0 t0) ^ Q ≤ (1 - c0 t0) ^ k :=
      pow_le_pow_of_le_one hbase.le (sub_le_self 1 hc0) (Nat.le_of_lt hkQ)
    calc
      _ ≤ mixingAlpha t0 ^ Q /
          signedDepthPosteriorLowerWindow N t0 zeta C Q v o k := hEq15
      _ ≤ mixingAlpha t0 ^ Q / (1 - c0 t0) ^ k :=
        div_le_div_of_nonneg_left (pow_nonneg (mixingAlpha_pos ht0).le _)
          (pow_pos hbase _) (by simpa using hpow)
      _ ≤ mixingAlpha t0 ^ Q / (1 - c0 t0) ^ Q :=
        div_le_div_of_nonneg_left (pow_nonneg (mixingAlpha_pos ht0).le _)
          (pow_pos hbase _) hpowers
      _ = _ := by rw [div_pow]

/-- Substituting the crude bound back into equation (15). [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthRawPosterior_le_refined {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) :
    signedDepthRawPosterior N t0 zeta C Q v o ≤
      mixingAlpha t0 ^ Q /
        (1 - c0 t0 * (mixingAlpha t0 / (1 - c0 t0)) ^ Q) ^ Q := by
  let r := mixingAlpha t0 / (1 - c0 t0)
  have hc0 : 0 ≤ c0 t0 := by
    unfold c0
    exact div_nonneg (sub_nonneg.mpr (mixingAlpha_lt_one ht0).le) (by norm_num)
  have hc0quarter : c0 t0 ≤ 1 / 4 := by
    unfold c0
    have ha0 := (mixingAlpha_pos ht0).le
    linarith
  have hr0 : 0 ≤ r := div_nonneg (mixingAlpha_pos ht0).le (by
    unfold c0
    have ha0 := mixingAlpha_pos ht0
    have ha1 := mixingAlpha_lt_one ht0
    linarith)
  have hr1 : r < 1 := by
    dsimp [r]
    unfold c0
    have ha0 := mixingAlpha_pos ht0
    have ha1 := mixingAlpha_lt_one ht0
    apply (div_lt_one (by linarith)).2
    linarith
  have hrpow : r ^ Q ≤ 1 := pow_le_one₀ hr0 hr1.le
  have hbase : 0 < 1 - c0 t0 * r ^ Q := by nlinarith
  by_cases hQk : Q ≤ k
  · have heq := signedDepthRawPosterior_le_product_of_le
      (N := N) ht0 hzeta hC v hQk o
    have hp := pow_one_sub_le_signedDepthPosteriorLowerWindow
      (N := N) (Q := Q) hc0 hbase.le v hQk o
      (fun i ↦ signedDepthRawPosterior_le_ratio_pow
        (N := N) (Q := Q) ht0 hzeta hC v _)
    exact heq.trans (div_le_div_of_nonneg_left (pow_nonneg (mixingAlpha_pos ht0).le _)
      (pow_pos hbase _) (by simpa [r] using hp))
  · have hkQ : k < Q := by omega
    have heq := signedDepthRawPosterior_le_product_of_lt
      (N := N) ht0 hzeta hC v hkQ o
    have hp := pow_one_sub_le_signedDepthPosteriorLowerWindow
      (N := N) (Q := Q) hc0 hbase.le v le_rfl o
      (fun i ↦ signedDepthRawPosterior_le_ratio_pow
        (N := N) (Q := Q) ht0 hzeta hC v _)
    have hpowers : (1 - c0 t0 * r ^ Q) ^ Q ≤ (1 - c0 t0 * r ^ Q) ^ k :=
      pow_le_pow_of_le_one hbase.le (by
        nlinarith [mul_nonneg hc0 (pow_nonneg hr0 Q)] : 1 - c0 t0 * r ^ Q ≤ 1)
        (Nat.le_of_lt hkQ)
    calc
      _ ≤ mixingAlpha t0 ^ Q /
          signedDepthPosteriorLowerWindow N t0 zeta C Q v o k := heq
      _ ≤ mixingAlpha t0 ^ Q / (1 - c0 t0 * r ^ Q) ^ k :=
        div_le_div_of_nonneg_left (pow_nonneg (mixingAlpha_pos ht0).le _)
          (pow_pos hbase _) (by simpa [r] using hp)
      _ ≤ mixingAlpha t0 ^ Q / (1 - c0 t0 * r ^ Q) ^ Q :=
        div_le_div_of_nonneg_left (pow_nonneg (mixingAlpha_pos ht0).le _)
          (pow_pos hbase _) hpowers
      _ = _ := by rfl

/-- The analytic bootstrap factor in equation (17) is uniformly bounded in `Q`. [the ht0 condition](hyp:ht0). [the stated conclusion](goal). -/
lemma exists_uniform_signedDepth_bootstrap_factor {t0 : ℝ} (ht0 : 0 < t0) :
    ∃ K0 : ℝ, 0 < K0 ∧ ∀ Q : Nat,
      1 / (1 - c0 t0 * (mixingAlpha t0 / (1 - c0 t0)) ^ Q) ^ Q ≤ K0 := by
  let r := mixingAlpha t0 / (1 - c0 t0)
  let c := c0 t0
  have hc0 : 0 ≤ c := by
    dsimp [c]
    unfold c0
    exact div_nonneg (sub_nonneg.mpr (mixingAlpha_lt_one ht0).le) (by norm_num)
  have hcquarter : c ≤ 1 / 4 := by
    dsimp [c]
    unfold c0
    linarith [(mixingAlpha_pos ht0).le]
  have hr0 : 0 ≤ r := by
    dsimp [r]
    apply div_nonneg (mixingAlpha_pos ht0).le
    unfold c0
    linarith [mixingAlpha_pos ht0, mixingAlpha_lt_one ht0]
  have hr1 : r < 1 := by
    dsimp [r]
    unfold c0
    apply (div_lt_one (by linarith [mixingAlpha_pos ht0, mixingAlpha_lt_one ht0])).2
    linarith [mixingAlpha_pos ht0, mixingAlpha_lt_one ht0]
  let s : Nat → ℝ := fun n ↦ (n : ℝ) * r ^ n
  have hmid0 : 0 ≤ (1 + r) / 2 := by linarith
  have hmid1 : (1 + r) / 2 < 1 := by linarith
  have hrnorm : ‖r‖ < (1 + r) / 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    linarith
  have hs0 : Filter.Tendsto s Filter.atTop (nhds 0) := by
    have hlo := isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
      (R := ℝ) 1 hrnorm
    have hpow0 := tendsto_pow_atTop_nhds_zero_of_lt_one hmid0 hmid1
    simpa [s] using hlo.trans_tendsto hpow0
  rcases hs0.bddAbove_range with ⟨B, hB⟩
  let M := max B 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hsM (Q : Nat) : (Q : ℝ) * r ^ Q ≤ M :=
    le_trans (hB ⟨Q, rfl⟩) (le_max_left _ _)
  refine ⟨Real.exp (2 * c * M), Real.exp_pos _, ?_⟩
  intro Q
  let x := c * r ^ Q
  have hx0 : 0 ≤ x := mul_nonneg hc0 (pow_nonneg hr0 _)
  have hxquarter : x ≤ 1 / 4 :=
    le_trans (mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1.le) hc0)
      (by simpa using hcquarter)
  have hbase : 0 < 1 - x := by linarith
  have hinv : (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
    have hrat : (1 - x)⁻¹ ≤ 1 + 2 * x := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hbase).2
      nlinarith [sq_nonneg x]
    exact hrat.trans (by simpa [add_comm] using Real.add_one_le_exp (2 * x))
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr hbase.le) hinv Q
  have hexp : Real.exp (2 * x) ^ Q ≤ Real.exp (2 * c * M) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hscale := mul_le_mul_of_nonneg_left (hsM Q)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc0)
    dsimp [x]
    nlinarith
  calc
    1 / (1 - c0 t0 * (mixingAlpha t0 / (1 - c0 t0)) ^ Q) ^ Q =
        (1 - x)⁻¹ ^ Q := by simp [x, r, c, inv_pow]
    _ ≤ Real.exp (2 * x) ^ Q := hp
    _ ≤ _ := hexp

end CausalSmith.Stat.PomdpLatentOverlapMinimax
