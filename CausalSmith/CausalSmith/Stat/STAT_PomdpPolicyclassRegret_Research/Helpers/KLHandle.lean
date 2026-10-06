module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparsePacking
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Observed-word likelihood handle

Finite sums retain the stationary initial prefix and the unobserved depth
posterior. The KL theorem will establish the claimed bound on these laws.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open CausalSmith.Stat.PomdpLatentOverlapMinimax
/-- [the sparse retention probability quantity](goal) is defined from
[the hidden-depth scale](hyp:Q) and [the policy-overlap scale](hyp:zeta). -/

noncomputable def sparseRetentionProbability (Q : Nat) (zeta : ℝ) : ℝ :=
  (policyFactor zeta)⁻¹ + (1 - (policyFactor zeta)⁻¹) / hdepth Q

/-- The observed context-action history factor, with the stationary-prefix
factor for indices earlier than the recorded trajectory. -/
noncomputable def retentionFactor {T M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) : ℝ :=
  let ell := min Q t.val
  sparseRetentionProbability Q zeta ^ (Q - ell) *
    ∏ r ∈ (Finset.range T).filter (fun r ↦ t.val - ell ≤ r ∧ r < t.val),
      if hr : r < T then
        retentionIndicator hd code v (w ⟨r, hr⟩).1 (w ⟨r, hr⟩).2.1
      else 0
  -- @realizes a_vt(observed retention history and stationary prefix)

/-- The retention probability is a convex combination of one and the behavior action
probability. For [the hidden-depth scale](hyp:Q), [the policy-overlap scale](hyp:zeta), and
[the policy-overlap scale assumption](hyp:hzeta), this establishes
[the sparse retention probability membership unit interval result](goal). -/
-- @node: sparseRetentionProbability_mem_unitInterval
lemma sparseRetentionProbability_mem_unitInterval (Q : Nat) (zeta : ℝ)
    (hzeta : 0 < zeta) :
    0 ≤ sparseRetentionProbability Q zeta ∧
      sparseRetentionProbability Q zeta ≤ 1 := by
  have hL : 1 ≤ policyFactor zeta := by
    unfold policyFactor
    exact (Real.one_le_exp_iff).2 (le_of_lt hzeta)
  have hLpos : 0 < policyFactor zeta := lt_of_lt_of_le zero_lt_one hL
  have hinv0 : 0 ≤ (policyFactor zeta)⁻¹ := le_of_lt (inv_pos.mpr hLpos)
  have hinv1 : (policyFactor zeta)⁻¹ ≤ 1 := (inv_le_one₀ hLpos).2 hL
  have hh : (1 : ℝ) ≤ hdepth Q := by
    exact_mod_cast (show 1 ≤ hdepth Q by simp [hdepth])
  have hhpos : (0 : ℝ) < hdepth Q := by linarith
  have hfrac : 0 ≤ (1 - (policyFactor zeta)⁻¹) / hdepth Q :=
    div_nonneg (by linarith) (le_of_lt hhpos)
  constructor
  · unfold sparseRetentionProbability
    positivity
  · unfold sparseRetentionProbability
    have hle : (1 - (policyFactor zeta)⁻¹) / hdepth Q ≤
        1 - (policyFactor zeta)⁻¹ :=
      div_le_self (by linarith) hh
    linarith

/-- Every observed-word retention factor lies in the unit interval, including the incomplete
windows at the stationary start. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the policy-overlap scale assumption](hyp:hzeta),
[the binary code](hyp:code), [the codeword index](hyp:v), [the epoch index](hyp:t), and
[the observed word](hyp:w), this establishes
[the retention factor membership unit interval result](goal). -/
-- @node: retentionFactor_mem_unitInterval
lemma retentionFactor_mem_unitInterval {T M d Q : Nat} (hd : 0 < d)
    (zeta : ℝ) (hzeta : 0 < zeta) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) :
    0 ≤ retentionFactor hd zeta code v t w ∧
      retentionFactor hd zeta code v t w ≤ 1 := by
  classical
  obtain ⟨hp0, hp1⟩ := sparseRetentionProbability_mem_unitInterval Q zeta hzeta
  have hterm : ∀ r : Fin T, 0 ≤ retentionIndicator hd code v (w r).1 (w r).2.1 ∧
      retentionIndicator hd code v (w r).1 (w r).2.1 ≤ 1 := by
    intro r
    unfold retentionIndicator
    split_ifs <;> norm_num
  have hprod :
      0 ≤ ∏ r ∈ (Finset.range T).filter
        (fun r ↦ t.val - min Q t.val ≤ r ∧ r < t.val),
        if hr : r < T then
          retentionIndicator hd code v (w ⟨r, hr⟩).1 (w ⟨r, hr⟩).2.1
        else 0 := by
    apply Finset.prod_nonneg
    intro r hr
    split_ifs with h
    · exact (hterm ⟨r, h⟩).1
    · exact le_refl 0
  have hprod1 :
      (∏ r ∈ (Finset.range T).filter
        (fun r ↦ t.val - min Q t.val ≤ r ∧ r < t.val),
        if hr : r < T then
          retentionIndicator hd code v (w ⟨r, hr⟩).1 (w ⟨r, hr⟩).2.1
        else 0) ≤ 1 := by
    apply Finset.prod_le_one
    · intro r hr
      split_ifs with h
      · exact (hterm ⟨r, h⟩).1
      · exact le_refl 0
    · intro r hr
      split_ifs with h
      · exact (hterm ⟨r, h⟩).2
      · norm_num
  unfold retentionFactor
  constructor
  · exact mul_nonneg (pow_nonneg hp0 _) hprod
  · calc
      _ ≤ sparseRetentionProbability Q zeta ^ (Q - min Q t.val) * 1 :=
        mul_le_mul_of_nonneg_left hprod1 (pow_nonneg hp0 _)
      _ ≤ 1 := by simpa using (pow_le_one₀ hp0 hp1 :
        sparseRetentionProbability Q zeta ^ (Q - min Q t.val) ≤ 1)
/-- [the observed prefix agrees predicate](goal) is defined from [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the reward-symbol count](hyp:nR), [the epoch index](hyp:t),
[the observed prefix](hyp:u), and [the observed word](hyp:w). -/

def observedPrefixAgrees {T nX nR : Nat} (t : Fin T)
    (u w : FiniteObsView T nX nR) : Prop :=
  ∀ r : Fin T, r.val < t.val → u r = w r

/-- Bayes numerator for the terminal hidden depth, summed over full words. -/
noncomputable def terminalPrefixMass {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) : ℝ :=
  by
    classical
    let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
    exact ∑ tau : FiniteTrajectory T (d * hdepth Q) (2 * (Q + 1)) 2,
      if observedPrefixAgrees t (finObsProj tau) w ∧
          hiddenDepth Q (tau.1 t.castSucc).2 = Q then
        (F.law tau).toReal else 0
/-- [the observed prefix mass quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the epoch index](hyp:t), and [the observed word](hyp:w). -/

noncomputable def observedPrefixMass {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) : ℝ :=
  by
    classical
    let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
    exact ∑ tau : FiniteTrajectory T (d * hdepth Q) (2 * (Q + 1)) 2,
      if observedPrefixAgrees t (finObsProj tau) w then (F.law tau).toReal else 0

/-- Restricting a nonnegative finite-word mass to an event cannot increase it. For
[the contraction coefficient](hyp:α), [the policy](hyp:p), [the policy assumption](hyp:hp),
[the first event](hyp:A), [the second event](hyp:B), and [the ab assumption](hyp:hAB), this
establishes [the finite event mass bound result](goal). -/
-- @node: finiteEventMass_le
lemma finiteEventMass_le {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (A B : α → Prop)
    [DecidablePred A] [DecidablePred B]
    (hAB : ∀ a, A a → B a) :
    (∑ a, if A a then p a else 0) ≤ ∑ a, if B a then p a else 0 := by
  classical
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : A a
  · simp [ha, hAB a ha]
  · simp only [ha, ↓reduceIte]
    split_ifs <;> simp [hp a]

/-- The terminal-depth Bayes numerator is bounded by its observed-prefix denominator, including
prefixes inside the stationary initial window. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the epoch index](hyp:t), and [the observed word](hyp:w), this establishes
[the terminal prefix mass bound observed prefix mass result](goal). -/
-- @node: terminalPrefixMass_le_observedPrefixMass
lemma terminalPrefixMass_le_observedPrefixMass {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) :
    terminalPrefixMass hd t0 zeta C code v t w ≤
      observedPrefixMass hd t0 zeta C code v t w := by
  classical
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  change (∑ tau, if observedPrefixAgrees t (finObsProj tau) w ∧
      hiddenDepth Q (tau.1 t.castSucc).2 = Q then (F.law tau).toReal else 0) ≤
    ∑ tau, if observedPrefixAgrees t (finObsProj tau) w then
      (F.law tau).toReal else 0
  exact finiteEventMass_le (fun tau ↦ (F.law tau).toReal)
    (fun tau ↦ ENNReal.toReal_nonneg)
    (fun tau ↦ observedPrefixAgrees t (finObsProj tau) w ∧
      hiddenDepth Q (tau.1 t.castSucc).2 = Q)
    (fun tau ↦ observedPrefixAgrees t (finObsProj tau) w)
    (fun tau h ↦ h.1)

/-- Every finite-word terminal Bayes numerator is nonnegative. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the epoch index](hyp:t), and [the observed word](hyp:w), this establishes
[the terminal prefix mass nonnegativity result](goal). -/
-- @node: terminalPrefixMass_nonneg
lemma terminalPrefixMass_nonneg {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) :
    0 ≤ terminalPrefixMass hd t0 zeta C code v t w := by
  unfold terminalPrefixMass
  apply Finset.sum_nonneg
  intro tau _
  split_ifs <;> positivity

/-- Every finite-word observed-prefix Bayes denominator is nonnegative. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the epoch index](hyp:t), and [the observed word](hyp:w), this establishes
[the observed prefix mass nonnegativity result](goal). -/
-- @node: observedPrefixMass_nonneg
lemma observedPrefixMass_nonneg {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) :
    0 ≤ observedPrefixMass hd t0 zeta C code v t w := by
  unfold observedPrefixMass
  apply Finset.sum_nonneg
  intro tau _
  split_ifs <;> positivity
/-- [the terminal posterior quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the epoch index](hyp:t), and [the observed word](hyp:w). -/

noncomputable def terminalPosterior {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) : ℝ :=
  terminalPrefixMass hd t0 zeta C code v t w /
    observedPrefixMass hd t0 zeta C code v t w
  -- @realizes z_vt(terminal-depth posterior given observed prefix)

/-- The finite-word terminal-depth filter is a probability, even on a zero-mass prefix where its
defining quotient is zero. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the binary code](hyp:code), [the codeword index](hyp:v), [the epoch index](hyp:t), and
[the observed word](hyp:w), this establishes
[the terminal posterior membership unit interval result](goal). -/
-- @node: terminalPosterior_mem_unitInterval
lemma terminalPosterior_mem_unitInterval {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) :
    0 ≤ terminalPosterior hd t0 zeta C code v t w ∧
      terminalPosterior hd t0 zeta C code v t w ≤ 1 := by
  have hnum := terminalPrefixMass_nonneg hd t0 zeta C code v t w
  have hden := observedPrefixMass_nonneg hd t0 zeta C code v t w
  have hle := terminalPrefixMass_le_observedPrefixMass hd t0 zeta C code v t w
  constructor
  · exact div_nonneg hnum hden
  · by_cases hpos : 0 < observedPrefixMass hd t0 zeta C code v t w
    · exact (div_le_iff₀ hpos).2 (by simpa [terminalPosterior] using hle)
    · have hzden : observedPrefixMass hd t0 zeta C code v t w = 0 := by
        linarith
      simp [terminalPosterior, hzden]
/-- [the sparse observed probability mass function object](goal) is defined from
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
and [the fair-reference flag](hyp:fair). -/

noncomputable def sparseObservedPMF {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (fair : Bool) : PMF (FiniteObsView T (d * hdepth Q) 2) :=
  (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v fair).obsPMF

/-- The probability of a finite observed prefix under an observed-word law. -/
noncomputable def observedWordPrefixMass {T nX nR : Nat}
    (p : PMF (FiniteObsView T nX nR)) (k : Nat)
    (w : FiniteObsView T nX nR) : ℝ :=
  ∑ u : FiniteObsView T nX nR,
    if (∀ r : Fin T, r.val < k → u r = w r) then (p u).toReal else 0

/-- A complete observed prefix specifies exactly one finite word. This is the terminal factor in
the finite-word likelihood telescoping identity. For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the reward-symbol count](hyp:nR), [the policy](hyp:p), and
[the observed word](hyp:w), this establishes [the observed word prefix mass full result](goal). -/
-- @node: observedWordPrefixMass_full
lemma observedWordPrefixMass_full {T nX nR : Nat}
    (p : PMF (FiniteObsView T nX nR))
    (w : FiniteObsView T nX nR) :
    observedWordPrefixMass p T w = (p w).toReal := by
  classical
  unfold observedWordPrefixMass
  simp only [show (∀ u : FiniteObsView T nX nR,
      (∀ r : Fin T, r.val < T → u r = w r) ↔ u = w) from
    fun u ↦ by
      constructor
      · intro h
        funext r
        exact h r r.isLt
      · intro h r _
        rw [h]]
  simp

/-- The empty prefix has unit mass under every finite observed-word law. For
[the time horizon](hyp:T), [the observed-state count](hyp:nX),
[the reward-symbol count](hyp:nR), [the policy](hyp:p), and [the observed word](hyp:w), this
establishes [the observed word prefix mass zero result](goal). -/
-- @node: observedWordPrefixMass_zero
lemma observedWordPrefixMass_zero {T nX nR : Nat}
    (p : PMF (FiniteObsView T nX nR))
    (w : FiniteObsView T nX nR) :
    observedWordPrefixMass p 0 w = 1 := by
  classical
  simp only [observedWordPrefixMass]
  simp only [Nat.not_lt_zero, false_implies]
  simp only [implies_true, ↓reduceIte]
  rw [← ENNReal.toReal_sum (fun u _ ↦ p.apply_ne_top u)]
  have hmass : (∑ a, p a) = 1 := by
    simpa only [tsum_fintype] using p.tsum_coe
  rw [hmass]
  norm_num

/-- Every observed prefix retains the mass of each complete word extending it. In particular,
all prefixes of a positive-mass word have positive mass. For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the reward-symbol count](hyp:nR), [the policy](hyp:p),
[the history length](hyp:k), and [the observed word](hyp:w), this establishes
[the observed word prefix mass ge word result](goal). -/
-- @node: observedWordPrefixMass_ge_word
lemma observedWordPrefixMass_ge_word {T nX nR : Nat}
    (p : PMF (FiniteObsView T nX nR)) (k : Nat)
    (w : FiniteObsView T nX nR) :
    (p w).toReal ≤ observedWordPrefixMass p k w := by
  classical
  unfold observedWordPrefixMass
  have hnonneg : ∀ u ∈ (Finset.univ : Finset (FiniteObsView T nX nR)),
      0 ≤ if (∀ r : Fin T, r.val < k → u r = w r) then (p u).toReal else 0 := by
    intro u _
    split_ifs <;> positivity
  have hsingle := Finset.single_le_sum hnonneg (Finset.mem_univ w)
  simpa using hsingle

/-- The Bayes numerator after observing the current context, action and reward.
The sum retains only full latent words at terminal depth. -/
noncomputable def terminalRewardBayesNumerator {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) : ℝ := by
  classical
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  exact ∑ tau : FiniteTrajectory T (d * hdepth Q) (2 * (Q + 1)) 2,
    if (∀ r : Fin T, r.val ≤ t.val → finObsProj tau r = w r) ∧
        hiddenDepth Q (tau.1 t.castSucc).2 = Q then
      (F.law tau).toReal else 0

/-- The terminal-depth Bayes numerator computed under the common fair-reward
reference law, with the observed reward included in the prefix. -/
noncomputable def fairRewardBayesNumerator {T M d Q : Nat} (hd : 0 < d)
    (hM : 0 < M) (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) : ℝ := by
  classical
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code ⟨0, hM⟩ true
  exact ∑ tau : FiniteTrajectory T (d * hdepth Q) (2 * (Q + 1)) 2,
    if (∀ r : Fin T, r.val ≤ t.val → finObsProj tau r = w r) ∧
        hiddenDepth Q (tau.1 t.castSucc).2 = Q then
      (F.law tau).toReal else 0

/-- The fair-reward Bayes denominator for the same observed prefix. -/
noncomputable def fairRewardBayesDenominator {T M d Q : Nat} (hd : 0 < d)
    (hM : 0 < M) (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) : ℝ :=
  observedWordPrefixMass
    (sparseObservedPMF hd t0 zeta C code ⟨0, hM⟩ true) (t.val + 1) w

/-- Observed-law chain rule written as the sum of finite-prefix log ratios. -/
noncomputable def observedChainLogRatio {T nX nR : Nat}
    (p p0 : PMF (FiniteObsView T nX nR))
    (w : FiniteObsView T nX nR) : ℝ :=
  ∑ t : Fin T,
    Real.log ((observedWordPrefixMass p (t.val + 1) w /
      observedWordPrefixMass p t.val w) /
      (observedWordPrefixMass p0 (t.val + 1) w /
        observedWordPrefixMass p0 t.val w))

/-- On a word of positive mass under both laws, the observed prefix chain telescopes to the
logarithm of the full-word likelihood ratio. For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the reward-symbol count](hyp:nR), [the policy](hyp:p),
[the p0](hyp:p0), [the observed word](hyp:w), [the policy assumption](hyp:hp), and
[the p0 assumption](hyp:hp0), this establishes
[the observed chain log ratio equality log ratio result](goal). -/
-- @node: observedChainLogRatio_eq_log_ratio
lemma observedChainLogRatio_eq_log_ratio {T nX nR : Nat}
    (p p0 : PMF (FiniteObsView T nX nR))
    (w : FiniteObsView T nX nR)
    (hp : 0 < (p w).toReal) (hp0 : 0 < (p0 w).toReal) :
    observedChainLogRatio p p0 w =
      Real.log ((p w).toReal / (p0 w).toReal) := by
  let x (k : Nat) := observedWordPrefixMass p k w
  let y (k : Nat) := observedWordPrefixMass p0 k w
  have hx (k : Nat) : 0 < x k :=
    lt_of_lt_of_le hp (observedWordPrefixMass_ge_word p k w)
  have hy (k : Nat) : 0 < y k :=
    lt_of_lt_of_le hp0 (observedWordPrefixMass_ge_word p0 k w)
  have hstep (k : Nat) :
      Real.log ((x (k + 1) / x k) / (y (k + 1) / y k)) =
        (Real.log (x (k + 1)) - Real.log (y (k + 1))) -
          (Real.log (x k) - Real.log (y k)) := by
    rw [Real.log_div (ne_of_gt (div_pos (hx (k + 1)) (hx k)))
        (ne_of_gt (div_pos (hy (k + 1)) (hy k))),
      Real.log_div (ne_of_gt (hx (k + 1))) (ne_of_gt (hx k)),
      Real.log_div (ne_of_gt (hy (k + 1))) (ne_of_gt (hy k))]
    ring
  calc
    observedChainLogRatio p p0 w =
        ∑ k : Fin T, ((Real.log (x (k.val + 1)) - Real.log (y (k.val + 1))) -
          (Real.log (x k.val) - Real.log (y k.val))) := by
      unfold observedChainLogRatio
      apply Finset.sum_congr rfl
      intro k _
      exact hstep k.val
    _ = (Real.log (x T) - Real.log (y T)) -
        (Real.log (x 0) - Real.log (y 0)) := by
      simpa only [Finset.sum_range] using
        (Finset.sum_range_sub (fun k ↦ Real.log (x k) - Real.log (y k)) T)
    _ = Real.log ((p w).toReal / (p0 w).toReal) := by
      rw [show x T = (p w).toReal from observedWordPrefixMass_full p w,
        show y T = (p0 w).toReal from observedWordPrefixMass_full p0 w,
        show x 0 = 1 from observedWordPrefixMass_zero p w,
        show y 0 = 1 from observedWordPrefixMass_zero p0 w]
      rw [Real.log_one, sub_self, sub_zero, Real.log_div (by positivity) (by positivity)]

/-- The observed likelihood ingredients include the fair-reward Bayes
numerator and denominator and the finite-word observed-law chain expression. -/
-- @node: def:kl-handle
noncomputable def observedWordHandle {T M d Q : Nat} (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M) (t0 zeta C : ℝ)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v : Fin M) :
    (Fin T → FiniteObsView T (d * hdepth Q) 2 → ℝ) ×
      (Fin T → FiniteObsView T (d * hdepth Q) 2 → ℝ) ×
      (Fin T → FiniteObsView T (d * hdepth Q) 2 → ℝ) ×
      PMF (FiniteObsView T (d * hdepth Q) 2) ×
      PMF (FiniteObsView T (d * hdepth Q) 2) ×
      (Fin T → FiniteObsView T (d * hdepth Q) 2 → ℝ) ×
      (Fin T → FiniteObsView T (d * hdepth Q) 2 → ℝ) ×
      (Fin T → FiniteObsView T (d * hdepth Q) 2 → ℝ) ×
      (FiniteObsView T (d * hdepth Q) 2 → ℝ) :=
  (retentionFactor hd zeta code v,
    terminalPosterior hd t0 zeta C code v,
    fun t w ↦ sparseSignal t0 * sparseEpsilon C *
      retentionFactor hd zeta code v t w * terminalPosterior hd t0 zeta C code v t w,
    sparseObservedPMF hd t0 zeta C code v false,
    sparseObservedPMF hd t0 zeta C code ⟨0, by omega⟩ true,
    terminalRewardBayesNumerator hd t0 zeta C code v,
    fairRewardBayesNumerator hd (by omega) t0 zeta C code,
    fairRewardBayesDenominator hd (by omega) t0 zeta C code,
    observedChainLogRatio
      (sparseObservedPMF hd t0 zeta C code v false)
      (sparseObservedPMF hd t0 zeta C code ⟨0, by omega⟩ true))
  -- @realizes HKL(finite-word likelihood construction) @realizes P0(fair observed PMF)

open Classical in
/-- The squared retention indicator has the same moment as the indicator: for independent
Bernoulli draws it costs one factor of `p` per observed position. This is the finite-product
calculation in (19). For [the ι](hyp:ι), [the state](hyp:s), and [the policy](hyp:p), this
establishes [the bernoulli window second moment result](goal). -/
-- @node: bernoulli_window_second_moment
lemma bernoulli_window_second_moment {ι : Type*} [Fintype ι]
    (s : Finset ι) (p : ℝ) :
    (∑ w : ι → Bool, ∏ i,
      (if w i then p else 1 - p) *
        (if i ∈ s then (if w i then (1 : ℝ) else 0) else 1) ^ 2) =
      p ^ s.card := by
  classical
  calc
    _ = ∏ i, ∑ b : Bool,
        (if b then p else 1 - p) *
          (if i ∈ s then (if b then (1 : ℝ) else 0) else 1) ^ 2 := by
      simpa only using (Fintype.prod_sum (fun i (b : Bool) ↦
        (if b then p else 1 - p) *
          (if i ∈ s then (if b then (1 : ℝ) else 0) else 1) ^ 2)).symm
    _ = p ^ s.card := by
      simp

open Classical in
/-- Stationary-prefix padding and the recorded Bernoulli window together have second moment at
most the full-depth retention probability. For [the ι](hyp:ι), [the state](hyp:s),
[the policy](hyp:p), [the hidden-depth scale](hyp:Q), [the p0 assumption](hyp:hp0),
[the p1 assumption](hyp:hp1), and [the state assumption](hyp:hs), this establishes
[the bernoulli padded window second moment result](goal). -/
-- @node: bernoulli_padded_window_second_moment
lemma bernoulli_padded_window_second_moment {ι : Type*} [Fintype ι]
    (s : Finset ι) (p : ℝ) (Q : Nat)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : s.card ≤ Q) :
    p ^ (2 * (Q - s.card)) *
      (∑ w : ι → Bool, ∏ i,
        (if w i then p else 1 - p) *
          (if i ∈ s then (if w i then (1 : ℝ) else 0) else 1) ^ 2) ≤
      p ^ Q := by
  rw [bernoulli_window_second_moment]
  have hexp : 2 * (Q - s.card) + s.card = Q + (Q - s.card) := by omega
  rw [← pow_add, hexp, pow_add]
  have hpow : p ^ (Q - s.card) ≤ 1 := pow_le_one₀ hp0 hp1
  calc
    p ^ Q * p ^ (Q - s.card) ≤ p ^ Q * 1 :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg hp0 _)
    _ = p ^ Q := mul_one _

end CausalSmith.Stat.PomdpPolicyclassRegret
