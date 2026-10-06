module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.KLHandle
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseRetention

/-! # Stationary prefix of the observed sparse filter

The actual initial PMF has the geometric depth masses and sign means in
(3)--(4) of the contextual KL roadmap. The forced early-window structural
mass is bounded uniformly as in (11), without revealing reset indicators.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- The actual alternative initial law equals the explicit behavior density. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the state](hyp:s), this establishes
[the sparse init equality signed density result](goal). -/
-- @node: sparse_init_eq_signed_density
lemma sparse_init_eq_signed_density {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (s : JointState (d * hdepth Q) (2 * (Q + 1))) :
    (sparseInit hd t0 zeta C code v false s).toReal =
      sparseSignedDensity d Q t0 C (sparseRetentionProbability Q zeta) s := by
  rw [sparse_init_toReal hd t0 zeta C ht0 hzeta hC code v false,
    sparse_transition_weight_eq hd t0 zeta C ht0 hzeta hC code v false,
    sparse_behavior_weight_stationary_density hd t0 zeta C ht0 hzeta hC code v]
  rfl

/-- Summing the initial sign gives the joint context-depth mass in (3). For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), and [the candidate index](hyp:j), this
establishes [the sparse init context depth mass result](goal). -/
-- @node: sparse_init_context_depth_mass
lemma sparse_init_context_depth_mass {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) (j : Fin (Q + 1)) :
    (∑ u : Fin 2,
      (sparseInit hd t0 zeta C code v false (x, depthSignEquiv Q (j, u))).toReal) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * depthMass t0 Q j.val := by
  simp_rw [sparse_init_eq_signed_density hd t0 zeta C ht0 hzeta hC code v]
  exact sparse_signed_density_sum_sign d Q t0 C _ x j

/-- The initial signed mass at each context and depth retains the bias power. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), and [the candidate index](hyp:j), this
establishes [the sparse init context depth signed mass result](goal). -/
-- @node: sparse_init_context_depth_signed_mass
lemma sparse_init_context_depth_signed_mass {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) (j : Fin (Q + 1)) :
    (∑ u : Fin 2,
      (sparseInit hd t0 zeta C code v false (x, depthSignEquiv Q (j, u))).toReal *
        signValue (hiddenSign Q (depthSignEquiv Q (j, u)))) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * depthMass t0 Q j.val *
        sparseEpsilon C * sparseRetentionProbability Q zeta ^ j.val := by
  simp_rw [sparse_init_eq_signed_density hd t0 zeta C ht0 hzeta hC code v]
  exact sparse_signed_density_sign_moment d Q t0 C _ x j

/-- Every geometric stationary depth mass is strictly positive. For [the mixing scale](hyp:t0),
[the mixing scale assumption](hyp:ht0), [the hidden-depth scale](hyp:Q), and
[the candidate index](hyp:j), this establishes [the sparse depth mass positivity result](goal). -/
-- @node: sparse_depthMass_pos
lemma sparse_depthMass_pos (t0 : ℝ) (ht0 : 0 < t0) (Q j : Nat) :
    0 < depthMass t0 Q j := by
  have hα0 := mixingAlpha_pos ht0
  have hα1 := mixingAlpha_lt_one ht0
  have hp : mixingAlpha t0 ^ (Q + 1) < 1 :=
    pow_lt_one₀ hα0.le hα1 (by omega)
  unfold depthMass
  exact div_pos (mul_pos (by linarith) (pow_pos hα0 _)) (by linarith)

/-- Conditioning the actual stationary sign on context and depth yields exactly the reset bias
times the behavior retention power, as in (4). For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), and [the candidate index](hyp:j), this
establishes [the sparse init conditional sign mean result](goal). -/
-- @node: sparse_init_conditional_sign_mean
lemma sparse_init_conditional_sign_mean {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) (j : Fin (Q + 1)) :
    (∑ u : Fin 2,
      (sparseInit hd t0 zeta C code v false (x, depthSignEquiv Q (j, u))).toReal *
        signValue (hiddenSign Q (depthSignEquiv Q (j, u)))) /
      (∑ u : Fin 2,
        (sparseInit hd t0 zeta C code v false (x, depthSignEquiv Q (j, u))).toReal) =
      sparseEpsilon C * sparseRetentionProbability Q zeta ^ j.val := by
  rw [sparse_init_context_depth_signed_mass hd t0 zeta C ht0 hzeta hC code v,
    sparse_init_context_depth_mass hd t0 zeta C ht0 hzeta hC code v]
  have hn : ((d * hdepth Q : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth])))
  have hj := ne_of_gt (sparse_depthMass_pos t0 ht0 Q j.val)
  field_simp

/-- Marginalizing context as well as sign gives the geometric depth law. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the candidate index](hyp:j), this establishes
[the sparse init depth mass result](goal). -/
-- @node: sparse_init_depth_mass
lemma sparse_init_depth_mass {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (j : Fin (Q + 1)) :
    (∑ x : Fin (d * hdepth Q), ∑ u : Fin 2,
      (sparseInit hd t0 zeta C code v false (x, depthSignEquiv Q (j, u))).toReal) =
      depthMass t0 Q j.val := by
  simp_rw [sparse_init_context_depth_mass hd t0 zeta C ht0 hzeta hC code v]
  have hn : ((d * hdepth Q : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth])))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

/-- The forced initial depth followed by advances has the same structural mass as terminal
stationary depth, throughout the early window in (11). For [the mixing scale](hyp:t0),
[the hidden-depth scale](hyp:Q), [the block index](hyp:ell), and
[the block index assumption](hyp:hell), this establishes
[the sparse stationary prefix advance mass result](goal). -/
-- @node: sparse_stationary_prefix_advance_mass
lemma sparse_stationary_prefix_advance_mass (t0 : ℝ) (Q ell : Nat)
    (hell : ell ≤ Q) :
    depthMass t0 Q (Q - ell) * mixingAlpha t0 ^ ell = depthMass t0 Q Q := by
  unfold depthMass
  rw [div_mul_eq_mul_div, mul_assoc, ← pow_add, Nat.sub_add_cancel hell]

/-- Terminal stationary depth has mass at most the unnormalized advance probability, the last
inequality of (11). For [the mixing scale](hyp:t0), [the mixing scale assumption](hyp:ht0), and
[the hidden-depth scale](hyp:Q), this establishes
[the sparse terminal depth mass upper result](goal). -/
-- @node: sparse_terminal_depth_mass_upper
lemma sparse_terminal_depth_mass_upper (t0 : ℝ) (ht0 : 0 < t0) (Q : Nat) :
    depthMass t0 Q Q ≤ mixingAlpha t0 ^ Q := by
  have hα0 := mixingAlpha_pos ht0
  have hα1 := mixingAlpha_lt_one ht0
  have hp : mixingAlpha t0 ^ (Q + 1) < 1 :=
    pow_lt_one₀ hα0.le hα1 (by omega)
  have hpα : mixingAlpha t0 ^ (Q + 1) ≤ mixingAlpha t0 := by
    calc
      _ = mixingAlpha t0 * mixingAlpha t0 ^ Q := by rw [pow_succ]; ring
      _ ≤ mixingAlpha t0 * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hα0.le hα1.le) hα0.le
      _ = _ := mul_one _
  unfold depthMass
  apply (div_le_iff₀ (by linarith : 0 < 1 - mixingAlpha t0 ^ (Q + 1))).2
  nlinarith [mul_le_mul_of_nonneg_left hpα (pow_nonneg hα0.le Q)]

/-- The actual stationary initial mass of a forced early terminal path is bounded by alpha^Q
uniformly in the number of recorded advances. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the block index](hyp:ell), and
[the block index assumption](hyp:hell), this establishes
[the sparse init prefix advance mass bound result](goal). -/
-- @node: sparse_init_prefix_advance_mass_le
lemma sparse_init_prefix_advance_mass_le {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (ell : Nat) (hell : ell ≤ Q) :
    (∑ x : Fin (d * hdepth Q), ∑ u : Fin 2,
      (sparseInit hd t0 zeta C code v false
        (x, depthSignEquiv Q (⟨Q - ell, by omega⟩, u))).toReal) *
      mixingAlpha t0 ^ ell ≤ mixingAlpha t0 ^ Q := by
  rw [sparse_init_depth_mass hd t0 zeta C ht0 hzeta hC code v]
  exact (sparse_stationary_prefix_advance_mass t0 Q ell hell).trans_le
    (sparse_terminal_depth_mass_upper t0 ht0 Q)

/-- Expectations of an initial-state function under the generated full trajectory equal its
expectation under the supplied initial PMF. For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the reward-symbol count](hyp:nR), [the event family](hyp:F), and [the g](hyp:g), this
establishes [the finite reward model initial sum result](goal). -/
-- @node: finiteRewardModel_initial_sum
lemma finiteRewardModel_initial_sum {T nX nH nR : Nat}
    [NeZero nX] [NeZero nH] [NeZero nR]
    (F : FiniteRewardModel T nX nH nR) (g : JointState nX nH → ℝ) :
    (∑ tau, (F.law tau).toReal * g (tau.1 0)) =
      ∑ s, (F.init s).toReal * g s := by
  calc
    _ = ∑ tau : FiniteTrajectory T nX nH nR,
        finitePathWeightFrom F.kernel (fun s ↦ (F.init s).toReal * g s) F.b tau := by
      apply Finset.sum_congr rfl
      intro tau _
      rw [F.law_generated, ENNReal.toReal_mul, ENNReal.toReal_prod]
      simp only [ENNReal.toReal_mul, finitePathWeightFrom]
      ring
    _ = _ := sum_finitePathWeightFrom F.kernel F.b T _

/-- The actual initial hidden-depth marginal, stated with the hidden-state encoding used by the
Bayes numerator. For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the candidate index](hyp:j), this establishes
[the sparse init hidden depth mass result](goal). -/
-- @node: sparse_init_hidden_depth_mass
lemma sparse_init_hidden_depth_mass {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (j : Fin (Q + 1)) :
    (∑ s : JointState (d * hdepth Q) (2 * (Q + 1)),
      if hiddenDepth Q s.2 = j.val then
        (sparseInit hd t0 zeta C code v false s).toReal else 0) =
      depthMass t0 Q j.val := by
  classical
  rw [Fintype.sum_prod_type]
  have hsum (x : Fin (d * hdepth Q)) :
      (∑ h : Fin (2 * (Q + 1)),
        if hiddenDepth Q h = j.val then
          (sparseInit hd t0 zeta C code v false (x, h)).toReal else 0) =
        ∑ u : Fin 2,
          (sparseInit hd t0 zeta C code v false (x, depthSignEquiv Q (j, u))).toReal := by
    rw [Fintype.sum_equiv (depthSignEquiv Q).symm _
      (fun z ↦ if hiddenDepth Q (depthSignEquiv Q z) = j.val then
        (sparseInit hd t0 zeta C code v false (x, depthSignEquiv Q z)).toReal else 0)
      (fun h ↦ by rw [Equiv.apply_symm_apply]), Fintype.sum_prod_type]
    simp_rw [sparse_hidden_depth_enumeration,
      show ∀ k : Fin (Q + 1), (k.val = j.val) ↔ k = j from fun k ↦ Fin.ext_iff.symm]
    simp
  simp_rw [hsum]
  exact sparse_init_depth_mass hd t0 zeta C ht0 hzeta hC code v j

/-- An empty observed prefix has unit mass under the alternative law. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the epoch index](hyp:t), [the epoch index assumption](hyp:ht), and [the observed word](hyp:w),
this establishes [the observed prefix mass zero epoch result](goal). -/
-- @node: observedPrefixMass_zero_epoch
lemma observedPrefixMass_zero_epoch {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (ht : t.val = 0) (w : FiniteObsView T (d * hdepth Q) 2) :
    observedPrefixMass hd t0 zeta C code v t w = 1 := by
  classical
  have hprefix : ∀ tau : FiniteTrajectory T (d * hdepth Q) (2 * (Q + 1)) 2,
      observedPrefixAgrees t (finObsProj tau) w := by
    intro tau r hr
    simp [ht] at hr
  simp only [observedPrefixMass, hprefix, ↓reduceIte]
  exact sum_pmf_toReal_eq_one _

/-- At the first epoch the terminal Bayes numerator is the stationary terminal-depth mass,
independent of the observed word. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), [the epoch index assumption](hyp:ht), and
[the observed word](hyp:w), this establishes [the terminal prefix mass zero epoch result](goal). -/
-- @node: terminalPrefixMass_zero_epoch
lemma terminalPrefixMass_zero_epoch {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (ht : t.val = 0) (w : FiniteObsView T (d * hdepth Q) 2) :
    terminalPrefixMass hd t0 zeta C code v t w = depthMass t0 Q Q := by
  classical
  let : NeZero (d * hdepth Q) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos hd (by simp [hdepth]))⟩
  let : NeZero (2 * (Q + 1)) := ⟨by omega⟩
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  have hprefix : ∀ tau : FiniteTrajectory T (d * hdepth Q) (2 * (Q + 1)) 2,
      observedPrefixAgrees t (finObsProj tau) w := by
    intro tau r hr
    simp [ht] at hr
  have hindex : t.castSucc = 0 := Fin.ext ht
  simp only [terminalPrefixMass, hprefix, true_and, hindex]
  change (∑ tau, if hiddenDepth Q (tau.1 0).2 = Q then (F.law tau).toReal else 0) = _
  have h := finiteRewardModel_initial_sum F
    (fun s ↦ if hiddenDepth Q s.2 = Q then (1 : ℝ) else 0)
  simpa only [mul_ite, mul_one, mul_zero] using
    h.trans (by simpa [F, sparseFinite, mul_ite] using
      sparse_init_hidden_depth_mass hd t0 zeta C ht0 hzeta hC code v (Fin.last Q))

/-- The observed-prefix terminal posterior starts at its stationary mass. This is the base case
of the early-window Bayes recursion (12). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), [the epoch index assumption](hyp:ht), and
[the observed word](hyp:w), this establishes [the terminal posterior zero epoch result](goal). -/
-- @node: terminalPosterior_zero_epoch
lemma terminalPosterior_zero_epoch {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (ht : t.val = 0) (w : FiniteObsView T (d * hdepth Q) 2) :
    terminalPosterior hd t0 zeta C code v t w = depthMass t0 Q Q := by
  rw [terminalPosterior,
    terminalPrefixMass_zero_epoch hd t0 zeta C ht0 hzeta hC code v t ht w,
    observedPrefixMass_zero_epoch hd t0 zeta C code v t ht w, div_one]

/-- The observed-prefix Bayes recursion (12) holds at the first epoch without any likelihood or
posterior assumption. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), [the epoch index assumption](hyp:ht), and
[the observed word](hyp:w), this establishes
[the terminal posterior zero epoch recursion result](goal). -/
-- @node: terminalPosterior_zero_epoch_recursion
lemma terminalPosterior_zero_epoch_recursion {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (ht : t.val = 0) (w : FiniteObsView T (d * hdepth Q) 2) :
    terminalPosterior hd t0 zeta C code v t w ≤ mixingAlpha t0 ^ Q *
      ∏ r ∈ (Finset.univ : Finset (Fin T)).filter
        (fun r ↦ t.val - min Q t.val ≤ r.val ∧ r.val < t.val),
        (1 - sparseSignal t0 * terminalPosterior hd t0 zeta C code v r w)⁻¹ := by
  classical
  rw [terminalPosterior_zero_epoch hd t0 zeta C ht0 hzeta hC code v t ht w]
  simpa [ht] using sparse_terminal_depth_mass_upper t0 ht0 Q

/-- The initial signed terminal mass at each fresh observed context. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the observed state](hyp:x), this establishes
[the sparse init context terminal signed mass result](goal). -/
-- @node: sparse_init_context_terminal_signed_mass
lemma sparse_init_context_terminal_signed_mass {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (x : Fin (d * hdepth Q)) :
    (∑ h : Fin (2 * (Q + 1)),
      (sparseInit hd t0 zeta C code v false (x, h)).toReal *
        signValue (hiddenSign Q h) * (if hiddenDepth Q h = Q then 1 else 0)) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ * depthMass t0 Q Q *
        sparseEpsilon C * sparseRetentionProbability Q zeta ^ Q := by
  classical
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm _
    (fun z ↦ (sparseInit hd t0 zeta C code v false (x, depthSignEquiv Q z)).toReal *
      signValue (hiddenSign Q (depthSignEquiv Q z)) *
        (if hiddenDepth Q (depthSignEquiv Q z) = Q then 1 else 0))
    (fun h ↦ by rw [Equiv.apply_symm_apply]), Fintype.sum_prod_type]
  simp_rw [sparse_hidden_depth_enumeration, ← Finset.sum_mul,
    sparse_init_context_depth_signed_mass hd t0 zeta C ht0 hzeta hC code v]
  simp_rw [show ∀ j : Fin (Q + 1), (j.val = Q) ↔ j = Fin.last Q from
    fun j ↦ by simp [Fin.ext_iff]]
  simp

/-- Averaging the reward kernel over the actual initial hidden law gives (8) at the first epoch,
with stationary retention padding p_h^Q. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), and [the reward symbol](hyp:r), this
establishes [the sparse init reward joint mass result](goal). -/
-- @node: sparse_init_reward_joint_mass
lemma sparse_init_reward_joint_mass {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) (r : Fin 2) :
    (∑ h : Fin (2 * (Q + 1)),
      (sparseInit hd t0 zeta C code v false (x, h)).toReal *
        sparseRewardWeight t0 Q h r) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ *
        (1 + (if r = 0 then -1 else 1 : ℝ) * sparseSignal t0 * sparseEpsilon C *
          sparseRetentionProbability Q zeta ^ Q * depthMass t0 Q Q) / 2 := by
  have hmass : (∑ h : Fin (2 * (Q + 1)),
      (sparseInit hd t0 zeta C code v false (x, h)).toReal) =
      ((d * hdepth Q : Nat) : ℝ)⁻¹ := by
    simp_rw [sparse_init_eq_signed_density hd t0 zeta C ht0 hzeta hC code v]
    exact sparse_signed_density_context_mass d Q t0 C _ ht0 x
  calc
    _ = (∑ h, (sparseInit hd t0 zeta C code v false (x, h)).toReal) / 2 +
        (if r = 0 then -1 else 1 : ℝ) * sparseSignal t0 / 2 *
          (∑ h, (sparseInit hd t0 zeta C code v false (x, h)).toReal *
            signValue (hiddenSign Q h) * (if hiddenDepth Q h = Q then 1 else 0)) := by
      simp only [sparseRewardWeight, Finset.sum_div, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by
      rw [hmass, sparse_init_context_terminal_signed_mass hd t0 zeta C ht0 hzeta hC code v]
      ring

/-- The first observed context-action-reward joint mass follows from the actual initial PMF and
common kernel; the next hidden state is marginalized. For [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), [the action](hyp:a), and
[the reward symbol](hyp:r), this establishes [the sparse first observation mass result](goal). -/
-- @node: sparse_first_observation_mass
lemma sparse_first_observation_mass {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Fin (d * hdepth Q)) (a : Bool) (r : Fin 2) :
    (∑ h : Fin (2 * (Q + 1)),
      (sparseInit hd t0 zeta C code v false (x, h)).toReal *
        (sparseBehaviorPMF zeta d Q x a).toReal *
        ∑ s' : JointState (d * hdepth Q) (2 * (Q + 1)),
          (sparseKernel hd t0 C code v false (x, h) a (r, s')).toReal) =
      sparseBehaviorWeight zeta a * ((d * hdepth Q : Nat) : ℝ)⁻¹ *
        (1 + (if r = 0 then -1 else 1 : ℝ) * sparseSignal t0 * sparseEpsilon C *
          sparseRetentionProbability Q zeta ^ Q * depthMass t0 Q Q) / 2 := by
  simp_rw [sparse_kernel_toReal hd t0 C ht0 hC code v false]
  simp only [Bool.false_eq_true, if_false, ← Finset.mul_sum,
    sparse_state_weight_sum, mul_one]
  rw [sparse_behavior_pmf_toReal zeta hzeta]
  calc
    _ = sparseBehaviorWeight zeta a *
        ∑ h : Fin (2 * (Q + 1)),
          (sparseInit hd t0 zeta C code v false (x, h)).toReal *
            sparseRewardWeight t0 Q h r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by
      rw [sparse_init_reward_joint_mass hd t0 zeta C ht0 hzeta hC code v]
      ring

end CausalSmith.Stat.PomdpPolicyclassRegret
