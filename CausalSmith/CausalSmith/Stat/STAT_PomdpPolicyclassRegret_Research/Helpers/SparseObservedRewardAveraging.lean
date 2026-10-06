module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseObservedInformation

/-! # Conditioning the observed reward on its chronological history

Finite sums implement the iterated conditioning in (18). Hidden prefixes
are summed out before the conditional reward mean is used.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory InformationTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- Finite expectations commute with pushing a probability mass function through a deterministic
observation map. For [the contraction coefficient](hyp:α), [the β](hyp:β), [the policy](hyp:p),
[the f](hyp:f), and [the g](hyp:g), this establishes
[the finite probability mass function map sum result](goal). -/
-- @node: finitePMF_map_sum
lemma finitePMF_map_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (g : β → ℝ) :
    (∑ b, (p.map f b).toReal * g b) = ∑ a, (p a).toReal * g (f a) := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  have hmap := integral_map (μ := p.toMeasure)
    (measurable_of_finite f).aemeasurable
    (show AEStronglyMeasurable g (p.toMeasure.map f) by fun_prop)
  rw [PMF.toMeasure_map f p (measurable_of_finite _)] at hmap
  simpa only [PMF.integral_eq_sum, smul_eq_mul, Function.comp_def] using hmap

/-- The forward hidden filter at epoch n uses contexts only through n and actions and rewards
strictly before n. For [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the observed state](hyp:x), [the x'](hyp:x'), [the action](hyp:a), [the a'](hyp:a'),
[the reward symbol](hyp:r), [the r'](hyp:r'), [the sample size](hyp:n),
[the observed state assumption](hyp:hx), [the action assumption](hyp:ha), and
[the reward symbol assumption](hyp:hr), this establishes
[the sparse hidden filter prefix congr result](goal). -/
-- @node: sparse_hidden_filter_prefix_congr
lemma sparse_hidden_filter_prefix_congr {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x x' : Nat → Fin (d * hdepth Q)) (a a' : Nat → Bool) (r r' : Nat → Fin 2)
    (n : Nat) (hx : ∀ k ≤ n, x k = x' k)
    (ha : ∀ k < n, a k = a' k) (hr : ∀ k < n, r k = r' k) :
    sparseHiddenFilter hd t0 zeta C code v x a r n =
      sparseHiddenFilter hd t0 zeta C code v x' a' r' n := by
  induction n with
  | zero => simp only [sparseHiddenFilter, hx 0 (le_refl 0)]
  | succ n ih =>
    rw [sparseHiddenFilter, sparseHiddenFilter,
      ih (fun k hk ↦ hx k (by omega)) (fun k hk ↦ ha k (by omega))
        (fun k hk ↦ hr k (by omega)),
      hx n (by omega), hx (n + 1) (le_refl _), ha n (by omega), hr n (by omega)]

/-- The propagated sign bias uses only preceding observed context-action pairs; later
observations cannot change the current conditional mean. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the binary code](hyp:code), [the codeword index](hyp:v), [the observed state](hyp:x),
[the x'](hyp:x'), [the action](hyp:a), [the a'](hyp:a'), [the sample size](hyp:n),
[the candidate index](hyp:j), [the observed state assumption](hyp:hx), and
[the action assumption](hyp:ha), this establishes
[the sparse filter bias prefix congr result](goal). -/
-- @node: sparse_filter_bias_prefix_congr
lemma sparse_filter_bias_prefix_congr {M d Q : Nat} (hd : 0 < d)
    (zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (x x' : Nat → Fin (d * hdepth Q)) (a a' : Nat → Bool) (n j : Nat)
    (hx : ∀ k < n, x k = x' k) (ha : ∀ k < n, a k = a' k) :
    sparseFilterBias hd zeta C code v x a n j =
      sparseFilterBias hd zeta C code v x' a' n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [sparseFilterBias, hx n (by omega), ha n (by omega),
      ih (j - 1) (fun k hk ↦ hx k (by omega)) (fun k hk ↦ ha k (by omega))]

/-- The observed history includes the past contexts and action-reward
pairs, the current context and the current behavior action. -/
-- @node: SparseRewardHistory
abbrev SparseRewardHistory (k nX : Nat) :=
  ((Fin k → Fin nX) × (Fin k → Bool × Fin 2)) × Fin nX × Bool

/-- Separate a full action history into its visible history and hidden path. -/
-- @node: sparseRewardHistoryHiddenEquiv
def sparseRewardHistoryHiddenEquiv (k nX nH : Nat) :
    ((((Fin k → JointState nX nH) × (Fin k → Bool × Fin 2)) × JointState nX nH) × Bool) ≃
      SparseRewardHistory k nX × (Fin (k + 1) → Fin nH) where
  toFun h := ((((fun i ↦ (h.1.1.1 i).1), h.1.1.2), h.1.2.1, h.2),
    Fin.lastCases h.1.2.2 (fun i ↦ (h.1.1.1 i).2))
  invFun z := ((((fun i ↦ (z.1.1.1 i, z.2 i.castSucc)), z.1.1.2),
    (z.1.2.1, z.2 (Fin.last k))), z.1.2.2)
  left_inv h := by
    rcases h with ⟨⟨⟨s, o⟩, x, u⟩, a⟩
    simp
  right_inv z := by
    rcases z with ⟨⟨⟨x, o⟩, c, a⟩, h⟩
    apply Prod.ext
    · rfl
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp

/-- Complete a visible history with dummy future observations. The current
context and action are retained, while the current reward is still unobserved. -/
-- @node: sparseRewardHistoryExtension
def sparseRewardHistoryExtension {k nX : Nat} (h : SparseRewardHistory k nX)
    (n : Nat) : Fin nX × Bool × Fin 2 :=
  if hn : n < k then (h.1.1 ⟨n, hn⟩, h.1.2 ⟨n, hn⟩) else (h.2.1, h.2.2, 0)

/-- The filter mean evaluated on a visible chronological history. -/
-- @node: sparseRewardHistoryMean
noncomputable def sparseRewardHistoryMean {M d Q k : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (h : SparseRewardHistory k (d * hdepth Q)) : ℝ :=
  let x := fun n ↦ (sparseRewardHistoryExtension h n).1
  let a := fun n ↦ (sparseRewardHistoryExtension h n).2.1
  let r := fun n ↦ (sparseRewardHistoryExtension h n).2.2
  sparseSignal t0 * sparseFilterBias hd zeta C code v x a k Q *
    ((∑ u, sparseHiddenFilter hd t0 zeta C code v x a r k
      (depthSignEquiv Q (Fin.last Q, u))) /
      (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r k u))

/-- Evaluating the filter on the full observed word or its visible pre-reward history gives the
same current mean. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the binary code](hyp:code), [the codeword index](hyp:v), [the epoch index](hyp:t), and
[the observed word](hyp:w), this establishes
[the sparse observed reward mean equality history mean result](goal). -/
-- @node: sparse_observed_reward_mean_eq_history_mean
lemma sparse_observed_reward_mean_eq_history_mean {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) :
    sparseObservedRewardMean hd t0 zeta C code v t w =
      sparseRewardHistoryMean hd t0 zeta C code v
        (((fun i ↦ (w (prefixIndex t i)).1),
          (fun i ↦ (w (prefixIndex t i)).2)), (w t).1, (w t).2.1) := by
  let H : SparseRewardHistory t.val (d * hdepth Q) :=
    (((fun i ↦ (w (prefixIndex t i)).1), (fun i ↦ (w (prefixIndex t i)).2)),
      (w t).1, (w t).2.1)
  have hx (n : Nat) (hn : n ≤ t.val) :
      (sparseObservedWordExtension hd w n).1 = (sparseRewardHistoryExtension H n).1 := by
    have hnT : n < T := lt_of_le_of_lt hn t.isLt
    by_cases hnt : n < t.val
    · simp [sparseObservedWordExtension, sparseRewardHistoryExtension, H, hnT, hnt,
        prefixIndex]
    · have heq : n = t.val := by omega
      subst n
      simp [sparseObservedWordExtension, sparseRewardHistoryExtension, H, t.isLt]
  have hao (n : Nat) (hn : n < t.val) :
      (sparseObservedWordExtension hd w n).2 = (sparseRewardHistoryExtension H n).2 := by
    have hnT : n < T := lt_trans hn t.isLt
    simp [sparseObservedWordExtension, sparseRewardHistoryExtension, H, hnT, hn,
      prefixIndex]
  dsimp only [sparseObservedRewardMean, sparseRewardHistoryMean]
  rw [sparse_hidden_filter_prefix_congr hd t0 zeta C code v _ _ _ _ _ _ t.val
    hx (fun n hn ↦ congrArg Prod.fst (hao n hn))
      (fun n hn ↦ congrArg Prod.snd (hao n hn))]
  rw [sparse_filter_bias_prefix_congr hd zeta C code v _ _ _ _ t.val Q
    (fun n hn ↦ hx n hn.le) (fun n hn ↦ congrArg Prod.fst (hao n hn))]

/-- Actual probability mass of a visible pre-reward history, with the
compatible hidden prefixes marginalized. -/
-- @node: sparseRewardHistoryMass
noncomputable def sparseRewardHistoryMass {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (H : SparseRewardHistory t.val (d * hdepth Q)) : ℝ :=
  ∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
    (((sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false).law.map
      (finiteHistActionPair t))
        ((sparseRewardHistoryHiddenEquiv t.val (d * hdepth Q) (2 * (Q + 1))).symm
          (H, h))).toReal

/-- Actual joint mass of a visible pre-reward history and its next reward;
all hidden prefixes and successor states are marginalized. -/
-- @node: sparseRewardHistoryRewardMass
noncomputable def sparseRewardHistoryRewardMass {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (H : SparseRewardHistory t.val (d * hdepth Q)) (y : Fin 2) : ℝ :=
  ∑ h : Fin (t.val + 1) → Fin (2 * (Q + 1)),
    ∑ s' : JointState (d * hdepth Q) (2 * (Q + 1)),
      (((sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false).law.map
        (finiteHistNextPair t))
          (((sparseRewardHistoryHiddenEquiv t.val (d * hdepth Q) (2 * (Q + 1))).symm
            (H, h)), (y, s'))).toReal

/-- A positive visible history has the normalized Rademacher reward law with precisely the
history-filter mean from equation (8). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), [the h](hyp:H), and [the y](hyp:y), this
establishes [the sparse reward history normalized reward result](goal). -/
-- @node: sparse_reward_history_normalized_reward
lemma sparse_reward_history_normalized_reward {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (H : SparseRewardHistory t.val (d * hdepth Q)) (y : Fin 2) :
    sparseRewardHistoryRewardMass hd t0 zeta C code v t H y /
      sparseRewardHistoryMass hd t0 zeta C code v t H =
        (1 + (if y = 0 then -1 else 1 : ℝ) *
          sparseRewardHistoryMean hd t0 zeta C code v H) / 2 := by
  have h := sparse_generated_action_history_reward_ratio hd t0 zeta C code v
    (fun n ↦ (sparseRewardHistoryExtension H n).1)
    (fun n ↦ (sparseRewardHistoryExtension H n).2.1)
    (fun n ↦ (sparseRewardHistoryExtension H n).2.2) ht0 hzeta hC t y
  have h' := congrArg (fun z : ℝ ↦ z / 2) h
  simpa [sparseRewardHistoryRewardMass, sparseRewardHistoryMass,
    sparseRewardHistoryMean, sparseRewardHistoryHiddenEquiv,
    sparseRewardHistoryExtension, Fin.isLt, div_div] using h' 

/-- Every visible chronological history has positive mass, so its conditional reward probability
can be multiplied back into its joint mass. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), and [the h](hyp:H), this establishes
[the sparse reward history mass positivity result](goal). -/
-- @node: sparse_reward_history_mass_pos
lemma sparse_reward_history_mass_pos {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (H : SparseRewardHistory t.val (d * hdepth Q)) :
    0 < sparseRewardHistoryMass hd t0 zeta C code v t H := by
  have h := sparse_generated_action_history_mass_pos hd t0 zeta C code v
    (fun n ↦ (sparseRewardHistoryExtension H n).1)
    (fun n ↦ (sparseRewardHistoryExtension H n).2.1)
    (fun n ↦ (sparseRewardHistoryExtension H n).2.2) ht0 hzeta hC t
  simpa [sparseRewardHistoryMass, sparseRewardHistoryHiddenEquiv,
    sparseRewardHistoryExtension, Fin.isLt] using h

/-- Averaging a signed reward at each fixed visible history gives its probability mass times the
squared conditional reward mean. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the epoch index](hyp:t), and [the h](hyp:H), this establishes
[the sparse reward history signed mean equality sq result](goal). -/
-- @node: sparse_reward_history_signed_mean_eq_sq
lemma sparse_reward_history_signed_mean_eq_sq {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (H : SparseRewardHistory t.val (d * hdepth Q)) :
    (∑ y : Fin 2, sparseRewardHistoryRewardMass hd t0 zeta C code v t H y *
      ((if y = 0 then -1 else 1 : ℝ) * sparseRewardHistoryMean hd t0 zeta C code v H)) =
      sparseRewardHistoryMass hd t0 zeta C code v t H *
        sparseRewardHistoryMean hd t0 zeta C code v H ^ 2 := by
  have hpos := sparse_reward_history_mass_pos hd t0 zeta C ht0 hzeta hC code v t H
  have hmass (y : Fin 2) := (div_eq_iff hpos.ne').mp
    (sparse_reward_history_normalized_reward hd t0 zeta C ht0 hzeta hC code v t H y)
  simp_rw [hmass]
  rw [Fin.sum_univ_two]
  norm_num
  <;> ring

/-- Push the generated trajectory expectation to its visible pre-reward histories, marginalizing
hidden states first. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the binary code](hyp:code), [the codeword index](hyp:v), [the epoch index](hyp:t), and
[the g](hyp:g), this establishes [the sparse generated visible history sum result](goal). -/
-- @node: sparse_generated_visible_history_sum
lemma sparse_generated_visible_history_sum {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (g : SparseRewardHistory t.val (d * hdepth Q) → ℝ) :
    (∑ tau, ((sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false).law tau).toReal *
      g ((sparseRewardHistoryHiddenEquiv t.val (d * hdepth Q) (2 * (Q + 1)))
        (finiteHistActionPair t tau)).1) =
      ∑ H, sparseRewardHistoryMass hd t0 zeta C code v t H * g H := by
  let e := sparseRewardHistoryHiddenEquiv t.val (d * hdepth Q) (2 * (Q + 1))
  rw [← finitePMF_map_sum _ (finiteHistActionPair t) (fun h ↦ g (e h).1)]
  rw [Fintype.sum_equiv e _
    (fun z ↦ (((sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false).law.map
      (finiteHistActionPair t)) (e.symm z)).toReal * g z.1)
    (fun h ↦ by simp), Fintype.sum_prod_type]
  simp only [sparseRewardHistoryMass, Finset.sum_mul, e]

/-- Push a history-and-reward score to its visible joint masses, summing all successor states
and hidden prefixes. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the code dimension](hyp:d), [the hidden-depth scale](hyp:Q),
[the code dimension assumption](hyp:hd), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the binary code](hyp:code), [the codeword index](hyp:v), [the epoch index](hyp:t), and
[the g](hyp:g), this establishes [the sparse generated visible history reward sum result](goal). -/
-- @node: sparse_generated_visible_history_reward_sum
lemma sparse_generated_visible_history_reward_sum {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T)
    (g : SparseRewardHistory t.val (d * hdepth Q) → Fin 2 → ℝ) :
    (∑ tau, ((sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false).law tau).toReal *
      g ((sparseRewardHistoryHiddenEquiv t.val (d * hdepth Q) (2 * (Q + 1)))
        (finiteHistActionPair t tau)).1 (tau.2 t).2) =
      ∑ H, ∑ y, sparseRewardHistoryRewardMass hd t0 zeta C code v t H y * g H y := by
  let e := sparseRewardHistoryHiddenEquiv t.val (d * hdepth Q) (2 * (Q + 1))
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  change (∑ tau, (F.law tau).toReal *
    g (e (finiteHistNextPair t tau).1).1 (finiteHistNextPair t tau).2.1) = _
  rw [← finitePMF_map_sum F.law (finiteHistNextPair t) (fun z ↦ g (e z.1).1 z.2.1)]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_equiv e _
    (fun z ↦ ∑ y, ((F.law.map (finiteHistNextPair t)) (e.symm z, y)).toReal * g z.1 y.1)
    (fun h ↦ by simp), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro H _
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [sparseRewardHistoryRewardMass, Finset.sum_mul, e, F, Fintype.sum_prod_type]

/-- Iterated conditioning in (18): the expectation of the realized signed reward times its
observed-history mean equals the expected squared mean. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the epoch index](hyp:t), this establishes
[the sparse observed signed reward mean equality sq result](goal). -/
-- @node: sparse_observed_signed_reward_mean_eq_sq
lemma sparse_observed_signed_reward_mean_eq_sq {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M) (t : Fin T) :
    (∑ w : FiniteObsView T (d * hdepth Q) 2,
      (sparseObservedPMF hd t0 zeta C code v false w).toReal *
        ((if (w t).2.2 = 0 then -1 else 1 : ℝ) *
          sparseObservedRewardMean hd t0 zeta C code v t w)) =
      ∑ w : FiniteObsView T (d * hdepth Q) 2,
        (sparseObservedPMF hd t0 zeta C code v false w).toReal *
          sparseObservedRewardMean hd t0 zeta C code v t w ^ 2 := by
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  let e := sparseRewardHistoryHiddenEquiv t.val (d * hdepth Q) (2 * (Q + 1))
  change (∑ w, (F.obsPMF w).toReal * _) = ∑ w, (F.obsPMF w).toReal * _
  rw [finiteRewardModel_observed_sum, finiteRewardModel_observed_sum]
  simp_rw [sparse_observed_reward_mean_eq_history_mean hd t0 zeta C code v t]
  change (∑ tau, (F.law tau).toReal *
    ((if (tau.2 t).2 = 0 then -1 else 1 : ℝ) *
      sparseRewardHistoryMean hd t0 zeta C code v (e (finiteHistActionPair t tau)).1)) =
    ∑ tau, (F.law tau).toReal *
      sparseRewardHistoryMean hd t0 zeta C code v (e (finiteHistActionPair t tau)).1 ^ 2
  rw [sparse_generated_visible_history_reward_sum hd t0 zeta C code v t
    (fun H y ↦ (if y = 0 then -1 else 1 : ℝ) *
      sparseRewardHistoryMean hd t0 zeta C code v H)]
  rw [sparse_generated_visible_history_sum hd t0 zeta C code v t
    (fun H ↦ sparseRewardHistoryMean hd t0 zeta C code v H ^ 2)]
  apply Finset.sum_congr rfl
  intro H _
  exact sparse_reward_history_signed_mean_eq_sq hd t0 zeta C ht0 hzeta hC code v t H

/-- The actual finite observed law obeys the contextual KL budget from (18)--(20), with
stationary windows included and no reset indicator observed. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT),
[the binary code](hyp:code), [the codeword index](hyp:v), and [the v0](hyp:v0), this establishes
[the sparse observed KL div bound budget result](goal). -/
-- @node: sparse_observed_klDiv_le_budget
lemma sparse_observed_klDiv_le_budget {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hT : 0 < T) (code : Fin M → Fin d → Bool) (v v0 : Fin M) :
    (klDiv (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false).toMeasure
      (sparseObservedPMF hd t0 zeta C code v0 true).toMeasure).toReal ≤
        klConstant t0 zeta * T * overlapRadius C ^ 2 * mixingAlpha t0 ^ (2 * Q) *
          policyFactor zeta ^ (-(Q : ℤ)) := by
  calc
    _ ≤ _ := sparse_observed_klDiv_le_signed_reward_sum hd t0 zeta C ht0 hzeta hC hT
      code v v0
    _ = ∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
        (sparseObservedPMF hd t0 zeta C code v false w).toReal *
          sparseObservedRewardMean hd t0 zeta C code v t w ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      exact sparse_observed_signed_reward_mean_eq_sq hd t0 zeta C ht0 hzeta hC code v t
    _ ≤ _ := sparse_observed_reward_mean_sq_sum_le_frontier_budget hd t0 zeta C
      ht0 hzeta hC code v

end CausalSmith.Stat.PomdpPolicyclassRegret
