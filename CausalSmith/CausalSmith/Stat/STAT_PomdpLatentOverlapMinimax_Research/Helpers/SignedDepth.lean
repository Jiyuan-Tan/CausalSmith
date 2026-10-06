module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FiniteEncoding
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FinitePathMarginal
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.Kernels

set_option linter.style.longLine false

/-! # Signed-depth lower-bound family -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

-- @env: S3
variable (Q : Nat) (v : Bool)

/-- Interpret the Boolean alternative/sign coordinate as `-1` or `+1`. -/
def signedValue (u : Bool) : ℝ := if u then 1 else -1
  -- @realizes \(v\)(two alternatives) @realizes \(U_t\)(hidden sign coordinate)

/-- Decode the depth coordinate packed into `Fin (2*(Q+1))`. -/
def latentDepth (Q : Nat) (h : Fin (2 * (Q + 1))) : Nat := h.val / 2
  -- @realizes \(J_t\)(packed hidden depth)

/-- Decode the sign coordinate packed into `Fin (2*(Q+1))`. -/
def latentSign (Q : Nat) (h : Fin (2 * (Q + 1))) : Bool := decide (h.val % 2 = 1)

/-- The reset-sign amplitude. -/
noncomputable def epsC (C : ℝ) : ℝ := min ((C - 1) / 2) (1 / 2)
  -- @realizes \(\varepsilon_C\)(min((C-1)/2,1/2))

/-- The terminal reward-emission amplitude. -/
noncomputable def c0 (t0 : ℝ) : ℝ := (1 - mixingAlpha t0) / 4
  -- @realizes \(c_0\)((1-alpha)/4)

/-- The stationary depth mass. -/
noncomputable def depthMass (t0 : ℝ) (Q j : Nat) : ℝ :=
  (1 - mixingAlpha t0) * mixingAlpha t0 ^ j /
    (1 - mixingAlpha t0 ^ (Q + 1))
  -- @realizes \(w_j\)(truncated geometric stationary depth mass)

/-- Reset-sign probability weight. -/
noncomputable def resetSignWeight (C : ℝ) (u : Bool) : ℝ :=
  (1 + signedValue u * epsC C) / 2

/-- The signed-depth initial probability mass before normalization. -/
noncomputable def signedDepthInitWeight (t0 zeta C : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) : ℝ :=
  depthMass t0 Q (latentDepth Q h) *
    (1 + signedValue (latentSign Q h) * epsC C *
      policyFactor zeta ^ (-(latentDepth Q h : ℤ))) / 2

/-- Behavior-policy action weight in the signed-depth family. -/
noncomputable def signedDepthBehaviourWeight (zeta : ℝ) (a : Bool) : ℝ :=
  if a then 1 / policyFactor zeta else 1 - 1 / policyFactor zeta

/-- The constant policy whose action-one probability is `r`. -/
noncomputable def actionOnePolicy (r : ℝ) : Policy 1 :=
  fun _ a ↦ if a then r else 1 - r

/-- Hidden-state transition weight implementing reset/advance dynamics. -/
noncomputable def signedDepthStateWeight (t0 C : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) (a : Bool) (h' : Fin (2 * (Q + 1))) : ℝ :=
  let j := latentDepth Q h
  let j' := latentDepth Q h'
  let u := latentSign Q h
  let u' := latentSign Q h'
  if j = Q then
    if j' = 0 then resetSignWeight C u' else 0
  else
    (if j' = 0 then (1 - mixingAlpha t0) * resetSignWeight C u' else 0) +
    (if j' = j + 1 then mixingAlpha t0 *
      (if a then if u' = u then 1 else 0 else 1 / 2) else 0)

/-- Rademacher reward weight with terminal signed mean. -/
noncomputable def signedDepthRewardWeight (t0 : ℝ) (Q : Nat) (v : Bool)
    (h : Fin (2 * (Q + 1))) (r : Fin 2) : ℝ :=
  let y : ℝ := if r = 0 then -1 else 1
  (1 + y * signedValue v * c0 t0 * signedValue (latentSign Q h) *
    (if latentDepth Q h = Q then 1 else 0)) / 2

/-- The finite-symbol signed-depth witness. -/
noncomputable def signedDepthFinite (T : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool) :
    FiniteRewardModel T 1 (2 * (Q + 1)) 2 :=
  let K : JointState 1 (2 * (Q + 1)) → Bool →
      PMF (Fin 2 × JointState 1 (2 * (Q + 1))) :=
    fun s a ↦ pmfOfRealWeight fun p ↦
      signedDepthRewardWeight t0 Q v s.2 p.1 *
        signedDepthStateWeight t0 C Q s.2 a p.2.2
  let init : PMF (JointState 1 (2 * (Q + 1))) :=
    pmfOfRealWeight fun s ↦ signedDepthInitWeight t0 zeta C Q s.2
  let b : Fin 1 → PMF Bool := fun _ ↦ pmfOfRealWeight (signedDepthBehaviourWeight zeta)
  let e : Fin 1 → PMF Bool := fun _ ↦ pmfOfRealWeight fun a ↦ if a then 1 else 0
  { kernel := K
    rew := fun r ↦ if r = 0 then -1 else 1
    rew_mem := by
      intro r
      fin_cases r <;> norm_num
    init := init
    b := b
    e := e
    law := finitePathPMF K init b
    law_generated := finitePathPMF_apply K init b }

/-- Lower-level extension of the finite construction to the boundary `C = 1`.
Public signed-depth alternatives use `signedDepthFamily`, whose paper domain is `C > 1`. -/
noncomputable def signedDepthFamilyAtLeastOne (T : Nat) (t0 zeta C : ℝ)
    (Q : Nat) (v : Bool) :
    0 < t0 → 0 < zeta → 1 ≤ C → 1 ≤ Q →
    RawPomdpExperiment T 1 (2 * (Q + 1)) :=
  fun _ _ _ _ ↦ embed (signedDepthFinite T t0 zeta C Q v)

-- @node: def:signed-depth-family
/-- The signed-depth witness embedded into the unrestricted real-reward world. -/
noncomputable def signedDepthFamily (T : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool) :
    0 < t0 → 0 < zeta → 1 < C → 1 ≤ Q →
    RawPomdpExperiment T 1 (2 * (Q + 1)) :=
  fun _ _ _ _ ↦ embed (signedDepthFinite T t0 zeta C Q v)
  -- @realizes \(Q\)(hidden depth) @realizes \(\mathbb P_{Q,v}^{\mathrm{obs},T}\)(embedded observed-path law)

/-- Every finite observed word has strictly positive mass in the signed-depth family. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepth_fullSupportObs {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) :
    FullSupportPMF (signedDepthFinite T t0 zeta C Q v).obsPMF := by
  classical
  letI : DecidableEq (FiniteObsView T 1 2) := Classical.decEq _
  intro w
  let tau : FiniteTrajectory T 1 (2 * (Q + 1)) 2 :=
    (fun _ ↦ (0, 0), fun t ↦ ((w t).2.1, (w t).2.2))
  have hproj : finObsProj tau = w := by
    funext t
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  have halpha_pos : 0 < mixingAlpha t0 := by
    unfold mixingAlpha
    positivity
  have halpha_lt : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have heps_pos : 0 < epsC C := by
    unfold epsC
    positivity
  have heps_le : epsC C ≤ 1 / 2 := min_le_right _ _
  have hc0_nonneg : 0 ≤ c0 t0 := by
    unfold c0
    positivity
  have hc0_lt : c0 t0 < 1 := by
    unfold c0
    linarith
  have hpmf_pos {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) (a : A)
      (hfa : 0 < f a) : 0 < pmfOfRealWeight f a := by
    have hsum : ∑' x, ENNReal.ofReal (f x) ≠ 0 := by
      apply ne_of_gt
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hfa)
        (ENNReal.le_tsum a)
    rw [pmfOfRealWeight, dif_neg hsum, PMF.normalize_apply]
    apply ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr hfa))
    rw [ENNReal.inv_ne_zero]
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr fun x _ ↦ ENNReal.ofReal_ne_top
  have hreset : 0 < resetSignWeight C false := by
    simp [resetSignWeight, signedValue]
    linarith
  have hinit : 0 < (signedDepthFinite T t0 zeta C Q v).init (tau.1 0) := by
    simp only [signedDepthFinite]
    apply hpmf_pos
    simp [tau, signedDepthInitWeight, latentDepth, latentSign, signedValue,
      depthMass]
    have hden : 0 < 1 - mixingAlpha t0 ^ (Q + 1) := by
      have hp : mixingAlpha t0 ^ (Q + 1) < 1 :=
        pow_lt_one₀ halpha_pos.le halpha_lt (by omega)
      linarith
    have hfac : 0 < 1 - epsC C := by linarith
    positivity
  have hb : ∀ t : Fin T,
      0 < (signedDepthFinite T t0 zeta C Q v).b
        (tau.1 t.castSucc).1 (tau.2 t).1 := by
    intro t
    simp only [signedDepthFinite]
    apply hpmf_pos
    by_cases hact : (tau.2 t).1 = true
    · simp [signedDepthBehaviourWeight, hact, policyFactor]
      positivity
    · have hfalse : (tau.2 t).1 = false := Bool.eq_false_of_not_eq_true hact
      simp [signedDepthBehaviourWeight, hfalse]
      have hL : 1 < policyFactor zeta := by
        rw [policyFactor, Real.one_lt_exp_iff]
        exact hzeta
      have hone : 1 / policyFactor zeta < 1 :=
        (div_lt_one (by positivity : 0 < policyFactor zeta)).2 hL
      simpa only [one_div] using hone
  have hkernel : ∀ t : Fin T,
      0 < (signedDepthFinite T t0 zeta C Q v).kernel
        (tau.1 t.castSucc) (tau.2 t).1 ((tau.2 t).2, tau.1 t.succ) := by
    intro t
    simp only [signedDepthFinite]
    apply hpmf_pos
    apply mul_pos
    · by_cases hQ0 : Q = 0
      · subst Q
        have hr : (w t).2.2 = 0 ∨ (w t).2.2 = 1 := by omega
        rcases hr with hr | hr <;> cases v <;>
          simp [signedDepthRewardWeight, tau, latentDepth, latentSign, signedValue, hr] <;>
          linarith
      · simp [signedDepthRewardWeight, tau, latentDepth, latentSign, signedValue,
          hQ0, Ne.symm hQ0]
    · simp [signedDepthStateWeight, tau, latentDepth, latentSign]
      by_cases hQ0 : Q = 0
      · subst Q
        simpa using hreset
      · rw [if_neg (Ne.symm hQ0)]
        exact mul_pos (sub_pos.mpr halpha_lt) hreset
  have hlaw : 0 < (signedDepthFinite T t0 zeta C Q v).law tau := by
    rw [(signedDepthFinite T t0 zeta C Q v).law_generated tau]
    apply ENNReal.mul_pos (ne_of_gt hinit)
    rw [Finset.prod_ne_zero_iff]
    intro t _
    exact ne_of_gt (ENNReal.mul_pos (ne_of_gt (hb t)) (ne_of_gt (hkernel t)))
  unfold FiniteRewardModel.obsPMF
  rw [PMF.map_apply]
  have hle := ENNReal.le_tsum
    (f := fun a : FiniteTrajectory T 1 (2 * (Q + 1)) 2 ↦
      if w = finObsProj a then (signedDepthFinite T t0 zeta C Q v).law a else 0) tau
  have hle' : (signedDepthFinite T t0 zeta C Q v).law tau ≤
      ∑' a, if w = finObsProj a then (signedDepthFinite T t0 zeta C Q v).law a else 0 := by
    simpa [hproj] using hle
  exact lt_of_lt_of_le hlaw hle'

end CausalSmith.Stat.PomdpLatentOverlapMinimax
