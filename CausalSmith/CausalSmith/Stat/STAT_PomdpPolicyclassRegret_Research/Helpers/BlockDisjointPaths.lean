module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockSegmentOverlap

/-!
# Disjoint PHIW windows after chronological prefixes

The proved conditional future moment identities survive arbitrary unweighted
prefixes. A common anchor for the future mean permits centering at a global
past mean, as required when mixing arbitrary full-state starts.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open scoped BigOperators ENNReal

/-- Equal bounded fixed-start expectations remain equal after any behavior prefix. Each reward
and successor is integrated as one joint step. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the f](hyp:f), [the g](hyp:g),
[the f assumption](hyp:hf), [the g assumption](hyp:hg), [the bf](hyp:Bf), [the bg](hyp:Bg),
[the bf assumption](hyp:hbf), [the bg assumption](hyp:hbg), [the code dimension](hyp:d),
[the sample size](hyp:n), [the equality assumption](hyp:heq), and [the state](hyp:s), this
establishes [the partial-history importance-weighted path shift integral congr result](goal). -/
-- @node: phiwPathShift_integral_congr
lemma phiwPathShift_integral_congr {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b)
    (f g : JointState m.nX m.nH → List (Bool × ℝ × JointState m.nX m.nH) → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (Bf Bg : ℝ) (hbf : ∀ s path, 0 ≤ f s path ∧ f s path ≤ Bf)
    (hbg : ∀ s path, 0 ≤ g s path ∧ g s path ≤ Bg)
    (d n : Nat)
    (heq : ∀ s, (∫ path, f s path ∂segmentFrom m n s) =
      ∫ path, g s path ∂segmentFrom m n s) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathShift f d s path ∂segmentFrom m (d + n) s) =
      ∫ path, phiwPathShift g d s path ∂segmentFrom m (d + n) s := by
  induction d generalizing s with
  | zero => simpa only [phiwPathShift, Nat.zero_add] using heq s
  | succ d ih =>
    have : IsProbabilityMeasure (segmentFrom m ((d + n) + 1) s) :=
      segmentFrom_isProbability m hb _ s
    have hfi := phiwPathShift_memLp m hb f hf Bf hbf (d + 1) ((d + n) + 1) s 1
    have hgi := phiwPathShift_memLp m hb g hg Bg hbg (d + 1) ((d + n) + 1) s 1
    rw [show d + 1 + n = (d + n) + 1 by omega,
      segmentFrom_integral_succ m hb _ s _ (hfi.integrable le_rfl),
      segmentFrom_integral_succ m hb _ s _ (hgi.integrable le_rfl)]
    simp only [phiwPathShift, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
    congr 1
    funext step
    exact ih step.2.2

/-- A disjoint cross-moment conditional future identity survives the entire unweighted past
preceding the first score window. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the code dimension](hyp:d),
[the history length](hyp:k), [the reward symbol](hyp:r), [the extra](hyp:extra), and
[the state](hyp:s), this establishes
[the partial-history importance-weighted path shift disjoint cross identity result](goal). -/
-- @node: phiwPathShift_disjoint_cross_identity
lemma phiwPathShift_disjoint_cross_identity {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (d k r extra : Nat) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathShift (phiwPathReward m j k) d s path *
      phiwPathShift (phiwPathReward m j k) (d + (k + 1 + r)) s path
      ∂segmentFrom m (d + ((k + 1) + (r + ((k + 1) + extra)))) s) =
    ∫ path, phiwPathShift (phiwPathReward m j k) d s path *
      phiwPathShift (fun u _ ↦ markovOperatorIter (listPolicyKernel m m.Mx.b) r
        (phiwChronologicalMean m j k) u) (d + (k + 1)) s path
      ∂segmentFrom m (d + ((k + 1) + (r + ((k + 1) + extra)))) s := by
  let f := markovOperatorIter (listPolicyKernel m m.Mx.b) r (phiwChronologicalMean m j k)
  let X := phiwPathReward m j k
  let Y := phiwPathShift X (k + 1 + r)
  let F := phiwPathShift (fun u _ ↦ f u) (k + 1)
  let B := policyFactor zeta ^ (k + 1)
  have hX := phiwPathReward_bounds t0 zeta C m hClass j k
  have hY := phiwPathShift_bounds X B hX (k + 1 + r)
  have hf : Measurable (fun p : JointState m.nX m.nH ×
      List (Bool × ℝ × JointState m.nX m.nH) ↦ f p.1) := by fun_prop
  have hF := phiwPathShift_bounds (fun u _ ↦ f u) 1
    (fun u _ ↦ phiw_behavior_future_mean_unit t0 zeta C m hClass j r k u) (k + 1)
  have hmX := phiwPathReward_measurable m j k
  have hmY := phiwPathShift_measurable X hmX (k + 1 + r)
  have hmF := phiwPathShift_measurable (fun u _ ↦ f u) hf (k + 1)
  have heq := phiwPathShift_integral_congr m hClass.sequential_ignorability.1
    (fun u p ↦ X u p * Y u p) (fun u p ↦ X u p * F u p)
    (hmX.mul hmY) (hmX.mul hmF) (B * B) (B * 1)
    (fun u p ↦ ⟨mul_nonneg (hX u p).1 (hY u p).1,
      mul_le_mul (hX u p).2 (hY u p).2 (hY u p).1
        (le_trans (hX u p).1 (hX u p).2)⟩)
    (fun u p ↦ ⟨mul_nonneg (hX u p).1 (hF u p).1,
      mul_le_mul (hX u p).2 (hF u p).2 (hF u p).1
        (le_trans (hX u p).1 (hX u p).2)⟩)
    d ((k + 1) + (r + ((k + 1) + extra)))
    (phiwPathReward_disjoint_cross_identity t0 zeta C m hClass j k k r extra) s
  simpa only [phiwPathShift_mul, phiwPathShift_add, X, Y, F, f] using heq

/-- The marginal future identity at the successor of the first window also holds after an
arbitrary chronological prefix. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the code dimension](hyp:d),
[the history length](hyp:k), [the reward symbol](hyp:r), [the extra](hyp:extra), and
[the state](hyp:s), this establishes
[the partial-history importance-weighted path shift disjoint mean identity result](goal). -/
-- @node: phiwPathShift_disjoint_mean_identity
lemma phiwPathShift_disjoint_mean_identity {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (d k r extra : Nat) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathShift (phiwPathReward m j k) (d + (k + 1 + r)) s path
      ∂segmentFrom m (d + ((k + 1) + (r + ((k + 1) + extra)))) s) =
    ∫ path, phiwPathShift (fun u _ ↦ markovOperatorIter (listPolicyKernel m m.Mx.b) r
        (phiwChronologicalMean m j k) u) (d + (k + 1)) s path
      ∂segmentFrom m (d + ((k + 1) + (r + ((k + 1) + extra)))) s := by
  simpa only [Nat.add_assoc] using
    phiwPathShift_future_mean_identity t0 zeta C m hClass j (d + (k + 1)) r k extra s

/-- Centering a nonnegative score of mean at most one at any number in the unit interval costs
at most two in L¹. This allows a mixture's global mean. For [the sample space](hyp:Ω),
[the measure](hyp:μ), [the x](hyp:X), [the event family](hyp:F), [the x assumption](hyp:hX),
[the event family assumption](hyp:hF), [the x0 assumption](hyp:hX0),
[the x1 assumption](hyp:hX1), [the action](hyp:a), [the c](hyp:c), [the d](hyp:D),
[the a0 assumption](hyp:ha0), [the a1 assumption](hyp:ha1), [the d assumption](hyp:hD), and
[the fbound assumption](hyp:hFbound), this establishes
[the partial-history importance-weighted pairing bound of unit center result](goal). -/
-- @node: phiw_pairing_le_of_unit_center
lemma phiw_pairing_le_of_unit_center
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X F : Ω → ℝ) (hX : MemLp X 2 μ) (hF : MemLp F 2 μ)
    (hX0 : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hX1 : (∫ ω, X ω ∂μ) ≤ 1)
    (a c D : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hD : 0 ≤ D)
    (hFbound : ∀ᵐ ω ∂μ, |F ω - c| ≤ D) :
    |∫ ω, (X ω - a) * (F ω - c) ∂μ| ≤ 2 * D := by
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have hcenter : MemLp (fun ω ↦ X ω - a) 2 μ := hX.sub (memLp_const _)
  have hfuture : MemLp (fun ω ↦ F ω - c) 2 μ := hF.sub (memLp_const _)
  have hl1 : (∫ ω, |X ω - a| ∂μ) ≤ 2 := by
    calc
      _ ≤ ∫ ω, X ω + a ∂μ := by
        apply integral_mono_ae (hXi.sub (integrable_const _)).abs
          (hXi.add (integrable_const _))
        filter_upwards [hX0] with ω hω
        calc
          |X ω - a| ≤ |X ω| + |a| := abs_sub _ _
          _ = X ω + a := by rw [abs_of_nonneg hω, abs_of_nonneg ha0]
      _ = (∫ ω, X ω ∂μ) + a := by
        rw [integral_add hXi (integrable_const _)]
        simp
      _ ≤ 2 := by linarith
  calc
    _ ≤ ∫ ω, |(X ω - a) * (F ω - c)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, |X ω - a| * D ∂μ := by
      apply integral_mono_ae (hcenter.integrable_mul hfuture).abs
        ((hXi.sub (integrable_const _)).abs.mul_const D)
      filter_upwards [hFbound] with ω hω
      change |(X ω - a) * (F ω - c)| ≤ |X ω - a| * D
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hω (abs_nonneg _)
    _ = (∫ ω, |X ω - a| ∂μ) * D := integral_mul_const _ _
    _ ≤ 2 * D := mul_le_mul_of_nonneg_right hl1 hD

/-- Substitution of the future mean remains valid when the earlier score is centered at an
arbitrary constant, and the future is anchored at a constant. For [the sample space](hyp:Ω),
[the measure](hyp:μ), [the x](hyp:X), [the y](hyp:Y), [the event family](hyp:F),
[the x assumption](hyp:hX), [the y assumption](hyp:hY), [the event family assumption](hyp:hF),
[the mean assumption](hyp:hmean), [the cross assumption](hyp:hcross), [the action](hyp:a), and
[the c](hyp:c), this establishes
[the partial-history importance-weighted centered cross equality of future identities result](goal). -/
-- @node: phiw_centered_cross_eq_of_future_identities
lemma phiw_centered_cross_eq_of_future_identities
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y F : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hF : MemLp F 2 μ)
    (hmean : (∫ ω, Y ω ∂μ) = ∫ ω, F ω ∂μ)
    (hcross : (∫ ω, X ω * Y ω ∂μ) = ∫ ω, X ω * F ω ∂μ)
    (a c : ℝ) :
    (∫ ω, X ω * Y ω ∂μ) - a * (∫ ω, Y ω ∂μ) -
      c * (∫ ω, X ω ∂μ) + a * c =
      ∫ ω, (X ω - a) * (F ω - c) ∂μ := by
  rw [hcross, hmean]
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have hFi : Integrable F μ := hF.integrable (by norm_num)
  have hXF : Integrable (fun ω ↦ X ω * F ω) μ := hX.integrable_mul hF
  simp_rw [sub_mul, mul_sub]
  integral_linearity
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- A common future anchor bounds a prefixed disjoint cross moment centered at any unit-interval
past mean. The anchor is independent of the initial state. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the code dimension](hyp:d),
[the history length](hyp:k), [the reward symbol](hyp:r), [the extra](hyp:extra),
[the state](hyp:s), [the s₀](hyp:s₀), [the action](hyp:a), [the a0 assumption](hyp:ha0), and
[the a1 assumption](hyp:ha1), this establishes
[the partial-history importance-weighted path shift disjoint centered cross bound result](goal). -/
-- @node: phiwPathShift_disjoint_centered_cross_bound
lemma phiwPathShift_disjoint_centered_cross_bound {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (d k r extra : Nat) (s s₀ : JointState m.nX m.nH)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    let n := d + ((k + 1) + (r + ((k + 1) + extra)))
    let X := phiwPathShift (phiwPathReward m j k) d s
    let Y := phiwPathShift (phiwPathReward m j k) (d + (k + 1 + r)) s
    let c := markovOperatorIter (listPolicyKernel m m.Mx.b) r
      (phiwChronologicalMean m j k) s₀
    |(∫ path, X path * Y path ∂segmentFrom m n s) -
      a * (∫ path, Y path ∂segmentFrom m n s) -
      c * (∫ path, X path ∂segmentFrom m n s) + a * c| ≤
      2 * mixingAlpha t0 ^ (k + r) := by
  dsimp only
  let n := d + ((k + 1) + (r + ((k + 1) + extra)))
  let μ := segmentFrom m n s
  let X := phiwPathShift (phiwPathReward m j k) d s
  let Y := phiwPathShift (phiwPathReward m j k) (d + (k + 1 + r)) s
  let f := markovOperatorIter (listPolicyKernel m m.Mx.b) r (phiwChronologicalMean m j k)
  let F := phiwPathShift (fun u _ ↦ f u) (d + (k + 1)) s
  have : IsProbabilityMeasure μ :=
    segmentFrom_isProbability m hClass.sequential_ignorability.1 n s
  have hX := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (phiwPathReward m j k) (phiwPathReward_measurable m j k)
    _ (phiwPathReward_bounds t0 zeta C m hClass j k) d n s 2
  have hY := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (phiwPathReward m j k) (phiwPathReward_measurable m j k)
    _ (phiwPathReward_bounds t0 zeta C m hClass j k) (d + (k + 1 + r)) n s 2
  have hF : MemLp F 2 μ := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (fun u _ ↦ f u) (by fun_prop) 1
    (fun u _ ↦ phiw_behavior_future_mean_unit t0 zeta C m hClass j r k u)
    (d + (k + 1)) n s 2
  rw [phiw_centered_cross_eq_of_future_identities μ X Y F hX hY hF
    (phiwPathShift_disjoint_mean_identity t0 zeta C m hClass j d k r extra s)
    (phiwPathShift_disjoint_cross_identity t0 zeta C m hClass j d k r extra s) a (f s₀)]
  apply phiw_pairing_le_of_unit_center μ X F hX hF
  · exact Filter.Eventually.of_forall fun path ↦
      (phiwPathShift_bounds _ _ (phiwPathReward_bounds t0 zeta C m hClass j k)
        d s path).1
  · exact phiwPathShift_reward_integral_le_one t0 zeta C m hClass j d k
      (r + ((k + 1) + extra)) s
  · exact ha0
  · exact ha1
  · exact pow_nonneg (Real.exp_nonneg _) _
  · apply Filter.Eventually.of_forall
    intro path
    apply phiwPathShift_anchored_bound (fun u _ ↦ f u) (f s₀) _ _ (d + (k + 1)) s path
    intro u _
    have ho := phiw_disjoint_future_oscillation t0 zeta C m hClass j k
      (k + 1 + r) (by omega) u s₀
    simpa only [show k + 1 + r - k - 1 = r by omega,
      show k + 1 + r - 1 = k + r by omega] using ho

end CausalSmith.Stat.PomdpPolicyclassRegret
