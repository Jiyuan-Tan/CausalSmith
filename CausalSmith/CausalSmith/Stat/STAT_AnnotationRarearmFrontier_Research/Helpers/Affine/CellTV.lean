module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.CellPredictive
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.NumericalTV

/-!
Absolute singleton discrepancy bounds for the actual core/filler rare-cell
predictive measures, connecting their likelihoods to the signed Taylor envelope.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
open NormalizedFiniteSignedMomentCertificate

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,he,he',hu,hw,first,B,eps,u,w,r,g,c), Either deterministic marked pattern has the same absolute signed discrepancy.
The core/filler likelihood is read back before taking the absolute value.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_abs_target_sub
lemma affineCellPoissonPredictive_abs_target_sub {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (he : 0 < eps) (he' : eps < 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (first : Bool) (r g c : Nat) :
    let b0 := B / (100 * (L : Real) ^ 2) / eps
    |(affineCellPoissonPredictive sigma u w true).real {palmSplitTarget first r g c} -
      (affineCellPoissonPredictive sigma u w false).real {palmSplitTarget first r g c}| =
    |∑ i, sigma.weights i *
        (Real.exp (-(u + w) * (b0 + sigma.nodes i)) *
          (u * (eps * b0 + (1 - eps) * sigma.nodes i)) ^ (r + 1) *
          (w * (eps * b0 + (1 - eps) * sigma.nodes i)) ^ g *
          ((u + w) * ((1 - eps) * b0 + eps * sigma.nodes i)) ^ c /
            (((r + 1).factorial : Real) * (g.factorial : Real) * (c.factorial : Real)) *
          (eps * b0 / (eps * b0 + (1 - eps) * sigma.nodes i)))| := by
  intro b0
  rw [affineCellPoissonPredictive_equation_six sigma u w ha he he' hu hw]
  cases first <;> simp [b0]

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,he,he',hu,hw,first,B,eps,u,w), The actual one-cell predictive singleton discrepancies are absolutely
summable, and their sum over one deterministic mark pattern has equation (7)'s bound.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_target_tail_bound
lemma affineCellPoissonPredictive_target_tail_bound {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (he : 0 < eps) (he' : eps < 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (first : Bool) :
    let D : Nat × (Nat × Nat) → Real := fun v =>
      |(affineCellPoissonPredictive sigma u w true).real
          {palmSplitTarget first v.2.1 v.2.2 v.1} -
        (affineCellPoissonPredictive sigma u w false).real
          {palmSplitTarget first v.2.1 v.2.2 v.1}|
    Summable D ∧ (∑' v, D v) ≤
      u * (B / (100 * (L : Real) ^ 2)) *
        ∑' h : Nat, if L < h then (2 * (u + w) * B) ^ h / (h.factorial : Real) else 0 := by
  intro D
  have hab : eps * (B / (100 * (L : Real) ^ 2) / eps) =
      B / (100 * (L : Real) ^ 2) := mul_div_cancel₀ _ he.ne'
  have h := affine_signed_raw_count_tail_bound sigma
    (B / (100 * (L : Real) ^ 2) / eps) u w (u + w)
    (div_pos ha he) he he'.le hu hw rfl
  simpa only [D, affineCellPoissonPredictive_abs_target_sub sigma u w ha he he' hu hw,
    hab] using h

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,first,n,m,d), At the paper's tuning the K-cell budget for actual marked-pattern
singleton discrepancies is strictly below one sixty-fourth.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_joint_target_small
lemma affineCellPoissonPredictive_joint_target_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (first : Bool) :
    let t := affineTuning n m d eps
    (t.Kstar : Real) * (∑' v : Nat × (Nat × Nat),
      |(affineCellPoissonPredictive sigma t.u t.w true).real
          {palmSplitTarget first v.2.1 v.2.2 v.1} -
        (affineCellPoissonPredictive sigma t.u t.w false).real
          {palmSplitTarget first v.2.1 v.2.2 v.1}|) < 1 / 64 := by
  intro t
  obtain ⟨_, _, _, _, _, ha, _, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hu : 0 ≤ t.u := by change 0 ≤ 128 * (n : Real); positivity
  have hw : 0 ≤ t.w := by change 0 ≤ 128 * ((n : Real) + m); positivity
  have h := (affineCellPoissonPredictive_target_tail_bound sigma t.u t.w
    ha heps (by linarith) hu hw first).2
  have hM : t.u + t.w = t.M := rfl
  have hA : t.B / (100 * (t.L : Real) ^ 2) = t.alpha := rfl
  change (∑' v : Nat × (Nat × Nat),
    |(affineCellPoissonPredictive sigma t.u t.w true).real
        {palmSplitTarget first v.2.1 v.2.2 v.1} -
      (affineCellPoissonPredictive sigma t.u t.w false).real
        {palmSplitTarget first v.2.1 v.2.2 v.1}|) ≤
    t.u * (t.B / (100 * (t.L : Real) ^ 2)) *
      ∑' h : Nat, if t.L < h then (2 * (t.u + t.w) * t.B) ^ h /
        (h.factorial : Real) else 0 at h
  rw [hM, hA] at h
  have hbudget := affine_poisson_joint_tail_small n m d eps hn hd heps heps'
  change (t.Kstar : Real) * t.u * t.alpha *
    (∑' h : Nat, if t.L < h then (2 * t.M * t.B) ^ h /
      (h.factorial : Real) else 0) < 1 / 64 at hbudget
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))
  simpa only [mul_assoc] using hbudget

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,he,he',hu,hw,B,eps,u,w), The two disjoint deterministic mark patterns exhaust the predictive discrepancy;
null treated counts and mixed positive marks contribute zero.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_l1_eq
lemma affineCellPoissonPredictive_l1_eq {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (he : 0 < eps) (he' : eps < 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) :
    (∑' o : MarkedPoissonObservation,
      |(affineCellPoissonPredictive sigma u w true).real {o} -
        (affineCellPoissonPredictive sigma u w false).real {o}|) =
    (∑' v : Nat × (Nat × Nat),
      |(affineCellPoissonPredictive sigma u w true).real
          {palmSplitTarget true v.2.1 v.2.2 v.1} -
        (affineCellPoissonPredictive sigma u w false).real
          {palmSplitTarget true v.2.1 v.2.2 v.1}|) +
    (∑' v : Nat × (Nat × Nat),
      |(affineCellPoissonPredictive sigma u w true).real
          {palmSplitTarget false v.2.1 v.2.2 v.1} -
        (affineCellPoissonPredictive sigma u w false).real
          {palmSplitTarget false v.2.1 v.2.2 v.1}|) := by
  classical
  let D : MarkedPoissonObservation → Real := fun o =>
    |(affineCellPoissonPredictive sigma u w true).real {o} -
      (affineCellPoissonPredictive sigma u w false).real {o}|
  let embed : Bool × (Nat × (Nat × Nat)) → MarkedPoissonObservation :=
    fun z => palmSplitTarget z.1 z.2.2.1 z.2.2.2 z.2.1
  have hi : Function.Injective embed := by
    rintro ⟨a, c, r, g⟩ ⟨b, c', r', g'⟩ h
    cases a <;> cases b <;> simp [embed, palmSplitTarget] at h ⊢ <;> omega
  have hcover : Function.support D ⊆ Set.range embed := by
    rintro ⟨⟨a, b⟩, g, c⟩ ho
    cases a with
    | zero =>
      cases b with
      | zero =>
        exfalso
        exact ho (by simp [D, affineCellPoissonPredictive_no_labeled_eq])
      | succ b => exact ⟨(false, c, b, g), rfl⟩
    | succ a =>
      cases b with
      | zero => exact ⟨(true, c, a, g), rfl⟩
      | succ b =>
        exfalso
        exact ho (by simp [D, affineCellPoissonPredictive_mixed_zero])
  have hsum : (∑' o, D o) = ∑' z : Bool × (Nat × (Nat × Nat)), D (embed z) := by
    apply tsum_eq_tsum_of_ne_zero_bij (fun z => embed z.val)
    · exact hi.comp Subtype.val_injective
    · intro o ho
      change D o ≠ 0 at ho
      obtain ⟨z, hz⟩ := hcover ho
      refine ⟨⟨z, ?_⟩, hz⟩
      change D (embed z) ≠ 0
      simpa only [hz] using ho
    · intro z; rfl
  have hs : Summable (fun z : Bool × (Nat × (Nat × Nat)) => D (embed z)) := by
    apply (summable_prod_of_nonneg (fun z => abs_nonneg _)).2
    refine ⟨?_, (hasSum_fintype _).summable⟩
    intro first
    exact (affineCellPoissonPredictive_target_tail_bound sigma u w ha he he' hu hw first).1
  rw [hsum, hs.tsum_prod' hs.prod_factor]
  simp only [tsum_fintype, Fintype.sum_bool, D, embed]

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,he,he',hu,hw,B,eps,u,w), The actual rare-cell predictive total variation is bounded by the signed
Taylor tail, retaining both observed channels and the core/filler mixture.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_tv_le
lemma affineCellPoissonPredictive_tv_le {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (he : 0 < eps) (he' : eps < 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) :
    Causalean.Stat.tvDist (affineCellPoissonPredictive sigma u w true)
      (affineCellPoissonPredictive sigma u w false) ≤
      u * (B / (100 * (L : Real) ^ 2)) *
        ∑' h : Nat, if L < h then (2 * (u + w) * B) ^ h / (h.factorial : Real) else 0 := by
  have htv := Causalean.Stat.tvDist_le_half_tsum_singleton_abs
    (affineCellPoissonPredictive sigma u w true)
    (affineCellPoissonPredictive sigma u w false)
  rw [affineCellPoissonPredictive_l1_eq sigma u w ha he he' hu hw] at htv
  have ht := (affineCellPoissonPredictive_target_tail_bound sigma u w ha he he' hu hw true).2
  have hf := (affineCellPoissonPredictive_target_tail_bound sigma u w ha he he' hu hw false).2
  linarith

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), The tuned sum of rare-cell total variation bounds is below the paper's
one-sixty-fourth budget.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_joint_tv_small
lemma affineCellPoissonPredictive_joint_tv_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    let t := affineTuning n m d eps
    (t.Kstar : Real) * Causalean.Stat.tvDist
      (affineCellPoissonPredictive sigma t.u t.w true)
      (affineCellPoissonPredictive sigma t.u t.w false) < 1 / 64 := by
  intro t
  obtain ⟨_, _, _, _, _, ha, _, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hu : 0 ≤ t.u := by change 0 ≤ 128 * (n : Real); positivity
  have hw : 0 ≤ t.w := by change 0 ≤ 128 * ((n : Real) + m); positivity
  have h := affineCellPoissonPredictive_tv_le sigma t.u t.w ha heps (by linarith) hu hw
  change Causalean.Stat.tvDist
    (affineCellPoissonPredictive sigma t.u t.w true)
    (affineCellPoissonPredictive sigma t.u t.w false) ≤
      t.u * t.alpha * ∑' h : Nat, if t.L < h then
        (2 * t.M * t.B) ^ h / (h.factorial : Real) else 0 at h
  have hbudget := affine_poisson_joint_tail_small n m d eps hn hd heps heps'
  change (t.Kstar : Real) * t.u * t.alpha *
    (∑' h : Nat, if t.L < h then (2 * t.M * t.B) ^ h /
      (h.factorial : Real) else 0) < 1 / 64 at hbudget
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))
  simpa only [mul_assoc] using hbudget

end CausalSmith.Stat.AnnotationRarearmFrontier
