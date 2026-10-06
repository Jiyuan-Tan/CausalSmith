module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerInformationScales
public import Mathlib.Topology.Order.Compact

/-! Sample-size-independent separation constants for the explicit lower programme. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- The explicit interaction constant is positive. -/
-- @node: cInter_pos
lemma cInter_pos (κ : Params) : 0 < cInter κ := by
  have hc : 0 < lowerC κ := by unfold lowerC; positivity
  unfold cInter lowerP0
  positivity

/-- Real powers of the optimized spacing give exactly the interaction sample-size power. -/
-- @node: lower_separation_scale_identity
lemma lower_separation_scale_identity (κ : Params) (n : ℕ) (hn : 2 ≤ n) :
    lowerA κ n*lowerB κ n =
      lowerC κ^sumReg κ*(n : ℝ)^(-rInter κ)/(1024 : ℝ)^2 := by
  have he := lowerEll_pos κ n (by omega)
  have hc : 0 < lowerC κ := by unfold lowerC; positivity
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  unfold lowerA lowerB
  rw [div_mul_div_comm, ← Real.rpow_add he]
  change lowerEll κ n^sumReg κ / (1024*1024) = _
  rw [lowerEll, Real.mul_rpow hc.le (Real.rpow_nonneg hn0.le _),
    ← Real.rpow_mul hn0.le]
  rw [show (-2/lowerDenom κ)*sumReg κ = -rInter κ by
    unfold rInter lowerDenom; ring]
  norm_num

/-- At the target the cutoff equals one, so the deterministic effect separation is exact. -/
-- @node: lower_effect_separation
lemma lower_effect_separation (κ : Params) (n : ℕ) (hn : 2 ≤ n) :
    |lowerEffect κ n true xstar-lowerEffect κ n false xstar| =
      2*lowerC κ^sumReg κ*(n : ℝ)^(-rInter κ)/
        ((1024 : ℝ)^2*lowerP0*(1-lowerP0)) := by
  have he := lowerEll_pos κ n (by omega)
  have ha : 0 < lowerA κ n := by unfold lowerA; positivity
  have hb : 0 < lowerB κ n := by unfold lowerB; positivity
  have hcut : lowerSquare κ n xstar = 1 := by
    norm_num [lowerSquare, lowerCutoff, xstar]
  have hid : lowerEffect κ n true xstar-lowerEffect κ n false xstar =
      -(2*lowerA κ n*lowerB κ n/(lowerP0*(1-lowerP0))) := by
    simp only [lowerEffect, hcut, sign, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [hid, abs_neg, abs_of_pos (by unfold lowerP0; positivity)]
  rw [show 2*lowerA κ n*lowerB κ n = 2*(lowerA κ n*lowerB κ n) by ring,
    lower_separation_scale_identity κ n hn]
  norm_num [lowerP0]
  ring

/-- The testing constant is three sixteenths of the exact effect-separation coefficient. -/
-- @node: cInter_separation_identity
lemma cInter_separation_identity (κ : Params) (n : ℕ) (hn : 2 ≤ n) :
    cInter κ*(n : ℝ)^(-rInter κ) =
      (3/16 : ℝ)*|lowerEffect κ n true xstar-lowerEffect κ n false xstar| := by
  rw [lower_effect_separation κ n hn]
  unfold cInter
  ring

/-- The original lower laws retain exact uniform design and the same deterministic smooth effect. -/
-- @node: lower_prior_member_properties
lemma lower_prior_member_properties (κ : Params) (n : ℕ) (hκ : κ.Valid)
    (hb : boundary κ ≤ 1) (hn : 2 ≤ n) (ε : Bool) (v : Signs κ n) :
    InModel κ (lowerPriorLaw κ n ε v) ∧ UniformDesign (lowerPriorLaw κ n ε v) ∧
    (lowerPriorLaw κ n ε v).tau = lowerEffect κ n ε ∧
    holderBall κ.γ (lowerPriorLaw κ n ε v).tau := by
  have hm := lower_prior_membership κ n hκ hb hn ε v
  exact ⟨hm.1, hm.1.uniform, hm.2, hm.1.effectHolder⟩

/-- The parameter coordinates are continuous for the specified induced product topology. -/
-- @node: lower_parameter_coordinates_continuous
lemma lower_parameter_coordinates_continuous :
    Continuous (fun κ : Params => κ.p) ∧ Continuous (fun κ : Params => κ.α) ∧
    Continuous (fun κ : Params => κ.β) ∧ Continuous (fun κ : Params => κ.γ) := by
  have h : Continuous (fun κ : Params => (κ.p,κ.α,κ.β,κ.γ)) := continuous_induced_dom
  exact ⟨h.fst,h.snd.fst,h.snd.snd.fst,h.snd.snd.snd⟩

/-- The explicit interaction constant is continuous throughout the valid parameter domain. -/
-- @node: cInter_continuousOn
lemma cInter_continuousOn (K : Set Params) (hK : K ⊆ {κ | κ.Valid}) :
    ContinuousOn cInter K := by
  obtain ⟨hp,ha,hb,hg⟩ := lower_parameter_coordinates_continuous
  have hs : ContinuousOn sumReg K := ha.continuousOn.add hb.continuousOn
  have hsne : ∀ κ ∈ K, sumReg κ ≠ 0 := by
    intro κ hκ
    exact (add_pos (hK hκ).2.1.1 (hK hκ).2.2.1.1).ne'
  have hlc : ContinuousOn lowerC K := by
    unfold lowerC
    apply continuousOn_const.inf
    apply continuousOn_const.rpow ((hg.continuousOn.neg).div hs hsne)
    intro κ hκ
    left
    norm_num
  have hlpos : ∀ κ ∈ K, lowerC κ ≠ 0 := by
    intro κ hκ
    apply ne_of_gt
    unfold lowerC
    positivity
  have hpow := hlc.rpow hs (fun κ hκ => Or.inl (hlpos κ hκ))
  unfold cInter
  exact ((continuousOn_const.mul continuousOn_const).mul hpow).div_const _

/-- Compact valid parameter sets admit one strictly positive common interaction constant. -/
-- @node: cInter_compact_lower_bound
lemma cInter_compact_lower_bound (K : Set Params) (hK : IsCompact K)
    (hsub : K ⊆ {κ | κ.Valid ∧ boundary κ ≤ 1}) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ κ ∈ K, c0 ≤ cInter κ := by
  by_cases hne : K.Nonempty
  · obtain ⟨κ,hκ,hmin⟩ := hK.exists_isMinOn hne
      (cInter_continuousOn K (fun κ hk => (hsub hk).1))
    exact ⟨cInter κ,cInter_pos κ,hmin⟩
  · exact ⟨1,by norm_num,fun κ hk => (hne ⟨κ,hk⟩).elim⟩

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
