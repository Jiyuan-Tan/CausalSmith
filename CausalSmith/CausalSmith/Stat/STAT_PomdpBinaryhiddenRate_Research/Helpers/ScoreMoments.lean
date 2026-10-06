module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Basic
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwWindowMoments

/-!
# Likelihood-weighted score moments

Kernel reward support gives almost-sure unit rewards. The finite-history
likelihood cancellation bounds first and second score moments, even when
behavior action cells vanish. These bounds do not require stationarity.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory
open scoped BigOperators

/-- The kernel reward support transfers to every sampled reward coordinate. [Under the listed formal conditions](hyp:hK), [the stated conclusion holds](goal).-/
-- @node: pomdp_reward_mem_Icc_ae
lemma pomdp_reward_mem_Icc_ae {T : Nat}
    (M : RawPomdpExperiment T 2 2) (hK : PomdpKernelLaw M) (t : Fin T) :
    ∀ᵐ tau ∂M.law, rewardAt t tau ∈ Set.Icc (0 : ℝ) 1 := by
  have hm : Measurable (histNextPair (nX := 2) (nH := 2) t) := by
    unfold histNextPair histView histActionPair histStateView
      curState actionAt rewardAt nextState
    fun_prop
  have hp : MeasurableSet {h : ActionHistoryView T 2 2 t × Step 2 2 |
      h.2.1 ∈ Set.Icc (0 : ℝ) 1} := by
    exact (measurable_fst.comp measurable_snd) measurableSet_Icc
  apply (ae_map_iff hm.aemeasurable hp).mp
  rw [hK.2.2 t]
  apply Measure.ae_compProd_of_ae_ae hp
  apply Filter.Eventually.of_forall
  intro h
  change ∀ᵐ q ∂M.K h.1.2 h.2, q.1 ∈ Set.Icc (0 : ℝ) 1
  let := hK.1 h.1.2 h.2
  exact (mem_ae_iff_prob_eq_one (measurable_fst measurableSet_Icc)).mpr (hK.2.1 _ _)

/-- Bounded kernel rewards are integrable under the trajectory probability law. [Under the listed formal conditions](hyp:hK), [the stated conclusion holds](goal).-/
-- @node: pomdp_reward_integrable
lemma pomdp_reward_integrable {T : Nat}
    (M : RawPomdpExperiment T 2 2) (hK : PomdpKernelLaw M) (t : Fin T) :
    Integrable (rewardAt t) M.law := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold rewardAt; fun_prop)
  filter_upwards [pomdp_reward_mem_Icc_ae M hK t] with tau ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2

/-- View the same trajectory experiment in the general finite POMDP carrier. -/
-- @node: finitePomdpView
def finitePomdpView {T : Nat} (M : RawPomdpExperiment T 2 2) :
    CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T 2 2 :=
  { K := M.K, b := M.b, e := M.e, init := M.init,
    law := M.law, law_isProbability := M.law_isProbability }

/-- The general finite-history law conditions follow from the binary law
conditions; the stronger kernel reward support supplies its reward premise. [Under the listed formal conditions](hyp:hK,hI,hO), [the stated conclusion holds](goal).-/
-- @node: finitePomdpView_laws
lemma finitePomdpView_laws {T : Nat} (M : RawPomdpExperiment T 2 2)
    (hK : PomdpKernelLaw M) (hI : SequentialIgnorability M)
    {L : ℝ} (hO : PolicyOverlap L M) :
    CausalSmith.Stat.PomdpLatentOverlapMinimax.PomdpKernelLaw (finitePomdpView M) ∧
    CausalSmith.Stat.PomdpLatentOverlapMinimax.SequentialIgnorability (finitePomdpView M) ∧
    CausalSmith.Stat.PomdpLatentOverlapMinimax.PolicyOverlap L (finitePomdpView M) ∧
    CausalSmith.Stat.PomdpLatentOverlapMinimax.BoundedReward (finitePomdpView M) := by
  refine ⟨⟨hK.1, hK.2.2⟩, hI, hO, ?_⟩
  intro t
  apply (mem_ae_iff_prob_eq_one (measurableSet_le
    (by unfold CausalSmith.Stat.PomdpLatentOverlapMinimax.rewardAt; fun_prop)
    measurable_const)).mp
  filter_upwards [pomdp_reward_mem_Icc_ae M hK t] with tau ht
  change |rewardAt t tau| ≤ 1
  rw [abs_of_nonneg ht.1]
  exact ht.2

/-- The observed score has the same definition in the general finite-history carrier. [the stated conclusion holds](goal).-/
-- @node: score_eq_phiwScore
lemma score_eq_phiwScore {T : Nat} (k : Nat) (b e : Policy 2)
    (w : ObsView T 2) (t : Fin T) :
    score k b e w t =
      CausalSmith.Stat.PomdpLatentOverlapMinimax.phiwScore k b e w t := rfl

/-- Likelihood cancellation bounds the absolute first moment by one. [Under the listed formal conditions](hyp:hK,hI,hO,hL,htk), [the stated conclusion holds](goal).-/
-- @node: score_abs_first_moment_le_one
lemma score_abs_first_moment_le_one {T k : Nat} {L : ℝ}
    (M : RawPomdpExperiment T 2 2) (hK : PomdpKernelLaw M)
    (hI : SequentialIgnorability M) (hO : PolicyOverlap L M) (hL : 1 ≤ L)
    (t : Fin T) (htk : k ≤ t.val) :
    (∫ tau, |score k M.b M.e (obsProj tau) t| ∂M.law) ≤ 1 := by
  obtain ⟨hK', hI', hO', hY'⟩ := finitePomdpView_laws M hK hI hO
  have h := CausalSmith.Stat.PomdpLatentOverlapMinimax.integral_abs_phiwScore_le_one
    hI' hO' hL hK' hY' t htk
  simp only [finitePomdpView] at h
  rw [CausalSmith.Stat.PomdpLatentOverlapMinimax.obsLaw,
    integral_map (μ := M.law)
      (f := fun w => |CausalSmith.Stat.PomdpLatentOverlapMinimax.phiwScore k M.b M.e w t|)
      CausalSmith.Stat.PomdpLatentOverlapMinimax.measurable_obsProj.aemeasurable
      (continuous_abs.measurable.comp
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.phiwScore_measurable
          (k := k) M.b M.e t)).aestronglyMeasurable] at h
  exact h

/-- Squaring a score costs one overlap factor per action, since the other
likelihood-ratio product integrates to one under sequential randomization. [Under the listed formal conditions](hyp:hK,hI,hO,hL,htk), [the stated conclusion holds](goal).-/
-- @node: score_second_moment_le
lemma score_second_moment_le {T k : Nat} {L : ℝ}
    (M : RawPomdpExperiment T 2 2) (hK : PomdpKernelLaw M)
    (hI : SequentialIgnorability M) (hO : PolicyOverlap L M) (hL : 1 ≤ L)
    (t : Fin T) (htk : k ≤ t.val) :
    (∫ tau, (score k M.b M.e (obsProj tau) t) ^ 2 ∂M.law) ≤ L ^ (k + 1) := by
  obtain ⟨hK', hI', hO', hY'⟩ := finitePomdpView_laws M hK hI hO
  have h := CausalSmith.Stat.PomdpLatentOverlapMinimax.integral_sq_phiwScore_le
    hI' hO' hL hK' hY' t htk
  simp only [finitePomdpView] at h
  rw [CausalSmith.Stat.PomdpLatentOverlapMinimax.obsLaw,
    integral_map CausalSmith.Stat.PomdpLatentOverlapMinimax.measurable_obsProj.aemeasurable
      ((CausalSmith.Stat.PomdpLatentOverlapMinimax.phiwScore_measurable
        (k := k) M.b M.e t).pow_const 2).aestronglyMeasurable] at h
  exact h

end CausalSmith.Stat.PomdpBinaryhiddenRate
