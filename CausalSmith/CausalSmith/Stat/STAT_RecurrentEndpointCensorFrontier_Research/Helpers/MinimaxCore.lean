module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LowerDirections
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.MinimaxLowerRisk
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.MinimaxUpperRisk
public import Causalean.Stat.Minimax.LeCam
public import Causalean.Stat.Minimax.Pinsker

/-!
# Ungated minimax facts

The paper-owned upper and lower rate arguments and the vanishing horizon
retention statement are separated from the four cited literature gates.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: minimax_core
lemma minimax_core (c : ClassConstants)
    (hNonempty : ∃ P : SubjectLaw, ModelClass c P) :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ c₀ < C ∧
      (∀ n : ℕ, 3 ≤ n →
        c₀ * riskScale c n ≤ minimaxRisk c n ∧
        minimaxRisk c n ≤ C * riskScale c n ∧
        ∀ P : SubjectLaw, ModelClass c P →
          Causalean.Stat.sqRisk (sampleLaw P n) (observableEstimator c)
            (causalTarget P) ≤ C * riskScale c n) := by
  have hlower := minimaxRisk_lower_rate c hNonempty
  obtain ⟨c₀, hc₀, hlower⟩ := hlower
  let C := max (honestConstant c 1) c₀ + 1
  have hC : honestConstant c 1 ≤ C := by
    dsimp [C]
    linarith [le_max_left (honestConstant c 1) c₀]
  refine ⟨c₀, C, hc₀, ?_, ?_⟩
  · dsimp [C]
    linarith [le_max_right (honestConstant c 1) c₀]
  · intro n hn
    have hrate := (riskScale_pos c hn).le
    have hupper := minimaxRisk_le_honestConstant c n hn 1 (by norm_num)
    have hcompare := mul_le_mul_of_nonneg_right hC hrate
    refine ⟨hlower n hn, ?_, ?_⟩
    · simp only [one_mul] at hupper
      exact hupper.trans hcompare
    · intro P hP
      have hrisk := observableEstimator_sqRisk_le_honestConstant c P hP n hn
        1 (by norm_num)
      simp only [one_mul] at hrisk
      exact hrisk.trans hcompare

lemma zero_horizon_retention (c : ClassConstants) (P : SubjectLaw)
    (hModel : ModelClass c P) : ∀ a : Arm, retention P a 1 = 0 := by
  intro a
  have hga : 0 < P.g a := lt_of_lt_of_le c.gMin_pos (hModel.endpointCoefficientBounds a).1
  have htail : ∀ x : ℝ, 0 < x → x ≤ c.x0 →
      retention P a 1 ≤ (3 / 2 : ℝ) * P.g a * x ^ c.kappa := by
    intro x hx hx0
    have hden : 0 < P.g a * x ^ c.kappa := mul_pos hga (Real.rpow_pos_of_pos hx _)
    have hbound := hModel.endpointRetention a x hx hx0
    have hpow : x ^ c.rho ≤ c.x0 ^ c.rho :=
      Real.rpow_le_rpow hx.le hx0 c.rho_pos.le
    have hsmall : c.LG * x ^ c.rho ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left hpow c.LG_pos.le).trans hModel.tailEnvelopeSmall
    have hquot := (abs_le.mp hbound).2
    have hupper : retention P a (1 - x) ≤ (3 / 2 : ℝ) * P.g a * x ^ c.kappa := by
      have h := (div_le_iff₀ hden).mp (by linarith :
        retention P a (1 - x) / (P.g a * x ^ c.kappa) ≤ 3 / 2)
      nlinarith
    have hmono : retention P a 1 ≤ retention P a (1 - x) := by
      unfold retention
      apply measureReal_mono
      · intro z hz
        exact le_trans (ENNReal.ofReal_le_ofReal (by linarith : 1 - x ≤ (1 : ℝ))) hz
      · have hfin : P.latent Set.univ ≠ ⊤ := by rw [P.prob]; exact ENNReal.one_ne_top
        exact ne_top_of_le_ne_top hfin (measure_mono (Set.subset_univ _))
    exact hmono.trans hupper
  have hnonneg : 0 ≤ retention P a 1 := by
    unfold retention
    exact measureReal_nonneg
  apply le_antisymm _ hnonneg
  by_contra hnot
  have hpos : 0 < retention P a 1 := lt_of_not_ge hnot
  have htend : Filter.Tendsto
      (fun x : ℝ => (3 / 2 : ℝ) * P.g a * x ^ c.kappa)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hid : Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      Filter.tendsto_id.mono_left inf_le_left
    have hpow : Filter.Tendsto (fun x : ℝ => x ^ c.kappa)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa [Real.zero_rpow (ne_of_gt c.kappa_pos)] using
        hid.rpow_const (Or.inr c.kappa_pos.le)
    simpa [mul_assoc] using
      (tendsto_const_nhds.mul hpow : Filter.Tendsto
        (fun x : ℝ => ((3 / 2 : ℝ) * P.g a) * x ^ c.kappa)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (((3 / 2 : ℝ) * P.g a) * 0)))
  have hevent := htend.eventually_lt_const hpos
  have hx0event : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x ≤ c.x0 := by
    filter_upwards [eventually_mem_nhdsWithin,
      (Filter.tendsto_id.mono_left inf_le_left).eventually_lt_const c.x0_pos]
      with x hx hlt
    exact hlt.le
  obtain ⟨x, hxpos, hx0, hlt⟩ :=
    (eventually_mem_nhdsWithin.and (hx0event.and hevent)).exists
  exact (not_lt_of_ge (htail x hxpos hx0)) hlt

lemma zero_horizon_retention_inf (c : ClassConstants) (P : SubjectLaw)
    (hModel : ModelClass c P) :
    sInf {v : ℝ | ∃ a : Arm, ∃ t ∈ Set.Icc (0 : ℝ) 1,
      v = P.p a * retention P a t} = 0 := by
  let S : Set ℝ := {v | ∃ a : Arm, ∃ t ∈ Set.Icc (0 : ℝ) 1,
      v = P.p a * retention P a t}
  have hret := zero_horizon_retention c P hModel
  have hmem : (0 : ℝ) ∈ S := by
    refine ⟨false, 1, by norm_num, ?_⟩
    simp [hret]
  have hnonneg : ∀ v ∈ S, 0 ≤ v := by
    rintro v ⟨a, t, ht, rfl⟩
    have hp : 0 ≤ P.p a := le_trans c.pMin_pos.le (hModel.treatmentOverlap a)
    have hg : 0 ≤ retention P a t := by
      unfold retention
      exact measureReal_nonneg
    exact mul_nonneg hp hg
  exact le_antisymm (csInf_le (⟨0, hnonneg⟩ : BddBelow S) hmem)
    (Real.sInf_nonneg hnonneg)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
