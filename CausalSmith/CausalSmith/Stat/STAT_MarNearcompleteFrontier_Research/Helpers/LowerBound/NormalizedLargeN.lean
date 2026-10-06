module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.NormalizedTargetConcentration
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.NormalizedCountMixture
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.PairedPrefixTransfer
public import Causalean.Stat.Minimax.TotalVariation

/-! # Remaining large-sample normalized certificate -/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

-- @node: pairedPrior_minus_event_mass_eq
/-- A minus-prior event is the corresponding latent event under `thetaLaw`. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma pairedPrior_minus_event_mass_eq (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (E : ClassLaw d q → Prop) :
    priorEventMass d q (pairedPrior n d q hn hd hq).1 E =
      (thetaLaw n d q hn hd hq).toMeasure.real
        {θ | E (pairedClassLaw n d q (-1) hn hd hq (by norm_num) θ)} := by
  unfold priorEventMass
  change ((thetaLaw n d q hn hd hq).map
    (pairedClassLaw n d q (-1) hn hd hq (by norm_num))).toMeasure.real {P | E P} = _
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  simp only [measureReal_def]
  rw [Measure.map_apply]
  rfl
  · exact measurable_of_finite
      (pairedClassLaw n d q (-1) hn hd hq (by norm_num))
  · trivial

-- @node: pairedPrior_plus_event_mass_eq
/-- A plus-prior event is the corresponding latent event under `thetaLaw`. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma pairedPrior_plus_event_mass_eq (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (E : ClassLaw d q → Prop) :
    priorEventMass d q (pairedPrior n d q hn hd hq).2 E =
      (thetaLaw n d q hn hd hq).toMeasure.real
        {θ | E (pairedClassLaw n d q 1 hn hd hq (by norm_num) θ)} := by
  unfold priorEventMass
  change ((thetaLaw n d q hn hd hq).map
    (pairedClassLaw n d q 1 hn hd hq (by norm_num))).toMeasure.real {P | E P} = _
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  simp only [measureReal_def]
  rw [Measure.map_apply]
  rfl
  · exact measurable_of_finite
      (pairedClassLaw n d q 1 hn hd hq (by norm_num))
  · trivial

-- @node: pairedPrior_target_events_eventual
/-- The concentration certificate transfers to both target events of the legal
pushed-forward priors. [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β), [the specified input `hβ`](hyp:hβ). -/
lemma pairedPrior_target_events_eventual (β : ℝ) (hβ : 0 < β) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (q : ℝ), ∀ (hnN : N ≤ n) (hn : 1 ≤ n) (hd : 1 ≤ d)
        (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1),
        gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
        ∃ m0 : ℝ,
          1 - β ≤ priorEventMass d q (pairedPrior n d q hn hd hq).1
            (fun P => tau P.val ≤ m0 - c * gScale n d q) ∧
          1 - β ≤ priorEventMass d q (pairedPrior n d q hn hd hq).2
            (fun P => m0 + c * gScale n d q ≤ tau P.val) := by
  obtain ⟨N, hN2, c, hc, hgood⟩ := paired_target_good_event_eventual β hβ
  refine ⟨N, hN2, c, hc, ?_⟩
  intro n d q hnN hn hd hq hreg
  refine ⟨baseMean q, ?_, ?_⟩
  · rw [pairedPrior_minus_event_mass_eq n d q hn hd hq]
    apply (hgood n d q hnN hn hd hq hreg).trans
    refine measureReal_mono ?_ (by finiteness)
    intro θ hθ
    exact (pairedFullLaw_tau_separated n d q c hn hd hq θ hθ).1
  · rw [pairedPrior_plus_event_mass_eq n d q hn hd hq]
    apply (hgood n d q hnN hn hd hq hreg).trans
    refine measureReal_mono ?_ (by finiteness)
    intro θ hθ
    exact (pairedFullLaw_tau_separated n d q c hn hd hq θ hθ).2

-- @node: paired_count_to_predictive_tv_eventual
/-- Remaining parameter-independent prefix-transfer leaf. Eventually, transfer
from the random-scale count experiment costs at most half the requested TV
budget, uniformly over the exact normalized paired construction. [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β), [the specified input `hβ`](hyp:hβ). -/
lemma paired_count_to_predictive_tv_eventual (β : ℝ) (hβ : 0 < β) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (n d : ℕ) (q : ℝ), N ≤ n → ∀ (hn : 1 ≤ n) (hd : 1 ≤ d)
        (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1),
        gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
        Causalean.Stat.tvDist
          (priorPredictive n d q (pairedPrior n d q hn hd hq).1)
          (priorPredictive n d q (pairedPrior n d q hn hd hq).2) ≤
        Causalean.Stat.tvDist
          (mixedCountLaw n d q (-1) hn hd hq)
          (mixedCountLaw n d q 1 hn hd hq) + β / 2 := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (32 / β)
  refine ⟨max N₀ 2, le_max_right _ _, ?_⟩
  intro n d q hnN hn hd hq _hreg
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hnN
  have hnR : 32 / β < (n : ℝ) :=
    lt_of_lt_of_le hN₀ (by exact_mod_cast hn0)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hbudget : 16 / (n : ℝ) ≤ β / 2 := by
    apply (div_le_iff₀ hnpos).mpr
    have h := (div_lt_iff₀ hβ).mp hnR
    linarith
  exact (paired_predictive_tv_le_count_tv_add_inverse n d q hn hd hq).trans
    (add_le_add le_rfl hbudget)

-- @node: paired_predictive_tv_eventual
/-- The count-mixture comparison and random-scale prefix transfer imply the
eventual fixed-size predictive TV bound. [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β), [the specified input `hβ`](hyp:hβ). -/
lemma paired_predictive_tv_eventual (β : ℝ) (hβ : 0 < β) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (n d : ℕ) (q : ℝ), N ≤ n → ∀ (hn : 1 ≤ n) (hd : 1 ≤ d)
        (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1),
        gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
        Causalean.Stat.tvDist
          (priorPredictive n d q (pairedPrior n d q hn hd hq).1)
          (priorPredictive n d q (pairedPrior n d q hn hd hq).2) ≤ β := by
  obtain ⟨NC, hNC2, hcount⟩ := mixedCountLaw_tv_eventual β hβ
  obtain ⟨NT, hNT2, htransfer⟩ :=
    paired_count_to_predictive_tv_eventual β hβ
  refine ⟨max NC NT, le_max_of_le_left hNC2, ?_⟩
  intro n d q hnN hn hd hq hreg
  have hnC : NC ≤ n := le_trans (le_max_left _ _) hnN
  have hnT : NT ≤ n := le_trans (le_max_right _ _) hnN
  have hC := hcount n d q hnC hn hd hq hreg
  have hT := htransfer n d q hnT hn hd hq hreg
  linarith

end CausalSmith.Stat.MarNearcompleteFrontier
