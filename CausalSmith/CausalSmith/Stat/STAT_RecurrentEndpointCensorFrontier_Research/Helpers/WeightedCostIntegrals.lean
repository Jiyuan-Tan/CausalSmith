module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LowerRateBounds
public import Causalean.Mathlib.Analysis.SpecialFunctions.PowerIntegral

/-!
# Weighted Poisson-cost integrals for the lower-bound directions

This module combines the terminal retention envelope with the compact support
of the endpoint and critical perturbations.  It supplies the deterministic
integral estimates that precede the sample-size cancellations in
`LowerRateBounds`.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The survival-retention weighted local Poisson cost of an additive
perturbation of a constant recurrence intensity. -/
@[no_expose]
noncomputable def weightedPoissonCost (P : SubjectLaw) (a : Arm) (lambda0 : ℝ)
    (direction : ℝ → ℝ) (t : ℝ) : ℝ :=
  survival P a t * retention P a t *
    ((lambda0 + direction t) *
        Real.log ((lambda0 + direction t) / lambda0) -
      (lambda0 + direction t) + lambda0)

@[simp] lemma weightedPoissonCost_apply (P : SubjectLaw) (a : Arm)
    (lambda0 : ℝ) (direction : ℝ → ℝ) (t : ℝ) :
    weightedPoissonCost P a lambda0 direction t =
      survival P a t * retention P a t *
        ((lambda0 + direction t) *
            Real.log ((lambda0 + direction t) / lambda0) -
          (lambda0 + direction t) + lambda0) := by
  rfl

/-- The endpoint perturbation's weighted Poisson cost has the exact
`h^(2β+κ+1)` envelope. -/
lemma endpoint_weightedPoissonCost_integral_le
    (c : ClassConstants) (reference : SubjectLaw)
    (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hModel : ModelClass c (SubjectLaw.baseline reference lambda0 d0 hd0))
    (cut : CutoffData c) {u h : ℝ}
    (hlambda0 : 0 < lambda0) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hhx0 : h ≤ c.x0)
    (hadd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < lambda0 + endpointDirection c cut u h t)
    (hint : IntervalIntegrable
      (weightedPoissonCost (SubjectLaw.baseline reference lambda0 d0 hd0)
        true lambda0 (endpointDirection c cut u h)) volume 0 1) :
    ∫ t in (0 : ℝ)..1,
        weightedPoissonCost
          (SubjectLaw.baseline reference lambda0 d0 hd0) true lambda0
          (endpointDirection c cut u h) t ≤
      ((3 / 2 : ℝ) * c.gMax *
          ((|u| * endpointBumpBound c cut) ^ 2 / lambda0)) *
        h ^ (2 * c.beta + c.kappa + 1) := by
  let Pbase := SubjectLaw.baseline reference lambda0 d0 hd0
  let f := weightedPoissonCost Pbase true lambda0
    (endpointDirection c cut u h)
  let K := (3 / 2 : ℝ) * c.gMax *
    ((|u| * endpointBumpBound c cut) ^ 2 / lambda0)
  have hmid : 1 - h ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc]
    constructor <;> linarith
  have hsplit := (IntervalIntegrable.trans_iff hmid).mp hint
  have hleftzero : (∫ t in (0 : ℝ)..(1 - h), f t) = 0 := by
    rw [show (∫ t in (0 : ℝ)..(1 - h), f t) =
        ∫ _t in (0 : ℝ)..(1 - h), (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) (1 - h) := by
        simpa [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ 1 - h)] using ht
      have hscaled : 1 ≤ (1 - t) / h := by
        exact (le_div_iff₀ hh0).2 (by linarith [ht'.2])
      have hdir : endpointDirection c cut u h t = 0 :=
        endpointDirection_eq_zero_of_not_mem c cut
          (by intro hm; exact (not_lt_of_ge hscaled) hm.2)
      simp [f, weightedPoissonCost, hdir]]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals hsplit.1 hsplit.2,
    hleftzero, zero_add]
  have hK0 : 0 ≤ K := by
    dsimp [K]
    have hgmax0 : 0 ≤ c.gMax :=
      (lt_trans c.gMin_pos c.gMin_lt).le
    positivity
  have hconst : IntervalIntegrable (fun _ : ℝ => K * h ^
      (2 * c.beta + c.kappa)) volume (1 - h) 1 :=
    intervalIntegrable_const
  calc
    (∫ t in (1 - h)..1, f t) ≤
        ∫ _t in (1 - h)..1, K * h ^ (2 * c.beta + c.kappa) := by
      apply intervalIntegral.integral_mono_on (by linarith) hsplit.2 hconst
      intro t ht
      by_cases hx0 : 1 - t = 0
      · have hdir : endpointDirection c cut u h t = 0 := by
          apply endpointDirection_eq_zero_of_not_mem c cut
          simp [hx0]
        dsimp [f, weightedPoissonCost]
        simp [hdir]
        exact mul_nonneg hK0 (Real.rpow_nonneg hh0.le _)
      · have hx : 0 < 1 - t :=
          lt_of_le_of_ne (by linarith [ht.2]) (Ne.symm hx0)
        have hxh : 1 - t ≤ h := by linarith [ht.1]
        have hxx0 : 1 - t ≤ c.x0 := hxh.trans hhx0
        have hs := SubjectLaw.baseline_survival_mem_unitInterval
          reference lambda0 d0 hd0 (a := true) (t := t) (by linarith [ht.1, hh1])
        have hs1 : survival Pbase true t ≤ 1 := by
          simpa only [Pbase] using hs.2
        have hr0 : 0 ≤ retention Pbase true t := measureReal_nonneg
        have hr := retention_le_three_halves_gMax_rpow c Pbase hModel true
          hx hxx0
        have hr' : retention Pbase true t ≤
            (3 / 2 : ℝ) * c.gMax * (1 - t) ^ c.kappa := by
          simpa only [sub_sub_cancel] using hr
        have hcost0 : 0 ≤
            (lambda0 + endpointDirection c cut u h t) *
                Real.log ((lambda0 + endpointDirection c cut u h t) / lambda0) -
              (lambda0 + endpointDirection c cut u h t) + lambda0 :=
          poissonIntensityCost_nonneg _ lambda0 (hadd t ⟨by linarith [ht.1, hh1], ht.2⟩).le
            hlambda0
        have hcost := endpointDirection_poissonCost_le c cut hlambda0 hh0.le
          (hadd t ⟨by linarith [ht.1, hh1], ht.2⟩)
        have hxpow : (1 - t) ^ c.kappa ≤ h ^ c.kappa :=
          Real.rpow_le_rpow hx.le hxh c.kappa_pos.le
        have hgmax0 : 0 ≤ c.gMax :=
          (lt_trans c.gMin_pos c.gMin_lt).le
        have htailConst0 : 0 ≤ (3 / 2 : ℝ) * c.gMax := by positivity
        have htail0 : 0 ≤
            (3 / 2 : ℝ) * c.gMax * (1 - t) ^ c.kappa :=
          mul_nonneg htailConst0 (Real.rpow_nonneg hx.le _)
        have htailh0 : 0 ≤
            (3 / 2 : ℝ) * c.gMax * h ^ c.kappa :=
          mul_nonneg htailConst0 (Real.rpow_nonneg hh0.le _)
        dsimp [f, weightedPoissonCost]
        calc
          survival Pbase true t * retention Pbase true t *
              ((lambda0 + endpointDirection c cut u h t) *
                  Real.log ((lambda0 + endpointDirection c cut u h t) / lambda0) -
                (lambda0 + endpointDirection c cut u h t) + lambda0)
              ≤ retention Pbase true t *
                ((lambda0 + endpointDirection c cut u h t) *
                    Real.log ((lambda0 + endpointDirection c cut u h t) / lambda0) -
                  (lambda0 + endpointDirection c cut u h t) + lambda0) := by
                calc
                  survival Pbase true t * retention Pbase true t *
                      ((lambda0 + endpointDirection c cut u h t) *
                          Real.log ((lambda0 + endpointDirection c cut u h t) / lambda0) -
                        (lambda0 + endpointDirection c cut u h t) + lambda0) =
                    survival Pbase true t *
                      (retention Pbase true t *
                        ((lambda0 + endpointDirection c cut u h t) *
                            Real.log ((lambda0 + endpointDirection c cut u h t) / lambda0) -
                          (lambda0 + endpointDirection c cut u h t) + lambda0)) := by ring
                  _ ≤ 1 *
                      (retention Pbase true t *
                        ((lambda0 + endpointDirection c cut u h t) *
                            Real.log ((lambda0 + endpointDirection c cut u h t) / lambda0) -
                          (lambda0 + endpointDirection c cut u h t) + lambda0)) :=
                    mul_le_mul_of_nonneg_right hs1 (mul_nonneg hr0 hcost0)
                  _ = retention Pbase true t *
                      ((lambda0 + endpointDirection c cut u h t) *
                          Real.log ((lambda0 + endpointDirection c cut u h t) / lambda0) -
                        (lambda0 + endpointDirection c cut u h t) + lambda0) := by ring
          _ ≤ ((3 / 2 : ℝ) * c.gMax * (1 - t) ^ c.kappa) *
                (((|u| * endpointBumpBound c cut) ^ 2 * h ^ (2 * c.beta)) /
                  lambda0) := by
                exact mul_le_mul hr' hcost hcost0 htail0
          _ ≤ ((3 / 2 : ℝ) * c.gMax * h ^ c.kappa) *
                (((|u| * endpointBumpBound c cut) ^ 2 * h ^ (2 * c.beta)) /
                  lambda0) := by
                apply mul_le_mul_of_nonneg_right
                · exact mul_le_mul_of_nonneg_left hxpow htailConst0
                · positivity
          _ = K * h ^ (2 * c.beta + c.kappa) := by
                dsimp [K]
                rw [Real.rpow_add hh0]
                ring
    _ = K * h ^ (2 * c.beta + c.kappa) * h := by
      rw [intervalIntegral.integral_const]
      ring
    _ = K * h ^ (2 * c.beta + c.kappa + 1) := by
      rw [show 2 * c.beta + c.kappa + 1 =
          (2 * c.beta + c.kappa) + 1 by ring]
      have hp := Real.rpow_add hh0 (2 * c.beta + c.kappa) 1
      calc
        K * h ^ (2 * c.beta + c.kappa) * h =
            K * (h ^ (2 * c.beta + c.kappa) * h ^ (1 : ℝ)) := by
              rw [Real.rpow_one]
              ring
        _ = K * h ^ ((2 * c.beta + c.kappa) + 1) := by
              rw [hp]
    _ = ((3 / 2 : ℝ) * c.gMax *
          ((|u| * endpointBumpBound c cut) ^ 2 / lambda0)) *
        h ^ (2 * c.beta + c.kappa + 1) := rfl

/-- Before replacing distance to the endpoint by the bandwidth, the critical
direction has an inverse-distance envelope. -/
lemma criticalDirection_abs_le_distance
    (c : ClassConstants) (cut : CutoffData c)
    {u Cchi Cpsi : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hCchi : 0 ≤ Cchi) (hCpsi : 0 ≤ Cpsi)
    (hchi : ∀ y ∈ Set.Ici (0 : ℝ), |cut.chi y| ≤ Cchi)
    (hpsi : ∀ x ∈ Set.Icc (0 : ℝ) 1, |cut.psi x| ≤ Cpsi)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht1 : t < 1) :
    |criticalDirection c cut u n t| ≤
      |u| * Cchi * Cpsi /
        (Real.sqrt ((n : ℝ) * Real.log n) * (1 - t)) := by
  have hz : 0 < (n : ℝ) * Real.log n :=
    mul_pos (by exact_mod_cast (show 0 < n by omega))
      (Real.log_pos (by exact_mod_cast hn))
  have hsqrt : 0 < Real.sqrt ((n : ℝ) * Real.log n) := Real.sqrt_pos.2 hz
  have hx : 0 < 1 - t := by linarith
  have hscaled : 0 ≤ (1 - t) / criticalBandwidth c n :=
    critical_scaled_nonneg c hn ht
  have hchi' := hchi ((1 - t) / criticalBandwidth c n) hscaled
  have hpsi' := hpsi (1 - t) ⟨hx.le, by linarith [ht.1]⟩
  rw [criticalDirection]
  simp only [hx.ne', ↓reduceIte, abs_div, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hx]
  rw [show |u| / Real.sqrt ((n : ℝ) * Real.log n) *
        |cut.chi ((1 - t) / criticalBandwidth c n)| * |cut.psi (1 - t)| /
          (1 - t) =
      (|u| * |cut.chi ((1 - t) / criticalBandwidth c n)| *
        |cut.psi (1 - t)|) /
          (Real.sqrt ((n : ℝ) * Real.log n) * (1 - t)) by field_simp]
  exact div_le_div_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hchi' (abs_nonneg u)) hpsi'
      (abs_nonneg _) (mul_nonneg (abs_nonneg u) hCchi))
    (mul_nonneg hsqrt.le hx.le)

/-- The inverse-distance integral over the active critical band is bounded by
the negative logarithm of the critical bandwidth. -/
lemma critical_inverse_distance_integral_le
    (c : ClassConstants) {n : ℕ} (hn : 2 ≤ n)
    (hhx0 : criticalBandwidth c n ≤ c.x0) :
    (∫ t in (1 - c.x0)..(1 - criticalBandwidth c n), (1 - t)⁻¹) ≤
      -Real.log (criticalBandwidth c n) := by
  have hh : 0 < criticalBandwidth c n := criticalBandwidth_pos c hn
  have hx0 : 0 < c.x0 := c.x0_pos
  have hx01 : c.x0 ≤ 1 := c.x0_le.trans (by norm_num)
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) 1]
  norm_num only [sub_sub_cancel, sub_sub]
  rw [integral_inv_of_pos hh hx0]
  rw [Real.log_div hx0.ne' hh.ne']
  have hlogx0 : Real.log c.x0 ≤ 0 := Real.log_nonpos hx0.le hx01
  linarith

/-- At the boundary retention exponent `κ = 1`, the critical perturbation's
weighted Poisson cost has the logarithmic envelope required by the critical
sample-size cancellation. -/
lemma critical_weightedPoissonCost_integral_le
    (c : ClassConstants) (reference : SubjectLaw)
    (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (hModel : ModelClass c (SubjectLaw.baseline reference lambda0 d0 hd0))
    (cut : CutoffData c) {u Cchi Cpsi : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hkappa : c.kappa = 1)
    (hhx0 : criticalBandwidth c n ≤ c.x0)
    (hlambda0 : 0 < lambda0) (hCchi : 0 ≤ Cchi) (hCpsi : 0 ≤ Cpsi)
    (hchi : ∀ y ∈ Set.Ici (0 : ℝ), |cut.chi y| ≤ Cchi)
    (hpsi : ∀ x ∈ Set.Icc (0 : ℝ) 1, |cut.psi x| ≤ Cpsi)
    (hadd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < lambda0 + criticalDirection c cut u n t)
    (hint : IntervalIntegrable
      (weightedPoissonCost (SubjectLaw.baseline reference lambda0 d0 hd0)
        true lambda0 (criticalDirection c cut u n)) volume 0 1) :
    ∫ t in (0 : ℝ)..1,
        weightedPoissonCost
          (SubjectLaw.baseline reference lambda0 d0 hd0) true lambda0
          (criticalDirection c cut u n) t ≤
      ((3 / 2 : ℝ) * c.gMax * (|u| * Cchi * Cpsi) ^ 2 / lambda0) /
          ((n : ℝ) * Real.log n) *
        (-Real.log (criticalBandwidth c n)) := by
  let Pbase := SubjectLaw.baseline reference lambda0 d0 hd0
  let f := weightedPoissonCost Pbase true lambda0
    (criticalDirection c cut u n)
  let h := criticalBandwidth c n
  let z := (n : ℝ) * Real.log n
  let A := (3 / 2 : ℝ) * c.gMax * (|u| * Cchi * Cpsi) ^ 2 / lambda0
  have hh : 0 < h := criticalBandwidth_pos c hn
  have hz : 0 < z := mul_pos (by exact_mod_cast (show 0 < n by omega))
    (Real.log_pos (by exact_mod_cast hn))
  have hx01 : c.x0 ≤ 1 := c.x0_le.trans (by norm_num)
  have hL : 1 - c.x0 ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc]
    constructor <;> linarith [c.x0_pos]
  have hR : 1 - h ∈ Set.uIcc (1 - c.x0) 1 := by
    rw [Set.uIcc_of_le (by linarith : 1 - c.x0 ≤ (1 : ℝ)), Set.mem_Icc]
    constructor <;> linarith
  have hsplitL := (IntervalIntegrable.trans_iff hL).mp hint
  have hsplitR := (IntervalIntegrable.trans_iff hR).mp hsplitL.2
  have hleftzero : (∫ t in (0 : ℝ)..(1 - c.x0), f t) = 0 := by
    rw [show (∫ t in (0 : ℝ)..(1 - c.x0), f t) =
        ∫ _t in (0 : ℝ)..(1 - c.x0), (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) (1 - c.x0) := by
        simpa [Set.uIcc_of_le (by linarith [hx01] : (0 : ℝ) ≤ 1 - c.x0)] using ht
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht'.1, ht'.2.trans (by linarith)⟩
      have hdir : criticalDirection c cut u n t = 0 := by
        by_contra hne
        have hb := criticalDirection_ne_zero_imp_band c cut hn ht01 hne
        exact (not_lt_of_ge (by linarith [ht'.2] : c.x0 ≤ 1 - t)) hb.2
      simp [f, weightedPoissonCost, hdir]]
    simp
  have hrightzero : (∫ t in (1 - h)..1, f t) = 0 := by
    rw [show (∫ t in (1 - h)..1, f t) =
        ∫ _t in (1 - h)..1, (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (1 - h) 1 := by
        simpa [Set.uIcc_of_le (by linarith : 1 - h ≤ (1 : ℝ))] using ht
      have hhx0' : h ≤ c.x0 := by simpa only [h] using hhx0
      have hh1 : h ≤ 1 := hhx0'.trans hx01
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [hh1, ht'.1], ht'.2⟩
      have hdir : criticalDirection c cut u n t = 0 :=
        criticalDirection_eq_zero_of_endpoint_band c cut hn ht01
          (by simpa only [h] using (show 1 - t ≤ h by linarith [ht'.1]))
      dsimp [f, weightedPoissonCost]
      simp [hdir]]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals hsplitL.1 hsplitL.2,
    hleftzero, zero_add,
    ← intervalIntegral.integral_add_adjacent_intervals hsplitR.1 hsplitR.2,
    hrightzero, add_zero]
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have hgmax0 : 0 ≤ c.gMax := (lt_trans c.gMin_pos c.gMin_lt).le
    positivity
  have hinv : IntervalIntegrable (fun t : ℝ => A / z * (1 - t)⁻¹)
      volume (1 - c.x0) (1 - h) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    apply ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id)
    intro t ht
    have ht' : t ∈ Set.Icc (1 - c.x0) (1 - h) := by
      simpa [Set.uIcc_of_le (by linarith : 1 - c.x0 ≤ 1 - h)] using ht
    exact ne_of_gt (by linarith [ht'.2, hh] : 0 < 1 - t)
  calc
    (∫ t in (1 - c.x0)..(1 - h), f t) ≤
        ∫ t in (1 - c.x0)..(1 - h), A / z * (1 - t)⁻¹ := by
      apply intervalIntegral.integral_mono_on (by linarith) hsplitR.1 hinv
      intro t ht
      have hx : 0 < 1 - t := by linarith [ht.2, hh]
      have hxx0 : 1 - t ≤ c.x0 := by linarith [ht.1]
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · linarith [ht.1, hx01]
        · linarith
      have hs := SubjectLaw.baseline_survival_mem_unitInterval
        reference lambda0 d0 hd0 (a := true) (t := t) ht01.1
      have hs1 : survival Pbase true t ≤ 1 := by simpa only [Pbase] using hs.2
      have hr0 : 0 ≤ retention Pbase true t := measureReal_nonneg
      have hrRaw := retention_le_three_halves_gMax_rpow c Pbase hModel true hx hxx0
      have hr : retention Pbase true t ≤ (3 / 2 : ℝ) * c.gMax * (1 - t) := by
        simpa only [sub_sub_cancel, hkappa, Real.rpow_one] using hrRaw
      have hcost0 : 0 ≤
          (lambda0 + criticalDirection c cut u n t) *
              Real.log ((lambda0 + criticalDirection c cut u n t) / lambda0) -
            (lambda0 + criticalDirection c cut u n t) + lambda0 :=
        poissonIntensityCost_nonneg _ lambda0 (hadd t ht01).le hlambda0
      have hquad := poissonIntensityCost_add_le_sq_div hlambda0 (hadd t ht01)
      have habs : |criticalDirection c cut u n t| ≤
          |u| * Cchi * Cpsi / (Real.sqrt z * (1 - t)) := by
        simpa only [z] using
          criticalDirection_abs_le_distance c cut hn hCchi hCpsi
            hchi hpsi ht01 (by linarith)
      have hdenpos : 0 < Real.sqrt z * (1 - t) :=
        mul_pos (Real.sqrt_pos.2 hz) hx
      have hU0 : 0 ≤ |u| * Cchi * Cpsi :=
        mul_nonneg (mul_nonneg (abs_nonneg u) hCchi) hCpsi
      have hd2 : (criticalDirection c cut u n t) ^ 2 ≤
          ((|u| * Cchi * Cpsi) /
            (Real.sqrt z * (1 - t))) ^ 2 := by
        rw [← sq_abs (criticalDirection c cut u n t)]
        exact (sq_le_sq₀ (abs_nonneg _) (div_nonneg hU0 hdenpos.le)).2 habs
      have hcost :
          (lambda0 + criticalDirection c cut u n t) *
                Real.log ((lambda0 + criticalDirection c cut u n t) / lambda0) -
              (lambda0 + criticalDirection c cut u n t) + lambda0 ≤
            (((|u| * Cchi * Cpsi) /
              (Real.sqrt z * (1 - t))) ^ 2) / lambda0 :=
        hquad.trans (div_le_div_of_nonneg_right hd2 hlambda0.le)
      have htail0 : 0 ≤ (3 / 2 : ℝ) * c.gMax * (1 - t) := by
        have hgmax0 : 0 ≤ c.gMax := (lt_trans c.gMin_pos c.gMin_lt).le
        positivity
      have halgebra :
          ((3 / 2 : ℝ) * c.gMax * (1 - t)) *
              ((((|u| * Cchi * Cpsi) /
                (Real.sqrt z * (1 - t))) ^ 2) / lambda0) =
            A / z * (1 - t)⁻¹ := by
        dsimp [A]
        have hsqrt_ne : Real.sqrt z ≠ 0 := (Real.sqrt_pos.2 hz).ne'
        field_simp [hsqrt_ne, hx.ne', hz.ne', hlambda0.ne']
        rw [Real.sq_sqrt hz.le]
      dsimp [f, weightedPoissonCost]
      calc
        survival Pbase true t * retention Pbase true t *
              ((lambda0 + criticalDirection c cut u n t) *
                  Real.log ((lambda0 + criticalDirection c cut u n t) / lambda0) -
                (lambda0 + criticalDirection c cut u n t) + lambda0) ≤
            retention Pbase true t *
              ((lambda0 + criticalDirection c cut u n t) *
                  Real.log ((lambda0 + criticalDirection c cut u n t) / lambda0) -
                (lambda0 + criticalDirection c cut u n t) + lambda0) := by
          calc
            _ = survival Pbase true t *
                (retention Pbase true t *
                  ((lambda0 + criticalDirection c cut u n t) *
                      Real.log ((lambda0 + criticalDirection c cut u n t) / lambda0) -
                    (lambda0 + criticalDirection c cut u n t) + lambda0)) := by ring
            _ ≤ 1 * (retention Pbase true t *
                  ((lambda0 + criticalDirection c cut u n t) *
                      Real.log ((lambda0 + criticalDirection c cut u n t) / lambda0) -
                    (lambda0 + criticalDirection c cut u n t) + lambda0)) :=
              mul_le_mul_of_nonneg_right hs1 (mul_nonneg hr0 hcost0)
            _ = _ := by ring
        _ ≤ ((3 / 2 : ℝ) * c.gMax * (1 - t)) *
              ((((|u| * Cchi * Cpsi) /
                (Real.sqrt z * (1 - t))) ^ 2) / lambda0) :=
          mul_le_mul hr hcost hcost0 htail0
        _ = A / z * (1 - t)⁻¹ := halgebra
    _ = A / z *
        (∫ t in (1 - c.x0)..(1 - h), (1 - t)⁻¹) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ A / z * (-Real.log h) := by
      apply mul_le_mul_of_nonneg_left
      · exact critical_inverse_distance_integral_le c hn hhx0
      · exact div_nonneg hA0 hz.le
    _ = ((3 / 2 : ℝ) * c.gMax * (|u| * Cchi * Cpsi) ^ 2 / lambda0) /
          ((n : ℝ) * Real.log n) *
        (-Real.log (criticalBandwidth c n)) := rfl

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
