module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveLaw
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveLocalization

/-! # Finite-row regularization for the adaptive pilot -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open Filter
open scoped Topology BigOperators

/-- For [the supplied quantities and conditions](hyp:m,n), the [adaptive pilot size](goal) is the mathematical object specified below. -/
def adaptivePilotSize (m : ℕ → ℕ) (n : ℕ) : ℕ :=
  min (m n) n

/-- Under [the supplied quantities and conditions](hyp:m,n), [the adaptive pilot size le assertion](goal) holds. -/
lemma adaptivePilotSize_le (m : ℕ → ℕ) (n : ℕ) :
    adaptivePilotSize m n ≤ n := by
  exact min_le_right _ _

/-- Under [the supplied quantities and conditions](hyp:m,hsub), [the adaptive pilot size eq assertion](goal) holds. For [the displayed quantities and conditions](hyp:hn), these specify the stated inputs. -/
lemma adaptivePilotSize_eq (m : ℕ → ℕ) (hsub : PilotSublinear m)
    {n : ℕ} (hn : 2 ≤ n) : adaptivePilotSize m n = m n := by
  exact min_eq_left (hsub.2 n hn).2.le

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under [the supplied quantities and conditions](hyp:m), [the adaptive pilot size tendsto at top assertion](goal) holds. For [the displayed quantities and conditions](hyp:hdiv,hsub), these specify the stated inputs. -/
lemma adaptivePilotSize_tendsto_atTop (m : ℕ → ℕ)
    (hdiv : PilotDiverges m) (hsub : PilotSublinear m) :
    Tendsto (adaptivePilotSize m) atTop atTop := by
  apply hdiv.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (adaptivePilotSize_eq m hsub hn).symm

/-- Under [the supplied quantities and conditions](hyp:m), [the adaptive pilot size sublinear assertion](goal) holds. For [the displayed quantities and conditions](hyp:hsub), these specify the stated inputs. -/
lemma adaptivePilotSize_sublinear (m : ℕ → ℕ)
    (hsub : PilotSublinear m) :
    Tendsto (fun n => (adaptivePilotSize m n : ℝ) / n) atTop (nhds 0) := by
  apply hsub.1.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [adaptivePilotSize_eq m hsub hn]

open Classical in
/-- For the supplied quantities and conditions, the adaptive true param is the mathematical object specified below. [The adaptive True Param](goal) is determined by [the displayed parameters](hyp:θ,h,n). -/
def adaptiveTrueParam (θ h : TrialParameter) (n : ℕ) : TrialParameter :=
  if InteriorMeans (localAlternative θ h n) then localAlternative θ h n else θ

/-- Under the supplied quantities and conditions, the adaptive true param interior assertion holds. Under [the stated assumptions](hyp:hθ), [the adaptive True Param interior](goal).

Under the stated assumptions, the adaptive True Param interior. -/
lemma adaptiveTrueParam_interior (θ h : TrialParameter) (n : ℕ)
    (hθ : InteriorMeans θ) : InteriorMeans (adaptiveTrueParam θ h n) := by
  unfold adaptiveTrueParam
  split_ifs with hlocal
  · exact hlocal
  · exact hθ

/-- Under [the supplied quantities and conditions](hyp:h,n), [the adaptive true param eq local alternative assertion](goal) holds. For [the displayed quantities and conditions](hyp:hlocal), these specify the stated inputs. -/
lemma adaptiveTrueParam_eq_localAlternative (θ h : TrialParameter) (n : ℕ)
    (hlocal : InteriorMeans (localAlternative θ h n)) :
    adaptiveTrueParam θ h n = localAlternative θ h n := by
  simp [adaptiveTrueParam, hlocal]

/-- Under [the supplied quantities and conditions](hyp:h), [the local alternative tendsto assertion](goal) holds. -/
lemma localAlternative_tendsto (θ h : TrialParameter) :
    Tendsto (localAlternative θ h) atTop (nhds θ) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  rw [tendsto_pi_nhds]
  intro k
  have hpert : Tendsto (fun n : ℕ => h k * (Real.sqrt (n : ℝ))⁻¹)
      atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hinv :
      Tendsto (fun n : ℕ => h k * (Real.sqrt (n : ℝ))⁻¹)
        atTop (nhds (h k * 0))) using 1 <;> simp
  simpa [localAlternative, div_eq_mul_inv] using tendsto_const_nhds.add hpert

/-- Under the supplied quantities and conditions, the eventually local alternative interior assertion holds. Under [the stated assumptions](hyp:hθ), [the eventually local Alternative interior](goal).

Under the stated assumptions, the eventually local Alternative interior. -/
lemma eventually_localAlternative_interior (θ h : TrialParameter)
    (hθ : InteriorMeans θ) :
    ∀ᶠ n in atTop, InteriorMeans (localAlternative θ h n) := by
  have ht := localAlternative_tendsto θ h
  have h0 := tendsto_pi_nhds.1 ht 0
  have h1 := tendsto_pi_nhds.1 ht 1
  filter_upwards [
    (tendsto_order.1 h0).1 0 hθ.1,
    (tendsto_order.1 h0).2 1 hθ.2.1,
    (tendsto_order.1 h1).1 0 hθ.2.2.1,
    (tendsto_order.1 h1).2 1 hθ.2.2.2] with n hn0l hn0r hn1l hn1r
  exact ⟨hn0l, hn0r, hn1l, hn1r⟩

/-- Under the supplied quantities and conditions, the eventually adaptive true param eq assertion holds. Under [the stated assumptions](hyp:hθ), [the eventually adaptive True Param eq](goal).

Under the stated assumptions, the eventually adaptive True Param eq. -/
lemma eventually_adaptiveTrueParam_eq (θ h : TrialParameter)
    (hθ : InteriorMeans θ) :
    ∀ᶠ n in atTop, adaptiveTrueParam θ h n = localAlternative θ h n := by
  filter_upwards [eventually_localAlternative_interior θ h hθ] with n hn
  exact adaptiveTrueParam_eq_localAlternative θ h n hn

/-- [the direction coord abs le assertion](goal) holds. For [the displayed quantities and conditions](hyp:hH,k), these specify the stated inputs. -/
lemma direction_coord_abs_le {h : TrialParameter} {H : ℝ}
    (hH : Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) ≤ H) (k : Fin 2) :
    |h k| ≤ H := by
  have hsqrt : 0 ≤ Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) := Real.sqrt_nonneg _
  have hsum : 0 ≤ (h 0) ^ 2 + (h 1) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  fin_cases k
  · have hsq : |h 0| ^ 2 ≤ (Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2)) ^ 2 := by
      rw [sq_abs, Real.sq_sqrt hsum]
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact ((sq_le_sq₀ (abs_nonneg _) hsqrt).mp hsq).trans hH
  · have hsq : |h 1| ^ 2 ≤ (Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2)) ^ 2 := by
      rw [sq_abs, Real.sq_sqrt hsum]
      exact le_add_of_nonneg_left (sq_nonneg _)
    exact ((sq_le_sq₀ (abs_nonneg _) hsqrt).mp hsq).trans hH

/-- Under the supplied quantities and conditions, the eventually local alternative dist lt uniform assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hδ), [the eventually local Alternative dist lt uniform](goal).

Under the stated assumptions, the eventually local Alternative dist lt uniform. -/
lemma eventually_localAlternative_dist_lt_uniform (θ : TrialParameter) (H δ : ℝ)
    (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ h : TrialParameter,
      Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) ≤ H →
        dist (localAlternative θ h n) θ < δ := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hev := hsqrt.eventually_gt_atTop (max 0 (H / δ))
  filter_upwards [hev] with n hn h hH
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) :=
    lt_of_le_of_lt (le_max_left 0 (H / δ)) hn
  rw [dist_pi_lt_iff hδ]
  intro k
  rw [Real.dist_eq]
  change |θ k + h k / Real.sqrt (n : ℝ) - θ k| < δ
  rw [add_sub_cancel_left, abs_div, abs_of_pos hsqrtpos]
  have hk := direction_coord_abs_le hH k
  have hratio : H / δ < Real.sqrt (n : ℝ) :=
    lt_of_le_of_lt (le_max_right 0 (H / δ)) hn
  calc
    |h k| / Real.sqrt (n : ℝ) ≤ H / Real.sqrt (n : ℝ) := by
      exact div_le_div_of_nonneg_right hk hsqrtpos.le
    _ < δ := by
      apply (div_lt_iff₀ hsqrtpos).2
      have hmul := (div_lt_iff₀ hδ).1 hratio
      nlinarith

/-- Under the supplied quantities and conditions, the eventually local alternative interior uniform assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ), [the eventually local Alternative interior uniform](goal).

Under the stated assumptions, the eventually local Alternative interior uniform. -/
lemma eventually_localAlternative_interior_uniform (θ : TrialParameter) (H : ℝ)
    (hθ : InteriorMeans θ) :
    ∀ᶠ n in atTop, ∀ h : TrialParameter,
      Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) ≤ H →
        InteriorMeans (localAlternative θ h n) := by
  let δ := min (min (θ 0) (1 - θ 0)) (min (θ 1) (1 - θ 1))
  have hδ : 0 < δ := by
    simp only [δ, lt_min_iff]
    exact ⟨⟨hθ.1, sub_pos.mpr hθ.2.1⟩, ⟨hθ.2.2.1, sub_pos.mpr hθ.2.2.2⟩⟩
  filter_upwards [eventually_localAlternative_dist_lt_uniform θ H δ hδ] with n hn
  intro h hH
  have hd := (dist_pi_lt_iff hδ).mp (hn h hH)
  have hd0 := hd 0
  have hd1 := hd 1
  rw [Real.dist_eq] at hd0 hd1
  dsimp [localAlternative] at hd0 hd1 ⊢
  have hδ0 : δ ≤ θ 0 ∧ δ ≤ 1 - θ 0 := by
    dsimp [δ]
    exact ⟨(min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _)⟩
  have hδ1 : δ ≤ θ 1 ∧ δ ≤ 1 - θ 1 := by
    dsimp [δ]
    exact ⟨(min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  constructor
  · change 0 < θ 0 + h 0 / Real.sqrt (n : ℝ)
    linarith [(abs_lt.mp hd0).1]
  constructor
  · change θ 0 + h 0 / Real.sqrt (n : ℝ) < 1
    linarith [(abs_lt.mp hd0).2]
  constructor
  · change 0 < θ 1 + h 1 / Real.sqrt (n : ℝ)
    linarith [(abs_lt.mp hd1).1]
  · change θ 1 + h 1 / Real.sqrt (n : ℝ) < 1
    linarith [(abs_lt.mp hd1).2]

/-- Under the supplied quantities and conditions, the eventually adaptive true param eq uniform assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ), [the eventually adaptive True Param eq uniform](goal).

Under the stated assumptions, the eventually adaptive True Param eq uniform. -/
lemma eventually_adaptiveTrueParam_eq_uniform (θ : TrialParameter) (H : ℝ)
    (hθ : InteriorMeans θ) :
    ∀ᶠ n in atTop, ∀ h : TrialParameter,
      Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) ≤ H →
        adaptiveTrueParam θ h n = localAlternative θ h n := by
  filter_upwards [eventually_localAlternative_interior_uniform θ H hθ] with n hn
  intro h hH
  exact adaptiveTrueParam_eq_localAlternative θ h n (hn h hH)

/-- Under the supplied quantities and conditions, the eventually adaptive true param dist lt uniform assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hδ), [the eventually adaptive True Param dist lt uniform](goal).

Under the stated assumptions, the eventually adaptive True Param dist lt uniform. -/
lemma eventually_adaptiveTrueParam_dist_lt_uniform (θ : TrialParameter) (H δ : ℝ)
    (hθ : InteriorMeans θ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ h : TrialParameter,
      Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) ≤ H →
        dist (adaptiveTrueParam θ h n) θ < δ := by
  filter_upwards [eventually_adaptiveTrueParam_eq_uniform θ H hθ,
    eventually_localAlternative_dist_lt_uniform θ H δ hδ] with n heq hdist
  intro h hH
  rw [heq h hH]
  exact hdist h hH

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the eventually adaptive true param mem open uniform assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hNopen,hθN), [the eventually adaptive True Param mem open uniform](goal).

Under the stated assumptions, the eventually adaptive True Param mem open uniform. -/
lemma eventually_adaptiveTrueParam_mem_open_uniform
    (θ : TrialParameter) (H : ℝ) (N : Set TrialParameter)
    (hθ : InteriorMeans θ) (hNopen : IsOpen N) (hθN : θ ∈ N) :
    ∀ᶠ n in atTop, ∀ h : TrialParameter,
      Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) ≤ H →
        adaptiveTrueParam θ h n ∈ N := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hNopen θ hθN
  filter_upwards [eventually_adaptiveTrueParam_dist_lt_uniform θ H δ hθ hδ] with n hn
  intro h hH
  exact hball (by simpa [Metric.mem_ball, dist_comm] using hn h hH)

/-- For the supplied quantities and conditions, the adaptive pilot prefix mass is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Pilot Prefix Mass](goal) is determined by [the displayed parameters](hyp:θ,h,p,ε,m,n,u). -/
def adaptivePilotPrefixMass (θ h : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (n : ℕ) (u : Fin (adaptivePilotSize m n) → Fin 4) : ℝ :=
  ∏ j : Fin (adaptivePilotSize m n),
    ∑ a : Fin 4, piTheta (adaptiveTrueParam θ h n) p a *
      rrPilotProbability ε a (u j)

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the adaptive pilot prefix mass nonneg assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the adaptive Pilot Prefix Mass nonneg](goal).

Under the stated assumptions, the adaptive Pilot Prefix Mass nonneg. -/
lemma adaptivePilotPrefixMass_nonneg (θ h : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (n : ℕ) (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (u : Fin (adaptivePilotSize m n) → Fin 4) :
    0 ≤ adaptivePilotPrefixMass θ h p ε m n u := by
  unfold adaptivePilotPrefixMass
  apply Finset.prod_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg
    (piTheta_pos_interior (adaptiveTrueParam θ h n) p hp
      (adaptiveTrueParam_interior θ h n hθ) a).le
    (by
      unfold rrPilotProbability
      split_ifs <;> positivity)

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under [the supplied quantities and conditions](hyp:h,p), [the adaptive pilot prefix mass sum assertion](goal) holds. For [the displayed quantities and conditions](hyp:m,n), these specify the stated inputs. -/
lemma adaptivePilotPrefixMass_sum (θ h : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (n : ℕ) :
    ∑ u : Fin (adaptivePilotSize m n) → Fin 4,
      adaptivePilotPrefixMass θ h p ε m n u = 1 := by
  unfold adaptivePilotPrefixMass
  calc
    (∑ u : Fin (adaptivePilotSize m n) → Fin 4,
        ∏ j : Fin (adaptivePilotSize m n),
          ∑ a : Fin 4, piTheta (adaptiveTrueParam θ h n) p a *
            rrPilotProbability ε a (u j)) =
        ∏ _j : Fin (adaptivePilotSize m n), ∑ k : Fin 4,
          ∑ a : Fin 4, piTheta (adaptiveTrueParam θ h n) p a *
            rrPilotProbability ε a k :=
      (Fintype.prod_sum (fun _j : Fin (adaptivePilotSize m n) => fun k : Fin 4 =>
        ∑ a : Fin 4, piTheta (adaptiveTrueParam θ h n) p a *
          rrPilotProbability ε a k)).symm
    _ = 1 := by simp [rrPilot_marginal_sum_eq_one]

end CausalSmith.Stat.LdpAteEfficiencySurface
