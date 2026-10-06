module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveAveraging
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveContinuity

/-!
# Finite triangular-row inputs for private-pilot attainment

This module packages the exact finite alphabet mass and centered score used by the
adaptive main sample.  It stays independent of the generic triangular-array substrate,
so a later adapter can instantiate that substrate without rebuilding the paper-specific
mass, centering, boundedness, variance, and finite-product algebra.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open Filter
open scoped Topology BigOperators

/-- The one-coordinate mass in the adaptive main row along a local alternative and a chosen sequence of pilot selectors. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Pilot Row Mass](goal) is determined by [the displayed parameters](hyp:select,θ,h,η,p,ε,hselect,hp,hε,n,s). -/
def adaptivePilotRowMass (θ h : TrialParameter) (η : ℕ → TrialParameter)
    (p ε : ℝ) (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p) (hε : 0 < ε)
    (n : ℕ) (s : Fin 14) : ℝ :=
  adaptiveMainMass select (adaptiveTrueParam θ h n) (η n) p ε s

/-- The selected main-release score centered by its exact one-coordinate mean. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Pilot Row Score](goal) is determined by [the displayed parameters](hyp:select,θ,h,η,p,ε,hselect,hp,hε,n,s). -/
def adaptivePilotRowScore (θ h : TrialParameter) (η : ℕ → TrialParameter)
    (p ε : ℝ) (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p) (hε : 0 < ε)
    (n : ℕ) (s : Fin 14) : ℝ :=
  adaptiveSelectedScore select (η n) p ε s -
    (contrast (adaptiveTrueParam θ h n) - contrast (η n))

/-- The limiting row variance as a nonnegative real. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Pilot Limit Variance](goal) is determined by [the displayed parameters](hyp:select,θ,p,ε,hselect,hp,hθ,hε). -/
def adaptivePilotLimitVariance (θ : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) : NNReal :=
  ⟨Vstar θ p ε,
    (inv_pos.mpr (Jstar_pos_interior θ p ε hp hθ hε)).le⟩

/-- The adaptive main row has nonnegative one-coordinate masses. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε), [the adaptive Pilot Row Mass nonneg](goal).

Under the stated assumptions, the adaptive Pilot Row Mass nonneg. -/
lemma adaptivePilotRowMass_nonneg (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (hη : ∀ n, InteriorMeans (η n)) (hε : 0 < ε)
    (n : ℕ) (s : Fin 14) :
    0 ≤ adaptivePilotRowMass select θ h η p ε hselect hp hε n s := by
  exact adaptiveMainMass_nonneg select _ _ p ε hselect hp
    (adaptiveTrueParam_interior θ h n hθ) (hη n) hε s

/-- The adaptive main row masses sum to one. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hη,hε), [the adaptive Pilot Row Mass sum](goal).

Under the stated assumptions, the adaptive Pilot Row Mass sum. -/
lemma adaptivePilotRowMass_sum (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p)
    (hη : ∀ n, InteriorMeans (η n)) (hε : 0 < ε) (n : ℕ) :
    ∑ s : Fin 14, adaptivePilotRowMass select θ h η p ε hselect hp hε n s = 1 := by
  exact adaptiveMainMass_sum select _ _ p ε hselect hp (hη n) hε

/-- The adaptive main-row score is exactly centered under its row mass. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hη,hε), [the adaptive Pilot Row Score centered](goal).

Under the stated assumptions, the adaptive Pilot Row Score centered. -/
lemma adaptivePilotRowScore_centered (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p)
    (hη : ∀ n, InteriorMeans (η n)) (hε : 0 < ε) (n : ℕ) :
    ∑ s : Fin 14, adaptivePilotRowMass select θ h η p ε hselect hp hε n s *
      adaptivePilotRowScore select θ h η p ε hselect hp hε n s = 0 := by
  rw [show (∑ s : Fin 14, adaptivePilotRowMass select θ h η p ε hselect hp hε n s *
      adaptivePilotRowScore select θ h η p ε hselect hp hε n s) =
      (∑ s : Fin 14, adaptiveMainMass select (adaptiveTrueParam θ h n) (η n)
        p ε s * adaptiveSelectedScore select (η n) p ε s) -
      (contrast (adaptiveTrueParam θ h n) - contrast (η n)) *
        ∑ s : Fin 14, adaptiveMainMass select (adaptiveTrueParam θ h n) (η n)
        p ε s by
    simp only [adaptivePilotRowMass, adaptivePilotRowScore]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    apply congrArg₂ (· - ·) rfl
    apply Finset.sum_congr rfl
    intro s _
    ring]
  rw [adaptiveSelectedScore_mean select _ _ p ε hselect hp (hη n) hε,
    adaptiveMainMass_sum select _ _ p ε hselect hp (hη n) hε]
  ring

/-- The exact mean correction is no larger than the common selected-score bound. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε), [the adaptive Pilot Row Mean abs le](goal).

Under the stated assumptions, the adaptive Pilot Row Mean abs le. -/
lemma adaptivePilotRowMean_abs_le (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (hη : ∀ n, InteriorMeans (η n)) (hε : 0 < ε)
    (n : ℕ) :
    |contrast (adaptiveTrueParam θ h n) - contrast (η n)| ≤
      pilotPhiUpper p ε := by
  rw [← adaptiveSelectedScore_mean select (adaptiveTrueParam θ h n) (η n)
    p ε hselect hp (hη n) hε]
  calc
    |∑ s : Fin 14, adaptiveMainMass select (adaptiveTrueParam θ h n) (η n)
        p ε s * adaptiveSelectedScore select (η n) p ε s| ≤
        ∑ s : Fin 14, |adaptiveMainMass select (adaptiveTrueParam θ h n) (η n)
        p ε s * adaptiveSelectedScore select (η n) p ε s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Fin 14, adaptiveMainMass select (adaptiveTrueParam θ h n) (η n)
        p ε s * pilotPhiUpper p ε := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, abs_of_nonneg (adaptiveMainMass_nonneg select _ _ p ε hselect hp
        (adaptiveTrueParam_interior θ h n hθ) (hη n) hε s)]
      exact mul_le_mul_of_nonneg_left
        (adaptiveSelectedScore_abs_le select (η n) p ε hselect hp (hη n) hε s)
        (adaptiveMainMass_nonneg select _ _ p ε hselect hp
          (adaptiveTrueParam_interior θ h n hθ) (hη n) hε s)
    _ = pilotPhiUpper p ε := by
      rw [← Finset.sum_mul, adaptiveMainMass_sum select _ _ p ε hselect hp (hη n) hε,
        one_mul]

/-- Every centered adaptive row score is bounded by twice the common selected-score bound. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε), [the adaptive Pilot Row Score abs le](goal).

Under the stated assumptions, the adaptive Pilot Row Score abs le. -/
lemma adaptivePilotRowScore_abs_le (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (hη : ∀ n, InteriorMeans (η n)) (hε : 0 < ε)
    (n : ℕ) (s : Fin 14) :
    |adaptivePilotRowScore select θ h η p ε hselect hp hε n s| ≤
      2 * pilotPhiUpper p ε := by
  unfold adaptivePilotRowScore
  calc
    |_ - _| ≤ |adaptiveSelectedScore select (η n) p ε s| +
        |contrast (adaptiveTrueParam θ h n) - contrast (η n)| :=
      abs_sub _ _
    _ ≤ pilotPhiUpper p ε + pilotPhiUpper p ε :=
      add_le_add
        (adaptiveSelectedScore_abs_le select (η n) p ε hselect hp (hη n) hε s)
        (adaptivePilotRowMean_abs_le select θ h η p ε hselect hp hθ hη hε n)
    _ = 2 * pilotPhiUpper p ε := by ring

/-- The one-coordinate second moment of the centered row score is exactly the adaptive score variance. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hη,hε), [the adaptive Pilot Row second Moment eq](goal).

Under the stated assumptions, the adaptive Pilot Row second Moment eq. -/
lemma adaptivePilotRow_secondMoment_eq (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p)
    (hη : ∀ n, InteriorMeans (η n)) (hε : 0 < ε) (n : ℕ) :
    (∑ s : Fin 14, adaptivePilotRowMass select θ h η p ε hselect hp hε n s *
      (adaptivePilotRowScore select θ h η p ε hselect hp hε n s) ^ 2) =
      adaptiveScoreVariance select (adaptiveTrueParam θ h n) (η n) p ε := by
  exact (adaptiveScoreVariance_eq_centered_sum select
    (adaptiveTrueParam θ h n) (η n) p ε hselect hp (hη n) hε).symm

/-- The regularized local parameter converges to the base parameter. For the displayed inputs and conditions, the stated result follows. Under [the stated assumptions](hyp:hθ), [the adaptive True Param tendsto](goal).

Under the stated assumptions, the adaptive True Param tendsto. -/
lemma adaptiveTrueParam_tendsto (θ h : TrialParameter) (hθ : InteriorMeans θ) :
    Tendsto (adaptiveTrueParam θ h) atTop (nhds θ) := by
  apply (localAlternative_tendsto θ h).congr'
  filter_upwards [eventually_adaptiveTrueParam_eq θ h hθ] with n hn
  exact hn.symm

/-- If the selected pilot parameters converge to the base point, the centered adaptive row variances converge to the oracle variance. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε,hηlim), [the adaptive Pilot Row variance tendsto](goal).

Under the stated assumptions, the adaptive Pilot Row variance tendsto. -/
lemma adaptivePilotRow_variance_tendsto (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (hη : ∀ n, InteriorMeans (η n)) (hε : 0 < ε)
    (hηlim : Tendsto η atTop (nhds θ)) :
    Tendsto (fun n => ∑ s : Fin 14,
      adaptivePilotRowMass select θ h η p ε hselect hp hε n s *
        (adaptivePilotRowScore select θ h η p ε hselect hp hε n s) ^ 2)
      atTop (nhds ((adaptivePilotLimitVariance select θ p ε hselect hp hθ hε : NNReal) : ℝ)) := by
  have hpair : Tendsto (fun n => (adaptiveTrueParam θ h n, η n)) atTop
      (nhds (θ, θ)) := (adaptiveTrueParam_tendsto θ h hθ).prodMk_nhds hηlim
  have hv := (continuousAt_adaptiveScoreVariance_diag select θ p ε hselect hp hθ hε).tendsto.comp hpair
  change Tendsto (fun n => ∑ s : Fin 14,
    adaptivePilotRowMass select θ h η p ε hselect hp hε n s *
      (adaptivePilotRowScore select θ h η p ε hselect hp hε n s) ^ 2)
    atTop (nhds (Vstar θ p ε))
  convert hv using 1
  · funext n
    exact adaptivePilotRow_secondMoment_eq select θ h η p ε hselect hp hη hε n
  · simp [adaptiveScoreVariance_diag select θ p ε hselect hp hθ hε]

/-- The limiting adaptive row variance is strictly positive. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε), [the adaptive Pilot Limit Variance pos](goal).

Under the stated assumptions, the adaptive Pilot Limit Variance pos. -/
lemma adaptivePilotLimitVariance_pos (θ : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    0 < adaptivePilotLimitVariance select θ p ε hselect hp hθ hε := by
  change 0 < Vstar θ p ε
  unfold Vstar
  exact inv_pos.mpr (Jstar_pos_interior θ p ε hp hθ hε)

/-- The literal iid product mass of an adaptive main row. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Pilot Row Product Mass](goal) is determined by [the displayed parameters](hyp:select,θ,h,η,p,ε,m,hselect,hp,hε,n,v). -/
def adaptivePilotRowProductMass (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ)
    (v : Fin (adaptiveMainSize m n) → Fin 14) : ℝ :=
  ∏ j, adaptivePilotRowMass select θ h η p ε hselect hp hε n (v j)

/-- Every conditional main-row product atom has nonnegative mass. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε), [the adaptive Pilot Row Product Mass nonneg](goal).

Under the stated assumptions, the adaptive Pilot Row Product Mass nonneg. -/
lemma adaptivePilotRowProductMass_nonneg (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (hη : ∀ n, InteriorMeans (η n)) (hε : 0 < ε) (n : ℕ)
    (v : Fin (adaptiveMainSize m n) → Fin 14) :
    0 ≤ adaptivePilotRowProductMass select θ h η p ε m hselect hp hε n v := by
  exact Finset.prod_nonneg fun j _ =>
    adaptivePilotRowMass_nonneg select θ h η p ε hselect hp hθ hη hε n (v j)

/-- The conditional iid main-row product masses sum to one. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hη,hε), [the adaptive Pilot Row Product Mass sum](goal).

Under the stated assumptions, the adaptive Pilot Row Product Mass sum. -/
lemma adaptivePilotRowProductMass_sum (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hη : ∀ n, InteriorMeans (η n))
    (hε : 0 < ε) (n : ℕ) :
    ∑ v : Fin (adaptiveMainSize m n) → Fin 14,
      adaptivePilotRowProductMass select θ h η p ε m hselect hp hε n v = 1 := by
  classical
  calc
    _ = ∏ _j : Fin (adaptiveMainSize m n),
        ∑ s : Fin 14, adaptivePilotRowMass select θ h η p ε hselect hp hε n s := by
      simpa [adaptivePilotRowProductMass] using
        (Fintype.prod_sum (fun _j : Fin (adaptiveMainSize m n) =>
          adaptivePilotRowMass select θ h η p ε hselect hp hε n)).symm
    _ = 1 := by simp [adaptivePilotRowMass_sum select θ h η p ε hselect hp hη hε n]

/-- Summing the centered row score subtracts exactly the row length times the paper estimator's mean correction. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε), [the adaptive Pilot Row Score sum eq](goal).

Under the stated assumptions, the adaptive Pilot Row Score sum eq. -/
lemma adaptivePilotRowScore_sum_eq (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ)
    (v : Fin (adaptiveMainSize m n) → Fin 14) :
    ∑ j, adaptivePilotRowScore select θ h η p ε hselect hp hε n (v j) =
      (∑ j, adaptiveSelectedScore select (η n) p ε (v j)) -
        (adaptiveMainSize m n : ℝ) *
          (contrast (adaptiveTrueParam θ h n) - contrast (η n)) := by
  simp only [adaptivePilotRowScore, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ : Finset (Fin (adaptiveMainSize m n))).card =
      adaptiveMainSize m n := by simp
  rw [hcard]
  ring

/-- For a nonempty main row, its corrected sample average minus the true contrast is the average centered row score. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hn), [the adaptive Pilot Row estimator Error eq](goal).

Under the stated assumptions, the adaptive Pilot Row estimator Error eq. -/
lemma adaptivePilotRow_estimatorError_eq (θ h : TrialParameter)
    (η : ℕ → TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ)
    (hn : 0 < adaptiveMainSize m n)
    (v : Fin (adaptiveMainSize m n) → Fin 14) :
    contrast (η n) + (adaptiveMainSize m n : ℝ)⁻¹ *
        (∑ j, adaptiveSelectedScore select (η n) p ε (v j)) -
        contrast (adaptiveTrueParam θ h n) =
      (adaptiveMainSize m n : ℝ)⁻¹ *
        ∑ j, adaptivePilotRowScore select θ h η p ε hselect hp hε n (v j) := by
  rw [adaptivePilotRowScore_sum_eq select θ h η p ε m hselect hp hε n v]
  have hN : (adaptiveMainSize m n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  field_simp
  ring

end CausalSmith.Stat.LdpAteEfficiencySurface
