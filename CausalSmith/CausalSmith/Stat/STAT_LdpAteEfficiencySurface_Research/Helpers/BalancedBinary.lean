module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiniteOracle
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Pilot
public import Causalean.Stat.Privacy.Binary.RandomizedResponse

/-! # Binary submodel for the balanced trial

This file groups the four trial cells by the signed treatment--outcome bit.  The
grouped experiment is the one-dimensional Bernoulli submodel used in the
balanced randomized-response calculation.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BalancedBinary

variable {Z : Type*} [MeasurableSpace Z]

/-- the [half nn](goal) is the mathematical object specified below. -/
def halfNN : NNReal := ⟨(1 / 2 : ℝ), by norm_num⟩
/-- the [half](goal) is the mathematical object specified below. -/
def half : ℝ≥0∞ := halfNN

/-- Average the two full-record rows having the same signed bit. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
def groupedChannel (Q : Kernel (Fin 4) Z) : Kernel Bool Z :=
  Kernel.ofFunOfCountable fun b =>
    if b then half • (Q 0 + Q 3) else half • (Q 1 + Q 2)

/-- Under [the supplied quantities and conditions](hyp:b), [the grouped channel apply assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma groupedChannel_apply (Q : Kernel (Fin 4) Z) (b : Bool) :
    groupedChannel Q b =
      if b then half • (Q 0 + Q 3) else half • (Q 1 + Q 2) := by
  rfl

/-- [the grouped channel markov assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma groupedChannel_markov (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q] :
    IsMarkovKernel (groupedChannel Q) := by
  have hhalf : half * 2 = (1 : ENNReal) := by
    change (↑halfNN : ENNReal) * ↑(2 : NNReal) = ↑(1 : NNReal)
    rw [← ENNReal.coe_mul]
    congr 1
    apply NNReal.eq
    change (1 / 2 : ℝ) * 2 = 1
    norm_num
  constructor
  intro b
  constructor
  cases b <;> simp [groupedChannel_apply]
  all_goals
    calc
      half + half = half * 2 := by ring
      _ = 1 := hhalf

/-- [the grouped channel private assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,hQ), these specify the stated inputs. -/
lemma groupedChannel_private (Q : Kernel (Fin 4) Z) {ε : ℝ}
    (hQ : StationaryLDP ε Q) :
    Causalean.Stat.Privacy.Binary.SetwisePrivate (groupedChannel Q) ε := by
  intro b c A hA
  cases b <;> cases c
  · simp only [groupedChannel_apply, Measure.smul_apply, hA, Measure.add_apply]
    calc
      half * (Q 1 A + Q 2 A) ≤
          half * (ENNReal.ofReal (Real.exp ε) * Q 1 A +
            ENNReal.ofReal (Real.exp ε) * Q 2 A) := by
        gcongr
        exact hQ.2 A hA 1 1
        exact hQ.2 A hA 2 2
      _ = ENNReal.ofReal (Real.exp ε) * (half * (Q 1 A + Q 2 A)) := by ring
  · simp only [groupedChannel_apply, Measure.smul_apply, hA, Measure.add_apply]
    calc
      half * (Q 1 A + Q 2 A) ≤
          half * (ENNReal.ofReal (Real.exp ε) * Q 0 A +
            ENNReal.ofReal (Real.exp ε) * Q 3 A) := by
        gcongr
        exact hQ.2 A hA 1 0
        exact hQ.2 A hA 2 3
      _ = ENNReal.ofReal (Real.exp ε) * (half * (Q 0 A + Q 3 A)) := by
        ring
  · simp only [groupedChannel_apply, Measure.smul_apply, hA, Measure.add_apply]
    calc
      half * (Q 0 A + Q 3 A) ≤
          half * (ENNReal.ofReal (Real.exp ε) * Q 1 A +
            ENNReal.ofReal (Real.exp ε) * Q 2 A) := by
        gcongr
        exact hQ.2 A hA 0 1
        exact hQ.2 A hA 3 2
      _ = ENNReal.ofReal (Real.exp ε) * (half * (Q 1 A + Q 2 A)) := by
        ring
  · simp only [groupedChannel_apply, Measure.smul_apply, hA, Measure.add_apply]
    calc
      half * (Q 0 A + Q 3 A) ≤
          half * (ENNReal.ofReal (Real.exp ε) * Q 0 A +
            ENNReal.ofReal (Real.exp ε) * Q 3 A) := by
        gcongr
        exact hQ.2 A hA 0 0
        exact hQ.2 A hA 3 3
      _ = ENNReal.ofReal (Real.exp ε) * (half * (Q 0 A + Q 3 A)) := by ring

/-- [the reference grouped channel assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma reference_groupedChannel (Q : Kernel (Fin 4) Z) :
    Causalean.Stat.Privacy.Binary.reference (groupedChannel Q) =
      half • dominatingMeasure Q := by
  ext A hA
  simp [Causalean.Stat.Privacy.Binary.reference, groupedChannel_apply,
    dominatingMeasure, Measure.sum_apply, hA, Fin.sum_univ_succ]
  ring

/-- [the grouped density true assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma groupedDensity_true (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q] :
    ∀ᵐ z ∂dominatingMeasure Q,
      Causalean.Stat.Privacy.Binary.rowDensity (groupedChannel Q) true z =
        channelDensity Q 0 z + channelDensity Q 3 z := by
  let D := dominatingMeasure Q
  let A := Q 0 + Q 3
  letI : IsFiniteMeasure D := by dsimp [D, dominatingMeasure]; infer_instance
  letI : IsFiniteMeasure A := by dsimp [A]; infer_instance
  have hs := Measure.rnDeriv_smul_same A D (r := halfNN) (by
    apply ne_of_gt
    change 0 < (1 / 2 : ℝ)
    norm_num)
  have ha := Measure.rnDeriv_add (Q 0) (Q 3) D
  filter_upwards [hs, ha, (Q 0).rnDeriv_ne_top D, (Q 3).rnDeriv_ne_top D] with z hs ha h0 h3
  unfold Causalean.Stat.Privacy.Binary.rowDensity channelDensity
  rw [reference_groupedChannel, groupedChannel_apply]
  change (((halfNN • A).rnDeriv (halfNN • D) z).toReal) = _
  rw [hs, ha]
  change (((Q 0).rnDeriv D z + (Q 3).rnDeriv D z).toReal) = _
  rw [ENNReal.toReal_add h0 h3]

/-- [the grouped density false assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma groupedDensity_false (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q] :
    ∀ᵐ z ∂dominatingMeasure Q,
      Causalean.Stat.Privacy.Binary.rowDensity (groupedChannel Q) false z =
        channelDensity Q 1 z + channelDensity Q 2 z := by
  let D := dominatingMeasure Q
  let A := Q 1 + Q 2
  letI : IsFiniteMeasure D := by dsimp [D, dominatingMeasure]; infer_instance
  letI : IsFiniteMeasure A := by dsimp [A]; infer_instance
  have hs := Measure.rnDeriv_smul_same A D (r := halfNN) (by
    apply ne_of_gt
    change 0 < (1 / 2 : ℝ)
    norm_num)
  have ha := Measure.rnDeriv_add (Q 1) (Q 2) D
  filter_upwards [hs, ha, (Q 1).rnDeriv_ne_top D, (Q 2).rnDeriv_ne_top D] with z hs ha h1 h2
  unfold Causalean.Stat.Privacy.Binary.rowDensity channelDensity
  rw [reference_groupedChannel, groupedChannel_apply]
  change (((halfNN • A).rnDeriv (halfNN • D) z).toReal) = _
  rw [hs, ha]
  change (((Q 1).rnDeriv D z + (Q 2).rnDeriv D z).toReal) = _
  rw [ENNReal.toReal_add h1 h2]

/-- Under the supplied quantities and conditions, the abs contrast lt one assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hbalance), [the abs contrast lt one](goal).

Under the stated assumptions, the abs contrast lt one. -/
lemma abs_contrast_lt_one (θ : TrialParameter) (hθ : InteriorMeans θ)
    (hbalance : θ 0 + θ 1 = 1) :
    |contrast θ| < 1 := by
  rcases hθ with ⟨h00, h01, h10, h11⟩
  rw [abs_lt]
  constructor <;> simp [contrast] <;> linarith

/-- Under [the supplied quantities and conditions](hyp:j), [the pi theta balanced by val assertion](goal) holds. -/
lemma piTheta_balanced_by_val (θ : TrialParameter) (j : Fin 4) :
    piTheta θ (1 / 2) j =
      if j.val = 0 then controlProb (1 / 2) * (1 - θ 0)
      else if j.val = 1 then controlProb (1 / 2) * θ 0
      else if j.val = 2 then (1 / 2) * (1 - θ 1)
      else (1 / 2) * θ 1 := by
  rcases j with ⟨j, hj⟩
  interval_cases j <;> rfl

/-- [the channel output density balanced assertion](goal) holds. For [the displayed quantities and conditions](hyp:hbalance,Q,z), these specify the stated inputs. -/
lemma channelOutputDensity_balanced (θ : TrialParameter)
    (hbalance : θ 0 + θ 1 = 1) (Q : Kernel (Fin 4) Z) (z : Z) :
    channelOutputDensity θ (1 / 2) Q z =
      ((1 - θ 0) * (channelDensity Q 0 z + channelDensity Q 3 z) +
        θ 0 * (channelDensity Q 1 z + channelDensity Q 2 z)) / 2 := by
  have hθ1 : θ 1 = 1 - θ 0 := by linarith
  unfold channelOutputDensity
  rw [show (∑ j : Fin 4, piTheta θ (1 / 2) j * channelDensity Q j z) =
      piTheta θ (1 / 2) 0 * channelDensity Q 0 z +
      piTheta θ (1 / 2) 1 * channelDensity Q 1 z +
      piTheta θ (1 / 2) 2 * channelDensity Q 2 z +
      piTheta θ (1 / 2) 3 * channelDensity Q 3 z by
        simp [Fin.sum_univ_succ]
        ring]
  have hp0 : piTheta θ (1 / 2) 0 = (1 - θ 0) / 2 := by
    rw [piTheta_balanced_by_val]
    norm_num [controlProb]
    ring
  have hp1 : piTheta θ (1 / 2) 1 = θ 0 / 2 := by
    rw [piTheta_balanced_by_val]
    norm_num [controlProb]
    ring
  have hp2 : piTheta θ (1 / 2) 2 = θ 0 / 2 := by
    rw [piTheta_balanced_by_val, hθ1]
    norm_num
    ring
  have hp3 : piTheta θ (1 / 2) 3 = (1 - θ 0) / 2 := by
    rw [piTheta_balanced_by_val, hθ1]
    norm_num
    ring
  rw [hp0, hp1, hp2, hp3]
  ring

/-- Under [the supplied quantities and conditions](hyp:z), [the directional derivative balanced assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma directionalDerivative_balanced (Q : Kernel (Fin 4) Z) (z : Z) :
    (∑ k, direction (-1 / 2) k * channelDerivativeDensity (1 / 2) Q k z) =
      (channelDensity Q 0 z + channelDensity Q 3 z -
        (channelDensity Q 1 z + channelDensity Q 2 z)) / 4 := by
  simp +decide [channelDerivativeDensity, inputDerivative, direction,
    controlProb, Fin.sum_univ_succ]
  ring

/-- Under the supplied quantities and conditions, the grouped information eq channel quadratic assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hbalance,hQ), [the grouped information eq channel Quadratic](goal).

Under the stated assumptions, the grouped information eq channel Quadratic. -/
lemma grouped_information_eq_channelQuadratic
    (θ : TrialParameter) (hθ : InteriorMeans θ)
    (hbalance : θ 0 + θ 1 = 1) (ε : ℝ)
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP ε Q) :
    Causalean.Stat.Privacy.Binary.information (groupedChannel Q) (contrast θ) =
      informationQuadratic (channelFisherInfo θ (1 / 2) Q) (direction (-1 / 2)) := by
  letI : IsMarkovKernel Q := hQ.1
  letI : IsMarkovKernel (groupedChannel Q) := groupedChannel_markov Q
  have ht := abs_contrast_lt_one θ hθ hbalance
  rw [Causalean.Stat.Privacy.Binary.information_eq_contrast_integral
    (groupedChannel Q) (contrast θ) ht]
  rw [informationQuadratic_eq_channelIntegral (1 / 2) θ
    (by constructor <;> norm_num) hθ ε Q hQ (direction (-1 / 2))]
  rw [reference_groupedChannel]
  rw [show half • dominatingMeasure Q = halfNN • dominatingMeasure Q by rfl]
  rw [integral_smul_nnreal_measure]
  change (halfNN : ℝ) * (∫ x,
    Causalean.Stat.Privacy.Binary.balancedDensity (groupedChannel Q) x *
      Causalean.Stat.Privacy.Binary.contrast (groupedChannel Q) x ^ 2 /
        (1 + contrast θ *
          Causalean.Stat.Privacy.Binary.contrast (groupedChannel Q) x)
      ∂dominatingMeasure Q) = _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [groupedDensity_true Q, groupedDensity_false Q] with z hzT hzF
  rw [show (halfNN : ℝ) = 1 / 2 by rfl]
  unfold Causalean.Stat.Privacy.Binary.balancedDensity
    Causalean.Stat.Privacy.Binary.contrast
  rw [hzT, hzF]
  rw [directionalDerivative_balanced, channelOutputDensity_balanced θ hbalance]
  have hcontrast : contrast θ = 1 - 2 * θ 0 := by
    simp [contrast]
    linarith
  rw [hcontrast]
  by_cases hs : channelDensity Q 0 z + channelDensity Q 3 z +
      (channelDensity Q 1 z + channelDensity Q 2 z) = 0
  · have h0 : channelDensity Q 0 z = 0 := by
      have hn (j : Fin 4) : 0 ≤ channelDensity Q j z := ENNReal.toReal_nonneg
      nlinarith [hn 0, hn 1, hn 2, hn 3]
    have h1 : channelDensity Q 1 z = 0 := by
      have hn (j : Fin 4) : 0 ≤ channelDensity Q j z := ENNReal.toReal_nonneg
      nlinarith [hn 0, hn 1, hn 2, hn 3]
    have h2 : channelDensity Q 2 z = 0 := by
      have hn (j : Fin 4) : 0 ≤ channelDensity Q j z := ENNReal.toReal_nonneg
      nlinarith [hn 0, hn 1, hn 2, hn 3]
    have h3 : channelDensity Q 3 z = 0 := by
      have hn (j : Fin 4) : 0 ≤ channelDensity Q j z := ENNReal.toReal_nonneg
      nlinarith [hn 0, hn 1, hn 2, hn 3]
    simp [h0, h1, h2, h3]
  · have hn (j : Fin 4) : 0 ≤ channelDensity Q j z := ENNReal.toReal_nonneg
    have hsumpos : 0 < channelDensity Q 0 z + channelDensity Q 3 z +
        (channelDensity Q 1 z + channelDensity Q 2 z) := by
      exact lt_of_le_of_ne
        (add_nonneg (add_nonneg (hn 0) (hn 3)) (add_nonneg (hn 1) (hn 2)))
        (Ne.symm hs)
    have hθ0 := hθ.1
    have hθ0' := hθ.2.1
    have hdenpos : 0 <
        (1 - θ 0) * (channelDensity Q 0 z + channelDensity Q 3 z) +
          θ 0 * (channelDensity Q 1 z + channelDensity Q 2 z) := by
      by_cases ha : channelDensity Q 0 z + channelDensity Q 3 z = 0
      · have hb : 0 < channelDensity Q 1 z + channelDensity Q 2 z := by
          linarith
        rw [ha]
        simpa using mul_pos hθ0 hb
      · have ha' : 0 < channelDensity Q 0 z + channelDensity Q 3 z :=
          lt_of_le_of_ne (add_nonneg (hn 0) (hn 3)) (Ne.symm ha)
        exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) ha')
          (mul_nonneg hθ0.le (add_nonneg (hn 1) (hn 2)))
    have hden2 : channelDensity Q 0 z * 2 - channelDensity Q 0 z * θ 0 * 2 +
          channelDensity Q 3 z * 2 - channelDensity Q 3 z * θ 0 * 2 +
          channelDensity Q 1 z * θ 0 * 2 + channelDensity Q 2 z * θ 0 * 2 ≠ 0 := by
      intro hz
      nlinarith
    field_simp [hs, hden2]
    rw [show
      channelDensity Q 0 z + channelDensity Q 3 z +
          (channelDensity Q 1 z + channelDensity Q 2 z) +
        (channelDensity Q 0 z + channelDensity Q 3 z -
          (channelDensity Q 1 z + channelDensity Q 2 z)) * (1 - 2 * θ 0) =
      2 * ((1 - θ 0) * (channelDensity Q 0 z + channelDensity Q 3 z) +
        θ 0 * (channelDensity Q 1 z + channelDensity Q 2 z)) by ring]
    field_simp [ne_of_gt hdenpos]
    ring

/-- the grouped staircase atom assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hα), [the grouped Staircase atom](goal).

Under the stated assumptions, the grouped Staircase atom. -/
lemma groupedStaircase_atom (ε : ℝ) (α : StaircaseWeight)
    (hα : staircaseFeasible ε α) (b : Bool) (s : Fin 14) :
    ((groupedChannel (staircaseChannel ε α) b) {s}).toReal =
      if b then
        α s * (patternRay ε s 0 + patternRay ε s 3) / 2
      else
        α s * (patternRay ε s 1 + patternRay ε s 2) / 2 := by
  have hnonneg (j : Fin 4) : 0 ≤ α s * patternRay ε s j := by
    apply mul_nonneg (hα.1 s)
    unfold patternRay privacyIncrement privacyRatio
    split_ifs <;> simp <;> positivity
  have hrow (j : Fin 4) :
      ((staircaseChannel ε α) j {s}).toReal = α s * patternRay ε s j := by
    change (Measure.count.withDensity
      (fun u : Fin 14 => ENNReal.ofReal (α u * patternRay ε u j)) {s}).toReal = _
    rw [withDensity_apply _ (measurableSet_singleton s), lintegral_singleton]
    simp
    exact hnonneg j
  letI : IsMarkovKernel (staircaseChannel ε α) :=
    staircaseChannel_markov ε α hα
  have hfinite (j : Fin 4) : (staircaseChannel ε α) j {s} ≠ ∞ :=
    measure_ne_top _ _
  have hhalfReal : half.toReal = (1 / 2 : ℝ) := by
    rw [half, ENNReal.coe_toReal]
    rfl
  cases b
  · change (half * ((staircaseChannel ε α) 1 {s} +
        (staircaseChannel ε α) 2 {s})).toReal = _
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_add (hfinite 1) (hfinite 2)]
    rw [hrow, hrow]
    rw [hhalfReal]
    simp
    ring
  · change (half * ((staircaseChannel ε α) 0 {s} +
        (staircaseChannel ε α) 3 {s})).toReal = _
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_add (hfinite 0) (hfinite 3)]
    rw [hrow, hrow]
    rw [hhalfReal]
    simp
    ring

/-- [the pattern mass balanced assertion](goal) holds. For [the displayed quantities and conditions](hyp:hbalance,s), these specify the stated inputs. -/
lemma patternMass_balanced (θ : TrialParameter)
    (hbalance : θ 0 + θ 1 = 1) (ε : ℝ) (s : Fin 14) :
    patternMass θ (1 / 2) ε s =
      ((1 - θ 0) * (patternRay ε s 0 + patternRay ε s 3) +
        θ 0 * (patternRay ε s 1 + patternRay ε s 2)) / 2 := by
  unfold patternMass
  rw [show (∑ j : Fin 4, piTheta θ (1 / 2) j * patternRay ε s j) =
      piTheta θ (1 / 2) 0 * patternRay ε s 0 +
      piTheta θ (1 / 2) 1 * patternRay ε s 1 +
      piTheta θ (1 / 2) 2 * patternRay ε s 2 +
      piTheta θ (1 / 2) 3 * patternRay ε s 3 by
        simp [Fin.sum_univ_succ]; ring]
  have hθ1 : θ 1 = 1 - θ 0 := by linarith
  rw [piTheta_balanced_by_val, piTheta_balanced_by_val,
    piTheta_balanced_by_val, piTheta_balanced_by_val, hθ1]
  norm_num [controlProb]
  ring

/-- Under [the supplied quantities and conditions](hyp:s), [the projected gradient balanced assertion](goal) holds. -/
lemma projectedGradient_balanced (ε : ℝ) (s : Fin 14) :
    projectedGradient (1 / 2) ε s (-1 / 2) =
      (patternRay ε s 0 + patternRay ε s 3 -
        (patternRay ε s 1 + patternRay ε s 2)) / 4 := by
  cases h0 : patternContains s 0 <;>
    cases h1 : patternContains s 1 <;>
    cases h2 : patternContains s 2 <;>
    cases h3 : patternContains s 3 <;>
    simp [projectedGradient, patternGradient, patternRay, privacyIncrement,
      direction, controlProb, Fin.sum_univ_two, h0, h1, h2, h3] <;> ring

/-- Under the supplied quantities and conditions, the grouped staircase information eq objective assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hbalance,hε,hα), [the grouped Staircase information eq objective](goal).

Under the stated assumptions, the grouped Staircase information eq objective. -/
lemma groupedStaircase_information_eq_objective
    (θ : TrialParameter) (hθ : InteriorMeans θ)
    (hbalance : θ 0 + θ 1 = 1) (ε : ℝ) (hε : 0 < ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) :
    Causalean.Stat.Privacy.Binary.information
        (groupedChannel (staircaseChannel ε α)) (contrast θ) =
      informationObjective θ (1 / 2) ε α (-1 / 2) := by
  letI : IsMarkovKernel (staircaseChannel ε α) :=
    staircaseChannel_markov ε α hα
  letI : IsMarkovKernel (groupedChannel (staircaseChannel ε α)) :=
    groupedChannel_markov _
  rw [Causalean.Stat.Privacy.Binary.information_eq_discrete _ _
    (abs_contrast_lt_one θ hθ hbalance)]
  unfold Causalean.Stat.Privacy.Binary.discreteInformation informationObjective
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro s hs
  rw [groupedStaircase_atom ε α hα true s,
    groupedStaircase_atom ε α hα false s]
  simp
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
  unfold patternInformation
  rw [patternMass_balanced θ hbalance ε s,
    projectedGradient_balanced ε s]
  have hcontrast : contrast θ = 1 - 2 * θ 0 := by
    simp [contrast]
    linarith
  rw [hcontrast]
  by_cases ha : α s = 0
  · simp [ha]
  · have hm := patternMass_pos_interior θ (1 / 2) ε
      (by constructor <;> norm_num) hθ hε.le s
    have hmassne : ((1 - θ 0) * (patternRay ε s 0 + patternRay ε s 3) +
        θ 0 * (patternRay ε s 1 + patternRay ε s 2)) ≠ 0 := by
      intro h
      rw [patternMass_balanced θ hbalance ε s, h] at hm
      norm_num at hm
    have hd : (1 + (1 - 2 * θ 0)) *
          (α s * (patternRay ε s 0 + patternRay ε s 3) / 2) +
        (1 - (1 - 2 * θ 0)) *
          (α s * (patternRay ε s 1 + patternRay ε s 2) / 2) ≠ 0 := by
      rw [show
        (1 + (1 - 2 * θ 0)) *
              (α s * (patternRay ε s 0 + patternRay ε s 3) / 2) +
            (1 - (1 - 2 * θ 0)) *
              (α s * (patternRay ε s 1 + patternRay ε s 2) / 2) =
          α s * ((1 - θ 0) * (patternRay ε s 0 + patternRay ε s 3) +
            θ 0 * (patternRay ε s 1 + patternRay ε s 2)) by ring]
      exact mul_ne_zero ha hmassne
    field_simp [ha, hd, ne_of_gt hm]
    rw [show
      (patternRay ε s 0 + patternRay ε s 3) * (1 + (1 - 2 * θ 0)) +
          (patternRay ε s 1 + patternRay ε s 2) * (1 - (1 - 2 * θ 0)) =
      2 * ((1 - θ 0) * (patternRay ε s 0 + patternRay ε s 3) +
        θ 0 * (patternRay ε s 1 + patternRay ε s 2)) by ring]
    field_simp [hmassne]
    ring

/-- Under the supplied quantities and conditions, the information objective balanced le sharp assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hbalance,hε,hα), [the information Objective balanced le sharp](goal).

Under the stated assumptions, the information Objective balanced le sharp. -/
lemma informationObjective_balanced_le_sharp
    (θ : TrialParameter) (hθ : InteriorMeans θ)
    (hbalance : θ 0 + θ 1 = 1) (ε : ℝ) (hε : 0 < ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) :
    informationObjective θ (1 / 2) ε α (-1 / 2) ≤
      Causalean.Stat.Privacy.Binary.contraction ε ^ 2 /
        (1 - Causalean.Stat.Privacy.Binary.contraction ε ^ 2 *
          contrast θ ^ 2) := by
  letI : IsMarkovKernel (staircaseChannel ε α) :=
    staircaseChannel_markov ε α hα
  letI : IsMarkovKernel (groupedChannel (staircaseChannel ε α)) :=
    groupedChannel_markov _
  rw [← groupedStaircase_information_eq_objective θ hθ hbalance ε hε α hα]
  exact Causalean.Stat.Privacy.Binary.information_le_sharp
    (groupedChannel (staircaseChannel ε α)) ε (contrast θ) hε
      (abs_contrast_lt_one θ hθ hbalance)
      (groupedChannel_private _ ⟨inferInstance, fun A hA j j' =>
        staircaseChannel_private ε hε α hα A j j'⟩)

/-- Under the supplied quantities and conditions, the jstar balanced le sharp assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hbalance,hε), [the Jstar balanced le sharp](goal).

Under the stated assumptions, the Jstar balanced le sharp. -/
lemma Jstar_balanced_le_sharp
    (θ : TrialParameter) (hθ : InteriorMeans θ)
    (hbalance : θ 0 + θ 1 = 1) (ε : ℝ) (hε : 0 < ε) :
    Jstar θ (1 / 2) ε ≤
      Causalean.Stat.Privacy.Binary.contraction ε ^ 2 /
        (1 - Causalean.Stat.Privacy.Binary.contraction ε ^ 2 *
          contrast θ ^ 2) := by
  refine (Jstar_le_upperEnvelope θ (1 / 2) ε
    (by constructor <;> norm_num) hθ hε.le (-1 / 2)).trans ?_
  obtain ⟨α, hα, hupper⟩ :=
    upperEnvelope_attained θ (1 / 2) ε (-1 / 2) hε.le
  rw [hupper]
  exact informationObjective_balanced_le_sharp θ hθ hbalance ε hε α hα

end BalancedBinary

end CausalSmith.Stat.LdpAteEfficiencySurface
