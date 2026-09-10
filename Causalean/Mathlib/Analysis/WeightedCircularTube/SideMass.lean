import Causalean.Mathlib.Analysis.WeightedCircularTube.Basic
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Power-weighted mass on either side of the unit circle

This module proves uniform local-mass bounds for a radial power weight on both sides of the
Euclidean unit circle. It also gives a finite, strictly positive normalizing integral on every
nontrivial annular tube of width below one.
-/

noncomputable section

open Metric MeasureTheory Set
open scoped ENNReal NNReal Real Topology

namespace Causalean.Mathlib.Analysis.WeightedCircularTube

/-- For [a real exponent](hyp:κ), [a choice of the inside or outside of the unit circle](hyp:side), [a planar centre](hyp:x), and [a real radius](hyp:h), the [weighted side-ball mass](goal) is the two-dimensional Lebesgue integral of the radial power weight with that exponent over the corresponding one-sided open ball. -/
def sideBallMass (κ : ℝ) (side : CircleSide) (x : Plane) (h : ℝ) : ℝ :=
  ∫ z in sideBall side x h, powerWeight κ z ∂volume

private def comparisonBall (side : CircleSide) (h : ℝ) : Set Plane :=
  match side with
  | .inside => ball ((1 - h / 2 : ℝ) : Plane) (h / 4)
  | .outside => ball ((1 + h / 2 : ℝ) : Plane) (h / 4)

private theorem comparisonBall_subset_sideBall (side : CircleSide) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) : comparisonBall side h ⊆ sideBall side 1 h := by
  intro z hz
  have hquarter : 0 < h / 4 := by positivity
  cases side with
  | inside =>
      have hcenter : ‖((1 - h / 2 : ℝ) : Plane)‖ = 1 - h / 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg]
        linarith
      have hcenter_dist : dist (((1 - h / 2 : ℝ) : Plane)) 1 = h / 2 := by
        rw [dist_eq_norm]
        norm_cast
        rw [Real.norm_eq_abs, abs_of_nonpos]
        · ring
        · linarith
      have hdist : dist z ((1 - h / 2 : ℝ) : Plane) < h / 4 := hz
      have hball : dist z 1 < h := by
        calc
          dist z 1 ≤ dist z ((1 - h / 2 : ℝ) : Plane) +
              dist ((1 - h / 2 : ℝ) : Plane) 1 := dist_triangle _ _ _
          _ < h / 4 + h / 2 := by rw [hcenter_dist]; linarith
          _ < h := by linarith
      have hnorm : ‖z‖ < 1 := by
        calc
          ‖z‖ = ‖(z - ((1 - h / 2 : ℝ) : Plane)) +
              ((1 - h / 2 : ℝ) : Plane)‖ := by ring_nf
          _ ≤ ‖z - ((1 - h / 2 : ℝ) : Plane)‖ +
              ‖((1 - h / 2 : ℝ) : Plane)‖ := norm_add_le _ _
          _ < h / 4 + (1 - h / 2) := by
            rw [hcenter]
            gcongr
            simpa [dist_eq_norm] using hdist
          _ < 1 := by linarith
      exact ⟨hball, by simp [CircleSide.region, radialOffset]; linarith⟩
  | outside =>
      have hcenter : ‖((1 + h / 2 : ℝ) : Plane)‖ = 1 + h / 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg]
        linarith
      have hcenter_dist : dist (((1 + h / 2 : ℝ) : Plane)) 1 = h / 2 := by
        rw [dist_eq_norm]
        norm_cast
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · ring
        · linarith
      have hdist : dist z ((1 + h / 2 : ℝ) : Plane) < h / 4 := hz
      have hball : dist z 1 < h := by
        calc
          dist z 1 ≤ dist z ((1 + h / 2 : ℝ) : Plane) +
              dist ((1 + h / 2 : ℝ) : Plane) 1 := dist_triangle _ _ _
          _ < h / 4 + h / 2 := by rw [hcenter_dist]; linarith
          _ < h := by linarith
      have hnorm : 1 < ‖z‖ := by
        have hrev := norm_sub_norm_le ((1 + h / 2 : ℝ) : Plane) z
        rw [hcenter] at hrev
        rw [norm_sub_rev] at hrev
        have : ‖z - ((1 + h / 2 : ℝ) : Plane)‖ < h / 4 := by
          simpa [dist_eq_norm] using hdist
        linarith
      exact ⟨hball, by simp [CircleSide.region, radialOffset]; linarith⟩

private theorem comparisonBall_offset_lower (side : CircleSide) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) {z : Plane} (hz : z ∈ comparisonBall side h) :
    h / 4 ≤ |radialOffset z| := by
  cases side with
  | inside =>
      have hcenter : ‖((1 - h / 2 : ℝ) : Plane)‖ = 1 - h / 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg]
        linarith
      have hdist : ‖z - ((1 - h / 2 : ℝ) : Plane)‖ < h / 4 := by
        simpa [comparisonBall, dist_eq_norm] using hz
      have hnorm : ‖z‖ < 1 - h / 4 := by
        calc
          ‖z‖ = ‖(z - ((1 - h / 2 : ℝ) : Plane)) +
              ((1 - h / 2 : ℝ) : Plane)‖ := by ring_nf
          _ ≤ ‖z - ((1 - h / 2 : ℝ) : Plane)‖ +
              ‖((1 - h / 2 : ℝ) : Plane)‖ := norm_add_le _ _
          _ < h / 4 + (1 - h / 2) := by rw [hcenter]; gcongr
          _ = 1 - h / 4 := by ring
      rw [radialOffset, abs_of_nonpos (by linarith)]
      linarith
  | outside =>
      have hcenter : ‖((1 + h / 2 : ℝ) : Plane)‖ = 1 + h / 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg]
        linarith
      have hdist : ‖z - ((1 + h / 2 : ℝ) : Plane)‖ < h / 4 := by
        simpa [comparisonBall, dist_eq_norm] using hz
      have hrev := norm_sub_norm_le ((1 + h / 2 : ℝ) : Plane) z
      rw [hcenter] at hrev
      rw [norm_sub_rev] at hrev
      have hnorm : 1 + h / 4 < ‖z‖ := by linarith
      rw [radialOffset, abs_of_nonneg (by linarith)]
      linarith

private theorem comparisonBall_volume_real (side : CircleSide) {h : ℝ} (hh : 0 < h) :
    volume.real (comparisonBall side h) = (h / 4) ^ 2 * Real.pi := by
  have hq : 0 ≤ h / 4 := by positivity
  cases side <;> simp [comparisonBall, Measure.real, ENNReal.toReal_ofReal, hq]

/-- When [the exponent κ exceeds two](hyp:hκ), [the radial power weight is integrable over the
one-sided ball determined by the chosen side, center, and radius](hyp:side,x,h) [and hence its
weighted mass is finite](goal). -/
theorem sideBallMass_integrable {κ : ℝ} (hκ : 2 < κ)
    (side : CircleSide) (x : Plane) (h : ℝ) :
    IntegrableOn (powerWeight κ) (sideBall side x h) := by
  exact integrableOn_powerWeight_sideBall hκ side x h

/-- When [the exponent κ exceeds two](hyp:hκ), [the weighted mass of the one-sided ball determined
by the chosen side, center, and radius](hyp:side,x,h) [is nonnegative](goal). -/
theorem sideBallMass_nonneg {κ : ℝ} (hκ : 2 < κ)
    (side : CircleSide) (x : Plane) (h : ℝ) :
    0 ≤ sideBallMass κ side x h := by
  exact setIntegral_nonneg (measurableSet_sideBall side x h)
    (fun z _ => powerWeight_nonneg κ z)

/-- For [a chosen radial side](hyp:side) and [a center on the unit circle](hyp:hx), [rotating that
center to the reference point one leaves its weighted side-ball mass unchanged](goal). -/
theorem sideBallMass_eq_reference {κ h : ℝ} (side : CircleSide)
    {x : Plane} (hx : x ∈ unitCircle) :
    sideBallMass κ side x h = sideBallMass κ side 1 h := by
  let u : Circle := ⟨x, by
    simpa [unitCircle, Submonoid.unitSphere, mem_sphere, dist_zero_right] using hx⟩
  let e : Plane ≃ₗᵢ[ℝ] Plane := rotation u
  have he_apply (z : Plane) : e z = x * z := rfl
  have he_meas : MeasurableEmbedding e := e.continuous.measurableEmbedding e.injective
  have he_pres : MeasurePreserving e volume volume := e.measurePreserving
  have hpre : e ⁻¹' sideBall side x h = sideBall side 1 h := by
    cases side with
    | inside =>
        ext z
        change (dist (e z) x < h ∧ radialOffset (e z) ≤ 0) ↔
          (dist z 1 < h ∧ radialOffset z ≤ 0)
        rw [he_apply, dist_mul_one_of_mem_unitCircle hx,
          radialOffset_mul_of_mem_unitCircle hx]
    | outside =>
        ext z
        change (dist (e z) x < h ∧ 0 < radialOffset (e z)) ↔
          (dist z 1 < h ∧ 0 < radialOffset z)
        rw [he_apply, dist_mul_one_of_mem_unitCircle hx,
          radialOffset_mul_of_mem_unitCircle hx]
  unfold sideBallMass
  rw [← he_pres.setIntegral_preimage_emb he_meas (powerWeight κ) (sideBall side x h), hpre]
  apply setIntegral_congr_fun (measurableSet_sideBall side 1 h)
  intro z hz
  change powerWeight κ (e z) = powerWeight κ z
  rw [he_apply]
  unfold powerWeight
  rw [radialOffset_mul_of_mem_unitCircle hx]

/-- When [the allowed exponent ceiling exceeds two](hyp:hκMax) and [the maximum scale is positive
and below one](hyp:hh0pos,hh0lt), [there are positive constants, uniform over both radial sides,
all exponents between two and that ceiling, and all positive scales up to that maximum, which
bound the reference one-sided weighted mass above and below by constant multiples of the scale to
the exponent](goal). -/
theorem reference_powerWeighted_sideBall_bounds
    {κMax h0 : ℝ} (hκMax : 2 < κMax) (hh0pos : 0 < h0) (hh0lt : h0 < 1) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ (κ : ℝ) (side : CircleSide) (h : ℝ),
        2 < κ → κ ≤ κMax → 0 < h → h ≤ h0 →
          c * h ^ κ ≤ sideBallMass κ side 1 h ∧
            sideBallMass κ side 1 h ≤ C * h ^ κ := by
  refine ⟨Real.pi / 4 ^ κMax, Real.pi, ?_, ?_, ?_⟩
  · exact div_pos Real.pi_pos (Real.rpow_pos_of_pos (by norm_num) _)
  · have hpow : 1 ≤ (4 : ℝ) ^ κMax :=
      Real.one_le_rpow (by norm_num) (by linarith)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) κMax)).2
      (by nlinarith [Real.pi_pos])
  · intro κ side h hκ hκle hh hh0
    have hh1 : h < 1 := lt_of_le_of_lt hh0 hh0lt
    have hexp : 0 ≤ κ - 2 := by linarith
    have hsideint := integrableOn_powerWeight_sideBall hκ side (1 : Plane) h
    have hballint : IntegrableOn (powerWeight κ) (ball (1 : Plane) h) := by
      have hc : IntegrableOn (powerWeight κ) (closedBall (1 : Plane) h) :=
        (continuous_powerWeight hκ).locallyIntegrable.integrableOn_isCompact
          (isCompact_closedBall (1 : Plane) h)
      exact Integrable.mono_measure hc
        (Measure.restrict_mono ball_subset_closedBall le_rfl)
    have hoff_upper : ∀ z ∈ ball (1 : Plane) h, powerWeight κ z ≤ h ^ (κ - 2) := by
      intro z hz
      have hoff : |radialOffset z| ≤ dist z 1 := by
        simpa [radialOffset, dist_eq_norm] using abs_norm_sub_norm_le z (1 : Plane)
      exact Real.rpow_le_rpow (abs_nonneg _) (hoff.trans (le_of_lt hz)) hexp
    have hmass_upper : sideBallMass κ side 1 h ≤ Real.pi * h ^ κ := by
      have hset : sideBall side 1 h ⊆ ball (1 : Plane) h := inter_subset_left
      have hmono : sideBallMass κ side 1 h ≤
          ∫ z in ball (1 : Plane) h, powerWeight κ z ∂volume := by
        exact setIntegral_mono_set hballint
          (Filter.Eventually.of_forall fun z => powerWeight_nonneg κ z) hset.eventuallyLE
      have hnorm := norm_setIntegral_le_of_norm_le_const
        (show volume (ball (1 : Plane) h) < ∞ from measure_ball_lt_top)
        (fun z hz => by
          rw [Real.norm_of_nonneg (powerWeight_nonneg κ z)]
          exact hoff_upper z hz)
      have hnonneg : 0 ≤ ∫ z in ball (1 : Plane) h, powerWeight κ z ∂volume :=
        setIntegral_nonneg (s := ball (1 : Plane) h) measurableSet_ball
          (fun z _ => powerWeight_nonneg κ z)
      have hvol : volume.real (ball (1 : Plane) h) = h ^ 2 * Real.pi := by
        simp [Measure.real, hh.le]
      rw [Real.norm_of_nonneg hnonneg, hvol] at hnorm
      calc
        sideBallMass κ side 1 h ≤ _ := hmono
        _ ≤ h ^ (κ - 2) * (h ^ 2 * Real.pi) := hnorm
        _ = Real.pi * h ^ κ := by
          rw [show κ = (κ - 2) + 2 by ring, Real.rpow_add hh, Real.rpow_two]
          ring_nf
    have hcompint : IntegrableOn (powerWeight κ) (comparisonBall side h) :=
      Integrable.mono_measure hsideint
        (Measure.restrict_mono (comparisonBall_subset_sideBall side hh hh1) le_rfl)
    have hlower_point : ∀ z ∈ comparisonBall side h,
        (h / 4) ^ (κ - 2) ≤ powerWeight κ z := by
      intro z hz
      exact Real.rpow_le_rpow (by positivity)
        (comparisonBall_offset_lower side hh hh1 hz) hexp
    have hcomp_lower : Real.pi * (h / 4) ^ κ ≤
        ∫ z in comparisonBall side h, powerWeight κ z ∂volume := by
      have hfinite : volume (comparisonBall side h) ≠ ∞ := by
        exact (show volume (comparisonBall side h) < ∞ by
          cases side <;> exact measure_ball_lt_top).ne
      have hge := setIntegral_ge_of_const_le_real
        (show MeasurableSet (comparisonBall side h) by
          cases side <;> exact measurableSet_ball)
        hfinite hlower_point hcompint
      rw [comparisonBall_volume_real side hh] at hge
      calc
        Real.pi * (h / 4) ^ κ =
            (h / 4) ^ (κ - 2) * ((h / 4) ^ 2 * Real.pi) := by
          rw [show κ = (κ - 2) + 2 by ring,
            Real.rpow_add (by positivity), Real.rpow_two]
          ring_nf
        _ ≤ _ := hge
    have hcomp_mono : (∫ z in comparisonBall side h, powerWeight κ z ∂volume) ≤
        sideBallMass κ side 1 h := by
      exact setIntegral_mono_set hsideint
        (Filter.Eventually.of_forall fun z => powerWeight_nonneg κ z)
        (comparisonBall_subset_sideBall side hh hh1).eventuallyLE
    have h4mono : (4 : ℝ) ^ κ ≤ 4 ^ κMax :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hκle
    have hdiv : h ^ κ / 4 ^ κMax ≤ h ^ κ / 4 ^ κ :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hh.le κ)
        (Real.rpow_pos_of_pos (by norm_num) κ) h4mono
    have hscale : (Real.pi / 4 ^ κMax) * h ^ κ ≤ Real.pi * (h / 4) ^ κ := by
      calc
        (Real.pi / 4 ^ κMax) * h ^ κ = Real.pi * (h ^ κ / 4 ^ κMax) := by ring
        _ ≤ Real.pi * (h ^ κ / 4 ^ κ) :=
          mul_le_mul_of_nonneg_left hdiv Real.pi_pos.le
        _ = Real.pi * (h / 4) ^ κ := by
          rw [Real.div_rpow hh.le (by norm_num : (0 : ℝ) ≤ 4)]
    exact ⟨hscale.trans (hcomp_lower.trans hcomp_mono), hmass_upper⟩

/-- When [the allowed exponent ceiling exceeds two](hyp:hκMax) and [the maximum scale is positive
and below one](hyp:hh0pos,hh0lt), [there are positive constants, uniform over every unit-circle
center, either radial side, all exponents between two and that ceiling, and all positive scales up
to that maximum, which bound one-sided weighted mass above and below by constant multiples of the
scale to the exponent](goal). -/
theorem unitCircle_powerWeighted_sideBall_bounds
    {κMax h0 : ℝ} (hκMax : 2 < κMax) (hh0pos : 0 < h0) (hh0lt : h0 < 1) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ (κ : ℝ) (x : Plane) (side : CircleSide) (h : ℝ),
        2 < κ → κ ≤ κMax → x ∈ unitCircle → 0 < h → h ≤ h0 →
          c * h ^ κ ≤ sideBallMass κ side x h ∧
            sideBallMass κ side x h ≤ C * h ^ κ := by
  obtain ⟨c, C, hc, hcC, hbounds⟩ :=
    reference_powerWeighted_sideBall_bounds hκMax hh0pos hh0lt
  refine ⟨c, C, hc, hcC, ?_⟩
  intro κ x side h hκ hκle hx hh hh0
  rw [sideBallMass_eq_reference side hx]
  exact hbounds κ side h hκ hκle hh hh0

/-- For [a real tube width](hyp:δ), the [annular tube](goal) is the set of planar points whose absolute radial distance from the unit circle is strictly less than $\delta$. -/
def annularTube (δ : ℝ) : Set Plane := {z | |radialOffset z| < δ}

/-- For [a tube width](hyp:δ), [the corresponding annular tube](goal) is Lebesgue measurable. -/
theorem measurableSet_annularTube (δ : ℝ) : MeasurableSet (annularTube δ) := by
  exact measurableSet_lt ((continuous_norm.sub continuous_const).abs.measurable) measurable_const

/-- When [the exponent κ exceeds two](hyp:hκ) and [the tube width is below one](hyp:hδ), [the
radial power weight is integrable over that annular tube](goal). -/
theorem integrableOn_powerWeight_annularTube {κ δ : ℝ} (hκ : 2 < κ) (hδ : δ < 1) :
    IntegrableOn (powerWeight κ) (annularTube δ) := by
  have hsub : annularTube δ ⊆ closedBall (0 : Plane) 2 := by
    intro z hz
    have hoff : |radialOffset z| < 1 := lt_trans hz hδ
    have hnorm : ‖z‖ < 2 := by
      have := (le_abs_self (radialOffset z)).trans_lt hoff
      dsimp [radialOffset] at this
      linarith
    simpa [mem_closedBall, dist_zero_right] using hnorm.le
  have hclosed : IntegrableOn (powerWeight κ) (closedBall (0 : Plane) 2) :=
    (continuous_powerWeight hκ).locallyIntegrable.integrableOn_isCompact
      (isCompact_closedBall (0 : Plane) 2)
  exact Integrable.mono_measure hclosed (Measure.restrict_mono hsub le_rfl)

/-- For [a real exponent](hyp:κ) and [a real tube width](hyp:δ), the [weighted annular normalizer](goal) is the two-dimensional Lebesgue integral of the radial power weight with that exponent over the annular tube of that width. -/
def annularNormalizer (κ δ : ℝ) : ℝ :=
  ∫ z in annularTube δ, powerWeight κ z ∂volume

/-- When [the exponent κ exceeds two](hyp:hκ) and [the tube width is positive and below one](hyp:hδpos,hδlt), [the radial power weight is integrable on that annular tube and its weighted
normalizer is strictly positive](goal). -/
theorem annularNormalizer_finite_pos {κ δ : ℝ}
    (hκ : 2 < κ) (hδpos : 0 < δ) (hδlt : δ < 1) :
    IntegrableOn (powerWeight κ) (annularTube δ) ∧ 0 < annularNormalizer κ δ := by
  have hint := integrableOn_powerWeight_annularTube hκ hδlt
  refine ⟨hint, ?_⟩
  obtain ⟨c, C, hc, hcC, hbounds⟩ :=
    reference_powerWeighted_sideBall_bounds hκ hδpos hδlt
  have hb := (hbounds κ CircleSide.outside δ hκ (le_refl κ) hδpos (le_refl δ)).1
  have hpowpos : 0 < δ ^ κ := Real.rpow_pos_of_pos hδpos κ
  have hsidepos : 0 < sideBallMass κ CircleSide.outside 1 δ :=
    lt_of_lt_of_le (mul_pos hc hpowpos) hb
  have hsub : sideBall CircleSide.outside 1 δ ⊆ annularTube δ := by
    intro z hz
    rcases hz with ⟨hzball, hzside⟩
    have hoffpos : 0 < radialOffset z := hzside
    have hoffle : |radialOffset z| ≤ dist z 1 := by
      simpa [radialOffset, dist_eq_norm] using abs_norm_sub_norm_le z (1 : Plane)
    exact lt_of_le_of_lt hoffle hzball
  have hmono : sideBallMass κ CircleSide.outside 1 δ ≤ annularNormalizer κ δ := by
    exact setIntegral_mono_set hint
      (Filter.Eventually.of_forall fun z => powerWeight_nonneg κ z) hsub.eventuallyLE
  exact hsidepos.trans_le hmono

end Causalean.Mathlib.Analysis.WeightedCircularTube
