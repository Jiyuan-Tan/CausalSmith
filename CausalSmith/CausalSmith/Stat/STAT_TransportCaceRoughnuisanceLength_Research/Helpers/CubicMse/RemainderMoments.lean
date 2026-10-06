module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.PilotEighthMoment
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.TaylorRemainder
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ExactStatisticBridge
public import Mathlib.Analysis.MeanInequalities

/-! # Pointwise second moment of the exact cubic Taylor remainder

The finite-dimensional Jensen inequality and the clipped pilot eighth moment
control the squared remainder with the constants in roadmap (9). The spatial
integral and the projection-bias assembly remain separate proof obligations.
-/

public section

open MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @node: sum_abs_eighth_le
/-- Given [the supplied inputs](hyp:v), [the stated result about sum abs eighth le holds](goal). -/
lemma sum_abs_eighth_le (v : Fin 7 → ℝ) :
    (∑ i, |v i|) ^ (8 : ℕ) ≤ (7 : ℝ) ^ (7 : ℕ) * ∑ i, |v i| ^ (8 : ℕ) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := Finset.univ) (f := fun i => |v i|) (p := (8 : ℝ))
    (by norm_num) (fun i _ => abs_nonneg (v i))
  norm_num [Real.rpow_natCast] at h
  norm_num
  exact h

-- @node: clippingRectangle_coordinate_abs_le
/-- Given [the supplied inputs](hyp:c_f,C_f,hc,hC,v,hv,i), [the stated result about clipping rectangle coordinate abs le holds](goal). -/
lemma clippingRectangle_coordinate_abs_le (c_f C_f : ℝ) (hc : 0 < c_f)
    (hC : 0 ≤ C_f) (v : Fin 7 → ℝ) (hv : clippingRectangle c_f C_f v)
    (i : Fin 7) : |v i| ≤ C_f := by
  rcases hv with ⟨h0, h1, h2, hr⟩
  fin_cases i
  · change |v 0| ≤ C_f
    rw [abs_of_nonneg (hc.le.trans h0.1)]; exact h0.2
  · change |v 1| ≤ C_f
    rw [abs_of_nonneg (by linarith [h1.1] : 0 ≤ v 1)]; linarith [h1.2]
  · change |v 2| ≤ C_f
    rw [abs_of_nonneg (by linarith [h2.1] : 0 ≤ v 2)]; linarith [h2.2]
  · change |v 3| ≤ C_f
    have h := hr 3 (by norm_num)
    rw [abs_of_nonneg h.1]; linarith [h.2]
  · change |v 4| ≤ C_f
    have h := hr 4 (by norm_num)
    rw [abs_of_nonneg h.1]; linarith [h.2]
  · change |v 5| ≤ C_f
    have h := hr 5 (by norm_num)
    rw [abs_of_nonneg h.1]; linarith [h.2]
  · change |v 6| ≤ C_f
    have h := hr 6 (by norm_num)
    rw [abs_of_nonneg h.1]; linarith [h.2]

-- @node: integrable_pilot_error_eighth
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hn,hP,x,hx,i), [the stated result about integrable pilot error eighth holds](goal). -/
lemma integrable_pilot_error_eighth (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (x : ℝ) (hx : x ∈ covariateSpace) (i : Fin 7) :
    Integrable (fun ω => |pilot c_f C_f ω x i -
      markedDensityVector c_f C_f L P n hP x i| ^ (8 : ℕ)) (dataLaw P n n) := by
  letI : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  letI : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hprob : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]; infer_instance
  letI := hprob
  have hc := hP.sourceBounds.1.1
  have hC : 0 ≤ C_f := le_trans (by norm_num) hP.sourceBounds.2.1.le
  have hm : Measurable (fun ω : TwoSample n n => |pilot c_f C_f ω x i -
      markedDensityVector c_f C_f L P n hP x i| ^ (8 : ℕ)) := by
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable ((2 * C_f) ^ (8 : ℕ))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply pow_le_pow_left₀ (abs_nonneg _) _
  simpa only [two_mul] using (abs_sub _ _).trans (add_le_add
    (clippingRectangle_coordinate_abs_le c_f C_f hc hC _
      (pilot_mem_clippingRectangle c_f C_f L P n hn hP ω x) i)
    (clippingRectangle_coordinate_abs_le c_f C_f hc hC _
      (markedDensityVector_mem_clippingRectangle c_f C_f L P n hP x hx) i))

-- @node: pilot_Phi_cubic_taylor_remainder_second_moment
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hn,hP,A,x,hx), [the stated result about pilot phi cubic taylor remainder second moment holds](goal). -/
lemma pilot_Phi_cubic_taylor_remainder_second_moment
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool)
    (x : ℝ) (hx : x ∈ covariateSpace) :
    (∫ ω, (let v := pilot c_f C_f ω x
      let h := markedDensityVector c_f C_f L P n hP x - v
      Phi A (markedDensityVector c_f C_f L P n hP x) - (Phi A v +
        iteratedFDeriv ℝ 1 (Phi A) v ![h] +
        iteratedFDeriv ℝ 2 (Phi A) v ![h, h] / 2 +
        iteratedFDeriv ℝ 3 (Phi A) v ![h, h, h] / 6)) ^ 2 ∂dataLaw P n n) ≤
      (fourthDerivativeEnvelope c_f C_f / 24) ^ 2 * (7 : ℝ) ^ (8 : ℕ) *
        pilotEighthConstant C_f L * (n : ℝ) ^ (-(4 / 5 : ℝ)) := by
  let μ := dataLaw P n n
  let e (ω : TwoSample n n) (i : Fin 7) :=
    pilot c_f C_f ω x i - markedDensityVector c_f C_f L P n hP x i
  let B := (fourthDerivativeEnvelope c_f C_f / 24) ^ 2 * (7 : ℝ) ^ (7 : ℕ)
  have hi (i : Fin 7) : Integrable (fun ω => |e ω i| ^ (8 : ℕ)) μ :=
    integrable_pilot_error_eighth c_f C_f L P n hn hP x hx i
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∫ ω, B * ∑ i, |e ω i| ^ (8 : ℕ) ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        ((integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul B)
      filter_upwards [] with ω
      have ht := pilot_Phi_cubic_taylor_remainder_abs_le c_f C_f L P n hn hP A ω x hx
      have hp := pow_le_pow_left₀ (abs_nonneg _) ht 2
      rw [sq_abs] at hp
      calc
        _ ≤ _ := hp
        _ = (fourthDerivativeEnvelope c_f C_f / 24) ^ 2 *
            (∑ i, |e ω i|) ^ (8 : ℕ) := by
          simp only [Pi.sub_apply, abs_sub_comm, e, mul_pow, ← pow_mul]
        _ ≤ _ := by
          dsimp only [B]
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (sum_abs_eighth_le (e ω)) (sq_nonneg _)
    _ = B * ∑ i, ∫ ω, |e ω i| ^ (8 : ℕ) ∂μ := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hi i)]
    _ ≤ B * ∑ _i : Fin 7, pilotEighthConstant C_f L *
        (n : ℝ) ^ (-(4 / 5 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact Finset.sum_le_sum fun i _ => pilot_eighth_moment c_f C_f L P n hn hP i x hx
    _ = _ := by simp [B]; ring

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
