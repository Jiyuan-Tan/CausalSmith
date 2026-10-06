module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.UpperGuarantees
public import Causalean.Stat.Privacy.LaplaceKernelMoments
/-! Exact centered Laplace release moments and the uniform density-free squared-error guarantee. -/
public section
open MeasureTheory ProbabilityTheory Causalean.Stat.Privacy
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The constructed pair release is the measurable Laplace kernel.  [the theorem's stated inputs and assumptions](hyp:he), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon). -/
-- @node: privateRatioRelease_eq_laplaceKernel
lemma privateRatioRelease_eq_laplaceKernel (n k : ℕ) (epsilon h : ℝ)
    (he : 0 < epsilon) :
    privateRatioRelease n epsilon h k = laplaceMechPiKernel (12/epsilon)
      (by positivity) (pairQuery n h k) (measurable_pairQuery n h k) := by
  ext D E : 2
  rw [laplaceMechPiKernel_apply]
  rfl

/-- The released coordinate squares add exactly two independent Laplace variances to the
input variances, with no inflation of the noise coefficient.  [the theorem's stated inputs and assumptions](hyp:he,hh,hk,P), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon). -/
-- @node: privateRatioRelease_centered_moments
lemma privateRatioRelease_centered_moments (n k : ℕ) (epsilon h : ℝ)
    (he : 0 < epsilon) (hh : 0 < h) (hk : 0 < k) (P : CausalLaw) :
    (∫ v, (v 0-Nbar n h k (dataLaw n P))^2 +
      (v 1-Dbar n h k (dataLaw n P))^2
      ∂(privateRatioRelease n epsilon h k ∘ₘ dataLaw n P)) =
      variance (SN n h k) (dataLaw n P) + variance (SD n h k) (dataLaw n P) +
        576/epsilon^2 := by
  letI : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  have hLp := statistic_memLp n k h hh hk (dataLaw n P) 2
  have hN : Integrable (fun D => (pairQuery n h k D 0)^2) (dataLaw n P) := by
    simpa [pairQuery] using hLp.1.integrable_sq
  have hD : Integrable (fun D => (pairQuery n h k D 1)^2) (dataLaw n P) := by
    simpa [pairQuery] using hLp.2.integrable_sq
  rw [privateRatioRelease_eq_laplaceKernel n k epsilon h he]
  have hiN := laplaceMechPiKernel_integrable_coord_sub_sq (12/epsilon) (by positivity)
    (pairQuery n h k) (measurable_pairQuery n h k) (dataLaw n P) 0 hN
    (Nbar n h k (dataLaw n P))
  have hiD := laplaceMechPiKernel_integrable_coord_sub_sq (12/epsilon) (by positivity)
    (pairQuery n h k) (measurable_pairQuery n h k) (dataLaw n P) 1 hD
    (Dbar n h k (dataLaw n P))
  rw [integral_add hiN hiD,
    laplaceMechPiKernel_integral_coord_sub_sq _ _ _ _ _ 0 hN,
    laplaceMechPiKernel_integral_coord_sub_sq _ _ _ _ _ 1 hD,
    variance_eq_integral (by fun_prop : AEMeasurable (SN n h k) (dataLaw n P)),
    variance_eq_integral (by fun_prop : AEMeasurable (SD n h k) (dataLaw n P))]
  simp only [pairQuery, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Nbar, Dbar]
  ring

/-- Integrating the pointwise floored-ratio bound and exact release moments proves the public
second-moment envelope throughout the complete model.  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon,h,hn,hk,he,hh,P,hP), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:efronStein_of_gate). -/
-- @node: Thk_model_squared_error_le
lemma Thk_model_squared_error_le (efronStein_of_gate : EfronSteinReplacement)
    (n k : ℕ) (epsilon h : ℝ) (hn : 2 ≤ n) (hk : 2 ≤ k)
    (he : 0 < epsilon) (hh : 0 < h ∧ h ≤ 1/4) (P : CausalLaw)
    (hP : CompleteModel P) :
    (∫⁻ u, ENNReal.ofReal ((u-theta P)^2) ∂(Thk n epsilon h k ∘ₘ dataLaw n P)) ≤
      ENNReal.ofReal (Vbound n epsilon h k) := by
  letI : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  letI := privateRatioRelease_markov n k epsilon h he
  let Q := privateRatioRelease n epsilon h k ∘ₘ dataLaw n P
  let f := fun v : Fin 2 → ℝ => (v 0-Nbar n h k (dataLaw n P))^2 +
    (v 1-Dbar n h k (dataLaw n P))^2
  have hLp := statistic_memLp n k h hh.1 (by omega) (dataLaw n P) 2
  have hi (i : Fin 2) (c : ℝ) : Integrable (fun v => (v i-c)^2) Q := by
    dsimp [Q]
    rw [privateRatioRelease_eq_laplaceKernel n k epsilon h he]
    apply laplaceMechPiKernel_integrable_coord_sub_sq
    fin_cases i
    · simpa [pairQuery] using hLp.1.integrable_sq
    · simpa [pairQuery] using hLp.2.integrable_sq
  have hif : Integrable f Q := (hi 0 _).add (hi 1 _)
  have hrhs : Integrable (fun v => 2*(bias h k)^2 + 4/(d0 n h k)^2 * f v) Q :=
    (integrable_const _).add (hif.const_mul _)
  have hbound := ratioMap_model_squared_error_le n k h hn hk hh P hP
  have hierr : Integrable (fun v => (ratioMap n h k v-theta P)^2) Q := by
    apply hrhs.mono' (by fun_prop)
    apply ae_of_all
    intro v
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ratioMap n h k v-theta P))]
    exact hbound v
  have hvar := (all_count_stability efronStein_of_gate n k h hn hk hh P
    (dataLaw n P) rfl hP).2
  have hmom : (∫ v, f v ∂Q) ≤ 36*Wocc n h k P + 576/epsilon^2 := by
    rw [show (∫ v, f v ∂Q) = _ from
      privateRatioRelease_centered_moments n k epsilon h he hh.1 (by omega) P]
    linarith [le_max_left (variance (SN n h k) (dataLaw n P))
      (variance (SD n h k) (dataLaw n P)),
      le_max_right (variance (SN n h k) (dataLaw n P))
        (variance (SD n h k) (dataLaw n P))]
  have herr : (∫ v, (ratioMap n h k v-theta P)^2 ∂Q) ≤ Vbound n epsilon h k := by
    calc
      _ ≤ ∫ v, (2*(bias h k)^2 + 4/(d0 n h k)^2 * f v) ∂Q :=
        integral_mono hierr hrhs hbound
      _ = 2*(bias h k)^2 + 4/(d0 n h k)^2 * (∫ v, f v ∂Q) := by
        rw [integral_add (integrable_const _) (hif.const_mul _), integral_const_mul]
        simp [integral_const_mul]
      _ ≤ 2*(bias h k)^2 + 4/(d0 n h k)^2 *
          (36*Wocc n h k P + 576/epsilon^2) := by
        gcongr
      _ = 2*(bias h k)^2 + 144*Wocc n h k P/(d0 n h k)^2 +
          2304/(epsilon^2*(d0 n h k)^2) := by ring
      _ ≤ _ := model_variance_envelope_le n k epsilon h hn hk he hh P hP
  rw [Thk_squared_error_eq, ← ofReal_integral_eq_lintegral_ofReal hierr
    (ae_of_all _ (fun v => sq_nonneg (ratioMap n h k v-theta P)))]
  exact ENNReal.ofReal_le_ofReal herr

end CausalSmith.Stat.PrivateCateRoughdesign
