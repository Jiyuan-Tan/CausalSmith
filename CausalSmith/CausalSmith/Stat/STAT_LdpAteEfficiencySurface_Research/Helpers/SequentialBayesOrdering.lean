module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialLocalRiskOrder

/-! # Compact-prior Bayes risk versus local worst risk -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
open Causalean.Stat.Minimax.ObservationDependentVanTrees

/-- Scalar multiplication of a trial-parameter direction. For [the displayed inputs and conditions](hyp:a,v), [the stated result](goal) follows. -/
def scaledDirection (a : ℝ) (v : TrialParameter) : TrialParameter :=
  fun k => a * v k

/-- Euclidean norm scales by the absolute scalar along a trial direction. For [the displayed inputs and conditions](hyp:a,v), [the stated result](goal) follows. -/
lemma norm_scaledDirection (a : ℝ) (v : TrialParameter) :
    Real.sqrt (((scaledDirection a v) 0) ^ 2 +
      ((scaledDirection a v) 1) ^ 2) =
      |a| * Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2) := by
  unfold scaledDirection
  rw [show (a * v 0) ^ 2 + (a * v 1) ^ 2 =
    a ^ 2 * ((v 0) ^ 2 + (v 1) ^ 2) by ring]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-- The scalar directions indexed by `[-R,R]` fit in the radius obtained by
multiplying `R` by the Euclidean norm of the base direction. For [the displayed inputs and conditions](hyp:v), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:ha), these specify the stated inputs. -/
lemma scaledDirection_mem_cover {R a : ℝ} (v : TrialParameter)
    (ha : a ∈ Icc (-R) R) :
    Real.sqrt (((scaledDirection a v) 0) ^ 2 +
      ((scaledDirection a v) 1) ^ 2) ≤
      R * Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2) := by
  rw [norm_scaledDirection]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  rw [abs_le]
  exact ⟨ha.1, ha.2⟩

/-- An integrable nonnegative real density normalized in the Bochner integral
is also normalized after embedding into `ENNReal`. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:mu,w,hwint,hw_nonneg,hnorm), these specify the stated inputs. -/
lemma lintegral_ofReal_eq_one_of_integral_eq_one {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (w : A → ℝ) (hwint : Integrable w mu)
    (hw_nonneg : ∀ᵐ a ∂mu, 0 ≤ w a) (hnorm : ∫ a, w a ∂mu = 1) :
    ∫⁻ a, ENNReal.ofReal (w a) ∂mu = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal hwint hw_nonneg, hnorm,
    ENNReal.ofReal_one]

/-- A normalized nonnegative weight preserves a uniform `ENNReal` upper bound
under integration. The measurability conclusion records the exact hypothesis
needed by later product and iterated-integral rewrites. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:mu,w,f,B,hw,hf,hwint,hw_nonneg,hnorm,hle), these specify the stated inputs. -/
lemma weighted_lintegral_le_uniform {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (w : A → ℝ) (f : A → ℝ≥0∞) (B : ℝ≥0∞)
    (hw : Measurable w) (hf : AEMeasurable f mu)
    (hwint : Integrable w mu) (hw_nonneg : ∀ᵐ a ∂mu, 0 ≤ w a)
    (hnorm : ∫ a, w a ∂mu = 1)
    (hle : ∀ᵐ a ∂mu, f a ≤ B) :
    AEMeasurable (fun a => ENNReal.ofReal (w a) * f a) mu ∧
      (∫⁻ a, ENNReal.ofReal (w a) * f a ∂mu) ≤ B := by
  have hwm : AEMeasurable (fun a => ENNReal.ofReal (w a)) mu :=
    (ENNReal.measurable_ofReal.comp hw).aemeasurable
  constructor
  · exact hwm.mul hf
  · calc
      (∫⁻ a, ENNReal.ofReal (w a) * f a ∂mu) ≤
          ∫⁻ a, ENNReal.ofReal (w a) * B ∂mu := by
            apply lintegral_mono_ae
            filter_upwards [hle] with a ha
            gcongr
      _ = (∫⁻ a, ENNReal.ofReal (w a) ∂mu) * B :=
        lintegral_mul_const B (ENNReal.measurable_ofReal.comp hw)
      _ = B := by rw [lintegral_ofReal_eq_one_of_integral_eq_one
        mu w hwint hw_nonneg hnorm, one_mul]

/-- If a compact family of scalar directions fits inside radius `H`, then at
all sufficiently large sample sizes its normalized Bayes average risk is at
most the local worst risk at that radius. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,theta,v,p,H,ell,upper,htheta,w,hw,hwint,hw_nonneg,hnorm,hcover,hriskMeas), these specify the stated inputs. -/
lemma eventually_compactPrior_bayesRisk_le_localWorstRisk
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (theta v : TrialParameter) (p H ell upper : ℝ)
    (htheta : InteriorMeans theta)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hwint : Integrable w (parameterMeasure ell upper))
    (hw_nonneg : ∀ a, 0 ≤ w a)
    (hnorm : ∫ a, w a ∂parameterMeasure ell upper = 1)
    (hcover : ∀ a ∈ Icc ell upper,
      Real.sqrt (((scaledDirection a v) 0) ^ 2 +
        ((scaledDirection a v) 1) ^ 2) ≤ H)
    (hriskMeas : ∀ n, AEMeasurable
      (fun a => localRisk P theta (scaledDirection a v) p n)
      (parameterMeasure ell upper)) :
    ∀ᶠ n in atTop,
      AEMeasurable (fun a => ENNReal.ofReal (w a) *
        localRisk P theta (scaledDirection a v) p n)
        (parameterMeasure ell upper) ∧
      (∫⁻ a, ENNReal.ofReal (w a) *
        localRisk P theta (scaledDirection a v) p n
        ∂parameterMeasure ell upper) ≤ localWorstRisk P theta p H n := by
  filter_upwards [eventually_localAlternative_interior_uniform theta H htheta]
      with n hinterior
  have hmem : ∀ᵐ a ∂parameterMeasure ell upper, a ∈ Icc ell upper := by
    unfold parameterMeasure
    exact ae_restrict_mem measurableSet_Icc
  apply weighted_lintegral_le_uniform
    (parameterMeasure ell upper) w
    (fun a => localRisk P theta (scaledDirection a v) p n)
    (localWorstRisk P theta p H n) hw (hriskMeas n) hwint
    (Filter.Eventually.of_forall hw_nonneg) hnorm
  filter_upwards [hmem] with a ha
  apply localRisk_le_localWorstRisk
  exact ⟨hcover a ha, hinterior (scaledDirection a v) (hcover a ha)⟩

end CausalSmith.Stat.LdpAteEfficiencySurface
