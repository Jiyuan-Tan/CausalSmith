import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Basic
import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge

/-!
Paper-local adapters from the model's conditional-mean assumptions and almost-sure coordinate
bounds to normalized restricted moments.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set
open Causalean.Mathlib.Probability

/-- Every entry of a rectangular matrix is bounded by its Euclidean operator norm. -/
-- @node: abs_matrix_entry_le_matrixCLM_norm
lemma abs_matrix_entry_le_matrixCLM_norm {rows cols : ℕ} (A : RectMatrix rows cols)
    (i : Fin rows) (j : Fin cols) : |A i j| ≤ ‖matrixCLM A‖ := by
  let e : Euc cols := WithLp.toLp 2 (Pi.single j 1)
  have he : ‖e‖ = 1 := by simp [e]
  have hcoord : |(matrixCLM A e) i| ≤ ‖matrixCLM A e‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (matrixCLM A e) i
  calc
    |A i j| = |(matrixCLM A e) i| := by
      simp [e, matrixCLM, Matrix.toEuclideanLin_apply]
    _ ≤ ‖matrixCLM A e‖ := hcoord
    _ ≤ ‖matrixCLM A‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖matrixCLM A‖ := by rw [he, mul_one]

/-- Anchor normalization converts the observable outer-product envelopes into coordinatewise
bounds for both proxies and the observed outcome--reference-proxy product. -/
-- @node: proxy_coordinate_bounds_of_model
lemma proxy_coordinate_bounds_of_model {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    (∀ᵐ w ∂P, ∀ i : Fin dx, |w.X i| ≤ L) ∧
      (∀ᵐ w ∂P, ∀ j : Fin dz, |w.Z j| ≤ L) ∧
      (∀ᵐ w ∂P, ∀ j : Fin dz, |w.Y * w.Z j| ≤ L) := by
  let i0 : Fin dx := ⟨0, by omega⟩
  have hX : ∀ᵐ w ∂P, ∀ i : Fin dx, |w.X i| ≤ L := by
    filter_upwards [hM.boundedX] with w hw i
    have hi : |w.X i| ≤ ‖(WithLp.toLp 2 w.X : Euc dx)‖ := by
      simpa only [Real.norm_eq_abs] using
        PiLp.norm_apply_le (WithLp.toLp 2 w.X : Euc dx) i
    have hnorm : ‖(WithLp.toLp 2 w.X : Euc dx)‖ ≤ L := by
      simpa only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using hw
    exact hi.trans hnorm
  have hZ : ∀ᵐ w ∂P, ∀ j : Fin dz, |w.Z j| ≤ L := by
    filter_upwards [hM.anchor, hM.boundedProxyProduct] with w hanchor hprod j
    have hi0 : w.X i0 = 1 := hanchor i0 rfl
    have hentry := abs_matrix_entry_le_matrixCLM_norm (outerProduct w.Z w.X) j i0
    simpa [outerProduct, hi0] using hentry.trans hprod
  have hYZ : ∀ᵐ w ∂P, ∀ j : Fin dz, |w.Y * w.Z j| ≤ L := by
    filter_upwards [hM.anchor, hM.boundedOutcomeProxyProduct] with w hanchor hprod j
    have hi0 : w.X i0 = 1 := hanchor i0 rfl
    have hentry :=
      abs_matrix_entry_le_matrixCLM_norm (w.Y • outerProduct w.Z w.X) j i0
    simpa [outerProduct, hi0, mul_assoc] using hentry.trans hprod
  exact ⟨hX, hZ, hYZ⟩

/-- Clamp a real value to the interval `[-R, R]`. -/
def clampReal (R x : ℝ) : ℝ := max (-R) (min R x)

lemma measurable_clampReal {Omega : Type*} [MeasurableSpace Omega]
    {f : Omega → ℝ} (hf : Measurable f) (R : ℝ) :
    Measurable (fun omega => clampReal R (f omega)) := by
  exact measurable_const.max (measurable_const.min hf)

lemma abs_clampReal_le (R x : ℝ) (hR : 0 ≤ R) : |clampReal R x| ≤ R := by
  rw [abs_le]
  constructor <;> simp [clampReal] <;> linarith

lemma clampReal_eq_self {R x : ℝ} (hx : |x| ≤ R) : clampReal R x = x := by
  rw [abs_le] at hx
  simp [clampReal, hx.1, hx.2]

/-- An a.e.-bounded measurable scalar has a globally bounded measurable clamped representative,
and the two representatives have the same integral. -/
theorem integral_clampReal_eq_of_ae_abs_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f : Omega → ℝ} (hf : Measurable f) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ᵐ omega ∂mu, |f omega| ≤ R) :
    Measurable (fun omega => clampReal R (f omega)) ∧
      UniformlyBounded (fun omega => clampReal R (f omega)) ∧
      f =ᵐ[mu] (fun omega => clampReal R (f omega)) ∧
      (∫ omega, f omega ∂mu) = ∫ omega, clampReal R (f omega) ∂mu := by
  have hae : f =ᵐ[mu] (fun omega => clampReal R (f omega)) :=
    hbound.mono fun omega homega => (clampReal_eq_self homega).symm
  exact ⟨measurable_clampReal hf R, ⟨R, fun omega => abs_clampReal_le R (f omega) hR⟩,
    hae, integral_congr_ae hae⟩

-- keep: reusable restricted-integral clamping adapter for bounded conditional-moment models
/-- Clamping an a.e.-bounded coordinate on a cell does not change its restricted integral. -/
theorem setIntegral_clampReal_eq_of_ae_abs_le
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {C : Set Omega}
    {f : Omega → ℝ} (hf : Measurable f) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ᵐ omega ∂P.restrict C, |f omega| ≤ R) :
    (∫ omega in C, f omega ∂P) = ∫ omega in C, clampReal R (f omega) ∂P :=
  (integral_clampReal_eq_of_ae_abs_le hf hR hbound).2.2.2

-- keep: reusable normalized-restriction clamping adapter for later conditional-moment consumers
/-- Clamping an a.e.-bounded coordinate on a positive cell does not change its normalized
restricted integral. -/
theorem normalizedRestrictedIntegral_clampReal_eq_of_ae_abs_le
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsFiniteMeasure P]
    {C : Set Omega} (hCpos : 0 < P C)
    {f : Omega → ℝ} (hf : Measurable f) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ᵐ omega ∂P.restrict C, |f omega| ≤ R) :
    normalizedRestrictedIntegral P C f =
      normalizedRestrictedIntegral P C (fun omega => clampReal R (f omega)) := by
  unfold normalizedRestrictedIntegral
  apply integral_congr_ae
  exact (ae_normalizedRestrict_iff hCpos).mpr
    (hbound.mono fun omega homega => (clampReal_eq_self homega).symm)

-- keep: reusable measurable vector-clamping certificate independent of this paper's estimator
/-- Coordinatewise clamping gives a measurable, globally coordinate-bounded vector representative
which agrees almost surely with the original vector when all coordinates obey the a.e. bound. -/
theorem measurable_clampedVector_and_aeEq
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega} {n : ℕ}
    {X : Omega → Fin n → ℝ} (hX : Measurable X) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ᵐ omega ∂mu, ∀ i, |X omega i| ≤ R) :
    Measurable (fun omega i => clampReal R (X omega i)) ∧
      (∀ i, UniformlyBounded (fun omega => clampReal R (X omega i))) ∧
      X =ᵐ[mu] (fun omega i => clampReal R (X omega i)) := by
  have hmeas : Measurable (fun omega i => clampReal R (X omega i)) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_clampReal ((measurable_pi_apply i).comp hX) R
  refine ⟨hmeas, fun i => ⟨R, fun omega => abs_clampReal_le R (X omega i) hR⟩, ?_⟩
  filter_upwards [hbound] with omega homega
  funext i
  exact (clampReal_eq_self (homega i)).symm

/-- The paper's conditional mean is exactly integration under the promoted normalized restriction
on a positive-mass cell. -/
theorem conditionalMean_eq_normalizedRestrictedIntegral
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsFiniteMeasure P]
    {C : Set Omega} (hCpos : 0 < P C) (f : Omega → ℝ) :
    conditionalMean P C f = normalizedRestrictedIntegral P C f := by
  rw [normalizedRestrictedIntegral_eq hCpos]
  rfl

/-- Reference-proxy separation supplies the promoted bounded-test factorization on each positive
latent cell. -/
theorem referenceProxySeparation_to_normalizedFactorization
    {k dx dz : ℕ} {P : Measure (FullData k dx dz)} [IsProbabilityMeasure P]
    (hsep : ReferenceProxySeparation P) (u : Fin k) (t : Bool)
    (hpos : 0 < P (latentCell u t)) :
    NormalizedRestrictedBoundedTestFactorization P (latentCell u t)
      (fun w => w.Z) (fun w => (w.X, w.Y)) := by
  intro phi psi hphi hpsi hphiBound hpsiBound
  have hs := hsep u t phi psi hphi hpsi hphiBound hpsiBound
  rw [conditionalMean_eq_normalizedRestrictedIntegral hpos,
    conditionalMean_eq_normalizedRestrictedIntegral hpos,
    conditionalMean_eq_normalizedRestrictedIntegral hpos] at hs
  simpa only [normalizedRestrictedIntegral] using hs

/-- Target-proxy separation supplies the promoted bounded-test factorization on each positive
latent class. -/
theorem targetProxySeparation_to_normalizedFactorization
    {k dx dz : ℕ} {P : Measure (FullData k dx dz)} [IsProbabilityMeasure P]
    (hsep : TargetProxySeparation P) (u : Fin k)
    (hpos : 0 < P (latentClass u)) :
    NormalizedRestrictedBoundedTestFactorization P (latentClass u)
      (fun w => w.X) (fun w => (w.Y, w.T)) := by
  intro phi psi hphi hpsi hphiBound hpsiBound
  have hs := hsep u phi psi hphi hpsi hphiBound hpsiBound
  rw [conditionalMean_eq_normalizedRestrictedIntegral hpos,
    conditionalMean_eq_normalizedRestrictedIntegral hpos,
    conditionalMean_eq_normalizedRestrictedIntegral hpos] at hs
  simpa only [normalizedRestrictedIntegral] using hs

/-- Armwise latent ignorability supplies bounded-test factorization of a potential outcome and
the treatment indicator under each positive latent-class law. -/
-- @node: latentIgnorability_to_normalizedFactorization
theorem latentIgnorability_to_normalizedFactorization
    {k dx dz : ℕ} {P : Measure (FullData k dx dz)} [IsProbabilityMeasure P]
    (hign : ArmwiseLatentIgnorability P) (u : Fin k) (t : Bool)
    (hpos : 0 < P (latentClass u)) :
    NormalizedRestrictedBoundedTestFactorization P (latentClass u)
      (potential t) (fun w => w.T) := by
  intro phi psi hphi hpsi hphiBound hpsiBound
  have hs := hign u t phi psi hphi hpsi hphiBound hpsiBound
  rw [conditionalMean_eq_normalizedRestrictedIntegral hpos,
    conditionalMean_eq_normalizedRestrictedIntegral hpos,
    conditionalMean_eq_normalizedRestrictedIntegral hpos] at hs
  simpa only [normalizedRestrictedIntegral] using hs

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
