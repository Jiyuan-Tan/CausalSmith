import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ConditionalMomentAdapters
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ObservedLawAdapters
import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
Assembly lemmas for the observed VMW margin proposition.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability

/-- The full-data target-proxy coordinate map is measurable. -/
-- @node: measurable_fullData_X
lemma measurable_fullData_X {k dx dz : ℕ} :
    Measurable (fun w : FullData k dx dz => w.X) := by
  change Measurable (fun w : FullData k dx dz => (FullData.toCoordinates w).2.2.1)
  exact continuous_induced_dom.measurable.snd.snd.fst

/-- The full-data reference-proxy coordinate map is measurable. -/
-- @node: measurable_fullData_Z
lemma measurable_fullData_Z {k dx dz : ℕ} :
    Measurable (fun w : FullData k dx dz => w.Z) := by
  change Measurable (fun w : FullData k dx dz => (FullData.toCoordinates w).2.2.2.1)
  exact continuous_induced_dom.measurable.snd.snd.snd.fst

/-- The full-data observed-outcome coordinate map is measurable. -/
-- @node: measurable_fullData_Y
lemma measurable_fullData_Y {k dx dz : ℕ} :
    Measurable (fun w : FullData k dx dz => w.Y) := by
  change Measurable (fun w : FullData k dx dz =>
    (FullData.toCoordinates w).2.2.2.2.2.2)
  exact continuous_induced_dom.measurable.snd.snd.snd.snd.snd.snd

/-- Each binary potential-outcome coordinate map is measurable. -/
-- @node: measurable_potential
lemma measurable_potential {k dx dz : ℕ} (t : Bool) :
    Measurable (@potential k dx dz t) := by
  cases t with
  | false =>
      change Measurable (fun w : FullData k dx dz =>
        (FullData.toCoordinates w).2.2.2.2.1)
      exact continuous_induced_dom.measurable.snd.snd.snd.snd.fst
  | true =>
      change Measurable (fun w : FullData k dx dz =>
        (FullData.toCoordinates w).2.2.2.2.2.1)
      exact continuous_induced_dom.measurable.snd.snd.snd.snd.snd.fst

/-- The observed target-proxy coordinate map is measurable. -/
-- @node: measurable_obs_X
lemma measurable_obs_X {dx dz : ℕ} : Measurable (fun o : Obs dx dz => o.X) := by
  change Measurable (fun o : Obs dx dz => (Obs.toCoordinates o).2.1)
  exact continuous_induced_dom.measurable.snd.fst

/-- The observed reference-proxy coordinate map is measurable. -/
-- @node: measurable_obs_Z
lemma measurable_obs_Z {dx dz : ℕ} : Measurable (fun o : Obs dx dz => o.Z) := by
  change Measurable (fun o : Obs dx dz => (Obs.toCoordinates o).2.2.1)
  exact continuous_induced_dom.measurable.snd.snd.fst

/-- The observed outcome coordinate map is measurable. -/
-- @node: measurable_obs_Y
lemma measurable_obs_Y {dx dz : ℕ} : Measurable (fun o : Obs dx dz => o.Y) := by
  change Measurable (fun o : Obs dx dz => (Obs.toCoordinates o).2.2.2)
  exact continuous_induced_dom.measurable.snd.snd.snd

/-- A conditional mean on a treatment arm is the finite mixture of the conditional means on
its latent cells. -/
-- @node: conditionalMean_fullDataArm_eq_sum_latentCell
lemma conditionalMean_fullDataArm_eq_sum_latentCell
    {k dx dz : ℕ} (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (t : Bool) (f : FullData k dx dz → ℝ)
    (hf : ∀ u : Fin k, IntegrableOn f (latentCell u t) P)
    (hArm : 0 < P.real {w | w.T = t}) :
    conditionalMean P {w | w.T = t} f =
      ∑ u : Fin k, (P.real (latentCell u t) / P.real {w | w.T = t}) *
        conditionalMean P (latentCell u t) f := by
  have hdisj : Pairwise (fun u v : Fin k =>
      Disjoint (latentCell (dx := dx) (dz := dz) u t) (latentCell v t)) := by
    intro u v huv
    rw [Set.disjoint_left]
    intro w hwu hwv
    exact huv (hwu.1.symm.trans hwv.1)
  have hint : (∫ w in {w : FullData k dx dz | w.T = t}, f w ∂P) =
      ∑ u : Fin k, ∫ w in latentCell u t, f w ∂P := by
    rw [fullDataArm_eq_iUnion_latentCell]
    exact integral_iUnion_fintype (fun u => measurableSet_latentCell u t) hdisj hf
  rw [conditionalMean, hint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  unfold conditionalMean
  by_cases hcell : P.real (latentCell u t) = 0
  · have hcell' : P (latentCell u t) = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top P (latentCell u t))).mp hcell
    simp [hcell, setIntegral_measure_zero f hcell']
  · field_simp

/-- Reference-proxy separation factors each latent-cell proxy cross moment, using bounded
clamped representatives of the proxy coordinates. -/
-- @node: latentCell_ZX_conditionalMean_factorization
lemma latentCell_ZX_conditionalMean_factorization
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hL : 1 ≤ L)
    (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) (i : Fin dz) (j : Fin dx) :
    conditionalMean P (latentCell u t) (fun w => w.Z i * w.X j) =
      conditionalMean P (latentCell u t) (fun w => w.Z i) *
        conditionalMean P (latentCell u t) (fun w => w.X j) := by
  have hpos := latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u t
  have hb := proxy_coordinate_bounds_of_model P hk hkx hM
  have hZb : ∀ᵐ w ∂P.restrict (latentCell u t), |w.Z i| ≤ L :=
    ae_restrict_of_ae (hb.2.1.mono fun w hw => hw i)
  have hXb : ∀ᵐ w ∂P.restrict (latentCell u t), |w.X j| ≤ L :=
    ae_restrict_of_ae (hb.1.mono fun w hw => hw j)
  let Zc : FullData k dx dz → ℝ := fun w => clampReal L (w.Z i)
  let Xc : FullData k dx dz → ℝ := fun w => clampReal L (w.X j)
  have hfac := referenceProxySeparation_to_normalizedFactorization
    hM.referenceProxySeparation u t hpos
  have hfact := hfac
    (fun z => clampReal L (z i)) (fun xy => clampReal L (xy.1 j))
    (measurable_clampReal (measurable_pi_apply i) L)
    (measurable_clampReal ((measurable_pi_apply j).comp measurable_fst) L)
    ⟨L, fun z => abs_clampReal_le L (z i) (zero_le_one.trans hL)⟩
    ⟨L, fun xy => abs_clampReal_le L (xy.1 j) (zero_le_one.trans hL)⟩
  rw [conditionalMean_eq_normalizedRestrictedIntegral hpos,
    conditionalMean_eq_normalizedRestrictedIntegral hpos,
    conditionalMean_eq_normalizedRestrictedIntegral hpos]
  calc
    normalizedRestrictedIntegral P (latentCell u t) (fun w => w.Z i * w.X j) =
        normalizedRestrictedIntegral P (latentCell u t) (fun w => Zc w * Xc w) := by
      apply integral_congr_ae
      exact (ae_normalizedRestrict_iff hpos).mpr <| by
        filter_upwards [hZb, hXb] with w hz hx
        simp only [Zc, Xc, clampReal_eq_self hz, clampReal_eq_self hx]
    _ = normalizedRestrictedIntegral P (latentCell u t) Zc *
        normalizedRestrictedIntegral P (latentCell u t) Xc := by
      simpa only [Zc, Xc, normalizedRestrictedIntegral] using hfact
    _ = normalizedRestrictedIntegral P (latentCell u t) (fun w => w.Z i) *
        normalizedRestrictedIntegral P (latentCell u t) (fun w => w.X j) := by
      congr 1 <;> apply integral_congr_ae
      · exact (ae_normalizedRestrict_iff hpos).mpr <|
          hZb.mono fun w hz => by simpa only [Zc] using clampReal_eq_self hz
      · exact (ae_normalizedRestrict_iff hpos).mpr <|
          hXb.mono fun w hx => by simpa only [Xc] using clampReal_eq_self hx

/-- Target-proxy separation makes the target-proxy conditional mean invariant across treatment
arms within a latent class. -/
-- @node: latentCell_X_conditionalMean_eq_latentClass
lemma latentCell_X_conditionalMean_eq_latentClass
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) (j : Fin dx) :
    conditionalMean P (latentCell u t) (fun w => w.X j) =
      conditionalMean P (latentClass u) (fun w => w.X j) := by
  let A : Set (FullData k dx dz) := {w | w.T = t}
  let C : Set (FullData k dx dz) := latentClass u
  let f : (Fin dx → ℝ) → ℝ := fun x => clampReal L (x j)
  let q : (ℝ × Bool) → ℝ := fun yt => if yt.2 = t then 1 else 0
  have hcellpos := latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u t
  have hclasspos : 0 < P.real C := by
    have hsub : latentCell u t ⊆ C := fun _ hw => hw.1
    exact lt_of_lt_of_le hpi ((hM.latentArmPositivity u t).trans (measureReal_mono hsub))
  have hcellreal : 0 < P.real (latentCell u t) :=
    lt_of_lt_of_le hpi (hM.latentArmPositivity u t)
  have hfac := hM.targetProxySeparation u f q
    (measurable_clampReal (measurable_pi_apply j) L)
    (by
      dsimp [q]
      apply Measurable.ite
      · exact measurable_snd (measurableSet_singleton t)
      · fun_prop
      · fun_prop)
    ⟨L, fun x => abs_clampReal_le L (x j) (zero_le_one.trans hL)⟩
    ⟨1, fun yt => by dsimp [q]; split <;> simp⟩
  have hinter : C ∩ A = latentCell u t := by
    ext w
    simp [C, A, latentClass, latentCell]
  have hprod : (fun w : FullData k dx dz => f w.X * q (w.Y, w.T)) =
      A.indicator (fun w => f w.X) := by
    funext w
    by_cases hw : w ∈ A
    · have hw' : w.T = t := hw
      simp [A, f, q, hw, hw']
    · have hw' : w.T ≠ t := by simpa [A] using hw
      simp [A, f, q, hw, hw']
  have hq : (fun w : FullData k dx dz => q (w.Y, w.T)) =
      A.indicator (fun _ => (1 : ℝ)) := by
    funext w
    by_cases hw : w ∈ A
    · have hw' : w.T = t := hw
      simp [A, q, hw, hw']
    · have hw' : w.T ≠ t := by simpa [A] using hw
      simp [A, q, hw, hw']
  rw [hprod, hq] at hfac
  unfold conditionalMean at hfac
  rw [setIntegral_indicator (measurableSet_fullDataArm t),
    setIntegral_indicator (measurableSet_fullDataArm t), hinter] at hfac
  have hclamp :
      conditionalMean P (latentCell u t) (fun w => f w.X) =
        conditionalMean P C (fun w => f w.X) := by
    unfold conditionalMean
    dsimp [C] at hclasspos ⊢
    have hclassne := ne_of_gt hclasspos
    have hcellne := ne_of_gt hcellreal
    have hone : (∫ _w in latentCell u t, (1 : ℝ) ∂P) =
        P.real (latentCell u t) := by
      simp [Measure.real]
    rw [hone] at hfac
    field_simp at hfac ⊢
    nlinarith
  have hb := (proxy_coordinate_bounds_of_model P hk hkx hM).1
  have hcellb : ∀ᵐ w ∂P.restrict (latentCell u t), |w.X j| ≤ L :=
    ae_restrict_of_ae (hb.mono fun w hw => hw j)
  have hclassb : ∀ᵐ w ∂P.restrict C, |w.X j| ≤ L :=
    ae_restrict_of_ae (hb.mono fun w hw => hw j)
  calc
    conditionalMean P (latentCell u t) (fun w => w.X j) =
        conditionalMean P (latentCell u t) (fun w => f w.X) := by
      unfold conditionalMean
      congr 1
      apply integral_congr_ae
      exact hcellb.mono fun w hw => by simp only [f, clampReal_eq_self hw]
    _ = conditionalMean P C (fun w => f w.X) := hclamp
    _ = conditionalMean P (latentClass u) (fun w => w.X j) := by
      unfold conditionalMean
      congr 1
      apply integral_congr_ae
      exact hclassb.mono fun w hw => by simp only [f, clampReal_eq_self hw]

/-- The observed armwise proxy moment has the latent finite-mixture factorization. -/
-- @node: observedProxyMoment_factorization
lemma observedProxyMoment_factorization
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (t : Bool) :
    observedProxyMoment (obsSummary P) t =
      referenceFeature P t * latentArmWeights P t * (targetFeature P).transpose := by
  ext i j
  have hb := proxy_coordinate_bounds_of_model P hk hkx hM
  have hint : ∀ u : Fin k,
      IntegrableOn (fun w : FullData k dx dz => w.Z i * w.X j) (latentCell u t) P := by
    intro u
    apply IntegrableOn.of_bound (measure_lt_top P (latentCell u t))
    · exact ((measurable_pi_apply i).comp measurable_fullData_Z).mul
        ((measurable_pi_apply j).comp measurable_fullData_X) |>.aestronglyMeasurable
    · exact ae_restrict_of_ae <| by
        filter_upwards [hb.2.1, hb.1] with w hz hx
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hz i) (hx j) (abs_nonneg _) (zero_le_one.trans hL)
  have harmpos : 0 < P.real {w : FullData k dx dz | w.T = t} := by
    exact lt_of_lt_of_le (mul_pos (Nat.cast_pos.mpr (by omega)) hpi)
      (arm_mass_lower_of_latentArmPositivity P hM.latentArmPositivity t)
  have hmix := conditionalMean_fullDataArm_eq_sum_latentCell P t
    (fun w => w.Z i * w.X j) hint harmpos
  have hobs : conditionalMean (obsLaw P) (obsArm t) (fun o => o.Z i * o.X j) =
      conditionalMean P {w | w.T = t} (fun w => w.Z i * w.X j) := by
    exact conditionalMean_obsArm_eq_fullDataArm P t _ <| by
      exact ((measurable_pi_apply i).comp <| by
        change Measurable (fun o : Obs dx dz => (Obs.toCoordinates o).2.2.1)
        exact continuous_induced_dom.measurable.snd.snd.fst).mul
        ((measurable_pi_apply j).comp <| by
          change Measurable (fun o : Obs dx dz => (Obs.toCoordinates o).2.1)
          exact continuous_induced_dom.measurable.snd.fst)
  have heval : observedProxyMoment (obsSummary P) t i j =
      conditionalMean (obsLaw P) (obsArm t) (fun o => o.Z i * o.X j) := by
    cases t <;> rfl
  rw [heval, hobs, hmix]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, latentArmWeights,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.mem_univ,
    if_true]
  apply Finset.sum_congr rfl
  intro u _
  rw [latentCell_ZX_conditionalMean_factorization P hk hkx hL hpi hM u t i j,
    latentCell_X_conditionalMean_eq_latentClass P hk hkx hL hpi hM u t j]
  simp only [referenceFeature, targetFeature]
  simp
  ring

/-- Entrywise conditional outer-product moments agree with the Bochner integral of the
corresponding continuous-linear maps under the normalized cell law. -/
-- @node: matrixCLM_conditionalOuterMoment_eq_integral
lemma matrixCLM_conditionalOuterMoment_eq_integral
    {k dx dz : ℕ} (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (C : Set (FullData k dx dz)) (hCpos : 0 < P C)
    (hcoord : ∀ i j, Integrable (fun w => w.Z i * w.X j) (normalizedRestrict P C))
    (hmap : Integrable (fun w => matrixCLM (outerProduct w.Z w.X))
      (normalizedRestrict P C)) :
    matrixCLM (fun i j => conditionalMean P C (fun w => w.Z i * w.X j)) =
      ∫ w, matrixCLM (outerProduct w.Z w.X) ∂normalizedRestrict P C := by
  ext x i
  rw [ContinuousLinearMap.integral_apply hmap x]
  have happ : Integrable (fun w => matrixCLM (outerProduct w.Z w.X) x)
      (normalizedRestrict P C) :=
    (ContinuousLinearMap.apply ℝ (Euc dz) x).integrable_comp hmap
  rw [eval_integral_piLp (fun a => happ.eval_piLp a) i]
  simp only [matrixCLM, Matrix.toEuclideanLin_apply, outerProduct]
  change (∑ j, conditionalMean P C (fun w => w.Z i * w.X j) * x j) =
    (∫ w, ∑ j, (w.Z i * w.X j) * x j ∂normalizedRestrict P C)
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [conditionalMean_eq_normalizedRestrictedIntegral hCpos]
    unfold normalizedRestrictedIntegral
    exact (integral_mul_const (μ := normalizedRestrict P C) (x j)
      (fun w : FullData k dx dz => w.Z i * w.X j)).symm
  · intro j _
    exact (hcoord i j).mul_const (x j)

/-- A matrix of scalar conditional means is the Bochner conditional mean of the
corresponding matrix-valued random element. -/
-- @node: matrixCLM_conditionalMatrix_eq_integral
lemma matrixCLM_conditionalMatrix_eq_integral
    {k dx dz : ℕ} (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (C : Set (FullData k dx dz)) (hCpos : 0 < P C)
    (A : FullData k dx dz → RectMatrix dz dx)
    (hcoord : ∀ i j, Integrable (fun w => A w i j) (normalizedRestrict P C))
    (hmap : Integrable (fun w => matrixCLM (A w)) (normalizedRestrict P C)) :
    matrixCLM (fun i j => conditionalMean P C (fun w => A w i j)) =
      ∫ w, matrixCLM (A w) ∂normalizedRestrict P C := by
  ext x i
  rw [ContinuousLinearMap.integral_apply hmap x]
  have happ : Integrable (fun w => matrixCLM (A w) x) (normalizedRestrict P C) :=
    (ContinuousLinearMap.apply ℝ (Euc dz) x).integrable_comp hmap
  rw [eval_integral_piLp (fun a => happ.eval_piLp a) i]
  simp only [matrixCLM, Matrix.toEuclideanLin_apply]
  change (∑ j, conditionalMean P C (fun w => A w i j) * x j) =
    (∫ w, ∑ j, A w i j * x j ∂normalizedRestrict P C)
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [conditionalMean_eq_normalizedRestrictedIntegral hCpos]
    unfold normalizedRestrictedIntegral
    exact (integral_mul_const (μ := normalizedRestrict P C) (x j)
      (fun w : FullData k dx dz => A w i j)).symm
  · intro j _
    exact (hcoord i j).mul_const (x j)

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
