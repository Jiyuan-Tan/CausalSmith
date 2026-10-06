module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.MeanAssembly
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ChainRegularity

/-! Fubini identities assembling conditional density projections into marginal coefficients. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- An integrable joint scalar function remains integrable after weighting by the representer. -/
-- @node: integrable_joint_weighted_phiCoefficients
lemma integrable_joint_weighted_phiCoefficients (J : ℕ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (unitVolume.prod unitVolume)) :
    Integrable (fun z : ℝ × ℝ => f z.1 z.2 • phiCoefficients J z.2)
      (unitVolume.prod unitVolume) := by
  apply Integrable.of_eval_piLp
  intro i
  change Integrable (fun z : ℝ × ℝ => f z.1 z.2 * phiCoefficients J z.2 i) _
  apply hf.mul_bdd (c := Real.sqrt J)
  · have hm : Measurable (fun z : ℝ × ℝ => phiCoefficients J z.2 i) := by
      change Measurable (fun z : ℝ × ℝ => if cell J z.2 = i.val + 1 then Real.sqrt J else 0)
      exact Measurable.ite ((measurable_histogram_cell J).comp measurable_snd
        (measurableSet_singleton _)) measurable_const measurable_const
    exact hm.aestronglyMeasurable
  · filter_upwards [] with z
    change ‖if cell J z.2 = i.val + 1 then Real.sqrt J else 0‖ ≤ Real.sqrt J
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_nonneg]

/-- Outcome projection commutes with uniform-design integration by Bochner Fubini. -/
-- @node: integral_coefficients_eq_coefficients_integral
lemma integral_coefficients_eq_coefficients_integral (J : ℕ) (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (unitVolume.prod unitVolume)) :
    (∫ x, coefficients J (f x) ∂unitVolume) =
      coefficients J (fun y => ∫ x, f x y ∂unitVolume) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hw := integrable_joint_weighted_phiCoefficients J f hf
  calc
    _ = ∫ x, ∫ y, f x y • phiCoefficients J y ∂unitVolume ∂unitVolume := by
      apply integral_congr_ae
      filter_upwards [hf.prod_right_ae] with x hx
      exact (integral_weighted_phiCoefficients J (f x) hx).symm
    _ = ∫ y, ∫ x, f x y • phiCoefficients J y ∂unitVolume ∂unitVolume :=
      integral_integral_swap hw
    _ = ∫ y, (∫ x, f x y ∂unitVolume) • phiCoefficients J y ∂unitVolume := by
      simp_rw [integral_smul_const]
    _ = _ := integral_weighted_phiCoefficients J _ hf.integral_prod_right

/-- The model envelope supplies joint integrability on the uniform covariate/outcome square. -/
-- @node: integrable_eta_joint
lemma integrable_eta_joint (P : ObsLaw) (hModel : Model P) (a : Bool) :
    Integrable (fun z : ℝ × ℝ => P.eta a z.1 z.2) (unitVolume.prod unitVolume) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (P.eta_measurable a).aestronglyMeasurable 4
  have hs : ∀ᵐ z ∂unitVolume.prod unitVolume,
      z.1 ∈ Set.Icc 0 1 ∧ z.2 ∈ Set.Icc 0 1 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod measurableSet_Icc)).2 (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact ⟨hx, hy⟩)
  filter_upwards [hs] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (P.eta_nonneg a z.1 z.2 hz.1 hz.2)]
  exact (hModel.density_envelope a z.1 z.2 hz.1 hz.2).2

/-- Integrating conditional true-density coefficients gives the marginal-density coefficients. -/
-- @node: integral_eta_coefficients_eq_marginalDensity
lemma integral_eta_coefficients_eq_marginalDensity (P : ObsLaw) (hModel : Model P)
    (a : Bool) (J : ℕ) :
    (∫ x, coefficients J (P.eta a x) ∂unitVolume) =
      coefficients J (marginalDensity P a) := by
  exact integral_coefficients_eq_coefficients_integral J (P.eta a)
    (integrable_eta_joint P hModel a)

/-- A trained normalized histogram is jointly measurable in covariate and outcome.
Its normalization depends only on the covariate cell label. -/
-- @node: measurable_densityPilot_joint
@[fun_prop] lemma measurable_densityPilot_joint {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) :
    Measurable (fun z : ℝ × ℝ => densityPilot train mx my a z.1 z.2) := by
  have hc : Measurable (fun z : ℝ × ℝ => outcomeCellCount train mx my a z.1 z.2) := by
    let g : ℕ × ℕ → ℕ := fun c => (Finset.univ.filter (fun i =>
      cell mx (X (train i)) = c.1 ∧ A (train i) = a ∧
        cell my (Y (train i)) = c.2)).card
    exact (measurable_of_countable g).comp
      (((measurable_histogram_cell mx).comp measurable_fst).prodMk
        ((measurable_histogram_cell my).comp measurable_snd))
  have ha : Measurable (fun z : ℝ × ℝ => armCellCount train mx a z.1) :=
    (measurable_armCellCount_covariate train mx a).comp measurable_fst
  have hn : Measurable (fun x => ∫ y, clippedDensityPilot train mx my a x y ∂unitVolume) := by
    apply measurable_of_histogram_const mx
    intro x z hxz
    congr 1
    funext y
    simp [clippedDensityPilot, armCellCount, outcomeCellCount, hxz]
  have hr : Measurable (fun z : ℝ × ℝ => clippedDensityPilot train mx my a z.1 z.2) := by
    unfold clippedDensityPilot clip
    have hi : Measurable (fun z : ℝ × ℝ => if armCellCount train mx a z.1 = 0 then (1 : ℝ)
        else (my : ℝ) * outcomeCellCount train mx my a z.1 z.2 / armCellCount train mx a z.1) :=
      Measurable.ite (ha (measurableSet_singleton 0)) measurable_const (by fun_prop)
    fun_prop
  unfold densityPilot
  exact hr.div (hn.comp measurable_fst)

/-- Global pilot clipping yields joint integrability without a good-pilot assumption. -/
-- @node: integrable_densityPilot_joint
lemma integrable_densityPilot_joint {m : ℕ} (train : Fin m → Omega)
    (mx my : ℕ) (a : Bool) :
    Integrable (fun z : ℝ × ℝ => densityPilot train mx my a z.1 z.2)
      (unitVolume.prod unitVolume) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by fun_prop) 64
  filter_upwards [] with z
  have h := densityPilot_mem_Icc train mx my a z.1 z.2
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [h.1])]
  exact h.2

/-- The pilot contribution in (21) is the projection of its covariate-integrated density. -/
-- @node: integral_pilotCoefficients_eq_coefficients_integral
lemma integral_pilotCoefficients_eq_coefficients_integral {m : ℕ}
    (train : Fin m → Omega) (mx my J : ℕ) (a : Bool) :
    (∫ x, pilotCoefficients train mx my J a x ∂unitVolume) =
      coefficients J (fun y => ∫ x, densityPilot train mx my a x y ∂unitVolume) := by
  exact integral_coefficients_eq_coefficients_integral J (densityPilot train mx my a)
    (integrable_densityPilot_joint train mx my a)

/-- Propensity-power density errors are jointly integrable by clipping and the model envelope. -/
-- @node: integrable_uerr_pow_mul_werr_joint
lemma integrable_uerr_pow_mul_werr_joint {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (n : ℕ) :
    Integrable (fun z : ℝ × ℝ => (uerr P train mx a z.1) ^ n *
      werr P train mx my a z.1 z.2) (unitVolume.prod unitVolume) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hw := (integrable_eta_joint P hModel a).sub
    (integrable_densityPilot_joint train mx my a)
  have hb : ∀ᵐ z ∂unitVolume.prod unitVolume, ‖(uerr P train mx a z.1) ^ n‖ ≤ 2 ^ n := by
    have hx : ∀ᵐ z ∂unitVolume.prod unitVolume, z.1 ∈ Set.Icc 0 1 :=
      (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod MeasurableSet.univ)).2 (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact Filter.Eventually.of_forall (fun _ => ⟨hx, Set.mem_univ _⟩)) |>.mono (fun _ h => h.1)
    filter_upwards [hx] with z hz
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (uerr_abs_le P hModel train mx a z.1 hz) n
  have hm : Measurable (fun z : ℝ × ℝ => (uerr P train mx a z.1) ^ n) := by fun_prop
  simpa only [werr, mul_comm, Pi.sub_apply] using hw.mul_bdd hm.aestronglyMeasurable hb

/-- The weighted residual's propensity-power products are jointly integrable. -/
-- @node: integrable_uerr_pow_mul_verr_joint
lemma integrable_uerr_pow_mul_verr_joint {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (n : ℕ) :
    Integrable (fun z : ℝ × ℝ => (uerr P train mx a z.1) ^ n *
      verr P train mx my a z.1 z.2) (unitVolume.prod unitVolume) := by
  have h0 := integrable_uerr_pow_mul_werr_joint P hModel train mx my a n
  have h1 := integrable_uerr_pow_mul_werr_joint P hModel train mx my a (n + 1)
  apply (h0.add h1).congr
  filter_upwards [] with z
  dsimp [verr]
  rw [pow_succ]
  ring

/-- Covariate-integrated error products are integrable in outcome by Fubini. -/
-- @node: integrable_integrated_uerr_pow_mul_verr
lemma integrable_integrated_uerr_pow_mul_verr {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my : ℕ) (a : Bool) (n : ℕ) :
    Integrable (fun y => ∫ x, (uerr P train mx a x) ^ n *
      verr P train mx my a x y ∂unitVolume) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  exact (integrable_uerr_pow_mul_verr_joint P hModel train mx my a n).integral_prod_right

/-- Equal outcome functions almost everywhere have equal histogram coefficients. -/
-- @node: coefficients_congr_ae
lemma coefficients_congr_ae (J : ℕ) (f g : ℝ → ℝ) (hfg : f =ᵐ[unitVolume] g) :
    coefficients J f = coefficients J g := by
  ext i
  change Real.sqrt J * (∫ y in histogramCell J (i.val + 1), f y ∂unitVolume) =
    Real.sqrt J * (∫ y in histogramCell J (i.val + 1), g y ∂unitVolume)
  rw [integral_congr_ae (ae_restrict_of_ae hfg)]

/-- Histogram coefficients preserve addition of integrable outcome functions. -/
-- @node: coefficients_add
lemma coefficients_add (J : ℕ) (f g : ℝ → ℝ)
    (hf : Integrable f unitVolume) (hg : Integrable g unitVolume) :
    coefficients J (fun y => f y + g y) = coefficients J f + coefficients J g := by
  ext i
  change Real.sqrt J * (∫ y in histogramCell J (i.val + 1), f y + g y ∂unitVolume) =
    Real.sqrt J * (∫ y in histogramCell J (i.val + 1), f y ∂unitVolume) +
    Real.sqrt J * (∫ y in histogramCell J (i.val + 1), g y ∂unitVolume)
  rw [integral_add hf.integrableOn hg.integrableOn, mul_add]

/-- Projecting the integrated cancellation (22) yields the exact cubic vector remainder. -/
-- @node: corrected_mean_coefficients_identity
lemma corrected_mean_coefficients_identity {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J : ℕ) (a : Bool) :
    coefficients J (fun y => ∫ x, densityPilot train mx my a x y ∂unitVolume) +
      coefficients J (fun y => ∫ x, verr P train mx my a x y ∂unitVolume) -
      coefficients J (fun y => ∫ x, uerr P train mx a x *
        verr P train mx my a x y ∂unitVolume) +
      coefficients J (fun y => ∫ x, (uerr P train mx a x) ^ 2 *
        verr P train mx my a x y ∂unitVolume) =
    coefficients J (marginalDensity P a) +
      coefficients J (fun y => ∫ x, (uerr P train mx a x) ^ 3 *
        werr P train mx my a x y ∂unitVolume) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hp := (integrable_densityPilot_joint train mx my a).integral_prod_right
  have he := (integrable_eta_joint P hModel a).integral_prod_right
  have hv : Integrable (fun y => ∫ x, verr P train mx my a x y ∂unitVolume) unitVolume := by
    simpa using integrable_integrated_uerr_pow_mul_verr P hModel train mx my a 0
  have huv : Integrable (fun y => ∫ x, uerr P train mx a x *
      verr P train mx my a x y ∂unitVolume) unitVolume := by
    simpa using integrable_integrated_uerr_pow_mul_verr P hModel train mx my a 1
  have hu2v := integrable_integrated_uerr_pow_mul_verr P hModel train mx my a 2
  have hu3w := (integrable_uerr_pow_mul_werr_joint P hModel train mx my a 3).integral_prod_right
  let p := fun y => ∫ x, densityPilot train mx my a x y ∂unitVolume
  let v := fun y => ∫ x, verr P train mx my a x y ∂unitVolume
  let uv := fun y => ∫ x, uerr P train mx a x * verr P train mx my a x y ∂unitVolume
  let u2v := fun y => ∫ x, (uerr P train mx a x) ^ 2 * verr P train mx my a x y ∂unitVolume
  let u3w := fun y => ∫ x, (uerr P train mx a x) ^ 3 * werr P train mx my a x y ∂unitVolume
  change Integrable p unitVolume at hp
  change Integrable (marginalDensity P a) unitVolume at he
  change Integrable v unitVolume at hv
  change Integrable uv unitVolume at huv
  change Integrable u2v unitVolume at hu2v
  change Integrable u3w unitVolume at hu3w
  have hc : coefficients J (fun y => (p y + v y - uv y) + u2v y) =
      coefficients J (fun y => marginalDensity P a y + u3w y) := by
    apply coefficients_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact corrected_mean_integrated_identity P hModel train mx my a y hy
  have hsub : coefficients J (fun y => p y + v y - uv y) =
      coefficients J (fun y => p y + v y) - coefficients J uv := by
    simpa using coefficients_const_mul_sub J 1 (fun y => p y + v y) uv (hp.add hv) huv
  rw [coefficients_add J (fun y => p y + v y - uv y) u2v ((hp.add hv).sub huv) hu2v,
    hsub, coefficients_add J p v hp hv,
    coefficients_add J (marginalDensity P a) u3w he hu3w] at hc
  exact hc

/-- The coefficient-valued arm cancellation in (22), in the form used by role expectations. -/
-- @node: corrected_mean_projected_arm_identity
lemma corrected_mean_projected_arm_identity {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J : ℕ) (a : Bool) :
    (∫ x, pilotCoefficients train mx my J a x ∂unitVolume) +
      (∫ x, coefficients J (verr P train mx my a x) ∂unitVolume) -
      (∫ x, coefficients J (fun y => uerr P train mx a x *
        verr P train mx my a x y) ∂unitVolume) +
      (∫ x, coefficients J (fun y => (uerr P train mx a x) ^ 2 *
        verr P train mx my a x y) ∂unitVolume) - coefficients J (marginalDensity P a) =
    coefficients J (fun y => ∫ x, (uerr P train mx a x) ^ 3 *
      werr P train mx my a x y ∂unitVolume) := by
  have hv : Integrable (Function.uncurry (verr P train mx my a))
      (unitVolume.prod unitVolume) := by
    change Integrable (fun z : ℝ × ℝ => verr P train mx my a z.1 z.2) _
    simpa only [pow_zero, one_mul] using
      integrable_uerr_pow_mul_verr_joint P hModel train mx my a 0
  have huv : Integrable (fun z : ℝ × ℝ => uerr P train mx a z.1 *
      verr P train mx my a z.1 z.2) (unitVolume.prod unitVolume) := by
    simpa using integrable_uerr_pow_mul_verr_joint P hModel train mx my a 1
  rw [integral_pilotCoefficients_eq_coefficients_integral,
    integral_coefficients_eq_coefficients_integral J _ hv,
    integral_coefficients_eq_coefficients_integral J
      (fun x y => uerr P train mx a x * verr P train mx my a x y) huv,
    integral_coefficients_eq_coefficients_integral J
      (fun x y => (uerr P train mx a x) ^ 2 * verr P train mx my a x y)
      (integrable_uerr_pow_mul_verr_joint P hModel train mx my a 2),
    corrected_mean_coefficients_identity P hModel train mx my J a,
    add_sub_cancel_left]

end CausalSmith.Stat.DensityEffectRoughNull
