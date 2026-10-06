module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.OutcomeCrossMoment
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.PoissonPartition

/-!
The actual null outcomes are independent of the reported cell design, even after
mixing the shared propensity sign. These measure identities justify integrating
outcomes first in the Poisson experiment cross-moment calculation (40).
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The actual covariate and treatment law before attaching baseline outcomes. -/
-- @node: lowerNullDesignLaw
def lowerNullDesignLaw (theta : ℝ) (k : ℕ) (lambda : Fin k → Bool) :
    Measure (ℝ × Bool) :=
  (unitVolume.prod Measure.count).withDensity
    (fun xa => ENNReal.ofReal (armProbability (lowerPropensity theta k lambda) xa.2 xa.1))

/-- The design density is measurable on the covariate and treatment product. -/
-- @node: measurable_lowerNullDesignDensity
@[fun_prop] lemma measurable_lowerNullDesignDensity (theta : ℝ) (k : ℕ)
    (lambda : Fin k → Bool) :
    Measurable (fun xa : ℝ × Bool =>
      ENNReal.ofReal (armProbability (lowerPropensity theta k lambda) xa.2 xa.1)) := by
  unfold armProbability
  apply Measurable.ennreal_ofReal
  apply Measurable.ite (measurable_snd (measurableSet_singleton true))
  · unfold lowerPropensity signedBumps; fun_prop
  · unfold lowerPropensity signedBumps; fun_prop

/-- Splitting the actual null record into design and outcome gives a product law. -/
-- @node: lower_null_record_design_outcome
lemma lower_null_record_design_outcome (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    (lowerNullLaw theta k j hp lambda omega).law.map
      (fun o => ((X o, A o), Y o)) =
      (lowerNullDesignLaw theta k lambda).prod lowerBaselineLaw := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  rw [lowerNullDesignLaw, lowerBaselineLaw,
    prod_withDensity (measurable_lowerNullDesignDensity theta k lambda)
      lower_baseline_valid.1.ennreal_ofReal]
  rw [lower_null_law_withDensity]
  rw [← (measurePreserving_prodAssoc unitVolume (Measure.count : Measure Bool)
    unitVolume).symm.map_eq]
  change _ = (densityBase.map (fun o => ((X o, A o), Y o))).withDensity _
  rw [← lower_map_withDensity_comp densityBase
    (fun o => ((X o, A o), Y o)) (by unfold X A Y; fun_prop)
    (fun z => ENNReal.ofReal (armProbability (lowerPropensity theta k lambda) z.1.2 z.1.1) *
      ENNReal.ofReal (baselineDensity z.2)) (by
      exact ((measurable_lowerNullDesignDensity theta k lambda).comp measurable_fst).mul
        (lower_baseline_valid.1.ennreal_ofReal.comp measurable_snd))]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [] with o
  dsimp [lowerRecordDensity, lowerNullLaw, ObsLaw.ofNuisance, lowerNullDensity]
  exact ENNReal.ofReal_mul' (by linarith [lower_baseline_valid.2.1 (Y o)])

/-- The covariate-treatment factor is normalized because the actual null law and
its independent baseline outcome factor are probability laws. -/
-- @node: lowerNullDesignLaw_probability
lemma lowerNullDesignLaw_probability (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    IsProbabilityMeasure (lowerNullDesignLaw theta k lambda) := by
  have he := congrArg (fun mu : Measure ((ℝ × Bool) × ℝ) => mu Set.univ)
    (lower_null_record_design_outcome theta k j hp lambda omega)
  rw [Measure.map_apply (by unfold X A Y; fun_prop) MeasurableSet.univ] at he
  constructor
  rw [Set.preimage_univ, measure_univ] at he
  rw [show (Set.univ : Set ((ℝ × Bool) × ℝ)) = Set.univ ×ˢ Set.univ from Set.univ_prod_univ.symm,
    Measure.prod_prod, (show lowerBaselineLaw Set.univ = 1 from measure_univ), mul_one] at he
  exact he.symm

/-- Reporting the full fixed-count design and all outcomes commutes with iid
sampling. The outcome factor is the actual non-flat baseline product. -/
-- @node: lower_null_sample_design_outcome
lemma lower_null_sample_design_outcome (theta : ℝ) (k j m : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    (dataLaw (lowerNullLaw theta k j hp lambda omega) m).map
      (fun o => ((fun i => (X (o i), A (o i))), fun i => Y (o i))) =
      (Measure.pi (fun _ : Fin m => lowerNullDesignLaw theta k lambda)).prod
        (Measure.pi (fun _ : Fin m => lowerBaselineLaw)) := by
  letI := lowerNullDesignLaw_probability theta k j hp lambda omega
  have hm : Measurable (fun o : Omega => ((X o, A o), Y o)) := by
    unfold X A Y
    fun_prop
  rw [show (fun o : Data m => ((fun i => (X (o i), A (o i))), fun i => Y (o i))) =
      (MeasurableEquiv.arrowProdEquivProdArrow (ℝ × Bool) ℝ (Fin m)) ∘
        (fun o : Data m => fun i => ((X (o i), A (o i)), Y (o i))) from rfl,
    ← Measure.map_map (MeasurableEquiv.measurable _) (by unfold X A Y; fun_prop)]
  change ((Measure.pi (fun _ : Fin m =>
    (lowerNullLaw theta k j hp lambda omega).law)).map _).map _ = _
  rw [Measure.pi_map_pi (fun _ => hm.aemeasurable)]
  simp_rw [lower_null_record_design_outcome theta k j hp lambda omega]
  exact (measurePreserving_arrowProdEquivProdArrow (ℝ × Bool) ℝ (Fin m)
    (fun _ => lowerNullDesignLaw theta k lambda) (fun _ => lowerBaselineLaw)).map_eq

/-- Bump scores and treatment flags depend only on the covariate-treatment data. -/
-- @node: lowerDesignCellData
def lowerDesignCellData (m : ℕ) (xa : Fin m → ℝ × Bool) :
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m :=
  (fun i => lowerBump (xa i).1, (fun i => (xa i).2), (fun i => (xa i).2))

/-- Reporting the design from covariate-treatment data is measurable. -/
-- @node: measurable_lowerDesignCellData
@[fun_prop] lemma measurable_lowerDesignCellData (m : ℕ) :
    Measurable (lowerDesignCellData m) := by
  unfold lowerDesignCellData
  fun_prop

/-- Under a fixed latent sign, the canonical reported design and all baseline
outcomes are independent. -/
-- @node: lower_unit_null_joint_fixed_sign
lemma lower_unit_null_joint_fixed_sign (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (b : Bool) (m : ℕ) :
    (dataLaw (lowerUnitNullFamily tau ht b) m).map
      (fun o => (lowerUnitCellData m o, fun i => Y (o i))) =
      ((dataLaw (lowerUnitNullFamily tau ht b) m).map (lowerUnitCellData m)).prod
        (Measure.pi (fun _ : Fin m => lowerBaselineLaw)) := by
  let mu := Measure.pi (fun _ : Fin m => lowerNullDesignLaw tau 1 (fun _ => b))
  let nu := Measure.pi (fun _ : Fin m => lowerBaselineLaw)
  letI := lowerNullDesignLaw_probability tau 1 1 (lower_unit_parameters tau ht)
    (fun _ => b) (fun _ => false)
  have h := lower_null_sample_design_outcome tau 1 1 m (lower_unit_parameters tau ht)
    (fun _ => b) (fun _ => false)
  have hjoint : (dataLaw (lowerUnitNullFamily tau ht b) m).map
      (fun o => (lowerUnitCellData m o, fun i => Y (o i))) =
      (mu.map (lowerDesignCellData m)).prod nu := by
    rw [show (fun o => (lowerUnitCellData m o, fun i => Y (o i))) =
        (Prod.map (lowerDesignCellData m) id) ∘
          (fun o : Data m => ((fun i => (X (o i), A (o i))), fun i => Y (o i))) from rfl,
      ← Measure.map_map (by fun_prop) (by unfold X A Y; fun_prop)]
    rw [show (dataLaw (lowerUnitNullFamily tau ht b) m).map
        (fun o => ((fun i => (X (o i), A (o i))), fun i => Y (o i))) = mu.prod nu from h,
      ← Measure.map_prod_map _ _ (measurable_lowerDesignCellData m) measurable_id,
      Measure.map_id]
  have hd := congrArg (fun rho => (rho : Measure
    (Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m × (Fin m → ℝ))).map Prod.fst)
    hjoint
  rw [Measure.map_map measurable_fst (by unfold lowerUnitCellData X A Y; fun_prop),
    Measure.map_fst_prod, measure_univ, one_smul] at hd
  rw [hjoint, ← hd]
  rfl

/-- Each fixed-sign canonical design is a probability law. -/
-- @node: lower_unit_null_fixed_design_probability
instance lower_unit_null_fixed_design_probability (tau : ℝ)
    (ht : tau ∈ Set.Ioc 0 (1 / 4)) (b : Bool) (m : ℕ) :
    IsProbabilityMeasure ((dataLaw (lowerUnitNullFamily tau ht b) m).map
      (lowerUnitCellData m)) := by
  letI : IsProbabilityMeasure (dataLaw (lowerUnitNullFamily tau ht b) m) := by
    unfold dataLaw
    infer_instance
  exact Measure.isProbabilityMeasure_map (measurable_lowerUnitCellData m).aemeasurable

/-- Mixing the shared sign preserves independence of the baseline outcomes from
the canonical design. The sign is averaged after constructing the entire sample. -/
-- @node: lower_unit_null_joint_sign_mixture
lemma lower_unit_null_joint_sign_mixture (tau : ℝ) (ht : tau ∈ Set.Ioc 0 (1 / 4))
    (m : ℕ) :
    (uniformSampleMixture m (lowerUnitNullFamily tau ht)).map
      (fun o => (lowerUnitCellData m o, fun i => Y (o i))) =
      (lowerUnitCellDesign tau ht m).prod
        (Measure.pi (fun _ : Fin m => lowerBaselineLaw)) := by
  unfold lowerUnitCellDesign uniformSampleMixture
    Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
  rw [Fintype.sum_bool, Measure.map_add _ _
    (by unfold lowerUnitCellData X A Y; fun_prop)]
  simp only [Measure.map_smul, lower_unit_null_joint_fixed_sign]
  rw [Measure.map_add _ _ (measurable_lowerUnitCellData m)]
  simp only [Measure.map_smul, Measure.add_prod, Measure.prod_smul_left]

/-- Affine cell localization retains the joint design and outcome report at fixed
sign and count. -/
-- @node: lower_localized_null_joint_fixed_sign
lemma lower_localized_null_joint_fixed_sign (theta : ℝ) (k j m : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (b : Bool) (omega : Fin j → Bool) :
    (Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega)).map
      (fun o => (lowerLocalizedCellData k m r o, fun i => Y (o i))) =
      ((dataLaw (lowerUnitNullFamily (lowerTau theta k)
        (lowerTau_mem_Ioc theta k j hp hk) b) m).map (lowerUnitCellData m)).prod
        (Measure.pi (fun _ : Fin m => lowerBaselineLaw)) := by
  have he : lowerLocalizedNullLaw theta k j hp r b omega =
      (lowerUnitNullFamily (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) b).law.map
        (lowerCellRecordEmbed k r) :=
    (lower_null_cell_law_eq_embedded_unit theta k j hp hk r b omega).symm
  simp_rw [he]
  rw [← Measure.pi_map_pi (fun _ => (measurable_lowerCellRecordEmbed k r).aemeasurable),
    Measure.map_map (by unfold lowerLocalizedCellData X A Y; fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin m =>
    (lowerUnitNullFamily (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) b).law)).map
    (fun o => (lowerLocalizedCellData k m r (fun i => lowerCellRecordEmbed k r (o i)),
      fun i => Y (lowerCellRecordEmbed k r (o i)))) = _
  rw [show (fun o : Data m =>
      (lowerLocalizedCellData k m r (fun i => lowerCellRecordEmbed k r (o i)),
        fun i => Y (lowerCellRecordEmbed k r (o i)))) =
      (fun o => (lowerUnitCellData m o, fun i => Y (o i))) by
        funext o
        rw [lowerLocalizedCellData_embed k m hk r]
        rfl]
  exact lower_unit_null_joint_fixed_sign _ _ b m

/-- The actual shared-sign localized sample reports precisely the canonical design
product with independent baseline outcomes. This is the conditional null law used
in the actual cell likelihood calculation. -/
-- @node: lower_localized_null_joint_sign_mixture
lemma lower_localized_null_joint_sign_mixture (theta : ℝ) (k j m : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k) (omega : Fin j → Bool) :
    (Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
      Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega))).map
        (fun o => (lowerLocalizedCellData k m r o, fun i => Y (o i))) =
      (lowerUnitCellDesign (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) m).prod
        (Measure.pi (fun _ : Fin m => lowerBaselineLaw)) := by
  unfold Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
  rw [Fintype.sum_bool, Measure.map_add _ _
    (by unfold lowerLocalizedCellData X A Y; fun_prop)]
  simp only [Measure.map_smul, lower_localized_null_joint_fixed_sign theta k j m hp hk r]
  unfold lowerUnitCellDesign uniformSampleMixture
    Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
  rw [Fintype.sum_bool, Measure.map_add _ _ (measurable_lowerUnitCellData m)]
  simp only [Measure.map_smul, Measure.add_prod, Measure.prod_smul_left]

/-- The finite likelihood is measurable jointly in the cell scores and outcomes;
treatment flags are handled as a discrete coordinate. -/
-- @node: measurable_lowerCellOutcomeLikelihood
@[fun_prop] lemma measurable_lowerCellOutcomeLikelihood (m j : ℕ) (tau gamma : ℝ)
    (omega : Fin j → Bool) :
    Measurable (fun p : Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m × (Fin m → ℝ) =>
      cellAlternativeRatio tau gamma p.1.1 p.1.2.1
        (fun i => lowerOutcomeScore j omega (p.2 i))) := by
  have hm : Measurable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × (Fin m → Bool) =>
      cellAlternativeRatio tau gamma p.1.1 p.2 p.1.2) := by
    apply measurable_from_prod_countable_left
    intro a
    have hl (b : Bool) : Measurable (fun u : Fin m → ℝ => cellSignLikelihood tau u a b) := by
      unfold cellSignLikelihood
      apply Finset.measurable_prod Finset.univ
      intro i hi
      exact (((show Measurable (fun u : Fin m → ℝ => u i) from measurable_pi_apply i).const_mul (tau * signValue b)).mul_const
        (signValue (a i))).const_add 1
    have hc (S : Finset (Fin m)) :
        Measurable (fun u : Fin m → ℝ => cellPosteriorCoefficient tau u a S) := by
      unfold cellPosteriorCoefficient
      apply Measurable.div
      · apply Finset.measurable_sum Finset.univ
        intro b hb
        apply (hl b).mul
        apply Finset.measurable_prod S
        intro i hi
        exact (show Measurable (fun u : Fin m → ℝ => u i) from measurable_pi_apply i).const_mul (signValue b) |>.div
          (((show Measurable (fun u : Fin m → ℝ => u i) from measurable_pi_apply i).const_mul (tau * signValue b)).const_add 1)
      · exact Finset.measurable_sum Finset.univ (fun b _ => hl b)
    unfold cellAlternativeRatio
    dsimp only
    apply Finset.measurable_sum ((Finset.univ.filter (fun i : Fin m => a i = true)).powerset)
    intro S hS
    apply (((hc S).comp measurable_fst).const_mul (gamma ^ S.card)).mul
    apply Finset.measurable_prod S
    intro i hi
    exact (show Measurable (fun u : Fin m → ℝ => u i) from measurable_pi_apply i).comp measurable_snd
  have hu : Measurable (fun p :
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m × (Fin m → ℝ) => p.1.1) :=
    measurable_fst.fst
  have ha : Measurable (fun p :
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m × (Fin m → ℝ) => p.1.2.1) :=
    measurable_fst.snd.fst
  have hv : Measurable (fun p :
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m × (Fin m → ℝ) =>
      fun i => lowerOutcomeScore j omega (p.2 i)) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_lowerOutcomeScore j omega).comp
      ((show Measurable (fun y : Fin m → ℝ => y i) from measurable_pi_apply i).comp measurable_snd)
  convert hm.comp ((hu.prodMk hv).prodMk ha) using 1
  funext p
  rfl

/-- A deterministic finite-count envelope bounds the actual outcome likelihood.
It supplies integrability before any exchange of design and outcome integration. -/
-- @node: lowerCellOutcomeLikelihood_abs_bound
lemma lowerCellOutcomeLikelihood_abs_bound {m : ℕ} (tau gamma : ℝ)
    (ht : |tau| ≤ 1 / 4) (u : Fin m → ℝ) (hu : ∀ i, |u i| ≤ 1)
    (a : Fin m → Bool) (j : ℕ) (omega : Fin j → Bool) (y : Fin m → ℝ) :
    |cellAlternativeRatio tau gamma u a (fun i => lowerOutcomeScore j omega (y i))| ≤
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, (4 * |gamma|) ^ S.card := by
  classical
  let active := Finset.univ.filter (fun i : Fin m => a i = true)
  have hterm (S : Finset (Fin m)) :
      |gamma ^ S.card * cellPosteriorCoefficient tau u a S *
        ∏ i ∈ S, lowerOutcomeScore j omega (y i)| ≤ (4 * |gamma|) ^ S.card := by
    rw [abs_mul, abs_mul, abs_pow, Finset.abs_prod]
    have hv : (∏ i ∈ S, |lowerOutcomeScore j omega (y i)|) ≤ (2 : ℝ) ^ S.card := by
      calc
        _ ≤ ∏ _i ∈ S, (2 : ℝ) := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          (fun i _ => lowerOutcomeScore_abs_le j omega (y i))
        _ = _ := by simp
    calc
      _ ≤ |gamma| ^ S.card * (2 : ℝ) ^ S.card * (2 : ℝ) ^ S.card :=
        mul_le_mul (mul_le_mul_of_nonneg_left
          (cellPosteriorCoefficient_abs_le tau ht u hu a S) (by positivity)) hv
          (by positivity) (by positivity)
      _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; ring
  calc
    _ ≤ ∑ S ∈ active.powerset,
        |gamma ^ S.card * cellPosteriorCoefficient tau u a S *
          ∏ i ∈ S, lowerOutcomeScore j omega (y i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ active.powerset, (4 * |gamma|) ^ S.card :=
      Finset.sum_le_sum (fun S _ => hterm S)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.powerset_mono.mpr (Finset.filter_subset _ _)) (fun _ _ _ => by positivity)

/-- The likelihood product is integrable under the joint canonical design and
actual baseline outcomes, with no additional moment hypothesis. -/
-- @node: lowerCellOutcomeLikelihood_joint_integrable
lemma lowerCellOutcomeLikelihood_joint_integrable (tau : ℝ)
    (ht : tau ∈ Set.Ioc 0 (1 / 4)) (gamma : ℝ) (m j : ℕ) (omega op : Fin j → Bool) :
    Integrable (fun p : Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m × (Fin m → ℝ) =>
      cellAlternativeRatio tau gamma p.1.1 p.1.2.1
        (fun i => lowerOutcomeScore j omega (p.2 i)) *
      cellAlternativeRatio tau gamma p.1.1 p.1.2.1
        (fun i => lowerOutcomeScore j op (p.2 i)))
      ((lowerUnitCellDesign tau ht m).prod (Measure.pi (fun _ : Fin m => lowerBaselineLaw))) := by
  let B : ℝ := ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, (4 * |gamma|) ^ S.card
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => by positivity)
  apply Integrable.of_bound
    (((measurable_lowerCellOutcomeLikelihood m j tau gamma omega).mul
      (measurable_lowerCellOutcomeLikelihood m j tau gamma op)).aestronglyMeasurable) (B * B)
  have hc : ∀ᵐ p ∂(lowerUnitCellDesign tau ht m).prod
      (Measure.pi (fun _ : Fin m => lowerBaselineLaw)),
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Valid p.1 :=
    (measurePreserving_fst (μ := lowerUnitCellDesign tau ht m)
      (ν := Measure.pi (fun _ : Fin m => lowerBaselineLaw))).quasiMeasurePreserving.ae
        (lowerUnitCellDesign_valid tau ht m)
  filter_upwards [hc] with p hp
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul
    (lowerCellOutcomeLikelihood_abs_bound tau gamma (by rw [abs_of_pos ht.1]; exact ht.2)
      p.1.1 hp.1 p.1.2.1 j omega p.2)
    (lowerCellOutcomeLikelihood_abs_bound tau gamma (by rw [abs_of_pos ht.1]; exact ht.2)
      p.1.1 hp.1 p.1.2.1 j op p.2) (abs_nonneg _) hB

/-- Fubini under the actual joint design/outcome law recovers the cell cross moment
already identified with the posterior polynomial. -/
-- @node: lowerCellOutcomeLikelihood_joint_cross_moment
lemma lowerCellOutcomeLikelihood_joint_cross_moment (tau : ℝ)
    (ht : tau ∈ Set.Ioc 0 (1 / 4)) (gamma : ℝ) (m j : ℕ) (omega op : Fin j → Bool) :
    (∫ p : Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m × (Fin m → ℝ),
      cellAlternativeRatio tau gamma p.1.1 p.1.2.1
        (fun i => lowerOutcomeScore j omega (p.2 i)) *
      cellAlternativeRatio tau gamma p.1.1 p.1.2.1
        (fun i => lowerOutcomeScore j op (p.2 i))
      ∂(lowerUnitCellDesign tau ht m).prod (Measure.pi (fun _ : Fin m => lowerBaselineLaw))) =
    ∫ c, lowerCellOutcomeCrossMoment tau gamma j omega op c ∂lowerUnitCellDesign tau ht m := by
  rw [integral_prod _ (lowerCellOutcomeLikelihood_joint_integrable tau ht gamma m j omega op)]
  rfl

/-- The actual localized likelihood product is integrable under the shared-sign
sample law, by its proved joint design/outcome pushforward. -/
-- @node: lower_localized_outcome_pair_integrable
lemma lower_localized_outcome_pair_integrable (theta : ℝ) (k j m : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (omega op : Fin j → Bool) :
    Integrable (fun o : Data m =>
      cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j)
        (lowerLocalizedCellData k m r o).1 (lowerLocalizedCellData k m r o).2.1
        (fun i => lowerOutcomeScore j omega (Y (o i))) *
      cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j)
        (lowerLocalizedCellData k m r o).1 (lowerLocalizedCellData k m r o).2.1
        (fun i => lowerOutcomeScore j op (Y (o i))))
      (Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
        Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega))) := by
  have hm : Measurable (fun o : Data m =>
      (lowerLocalizedCellData k m r o, fun i => Y (o i))) := by
    unfold lowerLocalizedCellData X A Y
    fun_prop
  have hmp : MeasurePreserving (fun o : Data m =>
      (lowerLocalizedCellData k m r o, fun i => Y (o i)))
      (Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
        Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega)))
      ((lowerUnitCellDesign (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) m).prod
        (Measure.pi (fun _ : Fin m => lowerBaselineLaw))) :=
    ⟨hm, lower_localized_null_joint_sign_mixture theta k j m hp hk r omega⟩
  exact hmp.integrable_comp_of_integrable
    (lowerCellOutcomeLikelihood_joint_integrable _ _ (lowerGamma theta j) m j omega op)

/-- Outcome integration under the actual localized shared-sign sample law gives
the canonical design-averaged posterior cross moment in (31). -/
-- @node: lower_localized_outcome_cross_moment
lemma lower_localized_outcome_cross_moment (theta : ℝ) (k j m : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (omega op : Fin j → Bool) :
    (∫ o : Data m,
      cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j)
        (lowerLocalizedCellData k m r o).1 (lowerLocalizedCellData k m r o).2.1
        (fun i => lowerOutcomeScore j omega (Y (o i))) *
      cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j)
        (lowerLocalizedCellData k m r o).1 (lowerLocalizedCellData k m r o).2.1
        (fun i => lowerOutcomeScore j op (Y (o i)))
      ∂Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
        Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega))) =
      ∫ c, lowerCellOutcomeCrossMoment (lowerTau theta k) (lowerGamma theta j) j omega op c
        ∂lowerUnitCellDesign (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) m := by
  have hm : Measurable (fun o : Data m =>
      (lowerLocalizedCellData k m r o, fun i => Y (o i))) := by
    unfold lowerLocalizedCellData X A Y
    fun_prop
  rw [← integral_map (φ := fun o : Data m =>
    (lowerLocalizedCellData k m r o, fun i => Y (o i)))
    (f := fun p : Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m × (Fin m → ℝ) =>
      cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j) p.1.1 p.1.2.1
        (fun i => lowerOutcomeScore j omega (p.2 i)) *
      cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j) p.1.1 p.1.2.1
        (fun i => lowerOutcomeScore j op (p.2 i))) hm.aemeasurable
    (by
      convert ((measurable_lowerCellOutcomeLikelihood m j (lowerTau theta k) (lowerGamma theta j) omega).mul
        (measurable_lowerCellOutcomeLikelihood m j (lowerTau theta k) (lowerGamma theta j) op)).aestronglyMeasurable using 1
      funext p
      rfl),
    lower_localized_null_joint_sign_mixture theta k j m hp hk r omega]
  exact lowerCellOutcomeLikelihood_joint_cross_moment _ _ _ m j omega op

/-- Averaging the actual localized sample cross moment over its independent
Poisson count identifies the coefficient series, rather than postulating the
experiment cross moment. -/
-- @node: lower_localized_outcome_poisson_cross_moment
lemma lower_localized_outcome_poisson_cross_moment (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (omega op : Fin j → Bool) (xi : NNReal) :
    (∫ m : ℕ, ∫ o : Data m,
      cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j)
        (lowerLocalizedCellData k m r o).1 (lowerLocalizedCellData k m r o).2.1
        (fun i => lowerOutcomeScore j omega (Y (o i))) *
      cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j)
        (lowerLocalizedCellData k m r o).1 (lowerLocalizedCellData k m r o).2.1
        (fun i => lowerOutcomeScore j op (Y (o i)))
      ∂Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
        Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega))
      ∂poissonMeasure xi) =
    lowerPoissonOverlap (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) xi
      (lowerGamma theta j) (weightedSignOverlap j (lowerOutcomeWeight j) omega op) := by
  simp_rw [lower_localized_outcome_cross_moment theta k j _ hp hk r omega op]
  exact lowerCellOutcomeCrossMoment_poisson_average _ _ xi _ j omega op

/-- The actual localized sample likelihood, expressed through the design report
and observed outcomes. -/
-- @node: lowerActualCellRatio
def lowerActualCellRatio (theta : ℝ) (k j m : ℕ) (r : Fin k)
    (omega : Fin j → Bool) (o : Data m) : ℝ :=
  cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j)
    (lowerLocalizedCellData k m r o).1 (lowerLocalizedCellData k m r o).2.1
    (fun i => lowerOutcomeScore j omega (Y (o i)))

/-- Independent actual cell sample laws and Poisson counts yield K(z)^k with the
common outcome sign vector held outside the product. This is the actual grouped
sample cross moment underlying (40), before restoring record order. -/
-- @node: lower_actual_outcome_independent_cells
lemma lower_actual_outcome_independent_cells (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k)
    (omega op : Fin j → Bool) (xi : NNReal) :
    (∫ counts : Fin k → ℕ,
      ∫ samples : (r : Fin k) → Data (counts r),
        ∏ r : Fin k, lowerActualCellRatio theta k j (counts r) r omega (samples r) *
          lowerActualCellRatio theta k j (counts r) r op (samples r)
        ∂Measure.pi (fun r => Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
          Measure.pi (fun _ : Fin (counts r) => lowerLocalizedNullLaw theta k j hp r b omega)))
      ∂Measure.pi (fun _ : Fin k => poissonMeasure xi)) =
    lowerPoissonOverlap (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) xi
      (lowerGamma theta j) (weightedSignOverlap j (lowerOutcomeWeight j) omega op) ^ k := by
  have (r : Fin k) (m : ℕ) : IsProbabilityMeasure
      (Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
        Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega))) :=
    Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability _
  have hf (counts : Fin k → ℕ) := integral_fintype_prod_eq_prod
    (fun r : Fin k => fun o : Data (counts r) =>
      lowerActualCellRatio theta k j (counts r) r omega o *
        lowerActualCellRatio theta k j (counts r) r op o)
    (μ := fun r => Causalean.Stat.Minimax.Mixture.uniformMixture (fun b : Bool =>
      Measure.pi (fun _ : Fin (counts r) => lowerLocalizedNullLaw theta k j hp r b omega)))
  simp_rw [hf, lowerActualCellRatio,
    lower_localized_outcome_cross_moment theta k j _ hp hk]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin k => fun m : ℕ =>
    ∫ c, lowerCellOutcomeCrossMoment (lowerTau theta k) (lowerGamma theta j) j omega op c
      ∂lowerUnitCellDesign (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) m)]
  simp_rw [lowerCellOutcomeCrossMoment_poisson_average]
  simp

end CausalSmith.Stat.DensityEffectRoughNull
