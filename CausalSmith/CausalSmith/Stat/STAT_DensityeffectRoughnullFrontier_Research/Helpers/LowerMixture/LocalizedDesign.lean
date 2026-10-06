module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.PoissonDesign
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.SampleFactorization
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Affine cell localization of the actual null experiment. Rescaling the covariate
retains the treatment and outcome coordinates and the shared latent propensity sign.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Embedding unit-cell covariates into the specified physical covariate cell. -/
-- @node: lowerCellEmbed
def lowerCellEmbed (k : ℕ) (r : Fin k) (z : ℝ) : ℝ := (z + r.val) / k

/-- Embedding a cell covariate is measurable. -/
-- @node: measurable_lowerCellEmbed
@[fun_prop] lemma measurable_lowerCellEmbed (k : ℕ) (r : Fin k) :
    Measurable (lowerCellEmbed k r) := by
  unfold lowerCellEmbed
  fun_prop

/-- Rescaling recovers the unit coordinate exactly. -/
-- @node: lowerCellEmbed_coordinate
lemma lowerCellEmbed_coordinate (k : ℕ) (hk : 0 < k) (r : Fin k) (z : ℝ) :
    (k : ℝ) * lowerCellEmbed k r z - r.val = z := by
  have hn : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold lowerCellEmbed
  field_simp
  ring

/-- Every other cell bump vanishes after unit-cell embedding, including the endpoints. -/
-- @node: signedBumps_lowerCellEmbed
lemma signedBumps_lowerCellEmbed (k : ℕ) (hk : 0 < k) (r : Fin k)
    (lambda : Fin k → Bool) (z : ℝ) (hz : z ∈ Set.Icc 0 1) :
    signedBumps k lambda (lowerCellEmbed k r z) = signValue (lambda r) * lowerBump z := by
  classical
  unfold signedBumps
  have he := lowerCellEmbed_coordinate k hk r z
  conv_rhs => rw [← he]
  apply Finset.sum_eq_single r
  · intro s _ hsr
    have hn : lowerBump ((k : ℝ) * lowerCellEmbed k r z - s.val) = 0 := by
      by_contra h
      have hs := lowerBump_nonzero_support h
      have hne : s.val ≠ r.val := fun h => hsr (Fin.ext h)
      have hor : s.val < r.val ∨ r.val < s.val := lt_or_gt_of_ne hne
      rcases hor with hlt | hgt
      · have hc : (s.val : ℝ) + 1 ≤ r.val := by exact_mod_cast hlt
        linarith [hz.1, hs.2]
      · have hc : (r.val : ℝ) + 1 ≤ s.val := by exact_mod_cast hgt
        linarith [hz.2, hs.1]
    simp only [hn, mul_zero]
  · simp

/-- The physical closed cell; endpoints have zero covariate mass. -/
-- @node: lowerClosedCell
def lowerClosedCell (k : ℕ) (r : Fin k) : Set ℝ :=
  Set.Icc ((r.val : ℝ) / k) (((r.val : ℝ) + 1) / k)

/-- Unit-interval support is exactly the preimage of the physical cell. -/
-- @node: lowerCellEmbed_preimage
lemma lowerCellEmbed_preimage (k : ℕ) (hk : 0 < k) (r : Fin k) :
    lowerCellEmbed k r ⁻¹' lowerClosedCell k r = Set.Icc 0 1 := by
  have hp : (0 : ℝ) < k := by exact_mod_cast hk
  ext z
  simp only [Set.mem_preimage, lowerClosedCell, lowerCellEmbed, Set.mem_Icc,
    div_le_div_iff_of_pos_right hp]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The physical cell lies in the observed covariate support. -/
-- @node: lowerClosedCell_subset
lemma lowerClosedCell_subset (k : ℕ) (hk : 0 < k) (r : Fin k) :
    lowerClosedCell k r ⊆ Set.Icc 0 1 := by
  have hp : (0 : ℝ) < k := by exact_mod_cast hk
  have hr : (r.val : ℝ) + 1 ≤ k := by exact_mod_cast r.isLt
  intro x hx
  exact ⟨le_trans (div_nonneg (Nat.cast_nonneg _) hp.le) hx.1,
    le_trans hx.2 ((div_le_one hp).2 hr)⟩

/-- Lebesgue scaling gives the exact cell mass, before nuisance weighting. -/
-- @node: lowerCellEmbed_map_unitVolume
lemma lowerCellEmbed_map_unitVolume (k : ℕ) (hk : 0 < k) (r : Fin k) :
    unitVolume.map (lowerCellEmbed k r) =
      ENNReal.ofReal (k : ℝ) • unitVolume.restrict (lowerClosedCell k r) := by
  have hp : (0 : ℝ) < k := by exact_mod_cast hk
  have htrans := (measurePreserving_add_right (volume : Measure ℝ) (r.val : ℝ)).map_eq
  have hvol : (volume : Measure ℝ).map (lowerCellEmbed k r) =
      ENNReal.ofReal (k : ℝ) • volume := by
    have hf : lowerCellEmbed k r =
        (fun x : ℝ => (k : ℝ)⁻¹ * x) ∘ (fun x : ℝ => x + r.val) := by
      funext x
      simp [lowerCellEmbed, div_eq_mul_inv, mul_comm]
    rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), htrans,
      Real.map_volume_mul_left (inv_ne_zero hp.ne')]
    simp [abs_of_pos hp]
  change (volume.restrict (Set.Icc 0 1)).map (lowerCellEmbed k r) =
    ENNReal.ofReal (k : ℝ) • (volume.restrict (Set.Icc 0 1)).restrict (lowerClosedCell k r)
  rw [Measure.restrict_restrict_of_subset (lowerClosedCell_subset k hk r)]
  conv_lhs => rw [← lowerCellEmbed_preimage k hk r]
  rw [← Measure.restrict_map (measurable_lowerCellEmbed k r)
    (show MeasurableSet (lowerClosedCell k r) from measurableSet_Icc), hvol,
    Measure.restrict_smul]

/-- Cell embedding leaves the arm and outcome unchanged. -/
-- @node: lowerCellRecordEmbed
def lowerCellRecordEmbed (k : ℕ) (r : Fin k) (o : Omega) : Omega :=
  (lowerCellEmbed k r (X o), A o, Y o)

/-- Embedding an observed record is measurable. -/
-- @node: measurable_lowerCellRecordEmbed
@[fun_prop] lemma measurable_lowerCellRecordEmbed (k : ℕ) (r : Fin k) :
    Measurable (lowerCellRecordEmbed k r) := by
  unfold lowerCellRecordEmbed X A Y
  fun_prop

/-- Weighting by a function of the reported coordinate commutes with reporting. -/
-- @node: lower_map_withDensity_comp
lemma lower_map_withDensity_comp {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (mu : Measure E) (f : E → F) (hf : Measurable f)
    (g : F → ℝ≥0∞) (hg : Measurable g) :
    (mu.withDensity (g ∘ f)).map f = (mu.map f).withDensity g := by
  apply Measure.ext_of_lintegral
  intro phi hphi
  rw [lintegral_map hphi hf]
  change (∫⁻ a, (phi ∘ f) a ∂mu.withDensity (g ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul mu (hg.comp hf) (hphi.comp hf),
    lintegral_withDensity_eq_lintegral_mul (mu.map f) hg hphi,
    lintegral_map (hg.mul hphi) hf]
  rfl

/-- Cell embedding has the same exact mass factor on the full record reference measure. -/
-- @node: lowerCellRecordEmbed_map_densityBase
lemma lowerCellRecordEmbed_map_densityBase (k : ℕ) (hk : 0 < k) (r : Fin k) :
    densityBase.map (lowerCellRecordEmbed k r) = ENNReal.ofReal (k : ℝ) •
      densityBase.restrict {o | X o ∈ lowerClosedCell k r} := by
  have : IsFiniteMeasure unitVolume := by unfold unitVolume; infer_instance
  change (unitVolume.prod (Measure.count.prod unitVolume)).map
      (Prod.map (lowerCellEmbed k r) id) = _
  rw [← Measure.map_prod_map _ _ (measurable_lowerCellEmbed k r) measurable_id,
    Measure.map_id, lowerCellEmbed_map_unitVolume k hk r, Measure.prod_smul_left,
    Measure.restrict_prod_eq_prod_univ]
  simp only [densityBase, X, Set.prod_univ]
  rfl

/-- The physical amplitude is positive, so the canonical unit-cell design is available. -/
-- @node: lowerTau_mem_Ioc
lemma lowerTau_mem_Ioc (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (hk : 0 < k) : lowerTau theta k ∈ Set.Ioc 0 (1 / 4) := by
  refine ⟨?_, (lowerTau_mem_Icc theta k j hp).2⟩
  unfold lowerTau
  exact mul_pos hp.1.1 (Real.rpow_pos_of_pos (by exact_mod_cast hk) _)

/-- After affine embedding, a fixed-sign unit-cell null density is the actual
fixed-sign physical-cell null density. -/
-- @node: lower_null_record_density_embed
lemma lower_null_record_density_embed (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (b : Bool) (omega : Fin j → Bool) (o : Omega) (hx : X o ∈ Set.Icc 0 1) :
    lowerRecordDensity (lowerUnitNullFamily (lowerTau theta k)
      (lowerTau_mem_Ioc theta k j hp hk) b) o =
    lowerRecordDensity (lowerNullLaw theta k j hp (fun _ => b) omega)
      (lowerCellRecordEmbed k r o) := by
  have h := signedBumps_lowerCellEmbed k hk r (fun _ => b) (X o) hx
  change armProbability (lowerPropensity (lowerTau theta k) 1 (fun _ => b))
      (A o) (X o) * baselineDensity (Y o) =
    armProbability (lowerPropensity theta k (fun _ => b))
      (A o) (lowerCellEmbed k r (X o)) * baselineDensity (Y o)
  simp only [armProbability, lowerPropensity, h]
  simp [signedBumps, lowerTau]

/-- The actual null law restricted to a cell is the embedded canonical unit-cell
null law, with normalization k and one fixed shared sign. -/
-- @node: lower_null_cell_law_eq_embedded_unit
lemma lower_null_cell_law_eq_embedded_unit (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (b : Bool) (omega : Fin j → Bool) :
    (lowerUnitNullFamily (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) b).law.map
      (lowerCellRecordEmbed k r) = ENNReal.ofReal (k : ℝ) •
        (lowerNullLaw theta k j hp (fun _ => b) omega).law.restrict
          {o | X o ∈ lowerClosedCell k r} := by
  let g : Omega → ℝ≥0∞ := fun o => ENNReal.ofReal
    (lowerRecordDensity (lowerNullLaw theta k j hp (fun _ => b) omega) o)
  have hg : Measurable g := nuisance_density_measurable _ _
    (lower_nuisance_valid theta k j hp (fun _ => b) omega).1
  have heq : (lowerUnitNullFamily (lowerTau theta k)
      (lowerTau_mem_Ioc theta k j hp hk) b).law =
      densityBase.withDensity (g ∘ lowerCellRecordEmbed k r) := by
    change densityBase.withDensity _ = _
    apply withDensity_congr_ae
    have hs : ∀ᵐ o ∂densityBase, X o ∈ Set.Icc 0 1 := by
      have : IsFiniteMeasure unitVolume := by unfold unitVolume; infer_instance
      exact (Measure.quasiMeasurePreserving_fst
        (μ := unitVolume) (ν := Measure.count.prod unitVolume)).ae
        (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hs] with o ho
    exact congrArg ENNReal.ofReal (lower_null_record_density_embed theta k j hp hk r b omega o ho)
  rw [heq, lower_map_withDensity_comp _ _ (measurable_lowerCellRecordEmbed k r) _ hg,
    lowerCellRecordEmbed_map_densityBase k hk r, withDensity_smul_measure,
    ← restrict_withDensity (show MeasurableSet {o : Omega | X o ∈ lowerClosedCell k r} from
      measurableSet_Icc.preimage (by unfold X; fun_prop))]
  rfl

/-- Normalized restriction of the actual fixed-sign null record law to one cell. -/
-- @node: lowerLocalizedNullLaw
def lowerLocalizedNullLaw (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (r : Fin k) (b : Bool) (omega : Fin j → Bool) : Measure Omega :=
  ENNReal.ofReal (k : ℝ) • (lowerNullLaw theta k j hp (fun _ => b) omega).law.restrict
    {o | X o ∈ lowerClosedCell k r}

/-- The normalized physical-cell null law is a probability measure. -/
-- @node: lowerLocalizedNullLaw_probability
instance lowerLocalizedNullLaw_probability (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (r : Fin k) (b : Bool) (omega : Fin j → Bool) :
    IsProbabilityMeasure (lowerLocalizedNullLaw theta k j hp r b omega) := by
  have hk : 0 < k := Nat.zero_lt_of_lt r.isLt
  rw [lowerLocalizedNullLaw, ← lower_null_cell_law_eq_embedded_unit theta k j hp hk r b omega]
  exact Measure.isProbabilityMeasure_map (measurable_lowerCellRecordEmbed k r).aemeasurable

/-- Report the localized bump score and the actual treatment flags. -/
-- @node: lowerLocalizedCellData
def lowerLocalizedCellData (k m : ℕ) (r : Fin k) (o : Data m) :
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m :=
  (fun i => lowerBump ((k : ℝ) * X (o i) - r.val),
    (fun i => A (o i)), (fun i => A (o i)))

/-- Reporting the localized design is measurable. -/
-- @node: measurable_lowerLocalizedCellData
@[fun_prop] lemma measurable_lowerLocalizedCellData (k m : ℕ) (r : Fin k) :
    Measurable (lowerLocalizedCellData k m r) := by
  unfold lowerLocalizedCellData X A
  fun_prop

/-- Rescaling the covariates changes neither the reported design nor its shared sign. -/
-- @node: lowerLocalizedCellData_embed
lemma lowerLocalizedCellData_embed (k m : ℕ) (hk : 0 < k) (r : Fin k) (o : Data m) :
    lowerLocalizedCellData k m r (fun i => lowerCellRecordEmbed k r (o i)) =
      lowerUnitCellData m o := by
  unfold lowerLocalizedCellData lowerUnitCellData lowerCellRecordEmbed X A
  simp only [lowerCellEmbed_coordinate k hk r]

/-- At each fixed count, the iid physical-cell law reports exactly the canonical
fixed-sign unit-cell design. The latent sign is held fixed throughout the product. -/
-- @node: lower_localized_null_design_fixed_sign
lemma lower_localized_null_design_fixed_sign (theta : ℝ) (k j m : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (b : Bool) (omega : Fin j → Bool) :
    (Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega)).map
      (lowerLocalizedCellData k m r) =
    (dataLaw (lowerUnitNullFamily (lowerTau theta k)
      (lowerTau_mem_Ioc theta k j hp hk) b) m).map (lowerUnitCellData m) := by
  have he : lowerLocalizedNullLaw theta k j hp r b omega =
      (lowerUnitNullFamily (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) b).law.map
        (lowerCellRecordEmbed k r) :=
    (lower_null_cell_law_eq_embedded_unit theta k j hp hk r b omega).symm
  have : IsProbabilityMeasure
      ((lowerUnitNullFamily (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) b).law.map
        (lowerCellRecordEmbed k r)) :=
    Measure.isProbabilityMeasure_map (measurable_lowerCellRecordEmbed k r).aemeasurable
  simp_rw [he]
  rw [← Measure.pi_map_pi (fun _ => (measurable_lowerCellRecordEmbed k r).aemeasurable),
    Measure.map_map (measurable_lowerLocalizedCellData k m r)
      (by fun_prop)]
  congr 1
  funext o
  exact lowerLocalizedCellData_embed k m hk r o

/-- Mixing the single shared cell sign after iid sampling identifies the actual
localized design with the canonical design used in the Poisson coefficient bounds. -/
-- @node: lower_localized_null_design_eq_unit
lemma lower_localized_null_design_eq_unit (theta : ℝ) (k j m : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k) (omega : Fin j → Bool) :
    (∑ b : Bool, (Fintype.card Bool : ℝ≥0∞)⁻¹ •
      Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega)).map
        (lowerLocalizedCellData k m r) =
      lowerUnitCellDesign (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) m := by
  simp only [Fintype.sum_bool, Measure.map_add _ _
    (measurable_lowerLocalizedCellData k m r), Measure.map_smul,
    lower_localized_null_design_fixed_sign theta k j m hp hk r]
  unfold lowerUnitCellDesign uniformSampleMixture
    Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
  rw [Fintype.sum_bool, Measure.map_add _ _ (measurable_lowerUnitCellData m)]
  simp only [Measure.map_smul]

/-- On a closed physical cell, the complete sign field reduces to its cell sign,
including both endpoints where all neighboring bumps vanish. -/
-- @node: signedBumps_on_lowerClosedCell
lemma signedBumps_on_lowerClosedCell (k : ℕ) (hk : 0 < k) (r : Fin k)
    (lambda : Fin k → Bool) (x : ℝ) (hx : x ∈ lowerClosedCell k r) :
    signedBumps k lambda x = signValue (lambda r) * lowerBump ((k : ℝ) * x - r.val) := by
  have hp : (0 : ℝ) < k := by exact_mod_cast hk
  have hz : (k : ℝ) * x - r.val ∈ Set.Icc 0 1 := by
    change (r.val : ℝ) / k ≤ x ∧ x ≤ ((r.val : ℝ) + 1) / k at hx
    have hl := (div_le_iff₀ hp).1 hx.1
    have hu := (le_div_iff₀ hp).1 hx.2
    constructor <;> nlinarith
  have he : lowerCellEmbed k r ((k : ℝ) * x - r.val) = x := by
    unfold lowerCellEmbed
    field_simp
    ring
  simpa only [he] using signedBumps_lowerCellEmbed k hk r lambda _ hz

/-- Restricting the actual full sign-vector null law to a cell erases all other
propensity signs. This supplies the conditional law for the actual experiment. -/
-- @node: lower_null_law_restrict_depends_on_cell
lemma lower_null_law_restrict_depends_on_cell (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    (lowerNullLaw theta k j hp lambda omega).law.restrict
        {o | X o ∈ lowerClosedCell k r} =
      (lowerNullLaw theta k j hp (fun _ => lambda r) omega).law.restrict
        {o | X o ∈ lowerClosedCell k r} := by
  have hm : MeasurableSet {o : Omega | X o ∈ lowerClosedCell k r} :=
    measurableSet_Icc.preimage (by unfold X; fun_prop)
  rw [lower_null_law_withDensity, lower_null_law_withDensity,
    restrict_withDensity hm, restrict_withDensity hm]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hm] with o ho
  have he : signedBumps k lambda (X o) = signedBumps k (fun _ => lambda r) (X o) := by
    rw [signedBumps_on_lowerClosedCell k hk r lambda _ ho,
      signedBumps_on_lowerClosedCell k hk r (fun _ => lambda r) _ ho]
  simp only [lowerRecordDensity, lowerNullLaw, ObsLaw.ofNuisance, lowerNullDensity,
    armProbability, lowerPropensity, he]

/-- Every full-vector actual null component has the canonical normalized conditional
record law at its own cell sign. -/
-- @node: lower_null_full_sign_cell_law_eq_unit
lemma lower_null_full_sign_cell_law_eq_unit (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    ENNReal.ofReal (k : ℝ) • (lowerNullLaw theta k j hp lambda omega).law.restrict
        {o | X o ∈ lowerClosedCell k r} =
      (lowerUnitNullFamily (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk)
        (lambda r)).law.map (lowerCellRecordEmbed k r) := by
  rw [lower_null_law_restrict_depends_on_cell theta k j hp hk r lambda omega]
  exact (lower_null_cell_law_eq_embedded_unit theta k j hp hk r (lambda r) omega).symm

/-- Every actual null component assigns each physical cell mass exactly 1/k. -/
-- @node: lower_null_closed_cell_mass
lemma lower_null_closed_cell_mass (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    (lowerNullLaw theta k j hp lambda omega).law {o | X o ∈ lowerClosedCell k r} =
      (ENNReal.ofReal (k : ℝ))⁻¹ := by
  have hm : MeasurableSet {o : Omega | X o ∈ lowerClosedCell k r} :=
    measurableSet_Icc.preimage (by unfold X; fun_prop)
  have : IsProbabilityMeasure
      ((lowerUnitNullFamily (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk)
        (lambda r)).law.map (lowerCellRecordEmbed k r)) :=
    Measure.isProbabilityMeasure_map (measurable_lowerCellRecordEmbed k r).aemeasurable
  have he := congrArg (fun mu : Measure Omega => mu Set.univ)
    (lower_null_full_sign_cell_law_eq_unit theta k j hp hk r lambda omega)
  simp only [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    smul_eq_mul, measure_univ] at he
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact he)

/-- The fixed-count localized null design, with one sign shared by all records. -/
-- @node: lowerLocalizedCellDesign
def lowerLocalizedCellDesign (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (r : Fin k) (omega : Fin j → Bool) (m : ℕ) :
    Measure (Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Cell m) :=
  (∑ b : Bool, (Fintype.card Bool : ℝ≥0∞)⁻¹ •
    Measure.pi (fun _ : Fin m => lowerLocalizedNullLaw theta k j hp r b omega)).map
      (lowerLocalizedCellData k m r)

/-- Poisson count averaging of the actual localized design has exactly the canonical
coefficient, rather than merely an upper bound. -/
-- @node: lower_localized_poisson_coefficient_eq
lemma lower_localized_poisson_coefficient_eq (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (r : Fin k) (omega : Fin j → Bool)
    (xi : NNReal) (gamma : ℝ) (d : ℕ) :
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.coefficient
      (lowerLocalizedCellDesign theta k j hp r omega) xi (lowerTau theta k) gamma d =
      lowerPoissonCoefficient (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) xi gamma d := by
  have he : lowerLocalizedCellDesign theta k j hp r omega =
      lowerUnitCellDesign (lowerTau theta k) (lowerTau_mem_Ioc theta k j hp hk) := by
    funext m
    exact lower_localized_null_design_eq_unit theta k j m hp hk r omega
  rw [he]
  rfl

end CausalSmith.Stat.DensityEffectRoughNull
