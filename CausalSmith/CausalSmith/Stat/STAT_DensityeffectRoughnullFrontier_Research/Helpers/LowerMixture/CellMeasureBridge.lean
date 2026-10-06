module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.CellLawBridge
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.MixtureTransfer
public import Mathlib.MeasureTheory.Integral.Pi
/-!
Actual finite-prior sample densities and their Radon--Nikodym derivatives. The cell
localization theorem lifts the pointwise likelihood bridge to equality of measures,
retaining a shared latent sign across all records before taking the prior average.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull
/-- Tonelli factorization of nonnegative products on a finite sample space. -/
-- @node: lower_lintegral_fin_prod
lemma lower_lintegral_fin_prod {E : Type*} [MeasurableSpace E]
    (n : ℕ) (mu : Fin n → Measure E) [∀ i, SigmaFinite (mu i)] (f : Fin n → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi mu) =
      ∏ i, ∫⁻ x, f i x ∂mu i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : Measurable (fun x : Fin (n + 1) → E => ∏ i, f i (x i)) := by
      fun_prop
    rw [← ((measurePreserving_piFinSuccAbove mu 0).symm).lintegral_comp hm]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    rw [lintegral_prod_mul (g := fun x : Fin n → E => ∏ i, f i.succ (x i)) (hf 0).aemeasurable
      ((Finset.measurable_prod Finset.univ
        (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable),
      ih (fun i => mu i.succ) (fun i => f i.succ) (fun i => hf i.succ)]
/-- A finite iid product of density-weighted measures has the product density. -/
-- @node: lower_pi_withDensity
lemma lower_pi_withDensity {E : Type*} [MeasurableSpace E]
    (mu : Measure E) [SigmaFinite mu] (f : E → ℝ≥0∞) (hf : Measurable f)
    [SigmaFinite (mu.withDensity f)] (n : ℕ) :
    Measure.pi (fun _ : Fin n => mu.withDensity f) =
      (Measure.pi (fun _ : Fin n => mu)).withDensity (fun x => ∏ i, f (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [lower_lintegral_fin_prod n (fun i => mu.restrict (s i)) (fun _ => f) (fun _ => hf)]
  simp_rw [withDensity_apply _ (hs _)]


/-- The exact iid record density against the product reference measure. -/
-- @node: lowerSampleDensity
def lowerSampleDensity (P : ObsLaw) (n : ℕ) (o : Data n) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (lowerRecordDensity P (o i))

/-- Actual constructed null observations have their specified record density. -/
-- @node: lower_null_law_withDensity
lemma lower_null_law_withDensity (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    (lowerNullLaw theta k j hp lambda omega).law =
      densityBase.withDensity (fun o => ENNReal.ofReal
        (lowerRecordDensity (lowerNullLaw theta k j hp lambda omega) o)) := rfl

/-- Actual constructed alternative observations have their specified record density. -/
-- @node: lower_alternative_law_withDensity
lemma lower_alternative_law_withDensity (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    (lowerAlternativeLaw theta k j hp lambda omega).law =
      densityBase.withDensity (fun o => ENNReal.ofReal
        (lowerRecordDensity (lowerAlternativeLaw theta k j hp lambda omega) o)) := rfl

/-- The null sample density multiplies iid factors, without independently mixing each record. -/
-- @node: lower_null_dataLaw_withDensity
lemma lower_null_dataLaw_withDensity (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool) (n : ℕ) :
    dataLaw (lowerNullLaw theta k j hp lambda omega) n =
      (Measure.pi (fun _ : Fin n => densityBase)).withDensity
        (lowerSampleDensity (lowerNullLaw theta k j hp lambda omega) n) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let : IsFiniteMeasure densityBase := by unfold densityBase; infer_instance
  have hm := nuisance_density_measurable _ _
    (lower_nuisance_valid theta k j hp lambda omega).1
  change Measure.pi (fun _ : Fin n => (lowerNullLaw theta k j hp lambda omega).law) = _
  rw [lower_null_law_withDensity]
  exact lower_pi_withDensity densityBase _ hm n

/-- The alternative sample density multiplies iid factors for one fixed latent sign vector. -/
-- @node: lower_alternative_dataLaw_withDensity
lemma lower_alternative_dataLaw_withDensity (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool) (n : ℕ) :
    dataLaw (lowerAlternativeLaw theta k j hp lambda omega) n =
      (Measure.pi (fun _ : Fin n => densityBase)).withDensity
        (lowerSampleDensity (lowerAlternativeLaw theta k j hp lambda omega) n) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let : IsFiniteMeasure densityBase := by unfold densityBase; infer_instance
  have hm := nuisance_density_measurable _ _
    (lower_nuisance_valid theta k j hp lambda omega).2
  change Measure.pi (fun _ : Fin n => (lowerAlternativeLaw theta k j hp lambda omega).law) = _
  rw [lower_alternative_law_withDensity]
  exact lower_pi_withDensity densityBase _ hm n


/-- Each specified observed record density is measurable. -/
-- @node: lowerRecordDensity_measurable
@[fun_prop] lemma lowerRecordDensity_measurable (P : ObsLaw) :
    Measurable (fun o => ENNReal.ofReal (lowerRecordDensity P o)) := by
  exact nuisance_density_measurable P.e P.eta
    ⟨P.e_measurable, P.eta_measurable, P.e_range, P.eta_nonneg,
      P.eta_integrable, P.eta_normalized⟩

/-- Products of record densities are measurable on the sample space. -/
-- @node: lowerSampleDensity_measurable
@[fun_prop] lemma lowerSampleDensity_measurable (P : ObsLaw) (n : ℕ) :
    Measurable (lowerSampleDensity P n) := by
  unfold lowerSampleDensity
  exact Finset.measurable_prod Finset.univ
    (fun i _ => (lowerRecordDensity_measurable P).comp (measurable_pi_apply i))

/-- Finite averaging commutes with density construction. -/
-- @node: lower_withDensity_finset_sum
lemma lower_withDensity_finset_sum {E S : Type*} [MeasurableSpace E]
    (mu : Measure E) (f : S → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (s : Finset S) :
    mu.withDensity (fun o => ∑ i ∈ s, f i o) = ∑ i ∈ s, mu.withDensity (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [show (fun o => f a o + ∑ i ∈ s, f i o) =
      f a + (fun o => ∑ i ∈ s, f i o) from rfl,
      withDensity_add_left (hf a), ih]

/-- Density of the finite uniform prior, averaging whole sample likelihoods. -/
-- @node: lowerUniformSampleDensity
def lowerUniformSampleDensity {S : Type*} [Fintype S]
    (family : S → ObsLaw) (n : ℕ) (o : Data n) : ℝ≥0∞ :=
  (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ s, lowerSampleDensity (family s) n o

/-- The finite-prior density is measurable. -/
-- @node: lowerUniformSampleDensity_measurable
@[fun_prop] lemma lowerUniformSampleDensity_measurable {S : Type*} [Fintype S]
    (family : S → ObsLaw) (n : ℕ) : Measurable (lowerUniformSampleDensity family n) := by
  unfold lowerUniformSampleDensity
  fun_prop

/-- The actual observation mixture has its averaged iid density against the common reference. -/
-- @node: lower_uniformSampleMixture_withDensity
lemma lower_uniformSampleMixture_withDensity {S : Type*} [Fintype S] [Nonempty S]
    (family : S → ObsLaw)
    (hlaw : ∀ s, (family s).law = densityBase.withDensity
      (fun o => ENNReal.ofReal (lowerRecordDensity (family s) o))) (n : ℕ) :
    uniformSampleMixture n family =
      (Measure.pi (fun _ : Fin n => densityBase)).withDensity
        (lowerUniformSampleDensity family n) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let : IsFiniteMeasure densityBase := by unfold densityBase; infer_instance
  have hi (s : S) : dataLaw (family s) n =
      (Measure.pi (fun _ : Fin n => densityBase)).withDensity
        (lowerSampleDensity (family s) n) := by
    let : IsProbabilityMeasure (densityBase.withDensity
        (fun o => ENNReal.ofReal (lowerRecordDensity (family s) o))) := by
      rw [← hlaw s]; infer_instance
    change Measure.pi (fun _ : Fin n => (family s).law) = _
    rw [hlaw s]
    exact lower_pi_withDensity densityBase _ (lowerRecordDensity_measurable _) n
  simp only [uniformSampleMixture, Causalean.Stat.Minimax.Mixture.uniformMixture,
    Causalean.Stat.mixture, hi]
  unfold lowerUniformSampleDensity
  rw [show (fun o : Data n => (Fintype.card S : ℝ≥0∞)⁻¹ *
      ∑ s, lowerSampleDensity (family s) n o) =
    (Fintype.card S : ℝ≥0∞)⁻¹ • (fun o => ∑ s, lowerSampleDensity (family s) n o) from rfl,
    withDensity_smul _ (by fun_prop),
    lower_withDensity_finset_sum _ _ (fun s => lowerSampleDensity_measurable _ _) ]
  simp only [Finset.smul_sum]


/-- Null record densities are positive everywhere, including outside the unit support. -/
-- @node: lower_null_recordDensity_pos
lemma lower_null_recordDensity_pos (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (o : Omega) : 0 < lowerRecordDensity (lowerNullLaw theta k j hp lambda omega) o := by
  have ht := lowerTau_mem_Icc theta k j hp
  have hf := abs_le.mp (signedBumps_abs_le_one k lambda (X o))
  have hb := lower_baseline_valid.2.1 (Y o)
  have hpi : 0 < armProbability (lowerPropensity theta k lambda) (A o) (X o) := by
    cases h : A o <;> simp only [armProbability, lowerPropensity,
      Bool.false_eq_true, if_false, if_true] <;> nlinarith [ht.1, ht.2, hf.1, hf.2]
  exact mul_pos hpi (by change 0 < baselineDensity (Y o); linarith)

/-- A finite prior density cannot be infinite. -/
-- @node: lowerUniformSampleDensity_ne_top
lemma lowerUniformSampleDensity_ne_top {S : Type*} [Fintype S] [Nonempty S]
    (family : S → ObsLaw) (n : ℕ) (o : Data n) :
    lowerUniformSampleDensity family n o ≠ ∞ := by
  unfold lowerUniformSampleDensity lowerSampleDensity
  apply ENNReal.mul_ne_top
  · simp [Fintype.card_ne_zero]
  · exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top))

/-- A finite nonempty prior on the constructed null laws has a strictly positive sample density. -/
-- @node: lower_null_uniform_density_ne_zero
lemma lower_null_uniform_density_ne_zero {S : Type*} [Fintype S] [Nonempty S]
    (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : S → Fin k → Bool) (omega : S → Fin j → Bool) (n : ℕ) (o : Data n) :
    lowerUniformSampleDensity (fun s => lowerNullLaw theta k j hp (lambda s) (omega s))
      n o ≠ 0 := by
  classical
  unfold lowerUniformSampleDensity lowerSampleDensity
  apply mul_ne_zero
  · simp
  · intro h
    let s : S := Classical.choice inferInstance
    have hz := (Finset.sum_eq_zero_iff).mp h s (Finset.mem_univ s)
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (ENNReal.ofReal_pos.mpr
      (lower_null_recordDensity_pos theta k j hp (lambda s) (omega s) (o i))))) hz

/-- The actual alternative finite prior is obtained by weighting the matching actual null
prior by the quotient of their sample densities. Both priors retain one shared sign per law. -/
-- @node: lower_sign_mixture_withDensity_quotient
lemma lower_sign_mixture_withDensity_quotient {S : Type*} [Fintype S] [Nonempty S]
    (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : S → Fin k → Bool) (omega : S → Fin j → Bool) (n : ℕ) :
    let nullFamily := fun s => lowerNullLaw theta k j hp (lambda s) (omega s)
    let altFamily := fun s => lowerAlternativeLaw theta k j hp (lambda s) (omega s)
    uniformSampleMixture n altFamily = (uniformSampleMixture n nullFamily).withDensity
      (fun o => lowerUniformSampleDensity altFamily n o /
        lowerUniformSampleDensity nullFamily n o) := by
  dsimp only
  rw [lower_uniformSampleMixture_withDensity _
      (fun s => lower_alternative_law_withDensity theta k j hp (lambda s) (omega s)),
    lower_uniformSampleMixture_withDensity _
      (fun s => lower_null_law_withDensity theta k j hp (lambda s) (omega s)),
    ← withDensity_mul _ (lowerUniformSampleDensity_measurable _ _) (by fun_prop)]
  congr 1
  funext o
  exact (ENNReal.mul_div_cancel
    (lower_null_uniform_density_ne_zero theta k j hp lambda omega n o)
    (lowerUniformSampleDensity_ne_top _ n o)).symm


/-- Alternative record densities are nonnegative everywhere under the construction parameters. -/
-- @node: lower_alternative_recordDensity_nonneg
lemma lower_alternative_recordDensity_nonneg (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (o : Omega) : 0 ≤ lowerRecordDensity (lowerAlternativeLaw theta k j hp lambda omega) o := by
  have ht := lowerTau_mem_Icc theta k j hp
  have hf := abs_le.mp (signedBumps_abs_le_one k lambda (X o))
  have hb := lower_baseline_valid.2.1 (Y o)
  have he := abs_le.mp (lower_perturbation_abs_le theta k j hp lambda omega (X o) (Y o))
  have hpi : 0 ≤ armProbability (lowerPropensity theta k lambda) (A o) (X o) := by
    cases h : A o <;> simp only [armProbability, lowerPropensity,
      Bool.false_eq_true, if_false, if_true] <;> nlinarith [ht.1, ht.2, hf.1, hf.2]
  apply mul_nonneg hpi
  change 0 ≤ lowerAlternativeDensity theta k j lambda omega (A o) (X o) (Y o)
  cases h : A o <;> simp only [lowerAlternativeDensity, Bool.false_eq_true,
    if_false, if_true] <;> linarith [he.1]

/-- The binary whole-sample mixture density is the nonnegative real density used by the
pointwise cell-law bridge, with the fair prior's factor one half. -/
-- @node: lower_bool_sample_density_eq_ofReal
lemma lower_bool_sample_density_eq_ofReal (family : Bool → ObsLaw)
    (h : ∀ b o, 0 ≤ lowerRecordDensity (family b) o) (n : ℕ) (o : Data n) :
    lowerUniformSampleDensity family n o = ENNReal.ofReal
      ((1 / 2 : ℝ) * ∑ b : Bool, ∏ i, lowerRecordDensity (family b) (o i)) := by
  have hprod (b : Bool) : ENNReal.ofReal (∏ i, lowerRecordDensity (family b) (o i)) =
      ∏ i, ENNReal.ofReal (lowerRecordDensity (family b) (o i)) :=
    ENNReal.ofReal_prod_of_nonneg (fun i _ => h b (o i))
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg
    (fun b _ => Finset.prod_nonneg (fun i _ => h b (o i)))]
  simp only [lowerUniformSampleDensity, lowerSampleDensity, hprod, Fintype.card_bool]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- For cell-localized records, the density quotient of the actual two-sign sample
mixtures is exactly the nonnegative cell likelihood expansion (30). -/
-- @node: lower_cell_sample_density_quotient
lemma lower_cell_sample_density_quotient {M : ℕ} (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (r : Fin k) (o : Data M) (u : Fin M → ℝ)
    (hcell : ∀ b i, signedBumps k (Function.update lambda r b) (X (o i)) = signValue b * u i) :
    lowerUniformSampleDensity
        (fun b => lowerAlternativeLaw theta k j hp (Function.update lambda r b) omega) M o /
      lowerUniformSampleDensity
        (fun b => lowerNullLaw theta k j hp (Function.update lambda r b) omega) M o =
      ENNReal.ofReal (cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j) u
        (fun i => A (o i))
        (fun i => signedBumps j omega (Y (o i)) / baselineDensity (Y (o i)))) := by
  rw [lower_bool_sample_density_eq_ofReal _
      (fun b o => lower_alternative_recordDensity_nonneg theta k j hp _ omega o),
    lower_bool_sample_density_eq_ofReal _
      (fun b o => (lower_null_recordDensity_pos theta k j hp _ omega o).le)]
  rw [← ENNReal.ofReal_div_of_pos]
  · rw [cellAlternativeRatio_eq_lowerLaw_cellMixture theta k j hp lambda omega r
      (fun i => X (o i)) (fun i => Y (o i)) (fun i => A (o i)) u hcell]
    congr 1
    have ho (i : Fin M) : (X (o i), A (o i), Y (o i)) = o i := rfl
    simp_rw [ho]
    ring
  · apply mul_pos (by norm_num)
    exact Finset.sum_pos (fun b _ => Finset.prod_pos (fun i _ =>
      lower_null_recordDensity_pos theta k j hp _ omega (o i))) Finset.univ_nonempty


/-- On a measurable cell-localization event, the actual alternative mixture is the actual
null mixture weighted by the paper's cell likelihood. No posterior law is assumed. -/
-- @node: lower_cell_mixture_withDensity
lemma lower_cell_mixture_withDensity {M : ℕ} (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (r : Fin k) (s : Set (Data M)) (hs : MeasurableSet s) (u : Data M → Fin M → ℝ)
    (hcell : ∀ o ∈ s, ∀ b i,
      signedBumps k (Function.update lambda r b) (X (o i)) = signValue b * u o i) :
    (uniformSampleMixture M (fun b =>
      lowerAlternativeLaw theta k j hp (Function.update lambda r b) omega)).restrict s =
    ((uniformSampleMixture M (fun b =>
      lowerNullLaw theta k j hp (Function.update lambda r b) omega)).restrict s).withDensity
      (fun o => ENNReal.ofReal (cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j)
        (u o) (fun i => A (o i))
        (fun i => signedBumps j omega (Y (o i)) / baselineDensity (Y (o i))))) := by
  rw [lower_sign_mixture_withDensity_quotient theta k j hp
    (fun b => Function.update lambda r b) (fun _ => omega) M, restrict_withDensity hs]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hs] with o ho
  exact lower_cell_sample_density_quotient theta k j hp lambda omega r o (u o) (hcell o ho)

/-- The Radon--Nikodym derivative of the actual alternative prior relative to its actual
null prior is the quotient of their averaged whole-sample densities. -/
-- @node: lower_sign_mixture_rnDeriv
lemma lower_sign_mixture_rnDeriv {S : Type*} [Fintype S] [Nonempty S]
    (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : S → Fin k → Bool) (omega : S → Fin j → Bool) (n : ℕ) :
    let nullFamily := fun s => lowerNullLaw theta k j hp (lambda s) (omega s)
    let altFamily := fun s => lowerAlternativeLaw theta k j hp (lambda s) (omega s)
    (uniformSampleMixture n altFamily).rnDeriv (uniformSampleMixture n nullFamily) =ᵐ[
      uniformSampleMixture n nullFamily]
      (fun o => lowerUniformSampleDensity altFamily n o /
        lowerUniformSampleDensity nullFamily n o) := by
  dsimp only
  let : IsProbabilityMeasure (uniformSampleMixture n
      (fun s => lowerNullLaw theta k j hp (lambda s) (omega s))) := by
    let : ∀ s, IsProbabilityMeasure (dataLaw (lowerNullLaw theta k j hp (lambda s) (omega s)) n) :=
      fun s => by unfold dataLaw; infer_instance
    exact Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability _
  rw [lower_sign_mixture_withDensity_quotient theta k j hp lambda omega n]
  exact Measure.rnDeriv_withDensity _ (by fun_prop)
end CausalSmith.Stat.DensityEffectRoughNull
