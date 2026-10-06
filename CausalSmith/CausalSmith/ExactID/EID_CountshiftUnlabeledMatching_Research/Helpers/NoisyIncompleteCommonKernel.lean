module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.GaussianLikelihood
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.NoisyIncompleteExperiment

/-! The common unit-offset observation kernel for the incomplete-cover experiment.
Finite-product density identities identify the explicit normal likelihood tilts
with shifted Gaussian replicate laws. The kernel independently samples unchanged
count cells from their baseline laws, adds the fixed baseline vector to the
changing latent replicates, applies the unit Poisson kernel, and attaches unit
offsets. Its law identity matches the original Gaussian–Poisson experiment. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

set_option backward.isDefEq.respectTransparency false in
/-- Nonnegative product integrals factor over finitely many independent coordinates. -/
-- @node: kernel_lintegral_fin_prod
lemma kernel_lintegral_fin_prod {n : ℕ} {E : Type*}
    [MeasurableSpace E] (μ : Fin n → Measure E)
    [∀ i, SigmaFinite (μ i)] (f : Fin n → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp
      (by fun_prop)]
    simp only [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.coe_mk, MeasurableEquiv.symm_mk, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Fin.zero_succAbove,
      Equiv.symm_symm, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ, cast_eq]
    rw [lintegral_prod_mul (hf 0).aemeasurable
      (show Measurable (fun x : Fin n → E => ∏ i, f i.succ (x i)) by fun_prop).aemeasurable,
      ih _ _ (fun i => hf i.succ)]

/-- The finite-index version of the nonnegative product integral identity. -/
-- @node: kernel_lintegral_fintype_prod
lemma kernel_lintegral_fintype_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)] (f : ι → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp (by fun_prop)]
  simp only [MeasurableEquiv.coe_piCongrLeft, Function.comp_def,
    Equiv.piCongrLeft_apply_apply]
  simp_rw [← e.prod_comp]
  simpa only [Equiv.piCongrLeft_apply_apply] using
    kernel_lintegral_fin_prod (fun i => μ (e i)) (fun i => f (e i)) (fun i => hf (e i))

/-- Independent coordinate tilts give the product of the tilted coordinate measures. -/
-- @node: kernel_pi_withDensity
lemma kernel_pi_withDensity {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)] (f : ι → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) =
      Measure.pi (fun i => (μ i).withDensity (f i)) := by
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  simp_rw [withDensity_apply _ (hs _)]
  simp_rw [← lintegral_indicator (hs _) (f _)]
  rw [← kernel_lintegral_fintype_prod μ _ (fun i => (hf i).indicator (hs i))]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  congr 1
  funext x
  classical
  by_cases hx : x ∈ Set.univ.pi s
  · simp only [Set.mem_pi, Set.mem_univ, forall_true_left] at hx
    simp [Set.indicator_of_mem, hx]
  · have hi : ∃ i, x i ∉ s i := by simpa [Set.mem_pi] using hx
    obtain ⟨i, hi⟩ := hi
    rw [Set.indicator_of_notMem hx]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

/-- The explicit standard-normal exponential tilt is the normal law with shifted mean. -/
-- @node: normalTilt_withDensity
lemma normalTilt_withDensity (h : ℝ) :
    (gaussianReal 0 1).withDensity (fun x => ENNReal.ofReal (normalTilt h x)) =
      gaussianReal h 1 := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),
    gaussianReal_of_var_ne_zero _ (by norm_num),
    ← withDensity_mul _ (measurable_gaussianPDF 0 1)
      (by unfold normalTilt; fun_prop)]
  congr 1
  funext x
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  unfold gaussianPDFReal normalTilt
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  norm_num
  ring

/-- Tilting one coordinate of the standard normal vector shifts exactly that coordinate. -/
-- @node: normalCoordinateTiltLaw_eq_shifted
lemma normalCoordinateTiltLaw_eq_shifted {p : ℕ} (j : Fin p) (h : ℝ) :
    (Measure.pi (fun _ : Fin p => gaussianReal 0 1)).withDensity
      (fun x => ENNReal.ofReal (normalTilt h (x j))) =
        shiftedGaussianLaw (h • Pi.single j 1) := by
  classical
  let w : Fin p → ℝ → ℝ≥0∞ := fun i x => if i = j then ENNReal.ofReal (normalTilt h x) else 1
  have hw (i : Fin p) : Measurable (w i) := by dsimp [w]; unfold normalTilt; split_ifs <;> fun_prop
  have heq (i : Fin p) : (gaussianReal 0 1).withDensity (w i) =
      gaussianReal ((h • Pi.single j (1 : ℝ)) i) 1 := by
    by_cases hi : i = j
    · subst i; simpa [w] using normalTilt_withDensity h
    · simp [w, hi, Pi.single_apply, Ne.symm hi]
  haveI : ∀ i, SigmaFinite ((gaussianReal 0 1).withDensity (w i)) :=
    fun i => heq i ▸ inferInstance
  have hprod (x : Fin p → ℝ) : (∏ i, w i (x i)) = ENNReal.ofReal (normalTilt h (x j)) := by
    simp [w]
  simp_rw [← hprod]
  rw [kernel_pi_withDensity _ w hw, shiftedGaussianLaw_eq_pi]
  simp_rw [heq]

/-- The replicate likelihood produces independent Gaussian vectors with the alternative mean. -/
-- @node: normalReplicateTiltLaw_eq_pi_shifted
lemma normalReplicateTiltLaw_eq_pi_shifted {p n : ℕ} (j : Fin p) (h : ℝ) :
    normalReplicateTiltLaw (n := n) j h =
      Measure.pi (fun _ : Fin n => shiftedGaussianLaw (h • Pi.single j 1)) := by
  let w : Fin n → (Fin p → ℝ) → ℝ≥0∞ :=
    fun _ x => ENNReal.ofReal (normalTilt h (x j))
  have hw (r : Fin n) : Measurable (w r) := by dsimp [w]; unfold normalTilt; fun_prop
  haveI : ∀ r : Fin n, SigmaFinite
      ((Measure.pi (fun _ : Fin p => gaussianReal 0 1)).withDensity (w r)) := by
    intro r
    dsimp [w]
    rw [normalCoordinateTiltLaw_eq_shifted]
    infer_instance
  unfold normalReplicateTiltLaw normalReplicateReference normalReplicateLikelihood
  rw [show (fun x : Fin n → Fin p → ℝ => ENNReal.ofReal (∏ r, normalTilt h (x r j))) =
      (fun x => ∏ r, w r (x r)) by
        funext x; exact ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  rw [kernel_pi_withDensity _ w hw]
  simp_rw [w, normalCoordinateTiltLaw_eq_shifted]

/-- A fixed translation adds to the mean of an identity-covariance Gaussian vector. -/
-- @node: shiftedGaussianLaw_map_add
lemma shiftedGaussianLaw_map_add {p : ℕ} (a b : Fin p → ℝ) :
    (shiftedGaussianLaw a).map (fun x => b + x) = shiftedGaussianLaw (b + a) := by
  rw [shiftedGaussianLaw_eq_pi, shiftedGaussianLaw_eq_pi]
  rw [show (fun x : Fin p → ℝ => b + x) = (fun x i => b i + x i) by rfl,
    Measure.pi_map_pi (fun _ => (by fun_prop))]
  congr 1
  funext i
  have hg : HasLaw id (gaussianReal (a i) 1) (gaussianReal (a i) 1) :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  simpa only [Function.comp_def, id_eq, Pi.add_apply, add_comm (a i) (b i)] using
    (gaussianReal_const_add hg (b i)).map_eq

/-- In the changing environment, apply the Poisson law to the translated input; elsewhere sample the unchanged baseline count law. -/
-- @node: commonCountCellLaw
noncomputable def commonCountCellLaw {p n k : ℕ} (b : Fin k → Fin p → ℝ)
    (e : Fin k) (x : Fin n → Fin p → ℝ) (er : Fin k × Fin n) : Measure (Fin p → ℕ) :=
  if er.1 = e then unitPoissonKernel p (b e + x er.2)
  else (permutationCellLaw (b er.1)).snd

/-- Each conditional cell count law is a probability measure. -/
-- @node: commonCountCellLaw_probability
instance commonCountCellLaw_probability {p n k : ℕ} (b : Fin k → Fin p → ℝ)
    (e : Fin k) (x : Fin n → Fin p → ℝ) (er : Fin k × Fin n) :
    IsProbabilityMeasure (commonCountCellLaw b e x er) := by
  unfold commonCountCellLaw
  split_ifs <;> infer_instance

/-- Sample all count cells independently, using the supplied latent replicates only in the designated environment. -/
-- @node: commonCountKernel
noncomputable def commonCountKernel {p n k : ℕ} (b : Fin k → Fin p → ℝ)
    (e : Fin k) : Kernel (Fin n → Fin p → ℝ) ((Fin k × Fin n) → Fin p → ℕ) :=
  Kernel.mk (fun x => Measure.pi (commonCountCellLaw b e x)) (by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have heq (x : Fin n → Fin p → ℝ) :
        (Measure.pi (commonCountCellLaw b e x)) A =
          ∑' y : (Fin k × Fin n) → Fin p → ℕ,
            A.indicator (fun y => ∏ er, commonCountCellLaw b e x er {y er}) y := by
      rw [← Measure.tsum_indicator_apply_singleton _ A hA]
      simp_rw [Measure.pi_singleton]
    simp_rw [heq]
    apply Measurable.tsum
    intro y
    by_cases hy : y ∈ A
    · simp only [Set.indicator_of_mem hy]
      apply Finset.measurable_prod
      intro er _
      unfold commonCountCellLaw
      split_ifs
      · exact (Kernel.measurable_coe (unitPoissonKernel p) (MeasurableSet.singleton _)).comp
          (by fun_prop)
      · fun_prop
    · simp [Set.indicator_of_notMem hy])

/-- Independent conditional probability laws form a Markov kernel. -/
-- @node: commonCountKernel_markov
instance commonCountKernel_markov {p n k : ℕ} (b : Fin k → Fin p → ℝ)
    (e : Fin k) : IsMarkovKernel (commonCountKernel (n := n) b e) where
  isProbabilityMeasure x := by change IsProbabilityMeasure (Measure.pi _); infer_instance

/-- Independent shifted Gaussian inputs reproduce the experiment with the corresponding mean change in one environment. -/
-- @node: commonCountKernel_law
lemma commonCountKernel_law {p n k : ℕ} (b : Fin k → Fin p → ℝ)
    (e : Fin k) (a : Fin p → ℝ) :
    (commonCountKernel (n := n) b e) ∘ₘ
      (Measure.pi (fun _ : Fin n => shiftedGaussianLaw a)) =
    Measure.pi (fun er : Fin k × Fin n =>
      (permutationCellLaw (if er.1 = e then b e + a else b er.1)).snd) := by
  classical
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.bind_apply (MeasurableSet.singleton _) (Kernel.aemeasurable _)]
  change (∫⁻ x, (Measure.pi (commonCountCellLaw b e x)) {y}
      ∂Measure.pi (fun _ : Fin n => shiftedGaussianLaw a)) = _
  simp_rw [Measure.pi_singleton, Fintype.prod_prod_type]
  have hexpand (x : Fin n → Fin p → ℝ) :
      (∏ i : Fin k, ∏ r : Fin n, commonCountCellLaw b e x (i, r) {y (i, r)}) =
      (∏ r : Fin n, unitPoissonKernel p (b e + x r) {y (e, r)}) *
        ∏ i ∈ Finset.univ.erase e, ∏ r : Fin n, (permutationCellLaw (b i)).snd {y (i, r)} := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
    congr 1
    · simp [commonCountCellLaw]
    · apply Finset.prod_congr rfl
      intro i hi
      simp [commonCountCellLaw, (Finset.mem_erase.mp hi).1]
  simp_rw [hexpand]
  have hm (r : Fin n) : Measurable (fun z : Fin p → ℝ =>
      unitPoissonKernel p (b e + z) {y (e, r)}) :=
    (Kernel.measurable_coe (unitPoissonKernel p) (MeasurableSet.singleton _)).comp (by fun_prop)
  have hmprod : Measurable (fun x : Fin n → Fin p → ℝ =>
      ∏ r, unitPoissonKernel p (b e + x r) {y (e, r)}) := by
    apply Finset.measurable_prod
    intro r _
    exact (hm r).comp (measurable_pi_apply r)
  rw [lintegral_mul_const _ hmprod,
    kernel_lintegral_fintype_prod (fun _ : Fin n => shiftedGaussianLaw a)
      (fun r z => unitPoissonKernel p (b e + z) {y (e, r)}) hm]
  have hcell (r : Fin n) :
      (∫⁻ z, unitPoissonKernel p (b e + z) {y (e, r)} ∂shiftedGaussianLaw a) =
        (permutationCellLaw (b e + a)).snd {y (e, r)} := by
    rw [Measure.snd_apply (MeasurableSet.singleton _), permutationCellLaw,
      Measure.compProd_apply (measurable_snd (MeasurableSet.singleton _))]
    change (∫⁻ z, unitPoissonKernel p (b e + z) {y (e, r)} ∂shiftedGaussianLaw a) =
      ∫⁻ z, unitPoissonKernel p z {y (e, r)} ∂shiftedGaussianLaw (b e + a)
    rw [← shiftedGaussianLaw_map_add a (b e), lintegral_map
      (Kernel.measurable_coe _ (MeasurableSet.singleton _)) (by fun_prop)]
  simp_rw [hcell]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    simp [(Finset.mem_erase.mp hi).1]

/-- Attach constant unit offsets and arrange the count cells as an observed sample. -/
-- @node: unitCountObservation
noncomputable def unitCountObservation {p n : ℕ}
    (y : (Fin (p + 1) × Fin n) → Fin p → ℕ) : ObservedSample p n :=
  (fun _ _ _ => 1, fun e r => y (e, r))

/-- The common count kernel with the observed sample packaging and unit offsets. -/
-- @node: commonObservedKernel
noncomputable def commonObservedKernel {p n : ℕ} (b : Fin (p + 1) → Fin p → ℝ)
    (e : Fin (p + 1)) : Kernel (Fin n → Fin p → ℝ) (ObservedSample p n) :=
  (commonCountKernel (n := n) b e).map unitCountObservation

/-- Packaging a probability kernel as an observed sample preserves its Markov property. -/
-- @node: commonObservedKernel_markov
instance commonObservedKernel_markov {p n : ℕ} (b : Fin (p + 1) → Fin p → ℝ)
    (e : Fin (p + 1)) : IsMarkovKernel (commonObservedKernel (n := n) b e) := by
  unfold commonObservedKernel
  exact Kernel.IsMarkovKernel.map _ (by unfold unitCountObservation; fun_prop)

/-- The common observation kernel reproduces the original finite Gaussian–Poisson experiment after a mean shift in the designated environment. -/
-- @node: commonObservedKernel_law
lemma commonObservedKernel_law {p n : ℕ} (b : Fin (p + 1) → Fin p → ℝ)
    (e : Fin (p + 1)) (a : Fin p → ℝ) :
    ((Measure.pi (fun _ : Fin n => shiftedGaussianLaw a)) ⊗ₘ
      commonObservedKernel b e).map Prod.snd =
    (unitGaussianExperimentMeasure (n := n)
      (fun i => if i = e then b e + a else b i)).map
        (fun ω => (fun _ _ _ => (1 : ℝ), fun i r => (ω (i, r)).2)) := by
  change (Measure.pi (fun _ : Fin n => shiftedGaussianLaw a) ⊗ₘ
    commonObservedKernel b e).snd = _
  rw [Measure.snd_compProd, commonObservedKernel, ← Measure.map_comp _ _
    (by unfold unitCountObservation; fun_prop), commonCountKernel_law]
  unfold unitGaussianExperimentMeasure
  haveI : ∀ er : Fin (p + 1) × Fin n, IsProbabilityMeasure
      ((permutationCellLaw (if er.1 = e then b e + a else b er.1)).map Prod.snd) :=
    fun _ => Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hp := Measure.pi_map_pi
    (X := fun _ : Fin (p + 1) × Fin n => PermutationCell p)
    (Y := fun _ : Fin (p + 1) × Fin n => Fin p → ℕ)
    (μ := fun er : Fin (p + 1) × Fin n =>
      permutationCellLaw (if er.1 = e then b e + a else b er.1))
    (f := fun _ => (Prod.snd : PermutationCell p → Fin p → ℕ))
    (hμ := fun er => (inferInstance : SigmaFinite
      ((permutationCellLaw (if er.1 = e then b e + a else b er.1)).map
        (Prod.snd : PermutationCell p → Fin p → ℕ))))
    (fun _ => measurable_snd.aemeasurable)
  change (Measure.pi (fun er => (permutationCellLaw
    (if er.1 = e then b e + a else b er.1)).map Prod.snd)).map unitCountObservation = _
  rw [← hp, Measure.map_map (by unfold unitCountObservation; fun_prop) (by fun_prop)]
  rfl

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
