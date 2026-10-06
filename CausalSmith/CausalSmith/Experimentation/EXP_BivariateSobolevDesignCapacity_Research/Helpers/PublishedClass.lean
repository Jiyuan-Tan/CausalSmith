module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.OutcomeLaws
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.LowerConverse
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionBudget
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.TFullDesignLower
public import Causalean.Mathlib.Probability.ProductAbsolutelyContinuous
public import Mathlib.Analysis.Asymptotics.Defs

/-! # Published prognostic law classes and exact capacity transfer

The prognostic function is pinned to each law's conditional kernel. The uniform class
retains arbitrary square-integrable outcomes; Gaussian completions are a strict subclass.
The larger class permits intercepts and fixed covariate-density bounds and receives a
converse only. Its original prognostic L² bound is retained.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The larger published correctly specified class, with intercepts and a prognostic L² bound. -/
def boundedDensityClass (d : ℕ) (s lower upper : ℝ) : Set (OutcomeLaw d) :=
  {P | CovDensityBounds P lower upper ∧ FiniteOutcomeMoments P ∧
    (∫ u, prognosisOf P u ^ 2 ∂covMarginal P) ≤ 1 ∧
    ∃ (intercept : ℝ) (m : CenteredL2Fn d), SobolevClass d s m ∧
      prognosisOf P =ᵐ[cubeMeasure d] fun u => intercept + m.val u}
/-- Covariate projection of the iid single-unit sample. -/
def sampleCovariates {n d : ℕ} (xs : Fin n → Cube d × ℝ × ℝ) : Covariates n d :=
  fun i => (xs i).1
/-- Borel measurability of the covariate projection on the full experiment. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: publishedCovariates_measurable
lemma publishedCovariates_measurable (n d : ℕ) :
    Measurable (fun ω : (Fin n → Cube d × ℝ × ℝ) × Signs n =>
      sampleCovariates ω.1) := by
  unfold sampleCovariates
  fun_prop
/-- The iid-outcome experiment is a probability law.](goal) This uses [the stated conclusion](goal). -/
-- @node: publishedExperiment_probability
lemma publishedExperiment_probability {n d : ℕ} (P : OutcomeLaw d) (π : Design n d) :
    IsProbabilityMeasure (publishedExperiment P π) := by
  let : IsMarkovKernel π.val := π.property
  unfold publishedExperiment
  infer_instance
/-- Published admissibility: iid pre-assignment schedules, conditional fairness and
conditional independence given the observed original covariate array. -/
def PublishedAdmissible {n d : ℕ} (π : Design n d) : Prop :=
  (∀ᵐ x ∂covLaw n d, ∀ i, ∫ z, sgn (z i) ∂π.val x = 0) ∧
    ∀ P : OutcomeLaw d,
    BoundedPositiveCovDensity P → FiniteOutcomeMoments P →
    letI := publishedExperiment_probability P π
    CondIndepFun (MeasurableSpace.comap
      (fun ω : (Fin n → Cube d × ℝ × ℝ) × Signs n => sampleCovariates ω.1) inferInstance)
      (publishedCovariates_measurable n d).comap_le
      (fun ω => ω.2) (fun ω i => (ω.1 i).2) (publishedExperiment P π)
/-- Replacing a design on a cube-null set preserves every iid experiment whose
covariate marginal is absolutely continuous with respect to the cube law. Under [the stated conditions](hyp:hac,heq), [the asserted mathematical result follows](goal). -/
-- @node: publishedExperiment_eq_of_ae_kernel
lemma publishedExperiment_eq_of_ae_kernel {n d : ℕ} (P : OutcomeLaw d)
    (hac : covMarginal P ≪ cubeMeasure d) (π ρ : Design n d)
    (heq : (fun x => π.val x) =ᵐ[covLaw n d] (fun x => ρ.val x)) :
    publishedExperiment P π = publishedExperiment P ρ := by
  letI := cubeMeasure_probability d
  letI : IsMarkovKernel π.val := π.property
  letI : IsMarkovKernel ρ.val := ρ.property
  letI : IsProbabilityMeasure (covMarginal P) := by
    unfold covMarginal
    infer_instance
  have hmap : (Measure.pi (fun _ : Fin n => P.toMeasure)).map sampleCovariates =
      Measure.pi (fun _ : Fin n => covMarginal P) := by
    exact Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)
  have hprod := Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
    (covMarginal P) (cubeMeasure d) hac n
  have hsample : ∀ᵐ xs ∂Measure.pi (fun _ : Fin n => P.toMeasure),
      π.val (sampleCovariates xs) = ρ.val (sampleCovariates xs) := by
    apply ae_of_ae_map (f := sampleCovariates (n := n) (d := d))
      (μ := Measure.pi (fun _ : Fin n => P.toMeasure))
      (p := fun x => π.val x = ρ.val x)
      (by
        apply Measurable.aemeasurable
        unfold sampleCovariates
        fun_prop)
    rw [hmap]
    exact hprod.ae_le heq
  apply Measure.compProd_congr
  exact hsample

/-- A covariate-only assignment kernel is independent of every outcome mechanism
conditional on the covariates, by uniqueness of its conditional distribution. [The asserted mathematical result follows](goal). -/
-- @node: outcomeIndependent_of_covariate_kernel
lemma outcomeIndependent_of_covariate_kernel {n d : ℕ} (π : Design n d) :
    OutcomeIndependentKernel π.val := by
  intro hπ μX hμ κ hκ
  letI := hπ
  letI := hμ
  letI := hκ
  let ν := μX ⊗ₘ κ
  let K : Kernel (Covariates n d × Sched n) (Signs n) :=
    π.val.comap Prod.fst measurable_fst
  let E := ν ⊗ₘ K
  have hfst : E.map Prod.fst = ν := Measure.fst_compProd ν K
  have hbase : E.map (fun ω => ω.1.1) = μX := by
    rw [show (fun ω : (Covariates n d × Sched n) × Signs n => ω.1.1) =
      Prod.fst ∘ Prod.fst from rfl, ← Measure.map_map measurable_fst measurable_fst,
      hfst]
    exact Measure.fst_compProd μX κ
  have hjoint : E.map (fun ω => (ω.1.1, ω.2)) = μX ⊗ₘ π.val := by
    apply Measure.ext_prod
    intro s t hs ht
    rw [Measure.map_apply (by fun_prop) (hs.prod ht), Measure.compProd_apply_prod hs ht]
    dsimp only [E]
    rw [Measure.compProd_apply ((by fun_prop : Measurable
      (fun ω : (Covariates n d × Sched n) × Signs n => (ω.1.1, ω.2)))
      (hs.prod ht))]
    change (∫⁻ xy, K xy {z | (xy.1, z) ∈ s ×ˢ t} ∂ν) = _
    have hinner : (fun xy : Covariates n d × Sched n =>
        K xy {z | (xy.1, z) ∈ s ×ˢ t}) =
        fun xy => s.indicator (fun x => π.val x t) xy.1 := by
      funext xy
      by_cases hx : xy.1 ∈ s <;> simp [K, hx, Set.indicator]
    rw [hinner]
    dsimp only [ν]
    rw [Measure.lintegral_compProd (μ := μX) (κ := κ)
      (f := fun xy => s.indicator (fun x => π.val x t) xy.1)
      (((Kernel.measurable_coe π.val ht).indicator hs).comp measurable_fst)]
    simp only [lintegral_const, measure_univ, mul_one]
    exact lintegral_indicator hs _
  have hfull : condDistrib Prod.snd Prod.fst E =ᵐ[E.map Prod.fst] K := by
    apply condDistrib_ae_eq_of_measure_eq_compProd _ (by fun_prop)
    rw [hfst]
    change E.map id = E
    exact Measure.map_id
  have hsmall : condDistrib Prod.snd (fun ω => ω.1.1) E =ᵐ[μX] π.val := by
    have h := condDistrib_ae_eq_of_measure_eq_compProd
      (μ := E) (fun ω => ω.1.1) (Y := Prod.snd) (by fun_prop)
      (κ := π.val) (by rw [hbase]; exact hjoint)
    rwa [hbase] at h
  have hsmall' : ∀ᵐ xy ∂ν,
      condDistrib Prod.snd (fun ω => ω.1.1) E xy.1 = π.val xy.1 := by
    apply ae_of_ae_map (f := Prod.fst) (μ := ν)
      (p := fun x => condDistrib Prod.snd (fun ω => ω.1.1) E x = π.val x)
      measurable_fst.aemeasurable
    change ∀ᵐ x ∂ν.map Prod.fst, _
    rw [show ν.map Prod.fst = μX from Measure.fst_compProd μX κ]
    exact hsmall
  have hci : CondIndepFun
      (MeasurableSpace.comap (fun ω : (Covariates n d × Sched n) × Signs n =>
        ω.1.1) inferInstance) measurable_fst.fst.comap_le
      (fun ω => ω.1.2) Prod.snd E := by
    rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
      (by fun_prop) (by fun_prop) (by fun_prop)]
    change condDistrib Prod.snd Prod.fst E =ᵐ[E.map Prod.fst]
      (condDistrib Prod.snd (fun ω => ω.1.1) E).prodMkRight (Sched n)
    rw [hfst] at hfull ⊢
    filter_upwards [hfull, hsmall'] with xy hxy hx
    simpa [K, Kernel.prodMkRight, Kernel.comap_apply, hx] using hxy
  exact hci.symm

/-- Pushing the base sample through a Borel observation map commutes with drawing
an assignment from a kernel that depends only on that observation. Under [the stated conditions](hyp:hf), [the asserted mathematical result follows](goal). -/
-- @node: assignment_joint_map
lemma assignment_joint_map {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (ν : Measure α)
    [IsProbabilityMeasure ν] (f : α → β) (hf : Measurable f)
    (κ : Kernel β γ) [IsMarkovKernel κ] :
    (ν ⊗ₘ κ.comap f hf).map (fun ω => (f ω.1, ω.2)) = ν.map f ⊗ₘ κ := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (by fun_prop) (hs.prod ht),
    Measure.compProd_apply_prod hs ht,
    Measure.compProd_apply ((by fun_prop : Measurable
      (fun ω : α × γ => (f ω.1, ω.2))) (hs.prod ht))]
  have hinner : (fun x => κ.comap f hf x {z | (f x, z) ∈ s ×ˢ t}) =
      fun x => s.indicator (fun y => κ y t) (f x) := by
    funext x
    by_cases hx : f x ∈ s <;> simp [hx, Set.indicator]
  change (∫⁻ x, κ.comap f hf x {z | (f x, z) ∈ s ×ˢ t} ∂ν) = _
  rw [hinner, ← lintegral_indicator hs (fun y => κ y t),
    lintegral_map ((Kernel.measurable_coe κ ht).indicator hs) hf]

/-- Assignment conditioned on all sampled outcomes has the same conditional law as
assignment conditioned on the observed covariates alone. [The asserted mathematical result follows](goal). -/
-- @node: published_assignment_condIndep
lemma published_assignment_condIndep {n d : ℕ} (P : OutcomeLaw d) (π : Design n d) :
    letI := publishedExperiment_probability P π
    CondIndepFun (MeasurableSpace.comap
      (fun ω : (Fin n → Cube d × ℝ × ℝ) × Signs n => sampleCovariates ω.1)
      inferInstance) (publishedCovariates_measurable n d).comap_le
      (fun ω => ω.2) (fun ω i => (ω.1 i).2) (publishedExperiment P π) := by
  letI : IsMarkovKernel π.val := π.property
  letI := publishedExperiment_probability P π
  let ν := Measure.pi (fun _ : Fin n => P.toMeasure)
  let f := sampleCovariates (n := n) (d := d)
  have hf : Measurable f := by unfold f sampleCovariates; fun_prop
  let E := publishedExperiment P π
  have hbase : E.map (fun ω => f ω.1) = ν.map f := by
    rw [show (fun ω : (Fin n → Cube d × ℝ × ℝ) × Signs n => f ω.1) =
      f ∘ Prod.fst from rfl, ← Measure.map_map hf measurable_fst]
    congr 1
    exact Measure.fst_compProd ν (π.val.comap f hf)
  have hsmall : condDistrib Prod.snd (fun ω => f ω.1) E =ᵐ[ν.map f] π.val := by
    have h := condDistrib_ae_eq_of_measure_eq_compProd
      (μ := E) (fun ω => f ω.1) (Y := Prod.snd) (by fun_prop)
      (κ := π.val) (by rw [hbase]; exact assignment_joint_map ν f hf π.val)
    rwa [hbase] at h
  let g := fun xs : Fin n → Cube d × ℝ × ℝ => (f xs, xs)
  have hg : Measurable g := hf.prodMk measurable_id
  have haug : E.map (fun ω => (f ω.1, ω.1)) = ν.map g := by
    rw [show (fun ω : (Fin n → Cube d × ℝ × ℝ) × Signs n => (f ω.1, ω.1)) =
      g ∘ Prod.fst from rfl, ← Measure.map_map hg measurable_fst]
    congr 1
    exact Measure.fst_compProd ν (π.val.comap f hf)
  have hfull : condDistrib Prod.snd (fun ω => (f ω.1, ω.1)) E =ᵐ[ν.map g]
      π.val.prodMkRight (Fin n → Cube d × ℝ × ℝ) := by
    have h := condDistrib_ae_eq_of_measure_eq_compProd
      (μ := E) (fun ω => (f ω.1, ω.1)) (Y := Prod.snd) (by fun_prop)
      (κ := π.val.prodMkRight (Fin n → Cube d × ℝ × ℝ)) (by
        rw [haug]
        exact assignment_joint_map ν g hg
          (π.val.prodMkRight (Fin n → Cube d × ℝ × ℝ)))
    rwa [haug] at h
  have hsmall' : ∀ᵐ xy ∂ν.map g,
      condDistrib Prod.snd (fun ω => f ω.1) E xy.1 = π.val xy.1 := by
    apply ae_of_ae_map (f := Prod.fst) (μ := ν.map g)
      (p := fun x => condDistrib Prod.snd (fun ω => f ω.1) E x = π.val x)
      measurable_fst.aemeasurable
    rw [Measure.map_map measurable_fst hg]
    exact hsmall
  have hci : CondIndepFun (MeasurableSpace.comap
      (fun ω : (Fin n → Cube d × ℝ × ℝ) × Signs n => f ω.1) inferInstance)
      (hf.comp measurable_fst).comap_le Prod.fst Prod.snd E := by
    rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
      (μ := E) (f := Prod.snd) (g := Prod.fst) (k := fun ω => f ω.1)
      measurable_snd measurable_fst (by fun_prop), haug]
    filter_upwards [hfull, hsmall'] with xy hxy hx
    simpa [Kernel.prodMkRight, Kernel.comap_apply, hx] using hxy
  exact hci.symm.comp measurable_id
    (show Measurable (fun xs : Fin n → Cube d × ℝ × ℝ => fun i => (xs i).2) by
      fun_prop)

/-- [ Published and research admissibility are the same fairness condition on the same
covariate-only Borel kernel; conditional outcome independence follows from its input.](goal) -/
-- @node: published_admissible_iff_designClass
lemma published_admissible_iff_designClass {n d : ℕ} (π : Design n d) :
    PublishedAdmissible π ↔ DesignClass n d π := by
  constructor
  · intro h
    exact ⟨h.1, outcomeIndependent_of_covariate_kernel π⟩
  · intro h
    refine ⟨h.fair, ?_⟩
    intro P _ _
    exact published_assignment_condIndep P π

/-- The cited pointwise carrier transfers to every publicly admissible a.e. fair kernel.
Bounded positive densities share the cube's null sets, so representative replacement
preserves the iid experiment and both sides of the excess identity. Under [the stated conditions](hyp:hExcess_of_gate,hn,hd,hdensity,hmom,hfair,hindep), [the asserted mathematical result follows](goal). -/
-- @node: published_excess_of_ae_fair
lemma published_excess_of_ae_fair
    (hExcess_of_gate : PublishedHTExcessIdentity)
    (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (P : OutcomeLaw d)
    (hdensity : BoundedPositiveCovDensity P) (hmom : FiniteOutcomeMoments P)
    (π : Design n d) (hfair : FairKernel π.val)
    (hindep : OutcomeIndependentKernel π.val) :
    publishedExcessReal π P = (4 / (n : ℝ)) *
      ∫ ω, (∑ i, sgn (ω.2 i) * prognosisOf P ((ω.1 i).1)) ^ 2
        ∂publishedExperiment P π := by
  obtain ⟨ρ, hρfair, hρeq⟩ := pointwiseFairRepresentative π hfair
  have hρindep : OutcomeIndependentKernel ρ.val :=
    outcomeIndependent_of_covariate_kernel ρ
  have hac : covMarginal P ≪ cubeMeasure d := by
    obtain ⟨lower, upper, _, _, f, _, hf, _⟩ := hdensity
    rw [hf]
    exact withDensity_absolutelyContinuous _ _
  have hexperiment := publishedExperiment_eq_of_ae_kernel P hac π ρ hρeq.symm
  have hexcess : publishedExcessReal π P = publishedExcessReal ρ P := by
    unfold publishedExcessReal
    rw [hexperiment]
  have himbalance :
      (∫ ω, (∑ i, sgn (ω.2 i) * prognosisOf P ((ω.1 i).1)) ^ 2
        ∂publishedExperiment P ρ) =
      (∫ ω, (∑ i, sgn (ω.2 i) * prognosisOf P ((ω.1 i).1)) ^ 2
        ∂publishedExperiment P π) := by
    rw [hexperiment]
  rw [hexcess, hExcess_of_gate n d hn hd P hdensity hmom ρ hρfair hρindep, himbalance]

/-- [ Nonnegative carrier of the actual law-specific excess, not a surrogate imbalance risk. -/
def excess {n d : ℕ} (π : Design n d) (P : OutcomeLaw d) : ℝ≥0∞ :=
  ENNReal.ofReal (publishedExcessReal π P)
/-- Fixed-law worst excess, outside the experiment expectation. -/
def publishedWorst {n d : ℕ} (π : Design n d) (C : Set (OutcomeLaw d)) : ℝ≥0∞ :=
  ⨆ P : C, excess π P.val
/-- Minimax actual excess over a specified class of iid laws. -/
def publishedCapacity (n d : ℕ) (C : Set (OutcomeLaw d)) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (π : {π : Design n d // DesignClass n d π}) (P : C) => excess π.val P.val)
/-- A fixed cube-null change of prognosis leaves every finite-sample design loss unchanged.](goal) Under [the stated conditions](hyp:hfg). This uses [the stated conclusion](goal). -/
-- @node: loss_congr_cube_ae
lemma loss_congr_cube_ae {n d : ℕ} (π : Design n d) {f g : Cube d → ℝ}
    (hfg : f =ᵐ[cubeMeasure d] g) : loss π f = loss π g := by
  letI := cubeMeasure_probability d
  have hi (i : Fin n) : ∀ᵐ x ∂covLaw n d, f (x i) = g (x i) := by
    exact (measurePreserving_eval (fun _ : Fin n => cubeMeasure d) i).quasiMeasurePreserving.ae hfg
  have hall : ∀ᵐ x ∂covLaw n d, ∀ i, f (x i) = g (x i) :=
    ae_all_iff.mpr hi
  unfold loss
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hall] with x hx
  congr 1
  funext z
  simp only [hx]

/-- [ Uniform outcome laws induce exactly the original covariate/sign experiment.](goal) Under [the stated conditions](hyp:hU). -/
-- @node: published_covariate_sign_map
lemma published_covariate_sign_map {n d : ℕ} (P : OutcomeLaw d)
    (hU : covMarginal P = cubeMeasure d) (π : Design n d) :
    (publishedExperiment P π).map
      (fun ω => (sampleCovariates ω.1, ω.2)) = covLaw n d ⊗ₘ π.val := by
  letI : IsMarkovKernel π.val := π.property
  have hf : Measurable (sampleCovariates (n := n) (d := d)) := by
    unfold sampleCovariates
    fun_prop
  have hmap : (Measure.pi (fun _ : Fin n => P.toMeasure)).map sampleCovariates =
      covLaw n d := by
    change (Measure.pi (fun _ : Fin n => P.toMeasure)).map
      (fun xs i => (xs i).1) = covLaw n d
    rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
    change (Measure.pi (fun _ : Fin n => covMarginal P)) = covLaw n d
    rw [hU]
    rfl
  calc
    _ = (Measure.pi (fun _ : Fin n => P.toMeasure)).map sampleCovariates ⊗ₘ π.val :=
      assignment_joint_map _ sampleCovariates hf π.val
    _ = _ := by rw [hmap]

/-- Every Markov sign law preserves integrability of the squared finite imbalance. [The asserted mathematical result follows](goal). -/
-- @node: imbalance_square_integrable
lemma imbalance_square_integrable {n d : ℕ} (π : Design n d) (m : CenteredL2Fn d) :
    Integrable (fun ω : Covariates n d × Signs n =>
      (∑ i, sgn (ω.2 i) * m.val (ω.1 i)) ^ 2) (covLaw n d ⊗ₘ π.val) := by
  letI : IsMarkovKernel π.val := π.property
  letI := cubeMeasure_probability d
  letI : IsProbabilityMeasure (covLaw n d) := by unfold covLaw; infer_instance
  have hm : Measurable m.val := m.property.1
  have hi (i : Fin n) : Integrable (fun x : Covariates n d => m.val (x i) ^ 2)
      (covLaw n d) :=
    (m.property.2.1.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => cubeMeasure d) i)).integrable_sq
  have hb : Integrable (fun x : Covariates n d =>
      (n : ℝ) * ∑ i, m.val (x i) ^ 2) (covLaw n d) :=
    (integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul _
  have hfst : MeasurePreserving Prod.fst (covLaw n d ⊗ₘ π.val) (covLaw n d) :=
    ⟨measurable_fst, Measure.fst_compProd _ _⟩
  apply (hfst.integrable_comp_of_integrable hb).mono'
  · exact (by fun_prop : Measurable (fun ω : Covariates n d × Signs n =>
      (∑ i, sgn (ω.2 i) * m.val (ω.1 i)) ^ 2)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact signed_sum_sq_le ω.2 _)

/-- [ The finite imbalance loss is the nonnegative real joint second moment.](goal) -/
-- @node: loss_eq_ofReal_joint_integral
lemma loss_eq_ofReal_joint_integral {n d : ℕ} (π : Design n d) (m : CenteredL2Fn d) :
    loss π m.val = ENNReal.ofReal ((4 / (n : ℝ)) *
      ∫ ω : Covariates n d × Signs n,
        (∑ i, sgn (ω.2 i) * m.val (ω.1 i)) ^ 2 ∂(covLaw n d ⊗ₘ π.val)) := by
  letI : IsMarkovKernel π.val := π.property
  letI := cubeMeasure_probability d
  letI : IsProbabilityMeasure (covLaw n d) := by unfold covLaw; infer_instance
  have hm : Measurable m.val := m.property.1
  rw [ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal (imbalance_square_integrable π m)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  unfold loss
  rw [Measure.lintegral_compProd (by fun_prop)]

/-- The cited excess identity transfers to the original-sample loss for every uniform
law with square-integrable Sobolev prognosis; null representatives cause no change. Under [the stated conditions](hyp:hExcess,hn,hd,hπ,hP), [the asserted mathematical result follows](goal). -/
-- @node: published_uniform_excess_eq_loss
lemma published_uniform_excess_eq_loss (hExcess : PublishedHTExcessIdentity)
    {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d) {s : ℝ} (π : Design n d)
    (hπ : DesignClass n d π) (P : OutcomeLaw d) (hP : P ∈ frozenUniformClass d s) :
    0 ≤ publishedExcessReal π P ∧ excess π P = loss π (prognosisOf P) := by
  letI := cubeMeasure_probability d
  letI : IsMarkovKernel π.val := π.property
  letI : IsProbabilityMeasure (covLaw n d) := by unfold covLaw; infer_instance
  obtain ⟨hU, hmom, m, hm, hae⟩ := hP
  have hjoint : Measurable (fun ω : (Fin n → Cube d × ℝ × ℝ) × Signs n =>
      (sampleCovariates ω.1, ω.2)) :=
    (publishedCovariates_measurable n d).prodMk measurable_snd
  have hdensity : BoundedPositiveCovDensity P := by
    refine ⟨1, 1, by norm_num, le_rfl, fun _ => 1, by fun_prop, ?_, ?_⟩
    · simpa using hU
    · exact Filter.Eventually.of_forall (fun _ => ⟨le_rfl, le_rfl⟩)
  have hmap := published_covariate_sign_map P hU π
  have hsample : (publishedExperiment P π).map
      (fun ω => sampleCovariates ω.1) = covLaw n d := by
    rw [show (fun ω : (Fin n → Cube d × ℝ × ℝ) × Signs n =>
        sampleCovariates ω.1) = Prod.fst ∘
          (fun ω => (sampleCovariates ω.1, ω.2)) from rfl,
      ← Measure.map_map measurable_fst hjoint, hmap]
    exact Measure.fst_compProd _ _
  have hall : ∀ᵐ ω ∂publishedExperiment P π,
      ∀ i, prognosisOf P ((ω.1 i).1) = m.val ((ω.1 i).1) := by
    have hi (i : Fin n) : ∀ᵐ x ∂covLaw n d,
        prognosisOf P (x i) = m.val (x i) :=
      (measurePreserving_eval (fun _ : Fin n => cubeMeasure d) i).quasiMeasurePreserving.ae hae
    apply ae_of_ae_map (p := fun x => ∀ i, prognosisOf P (x i) = m.val (x i))
      (publishedCovariates_measurable n d).aemeasurable
    rw [hsample]
    exact ae_all_iff.mpr hi
  have hmean : (∫ ω, (∑ i, sgn (ω.2 i) * prognosisOf P ((ω.1 i).1)) ^ 2
      ∂publishedExperiment P π) =
      ∫ ω : Covariates n d × Signs n,
        (∑ i, sgn (ω.2 i) * m.val (ω.1 i)) ^ 2 ∂(covLaw n d ⊗ₘ π.val) := by
    have hmeas : Measurable m.val := m.property.1
    calc
      _ = ∫ ω, (∑ i, sgn (ω.2 i) * m.val ((ω.1 i).1)) ^ 2
          ∂publishedExperiment P π := by
        apply integral_congr_ae
        filter_upwards [hall] with ω hω
        simp only [hω]
      _ = _ := by
        rw [← hmap, integral_map hjoint.aemeasurable
          (by rw [hmap]; exact (imbalance_square_integrable π m).aestronglyMeasurable)]
        rfl
  have heq := published_excess_of_ae_fair hExcess n d hn hd P hdensity hmom π hπ.1 hπ.2
  rw [hmean] at heq
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))
  · rw [excess, heq, loss_congr_cube_ae π hae, loss_eq_ofReal_joint_integral]

/-- [ Equality of prognostic images modulo null sets and the pointwise excess identity
identify the fixed-design suprema, without moving a supremum inside an expectation.](goal) Under [the stated conditions](hyp:himage,hexcess). -/
-- @node: publishedWorst_eq_of_image_and_excess
lemma publishedWorst_eq_of_image_and_excess {n d : ℕ} {s : ℝ} (π : Design n d)
    (himage : publishedPrognosticImage d s = sobolevImage d s)
    (hexcess : ∀ P ∈ frozenUniformClass d s, excess π P = loss π (prognosisOf P)) :
    publishedWorst π (frozenUniformClass d s) = worstLoss π s := by
  apply le_antisymm
  · apply iSup_le
    intro P
    obtain ⟨m, hm, heq⟩ := P.property.2.2
    rw [hexcess P.val P.property, loss_congr_cube_ae π heq]
    exact le_iSup_of_le ⟨m, hm⟩ le_rfl
  · apply iSup_le
    intro m
    have hmem : m.val.val ∈ sobolevImage d s := ⟨m.val, m.property, Filter.EventuallyEq.rfl⟩
    rw [← himage] at hmem
    obtain ⟨P, hP, heq⟩ := hmem
    calc
      loss π m.val.val = loss π (prognosisOf P) := loss_congr_cube_ae π heq
      _ = excess π P := (hexcess P hP).symm
      _ ≤ publishedWorst π (frozenUniformClass d s) := le_iSup_of_le ⟨P, hP⟩ le_rfl

/-- [ Equal worst risks for every admissible original-sample design give equal capacities
by taking the infimum over the common design class.](goal) Under [the stated conditions](hyp:hworst). -/
-- @node: publishedCapacity_eq_of_worst
lemma publishedCapacity_eq_of_worst {n d : ℕ} {s : ℝ}
    (hworst : ∀ π : Design n d, DesignClass n d π →
      publishedWorst π (frozenUniformClass d s) = worstLoss π s) :
    publishedCapacity n d (frozenUniformClass d s) = capacity n d s := by
  unfold publishedCapacity capacity Causalean.Stat.minimaxValueENNReal
  apply iInf_congr
  intro π
  exact hworst π.val π.property

/-- [ Enlarging the law class increases its fixed-design supremum and minimax capacity.](goal) Under [the stated conditions](hyp:hCD). -/
-- @node: publishedCapacity_mono_class
lemma publishedCapacity_mono_class {n d : ℕ} {C D : Set (OutcomeLaw d)}
    (hCD : C ⊆ D) : publishedCapacity n d C ≤ publishedCapacity n d D := by
  unfold publishedCapacity Causalean.Stat.minimaxValueENNReal
  apply iInf_mono
  intro π
  apply iSup_le
  intro P
  exact le_iSup_of_le ⟨P.val, hCD P.property⟩ le_rfl

/-- [ A uniform law meets all permitted fixed density bounds.](goal) Under [the stated conditions](hyp:hU,hl,hl1,hu1). -/
-- @node: uniform_covDensityBounds
lemma uniform_covDensityBounds {d : ℕ} (P : OutcomeLaw d)
    (hU : covMarginal P = cubeMeasure d) {lower upper : ℝ}
    (hl : 0 < lower) (hl1 : lower ≤ 1) (hu1 : 1 ≤ upper) :
    CovDensityBounds P lower upper := by
  refine ⟨hl, hl1.trans hu1, fun _ => 1, by fun_prop, ?_, ?_⟩
  · simpa using hU
  · exact Filter.Eventually.of_forall (fun _ => ⟨hl1, hu1⟩)

-- @node: lem:published-prognostic-capacity
/-- The frozen published class has exactly the legal prognostic image and full-design
capacity; the bounded-density class inherits the all-design converse and vanishing necessity. This uses [the hExcess_of_gate hypothesis](hyp:hExcess_of_gate), [the hContraction_of_gate hypothesis](hyp:hContraction_of_gate), [the stated conclusion](goal). -/
lemma published_prognostic_capacity
    (hExcess_of_gate : PublishedHTExcessIdentity)
    (hContraction_of_gate : ClassicalRademacherContraction) :
    (∀ (d : ℕ) (hd : 2 ≤ d) (s : ℝ), 0 < s → s ≤ 1 →
      publishedPrognosticImage d s = sobolevImage d s ∧
      gaussianLawClass d (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) s ⊂ frozenUniformClass d s ∧
      twoPointOutcomeLaw d ∈ frozenUniformClass d s ∧
      twoPointOutcomeLaw d ∉ gaussianLawClass d (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) s) ∧
    (∀ n d : ℕ, 2 ≤ n → 2 ≤ d → ∀ π : Design n d,
      PublishedAdmissible π ↔ DesignClass n d π) ∧
    (∀ n d : ℕ, 2 ≤ n → 2 ≤ d → ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∀ π : Design n d, DesignClass n d π →
      (∀ P ∈ frozenUniformClass d s,
        0 ≤ publishedExcessReal π P ∧ excess π P = loss π (prognosisOf P)) ∧
      publishedWorst π (frozenUniformClass d s) = worstLoss π s) ∧
    (∀ n d : ℕ, 2 ≤ n → 2 ≤ d → ∀ s : ℝ, 0 < s → s ≤ 1 →
      publishedCapacity n d (frozenUniformClass d s) = capacity n d s) ∧
    (∀ (s lower upper : ℝ), 0 < s → s ≤ 1 → 0 < lower → lower ≤ 1 → 1 ≤ upper →
      (0 < cLower 1 ∧ cLower 1 ≤ cLower s) ∧
      (∀ n d : ℕ, 2 ≤ n → 2 ≤ d →
        ENNReal.ofReal (cLower s * bScale n d s) ≤ capacity n d s ∧
        capacity n d s ≤ publishedCapacity n d (boundedDensityClass d s lower upper)) ∧
      (∀ ds : ℕ → ℕ, (∀ n, 2 ≤ ds n) →
        Tendsto (fun n => publishedCapacity n (ds n)
          (boundedDensityClass (ds n) s lower upper)) atTop (𝓝 0) →
        Asymptotics.IsLittleO atTop (fun n => (ds n : ℝ)) (fun n => Real.sqrt (n : ℝ)))) :=
  by
    have himage : ∀ (d : ℕ) (hd : 2 ≤ d) (s : ℝ), 0 < s → s ≤ 1 →
        publishedPrognosticImage d s = sobolevImage d s ∧
        gaussianLawClass d (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) s ⊂ frozenUniformClass d s ∧
        twoPointOutcomeLaw d ∈ frozenUniformClass d s ∧
        twoPointOutcomeLaw d ∉ gaussianLawClass d
          (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) s := by
      intro d hd s hs hs1
      have hd0 : 0 < d := lt_of_lt_of_le (Nat.zero_lt_succ 1) hd
      exact ⟨publishedPrognosticImage_eq_sobolevImage d hd0 s,
        gaussianLawClass_ssubset_frozenUniformClass hd0 s,
        twoPointOutcomeLaw_mem_frozenUniformClass d s,
        twoPointOutcomeLaw_not_mem_gaussianLawClass hd0 s⟩
    have htransfer : ∀ n d : ℕ, 2 ≤ n → 2 ≤ d → ∀ s : ℝ, 0 < s → s ≤ 1 →
        ∀ π : Design n d, DesignClass n d π →
        (∀ P ∈ frozenUniformClass d s,
          0 ≤ publishedExcessReal π P ∧ excess π P = loss π (prognosisOf P)) ∧
        publishedWorst π (frozenUniformClass d s) = worstLoss π s := by
      intro n d hn hd s hs hs1 π hπ
      have hpointwise : ∀ P ∈ frozenUniformClass d s,
          0 ≤ publishedExcessReal π P ∧ excess π P = loss π (prognosisOf P) := by
        intro P hP
        exact published_uniform_excess_eq_loss hExcess_of_gate hn hd π hπ P hP
      exact ⟨hpointwise, publishedWorst_eq_of_image_and_excess π
        (himage d hd s hs hs1).1 (fun P hP => (hpointwise P hP).2)⟩
    refine ⟨himage, ?_, htransfer, ?_, ?_⟩
    · intro n d hn hd π
      exact published_admissible_iff_designClass π
    · intro n d hn hd s hs hs1
      exact publishedCapacity_eq_of_worst (fun π hπ =>
        (htransfer n d hn hd s hs hs1 π hπ).2)
    · intro s lower upper hs hs1 hl hl1 hu1
      have hsub : ∀ d : ℕ, 2 ≤ d →
          frozenUniformClass d s ⊆ boundedDensityClass d s lower upper := by
        intro d hd P hP
        obtain ⟨hU, hmom, m, hm, heq⟩ := hP
        refine ⟨uniform_covDensityBounds P hU hl hl1 hu1, hmom, ?_,
          0, m, hm, ?_⟩
        · rw [hU]
          have heq_sq : (fun u => prognosisOf P u ^ 2) =ᵐ[cubeMeasure d]
              (fun u => m.val u ^ 2) := heq.fun_comp (fun x => x ^ 2)
          rw [integral_congr_ae heq_sq]
          exact sobolev_cube_second_moment_le_one hd hs hs1 m hm
        · simpa only [zero_add] using heq
      have hcapacity : ∀ n d : ℕ, 2 ≤ n → 2 ≤ d →
          capacity n d s ≤ publishedCapacity n d (boundedDensityClass d s lower upper) := by
        intro n d hn hd
        rw [← publishedCapacity_eq_of_worst (fun π hπ =>
          (htransfer n d hn hd s hs hs1 π hπ).2)]
        exact publishedCapacity_mono_class (hsub d hd)
      have hbound : ∀ n d : ℕ, 2 ≤ n → 2 ≤ d →
          ENNReal.ofReal (cLower s * bScale n d s) ≤ capacity n d s := by
        intro n d hn hd
        exact ((full_design_lower hContraction_of_gate s hs hs1).2 n d hn hd).2
      refine ⟨cLower_uniform_positive s hs1, ?_, ?_⟩
      · intro n d hn hd
        exact ⟨hbound n d hn hd, hcapacity n d hn hd⟩
      · intro ds hd hvanish
        apply dimension_necessity_of_scale_lower s hs hs1 ds hd
          (fun n => publishedCapacity n (ds n) (boundedDensityClass (ds n) s lower upper))
          _ hvanish
        filter_upwards [eventually_ge_atTop 2] with n hn
        exact (hbound n (ds n) hn (hd n)).trans (hcapacity n (ds n) hn (hd n))

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
