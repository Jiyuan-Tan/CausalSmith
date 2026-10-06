module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.TAdaptiveMinimax
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.TStrictEnlargement
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Measurability
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.HolderCompletion
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.DornScope
public import Causalean.Mathlib.Probability.Independence.Conditional.Transport
public import Causalean.Mathlib.Probability.Independence.Conditional.Transport.AeRetraction
public import Causalean.Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Assumption-3-free upper bound on Dorn's remaining Gaussian model -/
@[expose] public section
set_option linter.style.haveILetI false
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Coordinatewise affine transformation from `[-1,1]^d` to `[0,1]^d`. For [the stated inputs and conditions](hyp:x), [the `affineToCube` object being defined](goal). -/
noncomputable def affineToCube {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (x i + 1) / 2

/-- Push an observed law from Dorn's cube to the unit cube. For [the stated inputs and conditions](hyp:P), [the `transformedDornLaw` object being defined](goal). -/
noncomputable def transformedDornLaw {d : ℕ} (P : Measure (Obs d)) : Measure (Obs d) :=
  P.map (fun z => (affineToCube z.1, z.2.1, z.2.2))

/-- Corresponding transformed treated-response curve. For [the stated inputs and conditions](hyp:μ), [the `transformedResponse` object being defined](goal). -/
def transformedResponse {d : ℕ} (μ : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun x => μ (fun i => 2 * x i - 1)

/-- The coordinate change used to transport Dorn's source cube is measurable. [For the stated inputs and conditions](hyp:d), [the asserted conclusion holds](goal). -/
lemma affineToCube_measurable {d : ℕ} :
    Measurable (@affineToCube d) := by
  unfold affineToCube
  fun_prop

/-- The displayed inverse coordinate change cancels `affineToCube` globally. [For the stated inputs and conditions](hyp:d,x), [the asserted conclusion holds](goal). -/
lemma affineToCube_inverse {d : ℕ} (x : Fin d → ℝ) :
    (fun i => 2 * affineToCube x i - 1) = x := by
  funext i
  simp [affineToCube]
  ring

/-- The inverse coordinate change from the unit cube to Dorn's cube is
measurable on the whole ambient space. [For the stated inputs and conditions](hyp:d), [the asserted conclusion holds](goal). -/
lemma affineFromCube_measurable {d : ℕ} :
    Measurable (fun x : Fin d → ℝ => fun i => 2 * x i - 1) := by
  fun_prop

/-- The inverse coordinate change is also a right inverse of `affineToCube`. [For the stated inputs and conditions](hyp:d,x), [the asserted conclusion holds](goal). -/
lemma affineToCube_affineFromCube {d : ℕ} (x : Fin d → ℝ) :
    affineToCube (fun i => 2 * x i - 1) = x := by
  funext i
  simp [affineToCube]

/-- An invertible measurable affine change of covariates generates exactly the
same conditioning sigma algebra. [For the stated inputs and conditions](hyp:d,Omega,X), [the asserted conclusion holds](goal). -/
lemma affineToCube_comap_eq {d : ℕ} {Omega : Type*}
    (X : Omega → (Fin d → ℝ)) :
    MeasurableSpace.comap (affineToCube ∘ X) inferInstance =
      MeasurableSpace.comap X inferInstance := by
  apply le_antisymm
  · exact MeasurableSpace.comap_le_comap_of_eq_comp affineToCube
      affineToCube_measurable rfl
  · apply MeasurableSpace.comap_le_comap_of_eq_comp
      (fun x : Fin d → ℝ => fun i => 2 * x i - 1)
      affineFromCube_measurable
    funext omega
    exact (affineToCube_inverse (X omega)).symm

/-- The global affine coordinate change as a measurable equivalence. For [the stated inputs and conditions](hyp:d), [the `affineToCubeMeasurableEquiv` object being defined](goal). -/
noncomputable def affineToCubeMeasurableEquiv (d : ℕ) :
    (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) where
  toFun := affineToCube
  invFun := fun x i => 2 * x i - 1
  left_inv := affineToCube_inverse
  right_inv := affineToCube_affineFromCube
  measurable_toFun := affineToCube_measurable
  measurable_invFun := affineFromCube_measurable

/-- Conditional independence is insensitive to replacing the conditioning
measurable space by an equal one. [For the stated inputs and conditions](hyp:Omega,B,C,mOmega,m₁,m₂,hm,h₁,h₂,f,g,mu,h), [the asserted conclusion holds](goal). -/
lemma condIndepFun_congr_conditioning
    {Omega B C : Type*} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega] [MeasurableSpace B] [MeasurableSpace C]
    {m₁ m₂ : MeasurableSpace Omega} (hm : m₁ = m₂)
    (h₁ : m₁ ≤ mOmega) (h₂ : m₂ ≤ mOmega)
    (f : Omega → B) (g : Omega → C)
    (mu : @Measure Omega mOmega := by volume_tac)
    [IsFiniteMeasure mu]
    (h : ProbabilityTheory.CondIndepFun m₁ h₁ f g (μ := mu)) :
    ProbabilityTheory.CondIndepFun m₂ h₂ f g (μ := mu) := by
  subst m₂
  exact h

/-- Conditional expectation is unchanged when its conditioning measurable
space is replaced by an equal one. [For the stated inputs and conditions](hyp:Omega,E,mOmega,m₁,m₂,hm,mu,f), [the asserted conclusion holds](goal). -/
lemma condExp_congr_conditioning
    {Omega E : Type*} [mOmega : MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m₁ m₂ : MeasurableSpace Omega} (hm : m₁ = m₂)
    (mu : @Measure Omega mOmega) (f : Omega → E) :
    @condExp Omega E m₁ mOmega _ _ mu f =ᵐ[mu]
      @condExp Omega E m₂ mOmega _ _ mu f := by
  subst m₂
  rfl

/-- Pulling a response to the unit cube and evaluating at the transported
point recovers the original response exactly. [For the stated inputs and conditions](hyp:d,μ,x), [the asserted conclusion holds](goal). -/
lemma transformedResponse_affineToCube {d : ℕ}
    (μ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    transformedResponse μ (affineToCube x) = μ x := by
  simp only [transformedResponse, affineToCube_inverse]

/-- The affine coordinate change identifies Dorn's source cube with the unit
cube used by the causal model. [For the stated inputs and conditions](hyp:d,x), [the asserted conclusion holds](goal). -/
lemma affineToCube_mem_cube_iff {d : ℕ} (x : Fin d → ℝ) :
    affineToCube x ∈ cube d ↔ x ∈ dornCube d := by
  unfold cube dornCube affineToCube
  constructor
  · intro hx i hi
    have hxi := hx i hi
    constructor <;> linarith [hxi.1, hxi.2]
  · intro hx i hi
    have hxi := hx i hi
    constructor <;> linarith [hxi.1, hxi.2]

/-- The covariate marginal of the transported observed law is the pushforward
of the original marginal by the affine coordinate change. [For the stated inputs and conditions](hyp:d,P), [the asserted conclusion holds](goal). -/
lemma transformedDornLaw_covariateLaw {d : ℕ} (P : Measure (Obs d)) :
    covariateLaw (transformedDornLaw P) =
      (covariateLaw P).map affineToCube := by
  have htransport : Measurable
      (fun z : Obs d => (affineToCube z.1, z.2.1, z.2.2)) := by
    unfold affineToCube
    fun_prop
  unfold transformedDornLaw covariateLaw
  rw [Measure.map_map (by fun_prop) htransport]
  rw [Measure.map_map affineToCube_measurable (by fun_prop)]
  rfl

/-- The coordinatewise affine map has Jacobian factor `2⁻ᵈ` and hence its
pushforward multiplies ambient volume by `2ᵈ`. [For the stated inputs and conditions](hyp:d), [the asserted conclusion holds](goal). -/
lemma affineToCube_map_volume (d : ℕ) :
    (volume : Measure (Fin d → ℝ)).map affineToCube =
      ENNReal.ofReal ((2 : ℝ) ^ d) • volume := by
  let f : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    (2 : ℝ)⁻¹ • LinearMap.id
  have hdet : LinearMap.det f ≠ 0 := by
    simp [f, LinearMap.det_smul, LinearMap.det_id]
  have hlin := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  have hfactor : ENNReal.ofReal |(LinearMap.det f)⁻¹| =
      ENNReal.ofReal ((2 : ℝ) ^ d) := by
    congr 1
    simp [f, LinearMap.det_smul, LinearMap.det_id, abs_of_nonneg]
  have hlin' : (volume : Measure (Fin d → ℝ)).map f =
      ENNReal.ofReal ((2 : ℝ) ^ d) • volume := by
    rw [hfactor] at hlin
    exact hlin
  let b : Fin d → ℝ := fun _ => 2⁻¹
  calc
    (volume : Measure (Fin d → ℝ)).map affineToCube =
        ((volume : Measure (Fin d → ℝ)).map f).map (fun x => x + b) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x i
      simp [affineToCube, f, b]
      ring
    _ = (ENNReal.ofReal ((2 : ℝ) ^ d) • volume).map (fun x => x + b) := by
      rw [hlin']
    _ = ENNReal.ofReal ((2 : ℝ) ^ d) • volume := by
      rw [Measure.map_smul, map_add_right_eq_self]

/-- Normalized volume on Dorn's cube pushes forward exactly to unit-cube
volume under the coordinatewise affine map. [For the stated inputs and conditions](hyp:d), [the asserted conclusion holds](goal). -/
lemma normalizedDornVolume_map_affineToCube (d : ℕ) :
    (((ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ •
      volume.restrict (dornCube d)).map affineToCube) =
      volume.restrict (cube d) := by
  have hpre : affineToCube ⁻¹' cube d = dornCube d := by
    ext x
    exact affineToCube_mem_cube_iff x
  have hcube : MeasurableSet (cube d) := by
    unfold cube
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hrestricted : (volume.restrict (dornCube d)).map affineToCube =
      ENNReal.ofReal ((2 : ℝ) ^ d) • volume.restrict (cube d) := by
    rw [← hpre, ← Measure.restrict_map affineToCube_measurable hcube,
      affineToCube_map_volume, Measure.restrict_smul]
  rw [Measure.map_smul, hrestricted, smul_smul]
  rw [ENNReal.inv_mul_cancel]
  · simp
  · positivity
  · simp

/-- A Dorn law with normalized uniform covariates transports to exact uniform
volume on the unit cube. [For the stated inputs and conditions](hyp:d,P,hcov), [the asserted conclusion holds](goal). -/
lemma transformedDornLaw_covariate_eq_cubeVolume {d : ℕ}
    (P : Measure (Obs d))
    (hcov : covariateLaw P =
      (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ • volume.restrict (dornCube d)) :
    covariateLaw (transformedDornLaw P) = volume.restrict (cube d) := by
  rw [transformedDornLaw_covariateLaw, hcov]
  exact normalizedDornVolume_map_affineToCube d

/-- Exact transported uniform covariates supply cube support, absolute
continuity, and density lower bound one. [For the stated inputs and conditions](hyp:d,P,hcov), [the asserted conclusion holds](goal). -/
lemma transformedDornLaw_cube_fields {d : ℕ}
    (P : Measure (Obs d))
    (hcov : covariateLaw P =
      (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ • volume.restrict (dornCube d)) :
    covariateLaw (transformedDornLaw P) (cube d) = 1 ∧
      covariateLaw (transformedDornLaw P) ≪ volume.restrict (cube d) ∧
      CovariateDensityLowerBound (transformedDornLaw P) 1 := by
  have htarget := transformedDornLaw_covariate_eq_cubeVolume P hcov
  constructor
  · rw [htarget, Measure.restrict_apply
        (by simp [cube] : MeasurableSet (cube d)), Set.inter_self]
    have hcube : cube d =
        Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  constructor
  · rw [htarget]
  · unfold CovariateDensityLowerBound covariateDensity
    rw [htarget]
    filter_upwards [Measure.rnDeriv_self (volume.restrict (cube d))] with x hx
    simp [hx]

/-- Affine transport reindexes the conditional treatment kernel by the
covariate equivalence. [For the stated inputs and conditions](hyp:d,P), [the asserted conclusion holds](goal). -/
lemma transformedDornLaw_treatmentKernel_ae {d : ℕ}
    (P : Measure (Obs d)) [IsFiniteMeasure P]
    [IsFiniteMeasure (transformedDornLaw P)] :
    ∀ᵐ x ∂covariateLaw P,
      ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
          (fun z => z.1) (transformedDornLaw P) (affineToCube x) =
        ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
          (fun z => z.1) P x := by
  let G : Obs d → Obs d := fun z => (affineToCube z.1, z.2.1, z.2.2)
  have hG : Measurable G := by
    dsimp [G]
    have hx : Measurable (fun z : Obs d => affineToCube z.1) :=
      affineToCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)
  have hmap := ProbabilityTheory.condDistrib_map
    (X := fun z : Obs d => z.1) (Y := fun z : Obs d => z.2.1)
    (f := G) (ν := P) (by fun_prop) (by fun_prop) hG.aemeasurable
  dsimp [G] at hmap
  have hfilter : P.map
      ((fun z : Obs d => z.1) ∘ fun z => (affineToCube z.1, z.2.1, z.2.2)) =
      (covariateLaw P).map affineToCube := by
    calc
      _ = P.map (affineToCube ∘ (fun z : Obs d => z.1)) := by rfl
      _ = (covariateLaw P).map affineToCube := by
        unfold covariateLaw
        exact (Measure.map_map affineToCube_measurable (by fun_prop)).symm
  rw [hfilter] at hmap
  have hmap' := ae_of_ae_map affineToCube_measurable.aemeasurable hmap
  have hreparam :=
    Causalean.Mathlib.Probability.Kernel.condDistrib_comp_right_measurableEquiv
      P (affineToCubeMeasurableEquiv d)
      (Y := fun z : Obs d => z.2.1) (X := fun z : Obs d => z.1)
      (by fun_prop) (by fun_prop)
  filter_upwards [hmap', hreparam] with x hx hr
  unfold transformedDornLaw
  simpa only [Function.comp_apply] using hx.trans hr

/-- Affine transport reindexes both coordinates of the conditional outcome
kernel and leaves its response law unchanged. [For the stated inputs and conditions](hyp:d,P), [the asserted conclusion holds](goal). -/
lemma transformedDornLaw_outcomeKernel_ae {d : ℕ}
    (P : Measure (Obs d)) [IsFiniteMeasure P]
    [IsFiniteMeasure (transformedDornLaw P)] :
    ∀ᵐ xa ∂P.map (fun z : Obs d => (z.1, z.2.1)),
      ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
          (fun z => (z.1, z.2.1)) (transformedDornLaw P)
          (affineToCube xa.1, xa.2) =
        ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
          (fun z => (z.1, z.2.1)) P xa := by
  let G : Obs d → Obs d := fun z => (affineToCube z.1, z.2.1, z.2.2)
  let E : ((Fin d → ℝ) × Bool) ≃ᵐ ((Fin d → ℝ) × Bool) :=
    (affineToCubeMeasurableEquiv d).prodCongr (MeasurableEquiv.refl Bool)
  have hG : Measurable G := by
    dsimp [G]
    have hx : Measurable (fun z : Obs d => affineToCube z.1) :=
      affineToCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)
  have hmap := ProbabilityTheory.condDistrib_map
    (X := fun z : Obs d => (z.1, z.2.1)) (Y := fun z : Obs d => z.2.2)
    (f := G) (ν := P) (by fun_prop) (by fun_prop) hG.aemeasurable
  dsimp [G, E] at hmap
  have hfilter : P.map
      ((fun z : Obs d => (z.1, z.2.1)) ∘
        fun z => (affineToCube z.1, z.2.1, z.2.2)) =
      (P.map (fun z : Obs d => (z.1, z.2.1))).map E := by
    calc
      _ = P.map (E ∘ (fun z : Obs d => (z.1, z.2.1))) := by
        rfl
      _ = (P.map (fun z : Obs d => (z.1, z.2.1))).map E := by
        exact (Measure.map_map E.measurable (by fun_prop)).symm
  rw [hfilter] at hmap
  have hmap' := ae_of_ae_map E.measurable.aemeasurable hmap
  have hreparam :=
    Causalean.Mathlib.Probability.Kernel.condDistrib_comp_right_measurableEquiv
      P E (Y := fun z : Obs d => z.2.2)
      (X := fun z : Obs d => (z.1, z.2.1)) (by fun_prop) (by fun_prop)
  filter_upwards [hmap', hreparam] with xa hx hr
  unfold transformedDornLaw
  have hE : E xa = (affineToCube xa.1, xa.2) := rfl
  rw [hE] at hx
  simpa only [Function.comp_apply] using hx.trans hr

/-- The global propensity tail is invariant under the affine covariate
equivalence when the displayed propensity is pulled back by its inverse. [For the stated inputs and conditions](hyp:d,P,e,C,gamma,he,htail), [the asserted conclusion holds](goal). -/
lemma transformedDornLaw_globalTail {d : ℕ}
    (P : Measure (Obs d)) [IsFiniteMeasure P]
    [IsFiniteMeasure (transformedDornLaw P)]
    (e : (Fin d → ℝ) → ℝ) (C gamma : ℝ)
    (he : Measurable e) (htail : GlobalPropensityTail P e C gamma) :
    GlobalPropensityTail (transformedDornLaw P) (transformedResponse e) C gamma := by
  let r : (Fin d → ℝ) → (Fin d → ℝ) := affineToCube
  let s : (Fin d → ℝ) → (Fin d → ℝ) := fun x i => 2 * x i - 1
  have hr : Measurable r := affineToCube_measurable
  have hs : Measurable s := affineFromCube_measurable
  have hcov : covariateLaw (transformedDornLaw P) =
      (covariateLaw P).map r := transformedDornLaw_covariateLaw P
  have hmapS : (covariateLaw (transformedDornLaw P)).map s =
      covariateLaw P := by
    rw [hcov, Measure.map_map hs hr]
    have hsr : s ∘ r = id := by
      funext x
      exact affineToCube_inverse x
    rw [hsr, Measure.map_id]
  constructor
  · have hk := transformedDornLaw_treatmentKernel_ae P
    have hpull : (fun y => transformedResponse e y) ∘ r =ᵐ[covariateLaw P]
        (fun y => propensity (transformedDornLaw P) y) ∘ r := by
      filter_upwards [htail.1, hk] with x heq hkx
      change transformedResponse e (affineToCube x) =
        propensity (transformedDornLaw P) (affineToCube x)
      rw [transformedResponse_affineToCube]
      rw [heq]
      unfold propensity
      rw [hkx]
    exact Causalean.Mathlib.Probability.Independence.Conditional.Transport.eventuallyEq_of_comp_aeRetraction
      r s hs hmapS (Filter.Eventually.of_forall fun x => by
        change affineToCube (fun i => 2 * x i - 1) = x
        exact affineToCube_affineFromCube x) hpull
  · intro t ht
    rw [hcov]
    have hset : MeasurableSet {x | transformedResponse e x ≤ t} :=
      measurableSet_le (he.comp hs) measurable_const
    rw [Measure.real, Measure.map_apply hr hset]
    have hpre : r ⁻¹' {x | transformedResponse e x ≤ t} = {x | e x ≤ t} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, r,
        transformedResponse_affineToCube]
    rw [hpre]
    exact htail.2 t ht

/-- Every observed law factors into its covariate marginal and the regular
conditional treatment kernel. [For the stated inputs and conditions](hyp:d,P), [the asserted conclusion holds](goal). -/
lemma observedLaw_treatment_compProd {d : ℕ} (P : Measure (Obs d))
    [IsFiniteMeasure P] :
    covariateLaw P ⊗ₘ
        ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
          (fun z => z.1) P =
      P.map (fun z : Obs d => (z.1, z.2.1)) := by
  simpa only [covariateLaw] using
    (ProbabilityTheory.compProd_map_condDistrib
      (μ := P) (X := fun z : Obs d => z.1)
      (Y := fun z : Obs d => z.2.1) (by fun_prop))

/-- Disintegrating an observed law over `(X,A)` and mapping the resulting
product back through tuple reassociation recovers the original law. [For the stated inputs and conditions](hyp:d,P), [the asserted conclusion holds](goal). -/
lemma observedLaw_outcome_recomposition {d : ℕ} (P : Measure (Obs d))
    [IsFiniteMeasure P] :
    ((P.map (fun z : Obs d => (z.1, z.2.1))) ⊗ₘ
        ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
          (fun z => (z.1, z.2.1)) P).map
        (fun z => (z.1.1, z.1.2, z.2)) = P := by
  rw [ProbabilityTheory.compProd_map_condDistrib (by fun_prop)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun :
      (fun z : ((Fin d → ℝ) × Bool) × ℝ => (z.1.1, z.1.2, z.2)) ∘
          (fun z : Obs d => ((z.1, z.2.1), z.2.2)) = id := by
    funext z
    rfl
  rw [hfun, Measure.map_id]

/-- Any almost-everywhere versions of the treatment and response kernels may
be substituted into the two-stage observed-law disintegration. [For the stated inputs and conditions](hyp:d,P,kA,kY,hA,hY), [the asserted conclusion holds](goal). -/
lemma observedLaw_kernel_recomposition {d : ℕ} (P : Measure (Obs d))
    [IsFiniteMeasure P]
    (kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool)
    (kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ)
    [ProbabilityTheory.IsSFiniteKernel kA]
    [ProbabilityTheory.IsSFiniteKernel kY]
    (hA : (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
        (fun z => z.1) P : (Fin d → ℝ) → Measure Bool) =ᵐ[covariateLaw P]
          fun x => kA x)
    (hY : (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
        (fun z => (z.1, z.2.1)) P :
          ((Fin d → ℝ) × Bool) → Measure ℝ) =ᵐ[
            P.map (fun z : Obs d => (z.1, z.2.1))] fun xa => kY xa) :
    (((covariateLaw P ⊗ₘ kA) ⊗ₘ kY).map
      (fun z => (z.1.1, z.1.2, z.2))) = P := by
  have hbase := Measure.compProd_congr hA
  have hbase' : covariateLaw P ⊗ₘ kA =
      P.map (fun z : Obs d => (z.1, z.2.1)) := by
    rw [← hbase]
    exact observedLaw_treatment_compProd P
  have hout := Measure.compProd_congr hY
  calc
    ((covariateLaw P ⊗ₘ kA) ⊗ₘ kY).map
        (fun z => (z.1.1, z.1.2, z.2)) =
      ((P.map (fun z : Obs d => (z.1, z.2.1))) ⊗ₘ kY).map
        (fun z => (z.1.1, z.1.2, z.2)) := by rw [hbase']
    _ = ((P.map (fun z : Obs d => (z.1, z.2.1))) ⊗ₘ
          ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
            (fun z => (z.1, z.2.1)) P).map
        (fun z => (z.1.1, z.1.2, z.2)) := by rw [hout]
    _ = P := observedLaw_outcome_recomposition P

/-- A probability law on `Bool` is determined by the real value of its mass
at `true`. [For the stated inputs and conditions](hyp:ν,p,hp,htrue), [the asserted conclusion holds](goal). -/
lemma boolProbability_eq_realBernoulli (ν : Measure Bool)
    [IsProbabilityMeasure ν] (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (htrue : (ν {true}).toReal = p) :
    ν = realBernoulli p := by
  letI : IsProbabilityMeasure (realBernoulli p) :=
    realBernoulli_probability p hp
  have hνtrue : ν {true} = ENNReal.ofReal p := by
    rw [← htrue, ENNReal.ofReal_toReal]
    exact measure_ne_top ν {true}
  apply Measure.ext
  intro s hs
  by_cases ht : true ∈ s
  · by_cases hf : false ∈ s
    · have hsuniv : s = Set.univ := by
        ext b
        cases b <;> simp_all
      subst s
      simp only [measure_univ]
    · have hsone : s = {true} := by
        ext b
        cases b <;> simp_all
      subst s
      simp [realBernoulli, hνtrue]
  · by_cases hf : false ∈ s
    · have hsone : s = {false} := by
        ext b
        cases b <;> simp_all
      subst s
      have hcomp : ({false} : Set Bool) = {true}ᶜ := by
        ext b
        cases b <;> simp
      have hνfin : ν {true} ≠ ∞ := measure_ne_top ν {true}
      have hrfin : realBernoulli p {true} ≠ ∞ :=
        measure_ne_top (realBernoulli p) {true}
      rw [hcomp, measure_compl (MeasurableSet.singleton true) hνfin,
        measure_compl (MeasurableSet.singleton true) hrfin,
        measure_univ, measure_univ, hνtrue]
      simp [realBernoulli]
    · have hsempty : s = ∅ := by
        ext b
        cases b <;> simp_all
      subst s
      simp [realBernoulli]

/-- A selected propensity in `(0,1)` identifies the entire Bool-valued
conditional treatment law, rather than only its mass at `true`. [For the stated inputs and conditions](hyp:d,P,e,hselected), [the asserted conclusion holds](goal). -/
lemma condDistrib_treatment_eq_realBernoulli_of_selected {d : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (e : (Fin d → ℝ) → ℝ)
    (hselected : ∀ᵐ x ∂covariateLaw P,
      e x = propensity P x ∧ 0 < e x ∧ e x < 1) :
    (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
      (fun z => z.1) P : (Fin d → ℝ) → Measure Bool) =ᵐ[covariateLaw P]
        fun x => realBernoulli (e x) := by
  filter_upwards [hselected] with x hx
  let ν : Measure Bool := ProbabilityTheory.condDistrib
    (fun z : Obs d => z.2.1) (fun z => z.1) P x
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  apply boolProbability_eq_realBernoulli ν (e x)
  · exact ⟨hx.2.1.le, hx.2.2.le⟩
  · change (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
      (fun z => z.1) P x {true}).toReal = e x
    exact hx.1.symm

/-- Gaussian arm-kernel identities holding for almost every covariate lift to
the joint `(X,A)` law used by observed-law disintegration. [For the stated inputs and conditions](hyp:d,P,σ,μ₀,μ₁,harms), [the asserted conclusion holds](goal). -/
lemma gaussianArmKernels_joint_ae {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (σ : ℝ)
    (μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (harms : ∀ᵐ x ∂covariateLaw P,
      armKernel P x true =
          gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩ ∧
        armKernel P x false =
          gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :
    (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
      (fun z => (z.1, z.2.1)) P :
        ((Fin d → ℝ) × Bool) → Measure ℝ) =ᵐ[
          P.map (fun z : Obs d => (z.1, z.2.1))]
      fun xa => if xa.2 then
        gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
      else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩ := by
  have hmap : (P.map (fun z : Obs d => (z.1, z.2.1))).map Prod.fst =
      covariateLaw P := by
    unfold covariateLaw
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [← hmap] at harms
  have harms' := ae_of_ae_map (μ := P.map (fun z : Obs d => (z.1, z.2.1)))
    measurable_fst.aemeasurable harms
  filter_upwards [harms'] with xa hx
  rcases xa with ⟨x, a⟩
  cases a with
  | false =>
      change armKernel P x false =
        gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩
      exact hx.2
  | true =>
      change armKernel P x true =
        gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩
      exact hx.1

/-- A positive selected propensity lets the joint affine outcome-kernel
transport be specialized to the treated Gaussian arm. [For the stated inputs and conditions](hyp:d,P,sigma,e,mu₀,mu₁,hselected,harms), [the asserted conclusion holds](goal). -/
lemma transformedDornLaw_treatedKernel_gaussian_ae {d : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    [IsFiniteMeasure (transformedDornLaw P)] (sigma : ℝ)
    (e mu₀ mu₁ : (Fin d → ℝ) → ℝ)
    (hselected : ∀ᵐ x ∂covariateLaw P,
      e x = propensity P x ∧ 0 < e x ∧ e x < 1)
    (harms : ∀ᵐ x ∂covariateLaw P,
      armKernel P x true =
          gaussianReal (mu₁ x) ⟨sigma ^ 2, sq_nonneg sigma⟩ ∧
        armKernel P x false =
          gaussianReal (mu₀ x) ⟨sigma ^ 2, sq_nonneg sigma⟩) :
    ∀ᵐ y ∂covariateLaw (transformedDornLaw P),
      treatedKernel (transformedDornLaw P) y =
        gaussianReal (transformedResponse mu₁ y)
          ⟨sigma ^ 2, sq_nonneg sigma⟩ := by
  letI : IsProbabilityMeasure (covariateLaw P) := by
    unfold covariateLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have htransport := transformedDornLaw_outcomeKernel_ae P
  rw [← observedLaw_treatment_compProd P] at htransport
  have hsections := Measure.ae_ae_of_ae_compProd htransport
  have hA := condDistrib_treatment_eq_realBernoulli_of_selected P e hselected
  have hsource : ∀ᵐ x ∂covariateLaw P,
      treatedKernel (transformedDornLaw P) (affineToCube x) =
        gaussianReal (mu₁ x) ⟨sigma ^ 2, sq_nonneg sigma⟩ := by
    filter_upwards [hsections, hA, hselected, harms] with x hx hAx hsel harmsx
    rw [hAx] at hx
    have htrue := realBernoulli_ae_at_true_of_pos (e x) hsel.2.1
      (fun a => ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
          (fun z => (z.1, z.2.1)) (transformedDornLaw P)
            (affineToCube x, a) =
        ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
          (fun z => (z.1, z.2.1)) P (x, a)) hx
    exact htrue.trans harmsx.1
  let r : (Fin d → ℝ) → (Fin d → ℝ) := affineToCube
  let s : (Fin d → ℝ) → (Fin d → ℝ) := fun x i => 2 * x i - 1
  have hs : Measurable s := affineFromCube_measurable
  have hcov : covariateLaw (transformedDornLaw P) =
      (covariateLaw P).map r := transformedDornLaw_covariateLaw P
  have hmapS : (covariateLaw (transformedDornLaw P)).map s =
      covariateLaw P := by
    rw [hcov, Measure.map_map hs affineToCube_measurable]
    have hsr : s ∘ r = id := by
      funext x
      exact affineToCube_inverse x
    rw [hsr, Measure.map_id]
  apply Causalean.Mathlib.Probability.Independence.Conditional.Transport.eventuallyEq_of_comp_aeRetraction
    r s hs hmapS (Filter.Eventually.of_forall fun x => by
      change affineToCube (fun i => 2 * x i - 1) = x
      exact affineToCube_affineFromCube x)
  filter_upwards [hsource] with x hx
  change treatedKernel (transformedDornLaw P) (affineToCube x) =
    gaussianReal (transformedResponse mu₁ (affineToCube x))
      ⟨sigma ^ 2, sq_nonneg sigma⟩
  simpa only [transformedResponse_affineToCube] using hx

/-- A Gaussian with standard deviation bounded by `B` satisfies the model's
centered MGF envelope with scale `B`. [For the stated inputs and conditions](hyp:m,sigma,B,t,hB,hsigma), [the asserted conclusion holds](goal). -/
lemma gaussianReal_centered_mgf_bound (m sigma B t : ℝ)
    (hB : 0 ≤ B) (hsigma : |sigma| ≤ B) :
    Integrable (fun y : ℝ => Real.exp (t * (y - m)))
        (gaussianReal m ⟨sigma ^ 2, sq_nonneg sigma⟩) ∧
      ProbabilityTheory.mgf (fun y : ℝ => y - m)
          (gaussianReal m ⟨sigma ^ 2, sq_nonneg sigma⟩) t ≤
        Real.exp (B ^ 2 * t ^ 2 / 2) := by
  let v : NNReal := ⟨sigma ^ 2, sq_nonneg sigma⟩
  have hmap : (gaussianReal m v).map (fun y : ℝ => y - m) =
      gaussianReal 0 v := by
    simpa using ProbabilityTheory.gaussianReal_map_sub_const (μ := m) (v := v) m
  constructor
  · have hi := ProbabilityTheory.integrable_exp_mul_gaussianReal
        (μ := (0 : ℝ)) (v := v) t
    rw [← hmap] at hi
    have hi' := (integrable_map_measure (by fun_prop)
      (by fun_prop : AEMeasurable (fun y : ℝ => y - m)
        (gaussianReal m v))).mp hi
    change Integrable ((fun x : ℝ => Real.exp (t * x)) ∘
      fun y : ℝ => y - m) (gaussianReal m v)
    exact hi'
  · have hmgf : ProbabilityTheory.mgf (fun y : ℝ => y - m)
        (gaussianReal m v) t = Real.exp (sigma ^ 2 * t ^ 2 / 2) := by
      rw [← ProbabilityTheory.mgf_id_map (by fun_prop), hmap]
      rw [show sigma ^ 2 = (v : ℝ) by rfl]
      simpa only [zero_mul, zero_add] using congrFun
        (ProbabilityTheory.mgf_id_gaussianReal (μ := (0 : ℝ)) (v := v)) t
    rw [hmgf]
    apply Real.exp_le_exp.mpr
    have hsquare : sigma ^ 2 ≤ B ^ 2 := by
      apply (sq_le_sq).2
      rw [abs_of_nonneg hB]
      exact hsigma
    nlinarith [sq_nonneg t]

/-- Transported Gaussian treated kernels give the bounded-mean and
sub-Gaussian residual field once their means and standard deviation are
bounded by the model scale. [For the stated inputs and conditions](hyp:d,P,sigma,B,e,mu₀,mu₁,hB,hsigma,hselected,harms,hmean), [the asserted conclusion holds](goal). -/
lemma transformedDornLaw_boundedGaussianOutcome {d : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    [IsFiniteMeasure (transformedDornLaw P)] (sigma B : ℝ)
    (e mu₀ mu₁ : (Fin d → ℝ) → ℝ)
    (hB : 0 ≤ B) (hsigma : |sigma| ≤ B)
    (hselected : ∀ᵐ x ∂covariateLaw P,
      e x = propensity P x ∧ 0 < e x ∧ e x < 1)
    (harms : ∀ᵐ x ∂covariateLaw P,
      armKernel P x true =
          gaussianReal (mu₁ x) ⟨sigma ^ 2, sq_nonneg sigma⟩ ∧
        armKernel P x false =
          gaussianReal (mu₀ x) ⟨sigma ^ 2, sq_nonneg sigma⟩)
    (hmean : ∀ᵐ y ∂covariateLaw (transformedDornLaw P),
      |transformedResponse mu₁ y| ≤ B) :
    BoundedMeanSubGaussianResidual (transformedDornLaw P) B := by
  have hk := transformedDornLaw_treatedKernel_gaussian_ae
    P sigma e mu₀ mu₁ hselected harms
  unfold BoundedMeanSubGaussianResidual
  filter_upwards [hk, hmean] with y hky hmy
  have hreg : treatedRegression (transformedDornLaw P) y =
      transformedResponse mu₁ y := by
    unfold treatedRegression
    rw [hky]
    exact ProbabilityTheory.integral_id_gaussianReal
  constructor
  · rw [hreg]
    exact hmy
  · intro t
    rw [hky, hreg]
    exact gaussianReal_centered_mgf_bound
      (transformedResponse mu₁ y) sigma B t hB hsigma

/-- Affine transport preserves the probability-law instance. [For the stated inputs and conditions](hyp:d,P), [the asserted conclusion holds](goal). -/
lemma transformedDornLaw_probability {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] :
    IsProbabilityMeasure (transformedDornLaw P) := by
  unfold transformedDornLaw
  exact Measure.isProbabilityMeasure_map (by
    unfold affineToCube
    fun_prop)

/-- Gaussian specialization of the two-stage recomposition theorem. The two
almost-everywhere hypotheses are exactly the propensity and arm-kernel
identifications supplied by a Dorn remaining-model witness. [For the stated inputs and conditions](hyp:d,P,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,he01,hA,hY), [the asserted conclusion holds](goal). -/
lemma gaussianObservedLaw_recomposition {d : ℕ} (P : Measure (Obs d))
    [IsFiniteMeasure P] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ) (he : Measurable e)
    (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hA : (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
        (fun z => z.1) P : (Fin d → ℝ) → Measure Bool) =ᵐ[covariateLaw P]
          fun x => realBernoulli (e x))
    (hY : (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
        (fun z => (z.1, z.2.1)) P :
          ((Fin d → ℝ) × Bool) → Measure ℝ) =ᵐ[
            P.map (fun z : Obs d => (z.1, z.2.1))]
          fun xa => if xa.2 then
            gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
          else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩) :
    let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
      ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
        (by unfold realBernoulli; fun_prop)
    letI : ProbabilityTheory.IsMarkovKernel kA :=
      ⟨fun x => realBernoulli_probability (e x) (he01 x)⟩
    let kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ :=
      ProbabilityTheory.Kernel.mk (fun xa => if xa.2 then
          gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
        else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
        (by
          apply Measurable.ite (measurable_snd (MeasurableSet.singleton true))
          · fun_prop
          · fun_prop)
    letI : ProbabilityTheory.IsMarkovKernel kY :=
      ⟨fun xa => by
        change IsProbabilityMeasure (if xa.2 then
          gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
        else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
        cases xa.2 <;>
          exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
    (((covariateLaw P ⊗ₘ kA) ⊗ₘ kY).map
      (fun z => (z.1.1, z.1.2, z.2))) = P := by
  dsimp
  let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun x => realBernoulli_probability (e x) (he01 x)⟩
  let kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ :=
    ProbabilityTheory.Kernel.mk (fun xa => if xa.2 then
        gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
      else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
      (by
        apply Measurable.ite (measurable_snd (MeasurableSet.singleton true))
        · fun_prop
        · fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kY :=
    ⟨fun xa => by
      change IsProbabilityMeasure (if xa.2 then
        gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
      else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
      cases xa.2 <;>
        exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
  apply observedLaw_kernel_recomposition P kA kY
  · change (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
      (fun z => z.1) P : (Fin d → ℝ) → Measure Bool) =ᵐ[covariateLaw P]
        fun x => realBernoulli (e x)
    exact hA
  · change (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
      (fun z => (z.1, z.2.1)) P :
        ((Fin d → ℝ) × Bool) → Measure ℝ) =ᵐ[
          P.map (fun z : Obs d => (z.1, z.2.1))]
        fun xa => if xa.2 then
          gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
        else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
    exact hY

/-- The displayed selected propensity and Dorn's two Gaussian arm identities
jointly determine the full observed law. [For the stated inputs and conditions](hyp:d,P,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,he01,hselected,harms), [the asserted conclusion holds](goal). -/
lemma gaussianObservedLaw_recomposition_of_selected {d : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ) (he : Measurable e)
    (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hselected : ∀ᵐ x ∂covariateLaw P,
      e x = propensity P x ∧ 0 < e x ∧ e x < 1)
    (harms : ∀ᵐ x ∂covariateLaw P,
      armKernel P x true =
          gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩ ∧
        armKernel P x false =
          gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :
    let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
      ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
        (by unfold realBernoulli; fun_prop)
    letI : ProbabilityTheory.IsMarkovKernel kA :=
      ⟨fun x => realBernoulli_probability (e x) (he01 x)⟩
    let kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ :=
      ProbabilityTheory.Kernel.mk (fun xa => if xa.2 then
          gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
        else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
        (by
          apply Measurable.ite (measurable_snd (MeasurableSet.singleton true))
          · fun_prop
          · fun_prop)
    letI : ProbabilityTheory.IsMarkovKernel kY :=
      ⟨fun xa => by
        change IsProbabilityMeasure (if xa.2 then
          gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
        else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
        cases xa.2 <;>
          exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
    (((covariateLaw P ⊗ₘ kA) ⊗ₘ kY).map
      (fun z => (z.1.1, z.1.2, z.2))) = P := by
  apply gaussianObservedLaw_recomposition P σ e μ₀ μ₁ he hμ₀ hμ₁ he01
  · exact condDistrib_treatment_eq_realBernoulli_of_selected P e hselected
  · exact gaussianArmKernels_joint_ae P σ μ₀ μ₁ harms

/-- Gaussian completion at covariate `x` with independent potential outcomes. For [the stated inputs and conditions](hyp:σ,e,μ₀,μ₁,x), [the `gaussianCompletionAt` object being defined](goal). -/
noncomputable def gaussianCompletionAt {d : ℕ} (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Measure (Completion d) :=
  ((realBernoulli (e x)).prod
    ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
      (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))).map
        (fun z => (x, z.1, z.2.1, z.2.2,
          if z.1 then z.2.2 else z.2.1))

/-- Gaussian completion is a measurable measure-valued map whenever its
propensity and the two arm means are measurable. [For the stated inputs and conditions](hyp:d,σ,e,μ₀,μ₁,he,hμ₀,hμ₁), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionAt_measurable {d : ℕ} (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁) :
    Measurable (gaussianCompletionAt σ e μ₀ μ₁) := by
  let νe : (Fin d → ℝ) → FiniteMeasure Bool := fun x => by
    letI : IsFiniteMeasure (realBernoulli (e x)) := by
      constructor
      simp [realBernoulli]
    exact ⟨realBernoulli (e x), inferInstance⟩
  let ν₀ : (Fin d → ℝ) → FiniteMeasure ℝ := fun x => by
    letI : IsProbabilityMeasure
        (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    exact ⟨gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩, inferInstance⟩
  let ν₁ : (Fin d → ℝ) → FiniteMeasure ℝ := fun x => by
    letI : IsProbabilityMeasure
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    exact ⟨gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩, inferInstance⟩
  have hνe : Measurable νe := by
    apply Measurable.subtype_mk
    unfold realBernoulli
    fun_prop
  have hν₀ : Measurable ν₀ := by
    apply Measurable.subtype_mk
    exact ProbabilityTheory.measurable_gaussianReal.comp
      (hμ₀.prodMk measurable_const)
  have hν₁ : Measurable ν₁ := by
    apply Measurable.subtype_mk
    exact ProbabilityTheory.measurable_gaussianReal.comp
      (hμ₁.prodMk measurable_const)
  let ν₀₁ : (Fin d → ℝ) → FiniteMeasure (ℝ × ℝ) := fun x =>
    ⟨(ν₀ x : Measure ℝ).prod (ν₁ x : Measure ℝ), inferInstance⟩
  have hν₀₁ : Measurable ν₀₁ := by
    apply Measurable.subtype_mk
    exact FiniteMeasure.measurable_fun_prod.comp (hν₀.prodMk hν₁)
  let νa : (Fin d → ℝ) → FiniteMeasure (Bool × ℝ × ℝ) := fun x =>
    ⟨(νe x : Measure Bool).prod (ν₀₁ x : Measure (ℝ × ℝ)), inferInstance⟩
  have hνa : Measurable νa := by
    apply Measurable.subtype_mk
    exact FiniteMeasure.measurable_fun_prod.comp (hνe.prodMk hν₀₁)
  let νx : (Fin d → ℝ) → FiniteMeasure
      ((Fin d → ℝ) × Bool × ℝ × ℝ) := fun x =>
    ⟨(Measure.dirac x).prod (νa x : Measure (Bool × ℝ × ℝ)), inferInstance⟩
  have hνx : Measurable νx := by
    apply Measurable.subtype_mk
    have hdirac : Measurable (fun x : Fin d → ℝ =>
        (⟨Measure.dirac x, inferInstance⟩ : FiniteMeasure (Fin d → ℝ))) := by
      apply Measurable.subtype_mk
      exact Measure.measurable_dirac
    exact FiniteMeasure.measurable_fun_prod.comp (hdirac.prodMk hνa)
  let F : ((Fin d → ℝ) × Bool × ℝ × ℝ) → Completion d := fun z =>
    (z.1, z.2.1, z.2.2.1, z.2.2.2,
      if z.2.1 then z.2.2.2 else z.2.2.1)
  have hF : Measurable F := by
    unfold F
    have hlast : Measurable (fun z : (Fin d → ℝ) × Bool × ℝ × ℝ =>
        if z.2.1 then z.2.2.2 else z.2.2.1) :=
      Measurable.ite (measurable_snd.fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  have heq : gaussianCompletionAt σ e μ₀ μ₁ = fun x =>
      (νx x : Measure ((Fin d → ℝ) × Bool × ℝ × ℝ)).map F := by
    funext x
    letI : IsFiniteMeasure (realBernoulli (e x)) := by
      constructor
      simp [realBernoulli]
    letI : IsProbabilityMeasure
        (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    letI : IsProbabilityMeasure
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    unfold gaussianCompletionAt
    change Measure.map _ ((realBernoulli (e x)).prod
        ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
          (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))) =
      Measure.map F ((Measure.dirac x).prod
        ((realBernoulli (e x)).prod
          ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
            (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))))
    rw [Measure.dirac_prod, Measure.map_map hF (by fun_prop)]
    rfl
  rw [heq]
  exact (Measure.measurable_map F hF).comp (measurable_subtype_coe.comp hνx)

/-- The measurable Gaussian completion family, packaged as a kernel. For [the stated inputs and conditions](hyp:σ,e,μ₀,μ₁,he,hμ₀,hμ₁), [the `gaussianCompletionKernel` object being defined](goal). -/
noncomputable def gaussianCompletionKernel {d : ℕ} (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁) :
    ProbabilityTheory.Kernel (Fin d → ℝ) (Completion d) :=
  ProbabilityTheory.Kernel.mk (gaussianCompletionAt σ e μ₀ μ₁)
    (gaussianCompletionAt_measurable σ e μ₀ μ₁ he hμ₀ hμ₁)

/-- Every fixed Gaussian product fibre records the selected potential outcome. [For the stated inputs and conditions](hyp:d,σ,e,μ₀,μ₁,x), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionAt_consistency {d : ℕ} (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    OutcomeConsistency (gaussianCompletionAt σ e μ₀ μ₁ x) := by
  unfold OutcomeConsistency gaussianCompletionAt
  have hm : Measurable (fun z : Bool × ℝ × ℝ =>
      (x, z.1, z.2.1, z.2.2, if z.1 then z.2.2 else z.2.1)) := by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  have hsel : Measurable (fun ω : Completion d =>
      if ω.2.1 then ω.2.2.2.1 else ω.2.2.1) := by
    apply Measurable.ite
      (by measurability : MeasurableSet {ω : Completion d | ω.2.1 = true})
      (by fun_prop) (by fun_prop)
  have hs : MeasurableSet {ω : Completion d |
      ω.2.2.2.2 = if ω.2.1 then ω.2.2.2.1 else ω.2.2.1} :=
    measurableSet_eq_fun (by fun_prop) hsel
  apply (ae_map_iff hm.aemeasurable hs).2
  filter_upwards [] with z
  cases z.1 <;> simp

/-- Mixing measurable Gaussian product fibres preserves outcome consistency. [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_consistency {d : ℕ}
    (mu : Measure (Fin d → ℝ)) (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁) :
    OutcomeConsistency
      (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)) := by
  let S : Set (Completion d) :=
    {ω | ω.2.2.2.2 = if ω.2.1 then ω.2.2.2.1 else ω.2.2.1}
  have hsel : Measurable (fun ω : Completion d =>
      if ω.2.1 then ω.2.2.2.1 else ω.2.2.1) := by
    apply Measurable.ite
      (by measurability : MeasurableSet {ω : Completion d | ω.2.1 = true})
      (by fun_prop) (by fun_prop)
  have hS : MeasurableSet S :=
    measurableSet_eq_fun (by fun_prop) hsel
  have hk := gaussianCompletionAt_measurable σ e μ₀ μ₁ he hμ₀ hμ₁
  have hzero : (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)) Sᶜ = 0 := by
    apply le_antisymm _ zero_le
    calc
      _ ≤ ∫⁻ x, (gaussianCompletionAt σ e μ₀ μ₁ x) Sᶜ ∂mu :=
        Measure.bind_apply_le _ hS.compl
      _ = 0 := by
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [] with x
        exact (measure_eq_zero_iff_ae_notMem).2
          (by simpa only [OutcomeConsistency, S, Set.mem_compl_iff,
                not_not, Set.mem_ofPred_eq] using
            gaussianCompletionAt_consistency σ e μ₀ μ₁ x)
  simpa only [OutcomeConsistency, S, Set.mem_compl_iff, not_not,
    Set.mem_ofPred_eq] using (measure_eq_zero_iff_ae_notMem).mp hzero

/-- A pair of Gaussian laws with measurable means is measure-valued measurable. [For the stated inputs and conditions](hyp:d,σ,μ₀,μ₁,hμ₀,hμ₁), [the asserted conclusion holds](goal). -/
lemma gaussianPair_measurable {d : ℕ} (σ : ℝ)
    (μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁) :
    Measurable (fun x =>
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)) := by
  let ν₀ : (Fin d → ℝ) → ProbabilityMeasure ℝ := fun x =>
    ⟨gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩,
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
  let ν₁ : (Fin d → ℝ) → ProbabilityMeasure ℝ := fun x =>
    ⟨gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩,
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
  have hν₀ : Measurable ν₀ := by
    apply Measurable.subtype_mk
    exact ProbabilityTheory.measurable_gaussianReal.comp
      (hμ₀.prodMk measurable_const)
  have hν₁ : Measurable ν₁ := by
    apply Measurable.subtype_mk
    exact ProbabilityTheory.measurable_gaussianReal.comp
      (hμ₁.prodMk measurable_const)
  exact ProbabilityMeasure.measurable_fun_prod.comp (hν₀.prodMk hν₁)

/-- At fixed covariates, Gaussian potential outcomes and treatment factor. [For the stated inputs and conditions](hyp:d,σ,e,μ₀,μ₁,x,he), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionAt_potential_treatment_factorization {d : ℕ}
    (σ : ℝ) (e μ₀ μ₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc (0 : ℝ) 1) :
    (gaussianCompletionAt σ e μ₀ μ₁ x).map
        (fun ω => (ω.1, ((ω.2.2.1, ω.2.2.2.1), ω.2.1))) =
      (Measure.dirac x).prod
        (((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
          (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)).prod
          (realBernoulli (e x))) := by
  letI := realBernoulli_probability (e x) he
  letI : IsProbabilityMeasure
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  letI : IsProbabilityMeasure
      (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  unfold gaussianCompletionAt
  rw [Measure.map_map (by fun_prop) (by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption))]
  rw [Measure.dirac_prod]
  change Measure.map ((Prod.mk x) ∘ Prod.swap)
      ((realBernoulli (e x)).prod
        ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
          (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))) = _
  rw [← Measure.map_map (by fun_prop) measurable_swap, Measure.prod_swap]

/-- Mixing the fixed Gaussian factorization preserves its conditional product. [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_potential_treatment_factorization {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1) :
    let kY : ProbabilityTheory.Kernel (Fin d → ℝ) (ℝ × ℝ) :=
      ProbabilityTheory.Kernel.mk (fun x =>
        (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
          (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))
        (gaussianPair_measurable σ μ₀ μ₁ hμ₀ hμ₁)
    let kA : ProbabilityTheory.Kernel ((Fin d → ℝ) × (ℝ × ℝ)) Bool :=
      ProbabilityTheory.Kernel.mk (fun xy => realBernoulli (e xy.1))
        (by unfold realBernoulli; fun_prop)
    (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map
        (fun ω => (ω.1, ((ω.2.2.1, ω.2.2.2.1), ω.2.1))) =
      Measure.compProd mu (ProbabilityTheory.Kernel.compProd kY kA) := by
  dsimp
  let kY : ProbabilityTheory.Kernel (Fin d → ℝ) (ℝ × ℝ) :=
    ProbabilityTheory.Kernel.mk (fun x =>
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))
      (gaussianPair_measurable σ μ₀ μ₁ hμ₀ hμ₁)
  let kA : ProbabilityTheory.Kernel ((Fin d → ℝ) × (ℝ × ℝ)) Bool :=
    ProbabilityTheory.Kernel.mk (fun xy => realBernoulli (e xy.1))
      (by unfold realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kY := ⟨fun x => by
    letI : IsProbabilityMeasure
        (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    letI : IsProbabilityMeasure
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    change IsProbabilityMeasure
      ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))
    exact Measure.prod.instIsProbabilityMeasure _ _⟩
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun xy => realBernoulli_probability (e xy.1) (hvalid xy.1)⟩
  have hk := gaussianCompletionAt_measurable σ e μ₀ μ₁ he hμ₀ hμ₁
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.bind_apply (hs.preimage (by fun_prop)) hk.aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  letI := realBernoulli_probability (e x) (hvalid x)
  letI : IsProbabilityMeasure
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  letI : IsProbabilityMeasure
      (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have hfix := gaussianCompletionAt_potential_treatment_factorization
    σ e μ₀ μ₁ x (hvalid x)
  have happ := congrArg
    (fun m : Measure ((Fin d → ℝ) × ((ℝ × ℝ) × Bool)) => m s) hfix
  rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply hs,
    lintegral_dirac] at happ
  rw [Measure.prod_apply (hs.preimage (by fun_prop))] at happ
  rw [ProbabilityTheory.Kernel.compProd_apply]
  · simpa [kY, kA] using happ
  · exact hs.preimage (by fun_prop)

/-- [For the stated inputs and conditions](hyp:d,σ,e,μ₀,μ₁,x,he), [the asserted conclusion holds](goal). -/

lemma gaussianCompletionAt_covariate_potential {d : ℕ} (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc (0 : ℝ) 1) :
    (gaussianCompletionAt σ e μ₀ μ₁ x).map
        (fun ω => (ω.1, (ω.2.2.1, ω.2.2.2.1))) =
      (Measure.dirac x).prod
        ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
          (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)) := by
  letI := realBernoulli_probability (e x) he
  letI : IsProbabilityMeasure
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  letI : IsProbabilityMeasure
      (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  unfold gaussianCompletionAt
  rw [Measure.map_map (by fun_prop) (by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)), Measure.dirac_prod]
  calc
    Measure.map (fun z : Bool × (ℝ × ℝ) => (x, z.2))
        ((realBernoulli (e x)).prod
          ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
            (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))) =
      Measure.map (Prod.mk x) (Measure.map Prod.snd
        ((realBernoulli (e x)).prod
          ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
            (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)))) := by
        rw [Measure.map_map (by fun_prop) measurable_snd]
        rfl
    _ = _ := by rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- [For the stated inputs and conditions](hyp:d,σ,e,μ₀,μ₁,x,he), [the asserted conclusion holds](goal). -/

lemma gaussianCompletionAt_covariate_treatment {d : ℕ} (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc (0 : ℝ) 1) :
    (gaussianCompletionAt σ e μ₀ μ₁ x).map
        (fun ω => (ω.1, ω.2.1)) =
      (Measure.dirac x).prod (realBernoulli (e x)) := by
  letI := realBernoulli_probability (e x) he
  letI : IsProbabilityMeasure
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  letI : IsProbabilityMeasure
      (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  unfold gaussianCompletionAt
  rw [Measure.map_map (by fun_prop) (by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)), Measure.dirac_prod]
  change Measure.map (fun z : Bool × (ℝ × ℝ) => (x, z.1))
      ((realBernoulli (e x)).prod
        ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
          (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))) = _
  calc
    Measure.map (fun z : Bool × (ℝ × ℝ) => (x, z.1))
        ((realBernoulli (e x)).prod
          ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
            (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))) =
      Measure.map (Prod.mk x) (Measure.map Prod.fst
        ((realBernoulli (e x)).prod
          ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
            (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)))) := by
        rw [Measure.map_map (by fun_prop) measurable_fst]
        rfl
    _ = _ := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid), [the asserted conclusion holds](goal). -/

lemma gaussianCompletionBind_covariate_potential {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1) :
    let kY : ProbabilityTheory.Kernel (Fin d → ℝ) (ℝ × ℝ) :=
      ProbabilityTheory.Kernel.mk (fun x =>
        (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
          (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))
        (gaussianPair_measurable σ μ₀ μ₁ hμ₀ hμ₁)
    (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map
        (fun ω => (ω.1, (ω.2.2.1, ω.2.2.2.1))) = mu ⊗ₘ kY := by
  dsimp
  let kY : ProbabilityTheory.Kernel (Fin d → ℝ) (ℝ × ℝ) :=
    ProbabilityTheory.Kernel.mk (fun x =>
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))
      (gaussianPair_measurable σ μ₀ μ₁ hμ₀ hμ₁)
  letI : ProbabilityTheory.IsMarkovKernel kY := ⟨fun x => by
    letI : IsProbabilityMeasure
        (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    letI : IsProbabilityMeasure
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    change IsProbabilityMeasure
      ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))
    exact Measure.prod.instIsProbabilityMeasure _ _⟩
  have hk := gaussianCompletionAt_measurable σ e μ₀ μ₁ he hμ₀ hμ₁
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.bind_apply (hs.preimage (by fun_prop)) hk.aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  letI : IsProbabilityMeasure
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  letI : IsProbabilityMeasure
      (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have hfix := gaussianCompletionAt_covariate_potential σ e μ₀ μ₁ x (hvalid x)
  have happ := congrArg (fun m : Measure ((Fin d → ℝ) × (ℝ × ℝ)) => m s) hfix
  rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply hs,
    lintegral_dirac] at happ
  simpa [kY] using happ

/-- [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid), [the asserted conclusion holds](goal). -/

lemma gaussianCompletionBind_covariate_treatment {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1) :
    let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
      ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
        (by unfold realBernoulli; fun_prop)
    (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map
        (fun ω => (ω.1, ω.2.1)) = mu ⊗ₘ kA := by
  dsimp
  let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun x => realBernoulli_probability (e x) (hvalid x)⟩
  have hk := gaussianCompletionAt_measurable σ e μ₀ μ₁ he hμ₀ hμ₁
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.bind_apply (hs.preimage (by fun_prop)) hk.aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  have hfix := gaussianCompletionAt_covariate_treatment σ e μ₀ μ₁ x (hvalid x)
  have happ := congrArg (fun m : Measure ((Fin d → ℝ) × Bool) => m s) hfix
  rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply hs,
    lintegral_dirac] at happ
  simpa [kA] using happ

/-- [For the stated inputs and conditions](hyp:d,σ,e,μ₀,μ₁,x,he), [the asserted conclusion holds](goal). -/

lemma gaussianCompletionAt_covariate_marginal {d : ℕ} (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc (0 : ℝ) 1) :
    (gaussianCompletionAt σ e μ₀ μ₁ x).map Prod.fst = Measure.dirac x := by
  letI := realBernoulli_probability (e x) he
  letI : IsProbabilityMeasure
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  letI : IsProbabilityMeasure
      (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  unfold gaussianCompletionAt
  rw [Measure.map_map measurable_fst (by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption))]
  change Measure.map (fun _ : Bool × (ℝ × ℝ) => x)
      ((realBernoulli (e x)).prod
        ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
          (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))) = _
  rw [Measure.map_const, measure_univ, one_smul]

/-- Covariate almost-everywhere propensity validity suffices for a Gaussian
completion bind to retain its base covariate law. [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_covariate_marginal_ae {d : ℕ}
    (mu : Measure (Fin d → ℝ)) (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ᵐ x ∂mu, e x ∈ Set.Icc (0 : ℝ) 1) :
    (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map Prod.fst = mu := by
  have hk := gaussianCompletionAt_measurable σ e μ₀ μ₁ he hμ₀ hμ₁
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    Measure.bind_apply (measurable_fst hs) hk.aemeasurable]
  simp_rw [← Measure.map_apply measurable_fst hs]
  calc
    _ = ∫⁻ x, (Measure.dirac x) s ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hvalid] with x hx
      rw [gaussianCompletionAt_covariate_marginal σ e μ₀ μ₁ x hx]
    _ = mu s := by
      simp only [Measure.dirac_apply' _ hs]
      exact lintegral_indicator_one hs

/-- The Bernoulli parameter used by a Gaussian completion is a propensity
version of its observed law. [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_propensity_ae {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [IsProbabilityMeasure mu] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    [IsFiniteMeasure
      ((mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map observed)] :
    let P := (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map observed
    ∀ᵐ x ∂mu, propensity P x = e x := by
  dsimp
  let P := (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map observed
  let k : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  have hk := gaussianCompletionAt_measurable σ e μ₀ μ₁ he hμ₀ hμ₁
  have hpoint : ∀ x, IsProbabilityMeasure
      (gaussianCompletionAt σ e μ₀ μ₁ x) := by
    intro x
    letI := realBernoulli_probability (e x) (hvalid x)
    letI : IsProbabilityMeasure
        (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    letI : IsProbabilityMeasure
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    unfold gaussianCompletionAt
    apply Measure.isProbabilityMeasure_map
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  letI : IsProbabilityMeasure (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)) :=
    isProbabilityMeasure_bind hk.aemeasurable
      (Filter.Eventually.of_forall hpoint)
  have hobs : Measurable (@observed d) := by unfold observed; fun_prop
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Measure.isProbabilityMeasure_map hobs.aemeasurable
  letI : ProbabilityTheory.IsMarkovKernel k :=
    ⟨fun x => realBernoulli_probability (e x) (hvalid x)⟩
  have hcov : P.map Prod.fst = mu := by
    dsimp [P]
    rw [Measure.map_map (by fun_prop) hobs]
    exact gaussianCompletionBind_covariate_marginal_ae mu σ e μ₀ μ₁
      he hμ₀ hμ₁ (Filter.Eventually.of_forall hvalid)
  have hpair : P.map (fun z => (z.1, z.2.1)) = Measure.compProd mu k := by
    dsimp [P]
    rw [Measure.map_map (by fun_prop) hobs]
    exact gaussianCompletionBind_covariate_treatment mu σ e μ₀ μ₁
      he hμ₀ hμ₁ hvalid
  have hae := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := P) (X := fun z : Obs d => z.1) (Y := fun z : Obs d => z.2.1)
    (κ := k) (by fun_prop) (by fun_prop) (by simpa [hcov] using hpair)
  rw [hcov] at hae
  filter_upwards [hae] with x hx
  unfold propensity
  rw [hx]
  simp [k, realBernoulli, (hvalid x).1]

/-- A globally valid representative of a real-valued propensity. For [the stated inputs and conditions](hyp:r), [the `gaussianPropensityClamp` object being defined](goal). -/
def gaussianPropensityClamp (r : ℝ) : ℝ := max 0 (min 1 r)

/-- [For the stated inputs and conditions](hyp:r), [the asserted conclusion holds](goal). -/

lemma gaussianPropensityClamp_mem_Icc (r : ℝ) :
    gaussianPropensityClamp r ∈ Set.Icc (0 : ℝ) 1 := by
  simp [gaussianPropensityClamp]

/-- If [a real number and its unit-interval certificate](hyp:r,hr) are given,
[clamping that number to the unit interval leaves it unchanged](goal). -/
@[simp] lemma gaussianPropensityClamp_eq_self {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : gaussianPropensityClamp r = r := by
  simp [gaussianPropensityClamp, hr.1, hr.2]

/-- If a propensity is valid on the base law almost everywhere, clamping it
globally does not change the Gaussian completion bind. [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,hvalid), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_clamp_eq_of_ae {d : ℕ}
    (mu : Measure (Fin d → ℝ)) (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (hvalid : ∀ᵐ x ∂mu, e x ∈ Set.Icc (0 : ℝ) 1) :
    mu.bind (gaussianCompletionAt σ (gaussianPropensityClamp ∘ e) μ₀ μ₁) =
      mu.bind (gaussianCompletionAt σ e μ₀ μ₁) := by
  apply Measure.bind_congr_right
  filter_upwards [hvalid] with x hx
  unfold gaussianCompletionAt
  rw [show (gaussianPropensityClamp ∘ e) x = e x by
    exact gaussianPropensityClamp_eq_self hx]

/-- Independent Gaussian potential-outcome fibres make treatment conditionally
independent of the potential outcomes given covariates. [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_condExchangeable {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    [IsFiniteMeasure (mu.bind (gaussianCompletionAt σ e μ₀ μ₁))] :
    CondExchangeable (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)) := by
  let Pc := mu.bind (gaussianCompletionAt σ e μ₀ μ₁)
  let X : Completion d → (Fin d → ℝ) := fun ω => ω.1
  let Y : Completion d → (ℝ × ℝ) := fun ω => (ω.2.2.1, ω.2.2.2.1)
  let A : Completion d → Bool := fun ω => ω.2.1
  let kY : ProbabilityTheory.Kernel (Fin d → ℝ) (ℝ × ℝ) :=
    ProbabilityTheory.Kernel.mk (fun x =>
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))
      (gaussianPair_measurable σ μ₀ μ₁ hμ₀ hμ₁)
  let kAx : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  let kA : ProbabilityTheory.Kernel ((Fin d → ℝ) × (ℝ × ℝ)) Bool :=
    ProbabilityTheory.Kernel.mk (fun xy => realBernoulli (e xy.1))
      (by unfold realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kY := ⟨fun x => by
    letI : IsProbabilityMeasure
        (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    letI : IsProbabilityMeasure
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    change IsProbabilityMeasure
      ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))
    exact Measure.prod.instIsProbabilityMeasure _ _⟩
  letI : ProbabilityTheory.IsMarkovKernel kAx :=
    ⟨fun x => realBernoulli_probability (e x) (hvalid x)⟩
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun xy => realBernoulli_probability (e xy.1) (hvalid xy.1)⟩
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hcov : Pc.map X = mu := by
    dsimp [Pc, X]
    exact gaussianCompletionBind_covariate_marginal_ae mu σ e μ₀ μ₁
      he hμ₀ hμ₁ (Filter.Eventually.of_forall hvalid)
  have hYmap : Pc.map (fun ω => (X ω, Y ω)) = mu ⊗ₘ kY := by
    dsimp [Pc, X, Y, kY]
    exact gaussianCompletionBind_covariate_potential mu σ e μ₀ μ₁
      he hμ₀ hμ₁ hvalid
  have hAmap : Pc.map (fun ω => (X ω, A ω)) = mu ⊗ₘ kAx := by
    dsimp [Pc, X, A, kAx]
    exact gaussianCompletionBind_covariate_treatment mu σ e μ₀ μ₁
      he hμ₀ hμ₁ hvalid
  have hYcond : ProbabilityTheory.condDistrib Y X Pc =ᵐ[mu] kY := by
    have h := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := Pc) (X := X) (Y := Y) (κ := kY) hX hY
        (by simpa [hcov] using hYmap)
    simpa [hcov] using h
  have hAcond : ProbabilityTheory.condDistrib A X Pc =ᵐ[mu] kAx := by
    have h := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := Pc) (X := X) (Y := A) (κ := kAx) hX hA
        (by simpa [hcov] using hAmap)
    simpa [hcov] using h
  have hkprod : ProbabilityTheory.Kernel.compProd kY kA =
      ProbabilityTheory.Kernel.prod kY kAx := by
    ext x s hs
    rw [ProbabilityTheory.Kernel.compProd_apply hs,
      ProbabilityTheory.Kernel.prod_apply kY kAx x, Measure.prod_apply hs]
    rfl
  have hfactor : Pc.map (fun ω => (X ω, Y ω, A ω)) =
      mu ⊗ₘ ProbabilityTheory.Kernel.prod kY kAx := by
    dsimp [Pc, X, Y, A]
    rw [← hkprod]
    exact gaussianCompletionBind_potential_treatment_factorization
      mu σ e μ₀ μ₁ he hμ₀ hμ₁ hvalid
  unfold CondExchangeable
  change ProbabilityTheory.CondIndepFun (MeasurableSpace.comap X inferInstance)
    (Measurable.comap_le hX) Y A Pc
  apply (ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    hY hA hX).2
  rw [← Measure.compProd_eq_comp_prod, hcov]
  calc
    Pc.map (fun ω => (X ω, Y ω, A ω)) =
        mu ⊗ₘ ProbabilityTheory.Kernel.prod kY kAx := hfactor
    _ = mu ⊗ₘ ProbabilityTheory.Kernel.prod
          (ProbabilityTheory.condDistrib Y X Pc)
          (ProbabilityTheory.condDistrib A X Pc) := by
      symm
      apply Measure.compProd_congr
      filter_upwards [hYcond, hAcond] with x hxy hxa
      rw [ProbabilityTheory.Kernel.prod_apply
          (ProbabilityTheory.condDistrib Y X Pc)
          (ProbabilityTheory.condDistrib A X Pc) x,
        ProbabilityTheory.Kernel.prod_apply kY kAx x, hxy, hxa]

/-- [For the stated inputs and conditions](hyp:d,σ,e,μ₀,μ₁,x,he), [the asserted conclusion holds](goal). -/

lemma gaussianCompletionAt_treatedPotential {d : ℕ} (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc (0 : ℝ) 1) :
    (gaussianCompletionAt σ e μ₀ μ₁ x).map
        (fun ω => (ω.1, ω.2.2.2.1)) =
      (Measure.dirac x).prod
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) := by
  letI := realBernoulli_probability (e x) he
  letI : IsProbabilityMeasure
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  letI : IsProbabilityMeasure
      (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  unfold gaussianCompletionAt
  rw [Measure.map_map (by fun_prop) (by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)), Measure.dirac_prod]
  calc
    Measure.map (fun z : Bool × (ℝ × ℝ) => (x, z.2.2))
        ((realBernoulli (e x)).prod
          ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
            (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))) =
      Measure.map (Prod.mk x)
        (Measure.map (fun z : Bool × (ℝ × ℝ) => z.2.2)
          ((realBernoulli (e x)).prod
            ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
              (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)))) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
    _ = _ := by
      rw [show (fun z : Bool × (ℝ × ℝ) => z.2.2) =
          Prod.snd ∘ Prod.snd by rfl]
      rw [← Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_snd_prod, measure_univ, one_smul,
        Measure.map_snd_prod, measure_univ, one_smul]

/-- [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid), [the asserted conclusion holds](goal). -/

lemma gaussianCompletionBind_treatedPotential {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1) :
    let k₁ : ProbabilityTheory.Kernel (Fin d → ℝ) ℝ :=
      ProbabilityTheory.Kernel.mk (fun x =>
        gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)
        (ProbabilityTheory.measurable_gaussianReal.comp
          (hμ₁.prodMk measurable_const))
    (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map
        (fun ω => (ω.1, ω.2.2.2.1)) = mu ⊗ₘ k₁ := by
  dsimp
  let k₁ : ProbabilityTheory.Kernel (Fin d → ℝ) ℝ :=
    ProbabilityTheory.Kernel.mk (fun x =>
      gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)
      (ProbabilityTheory.measurable_gaussianReal.comp
        (hμ₁.prodMk measurable_const))
  letI : ProbabilityTheory.IsMarkovKernel k₁ :=
    ⟨fun x => ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
  have hk := gaussianCompletionAt_measurable σ e μ₀ μ₁ he hμ₀ hμ₁
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.bind_apply (hs.preimage (by fun_prop)) hk.aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  letI : IsProbabilityMeasure
      (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have hfix := gaussianCompletionAt_treatedPotential σ e μ₀ μ₁ x (hvalid x)
  have happ := congrArg (fun m : Measure ((Fin d → ℝ) × ℝ) => m s) hfix
  rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply hs,
    lintegral_dirac] at happ
  change (gaussianCompletionAt σ e μ₀ μ₁ x)
      ((fun ω => (ω.1, ω.2.2.2.1)) ⁻¹' s) =
    (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) (Prod.mk x ⁻¹' s)
  exact happ

/-- Translating a centred Gaussian bounds its first absolute moment by the
absolute mean plus the centred first absolute moment. [For the stated inputs and conditions](hyp:m,σ), [the asserted conclusion holds](goal). -/
lemma gaussianReal_integral_abs_le (m σ : ℝ) :
    (∫ y : ℝ, |y| ∂gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩) ≤
      |m| + ∫ z : ℝ, |z| ∂gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ := by
  let v : NNReal := ⟨σ ^ 2, sq_nonneg σ⟩
  letI : IsProbabilityMeasure (gaussianReal 0 v) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have hshift : (gaussianReal 0 v).map (fun z : ℝ => z + m) =
      gaussianReal m v := by
    simpa using ProbabilityTheory.gaussianReal_map_add_const
      (μ := (0 : ℝ)) (v := v) m
  have hzero : Integrable (fun z : ℝ => |z|) (gaussianReal 0 v) :=
    (ProbabilityTheory.memLp_id_gaussianReal' 1 (by simp)).integrable (by norm_num) |>.abs
  have hadd : Integrable (fun z : ℝ => |z| + |m|) (gaussianReal 0 v) :=
    hzero.add (integrable_const |m|)
  have hshifted : Integrable (fun z : ℝ => |z + m|) (gaussianReal 0 v) :=
    hadd.mono' (by fun_prop) (Filter.Eventually.of_forall (fun z => by
      simpa [abs_of_nonneg (abs_nonneg (z + m))] using abs_add_le z m))
  rw [← hshift, integral_map (by fun_prop) (by fun_prop)]
  calc
    (∫ z : ℝ, |z + m| ∂gaussianReal 0 v) ≤
        ∫ z : ℝ, |z| + |m| ∂gaussianReal 0 v :=
      integral_mono hshifted hadd (fun z => abs_add_le z m)
    _ = (∫ z : ℝ, |z| ∂gaussianReal 0 v) +
        ∫ _ : ℝ, |m| ∂gaussianReal 0 v :=
      integral_add hzero (integrable_const |m|)
    _ = _ := by simp [v, add_comm]

/-- An integrable Gaussian mean over a finite base law makes the treated
potential outcome integrable under the completion bind. [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid,hμ₁int), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_treatedPotential_integrable {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [IsFiniteMeasure mu] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hμ₁int : Integrable μ₁ mu) :
    Integrable (fun ω : Completion d => ω.2.2.2.1)
      (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)) := by
  let k₁ : ProbabilityTheory.Kernel (Fin d → ℝ) ℝ :=
    ProbabilityTheory.Kernel.mk (fun x =>
      gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)
      (ProbabilityTheory.measurable_gaussianReal.comp
        (hμ₁.prodMk measurable_const))
  letI : ProbabilityTheory.IsMarkovKernel k₁ :=
    ⟨fun x => ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
  let cσ : ℝ := ∫ z : ℝ, |z| ∂gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩
  have hcσ : 0 ≤ cσ := integral_nonneg (fun _ => abs_nonneg _)
  have hg_meas : StronglyMeasurable (fun x =>
      ∫ y : ℝ, |y| ∂k₁ x) := by
    exact (by fun_prop : StronglyMeasurable (fun y : ℝ => |y|)).integral_kernel
  have hdom : Integrable (fun x => |μ₁ x| + cσ) mu :=
    hμ₁int.abs.add (integrable_const cσ)
  have hg_int : Integrable (fun x => ∫ y : ℝ, |y| ∂k₁ x) mu := by
    apply hdom.mono hg_meas.aestronglyMeasurable
    filter_upwards [] with x
    have hg0 : 0 ≤ ∫ y : ℝ, |y| ∂k₁ x :=
      integral_nonneg (fun _ => abs_nonneg _)
    have hdom0 : 0 ≤ |μ₁ x| + cσ := add_nonneg (abs_nonneg _) hcσ
    change ‖∫ y : ℝ, |y| ∂gaussianReal (μ₁ x)
      ⟨σ ^ 2, sq_nonneg σ⟩‖ ≤ ‖|μ₁ x| + cσ‖
    have hg0' : 0 ≤ ∫ y : ℝ, |y| ∂gaussianReal (μ₁ x)
        ⟨σ ^ 2, sq_nonneg σ⟩ := integral_nonneg (fun _ => abs_nonneg _)
    change |∫ y : ℝ, |y| ∂gaussianReal (μ₁ x)
      ⟨σ ^ 2, sq_nonneg σ⟩| ≤ abs (|μ₁ x| + cσ)
    rw [abs_of_nonneg hg0', abs_of_nonneg hdom0]
    exact gaussianReal_integral_abs_le (μ₁ x) σ
  have hcomp : Integrable (fun xy : (Fin d → ℝ) × ℝ => xy.2) (mu ⊗ₘ k₁) := by
    apply (Measure.integrable_compProd_iff (by fun_prop)).2
    constructor
    · filter_upwards [] with x
      change Integrable (fun y : ℝ => y)
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)
      exact (ProbabilityTheory.memLp_id_gaussianReal' 1 (by simp)).integrable
        (by norm_num)
    · simpa [k₁, Real.norm_eq_abs] using hg_int
  have hjoint := gaussianCompletionBind_treatedPotential mu σ e μ₀ μ₁
    he hμ₀ hμ₁ hvalid
  have hmap : Integrable Prod.snd
      ((mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map
        (fun ω => (ω.1, ω.2.2.2.1))) := by
    rw [hjoint]
    exact hcomp
  exact (integrable_map_measure
    (μ := mu.bind (gaussianCompletionAt σ e μ₀ μ₁))
    (f := fun ω : Completion d => (ω.1, ω.2.2.2.1))
    (g := Prod.snd) (by fun_prop) (by fun_prop)).mp hmap

/-- Once integrability is supplied, the Gaussian treated-arm mean is the
conditional treated-potential response of the product completion. [For the stated inputs and conditions](hyp:d,mu,σ,β,L,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid,hball,hYint), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_holderResponse {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (σ β L : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    [IsFiniteMeasure (mu.bind (gaussianCompletionAt σ e μ₀ μ₁))]
    (hball : HolderBall β L μ₁)
    (hYint : Integrable (fun ω : Completion d => ω.2.2.2.1)
      (mu.bind (gaussianCompletionAt σ e μ₀ μ₁))) :
    HolderResponse (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)) μ₁ β L := by
  let Pc := mu.bind (gaussianCompletionAt σ e μ₀ μ₁)
  let X : Completion d → (Fin d → ℝ) := fun ω => ω.1
  let Y₁ : Completion d → ℝ := fun ω => ω.2.2.2.1
  let k₁ : ProbabilityTheory.Kernel (Fin d → ℝ) ℝ :=
    ProbabilityTheory.Kernel.mk (fun x =>
      gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)
      (ProbabilityTheory.measurable_gaussianReal.comp
        (hμ₁.prodMk measurable_const))
  letI : ProbabilityTheory.IsMarkovKernel k₁ :=
    ⟨fun x => ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hY₁ : Measurable Y₁ := by dsimp [Y₁]; fun_prop
  have hcov : Pc.map X = mu := by
    dsimp [Pc, X]
    exact gaussianCompletionBind_covariate_marginal_ae mu σ e μ₀ μ₁
      he hμ₀ hμ₁ (Filter.Eventually.of_forall hvalid)
  have hjoint : Pc.map (fun ω => (X ω, Y₁ ω)) = mu ⊗ₘ k₁ := by
    dsimp [Pc, X, Y₁, k₁]
    exact gaussianCompletionBind_treatedPotential mu σ e μ₀ μ₁
      he hμ₀ hμ₁ hvalid
  have hcond : ProbabilityTheory.condDistrib Y₁ X Pc =ᵐ[mu] k₁ := by
    have h := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := Pc) (X := X) (Y := Y₁) (κ := k₁) hX hY₁
        (by simpa [hcov] using hjoint)
    simpa [hcov] using h
  have hce : Pc[Y₁ | MeasurableSpace.comap X inferInstance] =ᵐ[Pc]
      fun ω => ∫ y : ℝ, y ∂ProbabilityTheory.condDistrib Y₁ X Pc (X ω) := by
    simpa [Pc, Y₁] using
      ProbabilityTheory.condExp_ae_eq_integral_condDistrib' hX hYint
  have hkernel : ∀ᵐ ω ∂Pc,
      ProbabilityTheory.condDistrib Y₁ X Pc (X ω) = k₁ (X ω) := by
    have hcond' : ProbabilityTheory.condDistrib Y₁ X Pc =ᵐ[Pc.map X] k₁ := by
      rw [hcov]
      exact hcond
    exact ae_eq_comp hX.aemeasurable hcond'
  have hmean : (fun ω : Completion d =>
      ∫ y : ℝ, y ∂ProbabilityTheory.condDistrib Y₁ X Pc (X ω)) =ᵐ[Pc]
      fun ω => μ₁ (X ω) := by
    filter_upwards [hkernel] with ω hω
    rw [hω]
    exact ProbabilityTheory.integral_id_gaussianReal
  refine ⟨hball, ?_⟩
  exact hmean.symm.trans hce.symm

/-- Practical Gaussian Holder-response assembly from an integrable mean. [For the stated inputs and conditions](hyp:d,mu,σ,β,L,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid,hball,hμ₁int), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_holderResponse_of_integrable_mean {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [IsFiniteMeasure mu] (σ β L : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    [IsFiniteMeasure (mu.bind (gaussianCompletionAt σ e μ₀ μ₁))]
    (hball : HolderBall β L μ₁) (hμ₁int : Integrable μ₁ mu) :
    HolderResponse (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)) μ₁ β L :=
  gaussianCompletionBind_holderResponse mu σ β L e μ₀ μ₁ he hμ₀ hμ₁
    hvalid hball
    (gaussianCompletionBind_treatedPotential_integrable mu σ e μ₀ μ₁
      he hμ₀ hμ₁ hvalid hμ₁int)

/-- The conditional-mean component of the Gaussian completion, separated
from any regularity property of its representative. [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid,hYint), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_treatedConditionalMean {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    [IsFiniteMeasure (mu.bind (gaussianCompletionAt σ e μ₀ μ₁))]
    (hYint : Integrable (fun ω : Completion d => ω.2.2.2.1)
      (mu.bind (gaussianCompletionAt σ e μ₀ μ₁))) :
    (fun ω : Completion d => μ₁ ω.1) =ᵐ[
      mu.bind (gaussianCompletionAt σ e μ₀ μ₁)]
      (mu.bind (gaussianCompletionAt σ e μ₀ μ₁))[
        (fun ω : Completion d => ω.2.2.2.1) |
          MeasurableSpace.comap (fun ω => ω.1) inferInstance] := by
  -- The proof of `gaussianCompletionBind_holderResponse` uses the Holder
  -- premise only when pairing this identity with its regularity field.
  let Pc := mu.bind (gaussianCompletionAt σ e μ₀ μ₁)
  let X : Completion d → (Fin d → ℝ) := fun ω => ω.1
  let Y₁ : Completion d → ℝ := fun ω => ω.2.2.2.1
  let k₁ : ProbabilityTheory.Kernel (Fin d → ℝ) ℝ :=
    ProbabilityTheory.Kernel.mk (fun x =>
      gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)
      (ProbabilityTheory.measurable_gaussianReal.comp
        (hμ₁.prodMk measurable_const))
  letI : ProbabilityTheory.IsMarkovKernel k₁ :=
    ⟨fun x => ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hY₁ : Measurable Y₁ := by dsimp [Y₁]; fun_prop
  have hcov : Pc.map X = mu := by
    dsimp [Pc, X]
    exact gaussianCompletionBind_covariate_marginal_ae mu σ e μ₀ μ₁
      he hμ₀ hμ₁ (Filter.Eventually.of_forall hvalid)
  have hjoint : Pc.map (fun ω => (X ω, Y₁ ω)) = mu ⊗ₘ k₁ := by
    dsimp [Pc, X, Y₁, k₁]
    exact gaussianCompletionBind_treatedPotential mu σ e μ₀ μ₁
      he hμ₀ hμ₁ hvalid
  have hcond : ProbabilityTheory.condDistrib Y₁ X Pc =ᵐ[mu] k₁ := by
    have h := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := Pc) (X := X) (Y := Y₁) (κ := k₁) hX hY₁
        (by simpa [hcov] using hjoint)
    simpa [hcov] using h
  have hce : Pc[Y₁ | MeasurableSpace.comap X inferInstance] =ᵐ[Pc]
      fun ω => ∫ y : ℝ, y ∂ProbabilityTheory.condDistrib Y₁ X Pc (X ω) := by
    simpa [Pc, Y₁] using
      ProbabilityTheory.condExp_ae_eq_integral_condDistrib' hX hYint
  have hkernel : ∀ᵐ ω ∂Pc,
      ProbabilityTheory.condDistrib Y₁ X Pc (X ω) = k₁ (X ω) := by
    have hcond' : ProbabilityTheory.condDistrib Y₁ X Pc =ᵐ[Pc.map X] k₁ := by
      rw [hcov]
      exact hcond
    exact ae_eq_comp hX.aemeasurable hcond'
  filter_upwards [hkernel, hce] with ω hk hceω
  rw [hceω, hk]
  exact ProbabilityTheory.integral_id_gaussianReal.symm

/-- Changing only the covariate coordinate preserves consistency. [For the stated inputs and conditions](hyp:d,Pc,hPc), [the asserted conclusion holds](goal). -/
lemma affineCompletionMap_consistency {d : ℕ} (Pc : Measure (Completion d))
    (hPc : OutcomeConsistency Pc) :
    OutcomeConsistency (Pc.map (fun ω : Completion d =>
      (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1,
        ω.2.2.2.2))) := by
  let F : Completion d → Completion d := fun ω =>
    (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2)
  have hF : Measurable F := by
    dsimp [F]
    have hx : Measurable (fun ω : Completion d => affineToCube ω.1) :=
      affineToCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)
  let S : Set (Completion d) :=
    {ω | ω.2.2.2.2 = if ω.2.1 then ω.2.2.2.1 else ω.2.2.1}
  have hsel : Measurable (fun ω : Completion d =>
      if ω.2.1 then ω.2.2.2.1 else ω.2.2.1) := by
    apply Measurable.ite
      (by measurability : MeasurableSet {ω : Completion d | ω.2.1 = true})
      (by fun_prop) (by fun_prop)
  have hS : MeasurableSet S :=
    measurableSet_eq_fun (by fun_prop) hsel
  unfold OutcomeConsistency at hPc ⊢
  apply (ae_map_iff hF.aemeasurable hS).2
  simpa only [F, S, Set.mem_ofPred_eq] using hPc

/-- An invertible measurable affine change of the covariate coordinate
preserves conditional exchangeability. [For the stated inputs and conditions](hyp:d,Pc,hPc), [the asserted conclusion holds](goal). -/
lemma affineCompletionMap_condExchangeable {d : ℕ}
    (Pc : Measure (Completion d)) [IsFiniteMeasure Pc]
    [IsFiniteMeasure (Pc.map (fun ω : Completion d =>
      (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1,
        ω.2.2.2.2)))]
    (hPc : CondExchangeable Pc) :
    CondExchangeable (Pc.map (fun ω : Completion d =>
      (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1,
        ω.2.2.2.2))) := by
  let F : Completion d → Completion d := fun ω =>
    (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2)
  have hF : Measurable F := by
    dsimp [F]
    have hx : Measurable (fun ω : Completion d => affineToCube ω.1) :=
      affineToCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)
  unfold CondExchangeable at hPc ⊢
  apply Causalean.Mathlib.Probability.Independence.Conditional.condIndepFun_of_map
    (hφ := hF) (hX := by fun_prop) (hY := by fun_prop) (hZ := by fun_prop)
  change ProbabilityTheory.CondIndepFun
    (MeasurableSpace.comap
      (affineToCube ∘ (fun ω : Completion d => ω.1)) inferInstance)
    _ (fun ω : Completion d => (ω.2.2.1, ω.2.2.2.1))
    (fun ω : Completion d => ω.2.1) Pc
  refine condIndepFun_congr_conditioning
    (B := ℝ × ℝ) (C := Bool)
    (m₁ := MeasurableSpace.comap (fun ω : Completion d => ω.1)
      inferInstance)
    (m₂ := MeasurableSpace.comap
      (affineToCube ∘ (fun ω : Completion d => ω.1)) inferInstance)
    (affineToCube_comap_eq (fun ω : Completion d => ω.1)).symm _ _
    (fun ω : Completion d => (ω.2.2.1, ω.2.2.2.1))
    (fun ω : Completion d => ω.2.1) (mu := Pc) hPc

/-- Affine covariate transport preserves the treated-potential conditional
mean identity, independently of the chosen regularity representative. [For the stated inputs and conditions](hyp:d,Pc,mu₁,hsource,hYint), [the asserted conclusion holds](goal). -/
lemma affineCompletionMap_treatedConditionalMean {d : ℕ}
    (Pc : Measure (Completion d)) [IsFiniteMeasure Pc]
    [IsFiniteMeasure (Pc.map (fun ω : Completion d =>
      (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1,
        ω.2.2.2.2)))]
    (mu₁ : (Fin d → ℝ) → ℝ)
    (hsource : (fun ω : Completion d => mu₁ ω.1) =ᵐ[Pc]
      Pc[(fun ω : Completion d => ω.2.2.2.1) |
        MeasurableSpace.comap (fun ω => ω.1) inferInstance])
    (hYint : Integrable (fun ω : Completion d => ω.2.2.2.1) Pc) :
    (fun ω : Completion d => transformedResponse mu₁ ω.1) =ᵐ[
      Pc.map (fun ω : Completion d =>
        (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1,
          ω.2.2.2.2))]
      (Pc.map (fun ω : Completion d =>
        (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1,
          ω.2.2.2.2)))[(fun ω : Completion d => ω.2.2.2.1) |
            MeasurableSpace.comap (fun ω => ω.1) inferInstance] := by
  let F : Completion d → Completion d := fun ω =>
    (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2)
  let G : Completion d → Completion d := fun ω =>
    ((fun i => 2 * ω.1 i - 1), ω.2.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2)
  have hF : Measurable F := by
    dsimp [F]
    have hx : Measurable (fun ω : Completion d => affineToCube ω.1) :=
      affineToCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)
  have hG : Measurable G := by
    dsimp [G]
    have hx : Measurable (fun ω : Completion d => fun i => 2 * ω.1 i - 1) :=
      affineFromCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)
  have hmapG : (Pc.map F).map G = Pc := by
    rw [Measure.map_map hG hF]
    have hGF : G ∘ F = id := by
      funext ω
      simp only [Function.comp_apply, F, G, id_eq, affineToCube_inverse]
    rw [hGF, Measure.map_id]
  have hFG : F ∘ G = id := by
    funext ω
    simp only [Function.comp_apply, F, G, id_eq, affineToCube_affineFromCube]
  let Y₁ : Completion d → ℝ := fun ω => ω.2.2.2.1
  let X : Completion d → (Fin d → ℝ) := fun ω => ω.1
  have hmX : MeasurableSpace.comap X
      (inferInstance : MeasurableSpace (Fin d → ℝ)) ≤
      (inferInstance : MeasurableSpace (Completion d)) := by
    exact Measurable.comap_le (by dsimp [X]; fun_prop)
  have hYint' : Integrable Y₁ (Pc.map F) := by
    apply (integrable_map_measure (by dsimp [Y₁]; fun_prop)
      hF.aemeasurable).2
    exact hYint
  have hmPull : MeasurableSpace.comap F
      (MeasurableSpace.comap X
        (inferInstance : MeasurableSpace (Fin d → ℝ))) =
      MeasurableSpace.comap (fun ω : Completion d => ω.1) inferInstance := by
    calc
      _ = MeasurableSpace.comap (X ∘ F) inferInstance :=
        MeasurableSpace.comap_comp
      _ = MeasurableSpace.comap
          (affineToCube ∘ (fun ω : Completion d => ω.1)) inferInstance := by rfl
      _ = _ := affineToCube_comap_eq _
  have hcond :=
    Causalean.Mathlib.Probability.Independence.Conditional.Transport.condExp_comp_of_map_eq
      F hF (show Pc.map F = Pc.map F from rfl)
      (MeasurableSpace.comap X inferInstance) hmX hYint'
  have hcond' :
      Pc[Y₁ | MeasurableSpace.comap (fun ω : Completion d => ω.1)
        inferInstance] =ᵐ[Pc]
        (Pc.map F)[Y₁ | MeasurableSpace.comap X inferInstance] ∘ F := by
    exact (condExp_congr_conditioning hmPull.symm Pc Y₁).trans hcond
  apply Causalean.Mathlib.Probability.Independence.Conditional.Transport.eventuallyEq_of_comp_aeRetraction
    F G hG hmapG (Filter.Eventually.of_forall fun ω => congrFun hFG ω)
  change (fun ω : Completion d => transformedResponse mu₁ ω.1) ∘ F =ᵐ[Pc]
    ((Pc.map F)[Y₁ | MeasurableSpace.comap X inferInstance]) ∘ F
  calc
    _ = fun ω : Completion d => mu₁ ω.1 := by
      funext ω
      exact transformedResponse_affineToCube mu₁ ω.1
    _ =ᵐ[Pc] Pc[Y₁ | MeasurableSpace.comap
          (fun ω : Completion d => ω.1) inferInstance] := hsource
    _ =ᵐ[Pc] _ := hcond'

/-- An affine covariate pushforward transports a potential-outcome conditional
mean once the transformed representative has the requested Holder bound. [For the stated inputs and conditions](hyp:d,Pc,mu₁,beta,L,hsource,hball,hYint), [the asserted conclusion holds](goal). -/
lemma affineCompletionMap_holderResponse {d : ℕ}
    (Pc : Measure (Completion d)) [IsFiniteMeasure Pc]
    [IsFiniteMeasure (Pc.map (fun ω : Completion d =>
      (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1,
        ω.2.2.2.2)))]
    (mu₁ : (Fin d → ℝ) → ℝ) (beta L : ℝ)
    (hsource : HolderResponse Pc mu₁ beta L)
    (hball : HolderBall beta L (transformedResponse mu₁))
    (hYint : Integrable (fun ω : Completion d => ω.2.2.2.1) Pc) :
    HolderResponse (Pc.map (fun ω : Completion d =>
      (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1,
        ω.2.2.2.2))) (transformedResponse mu₁) beta L := by
  let F : Completion d → Completion d := fun ω =>
    (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2)
  let G : Completion d → Completion d := fun ω =>
    ((fun i => 2 * ω.1 i - 1), ω.2.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2)
  have hF : Measurable F := by
    dsimp [F]
    have hx : Measurable (fun ω : Completion d => affineToCube ω.1) :=
      affineToCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)
  have hG : Measurable G := by
    dsimp [G]
    have hx : Measurable
        (fun ω : Completion d => fun i => 2 * ω.1 i - 1) :=
      affineFromCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)
  have hmapG : (Pc.map F).map G = Pc := by
    rw [Measure.map_map hG hF]
    have hGF : G ∘ F = id := by
      funext ω
      simp only [Function.comp_apply, F, G, id_eq, affineToCube_inverse]
    rw [hGF, Measure.map_id]
  have hFG : F ∘ G = id := by
    funext ω
    simp only [Function.comp_apply, F, G, id_eq, affineToCube_affineFromCube]
  let Y₁ : Completion d → ℝ := fun ω => ω.2.2.2.1
  let X : Completion d → (Fin d → ℝ) := fun ω => ω.1
  have hmX : MeasurableSpace.comap X
      (inferInstance : MeasurableSpace (Fin d → ℝ)) ≤
      (inferInstance : MeasurableSpace (Completion d)) := by
    exact Measurable.comap_le (by dsimp [X]; fun_prop)
  have hYint' : Integrable Y₁ (Pc.map F) := by
    apply (integrable_map_measure (by dsimp [Y₁]; fun_prop)
      hF.aemeasurable).2
    change Integrable (fun ω : Completion d => ω.2.2.2.1) Pc
    exact hYint
  have hmPull : MeasurableSpace.comap F
      (MeasurableSpace.comap X
        (inferInstance : MeasurableSpace (Fin d → ℝ))) =
      MeasurableSpace.comap (fun ω : Completion d => ω.1) inferInstance := by
    calc
      MeasurableSpace.comap F (MeasurableSpace.comap X inferInstance) =
          MeasurableSpace.comap (X ∘ F) inferInstance := by
            exact MeasurableSpace.comap_comp
      _ = MeasurableSpace.comap
          (affineToCube ∘ (fun ω : Completion d => ω.1)) inferInstance := by rfl
      _ = MeasurableSpace.comap (fun ω : Completion d => ω.1)
          inferInstance := affineToCube_comap_eq _
  have hcond :=
    Causalean.Mathlib.Probability.Independence.Conditional.Transport.condExp_comp_of_map_eq
      F hF (show Pc.map F = Pc.map F from rfl)
      (MeasurableSpace.comap X inferInstance) hmX hYint'
  have hcond' :
      Pc[Y₁ | MeasurableSpace.comap (fun ω : Completion d => ω.1)
        inferInstance] =ᵐ[Pc]
        (Pc.map F)[Y₁ | MeasurableSpace.comap X inferInstance] ∘ F := by
    exact (condExp_congr_conditioning hmPull.symm Pc Y₁).trans hcond
  refine ⟨hball, ?_⟩
  apply Causalean.Mathlib.Probability.Independence.Conditional.Transport.eventuallyEq_of_comp_aeRetraction
    F G hG hmapG (Filter.Eventually.of_forall fun ω => congrFun hFG ω)
  have hsourceMean := hsource.2
  change (fun ω : Completion d => transformedResponse mu₁ ω.1) ∘ F =ᵐ[Pc]
    ((Pc.map F)[Y₁ | MeasurableSpace.comap X inferInstance]) ∘ F
  calc
    (fun ω : Completion d => transformedResponse mu₁ ω.1) ∘ F
        = fun ω : Completion d => mu₁ ω.1 := by
          funext ω
          exact transformedResponse_affineToCube mu₁ ω.1
    _ =ᵐ[Pc] Pc[Y₁ | MeasurableSpace.comap
          (fun ω : Completion d => ω.1) inferInstance] := by
      simpa only [Y₁] using hsourceMean
    _ =ᵐ[Pc] ((Pc.map F)[Y₁ | MeasurableSpace.comap X inferInstance]) ∘ F := hcond'

/-- For [the stated dimension, Gaussian scale, response functions, measurability
certificates, and covariate](hyp:d,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,x), [the Gaussian
completion kernel evaluates to the corresponding pointwise completion](goal). -/
@[simp] lemma gaussianCompletionKernel_apply {d : ℕ} (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (x : Fin d → ℝ) :
    gaussianCompletionKernel σ e μ₀ μ₁ he hμ₀ hμ₁ x =
      gaussianCompletionAt σ e μ₀ μ₁ x := rfl

/-- At fixed covariates, observing the independent Gaussian completion selects
the Gaussian response belonging to the realized treatment arm. [For the stated inputs and conditions](hyp:d,σ,e,μ₀,μ₁,x,he), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionAt_observed_map {d : ℕ} (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc (0 : ℝ) 1) :
    (gaussianCompletionAt σ e μ₀ μ₁ x).map observed =
      ENNReal.ofReal (1 - e x) •
          ((Measure.dirac x).prod ((Measure.dirac false).prod
            (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩))) +
        ENNReal.ofReal (e x) •
          ((Measure.dirac x).prod ((Measure.dirac true).prod
            (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))) := by
  letI := realBernoulli_probability (e x) he
  letI : IsProbabilityMeasure
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  letI : IsProbabilityMeasure
      (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  unfold gaussianCompletionAt
  rw [Measure.map_map (by unfold observed; fun_prop) (by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption))]
  rw [Measure.dirac_prod]
  let g : Bool × ℝ × ℝ → Obs d :=
    fun z => (x, z.1, if z.1 then z.2.2 else z.2.1)
  change Measure.map g ((realBernoulli (e x)).prod
      ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩))) = _
  have hg : Measurable g := by
    dsimp [g]
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  unfold realBernoulli
  rw [Measure.add_prod, Measure.map_add _ _ hg]
  congr 1
  · rw [Measure.prod_smul_left, Measure.map_smul]
    congr 1
    rw [Measure.dirac_prod, Measure.map_map hg (by fun_prop)]
    change Measure.map ((fun y : ℝ => (x, false, y)) ∘ Prod.fst)
      ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)) = _
    rw [← Measure.map_map (by fun_prop : Measurable
      (fun y : ℝ => (x, false, y))) measurable_fst, Measure.map_fst_prod]
    simp only [measure_univ, one_smul]
    rw [Measure.dirac_prod (x := false), Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · rw [Measure.prod_smul_left, Measure.map_smul]
    congr 1
    rw [Measure.dirac_prod, Measure.map_map hg (by fun_prop)]
    change Measure.map ((fun y : ℝ => (x, true, y)) ∘ Prod.snd)
      ((gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).prod
        (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩)) = _
    rw [← Measure.map_map (by fun_prop : Measurable
      (fun y : ℝ => (x, true, y))) measurable_snd, Measure.map_snd_prod]
    simp only [measure_univ, one_smul]
    rw [Measure.dirac_prod (x := true), Measure.dirac_prod x,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

/-- Fixed-covariate Gaussian completion agrees with a treatment Bernoulli
followed by the selected Gaussian arm kernel. [For the stated inputs and conditions](hyp:d,σ,e,μ₀,μ₁,x,he), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionAt_observed_compProd {d : ℕ} (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc (0 : ℝ) 1) :
    let kY : ProbabilityTheory.Kernel Bool ℝ :=
      ProbabilityTheory.Kernel.mk (fun a => if a then
          gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩
        else gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩)
        (measurable_of_finite _)
    (gaussianCompletionAt σ e μ₀ μ₁ x).map observed =
      (Measure.compProd (realBernoulli (e x)) kY).map
        (fun ay => (x, ay.1, ay.2)) := by
  dsimp
  letI : IsProbabilityMeasure
      (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  letI : IsProbabilityMeasure
      (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  let kY : ProbabilityTheory.Kernel Bool ℝ :=
    ProbabilityTheory.Kernel.mk (fun a => if a then
        gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩
      else gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩)
      (measurable_of_finite _)
  letI : ProbabilityTheory.IsMarkovKernel kY := ⟨fun a => by
    change IsProbabilityMeasure (if a then
      gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩
    else gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩)
    cases a <;> exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
  rw [gaussianCompletionAt_observed_map σ e μ₀ μ₁ x he]
  have hsource : Measure.compProd (realBernoulli (e x)) kY =
      ENNReal.ofReal (1 - e x) •
          (gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩).map (Prod.mk false) +
        ENNReal.ofReal (e x) •
          (gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩).map (Prod.mk true) := by
    unfold realBernoulli
    rw [Measure.compProd_add_left, Measure.compProd_smul_left,
      Measure.compProd_smul_left,
      dirac_compProd_eq_map_prodMk false kY,
      dirac_compProd_eq_map_prodMk true kY]
    rfl
  rw [hsource, Measure.map_add _ _ (by fun_prop),
    Measure.map_smul, Measure.map_smul]
  congr 1
  · rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.dirac_prod, Measure.dirac_prod,
      Measure.map_map (by fun_prop) (by fun_prop)]
  · rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.dirac_prod, Measure.dirac_prod,
      Measure.map_map (by fun_prop) (by fun_prop)]

/-- Binding the Gaussian completion over a covariate law produces the usual
two-stage treatment and selected-arm Gaussian observed law. [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,he01), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_observed {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1) :
    let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
      ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
        (by unfold realBernoulli; fun_prop)
    let kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ :=
      ProbabilityTheory.Kernel.mk (fun xa => if xa.2 then
          gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
        else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
        (by
          apply Measurable.ite (measurable_snd (MeasurableSet.singleton true))
          · fun_prop
          · fun_prop)
    (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map observed =
      ((mu ⊗ₘ kA) ⊗ₘ kY).map (fun z => (z.1.1, z.1.2, z.2)) := by
  dsimp
  let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  let kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ :=
    ProbabilityTheory.Kernel.mk (fun xa => if xa.2 then
        gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
      else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
      (by
        apply Measurable.ite (measurable_snd (MeasurableSet.singleton true))
        · fun_prop
        · fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun x => realBernoulli_probability (e x) (he01 x)⟩
  letI : ProbabilityTheory.IsMarkovKernel kY :=
    ⟨fun xa => by
      change IsProbabilityMeasure (if xa.2 then
        gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
      else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
      cases xa.2 <;>
        exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
  have hk := gaussianCompletionAt_measurable σ e μ₀ μ₁ he hμ₀ hμ₁
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by unfold observed; fun_prop) hs,
    Measure.bind_apply (hs.preimage (by unfold observed; fun_prop)) hk.aemeasurable,
    Measure.map_apply (by fun_prop) hs,
    Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.lintegral_compProd]
  swap
  · exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
      (hs.preimage (by fun_prop))
  apply lintegral_congr
  intro x
  let kYx : ProbabilityTheory.Kernel Bool ℝ :=
    ProbabilityTheory.Kernel.mk (fun a => if a then
        gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩
      else gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩)
      (measurable_of_finite _)
  letI : ProbabilityTheory.IsMarkovKernel kYx := ⟨fun a => by
    change IsProbabilityMeasure (if a then
      gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩
    else gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩)
    cases a <;> exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
  have hfix := gaussianCompletionAt_observed_compProd σ e μ₀ μ₁ x (he01 x)
  change (gaussianCompletionAt σ e μ₀ μ₁ x).map observed =
    (Measure.compProd (realBernoulli (e x)) kYx).map
      (fun ay => (x, ay.1, ay.2)) at hfix
  have happ := congrArg (fun m : Measure (Obs d) => m s) hfix
  rw [Measure.map_apply (by unfold observed; fun_prop) hs] at happ
  rw [Measure.map_apply (by fun_prop) hs] at happ
  rw [Measure.compProd_apply (hs.preimage (by fun_prop))] at happ
  rw [happ]
  apply lintegral_congr
  intro b
  change (if b then
      gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩
    else gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩)
      ((fun y => (x, b, y)) ⁻¹' s) = _
  rfl

/-- The observed response kernel of a Gaussian completion is the selected
Gaussian arm kernel. [For the stated inputs and conditions](hyp:d,mu,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,hvalid), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_observedKernel_ae {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (hvalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    [IsFiniteMeasure
      ((mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map observed)] :
    let P := (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map observed
    let kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ :=
      ProbabilityTheory.Kernel.mk (fun xa => if xa.2 then
          gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
        else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
        (by
          apply Measurable.ite (measurable_snd (MeasurableSet.singleton true))
          · fun_prop
          · fun_prop)
    ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
      (fun z : Obs d => (z.1, z.2.1)) P =ᵐ[
        P.map (fun z => (z.1, z.2.1))] kY := by
  dsimp
  let P := (mu.bind (gaussianCompletionAt σ e μ₀ μ₁)).map observed
  let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  let kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ :=
    ProbabilityTheory.Kernel.mk (fun xa => if xa.2 then
        gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
      else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
      (by
        apply Measurable.ite (measurable_snd (MeasurableSet.singleton true))
        · fun_prop
        · fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun x => realBernoulli_probability (e x) (hvalid x)⟩
  letI : ProbabilityTheory.IsMarkovKernel kY := ⟨fun xa => by
    change IsProbabilityMeasure (if xa.2 then
      gaussianReal (μ₁ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩
    else gaussianReal (μ₀ xa.1) ⟨σ ^ 2, sq_nonneg σ⟩)
    cases xa.2 <;>
      exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _⟩
  have hobsform := gaussianCompletionBind_observed mu σ e μ₀ μ₁
    he hμ₀ hμ₁ hvalid
  have hjoint : P.map (fun z : Obs d => ((z.1, z.2.1), z.2.2)) =
      Measure.compProd (Measure.compProd mu kA) kY := by
    dsimp [P]
    rw [hobsform]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have hid : (fun z : Obs d => ((z.1, z.2.1), z.2.2)) ∘
        (fun z : ((Fin d → ℝ) × Bool) × ℝ => (z.1.1, z.1.2, z.2)) = id := by
      funext z
      rfl
    rw [hid, Measure.map_id]
  have hobs : Measurable (@observed d) := by unfold observed; fun_prop
  have hxa : P.map (fun z => (z.1, z.2.1)) =
      Measure.compProd mu kA := by
    dsimp [P]
    rw [Measure.map_map (by fun_prop) hobs]
    exact gaussianCompletionBind_covariate_treatment mu σ e μ₀ μ₁
      he hμ₀ hμ₁ hvalid
  exact ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := P) (X := fun z : Obs d => (z.1, z.2.1))
    (Y := fun z : Obs d => z.2.2) (κ := kY)
    (by fun_prop) (by fun_prop) (by simpa [hxa] using hjoint)

/-- The Gaussian completion reconstructed from a selected propensity and the
two Gaussian arm kernels has exactly the original observed law. [For the stated inputs and conditions](hyp:d,P,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,he01,hselected,harms), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_observed_eq_of_selected {d : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hselected : ∀ᵐ x ∂covariateLaw P,
      e x = propensity P x ∧ 0 < e x ∧ e x < 1)
    (harms : ∀ᵐ x ∂covariateLaw P,
      armKernel P x true =
          gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩ ∧
        armKernel P x false =
          gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :
    ((covariateLaw P).bind (gaussianCompletionAt σ e μ₀ μ₁)).map observed = P := by
  letI : IsProbabilityMeasure (covariateLaw P) := by
    unfold covariateLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  rw [gaussianCompletionBind_observed (covariateLaw P) σ e μ₀ μ₁
    he hμ₀ hμ₁ he01]
  exact gaussianObservedLaw_recomposition_of_selected P σ e μ₀ μ₁
    he hμ₀ hμ₁ he01 hselected harms

/-- Affinely transporting the covariate coordinate of the reconstructed
Gaussian completion gives exactly the transported observed law. [For the stated inputs and conditions](hyp:d,P,σ,e,μ₀,μ₁,he,hμ₀,hμ₁,he01,hselected,harms), [the asserted conclusion holds](goal). -/
lemma gaussianCompletionBind_affine_observed_eq_of_selected {d : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P] (σ : ℝ)
    (e μ₀ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hμ₀ : Measurable μ₀) (hμ₁ : Measurable μ₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hselected : ∀ᵐ x ∂covariateLaw P,
      e x = propensity P x ∧ 0 < e x ∧ e x < 1)
    (harms : ∀ᵐ x ∂covariateLaw P,
      armKernel P x true =
          gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩ ∧
        armKernel P x false =
          gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩) :
    let Pc := (covariateLaw P).bind (gaussianCompletionAt σ e μ₀ μ₁)
    (Pc.map (fun ω : Completion d =>
      (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1,
        ω.2.2.2.2))).map observed = transformedDornLaw P := by
  dsimp
  let F : Completion d → Completion d := fun ω =>
    (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2)
  let G : Obs d → Obs d := fun z =>
    (affineToCube z.1, z.2.1, z.2.2)
  have hF : Measurable F := by
    dsimp [F]
    have hx : Measurable (fun ω : Completion d => affineToCube ω.1) :=
      affineToCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)
  have hG : Measurable G := by
    dsimp [G]
    have hx : Measurable (fun z : Obs d => affineToCube z.1) :=
      affineToCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)
  have hobs : Measurable (@observed d) := by
    unfold observed
    fun_prop
  have hsource := gaussianCompletionBind_observed_eq_of_selected
    P σ e μ₀ μ₁ he hμ₀ hμ₁ he01 hselected harms
  calc
    (((covariateLaw P).bind
      (gaussianCompletionAt σ e μ₀ μ₁)).map F).map observed =
        ((covariateLaw P).bind (gaussianCompletionAt σ e μ₀ μ₁)).map
          (observed ∘ F) := Measure.map_map hobs hF
    _ = ((covariateLaw P).bind (gaussianCompletionAt σ e μ₀ μ₁)).map
          (G ∘ observed) := by rfl
    _ = (((covariateLaw P).bind
          (gaussianCompletionAt σ e μ₀ μ₁)).map observed).map G :=
      (Measure.map_map hG hobs).symm
    _ = P.map G := by rw [hsource]
    _ = transformedDornLaw P := rfl

/-- Gaussianized thin-strip completion, rescaled to Dorn's cube. For [the stated inputs and conditions](hyp:d,hd,γ,a,σ), [the `gaussianThinStripOriginal` object being defined](goal). -/
noncomputable def gaussianThinStripOriginal (d : ℕ) (hd : 2 ≤ d)
    (γ a σ : ℝ) : Measure (Obs d) :=
  let Pc : Measure (Completion d) :=
    (volume.restrict (cube d)).bind
      (gaussianCompletionAt σ
        (fun x => min (3 / 4 : ℝ) (stripPropensity d hd γ a x))
        (fun _ => 0) (fun _ => 0))
  (Pc.map observed).map
    (fun z => ((fun i => 2 * z.1 i - 1), z.2.1, z.2.2))

/-- Original-cube version of the capped thin-strip propensity. For [the stated inputs and conditions](hyp:d,hd,γ,a,x), [the `gaussianStripPropensity` object being defined](goal). -/
noncomputable def gaussianStripPropensity (d : ℕ) (hd : 2 ≤ d)
    (γ a : ℝ) (x : Fin d → ℝ) : ℝ :=
  min (3 / 4 : ℝ) (stripPropensity d hd γ a (affineToCube x))

/-- The inverse affine map sends unit-cube volume to normalized volume on
Dorn's cube. [For the stated inputs and conditions](hyp:d), [the asserted conclusion holds](goal). -/
lemma cubeVolume_map_affineFromCube (d : ℕ) :
    (volume.restrict (cube d)).map
        (fun x : Fin d → ℝ => fun i => 2 * x i - 1) =
      (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ •
        volume.restrict (dornCube d) := by
  let r : (Fin d → ℝ) → (Fin d → ℝ) := affineToCube
  let s : (Fin d → ℝ) → (Fin d → ℝ) := fun x i => 2 * x i - 1
  have hr : Measurable r := affineToCube_measurable
  have hs : Measurable s := affineFromCube_measurable
  have h := congrArg (fun m : Measure (Fin d → ℝ) => m.map s)
    (normalizedDornVolume_map_affineToCube d)
  rw [Measure.map_map hs hr] at h
  have hsr : s ∘ r = id := by
    funext x
    exact affineToCube_inverse x
  rw [hsr, Measure.map_id] at h
  exact h.symm

/-- [For the stated inputs and conditions](hyp:d,hd,γ,a,σ,hγ), [the asserted conclusion holds](goal). -/

lemma gaussianThinStripOriginal_probability (d : ℕ) (hd : 2 ≤ d)
    (γ a σ : ℝ) (hγ : 1 < γ) :
    IsProbabilityMeasure (gaussianThinStripOriginal d hd γ a σ) := by
  let e : (Fin d → ℝ) → ℝ := fun x =>
    min (3 / 4 : ℝ) (stripPropensity d hd γ a x)
  have he : Measurable e := by
    dsimp [e]
    exact measurable_const.min (stripPropensity_measurable d hd γ a)
  have hevalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    have hx := stripPropensity_mem_Icc d hd γ a hγ x
    exact ⟨le_min (by norm_num) hx.1, (min_le_left _ _).trans (by norm_num)⟩
  have hk : Measurable (gaussianCompletionAt σ e (fun _ => 0) (fun _ => 0)) :=
    gaussianCompletionAt_measurable σ e (fun _ => 0) (fun _ => 0)
      he measurable_const measurable_const
  have hpoint : ∀ x, IsProbabilityMeasure
      (gaussianCompletionAt σ e (fun _ => 0) (fun _ => 0) x) := by
    intro x
    letI := realBernoulli_probability (e x) (hevalid x)
    letI : IsProbabilityMeasure
        (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    unfold gaussianCompletionAt
    apply Measure.isProbabilityMeasure_map
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  let mu := volume.restrict (cube d)
  letI : IsProbabilityMeasure mu := by
    apply isProbabilityMeasure_iff.mpr
    dsimp [mu]
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    have hcube : cube d =
        Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  let Pc := mu.bind (gaussianCompletionAt σ e (fun _ => 0) (fun _ => 0))
  letI : IsProbabilityMeasure Pc :=
    isProbabilityMeasure_bind hk.aemeasurable
      (Filter.Eventually.of_forall hpoint)
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  change IsProbabilityMeasure ((Pc.map observed).map
    (fun z : Obs d => ((fun i => 2 * z.1 i - 1), z.2.1, z.2.2)))
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- [For the stated inputs and conditions](hyp:d,hd,γ,a,σ,hγ), [the asserted conclusion holds](goal). -/

lemma gaussianThinStripOriginal_covariateLaw (d : ℕ) (hd : 2 ≤ d)
    (γ a σ : ℝ) (hγ : 1 < γ) :
    covariateLaw (gaussianThinStripOriginal d hd γ a σ) =
      (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ •
        volume.restrict (dornCube d) := by
  let e : (Fin d → ℝ) → ℝ := fun x =>
    min (3 / 4 : ℝ) (stripPropensity d hd γ a x)
  have he : Measurable e := by
    dsimp [e]
    exact measurable_const.min (stripPropensity_measurable d hd γ a)
  have hevalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    have hx := stripPropensity_mem_Icc d hd γ a hγ x
    exact ⟨le_min (by norm_num) hx.1, (min_le_left _ _).trans (by norm_num)⟩
  let mu := volume.restrict (cube d)
  let Pc := mu.bind (gaussianCompletionAt σ e (fun _ => 0) (fun _ => 0))
  have hcov : Pc.map Prod.fst = mu := by
    dsimp [Pc]
    exact gaussianCompletionBind_covariate_marginal_ae mu σ e
      (fun _ => 0) (fun _ => 0) he measurable_const measurable_const
      (Filter.Eventually.of_forall hevalid)
  unfold gaussianThinStripOriginal covariateLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by unfold observed; fun_prop)]
  change Pc.map ((fun x : Fin d → ℝ => fun i => 2 * x i - 1) ∘ Prod.fst) = _
  rw [← Measure.map_map affineFromCube_measurable measurable_fst, hcov]
  exact cubeVolume_map_affineFromCube d

/-- Affine normalization cancels the inverse affine map in the definition of
the original-cube Gaussian strip law. [For the stated inputs and conditions](hyp:d,hd,γ,a,σ), [the asserted conclusion holds](goal). -/
lemma transformedDornLaw_gaussianThinStripOriginal (d : ℕ) (hd : 2 ≤ d)
    (γ a σ : ℝ) :
    transformedDornLaw (gaussianThinStripOriginal d hd γ a σ) =
      ((volume.restrict (cube d)).bind
        (gaussianCompletionAt σ
          (fun x => min (3 / 4 : ℝ) (stripPropensity d hd γ a x))
          (fun _ => 0) (fun _ => 0))).map observed := by
  unfold transformedDornLaw gaussianThinStripOriginal
  rw [Measure.map_map (by
    have hx : Measurable (fun z : Obs d => affineToCube z.1) :=
      affineToCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)) (by fun_prop)]
  have hid : (fun z : Obs d => (affineToCube z.1, z.2.1, z.2.2)) ∘
      (fun z : Obs d => ((fun i => 2 * z.1 i - 1), z.2.1, z.2.2)) = id := by
    funext z
    simp only [Function.comp_apply, id_eq, affineToCube_affineFromCube]
  rw [hid, Measure.map_id]

/-- [For the stated inputs and conditions](hyp:d,hd,γ,a,σ,hγ), [the asserted conclusion holds](goal). -/

lemma gaussianThinStripOriginal_selected_ae (d : ℕ) (hd : 2 ≤ d)
    (γ a σ : ℝ) (hγ : 1 < γ) :
    let P := gaussianThinStripOriginal d hd γ a σ
    let _ : IsProbabilityMeasure P :=
      gaussianThinStripOriginal_probability d hd γ a σ hγ
    ∀ᵐ x ∂covariateLaw P,
      gaussianStripPropensity d hd γ a x = propensity P x := by
  dsimp
  let e : (Fin d → ℝ) → ℝ := fun x =>
    min (3 / 4 : ℝ) (stripPropensity d hd γ a x)
  let Pc := (volume.restrict (cube d)).bind
    (gaussianCompletionAt σ e (fun _ => 0) (fun _ => 0))
  let Q := Pc.map observed
  let P := gaussianThinStripOriginal d hd γ a σ
  have he : Measurable e := by
    dsimp [e]
    exact measurable_const.min (stripPropensity_measurable d hd γ a)
  have hevalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    have hx := stripPropensity_mem_Icc d hd γ a hγ x
    exact ⟨le_min (by norm_num) hx.1, (min_le_left _ _).trans (by norm_num)⟩
  letI : IsProbabilityMeasure P :=
    gaussianThinStripOriginal_probability d hd γ a σ hγ
  letI : IsProbabilityMeasure (volume.restrict (cube d)) := by
    apply isProbabilityMeasure_iff.mpr
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    have hcube : cube d =
        Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  have hk : Measurable
      (gaussianCompletionAt σ e (fun _ => 0) (fun _ => 0)) :=
    gaussianCompletionAt_measurable σ e (fun _ => 0) (fun _ => 0)
      he measurable_const measurable_const
  have hpoint : ∀ x, IsProbabilityMeasure
      (gaussianCompletionAt σ e (fun _ => 0) (fun _ => 0) x) := by
    intro x
    letI := realBernoulli_probability (e x) (hevalid x)
    letI : IsProbabilityMeasure
        (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
    unfold gaussianCompletionAt
    apply Measure.isProbabilityMeasure_map
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  letI : IsProbabilityMeasure Pc := by
    dsimp [Pc]
    exact isProbabilityMeasure_bind hk.aemeasurable
      (Filter.Eventually.of_forall hpoint)
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  have hunit : ∀ᵐ y ∂volume.restrict (cube d), propensity Q y = e y := by
    simpa [Pc, Q] using gaussianCompletionBind_propensity_ae
      (volume.restrict (cube d)) σ e (fun _ => 0) (fun _ => 0)
        he measurable_const measurable_const hevalid
  have hPQ : transformedDornLaw P = Q := by
    dsimp [P, Q, Pc, e]
    exact transformedDornLaw_gaussianThinStripOriginal d hd γ a σ
  have hcovQ : covariateLaw Q = volume.restrict (cube d) := by
    dsimp [Q, Pc, covariateLaw]
    rw [Measure.map_map (by fun_prop) (by unfold observed; fun_prop)]
    exact gaussianCompletionBind_covariate_marginal_ae
      (volume.restrict (cube d)) σ e (fun _ => 0) (fun _ => 0)
      he measurable_const measurable_const
      (Filter.Eventually.of_forall hevalid)
  have hpull : ∀ᵐ x ∂covariateLaw P,
      propensity Q (affineToCube x) = e (affineToCube x) := by
    have hu : ∀ᵐ y ∂covariateLaw (transformedDornLaw P),
        propensity Q y = e y := by
      rw [hPQ, hcovQ]
      exact hunit
    rw [transformedDornLaw_covariateLaw P] at hu
    exact ae_eq_comp affineToCube_measurable.aemeasurable hu
  letI : IsProbabilityMeasure (transformedDornLaw P) :=
    transformedDornLaw_probability P
  have htransport := transformedDornLaw_treatmentKernel_ae P
  filter_upwards [hpull, htransport] with x hx hkx
  change e (affineToCube x) = propensity P x
  rw [← hx]
  unfold propensity
  have hkx' : ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
      (fun z => z.1) Q (affineToCube x) =
        ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
          (fun z => z.1) P x := by
    simpa only [hPQ] using hkx
  exact congrArg (fun m : Measure Bool => (m {true}).toReal) hkx'

/-- The capped inverse-affine strip is a valid selected propensity on Dorn's
cube, including strict almost-sure overlap. [For the stated inputs and conditions](hyp:d,hd,γ,a,σ,hγ), [the asserted conclusion holds](goal). -/
lemma gaussianThinStripOriginal_selected (d : ℕ) (hd : 2 ≤ d)
    (γ a σ : ℝ) (hγ : 1 < γ) :
    DornSelectedPropensity (dornCube d)
      (gaussianThinStripOriginal d hd γ a σ)
      (gaussianStripPropensity d hd γ a) := by
  let P := gaussianThinStripOriginal d hd γ a σ
  letI : IsProbabilityMeasure P :=
    gaussianThinStripOriginal_probability d hd γ a σ hγ
  have he : Measurable (gaussianStripPropensity d hd γ a) := by
    unfold gaussianStripPropensity
    exact (measurable_const.min (stripPropensity_measurable d hd γ a)).comp
      affineToCube_measurable
  refine ⟨inferInstance, he, ?_, ?_⟩
  · intro x hx
    have hs := stripPropensity_mem_Icc d hd γ a hγ (affineToCube x)
    exact ⟨le_min (by norm_num) hs.1,
      (min_le_left _ _).trans (by norm_num)⟩
  · have heq := gaussianThinStripOriginal_selected_ae d hd γ a σ hγ
    have hmapcov : (covariateLaw P).map affineToCube =
        volume.restrict (cube d) := by
      rw [← transformedDornLaw_covariateLaw P,
        transformedDornLaw_gaussianThinStripOriginal d hd γ a σ]
      unfold covariateLaw
      rw [Measure.map_map (by fun_prop) (by unfold observed; fun_prop)]
      exact gaussianCompletionBind_covariate_marginal_ae
        (volume.restrict (cube d)) σ
        (fun x => min (3 / 4 : ℝ) (stripPropensity d hd γ a x))
        (fun _ => 0) (fun _ => 0)
        (measurable_const.min (stripPropensity_measurable d hd γ a))
        measurable_const measurable_const
        (Filter.Eventually.of_forall fun x => by
          have hs := stripPropensity_mem_Icc d hd γ a hγ x
          exact ⟨le_min (by norm_num) hs.1,
            (min_le_left _ _).trans (by norm_num)⟩)
    have hposUnit := stripPropensity_uniform_pos_ae d hd γ a hγ
    rw [← hmapcov] at hposUnit
    have hpos := ae_of_ae_map (μ := covariateLaw P)
      affineToCube_measurable.aemeasurable hposUnit
    filter_upwards [heq, hpos] with x hx hp
    exact ⟨hx, lt_min (by norm_num) hp,
      (min_le_left _ _).trans_lt (by norm_num)⟩

/-- An almost-sure Bernoulli property holds at `false` when the failure mass
is positive. [For the stated inputs and conditions](hyp:r,hr,q,hq), [the asserted conclusion holds](goal). -/
lemma realBernoulli_ae_at_false_of_lt_one (r : ℝ) (hr : r < 1)
    (q : Bool → Prop) (hq : ∀ᵐ a ∂realBernoulli r, q a) : q false := by
  by_contra hfalse
  have hzero : (realBernoulli r) {a | ¬ q a} = 0 := by
    simpa only [Set.compl_setOf, Classical.not_not] using (mem_ae_iff.mp hq)
  have hle : (realBernoulli r) ({false} : Set Bool) ≤
      (realBernoulli r) {a | ¬ q a} := by
    apply measure_mono
    intro a ha
    have ha' : a = false := by simpa using ha
    subst a
    exact hfalse
  have hmass : (realBernoulli r) ({false} : Set Bool) =
      ENNReal.ofReal (1 - r) := by
    simp [realBernoulli]
  rw [hzero, hmass] at hle
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hr))) hle

/-- Both conditional response arms of the inverse-affine Gaussian strip law
are the centred Gaussian used in its completion. [For the stated inputs and conditions](hyp:d,hd,γ,a,σ,hγ), [the asserted conclusion holds](goal). -/
lemma gaussianThinStripOriginal_armKernels_ae (d : ℕ) (hd : 2 ≤ d)
    (γ a σ : ℝ) (hγ : 1 < γ) :
    let P := gaussianThinStripOriginal d hd γ a σ
    let _ : IsProbabilityMeasure P :=
      gaussianThinStripOriginal_probability d hd γ a σ hγ
    ∀ᵐ x ∂covariateLaw P,
      armKernel P x true = gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ ∧
      armKernel P x false = gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ := by
  dsimp
  let e : (Fin d → ℝ) → ℝ := fun x =>
    min (3 / 4 : ℝ) (stripPropensity d hd γ a x)
  let Q := ((volume.restrict (cube d)).bind
    (gaussianCompletionAt σ e (fun _ => 0) (fun _ => 0))).map observed
  let P := gaussianThinStripOriginal d hd γ a σ
  letI : IsProbabilityMeasure P :=
    gaussianThinStripOriginal_probability d hd γ a σ hγ
  have hPQ : transformedDornLaw P = Q := by
    dsimp [P, Q, e]
    exact transformedDornLaw_gaussianThinStripOriginal d hd γ a σ
  letI : IsProbabilityMeasure Q := by
    rw [← hPQ]
    exact transformedDornLaw_probability P
  letI : IsProbabilityMeasure (transformedDornLaw P) :=
    transformedDornLaw_probability P
  have he : Measurable e := by
    dsimp [e]
    exact measurable_const.min (stripPropensity_measurable d hd γ a)
  have hevalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    have hx := stripPropensity_mem_Icc d hd γ a hγ x
    exact ⟨le_min (by norm_num) hx.1,
      (min_le_left _ _).trans (by norm_num)⟩
  have hQkernel := gaussianCompletionBind_observedKernel_ae
    (volume.restrict (cube d)) σ e (fun _ => 0) (fun _ => 0)
      he measurable_const measurable_const hevalid
  let E : ((Fin d → ℝ) × Bool) → ((Fin d → ℝ) × Bool) :=
    fun xa => (affineToCube xa.1, xa.2)
  have hE : Measurable E := by
    dsimp [E]
    exact (affineToCube_measurable.comp measurable_fst).prodMk measurable_snd
  have hG : Measurable (fun z : Obs d =>
      (affineToCube z.1, z.2.1, z.2.2)) := by
    have hx : Measurable (fun z : Obs d => affineToCube z.1) :=
      affineToCube_measurable.comp measurable_fst
    fun_prop (disch := assumption)
  have hmap : (P.map (fun z : Obs d => (z.1, z.2.1))).map E =
      Q.map (fun z : Obs d => (z.1, z.2.1)) := by
    rw [← hPQ]
    unfold transformedDornLaw
    rw [Measure.map_map hE (by fun_prop),
      Measure.map_map (by fun_prop) hG]
    rfl
  have hQkernel' : ∀ᵐ xa ∂Q.map (fun z : Obs d => (z.1, z.2.1)),
      ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
        (fun z : Obs d => (z.1, z.2.1)) Q xa =
          gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ := by
    filter_upwards [hQkernel] with xa hxa
    cases xa.2 <;> simpa [Q] using hxa
  rw [← hmap] at hQkernel'
  have hpull := ae_of_ae_map (μ := P.map (fun z : Obs d => (z.1, z.2.1)))
    hE.aemeasurable hQkernel'
  have htransport := transformedDornLaw_outcomeKernel_ae P
  have hjoint : ∀ᵐ xa ∂P.map (fun z : Obs d => (z.1, z.2.1)),
      armKernel P xa.1 xa.2 = gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ := by
    filter_upwards [hpull, htransport] with xa hq ht
    have hq' : ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
        (fun z : Obs d => (z.1, z.2.1)) Q
          (affineToCube xa.1, xa.2) =
        gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ := by
      simpa [E] using hq
    have ht' : ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
        (fun z : Obs d => (z.1, z.2.1)) Q
          (affineToCube xa.1, xa.2) =
        ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
          (fun z : Obs d => (z.1, z.2.1)) P xa := by
      simpa only [hPQ] using ht
    exact ht'.symm.trans hq'
  letI : IsProbabilityMeasure (covariateLaw P) := by
    unfold covariateLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  rw [← observedLaw_treatment_compProd P] at hjoint
  have hsections := Measure.ae_ae_of_ae_compProd hjoint
  have hselectedEq := gaussianThinStripOriginal_selected_ae d hd γ a σ hγ
  have hcovQ : covariateLaw Q = volume.restrict (cube d) := by
    dsimp [Q, covariateLaw]
    rw [Measure.map_map (by fun_prop) (by unfold observed; fun_prop)]
    exact gaussianCompletionBind_covariate_marginal_ae
      (volume.restrict (cube d)) σ e (fun _ => 0) (fun _ => 0)
      he measurable_const measurable_const
      (Filter.Eventually.of_forall hevalid)
  have hmapcov : (covariateLaw P).map affineToCube =
      volume.restrict (cube d) := by
    rw [← transformedDornLaw_covariateLaw P, hPQ, hcovQ]
  have hposUnit := stripPropensity_uniform_pos_ae d hd γ a hγ
  rw [← hmapcov] at hposUnit
  have hpos := ae_of_ae_map (μ := covariateLaw P)
    affineToCube_measurable.aemeasurable hposUnit
  have hselected : ∀ᵐ x ∂covariateLaw P,
      gaussianStripPropensity d hd γ a x = propensity P x ∧
        0 < gaussianStripPropensity d hd γ a x ∧
        gaussianStripPropensity d hd γ a x < 1 := by
    have hselectedEq' : ∀ᵐ x ∂covariateLaw P,
        gaussianStripPropensity d hd γ a x = propensity P x := by
      simpa [P] using hselectedEq
    filter_upwards [hselectedEq', hpos] with x heq hp
    refine ⟨heq, ?_, ?_⟩
    · exact lt_min (by norm_num) hp
    · exact (min_le_left _ _).trans_lt (by norm_num)
  have hA := condDistrib_treatment_eq_realBernoulli_of_selected P
    (gaussianStripPropensity d hd γ a) hselected
  filter_upwards [hsections, hA, hselected] with x hx hAx hs
  rw [hAx] at hx
  constructor
  · exact realBernoulli_ae_at_true_of_pos _ hs.2.1 _ hx
  · exact realBernoulli_ae_at_false_of_lt_one _ hs.2.2 _ hx

/-- Capping the strip propensity at `3/4` preserves a polynomial lower-tail
bound, with the fixed loss contributed only by levels above the cap. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ), [the asserted conclusion holds](goal). -/
lemma cappedStrip_uniform_tail (d : ℕ) (hd : 2 ≤ d)
    (γ a : ℝ) (hγ : 1 < γ) :
    let C := ((3 / 4 : ℝ) ^ (γ - 1))⁻¹
    0 < C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (volume.restrict (cube d)).real
        {x | min (3 / 4 : ℝ) (stripPropensity d hd γ a x) ≤ t} ≤
          C * t ^ (γ - 1) := by
  dsimp
  letI : IsProbabilityMeasure (volume.restrict (cube d)) := by
    apply isProbabilityMeasure_iff.mpr
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ))
        (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  let c : ℝ := (3 / 4 : ℝ) ^ (γ - 1)
  have hcpos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨inv_pos.mpr hcpos, ?_⟩
  intro t ht
  have htail := stripPropensity_uniform_tail_bound d hd γ a t hγ ht
  by_cases htc : t < 3 / 4
  · have hset : {x | min (3 / 4 : ℝ) (stripPropensity d hd γ a x) ≤ t} =
        {x | stripPropensity d hd γ a x ≤ t} := by
      ext x
      simp only [Set.mem_setOf_eq, min_le_iff]
      exact or_iff_right (not_le.mpr htc)
    rw [hset]
    have hc_le : c ≤ 1 := by
      dsimp [c]
      exact Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
    have hinv : 1 ≤ c⁻¹ := by
      simpa using (inv_le_inv₀ zero_lt_one hcpos).2 hc_le
    exact htail.trans (by
      simpa [c] using mul_le_mul_of_nonneg_right hinv
        (Real.rpow_nonneg ht.1 (γ - 1)))
  · have htc' : 3 / 4 ≤ t := le_of_not_gt htc
    have hmono : c ≤ t ^ (γ - 1) := by
      dsimp [c]
      exact Real.rpow_le_rpow (by norm_num) htc' (by linarith)
    have hprod : 1 ≤ c⁻¹ * t ^ (γ - 1) := by
      calc
        1 = c⁻¹ * c := by field_simp
        _ ≤ c⁻¹ * t ^ (γ - 1) :=
          mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hcpos.le)
    calc
      (volume.restrict (cube d)).real
          {x | min (3 / 4 : ℝ) (stripPropensity d hd γ a x) ≤ t} ≤ 1 := by
        exact (measureReal_mono (Set.subset_univ _)).trans (by simp)
      _ ≤ c⁻¹ * t ^ (γ - 1) := hprod

/-- The inverse-affine capped strip has the same global propensity tail as its
unit-cube representative. [For the stated inputs and conditions](hyp:d,hd,γ,a,σ,hγ), [the asserted conclusion holds](goal). -/
lemma gaussianThinStripOriginal_globalTail (d : ℕ) (hd : 2 ≤ d)
    (γ a σ : ℝ) (hγ : 1 < γ) :
    let P := gaussianThinStripOriginal d hd γ a σ
    let _ : IsProbabilityMeasure P :=
      gaussianThinStripOriginal_probability d hd γ a σ hγ
    GlobalPropensityTail P (gaussianStripPropensity d hd γ a)
      ((3 / 4 : ℝ) ^ (γ - 1))⁻¹ γ := by
  dsimp
  let P := gaussianThinStripOriginal d hd γ a σ
  letI : IsProbabilityMeasure P :=
    gaussianThinStripOriginal_probability d hd γ a σ hγ
  constructor
  · exact gaussianThinStripOriginal_selected_ae d hd γ a σ hγ
  · intro t ht
    have hu := (cappedStrip_uniform_tail d hd γ a hγ).2 t ht
    have hmapcov : (covariateLaw P).map affineToCube =
        volume.restrict (cube d) := by
      rw [← transformedDornLaw_covariateLaw P,
        transformedDornLaw_gaussianThinStripOriginal d hd γ a σ]
      unfold covariateLaw
      rw [Measure.map_map (by fun_prop) (by unfold observed; fun_prop)]
      exact gaussianCompletionBind_covariate_marginal_ae
        (volume.restrict (cube d)) σ
        (fun x => min (3 / 4 : ℝ) (stripPropensity d hd γ a x))
        (fun _ => 0) (fun _ => 0)
        (measurable_const.min (stripPropensity_measurable d hd γ a))
        measurable_const measurable_const
        (Filter.Eventually.of_forall fun x => by
          have hx := stripPropensity_mem_Icc d hd γ a hγ x
          exact ⟨le_min (by norm_num) hx.1,
            (min_le_left _ _).trans (by norm_num)⟩)
    rw [← hmapcov] at hu
    have hs : MeasurableSet
        {x | min (3 / 4 : ℝ) (stripPropensity d hd γ a x) ≤ t} :=
      measurableSet_le
        (measurable_const.min (stripPropensity_measurable d hd γ a))
        measurable_const
    rw [measureReal_def, Measure.map_apply affineToCube_measurable hs] at hu
    simpa [P, gaussianStripPropensity, Function.comp_def, measureReal_def] using hu

/-- Every centred real Gaussian has a finite `q` moment; enlarging its moment
integral produces the exact positive radius required by Dorn's model. [For the stated inputs and conditions](hyp:q,σ,hq), [the asserted conclusion holds](goal). -/
lemma exists_gaussianReal_qMoment_radius (q σ : ℝ) (hq : 1 < q) :
    ∃ M : ℝ, 0 < M ∧
      Integrable (fun y : ℝ => |y| ^ q)
        (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) ∧
      (∫ y : ℝ, |y| ^ q ∂gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) ≤ M ^ q := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hm := ProbabilityTheory.memLp_id_gaussianReal'
    (μ := (0 : ℝ)) (v := ⟨σ ^ 2, sq_nonneg σ⟩)
      (ENNReal.ofReal q) (by simp)
  have hi0 := hm.integrable_norm_rpow
    (ENNReal.ofReal_pos.mpr hq0).ne' ENNReal.ofReal_ne_top
  have hi : Integrable (fun y : ℝ => |y| ^ q)
      (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) := by
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hq0.le, id] using hi0
  let I : ℝ := ∫ y : ℝ, |y| ^ q ∂gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩
  let M : ℝ := max 1 |I|
  have hM1 : 1 ≤ M := le_max_left _ _
  have hIM : I ≤ M := (le_abs_self I).trans (le_max_right _ _)
  have hMq : M ≤ M ^ q := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hM1 hq.le)
  exact ⟨M, lt_of_lt_of_le zero_lt_one hM1, hi, hIM.trans hMq⟩

/-- The inverse cube affine map scales Euclidean balls by exactly two. [For the stated inputs and conditions](hyp:d,x,x₀,h), [the asserted conclusion holds](goal). -/
lemma affineFromCube_mem_ball2_iff {d : ℕ} (x x₀ : Fin d → ℝ) (h : ℝ) :
    (fun i => 2 * x i - 1) ∈ ball2 (fun i => 2 * x₀ i - 1) (2 * h) ↔
      x ∈ ball2 x₀ h := by
  unfold ball2
  change (∑ i, ((2 * x i - 1) - (2 * x₀ i - 1)) ^ 2) ≤
      (2 * h) ^ 2 ↔ (∑ i, (x i - x₀ i) ^ 2) ≤ h ^ 2
  have hsum : (∑ i, ((2 * x i - 1) - (2 * x₀ i - 1)) ^ 2) =
      4 * ∑ i, (x i - x₀ i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  constructor <;> intro hh <;> nlinarith

/-- Dorn's local ratio condition is invariant under the coordinatewise affine
similarity between the source cube and the unit cube. [For the stated inputs and conditions](hyp:d,P,Q,e,he,hcovP,hcovQ,hselQ,hA3), [the asserted conclusion holds](goal). -/
lemma dornA3OnCube_of_affine_original {d : ℕ}
    (P Q : Measure (Obs d)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (e : (Fin d → ℝ) → ℝ) (he : Measurable e)
    (hcovP : covariateLaw P =
      (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ • volume.restrict (dornCube d))
    (hcovQ : covariateLaw Q = volume.restrict (cube d))
    (hselQ : DornSelectedPropensity (cube d) Q e)
    (hA3 : DornA3 (dornCube d)
      ({(P, (fun _ => 0), (fun _ => 0), e ∘ affineToCube)} :
        Set (DornSourceLaw d))) :
    DornA3OnCube Q e := by
  classical
  obtain ⟨_, _, _, ρ, ν, h₀, hρ, hν, hh₀, hbound⟩ := hA3
  refine ⟨Set.singleton_nonempty _, ?_, ?_, ρ, ν, h₀ / 2,
    hρ, hν, by positivity, ?_⟩
  · intro z hz
    have hz' : z = (Q, (fun _ => 0), (fun _ => 0), e) :=
      Set.mem_singleton_iff.mp hz
    subst z
    rw [hcovQ]
    have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ))
        (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Measure.restrict_apply (by measurability),
      Set.inter_self, Real.volume_Icc_pi]
    simp
  · intro z hz
    have hz' : z = (Q, (fun _ => 0), (fun _ => 0), e) :=
      Set.mem_singleton_iff.mp hz
    subst z
    exact hselQ
  · intro z hz x₀ hx₀ h hh
    have hz' : z = (Q, (fun _ => 0), (fun _ => 0), e) :=
      Set.mem_singleton_iff.mp hz
    subst z
    let s : (Fin d → ℝ) → (Fin d → ℝ) := fun x i => 2 * x i - 1
    have hs : Measurable s := affineFromCube_measurable
    have hsx₀ : s x₀ ∈ dornCube d := by
      rw [← affineToCube_mem_cube_iff]
      change affineToCube (s x₀) ∈ cube d
      rw [show affineToCube (s x₀) = x₀ by
        funext i; exact congrFun (affineToCube_affineFromCube x₀) i]
      exact hx₀
    have h2h : 2 * h ∈ Set.Ioc (0 : ℝ) h₀ := by
      exact ⟨mul_pos (by norm_num) hh.1, by linarith [hh.2]⟩
    have hold := hbound
      (P, (fun _ => 0), (fun _ => 0), e ∘ affineToCube)
      (Set.mem_singleton _) (s x₀) hsx₀ (2 * h) h2h
    have himage : (e ∘ affineToCube) ''
          (ball2 (s x₀) (2 * h) ∩ dornCube d) =
        e '' (ball2 x₀ h ∩ cube d) := by
      apply Set.Subset.antisymm
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        refine ⟨affineToCube x, ?_, rfl⟩
        constructor
        · have hb := hx.1
          have hback : s (affineToCube x) = x := by
            funext i
            exact congrFun (affineToCube_inverse x) i
          rw [← hback] at hb
          exact (affineFromCube_mem_ball2_iff (affineToCube x) x₀ h).mp hb
        · exact (affineToCube_mem_cube_iff x).2 hx.2
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        refine ⟨s x, ?_, ?_⟩
        · constructor
          · exact (affineFromCube_mem_ball2_iff x x₀ h).2 hx.1
          · exact (affineToCube_mem_cube_iff (s x)).1 (by
              change affineToCube (s x) ∈ cube d
              rw [show affineToCube (s x) = x by
                funext i; exact congrFun (affineToCube_affineFromCube x) i]
              exact hx.2)
        · simp [s, Function.comp_def, affineToCube_affineFromCube]
    let AU : Set (Fin d → ℝ) :=
      {x | e x ≥ ρ * sSup (e '' (ball2 x₀ h ∩ cube d))} ∩ ball2 x₀ h
    let AO : Set (Fin d → ℝ) :=
      {x | (e ∘ affineToCube) x ≥
        ρ * sSup ((e ∘ affineToCube) ''
          (ball2 (s x₀) (2 * h) ∩ dornCube d))} ∩
        ball2 (s x₀) (2 * h)
    have hpreA : s ⁻¹' AO = AU := by
      dsimp [AO, AU]
      rw [himage]
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff,
        Set.mem_setOf_eq, Function.comp_apply]
      rw [show affineToCube (s x) = x by
        funext i; exact congrFun (affineToCube_affineFromCube x) i]
      rw [affineFromCube_mem_ball2_iff]
    have hpreB : s ⁻¹' ball2 (s x₀) (2 * h) = ball2 x₀ h := by
      ext x
      exact affineFromCube_mem_ball2_iff x x₀ h
    have hAO : MeasurableSet AO := by
      dsimp [AO]
      apply (measurableSet_le measurable_const (he.comp affineToCube_measurable)).inter
      unfold ball2
      exact measurableSet_le (by fun_prop) (by fun_prop)
    have hBO : MeasurableSet (ball2 (s x₀) (2 * h)) := by
      unfold ball2
      exact measurableSet_le (by fun_prop) (by fun_prop)
    have hmeasureA : (covariateLaw P).real AO =
        (covariateLaw Q).real AU := by
      rw [hcovP, ← cubeVolume_map_affineFromCube d, hcovQ,
        measureReal_def, Measure.map_apply hs hAO, hpreA, measureReal_def]
    have hmeasureB : (covariateLaw P).real (ball2 (s x₀) (2 * h)) =
        (covariateLaw Q).real (ball2 x₀ h) := by
      rw [hcovP, ← cubeVolume_map_affineFromCube d, hcovQ,
        measureReal_def, Measure.map_apply hs hBO, hpreB, measureReal_def]
    dsimp only at hold ⊢
    change ν < (covariateLaw P).real AO /
      (covariateLaw P).real (ball2 (s x₀) (2 * h)) at hold
    change ν < (covariateLaw Q).real AU /
      (covariateLaw Q).real (ball2 x₀ h)
    rw [← hmeasureA, ← hmeasureB]
    exact hold

/-- Capping the thin-strip propensity at `3/4` does not repair A3.  On the
shrinking balls used in the obstruction the uncapped propensity is already
strictly below the cap. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ,ha,P,hcov), [the asserted conclusion holds](goal). -/
lemma cappedStrip_not_dornA3_of_uniform (d : ℕ) (hd : 2 ≤ d)
    (γ a : ℝ) (hγ : 1 < γ) (ha : 1 < a)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hcov : covariateLaw P = volume.restrict (cube d)) :
    ¬ DornA3OnCube P
      (fun x => min (3 / 4 : ℝ) (stripPropensity d hd γ a x)) := by
  classical
  intro hA3
  change DornA3 (cube d)
    ({(P, (fun _ => 0), (fun _ => 0),
      fun x => min (3 / 4 : ℝ) (stripPropensity d hd γ a x))} :
      Set (DornSourceLaw d)) at hA3
  obtain ⟨_, _, _, ρ, ν, h₀, hρ, hν, hh₀, hA3bound⟩ := hA3
  obtain ⟨h, hh, hh₀', hsmall, hball, hratio⟩ :=
    uniformCube_thinStrip_local_ratio d hd γ a hγ ha
      (min ρ 2) ν h₀ (lt_min hρ (by norm_num)) hν hh₀
  have hsmallρ : ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) < ρ / 4 :=
    hsmall.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hsmallCap :
      ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) < 1 / 2 :=
    hsmall.trans_le (by
      have hm : min ρ 2 ≤ 2 := min_le_right _ _
      linarith)
  have hx₀ : (fun _ : Fin d => (1 / 2 : ℝ)) ∈ cube d := by
    simp [cube, Pi.le_def]
    intro i
    norm_num
  have hcapEq : Set.EqOn
      (fun x => min (3 / 4 : ℝ) (stripPropensity d hd γ a x))
      (stripPropensity d hd γ a)
      (ball2 (fun _ => (1 / 2 : ℝ)) h) := by
    intro x hx
    have hcoord : centreRadius x ≤ h := by
      unfold centreRadius
      letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      apply (pi_norm_le_iff_of_nonempty _).2
      intro i
      have hi : (x i - (1 / 2 : ℝ)) ^ 2 ≤
          ∑ j : Fin d, (x j - 1 / 2) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j - 1 / 2))
          (Finset.mem_univ i)
      have habs : |x i - 1 / 2| ≤ h := by
        change (∑ j : Fin d, (x j - 1 / 2) ^ 2) ≤ h ^ 2 at hx
        nlinarith [hx, hi, sq_abs (x i - (1 / 2 : ℝ)),
          abs_nonneg (x i - (1 / 2 : ℝ))]
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using habs
    have hstrip := stripPropensity_le_radial_add_quarter d hd γ a x
    have hrad := stripPropensity_off_strip_radius_bound d hd γ a h hγ x
    by_cases hs : x ∈ thinStrip d hd a
    · have hradial :
          (centreRadiusCDF d (centreRadius x)) ^ ((1 : ℝ) / (γ - 1)) ≤
            ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) := by
        have hbase : centreRadiusCDF d (centreRadius x) ≤ (2 * h) ^ d := by
          unfold centreRadiusCDF
          exact (min_le_right _ _).trans
            (pow_le_pow_left₀
              (mul_nonneg (by norm_num) (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hcoord (by norm_num)) d)
        exact Real.rpow_le_rpow (by
          unfold centreRadiusCDF
          exact le_min (by norm_num)
            (pow_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) _))
          hbase (by positivity)
      have : stripPropensity d hd γ a x < 3 / 4 := by
        nlinarith [hstrip, hradial, hsmallCap]
      exact min_eq_right this.le
    · have := hrad hs hcoord
      have hlt : stripPropensity d hd γ a x < 3 / 4 :=
        this.trans_lt (hsmallCap.trans (by norm_num))
      exact min_eq_right hlt.le
  have hbound := hA3bound
    (P, (fun _ => 0), (fun _ => 0),
      fun x => min (3 / 4 : ℝ) (stripPropensity d hd γ a x))
    (Set.mem_singleton _) (fun _ => (1 / 2 : ℝ)) hx₀ h ⟨hh, hh₀'⟩
  have himage :
      (fun x => min (3 / 4 : ℝ) (stripPropensity d hd γ a x)) ''
          (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ cube d) =
        stripPropensity d hd γ a ''
          (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ cube d) := by
    apply Set.image_congr
    intro x hx
    exact hcapEq hx.1
  have hsubset :
      {x | min (3 / 4 : ℝ) (stripPropensity d hd γ a x) ≥
          ρ * sSup ((fun y => min (3 / 4 : ℝ)
            (stripPropensity d hd γ a y)) ''
              (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ cube d))} ∩
        ball2 (fun _ => (1 / 2 : ℝ)) h ⊆
      thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h := by
    intro x hx
    have hxcap := hcapEq hx.2
    rw [himage] at hx
    have hx' : stripPropensity d hd γ a x ≥
        ρ * sSup (stripPropensity d hd γ a ''
          (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ cube d)) := by
      have hlevel := hx.1
      change ρ * sSup (stripPropensity d hd γ a ''
        (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ cube d)) ≤
          min (3 / 4 : ℝ) (stripPropensity d hd γ a x) at hlevel
      change min (3 / 4 : ℝ) (stripPropensity d hd γ a x) =
        stripPropensity d hd γ a x at hxcap
      rw [hxcap] at hlevel
      exact hlevel
    refine ⟨?_, hx.2⟩
    apply stripSuperlevel_ball_cube_subset_strip d hd γ a h ρ hγ
      (by linarith) hρ hsmallρ
    exact ⟨by
      unfold centreRadius
      letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      apply (pi_norm_le_iff_of_nonempty _).2
      intro i
      have hi : (x i - (1 / 2 : ℝ)) ^ 2 ≤
          ∑ j : Fin d, (x j - 1 / 2) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j - 1 / 2))
          (Finset.mem_univ i)
      have habs : |x i - 1 / 2| ≤ h := by
        have hxball := hx.2
        change (∑ j : Fin d, (x j - 1 / 2) ^ 2) ≤ h ^ 2 at hxball
        nlinarith [hxball, hi, sq_abs (x i - (1 / 2 : ℝ)),
          abs_nonneg (x i - (1 / 2 : ℝ))]
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using habs, hx'⟩
  letI : IsProbabilityMeasure (covariateLaw P) := by
    unfold covariateLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hmono : (covariateLaw P).real
      ({x | min (3 / 4 : ℝ) (stripPropensity d hd γ a x) ≥
          ρ * sSup ((fun y => min (3 / 4 : ℝ)
            (stripPropensity d hd γ a y)) ''
              (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ cube d))} ∩
        ball2 (fun _ => (1 / 2 : ℝ)) h) ≤
      (covariateLaw P).real
        (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) :=
    measureReal_mono hsubset
  rw [hcov] at hmono
  dsimp at hbound
  rw [hcov] at hbound
  have hdiv := (div_le_div_of_nonneg_right hmono hball.le).trans hratio
  exact (not_lt_of_ge hdiv) hbound

/-- The capped Gaussian strip violates Dorn A3 on the original source cube. [For the stated inputs and conditions](hyp:d,hd,γ,a,σ,hγ,ha), [the asserted conclusion holds](goal). -/
lemma gaussianThinStripOriginal_not_dornA3 (d : ℕ) (hd : 2 ≤ d)
    (γ a σ : ℝ) (hγ : 1 < γ) (ha : 1 < a) :
    ¬ DornA3 (dornCube d)
      ({(gaussianThinStripOriginal d hd γ a σ,
        (fun _ => 0), (fun _ => 0), gaussianStripPropensity d hd γ a)} :
          Set (DornSourceLaw d)) := by
  let P := gaussianThinStripOriginal d hd γ a σ
  let e : (Fin d → ℝ) → ℝ := fun x =>
    min (3 / 4 : ℝ) (stripPropensity d hd γ a x)
  let Q := ((volume.restrict (cube d)).bind
    (gaussianCompletionAt σ e (fun _ => 0) (fun _ => 0))).map observed
  letI : IsProbabilityMeasure P :=
    gaussianThinStripOriginal_probability d hd γ a σ hγ
  have hPQ : transformedDornLaw P = Q := by
    dsimp [P, Q, e]
    exact transformedDornLaw_gaussianThinStripOriginal d hd γ a σ
  letI : IsProbabilityMeasure Q := by
    rw [← hPQ]
    exact transformedDornLaw_probability P
  have he : Measurable e := by
    dsimp [e]
    exact measurable_const.min (stripPropensity_measurable d hd γ a)
  have hevalid : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    have hx := stripPropensity_mem_Icc d hd γ a hγ x
    exact ⟨le_min (by norm_num) hx.1,
      (min_le_left _ _).trans (by norm_num)⟩
  have hcovQ : covariateLaw Q = volume.restrict (cube d) := by
    dsimp [Q, covariateLaw]
    rw [Measure.map_map (by fun_prop) (by unfold observed; fun_prop)]
    exact gaussianCompletionBind_covariate_marginal_ae
      (volume.restrict (cube d)) σ e (fun _ => 0) (fun _ => 0)
      he measurable_const measurable_const
      (Filter.Eventually.of_forall hevalid)
  letI : IsProbabilityMeasure (volume.restrict (cube d)) := by
    apply isProbabilityMeasure_iff.mpr
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ))
        (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  have hprop : ∀ᵐ x ∂covariateLaw Q, propensity Q x = e x := by
    rw [hcovQ]
    simpa [Q] using gaussianCompletionBind_propensity_ae
      (volume.restrict (cube d)) σ e (fun _ => 0) (fun _ => 0)
        he measurable_const measurable_const hevalid
  have hpos := stripPropensity_uniform_pos_ae d hd γ a hγ
  have hfull : ∀ᵐ x ∂covariateLaw Q,
      e x = propensity Q x ∧ 0 < e x ∧ e x < 1 := by
    rw [hcovQ] at hprop
    rw [hcovQ]
    filter_upwards [hprop, hpos] with x hp hx
    exact ⟨hp.symm, lt_min (by norm_num) hx,
      (min_le_left _ _).trans_lt (by norm_num)⟩
  have hselQ : DornSelectedPropensity (cube d) Q e :=
    ⟨inferInstance, he, fun x hx => hevalid x, hfull⟩
  intro hA3
  have hunit : DornA3OnCube Q e := by
    apply dornA3OnCube_of_affine_original P Q e he
      (gaussianThinStripOriginal_covariateLaw d hd γ a σ hγ)
      hcovQ hselQ
    change DornA3 (dornCube d)
      ({(P, (fun _ => 0), (fun _ => 0), e ∘ affineToCube)} :
        Set (DornSourceLaw d)) at hA3
    exact hA3
  exact cappedStrip_not_dornA3_of_uniform d hd γ a hγ ha Q hcovQ hunit

/-- The full coordinatewise Hölder radius of a response on the unit cube. For [the stated inputs and conditions](hyp:β,g), [the `holderFullNorm` object being defined](goal). -/
noncomputable def holderFullNorm {d : ℕ} (β : ℝ)
    (g : (Fin d → ℝ) → ℝ) : ℝ :=
  sInf {L : ℝ | 0 ≤ L ∧ HolderBall β L g}

/-- One radius for every transformed member of Dorn's seminorm class with
the common response bound obtained from Assumption 1. For [the stated inputs and conditions](hyp:d,β,M,L₀), [the `dornCommonRadius` object being defined](goal). -/
noncomputable def dornCommonRadius (d : ℕ) (β M L₀ : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ g : (Fin d → ℝ) → ℝ,
    DornTopDerivativeSeminorm β L₀ g ∧
    (∀ x ∈ dornCube d, |g x| ≤ M) ∧
    r = holderFullNorm β (transformedResponse g)}

/-- Fixed-cube interpolation constant: its inputs are only dimension and
smoothness, with all admissible amplitude and seminorm pairs normalized out. For [the stated inputs and conditions](hyp:d,β), [the `dornInterpolationConstant` object being defined](goal). -/
noncomputable def dornInterpolationConstant (d : ℕ) (β : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ (M L₀ : ℝ) (g : (Fin d → ℝ) → ℝ),
    0 < M ∧ 0 < L₀ ∧ DornTopDerivativeSeminorm β L₀ g ∧
    (∀ x ∈ dornCube d, |g x| ≤ M) ∧
    r = holderFullNorm β (transformedResponse g) / (M + L₀)}

/-- The infimum defining `holderFullNorm` is attained.  Each defining
inequality is closed in its radius, so it may be passed to the infimum
pointwise. [For the stated inputs and conditions](hyp:d,β,g,hball), [the asserted conclusion holds](goal). -/
lemma holderBall_holderFullNorm {d : ℕ} (β : ℝ)
    (g : (Fin d → ℝ) → ℝ)
    (hball : ∃ L : ℝ, 0 ≤ L ∧ HolderBall β L g) :
    HolderBall β (holderFullNorm β g) g := by
  let S : Set ℝ := {L : ℝ | 0 ≤ L ∧ HolderBall β L g}
  have hSne : S.Nonempty := by
    obtain ⟨L, hL⟩ := hball
    exact ⟨L, hL⟩
  have hSbelow : BddBelow S := ⟨0, fun _ hL => hL.1⟩
  obtain ⟨L₀, hL₀, hball₀⟩ := hball
  refine ⟨hball₀.regularity, ?_, ?_⟩
  · intro j hj f x hx
    apply le_csInf hSne
    intro L hL
    exact hL.2.derivBound j hj f x hx
  · intro f x hx y hy
    let q : ℝ := ‖x - y‖ ^ (β - (polynomialDegree β : ℝ))
    have hq : 0 ≤ q := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hq0 : q = 0
    · have hz := hball₀.modulus f x hx y hy
      rw [show L₀ * q = 0 by simp [hq0]] at hz
      simpa [q, hq0] using hz
    · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      apply (div_le_iff₀ hqpos).mp
      apply le_csInf hSne
      intro L hL
      exact (div_le_iff₀ hqpos).mpr (hL.2.modulus f x hx y hy)

/-- Increasing the common radius preserves the intrinsic Holder ball. [For the stated inputs and conditions](hyp:d,β,L,L',g,h,hLL'), [the asserted conclusion holds](goal). -/
lemma HolderBall.mono_radius {d : ℕ} {β L L' : ℝ}
    {g : (Fin d → ℝ) → ℝ} (h : HolderBall β L g) (hLL' : L ≤ L') :
    HolderBall β L' g := by
  refine ⟨h.regularity, ?_, ?_⟩
  · intro j hj f x hx
    exact (h.derivBound j hj f x hx).trans hLL'
  · intro f x hx y hy
    exact (h.modulus f x hx y hy).trans
      (mul_le_mul_of_nonneg_right hLL' (Real.rpow_nonneg (norm_nonneg _) _))

/-- A Holder response may be replaced by a representative agreeing on the
cube when the completion covariate is supported there. [For the stated inputs and conditions](hyp:d,β,L,Pc,g,h,hg,heq,hsupp), [the asserted conclusion holds](goal). -/
lemma HolderResponse.congr_on_cube {d : ℕ} {β L : ℝ}
    {Pc : Measure (Completion d)} [IsProbabilityMeasure Pc]
    {g h : (Fin d → ℝ) → ℝ} (hg : HolderResponse Pc g β L)
    (heq : Set.EqOn g h (cube d))
    (hsupp : (Pc.map (fun ω : Completion d => ω.1)) (cube d) = 1) :
    HolderResponse Pc h β L := by
  have hcube : MeasurableSet (cube d) := by
    unfold cube
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have haecube : ∀ᵐ ω ∂Pc, ω.1 ∈ cube d := by
    letI : IsProbabilityMeasure (Pc.map (fun ω : Completion d => ω.1)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hmapped : ∀ᵐ x ∂Pc.map (fun ω : Completion d => ω.1),
        x ∈ cube d := by
      apply (ae_mem_iff_measure_eq hcube.nullMeasurableSet).2
      simpa using hsupp
    exact (ae_map_iff (μ := Pc)
      (show AEMeasurable (fun ω : Completion d => ω.1) Pc by fun_prop)
      hcube).1 hmapped
  refine ⟨?_, ?_⟩
  · have hi :=
      (Causalean.Mathlib.Analysis.Calculus.CubeExtension.holderBallOn_congr
        heq).mp hg.1.toIntrinsic
    exact ⟨hi.regularity, hi.derivBound, hi.modulus⟩
  · filter_upwards [haecube, hg.2] with ω hω hmean
    exact (heq hω).symm.trans hmean

/-- Every admissible Hölder radius bounds the value at a point of the cube. [For the stated inputs and conditions](hyp:d,β,g,x,hx,hball), [the asserted conclusion holds](goal). -/
lemma holderFullNorm_ge_pointwise {d : ℕ} (β : ℝ)
    (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (hx : x ∈ cube d)
    (hball : ∃ L : ℝ, 0 ≤ L ∧ HolderBall β L g) :
    |g x| ≤ holderFullNorm β g := by
  unfold holderFullNorm
  apply le_csInf hball
  intro L hL
  have hzero := hL.2.derivBound 0 (Nat.zero_le _) (fun i : Fin 0 => i.elim0) x hx
  simpa [HolderDerivBound, HolderDerivBoundOn,
    Causalean.Mathlib.Analysis.Calculus.CubeExtension.coordJetOn,
    iteratedFDerivWithin_zero_apply] using hzero

/-- Constant responses satisfy Dorn's top-order seminorm condition. [For the stated inputs and conditions](hyp:d,β,L₀,c,hL₀), [the asserted conclusion holds](goal). -/
lemma dornTopDerivativeSeminorm_const {d : ℕ} (β L₀ c : ℝ)
    (hL₀ : 0 ≤ L₀) :
    DornTopDerivativeSeminorm (d := d) β L₀ (fun _ => c) := by
  constructor
  · fun_prop
  · intro α hα f hf x hx y hy
    have heq : Causalean.Mathlib.Analysis.Calculus.CubeExtension.coordJetOn
        (dornCube d) (∑ i, α i) (fun _ : Fin d → ℝ => c) f x =
        Causalean.Mathlib.Analysis.Calculus.CubeExtension.coordJetOn
        (dornCube d) (∑ i, α i) (fun _ : Fin d → ℝ => c) f y := by
      by_cases hn : (∑ i, α i) = 0
      · let P : ℕ → Prop := fun j => ∀ g : Fin j → Fin d,
          Causalean.Mathlib.Analysis.Calculus.CubeExtension.coordJetOn
            (dornCube d) j (fun _ => c) g x =
          Causalean.Mathlib.Analysis.Calculus.CubeExtension.coordJetOn
            (dornCube d) j (fun _ => c) g y
        have hPzero : P 0 := by
          intro g
          simp [Causalean.Mathlib.Analysis.Calculus.CubeExtension.coordJetOn,
            iteratedFDerivWithin_zero_apply]
        exact (hn.symm ▸ hPzero) f
      · unfold Causalean.Mathlib.Analysis.Calculus.CubeExtension.coordJetOn
        rw [iteratedFDerivWithin_const_of_ne hn]
        simp
    rw [heq, sub_self, abs_zero]
    positivity

/-- Under Dorn's normalized cube design, the stated pulled-back `L∞` loss is
bounded by the pointwise cube supremum used in `dornTransformedSupRisk`. [For the stated inputs and conditions](hyp:d,n,β,B,ω,P,μ₁,hcov), [the asserted conclusion holds](goal). -/
lemma dorn_eLpNorm_le_cubeSup {d n : ℕ} (β B : ℝ)
    (ω : Fin n → Obs d) (P : Measure (Obs d))
    (μ₁ : (Fin d → ℝ) → ℝ)
    (hcov : covariateLaw P =
      (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ • volume.restrict (dornCube d)) :
    eLpNorm (fun x =>
      equalCellEstimator β B ω (affineToCube x) - μ₁ x) ⊤
        (covariateLaw P) ≤
      ⨆ y : Fin d → ℝ, ⨆ (_ : y ∈ cube d),
        ENNReal.ofReal
          |equalCellEstimator β B ω y - transformedResponse μ₁ y| := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  have hDorn : MeasurableSet (dornCube d) := by
    unfold dornCube
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hsupp : ∀ᵐ x ∂covariateLaw P, x ∈ dornCube d := by
    rw [hcov]
    have hp : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) d
    apply (Measure.ae_ennreal_smul_measure_iff (by simp [hp])).2
    exact ae_restrict_mem hDorn
  filter_upwards [hsupp] with x hx
  have hy : affineToCube x ∈ cube d := (affineToCube_mem_cube_iff x).2 hx
  rw [Real.enorm_eq_ofReal_abs]
  have hresp : transformedResponse μ₁ (affineToCube x) = μ₁ x :=
    transformedResponse_affineToCube μ₁ x
  rw [← hresp]
  exact le_iSup_of_le (affineToCube x) (le_iSup_of_le hy le_rfl)

/-- Markov's inequality converts an expected ENNReal loss bound into the
corresponding real probability bound at the rescaled rate. [For the stated inputs and conditions](hyp:Ω,μ,Z,A,r,ε,hZ,hA,hr,hε,hint), [the asserted conclusion holds](goal). -/
lemma measurableLoss_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ≥0∞)
    (A r ε : ℝ) (hZ : AEMeasurable Z μ)
    (hA : 0 < A) (hr : 0 < r) (hε : 0 < ε)
    (hint : ∫⁻ ω, Z ω ∂μ ≤ ENNReal.ofReal (A * r)) :
    μ.real {ω | ENNReal.ofReal ((A / ε) * r) < Z ω} ≤ ε := by
  have hthreshold : 0 < (A / ε) * r := mul_pos (div_pos hA hε) hr
  have hmark := meas_ge_le_lintegral_div hZ
    (ENNReal.ofReal_pos.mpr hthreshold).ne' ENNReal.ofReal_ne_top
  have hdiv : (∫⁻ ω, Z ω ∂μ) /
      ENNReal.ofReal ((A / ε) * r) ≤ ENNReal.ofReal ε := by
    calc
      (∫⁻ ω, Z ω ∂μ) / ENNReal.ofReal ((A / ε) * r) ≤
          ENNReal.ofReal (A * r) / ENNReal.ofReal ((A / ε) * r) :=
        ENNReal.div_le_div_right hint _
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_div_of_pos hthreshold]
        congr 1
        field_simp
  rw [measureReal_def]
  apply ENNReal.toReal_le_of_le_ofReal hε.le
  have hsub : {ω | ENNReal.ofReal ((A / ε) * r) < Z ω} ⊆
      {ω | ENNReal.ofReal ((A / ε) * r) ≤ Z ω} :=
    fun ω hω => by
      change ENNReal.ofReal ((A / ε) * r) ≤ Z ω
      exact le_of_lt hω
  exact (measure_mono hsub).trans (hmark.trans hdiv)

/-- Enlarging the numerical tail constant preserves membership in the causal
model class. [For the stated inputs and conditions](hyp:d,β,B,L,C,C',c_f,γ,P,hCC',hP), [the asserted conclusion holds](goal). -/
lemma ModelClass.mono_tailConstant {d : ℕ} {β B L C C' c_f γ : ℝ}
    {P : Measure (Obs d)} (hCC' : C ≤ C')
    (hP : P ∈ ModelClass d β B L C c_f γ) :
    P ∈ ModelClass d β B L C' c_f γ := by
  obtain ⟨hparam, hγ, Pc, hPc, μ₁, e, hEq, hmodel⟩ := hP
  letI : IsProbabilityMeasure Pc := hPc
  have hparam' : ModelParameterDomain d β B L C' c_f :=
    ⟨hparam.1, hparam.2.1, hparam.2.2.1, hparam.2.2.2.1,
      hparam.2.2.2.2.1.trans hCC', hparam.2.2.2.2.2⟩
  have htail : GlobalPropensityTail (Pc.map observed) e C' γ := by
    refine ⟨hmodel.tail.1, ?_⟩
    intro t ht
    exact (hmodel.tail.2 t ht).trans
      (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg ht.1 _))
  exact ⟨hparam', hγ, Pc, hPc, μ₁, e, hEq,
    { hmodel with tail := htail }⟩

/-- Expected supremum loss of the transformed estimator against Dorn's
designated Gaussian response, with no model-membership premise. For [the stated inputs and conditions](hyp:d,n,β,B,P,μ₁), [the `dornTransformedSupRisk` object being defined](goal). -/
noncomputable def dornTransformedSupRisk (d n : ℕ) (β B : ℝ)
    (P : Measure (Obs d)) (μ₁ : (Fin d → ℝ) → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ⨆ x ∈ cube d,
    ENNReal.ofReal |equalCellEstimator β B ω x - transformedResponse μ₁ x|
    ∂Measure.pi (fun _ : Fin n => transformedDornLaw P)

/-- Once affine transport has supplied a causal-model witness with the
transported response, the Dorn risk is exactly the model-class estimator risk.
This isolates the chosen-representative issue from the Gaussian construction. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,μ₁,Pc,e,hEq,hmodel,hmem), [the asserted conclusion holds](goal). -/
lemma dornTransformedSupRisk_eq_estimatorSupRisk_of_globalTailModel
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) (μ₁ : (Fin d → ℝ) → ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (e : (Fin d → ℝ) → ℝ)
    (hEq : transformedDornLaw P = Pc.map observed)
    (hmodel : GlobalTailModel β B L C c_f γ Pc
      (transformedResponse μ₁) e)
    (hmem : transformedDornLaw P ∈ ModelClass d β B L C c_f γ) :
    dornTransformedSupRisk d n β B P μ₁ =
      estimatorSupRisk d n β B L C c_f γ (transformedDornLaw P) hmem := by
  unfold dornTransformedSupRisk estimatorSupRisk
  apply lintegral_congr
  intro ω
  apply iSup_congr
  intro x
  apply iSup_congr
  intro hx
  rw [responseOf_eq_given_model_response
    (transformedDornLaw P) hmem Pc (transformedResponse μ₁) e
    hEq hmodel x hx]

/-- The Gaussian arm clause identifies its conditional mean with the designated response. [For the stated inputs and conditions](hyp:d,β,q,M,σ,C,L₀,γ,P,μ₁,μ₀,e,hmodel), [the asserted conclusion holds](goal). -/
lemma dornRemaining_treatedMean_ae (d : ℕ) (β q M σ C L₀ γ : ℝ)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (μ₁ μ₀ e : (Fin d → ℝ) → ℝ)
    (hmodel : DornRemainingModel d β q M σ C L₀ γ P μ₁ μ₀ e) :
    ∀ᵐ x ∂covariateLaw P, (∫ y, y ∂armKernel P x true) = μ₁ x := by
  filter_upwards [hmodel.2.2.2.2.2.2.2] with x hx
  rw [hx.1]
  exact ProbabilityTheory.integral_id_gaussianReal

-- @node: prop:dorn-a3-free-corollary
/-- Conditional on the disclosed Dorn remaining-class scope, every law in the
remaining uniform Gaussian Hölder model transfers to the global-tail causal
class and inherits the expected-supremum rate; Markov gives the published
uniform-probability criterion. The strict Gaussian strip uses witness constants
selected separately for each `γ`, independent of the fixed upper-rate tuple.
The common response bound comes from Dorn's conditional moment clause, and
the full Hölder radius comes from fixed-cube interpolation of his
top-derivative seminorm. [For the stated inputs and conditions](hyp:d,hd,β,q,M,σ,C,L₀,γ_min,γ_max,hβ,hq,hM,hσ,hC,hL₀,hγmin,hγrange,_remaining_of_gate), [the asserted conclusion holds](goal). -/
theorem dorn_A3_free_corollary (d : ℕ) (hd : 1 ≤ d)
    (β q M σ C L₀ γ_min γ_max : ℝ)
    (hβ : 1 < β) (hq : 3 < q) (hM : 0 < M) (hσ : 0 < σ)
    (hC : 0 < C) (hL₀ : 0 < L₀)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max)
    (_remaining_of_gate :
      ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        DornRemainingClassSpec d β q M σ C L₀ γ) :
    let B := max M σ
    let L := dornCommonRadius d β M L₀
    0 < dornInterpolationConstant d β ∧ 0 < L ∧
      L ≤ dornInterpolationConstant d β * (M + L₀) ∧
    (∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
          (μ₁ μ₀ e : (Fin d → ℝ) → ℝ),
          (P, μ₁, μ₀, e) ∈ DornRemainingClass d β q M σ C L₀ γ →
          transformedDornLaw P ∈ ModelClass d β B L C 1 γ) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
      (∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
          (μ₁ μ₀ e : (Fin d → ℝ) → ℝ),
          (P, μ₁, μ₀, e) ∈ DornRemainingClass d β q M σ C L₀ γ →
          dornTransformedSupRisk d n β B P μ₁ ≤
            ENNReal.ofReal (K * oracleRate d n β γ)) ∧
      (∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∀ 𝔓 : Set (DornSourceLaw d),
          DornA12Family d β q M σ C L₀ γ 𝔓 →
          𝔓.Nonempty ∧ 𝔓 ⊆ DornRemainingClass d β q M σ C L₀ γ ∧
          ∀ n ≥ n₀,
            (⨆ z : {z : DornSourceLaw d // z ∈ 𝔓},
              dornTransformedSupRisk d n β B z.1.1 z.1.2.1) ≤
                ENNReal.ofReal (K * oracleRate d n β γ))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
          (μ₁ μ₀ e : (Fin d → ℝ) → ℝ),
          (P, μ₁, μ₀, e) ∈ DornRemainingClass d β q M σ C L₀ γ →
          (Measure.pi (fun _ : Fin n => transformedDornLaw P)).real
            {ω | ENNReal.ofReal (R * oracleRate d n β γ) <
              eLpNorm (fun x =>
                equalCellEstimator β B ω (affineToCube x) - μ₁ x)
                ⊤ (covariateLaw P)} ≤ ε) ∧
    (∀ (hd₂ : 2 ≤ d), ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
      ∃ (C' M' σ' L₀' : ℝ) (P : Measure (Obs d))
        (μ₁' μ₀' e : (Fin d → ℝ) → ℝ),
        0 < C' ∧ 0 < M' ∧ 0 < σ' ∧ 0 < L₀' ∧
        DornSelectedPropensity (dornCube d) P e ∧
      ∃ (hP : IsProbabilityMeasure P),
        @DornRemainingModel d β q M' σ' C' L₀' γ P hP
          μ₁' μ₀' e ∧
        ¬ DornA3 (dornCube d)
          ({(P, μ₁', μ₀', e)} : Set (DornSourceLaw d))) ∧
    (∀ (𝔓 : Set (DornSourceLaw d)) (μref : (Fin d → ℝ) → ℝ)
      (x₀ : Fin d → ℝ), 𝔓.Nonempty →
      (∀ z ∈ 𝔓, ∀ x, z.2.1 x = μref x) →
      ∀ (n : ℕ) (c r : ℝ), 0 < c → 0 < r →
        Causalean.Stat.minimaxValueENNReal
          (dornPointwiseMissRisk (n := n) 𝔓 x₀ c r) = 0) ∧
    (∀ γ : ℝ, 1 < γ → ∀ x₀ ∈ cube d,
      ∃ cγ : ℝ, 0 < cγ ∧
        ∀ n : ℕ, 1 ≤ n →
          ENNReal.ofReal (cγ * oracleRate d n β γ) ≤
            boundedPointwiseRisk d n β B L (max C 1) 1 γ x₀) := by
  dsimp
  have hMomentIntegrable :
      ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
          (μ₁ μ₀ e : (Fin d → ℝ) → ℝ),
          DornRemainingModel d β q M σ C L₀ γ P μ₁ μ₀ e →
            Integrable μ₁ (covariateLaw P) := by
    intro γ hγ P _ μ₁ μ₀ e hmodel
    have hcont : ContinuousOn μ₁ (dornCube d) :=
      hmodel.2.2.2.2.1.1.continuousOn
    have hcompact : IsCompact (dornCube d) := by
      unfold dornCube
      exact isCompact_univ_pi (fun _ => isCompact_Icc)
    have hint : Integrable μ₁ (volume.restrict (dornCube d)) :=
      hcont.integrableOn_compact hcompact
    rw [covariateLaw, hmodel.1]
    exact hint.smul_measure (by simp)
  have hMeanBound :
      ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
          (μ₁ μ₀ e : (Fin d → ℝ) → ℝ),
          DornRemainingModel d β q M σ C L₀ γ P μ₁ μ₀ e →
            ∀ x ∈ dornCube d, |μ₁ x| ≤ M := by
    intro γ hγ P _ μ₁ μ₀ e hmodel
    have hq1 : 1 ≤ q := by linarith
    have hq0 : 0 < q := by linarith
    have hae : ∀ᵐ x ∂covariateLaw P, |μ₁ x| ≤ M := by
      filter_upwards [hmodel.2.2.1, hmodel.2.2.2.2.2.2.2] with x hx hxg
      let κ := armKernel P x true
      haveI : IsProbabilityMeasure κ := by
        dsimp [κ]
        rw [hxg.1]
        exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
      have hiy : Integrable (fun y : ℝ => y) κ := by
        rw [show κ = gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩ from hxg.1]
        exact (ProbabilityTheory.memLp_id_gaussianReal' 1 (by simp)).integrable (by norm_num)
      have hia : Integrable (fun y : ℝ => |y|) κ := hiy.abs
      have hj : (∫ y, |y| ∂κ) ^ q ≤ ∫ y, |y| ^ q ∂κ := by
        apply ConvexOn.map_integral_le (convexOn_rpow hq1)
        · exact Real.continuous_rpow_const hq0.le |>.continuousOn
        · exact isClosed_Ici
        · filter_upwards [] with y
          exact abs_nonneg y
        · exact hia
        · exact hx.1
      have hmean : |μ₁ x| ≤ ∫ y, |y| ∂κ := by
        rw [← ProbabilityTheory.integral_id_gaussianReal (μ := μ₁ x)
          (v := ⟨σ ^ 2, sq_nonneg σ⟩)]
        change |∫ y, y ∂gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩| ≤ _
        rw [show κ = gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩ from hxg.1]
        exact abs_integral_le_integral_abs
      have hpow : |μ₁ x| ^ q ≤ M ^ q :=
        (Real.rpow_le_rpow (abs_nonneg _) hmean hq0.le).trans (hj.trans hx.2)
      exact (Real.rpow_le_rpow_iff (abs_nonneg _) (le_of_lt hM) hq0).mp hpow
    have haevol : ∀ᵐ x ∂volume.restrict (dornCube d), |μ₁ x| ≤ M := by
      rw [covariateLaw, hmodel.1] at hae
      exact (Measure.ae_ennreal_smul_measure_iff (by simp :
        (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ ≠ 0)).mp hae
    have heqae : (fun x => max (|μ₁ x| - M) 0) =ᵐ[volume.restrict (dornCube d)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [haevol] with x hx
      simp [max_eq_right (sub_nonpos.mpr hx)]
    have hclosure : dornCube d ⊆ closure (interior (dornCube d)) := by
      intro y hy
      change y ∈ closure (interior (Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1)))
      rw [interior_pi_set Set.finite_univ, closure_pi_set]
      intro i hi
      rw [closure_interior_Icc (by norm_num : (-1 : ℝ) ≠ 1)]
      exact (show y ∈ Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) from hy) i hi
    have hcont : ContinuousOn (fun x => max (|μ₁ x| - M) 0) (dornCube d) :=
      ((hmodel.2.2.2.2.1.1.continuousOn.abs.sub continuousOn_const).sup' continuousOn_const)
    have heq := Measure.eqOn_of_ae_eq heqae hcont continuousOn_const hclosure
    intro x hx
    have hx' := heq hx
    dsimp at hx'
    have : |μ₁ x| - M ≤ 0 := by
      have := le_max_left (|μ₁ x| - M) 0
      rw [hx'] at this
      exact this
    linarith
  obtain ⟨Kcube, hKcube, hCubeCompletion⟩ :=
    fixedCube_holder_completion d hd β hβ
  have hCompletedResponse :
      ∀ (g : (Fin d → ℝ) → ℝ),
        DornTopDerivativeSeminorm β L₀ g →
        (∀ x ∈ dornCube d, |g x| ≤ M) →
        HolderBall β (Kcube * (M + L₀)) (transformedResponse g) := by
    intro g hg hbound
    exact hCubeCompletion M L₀ g (le_of_lt hM) (le_of_lt hL₀) hg hbound
  have hCompletedModelResponse :
      ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
          (μ₁ μ₀ e : (Fin d → ℝ) → ℝ),
          DornRemainingModel d β q M σ C L₀ γ P μ₁ μ₀ e →
          HolderBall β (Kcube * (M + L₀))
            (transformedResponse μ₁) := by
    intro γ hγ P _ μ₁ μ₀ e hmodel
    exact hCompletedResponse μ₁ hmodel.2.2.2.2.1
      (hMeanBound γ hγ P μ₁ μ₀ e hmodel)
  have hRadius :
      0 < dornInterpolationConstant d β ∧
      0 < dornCommonRadius d β M L₀ ∧
      dornCommonRadius d β M L₀ ≤
        dornInterpolationConstant d β * (M + L₀) := by
    -- `hCompletedResponse` bounds every term in the defining supremum.
    -- What remains is the order-completeness bookkeeping for `sInf`/`sSup`.
    have hUniformRadius :
        ∀ (g : (Fin d → ℝ) → ℝ),
          DornTopDerivativeSeminorm β L₀ g →
          (∀ x ∈ dornCube d, |g x| ≤ M) →
          holderFullNorm β (transformedResponse g) ≤
            Kcube * (M + L₀) := by
      intro g hg hbound
      have hball := hCompletedResponse g hg hbound
      unfold holderFullNorm
      apply csInf_le
      · exact ⟨0, by intro r hr; exact hr.1⟩
      · exact ⟨le_of_lt (mul_pos hKcube (add_pos hM hL₀)), hball⟩
    let Sinterp : Set ℝ := {r | ∃ (M' L' : ℝ) (g : (Fin d → ℝ) → ℝ),
      0 < M' ∧ 0 < L' ∧ DornTopDerivativeSeminorm β L' g ∧
      (∀ x ∈ dornCube d, |g x| ≤ M') ∧
      r = holderFullNorm β (transformedResponse g) / (M' + L')}
    let Scommon : Set ℝ := {r | ∃ g : (Fin d → ℝ) → ℝ,
      DornTopDerivativeSeminorm β L₀ g ∧
      (∀ x ∈ dornCube d, |g x| ≤ M) ∧
      r = holderFullNorm β (transformedResponse g)}
    have hUpperNorm : ∀ (M' L' : ℝ) (g : (Fin d → ℝ) → ℝ),
        0 ≤ M' → 0 ≤ L' → DornTopDerivativeSeminorm β L' g →
        (∀ x ∈ dornCube d, |g x| ≤ M') →
        holderFullNorm β (transformedResponse g) ≤ Kcube * (M' + L') := by
      intro M' L' g hM' hL' hg hb
      unfold holderFullNorm
      apply csInf_le
      · exact ⟨0, by intro r hr; exact hr.1⟩
      · exact ⟨mul_nonneg (le_of_lt hKcube) (add_nonneg hM' hL'),
          hCubeCompletion M' L' g hM' hL' hg hb⟩
    have hBddI : BddAbove Sinterp := by
      refine ⟨Kcube, ?_⟩
      intro r hr
      obtain ⟨M', L', g, hM', hL', hg, hb, rfl⟩ := hr
      have hsum : 0 < M' + L' := add_pos hM' hL'
      exact (div_le_iff₀ hsum).2 (hUpperNorm M' L' g
        hM'.le hL'.le hg hb)
    have hBddC : BddAbove Scommon := by
      refine ⟨Kcube * (M + L₀), ?_⟩
      intro r hr
      obtain ⟨g, hg, hb, rfl⟩ := hr
      exact hUniformRadius g hg hb
    have hzeroCube : (fun _ : Fin d => (0 : ℝ)) ∈ cube d := by
      exact Set.mem_univ_pi.mpr (fun i => by norm_num)
    have hConst1 : DornTopDerivativeSeminorm β 1
        (fun _ : Fin d → ℝ => 1) :=
      dornTopDerivativeSeminorm_const β 1 1 (by norm_num)
    have hBall1 : HolderBall β (Kcube * (1 + 1))
        (transformedResponse (fun _ : Fin d → ℝ => 1)) := by
      apply hCubeCompletion 1 1 (fun _ => 1) (by norm_num) (by norm_num) hConst1
      intro x hx
      norm_num
    have hNorm1 : 1 ≤ holderFullNorm β
        (transformedResponse (fun _ : Fin d → ℝ => 1)) := by
      have h := holderFullNorm_ge_pointwise β
        (transformedResponse (fun _ : Fin d → ℝ => 1))
        (fun _ => 0) hzeroCube
        ⟨Kcube * (1 + 1), by positivity, hBall1⟩
      simpa [transformedResponse] using h
    have hMemI : holderFullNorm β
        (transformedResponse (fun _ : Fin d → ℝ => 1)) / (1 + 1) ∈ Sinterp := by
      refine ⟨1, 1, (fun _ => 1), by norm_num, by norm_num, hConst1, ?_, rfl⟩
      intro x hx
      norm_num
    have hInterpPos : 0 < sSup Sinterp := by
      have hratio : 0 < holderFullNorm β
          (transformedResponse (fun _ : Fin d → ℝ => 1)) / (1 + 1) :=
        div_pos (lt_of_lt_of_le zero_lt_one hNorm1) (by norm_num)
      exact lt_of_lt_of_le hratio (le_csSup hBddI hMemI)
    have hConstM : DornTopDerivativeSeminorm β L₀
        (fun _ : Fin d → ℝ => M) :=
      dornTopDerivativeSeminorm_const β L₀ M hL₀.le
    have hBallM : HolderBall β (Kcube * (M + L₀))
        (transformedResponse (fun _ : Fin d → ℝ => M)) := by
      apply hCompletedResponse (fun _ => M) hConstM
      intro x hx
      simp [abs_of_pos hM]
    have hNormM : M ≤ holderFullNorm β
        (transformedResponse (fun _ : Fin d → ℝ => M)) := by
      have h := holderFullNorm_ge_pointwise β
        (transformedResponse (fun _ : Fin d → ℝ => M))
        (fun _ => 0) hzeroCube
        ⟨Kcube * (M + L₀), by positivity, hBallM⟩
      simpa [transformedResponse, abs_of_pos hM] using h
    have hMemC : holderFullNorm β
        (transformedResponse (fun _ : Fin d → ℝ => M)) ∈ Scommon := by
      refine ⟨(fun _ => M), hConstM, ?_, rfl⟩
      intro x hx
      simp [abs_of_pos hM]
    have hCommonPos : 0 < sSup Scommon :=
      lt_of_lt_of_le (lt_of_lt_of_le hM hNormM)
        (le_csSup hBddC hMemC)
    have hCompare : sSup Scommon ≤ sSup Sinterp * (M + L₀) := by
      apply csSup_le ⟨_, hMemC⟩
      intro r hr
      obtain ⟨g, hg, hb, rfl⟩ := hr
      have hMem : holderFullNorm β (transformedResponse g) / (M + L₀) ∈
          Sinterp := by
        exact ⟨M, L₀, g, hM, hL₀, hg, hb, rfl⟩
      exact (div_le_iff₀ (add_pos hM hL₀)).mp (le_csSup hBddI hMem)
    change 0 < sSup Sinterp ∧ 0 < sSup Scommon ∧
      sSup Scommon ≤ sSup Sinterp * (M + L₀)
    exact ⟨hInterpPos, hCommonPos, hCompare⟩
  have hStrict :
      ∀ (hd₂ : 2 ≤ d), ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∃ (C' M' σ' L₀' : ℝ) (P : Measure (Obs d))
          (μ₁' μ₀' e : (Fin d → ℝ) → ℝ),
          0 < C' ∧ 0 < M' ∧ 0 < σ' ∧ 0 < L₀' ∧
          DornSelectedPropensity (dornCube d) P e ∧
          ∃ (hP : IsProbabilityMeasure P),
            @DornRemainingModel d β q M' σ' C' L₀' γ P hP
              μ₁' μ₀' e ∧
              ¬ DornA3 (dornCube d)
                ({(P, μ₁', μ₀', e)} : Set (DornSourceLaw d)) := by
    -- The strip exponent and exact construction are proof witnesses, not part
    -- of the corollary's public existence claim.
    have hConstruct :
        ∀ (hd₂ : 2 ≤ d), ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
          ∃ (a C' M' σ' L₀' : ℝ) (P : Measure (Obs d))
            (μ₁' μ₀' e : (Fin d → ℝ) → ℝ),
            1 < a ∧ a < 1 + d / (γ - 1) ∧
            0 < C' ∧ 0 < M' ∧ 0 < σ' ∧ 0 < L₀' ∧
            P = gaussianThinStripOriginal d hd₂ γ a σ' ∧
            μ₁' = (fun _ => 0) ∧ μ₀' = (fun _ => 0) ∧
            e = gaussianStripPropensity d hd₂ γ a ∧
            DornSelectedPropensity (dornCube d) P e ∧
            ∃ (hP : IsProbabilityMeasure P),
              @DornRemainingModel d β q M' σ' C' L₀' γ P hP
                μ₁' μ₀' e ∧
                ¬ DornA3 (dornCube d)
                  ({(P, μ₁', μ₀', e)} : Set (DornSourceLaw d)) := by
      intro hd₂ γ hγmem
      have hγ : 1 < γ := hγmin.trans_le hγmem.1
      have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hd₂)
      have hden : 0 < γ - 1 := sub_pos.mpr hγ
      let δ : ℝ := d / (γ - 1)
      have hδ : 0 < δ := div_pos hdpos hden
      let a : ℝ := 1 + δ / 2
      have ha : 1 < a := by dsimp [a]; linarith
      have ha' : a < 1 + d / (γ - 1) := by
        dsimp [a, δ]
        have : 0 < (d : ℝ) / (γ - 1) := div_pos hdpos hden
        linarith
      obtain ⟨M', hM', hMint, hMbound⟩ :=
        exists_gaussianReal_qMoment_radius q 1 (by linarith [hq])
      let C' : ℝ := ((3 / 4 : ℝ) ^ (γ - 1))⁻¹
      have hC' : 0 < C' := by
        dsimp [C']
        exact inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
      let P : Measure (Obs d) := gaussianThinStripOriginal d hd₂ γ a 1
      let e : (Fin d → ℝ) → ℝ := gaussianStripPropensity d hd₂ γ a
      let μ₁' : (Fin d → ℝ) → ℝ := fun _ => 0
      let μ₀' : (Fin d → ℝ) → ℝ := fun _ => 0
      have hP : IsProbabilityMeasure P := by
        dsimp [P]
        exact gaussianThinStripOriginal_probability d hd₂ γ a 1 hγ
      letI : IsProbabilityMeasure P := hP
      have hSelected : DornSelectedPropensity (dornCube d) P e := by
        dsimp [P, e]
        exact gaussianThinStripOriginal_selected d hd₂ γ a 1 hγ
      have harms : ∀ᵐ x ∂covariateLaw P,
          armKernel P x true = gaussianReal 0 ⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ ∧
          armKernel P x false = gaussianReal 0 ⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ := by
        simpa [P] using
          gaussianThinStripOriginal_armKernels_ae d hd₂ γ a 1 hγ
      have hModel : @DornRemainingModel d β q M' 1 C' 1 γ P hP
          μ₁' μ₀' e := by
        refine ⟨?_, hSelected.toA12, ?_, ?_, ?_, ?_, ?_, harms⟩
        · dsimp [P]
          exact gaussianThinStripOriginal_covariateLaw d hd₂ γ a 1 hγ
        · filter_upwards [harms] with x hx
          rw [hx.1]
          exact ⟨hMint, hMbound⟩
        · simp [μ₁', hM'.le]
        · exact dornZero_topDerivativeSeminorm d β 1 (by norm_num)
        · exact dornZero_topDerivativeSeminorm d β 1 (by norm_num)
        · dsimp [P, e, C']
          exact gaussianThinStripOriginal_globalTail d hd₂ γ a 1 hγ
      have hNot : ¬ DornA3 (dornCube d)
          ({(P, μ₁', μ₀', e)} : Set (DornSourceLaw d)) := by
        dsimp [P, μ₁', μ₀', e]
        exact gaussianThinStripOriginal_not_dornA3 d hd₂ γ a 1 hγ ha
      exact ⟨a, C', M', 1, 1, P, μ₁', μ₀', e,
        ha, ha', hC', hM', by norm_num, by norm_num,
        rfl, rfl, rfl, rfl, hSelected, hP, hModel, hNot⟩
    intro hd₂ γ hγ
    obtain ⟨a, C', M', σ', L₀', P, μ₁', μ₀', e,
      ha, ha', hC', hM', hσ', hL₀', hPdef, hμ₁, hμ₀, he, hSelected,
      hP, hModel, hNotA3⟩ := hConstruct hd₂ γ hγ
    exact ⟨C', M', σ', L₀', P, μ₁', μ₀', e,
      hC', hM', hσ', hL₀', hSelected, hP, hModel, hNotA3⟩
  have hTransfer :
      ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
          (μ₁ μ₀ e : (Fin d → ℝ) → ℝ),
          (P, μ₁, μ₀, e) ∈ DornRemainingClass d β q M σ C L₀ γ →
          transformedDornLaw P ∈ ModelClass d β (max M σ)
              (dornCommonRadius d β M L₀) C 1 γ ∧
            ∃ (Pc : Measure (Completion d)) (hPc : IsProbabilityMeasure Pc)
              (eT : (Fin d → ℝ) → ℝ),
              transformedDornLaw P = Pc.map observed ∧
              @GlobalTailModel d β (max M σ)
                (dornCommonRadius d β M L₀) C 1 γ Pc hPc
                (transformedResponse μ₁) eT := by
    intro γ hγ P hP μ₁ μ₀ e hmem
    classical
    obtain ⟨hP', hmodel'⟩ := hmem
    have hmodel : DornRemainingModel d β q M σ C L₀ γ P μ₁ μ₀ e := by
      exact hmodel'
    obtain ⟨_, he, hselected⟩ := hmodel.2.1
    have hDorn : MeasurableSet (dornCube d) := by
      unfold dornCube
      exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
    let μ₁m : (Fin d → ℝ) → ℝ := (dornCube d).piecewise μ₁ (fun _ => 0)
    let μ₀m : (Fin d → ℝ) → ℝ := (dornCube d).piecewise μ₀ (fun _ => 0)
    let ec : (Fin d → ℝ) → ℝ := gaussianPropensityClamp ∘ e
    have hμ₁m : Measurable μ₁m := by
      dsimp [μ₁m]
      exact hmodel.2.2.2.2.1.1.continuousOn.measurable_piecewise
        continuous_const.continuousOn hDorn
    have hμ₀m : Measurable μ₀m := by
      dsimp [μ₀m]
      exact hmodel.2.2.2.2.2.1.1.continuousOn.measurable_piecewise
        continuous_const.continuousOn hDorn
    have hec : Measurable ec := by
      dsimp [ec, gaussianPropensityClamp, Function.comp_def]
      exact measurable_const.max (measurable_const.min he)
    have hecValid : ∀ x, ec x ∈ Set.Icc (0 : ℝ) 1 :=
      fun x => gaussianPropensityClamp_mem_Icc (e x)
    have hsupp : ∀ᵐ x ∂covariateLaw P, x ∈ dornCube d := by
      change ∀ᵐ x ∂P.map Prod.fst, x ∈ dornCube d
      rw [hmodel.1]
      have hp : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) d
      apply (Measure.ae_ennreal_smul_measure_iff (by simp [hp])).2
      exact ae_restrict_mem hDorn
    have hec_eq : ec =ᵐ[covariateLaw P] e := by
      filter_upwards [hselected] with x hx
      exact gaussianPropensityClamp_eq_self ⟨hx.2.1.le, hx.2.2.le⟩
    have hμ₁m_eq : μ₁m =ᵐ[covariateLaw P] μ₁ := by
      filter_upwards [hsupp] with x hx
      simp [μ₁m, hx]
    have hμ₀m_eq : μ₀m =ᵐ[covariateLaw P] μ₀ := by
      filter_upwards [hsupp] with x hx
      simp [μ₀m, hx]
    have hselectedC : ∀ᵐ x ∂covariateLaw P,
        ec x = propensity P x ∧ 0 < ec x ∧ ec x < 1 := by
      filter_upwards [hselected, hec_eq] with x hx heqx
      simpa [heqx] using hx
    have harmsM : ∀ᵐ x ∂covariateLaw P,
        armKernel P x true =
            gaussianReal (μ₁m x) ⟨σ ^ 2, sq_nonneg σ⟩ ∧
          armKernel P x false =
            gaussianReal (μ₀m x) ⟨σ ^ 2, sq_nonneg σ⟩ := by
      filter_upwards [hmodel.2.2.2.2.2.2.2, hμ₁m_eq, hμ₀m_eq]
        with x hx h1 h0
      simpa [h1, h0] using hx
    let mu : Measure (Fin d → ℝ) := covariateLaw P
    let Pc : Measure (Completion d) :=
      mu.bind (gaussianCompletionAt σ ec μ₀m μ₁m)
    let F : Completion d → Completion d := fun ω =>
      (affineToCube ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2)
    let PcA : Measure (Completion d) := Pc.map F
    have hk : Measurable (gaussianCompletionAt σ ec μ₀m μ₁m) :=
      gaussianCompletionAt_measurable σ ec μ₀m μ₁m hec hμ₀m hμ₁m
    have hpoint : ∀ x, IsProbabilityMeasure
        (gaussianCompletionAt σ ec μ₀m μ₁m x) := by
      intro x
      letI := realBernoulli_probability (ec x) (hecValid x)
      letI : IsProbabilityMeasure
          (gaussianReal (μ₀m x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
        ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
      letI : IsProbabilityMeasure
          (gaussianReal (μ₁m x) ⟨σ ^ 2, sq_nonneg σ⟩) :=
        ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
      unfold gaussianCompletionAt
      apply Measure.isProbabilityMeasure_map
      have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
          if z.1 then z.2.2 else z.2.1) :=
        Measurable.ite (measurable_fst (MeasurableSet.singleton true))
          (by fun_prop) (by fun_prop)
      fun_prop (disch := assumption)
    letI : IsProbabilityMeasure mu := by
      dsimp [mu, covariateLaw]
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure Pc := by
      dsimp [Pc]
      exact isProbabilityMeasure_bind hk.aemeasurable
        (Filter.Eventually.of_forall hpoint)
    have hF : Measurable F := by
      dsimp [F]
      have hx : Measurable (fun ω : Completion d => affineToCube ω.1) :=
        affineToCube_measurable.comp measurable_fst
      fun_prop (disch := assumption)
    letI : IsProbabilityMeasure PcA := by
      dsimp [PcA]
      exact Measure.isProbabilityMeasure_map hF.aemeasurable
    have hobsEq : PcA.map observed = transformedDornLaw P := by
      dsimp [PcA, Pc, mu, F]
      exact gaussianCompletionBind_affine_observed_eq_of_selected
        P σ ec μ₀m μ₁m hec hμ₀m hμ₁m hecValid hselectedC harmsM
    have hC1 : 1 ≤ C := by
      have he_le : ∀ᵐ x ∂covariateLaw P, e x ≤ 1 := by
        filter_upwards [hselected] with x hx
        exact hx.2.2.le
      have hmass : (covariateLaw P).real {x | e x ≤ 1} = 1 := by
        rw [Measure.real]
        have hm : covariateLaw P {x | e x ≤ 1} =
            covariateLaw P Set.univ :=
          (ae_iff_measure_eq
            (measurableSet_le he measurable_const).nullMeasurableSet).mp he_le
        rw [hm, measure_univ]
        simp
      have ht := hmodel.2.2.2.2.2.2.1.2 1 (by constructor <;> norm_num)
      rw [hmass] at ht
      simpa using ht
    have hparam : ModelParameterDomain d β (max M σ)
        (dornCommonRadius d β M L₀) C 1 := by
      exact ⟨hd, hβ, lt_of_lt_of_le hM (le_max_left _ _), hRadius.2.1,
        hC1, by norm_num, by norm_num⟩
    have hγgt : 1 < γ := lt_of_lt_of_le hγmin hγ.1
    letI : IsProbabilityMeasure (transformedDornLaw P) :=
      transformedDornLaw_probability P
    have hcubeFields := transformedDornLaw_cube_fields P hmodel.1
    have htail := transformedDornLaw_globalTail P e C γ he
      hmodel.2.2.2.2.2.2.1
    have hmean : ∀ᵐ y ∂covariateLaw (transformedDornLaw P),
        |transformedResponse μ₁ y| ≤ max M σ := by
      rw [transformedDornLaw_covariate_eq_cubeVolume P hmodel.1]
      filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))]
        with y hy
      have hx : (fun i => 2 * y i - 1) ∈ dornCube d := by
        intro i hi
        have hyi := hy i (Set.mem_univ i)
        constructor <;> dsimp at hyi ⊢ <;> linarith [hyi.1, hyi.2]
      exact (hMeanBound γ hγ P μ₁ μ₀ e hmodel (fun i => 2 * y i - 1) hx).trans
        (le_max_left _ _)
    have houtcome := transformedDornLaw_boundedGaussianOutcome
      P σ (max M σ) e μ₀ μ₁ (le_of_lt (lt_of_lt_of_le hM (le_max_left _ _)))
      (by rw [abs_of_pos hσ]; exact le_max_right _ _)
      hselected hmodel.2.2.2.2.2.2.2 hmean
    have hsourceMean := gaussianCompletionBind_treatedConditionalMean
      mu σ ec μ₀m μ₁m hec hμ₀m hμ₁m hecValid
      (gaussianCompletionBind_treatedPotential_integrable
        mu σ ec μ₀m μ₁m hec hμ₀m hμ₁m hecValid
        ((hMomentIntegrable γ hγ P μ₁ μ₀ e hmodel).congr hμ₁m_eq.symm))
    have hYint := gaussianCompletionBind_treatedPotential_integrable
      mu σ ec μ₀m μ₁m hec hμ₀m hμ₁m hecValid
      ((hMomentIntegrable γ hγ P μ₁ μ₀ e hmodel).congr hμ₁m_eq.symm)
    have htargetMean := affineCompletionMap_treatedConditionalMean
      Pc μ₁m hsourceMean hYint
    have hballK := hCompletedModelResponse γ hγ P μ₁ μ₀ e hmodel
    have hnormBall := holderBall_holderFullNorm β (transformedResponse μ₁)
      ⟨Kcube * (M + L₀), by positivity, hballK⟩
    have hnormLe : holderFullNorm β (transformedResponse μ₁) ≤
        dornCommonRadius d β M L₀ := by
      unfold dornCommonRadius
      apply le_csSup
      · refine ⟨Kcube * (M + L₀), ?_⟩
        intro r hr
        obtain ⟨g, hg, hb, rfl⟩ := hr
        unfold holderFullNorm
        apply csInf_le
        · exact ⟨0, fun _ h => h.1⟩
        · exact ⟨le_of_lt (mul_pos hKcube (add_pos hM hL₀)),
            hCompletedResponse g hg hb⟩
      · exact ⟨μ₁, hmodel.2.2.2.2.1,
          hMeanBound γ hγ P μ₁ μ₀ e hmodel, rfl⟩
    have hball := hnormBall.mono_radius hnormLe
    have hballM : HolderBall β (dornCommonRadius d β M L₀)
        (transformedResponse μ₁m) := by
      have heq : Set.EqOn (transformedResponse μ₁)
          (transformedResponse μ₁m) (cube d) := by
        intro y hy
        have hx : (fun i => 2 * y i - 1) ∈ dornCube d := by
          intro i hi
          have hyi := hy i (Set.mem_univ i)
          constructor <;> dsimp at hyi ⊢ <;> linarith [hyi.1, hyi.2]
        simp [transformedResponse, μ₁m, hx]
      have hi := (Causalean.Mathlib.Analysis.Calculus.CubeExtension.holderBallOn_congr
        heq).mp hball.toIntrinsic
      exact ⟨hi.regularity, hi.derivBound, hi.modulus⟩
    have hsmoothM : HolderResponse PcA (transformedResponse μ₁m) β
        (dornCommonRadius d β M L₀) := ⟨hballM, htargetMean⟩
    have hsmooth : HolderResponse PcA (transformedResponse μ₁) β
        (dornCommonRadius d β M L₀) := by
      apply hsmoothM.congr_on_cube
      · intro y hy
        have hx : (fun i => 2 * y i - 1) ∈ dornCube d := by
          intro i hi
          have hyi := hy i (Set.mem_univ i)
          constructor <;> dsimp at hyi ⊢ <;> linarith [hyi.1, hyi.2]
        simp [transformedResponse, μ₁m, hx]
      · dsimp [PcA, F]
        rw [Measure.map_map measurable_fst hF]
        change (Pc.map (affineToCube ∘ fun ω : Completion d => ω.1))
          (cube d) = 1
        rw [← Measure.map_map affineToCube_measurable measurable_fst]
        rw [show Pc = mu.bind (gaussianCompletionAt σ ec μ₀m μ₁m) from rfl]
        rw [gaussianCompletionBind_covariate_marginal_ae
          mu σ ec μ₀m μ₁m hec hμ₀m hμ₁m
            (Filter.Eventually.of_forall hecValid)]
        change (mu.map affineToCube) (cube d) = 1
        rw [show mu = covariateLaw P from rfl,
          show covariateLaw P =
            (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ •
              volume.restrict (dornCube d) from hmodel.1,
          normalizedDornVolume_map_affineToCube]
        simp [cube, Real.volume_Icc_pi]
    have hglobal : GlobalTailModel β (max M σ)
        (dornCommonRadius d β M L₀) C 1 γ PcA
        (transformedResponse μ₁) (transformedResponse e) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hsmooth⟩
      · rw [hobsEq]
        exact hcubeFields.1
      · rw [hobsEq]
        exact hcubeFields.2.1
      · rw [hobsEq]
        exact hcubeFields.2.2
      · exact affineCompletionMap_consistency Pc
          (gaussianCompletionBind_consistency mu σ ec μ₀m μ₁m hec hμ₀m hμ₁m)
      · exact affineCompletionMap_condExchangeable Pc
          (gaussianCompletionBind_condExchangeable mu σ ec μ₀m μ₁m
            hec hμ₀m hμ₁m hecValid)
      · simpa only [hobsEq] using htail
      · simpa only [hobsEq] using houtcome
    exact ⟨⟨hparam, hγgt, PcA, inferInstance, transformedResponse μ₁,
      transformedResponse e, hobsEq.symm, hglobal⟩,
      PcA, inferInstance, transformedResponse e, hobsEq.symm, hglobal⟩
  have hUpperWitness : ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
          ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
            ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
              (μ₁ μ₀ e : (Fin d → ℝ) → ℝ),
              (P, μ₁, μ₀, e) ∈ DornRemainingClass d β q M σ C L₀ γ →
              dornTransformedSupRisk d n β (max M σ) P μ₁ ≤
                ENNReal.ofReal (K * oracleRate d n β γ) := by
      have hBmax : 0 < max M σ := lt_of_lt_of_le hM (le_max_left _ _)
      have hCmax : 1 ≤ max C 1 := le_max_right _ _
      obtain ⟨K, hK, n₀, hUpperModel⟩ :=
        (adaptive_minimax_rate d β (max M σ)
          (dornCommonRadius d β M L₀) (max C 1) 1 γ_min γ_max
          (Nat.lt_of_lt_of_le Nat.zero_lt_one hd) hβ hBmax hRadius.2.1
          hCmax ⟨by norm_num, by norm_num⟩ hγmin hγrange).1
      refine ⟨K, hK, n₀, ?_⟩
      intro n hn γ hγ P hP μ₁ μ₀ e hmem
      have hbase := hTransfer γ hγ P μ₁ μ₀ e hmem
      have hmemC := hbase.1
      obtain ⟨Pc, hPc, eT, hEq, hmodelC⟩ := hbase.2
      letI : IsProbabilityMeasure Pc := hPc
      have htrans : transformedDornLaw P ∈ ModelClass d β (max M σ)
          (dornCommonRadius d β M L₀) (max C 1) 1 γ :=
        ModelClass.mono_tailConstant (le_max_left C 1) hmemC
      have htailMax : GlobalPropensityTail (Pc.map observed) eT (max C 1) γ := by
        refine ⟨hmodelC.tail.1, ?_⟩
        intro t ht
        exact (hmodelC.tail.2 t ht).trans
          (mul_le_mul_of_nonneg_right (le_max_left C 1)
            (Real.rpow_nonneg ht.1 _))
      have hmodelMax : GlobalTailModel β (max M σ)
          (dornCommonRadius d β M L₀) (max C 1) 1 γ Pc
          (transformedResponse μ₁) eT := { hmodelC with tail := htailMax }
      letI : IsProbabilityMeasure (transformedDornLaw P) :=
        transformedDornLaw_probability P
      calc
        dornTransformedSupRisk d n β (max M σ) P μ₁ =
            estimatorSupRisk d n β (max M σ)
              (dornCommonRadius d β M L₀) (max C 1) 1 γ
              (transformedDornLaw P) htrans :=
          dornTransformedSupRisk_eq_estimatorSupRisk_of_globalTailModel
            P μ₁ Pc eT hEq hmodelMax htrans
        _ ≤ ENNReal.ofReal (K * oracleRate d n β γ) :=
          hUpperModel n hn γ hγ (transformedDornLaw P) htrans
  refine ⟨hRadius.1, hRadius.2.1, hRadius.2.2,
    (fun γ hγ P _ μ₁ μ₀ e hmem => (hTransfer γ hγ P μ₁ μ₀ e hmem).1),
    ?_, ?_, hStrict, ?_, ?_⟩
  · obtain ⟨K, hK, n₀, hUpper⟩ := hUpperWitness
    refine ⟨K, hK, n₀, hUpper, ?_⟩
    intro γ hγ 𝔓 hA12
    have hγgt : 1 < γ := lt_of_lt_of_le hγmin hγ.1
    obtain ⟨hnonempty, hsub⟩ :=
      ((_remaining_of_gate γ hγ) hd (by linarith : 0 < β)
        hq hM hσ hC hL₀ hγgt 𝔓).mp hA12
    refine ⟨hnonempty, hsub, ?_⟩
    intro n hn
    apply iSup_le
    intro z
    obtain ⟨hP, _⟩ := hsub z.2
    letI : IsProbabilityMeasure z.1.1 := hP
    exact hUpper n hn γ hγ z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 (hsub z.2)
  · intro ε hε
    obtain ⟨K, hK, n₀, hUpper⟩ := hUpperWitness
    refine ⟨K / ε, div_pos hK hε, max n₀ 1, ?_⟩
    intro n hn γ hγ P hP μ₁ μ₀ e hmem
    have hn₀ : n₀ ≤ n := (le_max_left n₀ 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right n₀ 1).trans hn
    have hr : 0 < oracleRate d n β γ := by
      unfold oracleRate oracleMesh
      positivity
    let Z : (Fin n → Obs d) → ℝ≥0∞ := fun ω =>
      ⨆ y : Fin d → ℝ, ⨆ (_ : y ∈ cube d),
        ENNReal.ofReal
          |equalCellEstimator β (max M σ) ω y - transformedResponse μ₁ y|
    have hcont : ContinuousOn (transformedResponse μ₁) (cube d) :=
      (hCompletedModelResponse γ hγ P μ₁ μ₀ e hmem.2).regularity.continuousOn
    have hZ : AEMeasurable Z
        (Measure.pi (fun _ : Fin n => transformedDornLaw P)) :=
      (equalCellEstimator_cubeSup_measurable β (max M σ)
        (transformedResponse μ₁) hcont).aemeasurable
    have hint : ∫⁻ ω, Z ω
          ∂Measure.pi (fun _ : Fin n => transformedDornLaw P) ≤
        ENNReal.ofReal (K * oracleRate d n β γ) := by
      simpa [Z, dornTransformedSupRisk] using
        hUpper n hn₀ γ hγ P μ₁ μ₀ e hmem
    letI : IsProbabilityMeasure (transformedDornLaw P) :=
      transformedDornLaw_probability P
    have hmark := measurableLoss_probability_le
      (Measure.pi (fun _ : Fin n => transformedDornLaw P)) Z K
      (oracleRate d n β γ) ε hZ hK hr hε hint
    have hsub :
        {ω | ENNReal.ofReal ((K / ε) * oracleRate d n β γ) <
          eLpNorm (fun x =>
            equalCellEstimator β (max M σ) ω (affineToCube x) - μ₁ x)
            ⊤ (covariateLaw P)} ⊆
        {ω | ENNReal.ofReal ((K / ε) * oracleRate d n β γ) < Z ω} := by
      intro ω hω
      exact hω.trans_le
        (dorn_eLpNorm_le_cubeSup β (max M σ) ω P μ₁ hmem.2.1)
    exact (measureReal_mono hsub).trans hmark
  · intro 𝔓 μref x₀ _ hμ n c r hc hr
    exact knownRegression_minimax_miss_zero 𝔓 μref x₀ c r hc hr hμ
  · have hB : 0 < max M σ := lt_of_lt_of_le hM (le_max_left _ _)
    have hCmax : 1 ≤ max C 1 := le_max_right _ _
    have hmain := (adaptive_minimax_rate d β (max M σ)
      (dornCommonRadius d β M L₀) (max C 1) 1 γ_min γ_max
      (Nat.lt_of_lt_of_le Nat.zero_lt_one hd) hβ hB hRadius.2.1
      hCmax ⟨by norm_num, by norm_num⟩ hγmin hγrange).2
    intro γ hγ x₀ hx₀
    obtain ⟨cγ, Kγ, hcγ, _, hrate⟩ := hmain γ hγ x₀ hx₀
    exact ⟨cγ, hcγ, fun n hn => (hrate n hn).1⟩
end CausalSmith.Stat.WeakOverlap
