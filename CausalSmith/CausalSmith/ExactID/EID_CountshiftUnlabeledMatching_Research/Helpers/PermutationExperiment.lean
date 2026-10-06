module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.OffsetVariance
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.CompatibleModelRealization
public import Causalean.Mathlib.InformationTheory.GaussianKL
public import Causalean.Mathlib.InformationTheory.ProductKLLeCam
public import Causalean.Mathlib.InformationTheory.KLBind

/-! The canonical unit-offset Gaussian--Poisson permutation experiment. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

abbrev PermutationCell (p : ℕ) := (Fin p → ℝ) × (Fin p → ℕ)

/-- The unit-offset Poisson count law depends measurably on the latent vector. -/
-- @node: unitPoissonLaw_measurable
lemma unitPoissonLaw_measurable (p : ℕ) :
    Measurable (fun z : Fin p → ℝ => poissonCountLaw (fun _ => 1) z) := by
  refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
  have heval : (fun z : Fin p → ℝ => poissonCountLaw (fun _ => 1) z A) =
      fun z => ∑' x : Fin p → ℕ,
        A.indicator (fun x => ∏ j, ENNReal.ofReal
          (Real.exp (-(Real.toNNReal (Real.exp (z j)) : ℝ)) *
            (Real.toNNReal (Real.exp (z j)) : ℝ) ^ x j /
              (x j).factorial)) x := by
    funext z
    rw [← Measure.tsum_indicator_apply_singleton _ A hA, poissonCountLaw]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      rw [Measure.pi_singleton]
      congr 1
      funext j
      simpa using poissonMeasure_singleton (Real.toNNReal (Real.exp (z j))) (x j)
    · simp [Set.indicator, hx]
  rw [heval]
  exact Measurable.tsum fun x => by
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      fun_prop
    · simp [Set.indicator, hx]

def unitPoissonKernel (p : ℕ) : Kernel (Fin p → ℝ) (Fin p → ℕ) :=
  Kernel.mk (fun z : Fin p → ℝ => poissonCountLaw (fun _ => 1) z)
    (unitPoissonLaw_measurable p)

instance unitPoissonKernel_isMarkov (p : ℕ) : IsMarkovKernel (unitPoissonKernel p) where
  isProbabilityMeasure z := by
    change IsProbabilityMeasure (poissonCountLaw (fun _ : Fin p => 1) z)
    unfold poissonCountLaw
    infer_instance

def shiftedGaussianLaw (η : Fin p → ℝ) : Measure (Fin p → ℝ) :=
  (Measure.pi fun _ : Fin p => gaussianReal 0 1).map (fun x => η + x)

instance shiftedGaussianLaw_probability (η : Fin p → ℝ) :
    IsProbabilityMeasure (shiftedGaussianLaw η) := by
  unfold shiftedGaussianLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma shiftedGaussianLaw_eq_pi (η : Fin p → ℝ) :
    shiftedGaussianLaw η = Measure.pi (fun j => gaussianReal (η j) 1) := by
  rw [shiftedGaussianLaw]
  have hmap := Measure.pi_map_pi
    (μ := fun _ : Fin p => gaussianReal 0 1)
    (f := fun j x => η j + x) (fun _ => (by fun_prop))
  rw [show (fun x : Fin p → ℝ => η + x) = fun x j => η j + x j by
    funext x j; rfl, hmap]
  congr 1
  funext j
  have hbase : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have hshift := gaussianReal_const_add hbase (η j)
  simpa only [zero_add, Function.comp_apply, id_eq] using hshift.map_eq

def permutationCellLaw (η : Fin p → ℝ) : Measure (PermutationCell p) :=
  shiftedGaussianLaw η ⊗ₘ unitPoissonKernel p

instance permutationCellLaw_probability (η : Fin p → ℝ) :
    IsProbabilityMeasure (permutationCellLaw η) := by
  unfold permutationCellLaw
  infer_instance

lemma permutationCellLaw_kl_eq (η ζ : Fin p → ℝ) :
    InformationTheory.klDiv (permutationCellLaw η) (permutationCellLaw ζ) =
      InformationTheory.klDiv (shiftedGaussianLaw η) (shiftedGaussianLaw ζ) := by
  unfold permutationCellLaw
  exact InformationTheory.klDiv_compProd_left _ _ _

lemma shiftedGaussianLaw_map_sub (η : Fin p → ℝ) :
    (shiftedGaussianLaw η).map (fun z => WithLp.toLp 2 (z - η)) =
      multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ) := by
  rw [shiftedGaussianLaw, Measure.map_map]
  · simp only [Function.comp_def]
    have hfun : (fun x : Fin p → ℝ => WithLp.toLp 2 (η + x - η)) = WithLp.toLp 2 := by
      funext x
      congr 1
      ext i
      simp
    rw [hfun, map_pi_eq_stdGaussian, multivariateGaussian_zero_one]
  · fun_prop
  · fun_prop

lemma permutationCellLaw_fst (η : Fin p → ℝ) :
    (permutationCellLaw η).map Prod.fst = shiftedGaussianLaw η := by
  change (permutationCellLaw η).fst = _
  rw [permutationCellLaw, Measure.fst_compProd]

lemma permutationCellLaw_disturbance (η : Fin p → ℝ) :
    (permutationCellLaw η).map
        (fun y => WithLp.toLp 2 (y.1 - η)) =
      multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ) := by
  rw [show (fun y : PermutationCell p => WithLp.toLp 2 (y.1 - η)) =
      (fun z => WithLp.toLp 2 (z - η)) ∘ Prod.fst by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), permutationCellLaw_fst,
    shiftedGaussianLaw_map_sub]

lemma permutationCell_poisson (η : Fin p → ℝ) :
    PoissonMeasurement (permutationCellLaw η)
      (fun _ : Unit => fun _ : Unit => fun y => y.1)
      (fun _ _ _ => fun _ => 1) (fun _ _ y => y.2) := by
  intro _ _
  refine ⟨Filter.Eventually.of_forall (fun _ _ => by norm_num),
    (by fun_prop), (by fun_prop), ?_⟩
  have hSZ : (permutationCellLaw η).map
        (fun y => ((fun _ : Fin p => (1 : ℝ)), y.1)) =
      (shiftedGaussianLaw η).map
        (fun z => ((fun _ : Fin p => (1 : ℝ)), z)) := by
    rw [show (fun y : PermutationCell p => ((fun _ : Fin p => (1 : ℝ)), y.1)) =
        (fun z => ((fun _ : Fin p => (1 : ℝ)), z)) ∘ Prod.fst by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), permutationCellLaw_fst]
  rw [hSZ]
  ext A hA
  rw [Measure.map_apply (by fun_prop) hA]
  rw [Measure.bind_apply hA]
  · rw [permutationCellLaw, Measure.compProd_apply (hA.preimage (by fun_prop))]
    have hmeasure : Measurable (fun sz : (Fin p → ℝ) × (Fin p → ℝ) =>
        ((poissonCountLaw sz.1 sz.2).map (fun x => (sz, x))) A) :=
      (Measure.measurable_coe hA).comp
        (poissonCountLaw_attach_measurable_general (p := p))
    rw [lintegral_map hmeasure (by fun_prop)]
    apply lintegral_congr
    intro z
    rw [Measure.map_apply (by fun_prop) hA]
    rfl
  · exact (poissonCountLaw_attach_measurable_general (p := p)).comp (by fun_prop) |>.aemeasurable

def permutationEta (π : Equiv.Perm (Fin p)) (a : ℝ) :
    Fin (p + 1) → Fin p → ℝ :=
  Fin.cases 0 (fun m => a • Pi.single (π m) 1)

@[simp] lemma permutationEta_zero (π : Equiv.Perm (Fin p)) (a : ℝ) :
    permutationEta π a 0 = 0 := by rfl

@[simp] lemma permutationEta_succ (π : Equiv.Perm (Fin p)) (a : ℝ) (m : Fin p) :
    permutationEta π a m.succ = a • Pi.single (π m) 1 := by rfl

abbrev PermutationOmega (p n : ℕ) :=
  (Fin (p + 1) × Fin n) → PermutationCell p

def permutationExperimentMeasure (π : Equiv.Perm (Fin p)) (a : ℝ) :
    Measure (PermutationOmega p n) :=
  Measure.pi fun er : Fin (p + 1) × Fin n =>
    permutationCellLaw (permutationEta π a er.1)

lemma permutationExperimentMeasure_eq_pi (π : Equiv.Perm (Fin p)) (a : ℝ) :
    permutationExperimentMeasure (n := n) π a =
      Measure.pi (fun er : Fin (p + 1) × Fin n =>
        permutationCellLaw (permutationEta π a er.1)) := rfl

instance permutationExperimentMeasure_probability
    (π : Equiv.Perm (Fin p)) (a : ℝ) :
    IsProbabilityMeasure (permutationExperimentMeasure (n := n) π a) := by
  unfold permutationExperimentMeasure
  infer_instance

def permutationZ (e : Fin (p + 1)) (r : Fin n)
    (ω : PermutationOmega p n) : Fin p → ℝ := (ω (e, r)).1

def permutationS (_e : Fin (p + 1)) (_r : Fin n)
    (_ω : PermutationOmega p n) : Fin p → ℝ := fun _ => 1

@[simp] lemma permutationS_apply (e : Fin (p + 1)) (r : Fin n)
    (ω : PermutationOmega p n) (j : Fin p) : permutationS e r ω j = 1 := rfl

def permutationX (e : Fin (p + 1)) (r : Fin n)
    (ω : PermutationOmega p n) : Fin p → ℕ := (ω (e, r)).2

def permutationObservation (ω : PermutationOmega p n) : ObservedSample p n :=
  (fun e r => permutationS e r ω, fun e r => permutationX e r ω)

lemma permutationObservation_measurable :
    Measurable (permutationObservation : PermutationOmega p n → ObservedSample p n) := by
  unfold permutationObservation permutationS permutationX
  fun_prop

lemma permutationExperiment_eval_law (π : Equiv.Perm (Fin p)) (a : ℝ)
    (e : Fin (p + 1)) (r : Fin n) :
    (permutationExperimentMeasure (n := n) π a).map (fun ω => ω (e, r)) =
      permutationCellLaw (permutationEta π a e) := by
  exact (measurePreserving_eval
    (fun er : Fin (p + 1) × Fin n =>
      permutationCellLaw (permutationEta π a er.1)) (e, r)).map_eq

lemma permutationExperiment_Z_law (π : Equiv.Perm (Fin p)) (a : ℝ)
    (e : Fin (p + 1)) (r : Fin n) :
    (permutationExperimentMeasure (n := n) π a).map (permutationZ e r) =
      shiftedGaussianLaw (permutationEta π a e) := by
  rw [show permutationZ e r = Prod.fst ∘ (fun ω : PermutationOmega p n => ω (e, r)) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), permutationExperiment_eval_law,
    permutationCellLaw_fst]

lemma permutationExperiment_disturbance_law (π : Equiv.Perm (Fin p)) (a : ℝ)
    (e : Fin (p + 1)) (r : Fin n) :
    (permutationExperimentMeasure (n := n) π a).map
        (fun ω => WithLp.toLp 2
          (permutationZ e r ω - permutationEta π a e)) =
      multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ) := by
  rw [show (fun ω : PermutationOmega p n => WithLp.toLp 2
      (permutationZ e r ω - permutationEta π a e)) =
      (fun y : PermutationCell p => WithLp.toLp 2
        (y.1 - permutationEta π a e)) ∘ (fun ω => ω (e, r)) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), permutationExperiment_eval_law,
    permutationCellLaw_disturbance]

lemma permutationExperiment_disturbance_hasLaw (π : Equiv.Perm (Fin p)) (a : ℝ)
    (e : Fin (p + 1)) (r : Fin n) :
    HasLaw
      (fun ω : PermutationOmega p n => WithLp.toLp 2
        (permutationZ e r ω - permutationEta π a e))
      (multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ))
      (permutationExperimentMeasure π a) := by
  have hmap := permutationExperiment_disturbance_law (n := n) π a e r
  refine ⟨AEMeasurable.of_map_ne_zero ?_, hmap⟩
  rw [hmap]
  exact IsProbabilityMeasure.ne_zero _

lemma permutationExperiment_poisson (π : Equiv.Perm (Fin p)) (a : ℝ) :
    PoissonMeasurement (permutationExperimentMeasure (n := n) π a)
      permutationZ permutationS permutationX := by
  intro e r
  refine ⟨Filter.Eventually.of_forall (fun _ _ => by simp [permutationS]),
    ?_, ?_, ?_⟩
  · have hZ : Measurable (permutationZ e r) := by unfold permutationZ; fun_prop
    exact (measurable_const.prodMk hZ).aemeasurable
  · have hZ : Measurable (permutationZ e r) := by unfold permutationZ; fun_prop
    have hX : Measurable (permutationX e r) := by unfold permutationX; fun_prop
    exact ((measurable_const.prodMk hZ).prodMk hX).aemeasurable
  have hcell := (permutationCell_poisson (permutationEta π a e) () ()).2.2.2
  have hEval := permutationExperiment_eval_law (n := n) π a e r
  have hSZ : (permutationExperimentMeasure (n := n) π a).map
        (fun ω => (permutationS e r ω, permutationZ e r ω)) =
      (permutationCellLaw (permutationEta π a e)).map
        (fun y => ((fun _ : Fin p => (1 : ℝ)), y.1)) := by
    rw [show (fun ω : PermutationOmega p n =>
        (permutationS e r ω, permutationZ e r ω)) =
        (fun y : PermutationCell p => ((fun _ : Fin p => (1 : ℝ)), y.1)) ∘
          (fun ω => ω (e, r)) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), hEval]
  have hfull : (permutationExperimentMeasure (n := n) π a).map
        (fun ω => ((permutationS e r ω, permutationZ e r ω), permutationX e r ω)) =
      (permutationCellLaw (permutationEta π a e)).map
        (fun y => (((fun _ : Fin p => (1 : ℝ)), y.1), y.2)) := by
    rw [show (fun ω : PermutationOmega p n =>
        ((permutationS e r ω, permutationZ e r ω), permutationX e r ω)) =
        (fun y : PermutationCell p => (((fun _ : Fin p => (1 : ℝ)), y.1), y.2)) ∘
          (fun ω => ω (e, r)) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), hEval]
  rw [hfull, hSZ]
  exact hcell

lemma permutationExperiment_iid (π : Equiv.Perm (Fin p)) (a : ℝ) :
    IIDWithinEnvironment (permutationExperimentMeasure (n := n) π a)
      permutationS permutationX := by
  intro e
  constructor
  · have hall : iIndepFun
        (fun er : Fin (p + 1) × Fin n =>
          fun ω : PermutationOmega p n => ω er)
        (permutationExperimentMeasure (n := n) π a) := by
      unfold permutationExperimentMeasure
      exact iIndepFun_pi
        (μ := fun er : Fin (p + 1) × Fin n =>
          permutationCellLaw (permutationEta π a er.1))
        (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    have heval := hall.precomp (g := fun r : Fin n => (e, r)) (by
      intro r s h
      exact congrArg Prod.snd h)
    let F : PermutationCell p → (Fin p → ℝ) × (Fin p → ℕ) :=
      fun y => ((fun _ => 1), y.2)
    have h := heval.comp (fun _ => F) (fun _ => by
      dsimp [F]
      fun_prop)
    change iIndepFun (fun r ω => ((fun _ : Fin p => (1 : ℝ)), (ω (e, r)).2))
      (permutationExperimentMeasure (n := n) π a)
    simpa only [Function.comp_def, F] using h
  · intro r s
    refine IdentDistrib.mk
      ((measurable_const.prodMk ((measurable_pi_apply (e, r)).snd)).aemeasurable)
      ((measurable_const.prodMk ((measurable_pi_apply (e, s)).snd)).aemeasurable) ?_
    let F : PermutationCell p → (Fin p → ℝ) × (Fin p → ℕ) :=
      fun y => ((fun _ => 1), y.2)
    rw [show (fun ω : PermutationOmega p n =>
        (permutationS e r ω, permutationX e r ω)) =
        F ∘ (fun ω => ω (e, r)) by rfl,
      show (fun ω : PermutationOmega p n =>
        (permutationS e s ω, permutationX e s ω)) =
        F ∘ (fun ω => ω (e, s)) by rfl,
      ← Measure.map_map (by dsimp [F]; fun_prop) (by fun_prop),
      ← Measure.map_map (by dsimp [F]; fun_prop) (by fun_prop),
      permutationExperiment_eval_law, permutationExperiment_eval_law]

lemma permutationExperiment_Z_coord_law (π : Equiv.Perm (Fin p)) (a : ℝ)
    (e : Fin (p + 1)) (r : Fin n) (j : Fin p) :
    HasLaw (fun ω : PermutationOmega p n => permutationZ e r ω j)
      (gaussianReal (permutationEta π a e j) 1)
      (permutationExperimentMeasure (n := n) π a) := by
  refine ⟨((measurable_pi_apply j).comp
    (measurable_fst.comp (measurable_pi_apply (e, r)))).aemeasurable, ?_⟩
  rw [show (fun ω : PermutationOmega p n => permutationZ e r ω j) =
      (fun z => z j) ∘ permutationZ e r by rfl,
    ← Measure.map_map (by fun_prop) (by unfold permutationZ; fun_prop),
    permutationExperiment_Z_law, shiftedGaussianLaw]
  rw [Measure.map_map]
  · have hbase : HasLaw (fun x : Fin p → ℝ => x j) (gaussianReal 0 1)
        (Measure.pi fun _ : Fin p => gaussianReal 0 1) :=
      (measurePreserving_eval (fun _ : Fin p => gaussianReal 0 1) j).hasLaw
    have hshift := gaussianReal_const_add hbase (permutationEta π a e j)
    rw [zero_add] at hshift
    convert hshift.map_eq using 1
    congr 1
  · fun_prop
  · fun_prop

lemma integral_exp_of_gaussian_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ) (m k : ℝ)
    (hZ : HasLaw Z (gaussianReal m 1) μ) :
    (∫ ω, Real.exp (k * Z ω) ∂μ) = Real.exp (m * k + k ^ 2 / 2) := by
  calc
    (∫ ω, Real.exp (k * Z ω) ∂μ) =
        ∫ x, Real.exp (k * x) ∂gaussianReal m 1 :=
      hZ.integral_comp (f := fun x => Real.exp (k * x)) (by fun_prop)
    _ = mgf id (gaussianReal m 1) k := by rfl
    _ = Real.exp (m * k + k ^ 2 / 2) := by
      rw [mgf_id_gaussianReal]
      norm_num

lemma integrable_exp_of_gaussian_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ) (m k : ℝ)
    (hZ : HasLaw Z (gaussianReal m 1) μ) :
    Integrable (fun ω => Real.exp (k * Z ω)) μ := by
  change Integrable ((fun x => Real.exp (k * x)) ∘ Z) μ
  apply (integrable_map_measure (by fun_prop) hZ.aemeasurable).mp
  rw [hZ.map_eq]
  exact integrable_exp_mul_gaussianReal k

lemma memLp_exp_of_gaussian_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ) (m k : ℝ)
    (hZ : HasLaw Z (gaussianReal m 1) μ) :
    MemLp (fun ω => Real.exp (k * Z ω)) 2 μ := by
  refine (memLp_two_iff_integrable_sq
    ((hZ.aemeasurable.const_mul k).exp.aestronglyMeasurable)).2 ?_
  convert integrable_exp_of_gaussian_law μ Z m (2 * k) hZ using 1
  funext ω
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

lemma variance_exp_of_gaussian_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ) (m k : ℝ)
    (hZ : HasLaw Z (gaussianReal m 1) μ) :
    variance (fun ω => Real.exp (k * Z ω)) μ =
      Real.exp (2 * m * k + 2 * k ^ 2) -
      Real.exp (m * k + k ^ 2 / 2) ^ 2 := by
  letI : IsProbabilityMeasure μ := hZ.isProbabilityMeasure
  rw [variance_eq_sub (memLp_exp_of_gaussian_law μ Z m k hZ)]
  rw [integral_exp_of_gaussian_law μ Z m k hZ]
  have hsquare : (∫ ω, ((fun ω => Real.exp (k * Z ω)) ^ 2) ω ∂μ) =
      ∫ ω, Real.exp ((2 * k) * Z ω) ∂μ := by
    congr 1
    funext ω
    rw [Pi.pow_apply, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hsquare, integral_exp_of_gaussian_law μ Z m (2 * k) hZ]
  congr 2
  ring

lemma permutationEta_nonneg_le (π : Equiv.Perm (Fin p)) {a : ℝ} (ha : 0 ≤ a)
    (e : Fin (p + 1)) (j : Fin p) :
    0 ≤ permutationEta π a e j ∧ permutationEta π a e j ≤ a := by
  refine Fin.cases ?_ (fun m => ?_) e
  · simp [permutationEta, ha]
  · by_cases h : π m = j
    · subst j
      simp [permutationEta, ha]
    · simp [permutationEta, Pi.single_apply, h, ha]

lemma permutation_unit_offset_variance_envelope (μ a : ℝ) (hμ : μ ≤ a) :
    Real.exp (μ + 1 / 2) + (Real.exp 1 - 1) * Real.exp (2 * μ + 1) ≤ v0 a ∧
    4 * Real.exp (3 * μ + 9 / 2) + 2 * Real.exp (2 * μ + 2) +
      Real.exp (4 * μ + 8) - Real.exp (4 * μ + 4) ≤ v0 a := by
  have he : 0 ≤ Real.exp 4 - 1 := by
    have : 1 ≤ Real.exp (4 : ℝ) := Real.one_le_exp (by norm_num)
    linarith
  have he1 : 0 ≤ Real.exp 1 - 1 := by
    have : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
    linarith
  have h₁ := Real.exp_le_exp.mpr (show μ + 1 / 2 ≤ a + 1 / 2 by linarith)
  have h₂ := Real.exp_le_exp.mpr (show 2 * μ + 1 ≤ 2 * a + 1 by linarith)
  have h₃ := Real.exp_le_exp.mpr (show 3 * μ + 9 / 2 ≤ 3 * a + 9 / 2 by linarith)
  have h₄ := Real.exp_le_exp.mpr (show 2 * μ + 2 ≤ 2 * a + 2 by linarith)
  have h₅ := Real.exp_le_exp.mpr (show 4 * μ + 4 ≤ 4 * a + 4 by linarith)
  have hid (x : ℝ) : Real.exp (4 * x + 8) - Real.exp (4 * x + 4) =
      (Real.exp 4 - 1) * Real.exp (4 * x + 4) := by
    rw [show 4 * x + 8 = (4 * x + 4) + 4 by ring, Real.exp_add]
    ring
  constructor <;> unfold v0 <;> simp only [le_max_iff]
  · left
    nlinarith [mul_nonneg he1 (sub_nonneg.mpr h₂)]
  · right
    calc
      _ = 4 * Real.exp (3 * μ + 9 / 2) + 2 * Real.exp (2 * μ + 2) +
          (Real.exp (4 * μ + 8) - Real.exp (4 * μ + 4)) := by ring
      _ ≤ 4 * Real.exp (3 * a + 9 / 2) + 2 * Real.exp (2 * a + 2) +
          (Real.exp (4 * a + 8) - Real.exp (4 * a + 4)) := by
        rw [hid μ, hid a]
        nlinarith [mul_nonneg he (sub_nonneg.mpr h₅)]
      _ = _ := by ring

lemma permutationExperiment_exog (π : Equiv.Perm (Fin p)) (a : ℝ) :
    OffsetExogeneity (permutationExperimentMeasure (n := n) π a)
      permutationS permutationZ := by
  intro e r
  change IndepFun (fun _ : PermutationOmega p n => fun _ : Fin p => (1 : ℝ))
    (permutationZ e r) (permutationExperimentMeasure π a)
  exact
    (indepFun_const_right (permutationZ e r)
      (fun _ : Fin p => (1 : ℝ))).symm

lemma permutationExperiment_varBound (π : Equiv.Perm (Fin p)) {a v : ℝ}
    (ha : 0 ≤ a) (hav : v0 a ≤ v) :
    FactorialVarianceBound (permutationExperimentMeasure (n := n) π a)
      permutationZ permutationS v := by
  constructor
  · intro e r j
    let b := permutationEta π a e j
    have hZ := permutationExperiment_Z_coord_law (n := n) π a e r j
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [one_mul] using integrable_exp_of_gaussian_law
        _ (fun ω => permutationZ e r ω j) b 1 hZ
    · simpa only [one_mul] using memLp_exp_of_gaussian_law
        _ (fun ω => permutationZ e r ω j) b 1 hZ
    · exact integrable_exp_of_gaussian_law
        _ (fun ω => permutationZ e r ω j) b 2 hZ
    · exact memLp_exp_of_gaussian_law
        _ (fun ω => permutationZ e r ω j) b 2 hZ
    · exact integrable_exp_of_gaussian_law
        _ (fun ω => permutationZ e r ω j) b 3 hZ
    · simp [permutationS]
    · simp [permutationS]
  · intro e r j
    let b := permutationEta π a e j
    have hZ := permutationExperiment_Z_coord_law (n := n) π a e r j
    have hb := (permutationEta_nonneg_le π ha e j).2
    have henv := permutation_unit_offset_variance_envelope b a hb
    have h1 := variance_exp_of_gaussian_law
      _ (fun ω => permutationZ e r ω j) b 1 hZ
    have h2 := variance_exp_of_gaussian_law
      _ (fun ω => permutationZ e r ω j) b 2 hZ
    have hi1 := integral_exp_of_gaussian_law
      _ (fun ω => permutationZ e r ω j) b 1 hZ
    have hi2 := integral_exp_of_gaussian_law
      _ (fun ω => permutationZ e r ω j) b 2 hZ
    have hi3 := integral_exp_of_gaussian_law
      _ (fun ω => permutationZ e r ω j) b 3 hZ
    have h1' : variance (fun ω => Real.exp (permutationZ e r ω j))
        (permutationExperimentMeasure π a) =
        Real.exp (2 * b * 1 + 2 * 1 ^ 2) -
          Real.exp (b * 1 + 1 ^ 2 / 2) ^ 2 := by
      simpa only [one_mul] using h1
    have hi1' : (∫ ω, Real.exp (permutationZ e r ω j)
          ∂permutationExperimentMeasure π a) =
        Real.exp (b * 1 + 1 ^ 2 / 2) := by
      simpa only [one_mul] using hi1
    have hmass : (permutationExperimentMeasure (n := n) π a).real Set.univ = 1 := by
      simp [Measure.real_def]
    simp only [permutationS, inv_one, integral_const, one_pow]
    rw [hmass]
    simp only [one_smul]
    rw [h1', h2, hi1', hi2, hi3]
    apply (max_le_iff.mpr ⟨?_, ?_⟩)
    · calc
        _ = Real.exp (b + 1 / 2) +
            (Real.exp 1 - 1) * Real.exp (2 * b + 1) := by
          norm_num
          rw [show Real.exp (2 * b + 2) =
              Real.exp 1 * Real.exp (2 * b + 1) by
                rw [← Real.exp_add]; congr 1 <;> ring,
            show Real.exp (b + 1 / 2) ^ 2 = Real.exp (2 * b + 1) by
              rw [pow_two, ← Real.exp_add]; congr 1 <;> ring]
          ring
        _ ≤ v0 a := henv.1
        _ ≤ v := hav
    · calc
        _ = 4 * Real.exp (3 * b + 9 / 2) + 2 * Real.exp (2 * b + 2) +
            Real.exp (4 * b + 8) - Real.exp (4 * b + 4) := by
          norm_num
          rw [show Real.exp (b * 2 + 2) ^ 2 = Real.exp (4 * b + 4) by
            rw [pow_two, ← Real.exp_add]; congr 1 <;> ring]
          rw [show Real.exp (2 * b * 2 + 8) = Real.exp (4 * b + 8) by
                congr 1 <;> ring,
            show Real.exp (b * 3 + 9 / 2) = Real.exp (3 * b + 9 / 2) by
                congr 1 <;> ring,
            show Real.exp (b * 2 + 2) = Real.exp (2 * b + 2) by
                congr 1 <;> ring]
          ring
        _ ≤ v0 a := henv.2
        _ ≤ v := hav

lemma permutationExperiment_firstMoment (π : Equiv.Perm (Fin p)) {a ℓ : ℝ}
    (ha : 0 ≤ a) (hℓ : ℓ ≤ Real.exp (1 / 2)) :
    FirstMomentNondegeneracy (permutationExperimentMeasure (n := n) π a)
      permutationS permutationX ℓ := by
  intro e r j
  have hZ := permutationExperiment_Z_coord_law (n := n) π a e r j
  have hP : PoissonMeasurement (permutationExperimentMeasure (n := n) π a)
      (fun _ : Unit => fun _ : Unit => permutationZ e r)
      (fun _ _ => permutationS e r) (fun _ _ => permutationX e r) := by
    intro _ _
    exact permutationExperiment_poisson π a e r
  have h1 := integrable_exp_of_gaussian_law _
    (fun ω => permutationZ e r ω j) (permutationEta π a e j) 1 hZ
  have hdiag : Integrable
      (fun ω => Real.exp (permutationZ e r ω j + permutationZ e r ω j))
      (permutationExperimentMeasure π a) := by
    convert integrable_exp_of_gaussian_law _
      (fun ω => permutationZ e r ω j) (permutationEta π a e j) 2 hZ using 1
    funext ω
    congr 1
    ring
  obtain ⟨hfirst, _⟩ := poisson_mixture_factorial_moment_transfer
    (permutationExperimentMeasure π a) (permutationS e r) (permutationZ e r)
      (permutationX e r) hP j j (by simpa only [one_mul] using h1) hdiag
  rw [hfirst]
  have hm := integral_exp_of_gaussian_law _
    (fun ω => permutationZ e r ω j) (permutationEta π a e j) 1 hZ
  simp only [one_mul] at hm
  rw [hm]
  norm_num
  exact hℓ.trans (Real.exp_le_exp.mpr (by
    have := (permutationEta_nonneg_le π ha e j).1
    linarith))

def permutationBoundedMomentClass (π : Equiv.Perm (Fin p)) {a ℓ v : ℝ}
    (hp : 0 < p) (hn : 0 < n) (ha : 0 ≤ a)
    (hℓ : 0 < ℓ) (hℓle : ℓ ≤ Real.exp (1 / 2))
    (hv : 0 < v) (hav : v0 a ≤ v) :
    BoundedMomentClass p n ℓ v (PermutationOmega p n)
      (permutationExperimentMeasure π a) where
  p_pos := hp
  n_pos := hn
  ell_pos := hℓ
  ell_le := hℓle
  v_pos := hv
  Z := permutationZ
  S := permutationS
  X := permutationX
  poisson := permutationExperiment_poisson π a
  iid := permutationExperiment_iid π a
  exog := permutationExperiment_exog π a
  varBound := permutationExperiment_varBound π ha hav
  firstMoment := permutationExperiment_firstMoment π ha hℓle

@[simp] lemma permutationBoundedMomentClass_S (π : Equiv.Perm (Fin p))
    {a ℓ v : ℝ} (hp : 0 < p) (hn : 0 < n) (ha : 0 ≤ a)
    (hℓ : 0 < ℓ) (hℓle : ℓ ≤ Real.exp (1 / 2)) (hv : 0 < v)
    (hav : v0 a ≤ v) :
    (permutationBoundedMomentClass π hp hn ha hℓ hℓle hv hav).S =
      permutationS := rfl

@[simp] lemma permutationBoundedMomentClass_X (π : Equiv.Perm (Fin p))
    {a ℓ v : ℝ} (hp : 0 < p) (hn : 0 < n) (ha : 0 ≤ a)
    (hℓ : 0 < ℓ) (hℓle : ℓ ≤ Real.exp (1 / 2)) (hv : 0 < v)
    (hav : v0 a ≤ v) :
    (permutationBoundedMomentClass π hp hn ha hℓ hℓle hv hav).X =
      permutationX := rfl

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
