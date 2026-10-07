module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.FullMarkPartition
public import Causalean.Stat.Concentration.Hilbert.EmpiricalMean.Basic
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Main
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization

/-! Fixed-count i.i.d. sum moments used by the outcome-sum representation. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]

/-- Mapping every point of a finite Poisson sample maps its base law.  This
count-fibre form is kept local to the estimator representation layer. -/
lemma map_finitePoissonSampleLaw_finiteSampleMap_local
    {Y : Type*} [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (f : X → Y) (hf : Measurable f) (lam : ℝ≥0) :
    Measure.map (finiteSampleMap f) (finitePoissonSampleLaw P lam) =
      (letI : IsProbabilityMeasure (Measure.map f P) :=
        Measure.isProbabilityMeasure_map hf.aemeasurable
       finitePoissonSampleLaw (Measure.map f P) lam) := by
  letI : IsProbabilityMeasure (Measure.map f P) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let F := finiteSampleMap f
  have hF : Measurable F := measurable_finiteSampleMap f hf
  let mu := Measure.map F (finitePoissonSampleLaw P lam)
  let nu := finitePoissonSampleLaw (Measure.map f P) lam
  have hrest (m : ℕ) :
      mu.restrict (FiniteSample.count ⁻¹' ({m} : Set ℕ)) =
        nu.restrict (FiniteSample.count ⁻¹' ({m} : Set ℕ)) := by
    rw [show mu = Measure.map F (finitePoissonSampleLaw P lam) by rfl,
      Measure.restrict_map hF
        (measurable_finiteSample_count (MeasurableSet.singleton m))]
    have hpre : F ⁻¹' (FiniteSample.count ⁻¹' ({m} : Set ℕ)) =
        FiniteSample.count ⁻¹' ({m} : Set ℕ) := by ext s; rfl
    rw [hpre, finitePoissonSampleLaw_restrict_count_eq,
      show nu = finitePoissonSampleLaw (Measure.map f P) lam by rfl,
      finitePoissonSampleLaw_restrict_count_eq, Measure.map_smul,
      Measure.map_map hF (measurable_fixedSizeEmbed m)]
    have hfun : F ∘ fixedSizeEmbed m =
        fixedSizeEmbed m ∘ (fun x : Fin m → X => fun i => f (x i)) := by
      funext x
      exact finiteSampleMap_fixedSizeEmbed f m x
    rw [hfun]
    congr 1
    let G : (Fin m → X) → (Fin m → Y) := fun x i => f (x i)
    have hG : Measurable G :=
      measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
    change Measure.map (fixedSizeEmbed m ∘ G)
      (Measure.pi fun _ : Fin m => P) = _
    calc
      Measure.map (fixedSizeEmbed m ∘ G) (Measure.pi fun _ : Fin m => P) =
          Measure.map (fixedSizeEmbed m)
            (Measure.map G (Measure.pi fun _ : Fin m => P)) :=
        (Measure.map_map (measurable_fixedSizeEmbed m) hG).symm
      _ = Measure.map (fixedSizeEmbed m)
          (Measure.pi fun _ : Fin m => Measure.map f P) := by
        rw [show G = (fun x i => f (x i)) by rfl,
          Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  have hdecomp (eta : Measure (FiniteSample Y)) :
      eta = Measure.sum (fun m =>
        eta.restrict (FiniteSample.count ⁻¹' ({m} : Set ℕ))) := by
    have hdis : Pairwise (Function.onFun Disjoint
        (fun m : ℕ => (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹'
          ({m} : Set ℕ))) := by
      intro i j hij
      apply Set.disjoint_left.2
      intro s hi hj
      apply hij
      simpa using hi.symm.trans hj
    have hcover : ⋃ m : ℕ,
        (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹' ({m} : Set ℕ) =
          Set.univ := by ext s; simp
    calc
      eta = eta.restrict Set.univ := by rw [Measure.restrict_univ]
      _ = eta.restrict (⋃ m : ℕ,
          FiniteSample.count ⁻¹' ({m} : Set ℕ)) := by rw [hcover]
      _ = Measure.sum (fun m =>
          eta.restrict (FiniteSample.count ⁻¹' ({m} : Set ℕ))) := by
        exact Measure.restrict_iUnion hdis
          (fun m => measurable_finiteSample_count (MeasurableSet.singleton m))
  change mu = nu
  rw [hdecomp mu, hdecomp nu]
  congr 1
  funext m
  exact hrest m

/-- Two distinct coordinates of a finite product probability law have their
ordinary product law. -/
lemma map_pi_eval_pair_local {I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (mu : I → Measure X) [∀ i, IsProbabilityMeasure (mu i)]
    (i j : I) (hij : i ≠ j) :
    Measure.map (fun z : I → X => (z i, z j)) (Measure.pi mu) =
      (mu i).prod (mu j) := by
  let pred : I → Prop := fun q => q = i
  letI : Fintype (Subtype pred) := Subtype.fintype pred
  letI : Fintype (Subtype (fun q => ¬ pred q)) :=
    Subtype.fintype (fun q => ¬ pred q)
  let ii : Subtype pred := ⟨i, rfl⟩
  let jj : Subtype (fun q => ¬ pred q) := ⟨j, by
    intro hji
    exact hij hji.symm⟩
  let split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => X) pred
  let e0 : (Subtype pred → X) → X := Function.eval ii
  let e1 : (Subtype (fun q => ¬ pred q) → X) → X := Function.eval jj
  have hs := MeasureTheory.measurePreserving_piEquivPiSubtypeProd
    (μ := mu) pred
  have he0 : Measure.map e0 (Measure.pi fun q : Subtype pred => mu q.1) =
      mu i := by
    simpa [e0, ii] using
      (Measure.pi_map_eval (fun q : Subtype pred => mu q.1) ii)
  have he1 : Measure.map e1
      (Measure.pi fun q : Subtype (fun q => ¬ pred q) => mu q.1) = mu j := by
    simpa [e1, jj] using
      (Measure.pi_map_eval
        (fun q : Subtype (fun q => ¬ pred q) => mu q.1) jj)
  have hfun : Prod.map e0 e1 ∘ split = fun z : I → X => (z i, z j) := by
    funext z
    apply Prod.ext <;> rfl
  calc
    Measure.map (fun z : I → X => (z i, z j)) (Measure.pi mu) =
        Measure.map (Prod.map e0 e1) (Measure.map split (Measure.pi mu)) := by
      symm
      calc
        _ = Measure.map (Prod.map e0 e1 ∘ split) (Measure.pi mu) :=
          Measure.map_map ((measurable_pi_apply ii).prodMap
            (measurable_pi_apply jj)) split.measurable
        _ = _ := by rw [hfun]
    _ = Measure.map (Prod.map e0 e1)
        ((Measure.pi fun q : Subtype pred => mu q.1).prod
          (Measure.pi fun q : Subtype (fun q => ¬ pred q) => mu q.1)) := by
      exact congrArg (Measure.map (Prod.map e0 e1)) hs.map_eq
    _ = (Measure.map e0 (Measure.pi fun q : Subtype pred => mu q.1)).prod
        (Measure.map e1
          (Measure.pi fun q : Subtype (fun q => ¬ pred q) => mu q.1)) := by
      rw [Measure.map_prod_map (Measure.pi fun q : Subtype pred => mu q.1)
        (Measure.pi fun q : Subtype (fun q => ¬ pred q) => mu q.1)
        (measurable_pi_apply ii) (measurable_pi_apply jj)]
    _ = (mu i).prod (mu j) := by rw [he0, he1]

lemma integral_centered_add_const (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : Integrable f P) (hmean : (∫ x, f x ∂P) = 0) (c : ℝ) :
    (∫ x, f x + c ∂P) = c := by
  rw [integral_add hf (integrable_const _), hmean, integral_const,
    probReal_univ, one_smul, zero_add]

lemma integrable_add_const_sq (P : Measure X) [IsFiniteMeasure P] (f : X → ℝ)
    (hf : Integrable f P) (hf2 : Integrable (fun x => f x ^ 2) P) (c : ℝ) :
    Integrable (fun x => (f x + c) ^ 2) P := by
  have h := (hf2.add (hf.const_mul (2 * c))).add (integrable_const (c ^ 2))
  apply h.congr
  filter_upwards with x
  dsimp only [Pi.add_apply]
  ring

lemma integral_centered_add_const_sq (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : Integrable f P) (hf2 : Integrable (fun x => f x ^ 2) P)
    (hmean : (∫ x, f x ∂P) = 0) (c : ℝ) :
    (∫ x, (f x + c) ^ 2 ∂P) = (∫ x, f x ^ 2 ∂P) + c ^ 2 := by
  have hcross : Integrable (fun x => 2 * c * f x) P := hf.const_mul (2 * c)
  have hconst : Integrable (fun _ : X => c ^ 2) P := integrable_const _
  rw [show (fun x => (f x + c) ^ 2) =
      fun x => f x ^ 2 + 2 * c * f x + c ^ 2 by funext x; ring]
  calc
    (∫ x, (f x ^ 2 + 2 * c * f x) + c ^ 2 ∂P) =
        (∫ x, f x ^ 2 + 2 * c * f x ∂P) + ∫ _x : X, c ^ 2 ∂P :=
      integral_add (hf2.add hcross) hconst
    _ = ((∫ x, f x ^ 2 ∂P) + ∫ x, 2 * c * f x ∂P) +
        ∫ _x : X, c ^ 2 ∂P := by rw [integral_add hf2 hcross]
    _ = _ := by
      rw [integral_const_mul, hmean, mul_zero, integral_const,
        probReal_univ, one_smul, add_zero]

lemma integral_centered_add_const_mul (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : Integrable f P) (hf2 : Integrable (fun x => f x ^ 2) P)
    (hmean : (∫ x, f x ∂P) = 0) (c c' : ℝ) :
    (∫ x, (f x + c) * (f x + c') ∂P) =
      (∫ x, f x ^ 2 ∂P) + c * c' := by
  have hcross : Integrable (fun x => (c + c') * f x) P := hf.const_mul (c + c')
  have hconst : Integrable (fun _ : X => c * c') P := integrable_const _
  rw [show (fun x => (f x + c) * (f x + c')) =
      fun x => f x ^ 2 + (c + c') * f x + c * c' by funext x; ring]
  calc
    (∫ x, (f x ^ 2 + (c + c') * f x) + c * c' ∂P) =
        (∫ x, f x ^ 2 + (c + c') * f x ∂P) +
          ∫ _x : X, c * c' ∂P :=
      integral_add (hf2.add hcross) hconst
    _ = ((∫ x, f x ^ 2 ∂P) + ∫ x, (c + c') * f x ∂P) +
        ∫ _x : X, c * c' ∂P := by rw [integral_add hf2 hcross]
    _ = _ := by
      rw [integral_const_mul, hmean, mul_zero, integral_const,
        probReal_univ, one_smul, add_zero]

lemma integral_iid_centered_sum (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : Integrable f P) (N : ℕ) :
    (∫ x : Fin N → X, ∑ i : Fin N, (f (x i) - ∫ y, f y ∂P)
      ∂Measure.pi (fun _ : Fin N => P)) = 0 := by
  let c : X → ℝ := fun x => f x - ∫ y, f y ∂P
  have hc : Integrable c P := hf.sub (integrable_const _)
  change (∫ x : Fin N → X, ∑ i : Fin N, c (x i)
    ∂Measure.pi (fun _ : Fin N => P)) = 0
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_comp_eval (μ := fun _ : Fin N => P) (i := i) hc)]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_comp_eval (μ := fun _ : Fin N => P) (i := i)
    hc.aestronglyMeasurable]
  exact Causalean.Stat.Concentration.HilbertEmpiricalMean.integral_sub_populationMean_eq_zero
    P f hf

lemma integral_iid_centered_sum_sq (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : StronglyMeasurable f) (hf2 : MemLp f 2 P) (N : ℕ) :
    (∫ x : Fin N → X,
      (∑ i : Fin N, (f (x i) - ∫ y, f y ∂P)) ^ 2
      ∂Measure.pi (fun _ : Fin N => P)) =
      N * ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P := by
  simpa only [Causalean.Stat.Concentration.HilbertEmpiricalMean.populationMean,
    Real.norm_eq_abs, sq_abs] using
    (Causalean.Stat.Concentration.HilbertEmpiricalMean.centeredSum_secondMoment_eq
      P f hf2 N)

/-- A fixed i.i.d. outcome tuple has zero expected residual sum. -/
lemma integral_iid_outcome_residual_sum (P : Law n) (a : Bool) (k : Fin n)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) (N : ℕ) :
    (∫ y : Fin N → ℝ,
      ∑ i : Fin N, (y i - P.outcomeMean a k)
      ∂Measure.pi (fun _ : Fin N => P.outcomeLaw a k)) = 0 := by
  letI : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  have hresLp : MemLp (fun y : ℝ => y - P.outcomeMean a k) 2
      (P.outcomeLaw a k) :=
    (memLp_two_iff_integrable_sq
      ((measurable_id.sub measurable_const).aestronglyMeasurable)).2
      (hvariance a k hp).1
  have hres : Integrable (fun y : ℝ => y - P.outcomeMean a k)
      (P.outcomeLaw a k) := hresLp.integrable (by norm_num)
  have hid : Integrable (fun y : ℝ => y) (P.outcomeLaw a k) :=
    CausalSmith.Stat.DiscreteAteHeterogeneityFrontier.outcome_integrable_of_second_moment
      P hvariance a k hp
  have hzero : (∫ y, y - P.outcomeMean a k ∂P.outcomeLaw a k) = 0 := by
    rw [integral_sub hid (integrable_const _)]
    rw [P.outcomeMean_eq a k, integral_const, probReal_univ, one_smul]
    ring
  simpa only [hzero, sub_zero] using
    integral_iid_centered_sum (P.outcomeLaw a k)
      (fun y : ℝ => y - P.outcomeMean a k) hres N

/-- A fixed i.i.d. outcome tuple has residual-sum second moment equal to its
size times the one-observation conditional variance. -/
-- keep: reusable fixed-count residual-sum second-moment identity
lemma integral_iid_outcome_residual_sum_sq (P : Law n) (a : Bool) (k : Fin n)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) (N : ℕ) :
    (∫ y : Fin N → ℝ,
      (∑ i : Fin N, (y i - P.outcomeMean a k)) ^ 2
      ∂Measure.pi (fun _ : Fin N => P.outcomeLaw a k)) =
      N * ∫ y, (y - P.outcomeMean a k) ^ 2 ∂P.outcomeLaw a k := by
  letI : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  have hresLp : MemLp (fun y : ℝ => y - P.outcomeMean a k) 2
      (P.outcomeLaw a k) :=
    (memLp_two_iff_integrable_sq
      ((measurable_id.sub measurable_const).aestronglyMeasurable)).2
      (hvariance a k hp).1
  have hres : Integrable (fun y : ℝ => y - P.outcomeMean a k)
      (P.outcomeLaw a k) := hresLp.integrable (by norm_num)
  have hid : Integrable (fun y : ℝ => y) (P.outcomeLaw a k) :=
    CausalSmith.Stat.DiscreteAteHeterogeneityFrontier.outcome_integrable_of_second_moment
      P hvariance a k hp
  have hzero : (∫ y, y - P.outcomeMean a k ∂P.outcomeLaw a k) = 0 := by
    rw [integral_sub hid (integrable_const _)]
    rw [P.outcomeMean_eq a k, integral_const, probReal_univ, one_smul]
    ring
  simpa only [hzero, sub_zero] using
    integral_iid_centered_sum_sq (P.outcomeLaw a k)
      (fun y : ℝ => y - P.outcomeMean a k)
      (measurable_id.sub measurable_const).stronglyMeasurable hresLp N

lemma outcomeResidual_integrable (P : Law n) (a : Bool) (k : Fin n)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    Integrable (fun y : ℝ => y - P.outcomeMean a k) (P.outcomeLaw a k) := by
  letI : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  exact ((memLp_two_iff_integrable_sq
    ((measurable_id.sub measurable_const).aestronglyMeasurable)).2
      (hvariance a k hp).1).integrable (by norm_num)

lemma outcomeResidual_mean (P : Law n) (a : Bool) (k : Fin n)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    (∫ y, y - P.outcomeMean a k ∂P.outcomeLaw a k) = 0 := by
  letI : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  have hy :=
    CausalSmith.Stat.DiscreteAteHeterogeneityFrontier.outcome_integrable_of_second_moment
      P hvariance a k hp
  rw [integral_sub hy (integrable_const _), ← P.outcomeMean_eq a k,
    integral_const, probReal_univ, one_smul, sub_self]

/-- On a positive arm-cell, forgetting the dummy auxiliary mark and retaining
the outcome sends the marked cell law to the stipulated outcome law. -/
lemma map_markedCellPoint_outcome (P : Law n) (a : Bool) (k : Fin n)
    (harm : 0 < armMass P a k) :
    Measure.map (fun z : FullObservedMark n × ℝ => z.1.2.2)
        (((fullMarkArmCellPartition n).cellObservationLaw
          (fullObservedMarkLaw P) (k, a)).prod (Measure.dirac 0)) =
      P.outcomeLaw a k := by
  change Measure.map ((fun z : FullObservedMark n => z.2.2) ∘ Prod.fst)
      (((fullMarkArmCellPartition n).cellObservationLaw
        (fullObservedMarkLaw P) (k, a)).prod (Measure.dirac 0)) = _
  rw [← Measure.map_map measurable_snd.snd measurable_fst,
    Measure.map_fst_prod]
  rw [measure_univ, one_smul]
  exact map_outcome_cellObservationLaw P k a harm

/-- The coordinatewise outcome projection sends a fixed product of marked
cell observations to the corresponding fixed i.i.d. outcome law. -/
-- keep: exact outcome-projection law for marked fixed-count cells
lemma map_pi_markedCell_outcomes (P : Law n) (a : Bool) (k : Fin n)
    (harm : 0 < armMass P a k) (N : ℕ) :
    Measure.map
        (fun z : Fin N → FullObservedMark n × ℝ => fun i => (z i).1.2.2)
        (Measure.pi (fun _ : Fin N =>
          ((fullMarkArmCellPartition n).cellObservationLaw
            (fullObservedMarkLaw P) (k, a)).prod (Measure.dirac 0))) =
      Measure.pi (fun _ : Fin N => P.outcomeLaw a k) := by
  let g : FullObservedMark n × ℝ → ℝ := fun q => q.1.2.2
  have hg : Measurable g :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  change Measure.map
      (fun z : Fin N → FullObservedMark n × ℝ => fun i : Fin N => g (z i)) _ = _
  rw [Measure.pi_map_pi (fun _ => hg.aemeasurable)]
  congr 1
  funext i
  exact map_markedCellPoint_outcome P a k harm

/-- Outcome projection transports a full marked arm-cell Poisson sample to
the finite Poisson sample of the stipulated conditional outcome law. -/
lemma map_cellFinitePoisson_outcomes (P : Law n) (a : Bool) (k : Fin n)
    (harm : 0 < armMass P a k) (lam : ℝ≥0) :
    Measure.map
        (finiteSampleMap (fun z : FullObservedMark n × ℝ => z.1.2.2))
        (finiteMarkedPoissonSampleLaw
          ((fullMarkArmCellPartition n).cellObservationLaw
            (fullObservedMarkLaw P) (k, a))
          (Measure.dirac 0) lam) =
      @finitePoissonSampleLaw ℝ _ (P.outcomeLaw a k)
        (P.outcome_isProbability a k) lam := by
  let g : FullObservedMark n × ℝ → ℝ := fun z => z.1.2.2
  have hg : Measurable g :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  unfold finiteMarkedPoissonSampleLaw
  rw [map_finitePoissonSampleLaw_finiteSampleMap_local _ g hg lam]
  have hmap : Measure.map g
      (((fullMarkArmCellPartition n).cellObservationLaw
        (fullObservedMarkLaw P) (k, a)).prod (Measure.dirac 0)) =
      P.outcomeLaw a k := map_markedCellPoint_outcome P a k harm
  congr 1

/-- The two arm-cell restricted samples are jointly independent finite
Poisson samples before outcome projection. -/
lemma map_fullMark_twoArmCells (P : Law n) (k : Fin n) (lam : ℝ≥0) :
    Measure.map
        (fun s =>
          ((fullMarkArmCellPartition n).restrictCell (k, false) s,
            (fullMarkArmCellPartition n).restrictCell (k, true) s))
        (finiteMarkedPoissonSampleLaw (fullObservedMarkLaw P)
          (Measure.dirac 0) lam) =
      (finiteMarkedPoissonSampleLaw
        ((fullMarkArmCellPartition n).cellObservationLaw
          (fullObservedMarkLaw P) (k, false))
        (Measure.dirac 0)
        (lam * (fullMarkArmCellPartition n).cellMass
          (fullObservedMarkLaw P) (k, false))).prod
      (finiteMarkedPoissonSampleLaw
        ((fullMarkArmCellPartition n).cellObservationLaw
          (fullObservedMarkLaw P) (k, true))
        (Measure.dirac 0)
        (lam * (fullMarkArmCellPartition n).cellMass
          (fullObservedMarkLaw P) (k, true))) := by
  let p := fullMarkArmCellPartition n
  let mu := finiteMarkedPoissonSampleLaw (fullObservedMarkLaw P)
    (Measure.dirac 0) lam
  let nu : Fin n × Bool → Measure (FiniteSample (FullObservedMark n × ℝ)) :=
    fun j => finiteMarkedPoissonSampleLaw
      (p.cellObservationLaw (fullObservedMarkLaw P) j) (Measure.dirac 0)
      (lam * p.cellMass (fullObservedMarkLaw P) j)
  have hjoint : Measure.map p.restrictPartition mu = Measure.pi nu := by
    exact map_restrictPartition_fullMarkPoisson P lam
  have hpair : Measure.map
      (fun z : (Fin n × Bool) → FiniteSample (FullObservedMark n × ℝ) =>
        (z (k, false), z (k, true))) (Measure.pi nu) =
      (nu (k, false)).prod (nu (k, true)) := by
    apply map_pi_eval_pair_local
    intro h
    cases congrArg Prod.snd h
  change Measure.map
      (fun s => (p.restrictCell (k, false) s, p.restrictCell (k, true) s)) mu =
    (nu (k, false)).prod (nu (k, true))
  calc
    _ = Measure.map
        (fun z : (Fin n × Bool) → FiniteSample (FullObservedMark n × ℝ) =>
          (z (k, false), z (k, true)))
        (Measure.map p.restrictPartition mu) := by
      rw [Measure.map_map
        ((measurable_pi_apply (k, false)).prodMk
          (measurable_pi_apply (k, true)))
        p.measurable_restrictPartition]
      rfl
    _ = Measure.map
        (fun z : (Fin n × Bool) → FiniteSample (FullObservedMark n × ℝ) =>
          (z (k, false), z (k, true))) (Measure.pi nu) := by rw [hjoint]
    _ = _ := hpair

/-- After retaining outcomes, the two positive arm-cells are independent
finite Poisson samples from their stipulated outcome laws. -/
-- keep: exact two-arm outcome law after full-mark Poisson partitioning
lemma map_fullMark_twoArmOutcomeSamples (P : Law n) (k : Fin n) (lam : ℝ≥0)
    (harm0 : 0 < armMass P false k) (harm1 : 0 < armMass P true k) :
    Measure.map
        (fun s =>
          (finiteSampleMap (fun z : FullObservedMark n × ℝ => z.1.2.2)
            ((fullMarkArmCellPartition n).restrictCell (k, false) s),
           finiteSampleMap (fun z : FullObservedMark n × ℝ => z.1.2.2)
            ((fullMarkArmCellPartition n).restrictCell (k, true) s)))
        (finiteMarkedPoissonSampleLaw (fullObservedMarkLaw P)
          (Measure.dirac 0) lam) =
      (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
        (P.outcome_isProbability false k)
        (lam * (fullMarkArmCellPartition n).cellMass
          (fullObservedMarkLaw P) (k, false))).prod
      (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
        (P.outcome_isProbability true k)
        (lam * (fullMarkArmCellPartition n).cellMass
          (fullObservedMarkLaw P) (k, true))) := by
  let p := fullMarkArmCellPartition n
  let g : FullObservedMark n × ℝ → ℝ := fun z => z.1.2.2
  let F := finiteSampleMap g
  let mu := finiteMarkedPoissonSampleLaw (fullObservedMarkLaw P)
    (Measure.dirac 0) lam
  let mu0 := finiteMarkedPoissonSampleLaw
    (p.cellObservationLaw (fullObservedMarkLaw P) (k, false))
    (Measure.dirac 0) (lam * p.cellMass (fullObservedMarkLaw P) (k, false))
  let mu1 := finiteMarkedPoissonSampleLaw
    (p.cellObservationLaw (fullObservedMarkLaw P) (k, true))
    (Measure.dirac 0) (lam * p.cellMass (fullObservedMarkLaw P) (k, true))
  have hF : Measurable F := measurable_finiteSampleMap g
    (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hmark : Measure.map
      (fun s => (p.restrictCell (k, false) s, p.restrictCell (k, true) s)) mu =
      mu0.prod mu1 := by
    exact map_fullMark_twoArmCells P k lam
  have h0 : Measure.map F mu0 =
      @finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
        (P.outcome_isProbability false k)
        (lam * p.cellMass (fullObservedMarkLaw P) (k, false)) := by
    exact map_cellFinitePoisson_outcomes P false k harm0 _
  have h1 : Measure.map F mu1 =
      @finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
        (P.outcome_isProbability true k)
        (lam * p.cellMass (fullObservedMarkLaw P) (k, true)) := by
    exact map_cellFinitePoisson_outcomes P true k harm1 _
  change Measure.map
      (fun s => (F (p.restrictCell (k, false) s),
        F (p.restrictCell (k, true) s))) mu = _
  calc
    _ = Measure.map (Prod.map F F)
        (Measure.map
          (fun s => (p.restrictCell (k, false) s,
            p.restrictCell (k, true) s)) mu) := by
      symm
      calc
        _ = Measure.map
            (Prod.map F F ∘ fun s =>
              (p.restrictCell (k, false) s,
                p.restrictCell (k, true) s)) mu :=
          Measure.map_map (hF.prodMap hF)
            ((p.measurable_restrictCell (k, false)).prodMk
              (p.measurable_restrictCell (k, true)))
        _ = _ := rfl
    _ = Measure.map (Prod.map F F) (mu0.prod mu1) := by rw [hmark]
    _ = (Measure.map F mu0).prod (Measure.map F mu1) := by
      rw [Measure.map_prod_map mu0 mu1 hF hF]
    _ = _ := by rw [h0, h1]

/-- The actual two-arm fixed-count numerator is a bilinear pair sum, placing
it directly in the scope of the fixed-count pair second-moment theorem. -/
lemma fixedCount_centeredNumerator_eq_pairSum (t : ℝ) (N0 N1 : ℕ)
    (y0 : Fin N0 → ℝ) (y1 : Fin N1 → ℝ) :
    (N0 : ℝ) * (∑ j : Fin N1, y1 j) -
        (N1 : ℝ) * (∑ i : Fin N0, y0 i) -
        t * (N0 : ℝ) * (N1 : ℝ) =
      ∑ i : Fin N0, ∑ j : Fin N1, (y1 j - y0 i - t) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul]
  have h0 : (N1 : ℝ) * (∑ i : Fin N0, y0 i) =
      ∑ i : Fin N0, (N1 : ℝ) * y0 i := by
    simpa using Finset.mul_sum Finset.univ y0 (N1 : ℝ)
  rw [h0]
  ring

/-- The four coincidence classes from the pair second-moment formula collect
to the conditional numerator's variance-plus-squared-mean expression. -/
lemma fixedCount_coincidence_moments_collapse (N0 N1 : ℕ) (V0 V1 d : ℝ) :
    (N0 : ℝ) * N1 * (V0 + V1 + d ^ 2) +
        (N0 : ℝ) * ((N1 : ℝ) * ((N1 : ℝ) - 1)) * (V0 + d ^ 2) +
        ((N0 : ℝ) * ((N0 : ℝ) - 1)) * N1 * (V1 + d ^ 2) +
        ((N0 : ℝ) * ((N0 : ℝ) - 1)) *
          ((N1 : ℝ) * ((N1 : ℝ) - 1)) * d ^ 2 =
      (N0 : ℝ) ^ 2 * N1 * V1 +
        (N1 : ℝ) ^ 2 * N0 * V0 +
        (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 * d ^ 2 := by
  ring

noncomputable def centeredNumeratorKernel (P : Law n) (k : Fin n) (t : ℝ)
    (y0 y1 : ℝ) : ℝ := y1 - y0 - t

/-- The one-pair kernel has mean equal to the cell effect minus the pilot
center. -/
-- keep: first-moment API for the centered numerator kernel
lemma centeredNumeratorKernel_mean (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    (∫ y0, ∫ y1, centeredNumeratorKernel P k t y0 y1
        ∂P.outcomeLaw true k ∂P.outcomeLaw false k) =
      DiscreteAteHeterogeneityFrontier.cellEffect P k - t := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  have h0 : Integrable (fun y : ℝ => y) (P.outcomeLaw false k) :=
    CausalSmith.Stat.DiscreteAteHeterogeneityFrontier.outcome_integrable_of_second_moment
      P hvariance false k hp
  have h1 : Integrable (fun y : ℝ => y) (P.outcomeLaw true k) :=
    CausalSmith.Stat.DiscreteAteHeterogeneityFrontier.outcome_integrable_of_second_moment
      P hvariance true k hp
  have hinner (y0 : ℝ) :
      (∫ y1, centeredNumeratorKernel P k t y0 y1
        ∂P.outcomeLaw true k) = P.outcomeMean true k - y0 - t := by
    unfold centeredNumeratorKernel
    change (∫ y1, (fun y : ℝ => y - y0) y1 -
      (fun _ : ℝ => t) y1 ∂P.outcomeLaw true k) = _
    calc
      _ = (∫ y1, y1 - y0 ∂P.outcomeLaw true k) -
          ∫ _y1 : ℝ, t ∂P.outcomeLaw true k :=
        integral_sub (h1.sub (integrable_const _)) (integrable_const _)
      _ = ((∫ y1, y1 ∂P.outcomeLaw true k) -
          ∫ _y1 : ℝ, y0 ∂P.outcomeLaw true k) -
          ∫ _y1 : ℝ, t ∂P.outcomeLaw true k := by
        rw [integral_sub h1 (integrable_const _)]
      _ = _ := by
        rw [← P.outcomeMean_eq true k, integral_const, integral_const,
          probReal_univ]
        simp
  simp_rw [hinner]
  change (∫ y0, (fun y : ℝ => P.outcomeMean true k - y) y0 -
    (fun _ : ℝ => t) y0 ∂P.outcomeLaw false k) = _
  calc
    _ = (∫ y0, P.outcomeMean true k - y0 ∂P.outcomeLaw false k) -
        ∫ _y0 : ℝ, t ∂P.outcomeLaw false k :=
      integral_sub ((integrable_const _).sub h0) (integrable_const _)
    _ = ((∫ _y0 : ℝ, P.outcomeMean true k ∂P.outcomeLaw false k) -
        ∫ y0, y0 ∂P.outcomeLaw false k) -
        ∫ _y0 : ℝ, t ∂P.outcomeLaw false k := by
      rw [integral_sub (integrable_const _) h0]
    _ = _ := by
      rw [← P.outcomeMean_eq false k, integral_const, integral_const,
        probReal_univ]
      simp only [one_smul]
      unfold DiscreteAteHeterogeneityFrontier.cellEffect
      ring

lemma centeredNumeratorKernel_sq_mean (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    (∫ y0, ∫ y1, centeredNumeratorKernel P k t y0 y1 ^ 2
        ∂P.outcomeLaw true k ∂P.outcomeLaw false k) =
      (∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k) +
      (∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) +
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  let r0 : ℝ → ℝ := fun y => y - P.outcomeMean false k
  let r1 : ℝ → ℝ := fun y => y - P.outcomeMean true k
  let d : ℝ := DiscreteAteHeterogeneityFrontier.cellEffect P k - t
  have hr0 := outcomeResidual_integrable P false k hp hvariance
  have hr1 := outcomeResidual_integrable P true k hp hvariance
  have hr0sq : Integrable (fun y => r0 y ^ 2) (P.outcomeLaw false k) := by
    simpa [r0] using (hvariance false k hp).1
  have hr1sq : Integrable (fun y => r1 y ^ 2) (P.outcomeLaw true k) := by
    simpa [r1] using (hvariance true k hp).1
  have hr0mean : (∫ y, r0 y ∂P.outcomeLaw false k) = 0 := by
    simpa [r0] using outcomeResidual_mean P false k hp hvariance
  have hr1mean : (∫ y, r1 y ∂P.outcomeLaw true k) = 0 := by
    simpa [r1] using outcomeResidual_mean P true k hp hvariance
  have hinner (y0 : ℝ) :
      (∫ y1, centeredNumeratorKernel P k t y0 y1 ^ 2
        ∂P.outcomeLaw true k) =
        (∫ y1, r1 y1 ^ 2 ∂P.outcomeLaw true k) + (d - r0 y0) ^ 2 := by
    calc
      _ = ∫ y1, (r1 y1 + (d - r0 y0)) ^ 2 ∂P.outcomeLaw true k := by
        congr 1
        funext y1
        unfold centeredNumeratorKernel r0 r1 d
        unfold DiscreteAteHeterogeneityFrontier.cellEffect
        ring
      _ = _ := integral_centered_add_const_sq (P.outcomeLaw true k)
        r1 hr1 hr1sq hr1mean (d - r0 y0)
  simp_rw [hinner]
  have hshift : Integrable (fun y0 => (d - r0 y0) ^ 2)
      (P.outcomeLaw false k) := by
    have h := integrable_add_const_sq (P.outcomeLaw false k)
      (fun y => -r0 y) hr0.neg (by simpa using hr0sq) d
    simpa [sub_eq_add_neg, add_comm] using h
  rw [integral_add (integrable_const _) hshift, integral_const,
    probReal_univ, one_smul]
  have hout := integral_centered_add_const_sq (P.outcomeLaw false k)
    (fun y => -r0 y) hr0.neg (by simpa using hr0sq)
      (by
        rw [integral_neg, hr0mean, neg_zero]) d
  have hrewrite : (∫ y, (d - r0 y) ^ 2 ∂P.outcomeLaw false k) =
      ∫ y, (-r0 y + d) ^ 2 ∂P.outcomeLaw false k := by
    congr 1
    funext y
    ring
  rw [hrewrite, hout]
  have hneg0 : (∫ y, (-r0 y) ^ 2 ∂P.outcomeLaw false k) =
      ∫ y, r0 y ^ 2 ∂P.outcomeLaw false k := by
    apply integral_congr_ae
    filter_upwards with y
    ring
  rw [hneg0]
  change (∫ y, r1 y ^ 2 ∂P.outcomeLaw true k) +
      ((∫ y, r0 y ^ 2 ∂P.outcomeLaw false k) + d ^ 2) =
    (∫ y, r0 y ^ 2 ∂P.outcomeLaw false k) +
      (∫ y, r1 y ^ 2 ∂P.outcomeLaw true k) + d ^ 2
  ring

lemma centeredNumeratorKernel_mean_true (P : Law n) (k : Fin n) (t y0 : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    (∫ y1, centeredNumeratorKernel P k t y0 y1 ∂P.outcomeLaw true k) =
      DiscreteAteHeterogeneityFrontier.cellEffect P k - t -
        (y0 - P.outcomeMean false k) := by
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  let r1 : ℝ → ℝ := fun y => y - P.outcomeMean true k
  let c := DiscreteAteHeterogeneityFrontier.cellEffect P k - t -
    (y0 - P.outcomeMean false k)
  have hr1 := outcomeResidual_integrable P true k hp hvariance
  have hm := outcomeResidual_mean P true k hp hvariance
  calc
    _ = ∫ y1, r1 y1 + c ∂P.outcomeLaw true k := by
      congr 1
      funext y1
      unfold centeredNumeratorKernel r1 c
      unfold DiscreteAteHeterogeneityFrontier.cellEffect
      ring
    _ = c := integral_centered_add_const (P.outcomeLaw true k) r1 hr1
      (by simpa [r1] using hm) c
    _ = _ := rfl

-- keep: conditional first-moment identity for the false-arm integration order
lemma centeredNumeratorKernel_mean_false (P : Law n) (k : Fin n) (t y1 : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    (∫ y0, centeredNumeratorKernel P k t y0 y1 ∂P.outcomeLaw false k) =
      (y1 - P.outcomeMean true k) +
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  let r0 : ℝ → ℝ := fun y => y - P.outcomeMean false k
  let c := (y1 - P.outcomeMean true k) +
    (DiscreteAteHeterogeneityFrontier.cellEffect P k - t)
  have hr0 := outcomeResidual_integrable P false k hp hvariance
  have hm := outcomeResidual_mean P false k hp hvariance
  calc
    _ = ∫ y0, (-r0 y0) + c ∂P.outcomeLaw false k := by
      congr 1
      funext y0
      unfold centeredNumeratorKernel r0 c
      unfold DiscreteAteHeterogeneityFrontier.cellEffect
      ring
    _ = c := integral_centered_add_const (P.outcomeLaw false k)
      (fun y => -r0 y) hr0.neg (by rw [integral_neg]; simpa [r0] using hm) c
    _ = _ := rfl

lemma centeredNumeratorKernel_shared_left (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    (∫ y0, ∫ y1, ∫ y1',
      centeredNumeratorKernel P k t y0 y1 *
        centeredNumeratorKernel P k t y0 y1'
      ∂P.outcomeLaw true k ∂P.outcomeLaw true k
      ∂P.outcomeLaw false k) =
      (∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k) +
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  let r0 : ℝ → ℝ := fun y => y - P.outcomeMean false k
  let d := DiscreteAteHeterogeneityFrontier.cellEffect P k - t
  have hr0 := outcomeResidual_integrable P false k hp hvariance
  have hr0sq : Integrable (fun y => r0 y ^ 2) (P.outcomeLaw false k) := by
    simpa [r0] using (hvariance false k hp).1
  have hr0mean : (∫ y, r0 y ∂P.outcomeLaw false k) = 0 := by
    simpa [r0] using outcomeResidual_mean P false k hp hvariance
  simp_rw [integral_const_mul,
    centeredNumeratorKernel_mean_true P k t _ hp hvariance,
    integral_mul_const,
    centeredNumeratorKernel_mean_true P k t _ hp hvariance]
  rw [show (fun y0 : ℝ =>
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t -
          (y0 - P.outcomeMean false k)) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t -
          (y0 - P.outcomeMean false k))) =
      fun y0 => (d - r0 y0) ^ 2 by
        funext y0
        dsimp [d, r0]
        rw [pow_two]]
  change (∫ y, (d - r0 y) ^ 2 ∂P.outcomeLaw false k) =
    (∫ y, r0 y ^ 2 ∂P.outcomeLaw false k) + d ^ 2
  have hout := integral_centered_add_const_sq (P.outcomeLaw false k)
    (fun y => -r0 y) hr0.neg (by simpa using hr0sq)
      (by rw [integral_neg, hr0mean, neg_zero]) d
  have hrewrite : (∫ y, (d - r0 y) ^ 2 ∂P.outcomeLaw false k) =
      ∫ y, (-r0 y + d) ^ 2 ∂P.outcomeLaw false k := by
    congr 1
    funext y
    ring
  rw [hrewrite, hout]
  have hneg : (∫ y, (-r0 y) ^ 2 ∂P.outcomeLaw false k) =
      ∫ y, r0 y ^ 2 ∂P.outcomeLaw false k := by
    apply integral_congr_ae
    filter_upwards with y
    ring
  rw [hneg]

lemma centeredNumeratorKernel_shared_right (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    (∫ y0, ∫ y0', ∫ y1,
      centeredNumeratorKernel P k t y0 y1 *
        centeredNumeratorKernel P k t y0' y1
      ∂P.outcomeLaw true k ∂P.outcomeLaw false k
      ∂P.outcomeLaw false k) =
      (∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) +
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  let r0 : ℝ → ℝ := fun y => y - P.outcomeMean false k
  let r1 : ℝ → ℝ := fun y => y - P.outcomeMean true k
  let d := DiscreteAteHeterogeneityFrontier.cellEffect P k - t
  have hr0 := outcomeResidual_integrable P false k hp hvariance
  have hr1 := outcomeResidual_integrable P true k hp hvariance
  have hr1sq : Integrable (fun y => r1 y ^ 2) (P.outcomeLaw true k) := by
    simpa [r1] using (hvariance true k hp).1
  have hr0mean : (∫ y, r0 y ∂P.outcomeLaw false k) = 0 := by
    simpa [r0] using outcomeResidual_mean P false k hp hvariance
  have hr1mean : (∫ y, r1 y ∂P.outcomeLaw true k) = 0 := by
    simpa [r1] using outcomeResidual_mean P true k hp hvariance
  have hinner (y0 y0' : ℝ) :
      (∫ y1, centeredNumeratorKernel P k t y0 y1 *
          centeredNumeratorKernel P k t y0' y1
        ∂P.outcomeLaw true k) =
        (∫ y1, r1 y1 ^ 2 ∂P.outcomeLaw true k) +
          (d - r0 y0) * (d - r0 y0') := by
    calc
      _ = ∫ y1, (r1 y1 + (d - r0 y0)) *
          (r1 y1 + (d - r0 y0')) ∂P.outcomeLaw true k := by
        congr 1
        funext y1
        unfold centeredNumeratorKernel r0 r1 d
        unfold DiscreteAteHeterogeneityFrontier.cellEffect
        ring
      _ = _ := integral_centered_add_const_mul (P.outcomeLaw true k)
        r1 hr1 hr1sq hr1mean (d - r0 y0) (d - r0 y0')
  simp_rw [hinner]
  let V1 : ℝ := ∫ y, r1 y ^ 2 ∂P.outcomeLaw true k
  let c : ℝ → ℝ := fun y => d - r0 y
  have hc : Integrable c (P.outcomeLaw false k) := by
    apply (hr0.neg.add
      (integrable_const d : Integrable (fun _ : ℝ => d)
        (P.outcomeLaw false k))).congr
    filter_upwards with y
    dsimp [c]
    ring
  have hcmean : (∫ y, d - r0 y ∂P.outcomeLaw false k) = d := by
    have := integral_centered_add_const (P.outcomeLaw false k)
      (fun y => -r0 y) hr0.neg (by rw [integral_neg, hr0mean, neg_zero]) d
    simpa [sub_eq_add_neg, add_comm] using this
  have hcmean' : (∫ y, c y ∂P.outcomeLaw false k) = d := by
    simpa [c] using hcmean
  have hmid (y0 : ℝ) :
      (∫ y0', V1 + c y0 * c y0' ∂P.outcomeLaw false k) =
        V1 + c y0 * d := by
    calc
      _ = (∫ _ : ℝ, V1 ∂P.outcomeLaw false k) +
          ∫ y0', c y0 * c y0' ∂P.outcomeLaw false k :=
        integral_add (integrable_const _) (hc.const_mul (c y0))
      _ = V1 + c y0 * d := by
        rw [integral_const, probReal_univ, one_smul,
          integral_const_mul, hcmean']
  change (∫ y0, ∫ y0', V1 + c y0 * c y0'
      ∂P.outcomeLaw false k ∂P.outcomeLaw false k) = V1 + d ^ 2
  simp_rw [hmid]
  calc
    _ = (∫ _ : ℝ, V1 ∂P.outcomeLaw false k) +
        ∫ y0, c y0 * d ∂P.outcomeLaw false k :=
      integral_add (integrable_const _) (hc.mul_const d)
    _ = V1 + d * d := by
      rw [integral_const, probReal_univ, one_smul,
        integral_mul_const, hcmean']
    _ = V1 + d ^ 2 := by ring

lemma centeredNumeratorKernel_both_distinct (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    (∫ y0, ∫ y0', ∫ y1, ∫ y1',
      centeredNumeratorKernel P k t y0 y1 *
        centeredNumeratorKernel P k t y0' y1'
      ∂P.outcomeLaw true k ∂P.outcomeLaw true k
      ∂P.outcomeLaw false k ∂P.outcomeLaw false k) =
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  let d := DiscreteAteHeterogeneityFrontier.cellEffect P k - t
  let r0 : ℝ → ℝ := fun y => y - P.outcomeMean false k
  let c : ℝ → ℝ := fun y => d - r0 y
  have hr0 := outcomeResidual_integrable P false k hp hvariance
  have hr0mean : (∫ y, r0 y ∂P.outcomeLaw false k) = 0 := by
    simpa [r0] using outcomeResidual_mean P false k hp hvariance
  have hcmean : (∫ y, c y ∂P.outcomeLaw false k) = d := by
    have h := integral_centered_add_const (P.outcomeLaw false k)
      (fun y => -r0 y) hr0.neg
      (by rw [integral_neg, hr0mean, neg_zero]) d
    simpa [c, sub_eq_add_neg, add_comm] using h
  simp_rw [integral_const_mul,
    centeredNumeratorKernel_mean_true P k t _ hp hvariance,
    integral_mul_const,
    centeredNumeratorKernel_mean_true P k t _ hp hvariance]
  change (∫ y0, ∫ y0', c y0 * c y0'
      ∂P.outcomeLaw false k ∂P.outcomeLaw false k) = d ^ 2
  simp_rw [integral_const_mul, hcmean]
  rw [integral_mul_const, hcmean]
  ring

lemma centeredNumeratorKernel_sq_integrable (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P) :
    Integrable (fun p : ℝ × ℝ => centeredNumeratorKernel P k t p.1 p.2 ^ 2)
      ((P.outcomeLaw false k).prod (P.outcomeLaw true k)) := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  let r0 : ℝ → ℝ := fun y => y - P.outcomeMean false k
  let r1 : ℝ → ℝ := fun y => y - P.outcomeMean true k
  let d := DiscreteAteHeterogeneityFrontier.cellEffect P k - t
  have hr0 := outcomeResidual_integrable P false k hp hvariance
  have hr1 := outcomeResidual_integrable P true k hp hvariance
  have hr0sq : Integrable (fun y => r0 y ^ 2) (P.outcomeLaw false k) := by
    simpa [r0] using (hvariance false k hp).1
  have hr1sq : Integrable (fun y => r1 y ^ 2) (P.outcomeLaw true k) := by
    simpa [r1] using (hvariance true k hp).1
  have h0sq := hr0sq.comp_fst (P.outcomeLaw true k)
  have h1sq := hr1sq.comp_snd (P.outcomeLaw false k)
  have h01 := hr0.mul_prod hr1
  have h0 := hr0.comp_fst (P.outcomeLaw true k)
  have h1 := hr1.comp_snd (P.outcomeLaw false k)
  have hsum := ((((h1sq.add h0sq).add (h01.const_mul (-2))).add
    (h1.const_mul (2 * d))).add (h0.const_mul (-2 * d))).add
      (integrable_const (d ^ 2) : Integrable (fun _ : ℝ × ℝ => d ^ 2)
        ((P.outcomeLaw false k).prod (P.outcomeLaw true k)))
  apply hsum.congr
  filter_upwards with p
  change (((((r1 p.2 ^ 2 + r0 p.1 ^ 2) +
      (-2) * (r0 p.1 * r1 p.2)) +
      (2 * d) * r1 p.2) + (-2 * d) * r0 p.1) + d ^ 2) =
    centeredNumeratorKernel P k t p.1 p.2 ^ 2
  unfold centeredNumeratorKernel r0 r1 d
  unfold DiscreteAteHeterogeneityFrontier.cellEffect
  ring

/-- At fixed arm counts, the centered cell numerator has exactly the
variance-plus-squared-mean moment used by the variance audit. -/
lemma fixedCount_centeredNumerator_second (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P)
    (N0 N1 : ℕ) :
    (∫ p : (Fin N0 → ℝ) × (Fin N1 → ℝ),
      ((N0 : ℝ) * (∑ j : Fin N1, p.2 j) -
        (N1 : ℝ) * (∑ i : Fin N0, p.1 i) -
        t * (N0 : ℝ) * (N1 : ℝ)) ^ 2
      ∂((Measure.pi fun _ : Fin N0 => P.outcomeLaw false k).prod
        (Measure.pi fun _ : Fin N1 => P.outcomeLaw true k))) =
      conditionalNumeratorSecond P k t N0 N1 := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  let K := centeredNumeratorKernel P k t
  have hK : Measurable (Function.uncurry K) := by
    exact (measurable_snd.sub measurable_fst).sub measurable_const
  have hK2 : Integrable (fun p : ℝ × ℝ => K p.1 p.2 ^ 2)
      ((P.outcomeLaw false k).prod (P.outcomeLaw true k)) := by
    simpa [K] using centeredNumeratorKernel_sq_integrable P k t hp hvariance
  have hrewrite :
      (fun p : (Fin N0 → ℝ) × (Fin N1 → ℝ) =>
        ((N0 : ℝ) * (∑ j : Fin N1, p.2 j) -
          (N1 : ℝ) * (∑ i : Fin N0, p.1 i) -
          t * (N0 : ℝ) * (N1 : ℝ)) ^ 2) =
      fun p => (∑ i : Fin N0, ∑ j : Fin N1, K (p.1 i) (p.2 j)) ^ 2 := by
    funext p
    rw [fixedCount_centeredNumerator_eq_pairSum]
    rfl
  rw [hrewrite]
  rw [Causalean.Mathlib.Probability.Poisson.PairSecondMoment.integral_fixedCount_pairSum_sq
    (P.outcomeLaw false k) (P.outcomeLaw true k) K N0 N1 hK hK2]
  rw [show (∫ y0, ∫ y1, K y0 y1 * K y0 y1
        ∂P.outcomeLaw true k ∂P.outcomeLaw false k) =
      (∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k) +
      (∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) +
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 by
        simpa only [K, pow_two] using
          centeredNumeratorKernel_sq_mean P k t hp hvariance]
  rw [show (∫ y0, ∫ y1, ∫ y1', K y0 y1 * K y0 y1'
        ∂P.outcomeLaw true k ∂P.outcomeLaw true k
        ∂P.outcomeLaw false k) =
      (∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k) +
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 by
        simpa only [K] using
          centeredNumeratorKernel_shared_left P k t hp hvariance]
  rw [show (∫ y0, ∫ y0', ∫ y1, K y0 y1 * K y0' y1
        ∂P.outcomeLaw true k ∂P.outcomeLaw false k
        ∂P.outcomeLaw false k) =
      (∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) +
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 by
        simpa only [K] using
          centeredNumeratorKernel_shared_right P k t hp hvariance]
  rw [show (∫ y0, ∫ y0', ∫ y1, ∫ y1', K y0 y1 * K y0' y1'
        ∂P.outcomeLaw true k ∂P.outcomeLaw true k
        ∂P.outcomeLaw false k ∂P.outcomeLaw false k) =
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 by
        simpa only [K] using
          centeredNumeratorKernel_both_distinct P k t hp hvariance]
  unfold conditionalNumeratorSecond
  exact fixedCount_coincidence_moments_collapse N0 N1
    (∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k)
    (∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k)
    (DiscreteAteHeterogeneityFrontier.cellEffect P k - t)

/-- At fixed arm counts, the centered numerator has mean
`N0*N1*(cellEffect-t)`. -/
lemma fixedCount_centeredNumerator_first (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P)
    (N0 N1 : ℕ) :
    (∫ p : (Fin N0 → ℝ) × (Fin N1 → ℝ),
      ((N0 : ℝ) * (∑ j : Fin N1, p.2 j) -
        (N1 : ℝ) * (∑ i : Fin N0, p.1 i) -
        t * (N0 : ℝ) * (N1 : ℝ))
      ∂((Measure.pi fun _ : Fin N0 => P.outcomeLaw false k).prod
        (Measure.pi fun _ : Fin N1 => P.outcomeLaw true k))) =
      (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  let Q0 := P.outcomeLaw false k
  let Q1 := P.outcomeLaw true k
  let r0 : ℝ → ℝ := fun y => y - P.outcomeMean false k
  let r1 : ℝ → ℝ := fun y => y - P.outcomeMean true k
  let A : (Fin N0 → ℝ) → ℝ := fun y => ∑ i : Fin N0, r0 (y i)
  let B : (Fin N1 → ℝ) → ℝ := fun y => ∑ j : Fin N1, r1 (y j)
  let d := DiscreteAteHeterogeneityFrontier.cellEffect P k - t
  have hr0 := outcomeResidual_integrable P false k hp hvariance
  have hr1 := outcomeResidual_integrable P true k hp hvariance
  have hA : Integrable A (Measure.pi fun _ : Fin N0 => Q0) := by
    apply integrable_finsetSum
    intro i hi
    exact integrable_comp_eval (i := i) hr0
  have hB : Integrable B (Measure.pi fun _ : Fin N1 => Q1) := by
    apply integrable_finsetSum
    intro j hj
    exact integrable_comp_eval (i := j) hr1
  have hAmean : (∫ y, A y ∂Measure.pi fun _ : Fin N0 => Q0) = 0 := by
    simpa [A, r0, Q0] using
      integral_iid_outcome_residual_sum P false k hp hvariance N0
  have hBmean : (∫ y, B y ∂Measure.pi fun _ : Fin N1 => Q1) = 0 := by
    simpa [B, r1, Q1] using
      integral_iid_outcome_residual_sum P true k hp hvariance N1
  have hAprod : (∫ p, A p.1 ∂(Measure.pi fun _ : Fin N0 => Q0).prod
      (Measure.pi fun _ : Fin N1 => Q1)) = 0 := by
    rw [integral_prod _ (hA.comp_fst (Measure.pi fun _ : Fin N1 => Q1))]
    simp_rw [integral_const, probReal_univ, one_smul]
    exact hAmean
  have hBprod : (∫ p, B p.2 ∂(Measure.pi fun _ : Fin N0 => Q0).prod
      (Measure.pi fun _ : Fin N1 => Q1)) = 0 := by
    rw [integral_prod _ (hB.comp_snd (Measure.pi fun _ : Fin N0 => Q0))]
    simp_rw [hBmean]
    simp
  have hrewrite :
      (fun p : (Fin N0 → ℝ) × (Fin N1 → ℝ) =>
        (N0 : ℝ) * (∑ j : Fin N1, p.2 j) -
          (N1 : ℝ) * (∑ i : Fin N0, p.1 i) -
          t * (N0 : ℝ) * (N1 : ℝ)) =
      fun p => (N0 : ℝ) * B p.2 - (N1 : ℝ) * A p.1 +
        (N0 : ℝ) * (N1 : ℝ) * d := by
    funext p
    simp only [A, B, r0, r1, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul]
    unfold d DiscreteAteHeterogeneityFrontier.cellEffect
    ring
  rw [hrewrite]
  have hlinear : Integrable
      (fun p => (N0 : ℝ) * B p.2 - (N1 : ℝ) * A p.1)
      ((Measure.pi fun _ : Fin N0 => Q0).prod
        (Measure.pi fun _ : Fin N1 => Q1)) :=
    (hB.comp_snd (Measure.pi fun _ : Fin N0 => Q0)).const_mul _ |>.sub
      ((hA.comp_fst (Measure.pi fun _ : Fin N1 => Q1)).const_mul _)
  rw [integral_add hlinear (integrable_const _),
    integral_sub
      ((hB.comp_snd (Measure.pi fun _ : Fin N0 => Q0)).const_mul _)
      ((hA.comp_fst (Measure.pi fun _ : Fin N1 => Q1)).const_mul _),
    integral_const_mul, hBprod, mul_zero,
    integral_const_mul, hAprod, mul_zero, sub_zero,
    integral_const, probReal_univ, one_smul, zero_add]

/-- The same exact numerator identity after mixing the two independent arm
counts with arbitrary Poisson rates. -/
-- keep: exact Poissonized second moment of the centered numerator
lemma poisson_centeredNumerator_second (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P)
    (rate0 rate1 : ℝ≥0) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 ^ 2
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1))) =
      (rate0 : ℝ) * (rate1 : ℝ) *
        ((∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k) +
          (∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) +
          (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2) +
      (rate0 : ℝ) * (rate1 : ℝ) ^ 2 *
        ((∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k) +
          (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2) +
      (rate0 : ℝ) ^ 2 * (rate1 : ℝ) *
        ((∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) +
          (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2) +
      (rate0 : ℝ) ^ 2 * (rate1 : ℝ) ^ 2 *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  let K := centeredNumeratorKernel P k t
  have hK : Measurable (Function.uncurry K) :=
    (measurable_snd.sub measurable_fst).sub measurable_const
  have hK2 : Integrable (fun p : ℝ × ℝ => K p.1 p.2 ^ 2)
      ((P.outcomeLaw false k).prod (P.outcomeLaw true k)) := by
    simpa [K] using centeredNumeratorKernel_sq_integrable P k t hp hvariance
  rw [Causalean.Mathlib.Probability.Poisson.PairSecondMoment.integral_pairSum_sq
    (P.outcomeLaw false k) (P.outcomeLaw true k) rate0 rate1 K hK hK2]
  rw [show (∫ y0, ∫ y1, K y0 y1 * K y0 y1
        ∂P.outcomeLaw true k ∂P.outcomeLaw false k) =
      (∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k) +
      (∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) +
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 by
        simpa only [K, pow_two] using
          centeredNumeratorKernel_sq_mean P k t hp hvariance]
  rw [show (∫ y0, ∫ y1, ∫ y1', K y0 y1 * K y0 y1'
        ∂P.outcomeLaw true k ∂P.outcomeLaw true k
        ∂P.outcomeLaw false k) =
      (∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k) +
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 by
        simpa only [K] using
          centeredNumeratorKernel_shared_left P k t hp hvariance]
  rw [show (∫ y0, ∫ y0', ∫ y1, K y0 y1 * K y0' y1
        ∂P.outcomeLaw true k ∂P.outcomeLaw false k
        ∂P.outcomeLaw false k) =
      (∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) +
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 by
        simpa only [K] using
          centeredNumeratorKernel_shared_right P k t hp hvariance]
  rw [show (∫ y0, ∫ y0', ∫ y1, ∫ y1', K y0 y1 * K y0' y1'
        ∂P.outcomeLaw true k ∂P.outcomeLaw true k
        ∂P.outcomeLaw false k ∂P.outcomeLaw false k) =
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 by
        simpa only [K] using
          centeredNumeratorKernel_both_distinct P k t hp hvariance]

/-- Count-fibre disintegration for a squared centered numerator multiplied by
an arbitrary count weight.  The hypotheses expose exactly the three
integrability obligations later discharged by the light/heavy envelopes. -/
lemma poisson_centeredNumerator_second_weighted
    (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P)
    (rate0 rate1 : ℝ≥0) (w : ℕ → ℕ → ℝ)
    (hstat : Integrable
      (fun p : FiniteSample ℝ × FiniteSample ℝ =>
        Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
          (centeredNumeratorKernel P k t) p.1 p.2 ^ 2 *
            w p.1.count p.2.count)
      ((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1)))
    (hinner : ∀ N0, Integrable
      (fun N1 => conditionalNumeratorSecond P k t N0 N1 * w N0 N1)
      (poissonMeasure rate1))
    (houter : Integrable
      (fun N0 => ∫ N1, conditionalNumeratorSecond P k t N0 N1 * w N0 N1
        ∂poissonMeasure rate1) (poissonMeasure rate0)) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 ^ 2 *
          w p.1.count p.2.count
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1))) =
      ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 * w N0 N1
        ∂poissonMeasure rate1 ∂poissonMeasure rate0 := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  let K := centeredNumeratorKernel P k t
  rw [Causalean.Mathlib.Probability.Poisson.PairSecondMoment.integral_pair_count_mixture
    (P.outcomeLaw false k) (P.outcomeLaw true k) rate0 rate1 _ hstat]
  have hfixed (N0 N1 : ℕ) :
      (∫ p : (Fin N0 → ℝ) × (Fin N1 → ℝ),
        (∑ i : Fin N0, ∑ j : Fin N1, K (p.1 i) (p.2 j)) ^ 2 * w N0 N1
        ∂((Measure.pi fun _ : Fin N0 => P.outcomeLaw false k).prod
          (Measure.pi fun _ : Fin N1 => P.outcomeLaw true k))) =
        conditionalNumeratorSecond P k t N0 N1 * w N0 N1 := by
    rw [integral_mul_const]
    have hrewrite :
        (fun p : (Fin N0 → ℝ) × (Fin N1 → ℝ) =>
          (∑ i : Fin N0, ∑ j : Fin N1, K (p.1 i) (p.2 j)) ^ 2) =
        fun p => ((N0 : ℝ) * (∑ j : Fin N1, p.2 j) -
          (N1 : ℝ) * (∑ i : Fin N0, p.1 i) -
          t * (N0 : ℝ) * (N1 : ℝ)) ^ 2 := by
      funext p
      rw [fixedCount_centeredNumerator_eq_pairSum]
      rfl
    rw [hrewrite]
    rw [fixedCount_centeredNumerator_second P k t hp hvariance N0 N1]
  simp only [FiniteSample.count,
    Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum]
  have hfixed' (N0 N1 : ℕ) :
      (∫ p : (Fin N0 → ℝ) × (Fin N1 → ℝ),
        (∑ i : Fin N0, ∑ j : Fin N1,
          centeredNumeratorKernel P k t (p.1 i) (p.2 j)) ^ 2 * w N0 N1
        ∂((Measure.pi fun _ : Fin N0 => P.outcomeLaw false k).prod
          (Measure.pi fun _ : Fin N1 => P.outcomeLaw true k))) =
        conditionalNumeratorSecond P k t N0 N1 * w N0 N1 := by
    simpa only [K] using hfixed N0 N1
  simp_rw [hfixed']
  have hout := integral_countable houter
  have hin (N0 : ℕ) := integral_countable (hinner N0)
  rw [hout]
  simp only [measureReal_def] at hin
  simp_rw [hin]
  simp only [smul_eq_mul, measureReal_def]
  apply tsum_congr
  intro N0
  have hsabs := (hinner N0).summable_of_dirac
  have hs : Summable (fun N1 =>
      ((poissonMeasure rate1) ({N1} : Set ℕ)).toReal *
        (conditionalNumeratorSecond P k t N0 N1 * w N0 N1)) := by
    apply Summable.of_norm
    simpa only [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg,
      poissonMeasure_singleton_eq_poissonPMF,
      ← poissonPMFReal_ofReal_eq_poissonPMF,
      poissonPMFReal] using hsabs
  rw [← hs.tsum_mul_left
    ((poissonMeasure rate0) ({N0} : Set ℕ)).toReal]
  apply tsum_congr
  intro N1
  ring

/-- Count-fibre disintegration for the centered numerator multiplied by an
arbitrary count weight. -/
lemma poisson_centeredNumerator_first_weighted
    (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P)
    (rate0 rate1 : ℝ≥0) (w : ℕ → ℕ → ℝ)
    (hstat : Integrable
      (fun p : FiniteSample ℝ × FiniteSample ℝ =>
        Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
          (centeredNumeratorKernel P k t) p.1 p.2 *
            w p.1.count p.2.count)
      ((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1)))
    (hinner : ∀ N0 : ℕ, Integrable
      (fun N1 : ℕ => (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1)
      (poissonMeasure rate1))
    (houter : Integrable
      (fun N0 : ℕ => ∫ N1 : ℕ, (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1
        ∂poissonMeasure rate1) (poissonMeasure rate0)) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 * w p.1.count p.2.count
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1))) =
      ∫ N0, ∫ N1, (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1
        ∂poissonMeasure rate1 ∂poissonMeasure rate0 := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  let K := centeredNumeratorKernel P k t
  rw [Causalean.Mathlib.Probability.Poisson.PairSecondMoment.integral_pair_count_mixture
    (P.outcomeLaw false k) (P.outcomeLaw true k) rate0 rate1 _ hstat]
  have hfixed (N0 N1 : ℕ) :
      (∫ p : (Fin N0 → ℝ) × (Fin N1 → ℝ),
        (∑ i : Fin N0, ∑ j : Fin N1, K (p.1 i) (p.2 j)) * w N0 N1
        ∂((Measure.pi fun _ : Fin N0 => P.outcomeLaw false k).prod
          (Measure.pi fun _ : Fin N1 => P.outcomeLaw true k))) =
        (N0 : ℝ) * (N1 : ℝ) *
          (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1 := by
    rw [integral_mul_const]
    have hrewrite :
        (fun p : (Fin N0 → ℝ) × (Fin N1 → ℝ) =>
          ∑ i : Fin N0, ∑ j : Fin N1, K (p.1 i) (p.2 j)) =
        fun p => (N0 : ℝ) * (∑ j : Fin N1, p.2 j) -
          (N1 : ℝ) * (∑ i : Fin N0, p.1 i) -
          t * (N0 : ℝ) * (N1 : ℝ) := by
      funext p
      rw [fixedCount_centeredNumerator_eq_pairSum]
      rfl
    rw [hrewrite, fixedCount_centeredNumerator_first P k t hp hvariance N0 N1]
  simp only [FiniteSample.count,
    Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum]
  have hfixed' (N0 N1 : ℕ) :
      (∫ p : (Fin N0 → ℝ) × (Fin N1 → ℝ),
        (∑ i : Fin N0, ∑ j : Fin N1,
          centeredNumeratorKernel P k t (p.1 i) (p.2 j)) * w N0 N1
        ∂((Measure.pi fun _ : Fin N0 => P.outcomeLaw false k).prod
          (Measure.pi fun _ : Fin N1 => P.outcomeLaw true k))) =
        (N0 : ℝ) * (N1 : ℝ) *
          (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1 := by
    simpa only [K] using hfixed N0 N1
  simp_rw [hfixed']
  have hout := integral_countable houter
  have hin (N0 : ℕ) := integral_countable (hinner N0)
  rw [hout]
  simp only [measureReal_def] at hin
  simp_rw [hin]
  simp only [smul_eq_mul, measureReal_def]
  apply tsum_congr
  intro N0
  have hsabs := (hinner N0).summable_of_dirac
  have hs : Summable (fun N1 =>
      ((poissonMeasure rate1) ({N1} : Set ℕ)).toReal *
        ((N0 : ℝ) * (N1 : ℝ) *
          (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1)) := by
    apply Summable.of_norm
    simpa only [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg,
      poissonMeasure_singleton_eq_poissonPMF,
      ← poissonPMFReal_ofReal_eq_poissonPMF,
      poissonPMFReal] using hsabs
  rw [← hs.tsum_mul_left
    ((poissonMeasure rate0) ({N0} : Set ℕ)).toReal]
  apply tsum_congr
  intro N1
  ring

/-- Nonnegative count-kernel integrability lifts through the two finite
Poisson count fibres to the weighted squared numerator itself. -/
lemma integrable_poisson_centeredNumerator_second_weighted
    (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P)
    (rate0 rate1 : ℝ≥0) (w : ℕ → ℕ → ℝ)
    (hw : ∀ N0 N1, 0 ≤ w N0 N1)
    (hinner : ∀ N0, Integrable
      (fun N1 => conditionalNumeratorSecond P k t N0 N1 * w N0 N1)
      (poissonMeasure rate1))
    (houter : Integrable
      (fun N0 => ∫ N1, conditionalNumeratorSecond P k t N0 N1 * w N0 N1
        ∂poissonMeasure rate1) (poissonMeasure rate0)) :
    Integrable
      (fun p : FiniteSample ℝ × FiniteSample ℝ =>
        Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
          (centeredNumeratorKernel P k t) p.1 p.2 ^ 2 *
            w p.1.count p.2.count)
      ((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1)) := by
  letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
    P.outcome_isProbability false k
  letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
    P.outcome_isProbability true k
  let K := centeredNumeratorKernel P k t
  let f : FiniteSample ℝ × FiniteSample ℝ → ℝ := fun p =>
    Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum K p.1 p.2 ^ 2 *
      w p.1.count p.2.count
  let g : ℕ × ℕ → ℝ := fun q =>
    conditionalNumeratorSecond P k t q.1 q.2 * w q.1 q.2
  have hK : Measurable (Function.uncurry K) :=
    (measurable_snd.sub measurable_fst).sub measurable_const
  have hK2 : Integrable (fun p : ℝ × ℝ => K p.1 p.2 ^ 2)
      ((P.outcomeLaw false k).prod (P.outcomeLaw true k)) := by
    simpa [K] using centeredNumeratorKernel_sq_integrable P k t hp hvariance
  have hfmeas : Measurable f :=
    ((Causalean.Mathlib.Probability.Poisson.PairSecondMoment.measurable_pairSum K hK).pow_const 2).mul
      ((measurable_of_countable (Function.uncurry w)).comp
        ((measurable_finiteSample_count.comp measurable_fst).prodMk
          (measurable_finiteSample_count.comp measurable_snd)))
  have hfnonneg : ∀ p, 0 ≤ f p := fun p =>
    mul_nonneg (sq_nonneg _) (hw p.1.count p.2.count)
  have hgnonneg : ∀ q, 0 ≤ g q := fun q =>
    mul_nonneg (by
      dsimp only [conditionalNumeratorSecond]
      positivity) (hw q.1 q.2)
  have hgint : Integrable g ((poissonMeasure rate0).prod (poissonMeasure rate1)) := by
    apply (integrable_prod_iff (measurable_of_countable g).aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall hinner
    · simpa only [Real.norm_eq_abs, abs_of_nonneg (hgnonneg _)] using houter
  apply (lintegral_ofReal_ne_top_iff_integrable hfmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hfnonneg)).mp
  have hfixed (N0 N1 : ℕ) :
      (∫⁻ p : (Fin N0 → ℝ) × (Fin N1 → ℝ),
        ENNReal.ofReal
          ((∑ i : Fin N0, ∑ j : Fin N1, K (p.1 i) (p.2 j)) ^ 2 * w N0 N1)
        ∂((Measure.pi fun _ : Fin N0 => P.outcomeLaw false k).prod
          (Measure.pi fun _ : Fin N1 => P.outcomeLaw true k))) =
        ENNReal.ofReal (g (N0, N1)) := by
    have hsq :=
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.integrable_fixedCount_pairSum_sq
        (P.outcomeLaw false k) (P.outcomeLaw true k) K N0 N1 hK hK2
    have hint := hsq.mul_const (w N0 N1)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun p =>
        mul_nonneg (sq_nonneg _) (hw N0 N1))]
    rw [integral_mul_const]
    have hrewrite :
        (fun p : (Fin N0 → ℝ) × (Fin N1 → ℝ) =>
          (∑ i : Fin N0, ∑ j : Fin N1, K (p.1 i) (p.2 j)) ^ 2) =
        fun p => ((N0 : ℝ) * (∑ j : Fin N1, p.2 j) -
          (N1 : ℝ) * (∑ i : Fin N0, p.1 i) -
          t * (N0 : ℝ) * (N1 : ℝ)) ^ 2 := by
      funext p
      rw [fixedCount_centeredNumerator_eq_pairSum]
      rfl
    rw [hrewrite, fixedCount_centeredNumerator_second P k t hp hvariance N0 N1]
  change (∫⁻ p, (ENNReal.ofReal ∘ f) p
    ∂((finitePoissonSampleLaw (P.outcomeLaw false k) rate0).prod
      (finitePoissonSampleLaw (P.outcomeLaw true k) rate1))) ≠ ⊤
  rw [Causalean.Mathlib.Probability.Poisson.PairSecondMoment.lintegral_pair_count_mixture
    (P.outcomeLaw false k) (P.outcomeLaw true k) rate0 rate1 _
    (ENNReal.measurable_ofReal.comp hfmeas)]
  simp only [f, Function.comp_apply, FiniteSample.count, K,
    Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum]
  have hfixed' (N0 N1 : ℕ) :
      (∫⁻ p : (Fin N0 → ℝ) × (Fin N1 → ℝ),
        ENNReal.ofReal
          ((∑ i : Fin N0, ∑ j : Fin N1,
            centeredNumeratorKernel P k t (p.1 i) (p.2 j)) ^ 2 * w N0 N1)
        ∂((Measure.pi fun _ : Fin N0 => P.outcomeLaw false k).prod
          (Measure.pi fun _ : Fin N1 => P.outcomeLaw true k))) =
        ENNReal.ofReal (g (N0, N1)) := by
    simpa only [K] using hfixed N0 N1
  simp_rw [hfixed']
  have hcount := hgint.lintegral_lt_top
  rw [lintegral_prod (fun q => ENNReal.ofReal (g q))
    ((ENNReal.measurable_ofReal.comp (measurable_of_countable g)).aemeasurable),
    lintegral_countable'] at hcount
  simp_rw [lintegral_countable'] at hcount
  have heq :
      (∑' N0 : ℕ, ∑' N1 : ℕ,
        poissonMeasure rate0 {N0} * poissonMeasure rate1 {N1} *
          ENNReal.ofReal (g (N0, N1))) =
      ∑' N0 : ℕ, (∑' N1 : ℕ,
        ENNReal.ofReal (g (N0, N1)) * poissonMeasure rate1 {N1}) *
          poissonMeasure rate0 {N0} := by
    apply tsum_congr
    intro N0
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro N1
    ac_rfl
  rw [heq]
  exact hcount.ne

/-- The weighted Poisson second-moment identity, with sample-level
integrability discharged from the count-fibre hypotheses. -/
lemma poisson_centeredNumerator_second_weighted_of_count_integrable
    (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P)
    (rate0 rate1 : ℝ≥0) (w : ℕ → ℕ → ℝ)
    (hw : ∀ N0 N1, 0 ≤ w N0 N1)
    (hinner : ∀ N0, Integrable
      (fun N1 => conditionalNumeratorSecond P k t N0 N1 * w N0 N1)
      (poissonMeasure rate1))
    (houter : Integrable
      (fun N0 => ∫ N1, conditionalNumeratorSecond P k t N0 N1 * w N0 N1
        ∂poissonMeasure rate1) (poissonMeasure rate0)) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 ^ 2 *
          w p.1.count p.2.count
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1))) =
      ∫ N0, ∫ N1, conditionalNumeratorSecond P k t N0 N1 * w N0 N1
        ∂poissonMeasure rate1 ∂poissonMeasure rate0 := by
  exact poisson_centeredNumerator_second_weighted P k t hp hvariance rate0 rate1 w
    (integrable_poisson_centeredNumerator_second_weighted P k t hp hvariance
      rate0 rate1 w hw hinner houter) hinner houter

/-- A weighted numerator is integrable whenever its square is controlled on
the two Poisson count fibres. -/
lemma integrable_poisson_centeredNumerator_first_weighted
    (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P)
    (rate0 rate1 : ℝ≥0) (w : ℕ → ℕ → ℝ)
    (hinner : ∀ N0, Integrable
      (fun N1 => conditionalNumeratorSecond P k t N0 N1 * w N0 N1 ^ 2)
      (poissonMeasure rate1))
    (houter : Integrable
      (fun N0 => ∫ N1, conditionalNumeratorSecond P k t N0 N1 * w N0 N1 ^ 2
        ∂poissonMeasure rate1) (poissonMeasure rate0)) :
    Integrable
      (fun p : FiniteSample ℝ × FiniteSample ℝ =>
        Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
          (centeredNumeratorKernel P k t) p.1 p.2 *
            w p.1.count p.2.count)
      ((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1)) := by
  let mu :=
    ((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
        (P.outcome_isProbability false k) rate0).prod
      (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
        (P.outcome_isProbability true k) rate1))
  let F : FiniteSample ℝ × FiniteSample ℝ → ℝ := fun p =>
    Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
      (centeredNumeratorKernel P k t) p.1 p.2 * w p.1.count p.2.count
  have hFmeas : Measurable F :=
    (Causalean.Mathlib.Probability.Poisson.PairSecondMoment.measurable_pairSum
      (centeredNumeratorKernel P k t)
      ((measurable_snd.sub measurable_fst).sub measurable_const)).mul
      ((measurable_of_countable (Function.uncurry w)).comp
        ((measurable_finiteSample_count.comp measurable_fst).prodMk
          (measurable_finiteSample_count.comp measurable_snd)))
  have hsq : Integrable (fun p => F p ^ 2) mu := by
    have h := integrable_poisson_centeredNumerator_second_weighted
      P k t hp hvariance rate0 rate1 (fun N0 N1 => w N0 N1 ^ 2)
      (fun _ _ => sq_nonneg _) hinner houter
    simpa only [F, mu, mul_pow] using h
  have hone : Integrable (fun _ : FiniteSample ℝ × FiniteSample ℝ => (1 : ℝ)) mu :=
    integrable_const _
  apply (hsq.add hone).mono'
  · exact hFmeas.aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs]
    change |F p| ≤ F p ^ 2 + 1
    have habs_sq : |F p| ^ 2 = F p ^ 2 := by rw [sq_abs]
    nlinarith [sq_nonneg (|F p| - 1)]

/-- The weighted Poisson first-moment identity with its sample-level
integrability discharged by the squared count kernel. -/
lemma poisson_centeredNumerator_first_weighted_of_count_integrable
    (P : Law n) (k : Fin n) (t : ℝ)
    (hp : 0 < P.cellMass k) (hvariance : VarianceEnvelope M P)
    (rate0 rate1 : ℝ≥0) (w : ℕ → ℕ → ℝ)
    (hsqInner : ∀ N0, Integrable
      (fun N1 => conditionalNumeratorSecond P k t N0 N1 * w N0 N1 ^ 2)
      (poissonMeasure rate1))
    (hsqOuter : Integrable
      (fun N0 => ∫ N1, conditionalNumeratorSecond P k t N0 N1 * w N0 N1 ^ 2
        ∂poissonMeasure rate1) (poissonMeasure rate0))
    (hinner : ∀ N0 : ℕ, Integrable
      (fun N1 : ℕ => (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1)
      (poissonMeasure rate1))
    (houter : Integrable
      (fun N0 : ℕ => ∫ N1 : ℕ, (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1
        ∂poissonMeasure rate1) (poissonMeasure rate0)) :
    (∫ p : FiniteSample ℝ × FiniteSample ℝ,
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k t) p.1 p.2 * w p.1.count p.2.count
      ∂((@finitePoissonSampleLaw ℝ _ (P.outcomeLaw false k)
          (P.outcome_isProbability false k) rate0).prod
        (@finitePoissonSampleLaw ℝ _ (P.outcomeLaw true k)
          (P.outcome_isProbability true k) rate1))) =
      ∫ N0, ∫ N1, (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1
        ∂poissonMeasure rate1 ∂poissonMeasure rate0 := by
  exact poisson_centeredNumerator_first_weighted P k t hp hvariance rate0 rate1 w
    (integrable_poisson_centeredNumerator_first_weighted P k t hp hvariance
      rate0 rate1 w hsqInner hsqOuter) hinner houter

lemma conditionalNumeratorMean_sq_le_second (P : Law n) (k : Fin n) (t : ℝ)
    (N0 N1 : ℕ) :
    ((N0 : ℝ) * (N1 : ℝ) *
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t)) ^ 2 ≤
        conditionalNumeratorSecond P k t N0 N1 := by
  have hV0 : 0 ≤ ∫ y, (y - P.outcomeMean false k) ^ 2
      ∂P.outcomeLaw false k := integral_nonneg fun _ => sq_nonneg _
  have hV1 : 0 ≤ ∫ y, (y - P.outcomeMean true k) ^ 2
      ∂P.outcomeLaw true k := integral_nonneg fun _ => sq_nonneg _
  dsimp only [conditionalNumeratorSecond]
  calc
    _ = (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2 := by ring
    _ ≤ _ := by
      have h0 : 0 ≤ (N0 : ℝ) ^ 2 * (N1 : ℝ) *
          (∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k) := by
        positivity
      have h1 : 0 ≤ (N1 : ℝ) ^ 2 * (N0 : ℝ) *
          (∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k) := by
        positivity
      linarith

/-- The deterministic conditional mean count-kernel is integrable whenever
the corresponding conditional second-moment kernel is integrable. -/
lemma countMean_integrable_of_second
    (P : Law n) (k : Fin n) (t : ℝ) (rate0 rate1 : ℝ≥0)
    (w : ℕ → ℕ → ℝ)
    (hsqInner : ∀ N0, Integrable
      (fun N1 => conditionalNumeratorSecond P k t N0 N1 * w N0 N1 ^ 2)
      (poissonMeasure rate1))
    (hsqOuter : Integrable
      (fun N0 => ∫ N1, conditionalNumeratorSecond P k t N0 N1 * w N0 N1 ^ 2
        ∂poissonMeasure rate1) (poissonMeasure rate0)) :
    (∀ N0 : ℕ, Integrable
      (fun N1 : ℕ => (N0 : ℝ) * (N1 : ℝ) *
        (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1)
      (poissonMeasure rate1)) ∧
    Integrable (fun N0 : ℕ => ∫ N1 : ℕ, (N0 : ℝ) * (N1 : ℝ) *
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1
      ∂poissonMeasure rate1) (poissonMeasure rate0) := by
  let F : ℕ → ℕ → ℝ := fun N0 N1 => (N0 : ℝ) * (N1 : ℝ) *
    (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) * w N0 N1
  let G : ℕ → ℕ → ℝ := fun N0 N1 =>
    conditionalNumeratorSecond P k t N0 N1 * w N0 N1 ^ 2
  have hGnonneg (N0 N1 : ℕ) : 0 ≤ G N0 N1 := by
    dsimp only [G]
    exact mul_nonneg (by
      dsimp only [conditionalNumeratorSecond]
      positivity) (sq_nonneg _)
  have hFsq_le (N0 N1 : ℕ) : F N0 N1 ^ 2 ≤ G N0 N1 := by
    dsimp only [F, G]
    calc
      _ = ((N0 : ℝ) * (N1 : ℝ) *
          (DiscreteAteHeterogeneityFrontier.cellEffect P k - t)) ^ 2 *
            w N0 N1 ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (conditionalNumeratorMean_sq_le_second P k t N0 N1) (sq_nonneg _)
  have hFin (N0 : ℕ) : Integrable (F N0) (poissonMeasure rate1) := by
    have hFsq : Integrable (fun N1 => F N0 N1 ^ 2) (poissonMeasure rate1) := by
      apply (hsqInner N0).mono' (measurable_of_countable _).aestronglyMeasurable
      filter_upwards with N1
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hFsq_le N0 N1
    apply (hFsq.add (integrable_const 1)).mono'
      (measurable_of_countable _).aestronglyMeasurable
    filter_upwards with N1
    rw [Real.norm_eq_abs]
    change |F N0 N1| ≤ F N0 N1 ^ 2 + 1
    rw [← sq_abs (F N0 N1)]
    nlinarith [sq_nonneg (|F N0 N1| - 1)]
  constructor
  · intro N0
    simpa only [F] using hFin N0
  · let A : ℕ → ℝ := fun N0 => ∫ N1, F N0 N1 ∂poissonMeasure rate1
    let B : ℕ → ℝ := fun N0 => ∫ N1, G N0 N1 ∂poissonMeasure rate1
    have hB : Integrable B (poissonMeasure rate0) := by
      simpa only [B, G] using hsqOuter
    apply (hB.add (integrable_const 1)).mono'
      (measurable_of_countable _).aestronglyMeasurable
    filter_upwards with N0
    change ‖A N0‖ ≤ B N0 + 1
    calc
      _ ≤ ∫ N1, ‖F N0 N1‖ ∂poissonMeasure rate1 :=
        norm_integral_le_integral_norm (F N0)
      _ ≤ ∫ N1, G N0 N1 + 1 ∂poissonMeasure rate1 := by
        apply integral_mono (hFin N0).norm ((hsqInner N0).add (integrable_const 1))
        intro N1
        change |F N0 N1| ≤ G N0 N1 + 1
        have habs : |F N0 N1| ^ 2 = F N0 N1 ^ 2 := sq_abs _
        nlinarith [sq_nonneg (|F N0 N1| - 1), hFsq_le N0 N1]
      _ = _ := by
        rw [integral_add (hsqInner N0) (integrable_const 1)]
        simp only [integral_const, smul_eq_mul, measureReal_def,
          IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_mul]
        rfl

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
