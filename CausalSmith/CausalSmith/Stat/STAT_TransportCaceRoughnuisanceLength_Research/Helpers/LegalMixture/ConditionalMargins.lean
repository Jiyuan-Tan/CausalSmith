module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.TargetLaws
public import Causalean.Mathlib.Probability.Kernel.FiniteAtomic

/-! # Conditional integration of the primitive finite law

The normalized primitive kernel disintegrates along its covariate coordinate.
-/

public section

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Every real function is integrable against the finite primitive kernel.  Under [the displayed assumptions and inputs](hyp:s,x,mass,f), [the stated conclusion holds](goal). -/
-- @node: primitiveKernel_integrable
lemma primitiveKernel_integrable (s : Bool) (x : ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ) (f : FullData → ℝ) :
    Integrable f (primitiveKernel s x mass) := by
  classical
  unfold primitiveKernel
  apply integrable_finsetSum_measure.mpr
  intro d0 _
  apply integrable_finsetSum_measure.mpr
  intro d1 _
  apply integrable_finsetSum_measure.mpr
  intro y0 _
  apply integrable_finsetSum_measure.mpr
  intro y1 _
  exact (integrable_dirac (by simp)).smul_measure (by simp)

/-- The primitive kernel integrates a function by the displayed sixteen-cell sum.  Under [the displayed assumptions and inputs](hyp:s,x,mass,hm0,f), [the stated conclusion holds](goal). -/
-- @node: primitiveKernel_integral
lemma primitiveKernel_integral (s : Bool) (x : ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm0 : ∀ d0 d1 y0 y1, 0 ≤ mass x d0 d1 y0 y1)
    (f : FullData → ℝ) :
    (∫ o, f o ∂primitiveKernel s x mass) =
      ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        mass x d0 d1 y0 y1 * f (s, x, d0, d1, boolReal y0, boolReal y1) := by
  classical
  have hi := primitiveKernel_integrable s x mass f
  unfold primitiveKernel at hi ⊢
  rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hi)]
  apply Finset.sum_congr rfl
  intro d0 hd0
  have hi1 := integrable_finsetSum_measure.mp hi d0 hd0
  rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hi1)]
  apply Finset.sum_congr rfl
  intro d1 hd1
  have hi2 := integrable_finsetSum_measure.mp hi1 d1 hd1
  rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hi2)]
  apply Finset.sum_congr rfl
  intro y0 hy0
  have hi3 := integrable_finsetSum_measure.mp hi2 y0 hy0
  rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hi3)]
  apply Finset.sum_congr rfl
  intro y1 hy1
  simp [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hm0 _ _ _ _)]

/-- A bounded observable on the primitive atoms disintegrates over every covariate set.  Under [the displayed assumptions and inputs](hyp:s,density,mass,hm,hm0,hsum,f,hf,bound,hbound,B,hB), [the stated conclusion holds](goal). -/
-- @node: primitivePopulation_setIntegral
lemma primitivePopulation_setIntegral (s : Bool) (density : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    [IsFiniteMeasure ((volume.restrict covariateSpace).withDensity
      (fun x => ENNReal.ofReal (density x)))]
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1)
    (hm0 : ∀ x d0 d1 y0 y1, 0 ≤ mass x d0 d1 y0 y1)
    (hsum : ∀ x, ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1)
    (f : FullData → ℝ) (hf : Measurable f) (bound : ℝ)
    (hbound : ∀ x d0 d1 y0 y1,
      ‖f (s, x, d0, d1, boolReal y0, boolReal y1)‖ ≤ bound)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫ o in {o | covariate o ∈ B}, f o ∂primitivePopulation s density mass) =
      ∫ x in B, (∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        mass x d0 d1 y0 y1 * f (s, x, d0, d1, boolReal y0, boolReal y1))
        ∂(volume.restrict covariateSpace).withDensity
          (fun x => ENNReal.ofReal (density x)) := by
  classical
  let μ := (volume.restrict covariateSpace).withDensity
    (fun x => ENNReal.ofReal (density x))
  let κ : Kernel ℝ FullData :=
    ⟨fun x => primitiveKernel s x mass, primitiveKernel_measurable_of s mass hm⟩
  have : IsMarkovKernel κ := ⟨fun x => isProbabilityMeasure_iff.mpr
    (primitiveKernel_univ s x mass (hm0 x) (hsum x))⟩
  let atom (x : ℝ) (i : Bool × Bool × Bool × Bool) : FullData :=
    (s, x, i.1, i.2.1, boolReal i.2.2.1, boolReal i.2.2.2)
  let weight (x : ℝ) (i : Bool × Bool × Bool × Bool) : ℝ :=
    mass x i.1 i.2.1 i.2.2.1 i.2.2.2
  have hw : ∀ x i, 0 ≤ weight x i := fun x i => hm0 x _ _ _ _
  have hn : ∀ x, ∑ i, weight x i = 1 := by
    intro x
    simpa only [weight, Fintype.sum_prod_type] using hsum x
  have hk : ∀ x, κ x = ∑ i, ENNReal.ofReal (weight x i) •
      Measure.dirac (atom x i) := by
    intro x
    change primitiveKernel s x mass = _
    simp only [primitiveKernel, weight, atom, Fintype.sum_prod_type]
  have hint : Integrable f (κ ∘ₘ μ) := by
    apply (Measure.integrable_comp_iff hf.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun x => primitiveKernel_integrable s x mass f), ?_⟩
    have heq (x : ℝ) : (∫ o, ‖f o‖ ∂κ x) = ∑ i, weight x i * ‖f (atom x i)‖ := by
      exact Causalean.Mathlib.Probability.Kernel.FiniteAtomic.integral_finiteAtomicKernel
        κ atom weight hw hk (fun o => ‖f o‖) x
        (primitiveKernel_integrable s x mass (fun o => ‖f o‖))
    simp_rw [heq]
    have hmeas : Measurable (fun x => ∑ i, weight x i * ‖f (atom x i)‖) := by
      apply Finset.measurable_fun_sum
      intro i _
      exact (hm _ _ _ _).mul ((hf.comp (by dsimp [atom]; fun_prop)).norm)
    apply (integrable_const bound).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (hw x i) (norm_nonneg _)))]
    calc
      ∑ i, weight x i * ‖f (atom x i)‖ ≤ ∑ i, weight x i * bound := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hbound x _ _ _ _) (hw x i)
      _ = bound := by rw [← Finset.sum_mul, hn]; simp
  have h := Causalean.Mathlib.Probability.Kernel.FiniteAtomic.setIntegral_finiteAtomicKernel
    μ κ atom weight hw hn hk covariate (by unfold covariate; fun_prop)
    (by intro x i; rfl) B hB f hint
  change (∫ o in {o | covariate o ∈ B}, f o ∂primitivePopulation s density mass) = _ at h
  simpa only [μ, weight, atom, Fintype.sum_prod_type] using h

/-- Normalized primitive masses preserve the total base mass.  Under [the displayed assumptions and inputs](hyp:s,density,mass,hm,hm0,hsum), [the stated conclusion holds](goal). -/
-- @node: primitivePopulation_univ
lemma primitivePopulation_univ (s : Bool) (density : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1)
    (hm0 : ∀ x d0 d1 y0 y1, 0 ≤ mass x d0 d1 y0 y1)
    (hsum : ∀ x, ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1) :
    primitivePopulation s density mass univ =
      ((volume.restrict covariateSpace).withDensity
        (fun x => ENNReal.ofReal (density x))) univ := by
  unfold primitivePopulation
  rw [Measure.bind_apply MeasurableSet.univ
    (primitiveKernel_measurable_of s mass hm).aemeasurable]
  simp_rw [primitiveKernel_univ s _ mass (hm0 _) (hsum _)]
  simp

/-- Conditioning a half-mixture on a population event selects its supported component.  Under [the displayed assumptions and inputs](hyp:source,target,S,hS,hs,ht,hu), [the stated conclusion holds](goal). -/
-- @node: cond_half_supported_mixture_event
lemma cond_half_supported_mixture_event (source target : Measure FullData)
    (S : Set FullData) (hS : MeasurableSet S)
    (hs : source S = 0) (ht : target S = 1) (hu : target univ = 1) :
    ProbabilityTheory.cond
      ((1 / 2 : ℝ≥0∞) • source + (1 / 2 : ℝ≥0∞) • target) S = target := by
  have hmass : ((1 / 2 : ℝ≥0∞) • source + (1 / 2 : ℝ≥0∞) • target) S = 1 / 2 := by
    simp [Measure.add_apply, Measure.smul_apply, hs, ht]
  have hrs : source.restrict S = 0 := Measure.restrict_eq_zero.mpr hs
  have hrt : target.restrict S = target := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    change target (Sᶜ) = 0
    rw [measure_compl hS (by rw [ht]; simp), hu, ht]
    simp
  unfold ProbabilityTheory.cond
  rw [hmass, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul, hrs, hrt]
  simp only [smul_zero, zero_add]
  rw [← mul_smul, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  exact one_smul _ _

/-- The legal law's conditional population is exactly its primitive mixture component. Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn,hb,hAdm,hn,s,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_populationLaw_eq_primitive
lemma legalIVComponent_populationLaw_eq_primitive (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1)
    (hn : 0 < n) (s : Bool) :
    populationLaw (legalIVComponent a n cStar τ sgn) s =
      primitivePopulation s (fun x => if s then 1 else 1 + tiledPerturbation cStar n sgn x)
        (lowerMass a n cStar τ sgn) := by
  let mass := lowerMass a n cStar τ sgn
  have hm := lowerMass_measurable a n cStar τ sgn
  have hm0 := lowerMass_nonneg a n cStar τ sgn hb hAdm hτ
  have hsum (x : ℝ) : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1 := by
    apply primitiveMass_sum _ _ _ (ne_of_gt hb.1)
    have h := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
    have h' := le_trans h hAdm.2.1
    nlinarith [sq_abs (tiledPerturbation cStar n sgn x),
      abs_nonneg (tiledPerturbation cStar n sgn x)]
  have hsource : primitivePopulation true (fun _ => 1) mass univ = 1 := by
    rw [primitivePopulation_univ true _ mass hm hm0 hsum]
    simp [covariateSpace]
  have htarget : primitivePopulation false
      (fun x => 1 + tiledPerturbation cStar n sgn x) mass univ = 1 := by
    rw [primitivePopulation_univ false _ mass hm hm0 hsum]
    apply targetDensity_univ cStar n sgn hn
    intro x
    have h := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
    have h' := le_trans h hAdm.2.1
    linarith [neg_abs_le (tiledPerturbation cStar n sgn x)]
  unfold populationLaw legalIVComponent lawFromMass
  dsimp
  cases s
  · apply cond_half_supported_mixture_event
    · unfold population; measurability
    · simpa using primitivePopulation_population_event true false (fun _ => 1) mass hm
    · simpa using (primitivePopulation_population_event false false
        (fun x => 1 + tiledPerturbation cStar n sgn x) mass hm).trans (by simpa using htarget)
    · exact htarget
  · rw [add_comm]
    apply cond_half_supported_mixture_event
    · unfold population; measurability
    · simpa using primitivePopulation_population_event false true
        (fun x => 1 + tiledPerturbation cStar n sgn x) mass hm
    · simpa using (primitivePopulation_population_event true true (fun _ => 1) mass hm).trans
        (by simpa using hsource)
    · exact hsource

/-- A measurable finite-cell mean is a conditional mean under either legal population. Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn,hb,hAdm,hn,s,f,hf,bound,hbound,q,hq,hmean,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_conditionalMean_of_pointwise
lemma legalIVComponent_conditionalMean_of_pointwise (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1)
    (hn : 0 < n) (s : Bool) (f : FullData → ℝ) (hf : Measurable f)
    (bound : ℝ) (hbound : ∀ x d0 d1 y0 y1,
      ‖f (s, x, d0, d1, boolReal y0, boolReal y1)‖ ≤ bound)
    (q : ℝ → ℝ) (hq : Measurable q)
    (hmean : ∀ x, lowerPointwiseMean a n cStar τ sgn s f x = q x) :
    ConditionalMean (legalIVComponent a n cStar τ sgn) s f q := by
  let density : ℝ → ℝ := fun x => if s then 1 else 1 + tiledPerturbation cStar n sgn x
  let mass := lowerMass a n cStar τ sgn
  let μ := (volume.restrict covariateSpace).withDensity
    (fun x => ENNReal.ofReal (density x))
  have hm := lowerMass_measurable a n cStar τ sgn
  have hm0 := lowerMass_nonneg a n cStar τ sgn hb hAdm hτ
  have hsum (x : ℝ) : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1 := by
    apply primitiveMass_sum _ _ _ (ne_of_gt hb.1)
    have h := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
    have h' := le_trans h hAdm.2.1
    nlinarith [sq_abs (tiledPerturbation cStar n sgn x),
      abs_nonneg (tiledPerturbation cStar n sgn x)]
  have hdensity : Measurable density := by
    cases s
    · exact measurable_const.add (tiledPerturbation_measurable cStar n sgn)
    · exact measurable_const
  have : IsProbabilityMeasure μ := by
    apply isProbabilityMeasure_iff.mpr
    cases s
    · apply targetDensity_univ cStar n sgn hn
      intro x
      have h := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
      have h' := le_trans h hAdm.2.1
      linarith [neg_abs_le (tiledPerturbation cStar n sgn x)]
    · simp [μ, density, covariateSpace]
  refine ⟨hq, ?_⟩
  intro B hB
  rw [legalIVComponent_populationLaw_eq_primitive a n cStar τ sgn hb hAdm hτ hn s]
  rw [map_covariate_primitivePopulation s density mass hdensity hm hm0 hsum]
  rw [primitivePopulation_setIntegral s density mass hm hm0 hsum f hf bound hbound B hB]
  apply setIntegral_congr_fun hB
  intro x _
  exact hmean x

/-- The primitive complier margins give both transport conditional means. Under [the displayed assumptions and inputs](hyp:a,n,cStar,sgn,hb,hAdm,hn,s,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_conditional_complier_margins
lemma legalIVComponent_conditional_complier_margins (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1)
    (hn : 0 < n) (s : Bool) :
    ConditionalMean (legalIVComponent a n cStar τ sgn) s complier
      (fun _ => actualStrength a n) ∧
    ConditionalMean (legalIVComponent a n cStar τ sgn) s
      (fun o => (outcome1 o - outcome0 o) * complier o)
      (fun x => -(tiledPerturbation cStar n sgn x * coupledPerturbation cStar τ n sgn x) /
        (1 / 4 - tiledPerturbation cStar n sgn x ^ 2)) := by
  classical
  have hm : Measurable complier := by
    have h0 : Measurable receipt0 := by unfold receipt0; fun_prop
    have h1 : Measurable receipt1 := by unfold receipt1; fun_prop
    have hset : MeasurableSet {o : FullData | receipt1 o = true ∧ receipt0 o = false} :=
      ((measurableSet_singleton true).preimage h1).inter
        ((measurableSet_singleton false).preimage h0)
    convert (measurable_const : Measurable (fun _ : FullData => (1 : ℝ))).ite hset
      (measurable_const : Measurable (fun _ : FullData => (0 : ℝ))) using 1
    · funext o
      simp [complier]
    · infer_instance
  have hY : Measurable (fun o : FullData => (outcome1 o - outcome0 o) * complier o) := by
    unfold outcome1 outcome0
    fun_prop
  have hpoint (x : ℝ) := lowerPointwiseMean_complier_margins a n cStar τ sgn s x
    (ne_of_gt hb.1)
  constructor
  · apply legalIVComponent_conditionalMean_of_pointwise a n cStar τ sgn hb hAdm hτ hn s
      complier hm 1
    · intro x d0 d1 y0 y1
      cases d0 <;> cases d1 <;> norm_num [complier, receipt1, receipt0]
    · exact measurable_const
    · exact fun x => (hpoint x).1
  · apply legalIVComponent_conditionalMean_of_pointwise a n cStar τ sgn hb hAdm hτ hn s
      _ hY 1
    · intro x d0 d1 y0 y1
      cases d0 <;> cases d1 <;> cases y0 <;> cases y1 <;>
        norm_num [complier, receipt1, receipt0, outcome1, outcome0, boolReal]
    · have hu := tiledPerturbation_measurable cStar n sgn
      exact (hu.mul (measurable_const.mul hu)).neg.div (measurable_const.sub (hu.pow_const 2))
    · exact fun x => (hpoint x).2

/-- The center's target effect vanishes by its primitive complier outcome margins.  Under [the displayed assumptions and inputs](hyp:a,n,hb), [the stated conclusion holds](goal). -/
-- @node: mixtureCenter_targetCACE_zero
lemma mixtureCenter_targetCACE_zero (a : ℝ) (n : ℕ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) :
    targetCACE (mixtureCenter a n) = 0 := by
  classical
  let mass : ℝ → Bool → Bool → Bool → Bool → ℝ :=
    fun _ => primitiveMass (actualStrength a n) 0 0
  have hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1 :=
    fun _ _ _ _ => measurable_const
  have hm0 : ∀ x d0 d1 y0 y1, 0 ≤ mass x d0 d1 y0 y1 := by
    intro x d0 d1 y0 y1
    exact primitiveMass_nonneg_of_bounds (actualStrength a n) 0 0 hb
      (by norm_num) (by norm_num) (by nlinarith [hb.1]) d0 d1 y0 y1
  have hsum (x : ℝ) : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1 :=
    primitiveMass_sum (actualStrength a n) 0 0 (ne_of_gt hb.1) (by norm_num)
  have hu (s : Bool) : primitivePopulation s (fun _ => 1) mass univ = 1 := by
    rw [primitivePopulation_univ s _ mass hm hm0 hsum]
    simp [covariateSpace]
  have hpop : populationLaw (mixtureCenter a n) false =
      primitivePopulation false (fun _ => 1) mass := by
    unfold populationLaw mixtureCenter lawFromMass
    dsimp
    apply cond_half_supported_mixture_event
    · unfold population; measurability
    · simpa using primitivePopulation_population_event true false (fun _ => 1) mass hm
    · simpa using (primitivePopulation_population_event false false (fun _ => 1) mass hm).trans
        (by simpa using hu false)
    · exact hu false
  have hmC : Measurable complier := by
    have h0 : Measurable receipt0 := by unfold receipt0; fun_prop
    have h1 : Measurable receipt1 := by unfold receipt1; fun_prop
    have hset : MeasurableSet {o : FullData | receipt1 o = true ∧ receipt0 o = false} :=
      ((measurableSet_singleton true).preimage h1).inter
        ((measurableSet_singleton false).preimage h0)
    convert (measurable_const : Measurable (fun _ : FullData => (1 : ℝ))).ite hset
      (measurable_const : Measurable (fun _ : FullData => (0 : ℝ))) using 1
    · funext o
      simp [complier]
    · infer_instance
  have hY : Measurable (fun o : FullData => (outcome1 o - outcome0 o) * complier o) := by
    unfold outcome1 outcome0
    fun_prop
  have hbound (x : ℝ) (d0 d1 y0 y1 : Bool) :
      ‖(outcome1 (false, x, d0, d1, boolReal y0, boolReal y1) -
        outcome0 (false, x, d0, d1, boolReal y0, boolReal y1)) *
        complier (false, x, d0, d1, boolReal y0, boolReal y1)‖ ≤ (1 : ℝ) := by
    cases d0 <;> cases d1 <;> cases y0 <;> cases y1 <;>
      norm_num [complier, receipt1, receipt0, outcome1, outcome0, boolReal]
  have : IsFiniteMeasure ((volume.restrict covariateSpace).withDensity
      (fun _ => ENNReal.ofReal (1 : ℝ))) := by
    simp only [ENNReal.ofReal_one]
    change IsFiniteMeasure ((volume.restrict covariateSpace).withDensity 1)
    rw [withDensity_one]
    change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
    infer_instance
  have h := primitivePopulation_setIntegral false (fun _ => 1) mass hm hm0 hsum
    (fun o => (outcome1 o - outcome0 o) * complier o) hY 1 hbound univ MeasurableSet.univ
  simp only [Set.mem_univ, Set.ofPred_true, Measure.restrict_univ] at h
  have hmean (x : ℝ) := primitiveMass_complier_outcome_sum (actualStrength a n) 0 0
    (ne_of_gt hb.1) false x
  change (∫ o, (outcome1 o - outcome0 o) * complier o
    ∂primitivePopulation false (fun _ => 1) mass) = _ at h
  simp_rw [show ∀ x, (∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    mass x d0 d1 y0 y1 * ((outcome1 (false, x, d0, d1, boolReal y0, boolReal y1) -
      outcome0 (false, x, d0, d1, boolReal y0, boolReal y1)) *
      complier (false, x, d0, d1, boolReal y0, boolReal y1))) = 0 by
        intro x; simpa [mass] using hmean x] at h
  simp only [integral_zero] at h
  unfold targetCACE
  rw [hpop, h, zero_div]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
