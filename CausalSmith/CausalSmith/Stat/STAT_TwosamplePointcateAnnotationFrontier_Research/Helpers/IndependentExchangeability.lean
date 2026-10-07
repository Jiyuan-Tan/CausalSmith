module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.MarkedHandle

/-! Conditional exchangeability for the explicit independent Bernoulli extension. -/

public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- For [Borel success-probability functions p and q](hyp:hp,hq), [the two potential-outcome Bernoulli kernels are Borel jointly](goal). -/
@[fun_prop] lemma measurable_bernPair {Ω : Type*} [MeasurableSpace Ω]
    (p q : Ω → ℝ) (hp : Measurable p) (hq : Measurable q) :
    Measurable (fun x => (bern (p x)).prod (bern (q x))) := by
  simp only [bern, Measure.prod_add, Measure.add_prod, Measure.prod_smul_right,
    Measure.prod_smul_left, Measure.dirac_prod_dirac]
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  fun_prop

/-- The independent construction satisfies conditional exchangeability with its explicit
product kernel for the two potential outcomes.  Given [the specified input d](hyp:d), [the specified input e](hyp:e), [the specified input p](hyp:p), [the specified input q](hyp:q), [the specified input he](hyp:he), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the independent primitive exchangeability conclusion](goal) holds. -/
lemma independentPrimitive_exchangeability {d : ℕ} (e p q : Cov d → ℝ)
    (he : Measurable e) (hp : Measurable p) (hq : Measurable q) :
    ConditionalExchangeability (independentPrimitive e p q he hp hq) := by
  letI := uniformLaw_probability d
  let E := fun x => probabilityClip (e x)
  let P := fun x => probabilityClip (p x)
  let Q := fun x => probabilityClip (q x)
  have hE : Measurable E := by fun_prop
  have hP : Measurable P := by fun_prop
  have hQ : Measurable Q := by fun_prop
  let Γ : Kernel (Cov d) (Bool × Bool) := ⟨fun x => (bern (P x)).prod (bern (Q x)),
    measurable_bernPair P Q hP hQ⟩
  have hΓ : IsMarkovKernel Γ := by
    constructor
    intro x
    letI := bern_probability (P x) (probabilityClip_mem _)
    letI := bern_probability (Q x) (probabilityClip_mem _)
    change IsProbabilityMeasure ((bern (P x)).prod (bern (Q x)))
    infer_instance
  letI := hΓ
  let K := bernKernel (fun w : Cov d × (Bool × Bool) => E w.1) (hE.comp measurable_fst)
  have hK : IsMarkovKernel K := ⟨fun w => bern_probability _ (probabilityClip_mem _)⟩
  letI := hK
  refine ⟨Γ, hΓ, ?_⟩
  change (independentFullLaw e p q).map (fun w => ((w.1, (w.2.2.1, w.2.2.2)), w.2.1)) =
    ((independentFullLaw e p q).map Prod.fst ⊗ₘ Γ) ⊗ₘ K
  rw [independentFullLaw_covariates d e p q he hp hq]
  unfold independentFullLaw
  rw [independent_map_bind _ _ _ (measurable_independentRecordKernel e p q he hp hq)
    (by fun_prop)]
  have hm : Measurable (fun x : Cov d =>
      (((Measure.dirac x).prod ((bern (probabilityClip (e x))).prod
        ((bern (probabilityClip (p x))).prod (bern (probabilityClip (q x)))))).map
        (fun w : FullRecord d => ((w.1, (w.2.2.1, w.2.2.2)), w.2.1)))) :=
    (Measure.measurable_map _ (by fun_prop)).comp
      (measurable_independentRecordKernel e p q he hp hq)
  ext s hs
  rw [Measure.bind_apply hs hm.aemeasurable, Measure.compProd_apply hs]
  rw [Measure.lintegral_compProd (K.measurable_kernel_prodMk_left hs)]
  apply lintegral_congr
  intro x
  change (((Measure.dirac x).prod ((bern (E x)).prod ((bern (P x)).prod (bern (Q x))))).map
    (fun w => ((w.1, (w.2.2.1, w.2.2.2)), w.2.1))) s =
    ∫⁻ y, bern (E x) {a | ((x,y),a) ∈ s} ∂(bern (P x)).prod (bern (Q x))
  rw [Measure.map_apply (show Measurable (fun w : FullRecord d =>
    ((w.1, (w.2.2.1, w.2.2.2)), w.2.1)) from by fun_prop) hs]
  simp only [bern, Measure.prod_add, Measure.add_prod, Measure.prod_smul_right,
    Measure.prod_smul_left, Measure.dirac_prod_dirac, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, lintegral_add_measure,
    lintegral_smul_measure, lintegral_dirac, Measure.dirac_apply]
  rfl

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
