module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.MixtureDensity
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationMoments

/-! Identification of marked targets from the original-record experiment laws. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The conditional observed Bernoulli law is a measurable kernel.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [conditional observed kernel](goal) is the corresponding construction. -/
def conditionalObservedKernel {d : ℕ} (P : PrimitiveLaw d) : Kernel (Cov d) (Bool × Bool) :=
  ⟨conditionalObserved P, by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    rw [show (fun x => conditionalObserved P x A) =
      (fun x => ∑ s : Bool × Bool, if s ∈ A then conditionalObserved P x {s} else 0) by
        funext x
        rw [← Measure.sum_smul_dirac (conditionalObserved P x)]
        simp [Measure.sum_apply, hA, tsum_fintype, Measure.dirac_apply' _ hA,
          Set.indicator, mul_ite]]
    apply Finset.measurable_fun_sum
    intro s _
    by_cases hs : s ∈ A
    · simp only [if_pos hs, conditionalObserved_singleton]
      have he := (Measure.measurable_coe (measurableSet_singleton s.1)).comp
        (measurable_bern P.e P.measurable_e)
      have hm : Measurable (fun x => if s.1 then P.mu1 x else P.mu0 x) := by
        cases s.1 <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
          first | exact P.measurable_mu0 | exact P.measurable_mu1
      exact he.mul ((Measure.measurable_coe (measurableSet_singleton s.2)).comp
        (measurable_bern _ hm))
    · simp only [if_neg hs]; exact measurable_const⟩

/-- Probability-valued margins make the observed conditional kernel Markov.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input he](hyp:he), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the conditional observed kernel markov conclusion](goal) holds. -/
lemma conditionalObservedKernel_markov {d : ℕ} (P : PrimitiveLaw d)
    (he : ∀ x, P.e x ∈ Icc 0 1) (hp : ∀ x, P.mu0 x ∈ Icc 0 1)
    (hq : ∀ x, P.mu1 x ∈ Icc 0 1) : IsMarkovKernel (conditionalObservedKernel P) := by
  constructor
  intro x
  change IsProbabilityMeasure (conditionalObserved P x)
  constructor
  rw [← Measure.sum_smul_dirac (conditionalObserved P x)]
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [tsum_fintype, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  simp only [conditionalObserved_singleton, Fintype.sum_prod_type]
  simp [bern, ENNReal.ofReal_add (sub_nonneg.mpr (hp x).2) (hp x).1,
    ENNReal.ofReal_add (sub_nonneg.mpr (hq x).2) (hq x).1,
    ← mul_add, ← ENNReal.ofReal_add (sub_nonneg.mpr (he x).2) (he x).1]
  rw [← ENNReal.ofReal_add (hq x).1 (sub_nonneg.mpr (hq x).2),
    ← ENNReal.ofReal_add (hp x).1 (sub_nonneg.mpr (hp x).2)]
  simp only [add_sub_cancel, ENNReal.ofReal_one, mul_one]
  rw [← ENNReal.ofReal_add (he x).1 (sub_nonneg.mpr (he x).2)]
  simp

/-- The explicit independent extension has its observed conditional kernel as disintegration.  Given [the specified input d](hyp:d), [the specified input e](hyp:e), [the specified input p](hyp:p), [the specified input q](hyp:q), [the specified input he](hyp:he), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the independent obs law comp prod conclusion](goal) holds. -/
lemma independent_obsLaw_compProd {d : ℕ} (e p q : Cov d → ℝ)
    (he : Measurable e) (hp : Measurable p) (hq : Measurable q) :
    let P := independentPrimitive e p q he hp hq
    obsLaw P = uniformLaw d ⊗ₘ conditionalObservedKernel P := by
  dsimp only
  let P := independentPrimitive e p q he hp hq
  letI := uniformLaw_probability d
  letI := conditionalObservedKernel_markov P (fun x => probabilityClip_mem _)
    (fun x => probabilityClip_mem _) (fun x => probabilityClip_mem _)
  rw [independent_obsLaw]
  ext s hs
  have hm : Measurable (fun x => (Measure.dirac x).prod (conditionalObserved P x)) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have heq (x : Cov d) : (Measure.dirac x).prod (conditionalObserved P x) =
        ∑ s : Bool × Bool, conditionalObserved P x {s} • Measure.dirac (x,s) := by
      conv_lhs => rw [← Measure.sum_smul_dirac (conditionalObserved P x)]
      rw [Measure.prod_sum_right, Measure.sum_fintype]
      simp only [Measure.prod_smul_right, Measure.dirac_prod_dirac]
    simp_rw [heq, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_fun_sum
    intro s _
    exact ((conditionalObservedKernel P).measurable_coe (measurableSet_singleton s)).mul
      ((Measure.measurable_coe hA).comp (Measure.measurable_dirac.comp (by fun_prop)))
  rw [Measure.bind_apply hs hm.aemeasurable, Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  rw [Measure.dirac_prod, Measure.map_apply (by fun_prop) hs]
  rfl

/-- Class overlap also holds almost everywhere for any probability-valued raw propensity witness.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input he](hyp:he), [the raw propensity overlap ae conclusion](goal) holds. -/
lemma raw_propensity_overlap_ae {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (he : ∀ x, P.e x ∈ Icc 0 1) :
    ∀ᵐ x ∂uniformLaw d, P.e x ∈ Icc eps (1 - eps) := by
  let W := canonicalLaw P hP
  have hW := canonicalLaw_spec P hP
  letI := uniformLaw_probability d
  letI : IsMarkovKernel (bernKernel P.e P.measurable_e) :=
    ⟨fun x => bern_probability _ (he x)⟩
  let wc := bernKernel (fun x => versionClip (W.e x)) (measurable_versionClip.comp W.measurable_e)
  letI : IsMarkovKernel wc := bernKernel_versionClip_markov W.e W.measurable_e
  letI := bernKernel_sfinite_of_margin W (fun w => w.2.1) (by fun_prop)
    W.e W.measurable_e W.margin_e
  have hcube : MeasurableSet (cube d) := by
    have heq : cube d = ⋂ i : Fin d, (fun x : Cov d => x i) ⁻¹' Icc (0:ℝ) 1 := by
      ext x; simp [cube]
    rw [heq]
    exact MeasurableSet.iInter fun i => measurableSet_Icc.preimage (by fun_prop)
  have hclip : bernKernel W.e W.measurable_e =ᵐ[uniformLaw d] wc := by
    filter_upwards [ae_restrict_mem hcube] with x hx
    change bern (W.e x) = bern (versionClip (W.e x))
    rw [versionClip_eq _ (hW.2.2.2.1.unit x hx)]
  have hu : UniformDesign P := by
    change P.law.map Prod.fst = _
    rw [← hW.1]
    exact hW.2.1
  have hmargin : uniformLaw d ⊗ₘ bernKernel P.e P.measurable_e =
      uniformLaw d ⊗ₘ wc := by
    rw [← Measure.compProd_congr hclip, ← hW.2.1, ← W.margin_e, hW.1,
      P.margin_e, hu]
  have hkernel := Kernel.ae_eq_of_compProd_eq hmargin
  filter_upwards [hkernel, hclip, ae_restrict_mem hcube] with x hx hcx hxc
  have hb : bern (P.e x) = bern (W.e x) := hx.trans hcx.symm
  have ht := congrArg (fun μ : Measure Bool => μ {true}) hb
  simp [bern] at ht
  have hband := hW.2.2.2.1.2 x hxc
  have heq := (ENNReal.ofReal_eq_ofReal_iff (he x).1 (hW.2.2.2.1.unit x hxc).1).mp ht
  rw [heq]
  exact hband

/-- The four observed cells determine the propensity and both arm means under overlap.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input Q](hyp:Q), [the specified input x](hyp:x), [the specified input heP](hyp:heP), [the specified input heQ](hyp:heQ), [the specified input hpP](hyp:hpP), [the specified input hqP](hyp:hqP), [the specified input hpQ](hyp:hpQ), [the specified input hqQ](hyp:hqQ), [the specified input hobs](hyp:hobs), [the overlap level eps](hyp:eps), [the conditional observed identifies margins conclusion](goal) holds. -/
lemma conditionalObserved_identifies_margins {d : ℕ} (P Q : PrimitiveLaw d) (x : Cov d)
    (eps : ℝ) (heps : 0 < eps)
    (heP : P.e x ∈ Icc eps (1 - eps)) (heQ : Q.e x ∈ Icc 0 1)
    (hpP : P.mu0 x ∈ Icc 0 1) (hqP : P.mu1 x ∈ Icc 0 1)
    (hpQ : Q.mu0 x ∈ Icc 0 1) (hqQ : Q.mu1 x ∈ Icc 0 1)
    (hobs : conditionalObserved P x = conditionalObserved Q x) :
    P.e x = Q.e x ∧ P.mu0 x = Q.mu0 x ∧ P.mu1 x = Q.mu1 x := by
  have heP0 : 0 ≤ P.e x := by linarith [heP.1]
  have heP1 : 0 ≤ 1-P.e x := by linarith [heP.2]
  have hcell (s : Bool × Bool) := congrArg (fun μ : Measure (Bool × Bool) => (μ {s}).toReal) hobs
  have hTT := hcell (true,true)
  have hTF := hcell (true,false)
  have hFT := hcell (false,true)
  have hFF := hcell (false,false)
  simp [conditionalObserved_singleton, bern, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal, heP0, heP1, heQ.1, sub_nonneg.mpr heQ.2,
    hpP.1, sub_nonneg.mpr hpP.2, hqP.1, sub_nonneg.mpr hqP.2,
    hpQ.1, sub_nonneg.mpr hpQ.2, hqQ.1, sub_nonneg.mpr hqQ.2] at hTT hTF hFT hFF
  have he : P.e x = Q.e x := by nlinarith only [hTT, hTF]
  refine ⟨he, ?_, ?_⟩
  · rw [← he] at hFT
    nlinarith only [hFT, heP.2, heps]
  · rw [← he] at hTT
    nlinarith only [hTT, heP.1, heps]

/-- In the overlapping independent Bernoulli subfamily, equality of observed laws
identifies the full primitive law, up to null covariates.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input e](hyp:e), [the specified input p](hyp:p), [the specified input q](hyp:q), [the specified input e'](hyp:e'), [the specified input p'](hyp:p'), [the specified input q'](hyp:q'), [the specified input he](hyp:he), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the specified input he'](hyp:he'), [the specified input hp'](hyp:hp'), [the specified input hq'](hyp:hq'), [the specified input hP](hyp:hP), [the specified input hobs](hyp:hobs), [the independent full law eq of obs law conclusion](goal) holds. -/
lemma independent_fullLaw_eq_of_obsLaw {d : ℕ} {alpha beta gamma L eps : ℝ}
    (e p q e' p' q' : Cov d → ℝ)
    (he : Measurable e) (hp : Measurable p) (hq : Measurable q)
    (he' : Measurable e') (hp' : Measurable p') (hq' : Measurable q')
    (hP : PrimitiveClass alpha beta gamma L eps (independentPrimitive e p q he hp hq))
    (hobs : obsLaw (independentPrimitive e p q he hp hq) =
      obsLaw (independentPrimitive e' p' q' he' hp' hq')) :
    independentFullLaw e p q = independentFullLaw e' p' q' := by
  let P := independentPrimitive e p q he hp hq
  let Q := independentPrimitive e' p' q' he' hp' hq'
  letI := uniformLaw_probability d
  letI := conditionalObservedKernel_markov P (fun x => probabilityClip_mem _)
    (fun x => probabilityClip_mem _) (fun x => probabilityClip_mem _)
  letI := conditionalObservedKernel_markov Q (fun x => probabilityClip_mem _)
    (fun x => probabilityClip_mem _) (fun x => probabilityClip_mem _)
  have hk : conditionalObservedKernel P =ᵐ[uniformLaw d] conditionalObservedKernel Q := by
    apply Kernel.ae_eq_of_compProd_eq
    rw [← independent_obsLaw_compProd, ← independent_obsLaw_compProd]
    exact hobs
  have ho := raw_propensity_overlap_ae P hP (fun x => probabilityClip_mem _)
  unfold independentFullLaw
  apply Measure.bind_congr_right
  filter_upwards [hk, ho] with x hx hox
  have hm := conditionalObserved_identifies_margins P Q x eps hP.eps_pos hox (probabilityClip_mem _)
    (probabilityClip_mem _) (probabilityClip_mem _) (probabilityClip_mem _)
    (probabilityClip_mem _) hx
  change probabilityClip (e x) = probabilityClip (e' x) ∧
    probabilityClip (p x) = probabilityClip (p' x) ∧
    probabilityClip (q x) = probabilityClip (q' x) at hm
  rw [hm.1, hm.2.1, hm.2.2]

/-- The first labeled coordinate has exactly the observed-record law.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input j](hyp:j), [the experiment map labeled conclusion](goal) holds. -/
lemma experiment_map_labeled {d n m : ℕ} (P : PrimitiveLaw d) (j : Fin n) :
    (experiment P n m).map (fun w => w.1.1 j) = obsLaw P := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  have heq : (fun w : Sample d n m => w.1.1 j) =
      (Function.eval j) ∘ Prod.fst ∘ Prod.fst := rfl
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold experiment
  rw [Measure.map_fst_prod, measure_univ, one_smul,
    Measure.map_fst_prod, measure_univ, one_smul, Measure.pi_map_eval]
  simp

/-- Equal full experiments identify the canonical target within the marked subfamily.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input hn](hyp:hn), [the specified input hMembers](hyp:hMembers), [the specified input theta](hyp:theta), [the specified input theta'](hyp:theta'), [the specified input sigma](hyp:sigma), [the specified input sigma'](hyp:sigma'), [the specified input hE](hyp:hE), [the marked target eq of experiment conclusion](goal) holds. -/
lemma marked_target_eq_of_experiment {d n m : ℕ} {alpha beta gamma L eps h delta a b : ℝ}
    (hn : 0 < n)
    (hMembers : ∀ theta sigma,
      PrimitiveClass alpha beta gamma L eps ((markedHandle d h delta a b).law theta sigma))
    (theta theta' : Bool) (sigma sigma' : SignArray d h delta)
    (hE : experiment ((markedHandle d h delta a b).law theta sigma) n m =
      experiment ((markedHandle d h delta a b).law theta' sigma') n m) :
    tau ((markedHandle d h delta a b).law theta sigma) (hMembers theta sigma) (x0 d) =
      tau ((markedHandle d h delta a b).law theta' sigma') (hMembers theta' sigma') (x0 d) := by
  have ho := congrArg (fun μ : Measure (Sample d n m) =>
    μ.map (fun w => w.1.1 (⟨0, hn⟩ : Fin n))) hE
  rw [experiment_map_labeled, experiment_map_labeled] at ho
  have hl := independent_fullLaw_eq_of_obsLaw _ _ _ _ _ _
    (measurable_markedPropensity h delta a sigma)
    (measurable_markedMean h delta a b theta false sigma)
    (measurable_markedMean h delta a b theta true sigma)
    (measurable_markedPropensity h delta a sigma')
    (measurable_markedMean h delta a b theta' false sigma')
    (measurable_markedMean h delta a b theta' true sigma')
    (hMembers theta sigma) ho
  have hu := admissible_versions_unique _ _ (hMembers theta sigma)
    (hMembers theta' sigma') hl
  exact (hu (x0 d) (by intro i; norm_num [x0, cube])).2.2.2

/-- A target constant on experiment fibers has a well-defined extension to all laws.  Given [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input E](hyp:E), [the specified input t](hyp:t), [the specified input ht](hyp:ht), [the exists function on image conclusion](goal) holds. -/
lemma exists_function_on_image {A B : Type*} (E : A → B) (t : A → ℝ)
    (ht : ∀ x y, E x = E y → t x = t y) :
    ∃ f : B → ℝ, ∀ x, f (E x) = t x := by
  classical
  let f : B → ℝ := fun b => if hb : ∃ x, E x = b then t hb.choose else 0
  refine ⟨f, ?_⟩
  intro x
  have hx : ∃ y, E y = E x := ⟨x, rfl⟩
  simp only [f, dif_pos hx]
  exact ht hx.choose x hx.choose_spec

/-- The canonical marked target is a functional of the full randomized experiment law.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input hn](hyp:hn), [the specified input hMembers](hyp:hMembers), [the marked experiment target exists conclusion](goal) holds. -/
lemma marked_experiment_target_exists {d n m : ℕ} {alpha beta gamma L eps h delta a b : ℝ}
    (hn : 0 < n)
    (hMembers : ∀ theta sigma,
      PrimitiveClass alpha beta gamma L eps ((markedHandle d h delta a b).law theta sigma)) :
    ∃ Ψ : Measure (Sample d n m) → ℝ, ∀ theta sigma,
      Ψ (experiment ((markedHandle d h delta a b).law theta sigma) n m) =
        tau ((markedHandle d h delta a b).law theta sigma) (hMembers theta sigma) (x0 d) := by
  obtain ⟨Ψ, hΨ⟩ := exists_function_on_image
    (fun z : Bool × SignArray d h delta => experiment ((markedHandle d h delta a b).law z.1 z.2) n m)
    (fun z => tau ((markedHandle d h delta a b).law z.1 z.2) (hMembers z.1 z.2) (x0 d))
    (fun z z' heq => marked_target_eq_of_experiment hn hMembers z.1 z'.1 z.2 z'.2 heq)
  exact ⟨Ψ, fun theta sigma => hΨ (theta,sigma)⟩

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
