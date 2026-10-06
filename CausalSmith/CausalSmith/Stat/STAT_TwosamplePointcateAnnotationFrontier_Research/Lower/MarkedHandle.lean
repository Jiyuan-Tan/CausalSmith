module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Experiment
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.FrameRegularity

/-!
# Lower/MarkedHandle

Two-channel point-CATE annotation frontier: Lower/MarkedHandle
constructions and obligations.
-/

@[expose] public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


variable {d : ℕ}
/-- Total Bernoulli probability parametrization; equal to its argument on [0,1].  Given [the specified input x](hyp:x), [probability clip](goal) is the corresponding construction. -/
def probabilityClip (x : ℝ) : ℝ := max 0 (min 1 x)
/-- Given [the specified input e](hyp:e), [the specified input mu0](hyp:mu0), [the specified input mu1](hyp:mu1), [independent full law](goal) is the corresponding construction. -/
def independentFullLaw (e mu0 mu1 : Cov d → ℝ) : Measure (FullRecord d) :=
  (uniformLaw d).bind (fun x =>
    (Measure.dirac x).prod ((bern (probabilityClip (e x))).prod
      ((bern (probabilityClip (mu0 x))).prod (bern (probabilityClip (mu1 x))))))
/-- Given [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the measurable probability clip conclusion](goal) holds. -/
@[fun_prop] lemma measurable_probabilityClip (f : Cov d → ℝ) (hf : Measurable f) :
    Measurable (fun x => probabilityClip (f x)) := by
  unfold probabilityClip
  fun_prop
/-- Given [the specified input x](hyp:x), [the probability clip mem conclusion](goal) holds. -/
lemma probabilityClip_mem (x : ℝ) : probabilityClip x ∈ Icc (0 : ℝ) 1 := by
  unfold probabilityClip
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Probability clipping fixes every valid Bernoulli parameter.  Given [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the probability clip eq of mem conclusion](goal) holds. -/
lemma probabilityClip_eq_of_mem (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    probabilityClip x = x := by
  rw [probabilityClip, min_eq_right hx.2, max_eq_right hx.1]

/-- Given [the specified input d](hyp:d), [the measurable cube conclusion](goal) holds. -/
lemma measurable_cube (d : ℕ) : MeasurableSet (cube d) := by
  have heq : cube d = ⋂ i : Fin d, (fun x : Cov d => x i) ⁻¹' Icc (0 : ℝ) 1 := by
    ext x
    simp only [cube, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1)).preimage (by fun_prop)

/-- Given [the specified input d](hyp:d), [the uniform law probability conclusion](goal) holds. -/
lemma uniformLaw_probability (d : ℕ) : IsProbabilityMeasure (uniformLaw d) := by
  constructor
  rw [uniformLaw, Measure.restrict_apply_univ]
  have hv := (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    ((MeasurableSet.univ_pi (fun _ : Fin d =>
      (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1)))).nullMeasurableSet)
  change volume (cube d) = 1
  rw [show cube d = WithLp.ofLp ⁻¹' Set.pi Set.univ (fun _ : Fin d => Icc (0 : ℝ) 1) by
    ext x; simp only [cube, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, forall_const]]
  rw [hv]
  rw [volume_pi_pi]
  simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]

/-- Given [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the bern probability conclusion](goal) holds. -/
lemma bern_probability (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (bern p) := by
  constructor
  simp only [bern, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp.2) hp.1]
  norm_num

/-- Given [the specified input e](hyp:e), [the specified input mu0](hyp:mu0), [the specified input mu1](hyp:mu1), [the specified input he](hyp:he), [the specified input h0](hyp:h0), [the specified input h1](hyp:h1), [the measurable independent record kernel conclusion](goal) holds. -/
@[fun_prop] lemma measurable_independentRecordKernel (e mu0 mu1 : Cov d → ℝ)
    (he : Measurable e) (h0 : Measurable mu0) (h1 : Measurable mu1) :
    Measurable (fun x => (Measure.dirac x).prod
      ((bern (probabilityClip (e x))).prod
        ((bern (probabilityClip (mu0 x))).prod (bern (probabilityClip (mu1 x)))))) := by
  simp only [bern, Measure.prod_add, Measure.add_prod, Measure.prod_smul_right,
    Measure.prod_smul_left, Measure.dirac_prod_dirac]
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have hd (a y0 y1 : Bool) :
      Measurable (fun x : Cov d => Measure.dirac (x, a, y0, y1) s) :=
    (Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp (by fun_prop))
  unfold probabilityClip
  fun_prop


/-- Given [the specified input d](hyp:d), [the specified input e](hyp:e), [the specified input mu0](hyp:mu0), [the specified input mu1](hyp:mu1), [the specified input he](hyp:he), [the specified input h0](hyp:h0), [the specified input h1](hyp:h1), [the independent full law probability conclusion](goal) holds. -/
lemma independentFullLaw_probability (d : ℕ) (e mu0 mu1 : Cov d → ℝ)
    (he : Measurable e) (h0 : Measurable mu0) (h1 : Measurable mu1) :
    IsProbabilityMeasure (independentFullLaw e mu0 mu1) := by
  letI := uniformLaw_probability d
  unfold independentFullLaw
  constructor
  rw [Measure.bind_apply MeasurableSet.univ
    (measurable_independentRecordKernel e mu0 mu1 he h0 h1).aemeasurable]
  have hm (x : Cov d) : (Measure.dirac x).prod
      ((bern (probabilityClip (e x))).prod
        ((bern (probabilityClip (mu0 x))).prod (bern (probabilityClip (mu1 x)))))
      Set.univ = 1 := by
    letI := bern_probability _ (probabilityClip_mem (e x))
    letI := bern_probability _ (probabilityClip_mem (mu0 x))
    letI := bern_probability _ (probabilityClip_mem (mu1 x))
    exact measure_univ
  simp_rw [hm]
  simp

/-- Given [the specified input d](hyp:d), [the specified input e](hyp:e), [the specified input mu0](hyp:mu0), [the specified input mu1](hyp:mu1), [the specified input he](hyp:he), [the specified input h0](hyp:h0), [the specified input h1](hyp:h1), [the independent full law support conclusion](goal) holds. -/
lemma independentFullLaw_support (d : ℕ) (e mu0 mu1 : Cov d → ℝ)
    (he : Measurable e) (h0 : Measurable mu0) (h1 : Measurable mu1) :
    independentFullLaw e mu0 mu1 {w | w.1 ∈ cube d} = 1 := by
  letI := uniformLaw_probability d
  unfold independentFullLaw
  have hs : {w : FullRecord d | w.1 ∈ cube d} =
      (cube d) ×ˢ (Set.univ : Set (Bool × Bool × Bool)) := by
    ext w; simp
  rw [hs, Measure.bind_apply ((measurable_cube d).prod MeasurableSet.univ)
    (measurable_independentRecordKernel e mu0 mu1 he h0 h1).aemeasurable]
  have hm (x : Cov d) :
      ((bern (probabilityClip (e x))).prod
        ((bern (probabilityClip (mu0 x))).prod (bern (probabilityClip (mu1 x)))))
        Set.univ = 1 := by
    letI := bern_probability _ (probabilityClip_mem (e x))
    letI := bern_probability _ (probabilityClip_mem (mu0 x))
    letI := bern_probability _ (probabilityClip_mem (mu1 x))
    exact measure_univ
  simp_rw [Measure.prod_prod, hm, mul_one,
    Measure.dirac_apply' _ (measurable_cube d)]
  change (∫⁻ x, (cube d).indicator (fun _ => (1 : ℝ≥0∞)) x ∂uniformLaw d) = 1
  rw [lintegral_indicator_const (measurable_cube d)]
  have hmass : uniformLaw d (cube d) = 1 := by
    simpa only [uniformLaw, Measure.restrict_apply_univ, Measure.restrict_apply_self] using
      (measure_univ (μ := uniformLaw d))
  simp [hmass]

/-- Given [the measure μ](hyp:μ), [the kernel κ](hyp:κ), [the map f](hyp:f), [kernel measurability](hyp:hκ), and [map measurability](hyp:hf), [mapping a bind equals binding the mapped kernels](goal). -/
lemma independent_map_bind {α Ω Ξ : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [MeasurableSpace Ξ] (μ : Measure α) (κ : α → Measure Ω) (f : Ω → Ξ)
    (hκ : Measurable κ) (hf : Measurable f) :
    (μ.bind κ).map f = μ.bind (fun x => (κ x).map f) := by
  rw [← Measure.bind_dirac_eq_map _ hf,
    Measure.bind_bind hκ.aemeasurable
      (show AEMeasurable (fun x => Measure.dirac (f x)) (μ.bind κ) from
        (Measure.measurable_dirac.comp hf).aemeasurable)]
  simp_rw [Measure.bind_dirac_eq_map _ hf]
/-- Given [the specified input d](hyp:d), [the specified input e](hyp:e), [the specified input mu0](hyp:mu0), [the specified input mu1](hyp:mu1), [the specified input he](hyp:he), [the specified input h0](hyp:h0), [the specified input h1](hyp:h1), [the independent full law covariates conclusion](goal) holds. -/
lemma independentFullLaw_covariates (d : ℕ) (e mu0 mu1 : Cov d → ℝ)
    (he : Measurable e) (h0 : Measurable mu0) (h1 : Measurable mu1) :
    (independentFullLaw e mu0 mu1).map Prod.fst = uniformLaw d := by
  unfold independentFullLaw
  rw [independent_map_bind _ _ _ (measurable_independentRecordKernel e mu0 mu1 he h0 h1)
    measurable_fst]
  have hm (x : Cov d) :
      ((Measure.dirac x).prod ((bern (probabilityClip (e x))).prod
        ((bern (probabilityClip (mu0 x))).prod (bern (probabilityClip (mu1 x)))))).map
        Prod.fst = Measure.dirac x := by
    letI := bern_probability _ (probabilityClip_mem (e x))
    letI := bern_probability _ (probabilityClip_mem (mu0 x))
    letI := bern_probability _ (probabilityClip_mem (mu1 x))
    simp
  simp_rw [hm]
  exact Measure.bind_dirac
/-- Given [the specified input d](hyp:d), [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the measurable bern record conclusion](goal) holds. -/
@[fun_prop] lemma measurable_bernRecord (d : ℕ) (p : Cov d → ℝ) (hp : Measurable p) :
    Measurable (fun x => (Measure.dirac x).prod (bern (p x))) := by
  simp only [bern, Measure.prod_add, Measure.prod_smul_right, Measure.dirac_prod_dirac]
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have hd (a : Bool) : Measurable (fun x : Cov d => Measure.dirac (x, a) s) :=
    (Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp (by fun_prop))
  fun_prop
/-- Given [the specified input d](hyp:d), [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the specified input hprob](hyp:hprob), [the bern record bind eq comp prod conclusion](goal) holds. -/
lemma bernRecord_bind_eq_compProd (d : ℕ) (p : Cov d → ℝ) (hp : Measurable p)
    (hprob : ∀ x, p x ∈ Icc (0 : ℝ) 1) :
    (uniformLaw d).bind (fun x => (Measure.dirac x).prod (bern (p x))) =
      (uniformLaw d) ⊗ₘ bernKernel p hp := by
  letI := uniformLaw_probability d
  letI : IsMarkovKernel (bernKernel p hp) := ⟨fun x => bern_probability _ (hprob x)⟩
  ext s hs
  rw [Measure.bind_apply hs (measurable_bernRecord d p hp).aemeasurable, Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hs]
  rfl
/-- Given [the specified input x](hyp:x), [the specified input e](hyp:e), [the specified input p](hyp:p), [the specified input q](hyp:q), [the specified input he](hyp:he), [the specified input hp](hyp:hp), [the specified input hq](hyp:hq), [the independent record margins conclusion](goal) holds. -/
lemma independent_record_margins (x : Cov d) (e p q : ℝ)
    (he : e ∈ Icc (0 : ℝ) 1) (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    let μ := (Measure.dirac x).prod ((bern e).prod ((bern p).prod (bern q)))
    μ.map (fun w => (w.1, w.2.1)) = (Measure.dirac x).prod (bern e) ∧
    μ.map (fun w => (w.1, w.2.2.1)) = (Measure.dirac x).prod (bern p) ∧
    μ.map (fun w => (w.1, w.2.2.2)) = (Measure.dirac x).prod (bern q) := by
  letI := bern_probability e he
  letI := bern_probability p hp
  letI := bern_probability q hq
  have hmap (g : Bool × Bool × Bool → Bool) :
      ((Measure.dirac x).prod ((bern e).prod ((bern p).prod (bern q)))).map
        (fun w => (w.1, g w.2)) =
      (Measure.dirac x).prod (((bern e).prod ((bern p).prod (bern q))).map g) := by
    simpa only [Measure.map_id, Prod.map_def, id_eq] using
      (Measure.map_prod_map (Measure.dirac x) ((bern e).prod ((bern p).prod (bern q)))
        measurable_id (measurable_of_countable g)).symm
  dsimp only
  constructor
  · rw [hmap]
    simp
  · constructor
    · rw [hmap (fun w => w.2.1)]
      have hc : (fun w : Bool × Bool × Bool => w.2.1) = Prod.fst ∘ Prod.snd := rfl
      rw [hc, ← Measure.map_map measurable_fst measurable_snd]
      simp only [Measure.map_snd_prod, Measure.map_fst_prod, measure_univ, one_smul]
    · rw [hmap (fun w => w.2.2)]
      have hc : (fun w : Bool × Bool × Bool => w.2.2) = Prod.snd ∘ Prod.snd := rfl
      rw [hc, ← Measure.map_map measurable_snd measurable_snd]
      simp only [Measure.map_snd_prod, Measure.map_fst_prod, measure_univ, one_smul]
/-- Given [the specified input d](hyp:d), [the specified input e](hyp:e), [the specified input mu0](hyp:mu0), [the specified input mu1](hyp:mu1), [the specified input he](hyp:he), [the specified input h0](hyp:h0), [the specified input h1](hyp:h1), [the independent full law margin conclusion](goal) holds. -/
lemma independentFullLaw_margin (d : ℕ) (e mu0 mu1 : Cov d → ℝ)
    (he : Measurable e) (h0 : Measurable mu0) (h1 : Measurable mu1) :
    (independentFullLaw e mu0 mu1).map (fun w => (w.1,w.2.1)) =
      ((independentFullLaw e mu0 mu1).map Prod.fst) ⊗ₘ
        bernKernel (fun x => probabilityClip (e x)) (measurable_probabilityClip e he) ∧
    (independentFullLaw e mu0 mu1).map (fun w => (w.1,w.2.2.1)) =
      ((independentFullLaw e mu0 mu1).map Prod.fst) ⊗ₘ
        bernKernel (fun x => probabilityClip (mu0 x)) (measurable_probabilityClip mu0 h0) ∧
    (independentFullLaw e mu0 mu1).map (fun w => (w.1,w.2.2.2)) =
      ((independentFullLaw e mu0 mu1).map Prod.fst) ⊗ₘ
        bernKernel (fun x => probabilityClip (mu1 x)) (measurable_probabilityClip mu1 h1)  := by
  rw [independentFullLaw_covariates d e mu0 mu1 he h0 h1]
  have hm (x : Cov d) := independent_record_margins x
    (probabilityClip (e x)) (probabilityClip (mu0 x)) (probabilityClip (mu1 x))
    (probabilityClip_mem _) (probabilityClip_mem _) (probabilityClip_mem _)
  unfold independentFullLaw
  constructor
  · rw [independent_map_bind _ _ _ (measurable_independentRecordKernel e mu0 mu1 he h0 h1)
      (by fun_prop)]
    simp_rw [show ∀ x, ((Measure.dirac x).prod ((bern (probabilityClip (e x))).prod
      ((bern (probabilityClip (mu0 x))).prod (bern (probabilityClip (mu1 x)))))).map
      (fun w => (w.1, w.2.1)) = (Measure.dirac x).prod (bern (probabilityClip (e x)))
      from fun x => (hm x).1]
    exact bernRecord_bind_eq_compProd d _ (measurable_probabilityClip e he) (fun x => probabilityClip_mem _)
  · constructor
    · rw [independent_map_bind _ _ _ (measurable_independentRecordKernel e mu0 mu1 he h0 h1)
        (by fun_prop)]
      simp_rw [show ∀ x, ((Measure.dirac x).prod ((bern (probabilityClip (e x))).prod
        ((bern (probabilityClip (mu0 x))).prod (bern (probabilityClip (mu1 x)))))).map
        (fun w => (w.1, w.2.2.1)) = (Measure.dirac x).prod (bern (probabilityClip (mu0 x)))
        from fun x => (hm x).2.1]
      exact bernRecord_bind_eq_compProd d _ (measurable_probabilityClip mu0 h0) (fun x => probabilityClip_mem _)
    · rw [independent_map_bind _ _ _ (measurable_independentRecordKernel e mu0 mu1 he h0 h1)
        (by fun_prop)]
      simp_rw [show ∀ x, ((Measure.dirac x).prod ((bern (probabilityClip (e x))).prod
        ((bern (probabilityClip (mu0 x))).prod (bern (probabilityClip (mu1 x)))))).map
        (fun w => (w.1, w.2.2.2)) = (Measure.dirac x).prod (bern (probabilityClip (mu1 x)))
        from fun x => (hm x).2.2]
      exact bernRecord_bind_eq_compProd d _ (measurable_probabilityClip mu1 h1) (fun x => probabilityClip_mem _)


/-- Explicit independent potential-outcome extension, total even for inadmissible raw inputs.  Given [the specified input e](hyp:e), [the specified input mu0](hyp:mu0), [the specified input mu1](hyp:mu1), [the specified input he](hyp:he), [the specified input h0](hyp:h0), [the specified input h1](hyp:h1), [independent primitive](goal) is the corresponding construction. -/
def independentPrimitive (e mu0 mu1 : Cov d → ℝ) (he : Measurable e)
    (h0 : Measurable mu0) (h1 : Measurable mu1) : PrimitiveLaw d where
  law := independentFullLaw e mu0 mu1
  probability := independentFullLaw_probability d e mu0 mu1 he h0 h1
  supported := independentFullLaw_support d e mu0 mu1 he h0 h1
  e := fun x => probabilityClip (e x)
  mu0 := fun x => probabilityClip (mu0 x)
  mu1 := fun x => probabilityClip (mu1 x)
  measurable_e := measurable_probabilityClip e he
  measurable_mu0 := measurable_probabilityClip mu0 h0
  measurable_mu1 := measurable_probabilityClip mu1 h1
  margin_e := (independentFullLaw_margin d e mu0 mu1 he h0 h1).1
  margin_mu0 := (independentFullLaw_margin d e mu0 mu1 he h0 h1).2.1
  margin_mu1 := (independentFullLaw_margin d e mu0 mu1 he h0 h1).2.2
/-- Concrete finite sign-pair prior data. No certificate fields are assumed. -/
structure MarkedPriors (d : ℕ) where
  idx : Finset (Fin d → ℤ)
  weight : Bool → ({z // z ∈ idx} → Bool × Bool) → ℝ -- @realizes Pi(finite prior weights)
  law : Bool → ({z // z ∈ idx} → Bool × Bool) → PrimitiveLaw d
  contrast : Bool → Cov d → ℝ -- @realizes tautheta(deterministic contrast)
/-- Given [the specified input h](hyp:h), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [marked contrast](goal) is the corresponding construction. -/
def markedContrast (h a b : ℝ) (theta : Bool) (x : Cov d) : ℝ :=
  -2 * thetaSign theta * a*b*(macroBump h x)^2 -- @realizes tautheta(compensated deterministic contrast)
/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input sigma](hyp:sigma), [the specified input x](hyp:x), [marked propensity](goal) is the corresponding construction. -/
def markedPropensity (h delta a : ℝ) (sigma : SignArray d h delta) (x : Cov d) : ℝ :=
  1/2 + a*signField h delta sigma false x -- @realizes a(propensity amplitude)
/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input arm](hyp:arm), [the specified input sigma](hyp:sigma), [the specified input x](hyp:x), [marked mean](goal) is the corresponding construction. -/
def markedMean (h delta a b : ℝ) (theta arm : Bool) (sigma : SignArray d h delta) (x : Cov d) : ℝ :=
  1/2 + b*signField h delta sigma true x + thetaSign arm * markedContrast h a b theta x / 2 -- @realizes b(control amplitude)
/-- The marked arm functions differ by the prescribed contrast before probability clipping.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input sigma](hyp:sigma), [the specified input x](hyp:x), [the marked mean difference conclusion](goal) holds. -/
lemma markedMean_difference (h delta a b : ℝ) (theta : Bool)
    (sigma : SignArray d h delta) (x : Cov d) :
    markedMean h delta a b theta true sigma x -
      markedMean h delta a b theta false sigma x = markedContrast h a b theta x := by
  simp only [markedMean, thetaSign, Bool.true_eq_false, Bool.false_eq_true, if_true, if_false]
  ring

/-- The contrast is bounded by twice the product of the nuisance amplitudes.  Given [the specified input h](hyp:h), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the abs marked contrast le conclusion](goal) holds. -/
lemma abs_markedContrast_le (h a b : ℝ) (theta : Bool) (x : Cov d)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : |markedContrast h a b theta x| ≤ 2*a*b := by
  have hs : |thetaSign theta| = 1 := by cases theta <;> norm_num [thetaSign]
  have hm := macroBump_mem h x
  have hsq : (macroBump h x)^2 ≤ 1 := by nlinarith [hm.1, hm.2]
  simp only [markedContrast, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), hs, mul_one,
    abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (sq_nonneg (macroBump h x))]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2*a*b by positivity)

/-- The target value is exact, since the macro bump is one at the center.  Given [the specified input h](hyp:h), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the marked contrast at x0 conclusion](goal) holds. -/
lemma markedContrast_at_x0 (h a b : ℝ) (theta : Bool) :
    markedContrast (d:=d) h a b theta (x0 d) = -2*thetaSign theta*a*b := by
  rw [markedContrast, macroBump_at_x0, one_pow, mul_one]

/-- The two hypotheses have target separation four times the amplitude product.  Given [the specified input h](hyp:h), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the marked contrast separation conclusion](goal) holds. -/
lemma markedContrast_separation (h a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |markedContrast (d:=d) h a b true (x0 d) -
      markedContrast h a b false (x0 d)| = 4*a*b := by
  rw [markedContrast_at_x0, markedContrast_at_x0]
  simp only [thetaSign, if_true, Bool.false_eq_true, if_false]
  rw [show -2*1*a*b - -2*(-1)*a*b = -(4*a*b) by ring,
    abs_neg, abs_of_nonneg (by positivity)]

/-- The contrast vanishes off the localization cube.  Given [the specified input h](hyp:h), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input hh](hyp:hh), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the marked contrast zero outside conclusion](goal) holds. -/
lemma markedContrast_zero_outside (h a b : ℝ) (theta : Bool) (hh : 0 < h)
    (x : Cov d) (hx : x ∉ locCube d h) : markedContrast h a b theta x = 0 := by
  simp only [markedContrast, macroBump_zero_outside h hh x hx, zero_pow
    (by decide : 2 ≠ 0), mul_zero]

/-- A uniformly small propensity amplitude guarantees overlap for every sign array.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input sigma](hyp:sigma), [the specified input ha](hyp:ha), [the specified input hsmall](hyp:hsmall), [the specified input x](hyp:x), [the marked propensity overlap conclusion](goal) holds. -/
lemma markedPropensity_overlap (h delta a : ℝ) (sigma : SignArray d h delta)
    (ha : 0 ≤ a) (hsmall : a*(2:ℝ)^d ≤ 1/4) (x : Cov d) :
    markedPropensity h delta a sigma x ∈ Icc (1/4 : ℝ) (3/4) := by
  have hab : |a*signField h delta sigma false x| ≤ 1/4 := by
    rw [abs_mul, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (abs_signField_le h delta sigma false x) ha).trans hsmall
  have hlo := (abs_le.mp hab).1
  have hhi := (abs_le.mp hab).2
  constructor <;> dsimp [markedPropensity] <;> linarith

/-- Uniform field and contrast bounds put both marked arms in the required interior band.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input arm](hyp:arm), [the specified input sigma](hyp:sigma), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the specified input hsmall](hyp:hsmall), [the specified input x](hyp:x), [the marked mean interior conclusion](goal) holds. -/
lemma markedMean_interior (h delta a b : ℝ) (theta arm : Bool)
    (sigma : SignArray d h delta) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsmall : b*(2:ℝ)^d + a*b ≤ 3/8) (x : Cov d) :
    markedMean h delta a b theta arm sigma x ∈ Icc (1/8 : ℝ) (7/8) := by
  have hfield : |b*signField h delta sigma true x| ≤ b*(2:ℝ)^d := by
    rw [abs_mul, abs_of_nonneg hb]
    exact mul_le_mul_of_nonneg_left (abs_signField_le h delta sigma true x) hb
  have hcontrast : |thetaSign arm * markedContrast h a b theta x / 2| ≤ a*b := by
    have hs : |thetaSign arm| = 1 := by cases arm <;> norm_num [thetaSign]
    rw [abs_div, abs_mul, hs, one_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
      (by nlinarith [abs_markedContrast_le h a b theta x ha hb])
  have hlo1 := (abs_le.mp hfield).1
  have hhi1 := (abs_le.mp hfield).2
  have hlo2 := (abs_le.mp hcontrast).1
  have hhi2 := (abs_le.mp hcontrast).2
  constructor <;> dsimp [markedMean] <;> linarith

/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input sigma](hyp:sigma), [the measurable marked propensity conclusion](goal) holds. -/
@[fun_prop] lemma measurable_markedPropensity (h delta a : ℝ) (sigma : SignArray d h delta) :
    Measurable (markedPropensity h delta a sigma) := by
  unfold markedPropensity
  fun_prop
/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input arm](hyp:arm), [the specified input sigma](hyp:sigma), [the measurable marked mean conclusion](goal) holds. -/
@[fun_prop] lemma measurable_markedMean (h delta a b : ℝ) (theta arm : Bool) (sigma : SignArray d h delta) :
    Measurable (markedMean h delta a b theta arm sigma) := by
  unfold markedMean markedContrast
  fun_prop
/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input sigma](hyp:sigma), [marked law](goal) is the corresponding construction. -/
def markedLaw (h delta a b : ℝ) (theta : Bool) (sigma : SignArray d h delta) : PrimitiveLaw d :=
  independentPrimitive (markedPropensity h delta a sigma)
    (markedMean h delta a b theta false sigma) (markedMean h delta a b theta true sigma)
    (measurable_markedPropensity h delta a sigma)
    (measurable_markedMean h delta a b theta false sigma)
    (measurable_markedMean h delta a b theta true sigma)
/-- Under the overlap amplitude condition the law's treatment margin is the prescribed field.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input sigma](hyp:sigma), [the specified input ha](hyp:ha), [the specified input hsmall](hyp:hsmall), [the specified input x](hyp:x), [the marked law propensity eq conclusion](goal) holds. -/
lemma markedLaw_propensity_eq (h delta a b : ℝ) (theta : Bool)
    (sigma : SignArray d h delta) (ha : 0 ≤ a) (hsmall : a*(2:ℝ)^d ≤ 1/4)
    (x : Cov d) : (markedLaw h delta a b theta sigma).e x =
      markedPropensity h delta a sigma x := by
  change probabilityClip (markedPropensity h delta a sigma x) = _
  apply probabilityClip_eq_of_mem
  have hx := markedPropensity_overlap h delta a sigma ha hsmall x
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Under the interior amplitude condition both law margins are the prescribed arm functions.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input sigma](hyp:sigma), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the specified input hsmall](hyp:hsmall), [the specified input x](hyp:x), [the marked law means eq conclusion](goal) holds. -/
lemma markedLaw_means_eq (h delta a b : ℝ) (theta : Bool)
    (sigma : SignArray d h delta) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsmall : b*(2:ℝ)^d + a*b ≤ 3/8) (x : Cov d) :
    (markedLaw h delta a b theta sigma).mu0 x = markedMean h delta a b theta false sigma x ∧
    (markedLaw h delta a b theta sigma).mu1 x = markedMean h delta a b theta true sigma x := by
  have hvalid (arm : Bool) : probabilityClip (markedMean h delta a b theta arm sigma x) =
      markedMean h delta a b theta arm sigma x := by
    apply probabilityClip_eq_of_mem
    have hx := markedMean_interior h delta a b theta arm sigma ha hb hsmall x
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact ⟨hvalid false, hvalid true⟩

/-- The independent primitive's effect is the compensated contrast when clipping is inactive.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input sigma](hyp:sigma), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the specified input hsmall](hyp:hsmall), [the marked law raw contrast eq conclusion](goal) holds. -/
lemma markedLaw_rawContrast_eq (h delta a b : ℝ) (theta : Bool)
    (sigma : SignArray d h delta) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsmall : b*(2:ℝ)^d + a*b ≤ 3/8) :
    rawContrast (markedLaw h delta a b theta sigma) = markedContrast h a b theta := by
  funext x
  have hm := markedLaw_means_eq h delta a b theta sigma ha hb hsmall x
  rw [rawContrast, hm.1, hm.2]
  exact markedMean_difference h delta a b theta sigma x

/-- The constructed primitive satisfies the overlap condition at level eps and the two mean-range conditions at small amplitudes.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input sigma](hyp:sigma), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the specified input he](hyp:he), [the specified input hm](hyp:hm), [the overlap level eps](hyp:eps), [its positivity](hyp:heps), [the overlap amplitude bound](hyp:hov), [the marked law probability bands conclusion](goal) holds. -/
lemma markedLaw_probability_bands (h delta a b : ℝ) (theta : Bool)
    (sigma : SignArray d h delta) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : a*(2:ℝ)^d ≤ 1/4) (hm : b*(2:ℝ)^d + a*b ≤ 3/8)
    (eps : ℝ) (heps : 0 < eps) (hov : a*(2:ℝ)^d ≤ 1/2 - eps) :
    Overlap eps (markedLaw h delta a b theta sigma) ∧
    ControlInterior (markedLaw h delta a b theta sigma) ∧
    TreatedInterior (markedLaw h delta a b theta sigma) := by
  refine ⟨⟨heps, ?_⟩, ?_, ?_⟩
  · intro x hx
    rw [markedLaw_propensity_eq h delta a b theta sigma ha he x]
    have hab : |a*signField h delta sigma false x| ≤ 1/2 - eps := by
      rw [abs_mul, abs_of_nonneg ha]
      exact (mul_le_mul_of_nonneg_left (abs_signField_le h delta sigma false x) ha).trans hov
    have hlo := (abs_le.mp hab).1
    have hhi := (abs_le.mp hab).2
    constructor <;> dsimp [markedPropensity] <;> linarith
  · intro x hx
    rw [(markedLaw_means_eq h delta a b theta sigma ha hb hm x).1]
    have hi := markedMean_interior h delta a b theta false sigma ha hb hm x
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  · intro x hx
    rw [(markedLaw_means_eq h delta a b theta sigma ha hb hm x).2]
    have hi := markedMean_interior h delta a b theta true sigma ha hb hm x
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input theta](hyp:theta), [the specified input sigma](hyp:sigma), [marked weight](goal) is the corresponding construction. -/
def markedWeight (h delta : ℝ) (theta : Bool) (sigma : SignArray d h delta) : ℝ :=
  ∏ z : {z // z ∈ frameIdx d h delta},
    (1+thetaSign theta * thetaSign (sigma z).1 * thetaSign (sigma z).2 / 2)/4 -- @realizes Pi(product sign-pair weights)
-- @node: def:marked-handle
/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [marked handle](goal) is the corresponding construction. -/
def markedHandle (d : ℕ) (h delta a b : ℝ) : MarkedPriors d where
  idx := frameIdx d h delta
  weight := markedWeight h delta
  law := markedLaw h delta a b
  contrast := markedContrast h a b
-- @realizes lowerHandle(explicit finite-prior program)
/-- Given [the specified input H](hyp:H), [prior sign](goal) is the corresponding construction. -/
abbrev PriorSign (H : MarkedPriors d) := {z // z ∈ H.idx} → Bool × Bool
/-- Given [the specified input H](hyp:H), [the specified input theta](hyp:theta), [sign prior](goal) is the corresponding construction. -/
def signPrior (H : MarkedPriors d) (theta : Bool) : Measure (PriorSign H) :=
  ∑ sigma, ENNReal.ofReal (H.weight theta sigma) • Measure.dirac sigma
/-- Given [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input n](hyp:n), [the specified input m](hyp:m), [marked mixture](goal) is the corresponding construction. -/
def markedMixture (H : MarkedPriors d) (theta : Bool) (n m : ℕ) : Measure (Dataset d n m) :=
  ∑ sigma, ENNReal.ofReal (H.weight theta sigma) •
    (Measure.pi (fun _ : Fin n => obsLaw (H.law theta sigma))).prod
      (Measure.pi (fun _ : Fin m => xaLaw (H.law theta sigma))) -- @realizes Mtheta(fixed-size original-record mixture)


end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
