module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Witnesses
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ScaledProductBump
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # The global-tail class strictly contains laws excluded by Dorn A3 -/
@[expose] public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory

/-- The common Bernoulli response is admissible for both the outcome and
Hölder-radius envelopes. [For the stated inputs and conditions](hyp:B,L,hB,hL), [the asserted conclusion holds](goal). -/
lemma baselineSuccess_bounds (B L : ℝ) (hB : 0 < B) (hL : 0 < L) :
    0 < baselineSuccess B L ∧ baselineSuccess B L ≤ 1 / 4 ∧
      B * baselineSuccess B L ≤ L / 4 := by
  unfold baselineSuccess
  have hratio : 0 < L / (4 * B) := by positivity
  refine ⟨lt_min (by norm_num) hratio, min_le_left _ _, ?_⟩
  calc
    B * min (1 / 4) (L / (4 * B)) ≤ B * (L / (4 * B)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hB.le
    _ = L / 4 := by
      field_simp

/-- The strip used in the treatment kernel is Borel measurable. [For the stated inputs and conditions](hyp:d,hd,a), [the asserted conclusion holds](goal). -/
lemma thinStrip_measurableSet (d : ℕ) (hd : 2 ≤ d) (a : ℝ) :
    MeasurableSet (thinStrip d hd a) := by
  unfold thinStrip
  exact measurableSet_le (by fun_prop) (by fun_prop)

/-- The displayed propensity is a measurable function of the covariates. [For the stated inputs and conditions](hyp:d,hd,γ,a), [the asserted conclusion holds](goal). -/
lemma stripPropensity_measurable (d : ℕ) (hd : 2 ≤ d) (γ a : ℝ) :
    Measurable (stripPropensity d hd γ a) := by
  classical
  have hstrip := thinStrip_measurableSet d hd a
  have hite : Measurable (fun x : Fin d → ℝ =>
      if x ∈ thinStrip d hd a then (1 : ℝ) else 0) :=
    Measurable.ite hstrip measurable_const measurable_const
  have hrad : Measurable (fun x : Fin d → ℝ =>
      (min 1 ((2 * ‖x - fun _ => (1 / 2 : ℝ)‖) ^ d)) ^
        ((1 : ℝ) / (γ - 1))) := by
    fun_prop
  unfold stripPropensity centreRadiusCDF centreRadius
  exact measurable_const.min (hrad.add (measurable_const.mul hite))

/-- A pointwise-valid Bernoulli completion is a measurable measure-valued
kernel when its three success probabilities are measurable. [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,he,hp₀,hp₁,hvalid), [the asserted conclusion holds](goal). -/
lemma completionAt_measurable_of_measurable {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1) :
    Measurable (completionAt B e p₀ p₁) := by
  let μe : (Fin d → ℝ) → ProbabilityMeasure Bool := fun x =>
    ⟨realBernoulli (e x), realBernoulli_probability (e x) (hvalid x).1⟩
  let μ₀ : (Fin d → ℝ) → ProbabilityMeasure ℝ := fun x =>
    ⟨scaledBernoulli B (p₀ x), scaledBernoulli_probability B (p₀ x) (hvalid x).2.1⟩
  let μ₁ : (Fin d → ℝ) → ProbabilityMeasure ℝ := fun x =>
    ⟨scaledBernoulli B (p₁ x), scaledBernoulli_probability B (p₁ x) (hvalid x).2.2⟩
  have hμe : Measurable μe := by
    apply Measurable.subtype_mk
    unfold realBernoulli
    fun_prop
  have hμ₀ : Measurable μ₀ := by
    apply Measurable.subtype_mk
    unfold scaledBernoulli
    exact (Measure.measurable_map (fun b : Bool => if b then B else 0) (by fun_prop)).comp
      (by unfold realBernoulli; fun_prop)
  have hμ₁ : Measurable μ₁ := by
    apply Measurable.subtype_mk
    unfold scaledBernoulli
    exact (Measure.measurable_map (fun b : Bool => if b then B else 0) (by fun_prop)).comp
      (by unfold realBernoulli; fun_prop)
  let μ₀₁ : (Fin d → ℝ) → ProbabilityMeasure (ℝ × ℝ) := fun x =>
    ⟨(μ₀ x : Measure ℝ).prod (μ₁ x : Measure ℝ), inferInstance⟩
  have hμ₀₁ : Measurable μ₀₁ := by
    apply Measurable.subtype_mk
    exact ProbabilityMeasure.measurable_fun_prod.comp (hμ₀.prodMk hμ₁)
  let μa : (Fin d → ℝ) → ProbabilityMeasure (Bool × ℝ × ℝ) := fun x =>
    ⟨(μe x : Measure Bool).prod (μ₀₁ x : Measure (ℝ × ℝ)), inferInstance⟩
  have hμa : Measurable μa := by
    apply Measurable.subtype_mk
    exact ProbabilityMeasure.measurable_fun_prod.comp (hμe.prodMk hμ₀₁)
  let μx : (Fin d → ℝ) → ProbabilityMeasure ((Fin d → ℝ) × Bool × ℝ × ℝ) := fun x =>
    ⟨(Measure.dirac x).prod (μa x : Measure (Bool × ℝ × ℝ)), inferInstance⟩
  have hμx : Measurable μx := by
    apply Measurable.subtype_mk
    have hdirac : Measurable (fun x : Fin d → ℝ =>
        (⟨Measure.dirac x, inferInstance⟩ : ProbabilityMeasure (Fin d → ℝ))) := by
      apply Measurable.subtype_mk
      exact Measure.measurable_dirac
    exact ProbabilityMeasure.measurable_fun_prod.comp (hdirac.prodMk hμa)
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
  have heq : completionAt B e p₀ p₁ = fun x =>
      (μx x : Measure ((Fin d → ℝ) × Bool × ℝ × ℝ)).map F := by
    funext x
    letI := realBernoulli_probability (e x) (hvalid x).1
    letI := scaledBernoulli_probability B (p₀ x) (hvalid x).2.1
    letI := scaledBernoulli_probability B (p₁ x) (hvalid x).2.2
    unfold completionAt
    change Measure.map _ ((realBernoulli (e x)).prod
        ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))) =
      Measure.map F ((Measure.dirac x).prod
        ((realBernoulli (e x)).prod
          ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))))
    rw [Measure.dirac_prod, Measure.map_map hF (by fun_prop)]
    rfl
  rw [heq]
  exact (Measure.measurable_map F hF).comp (measurable_subtype_coe.comp hμx)

/-- At a fixed covariate, a treated covariate event has Bernoulli mass `e x`. [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,x,he,hp₀,hp₁,D,hD), [the asserted conclusion holds](goal). -/
lemma completionAt_treated_covariate_event {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc 0 1) (hp₀ : p₀ x ∈ Set.Icc 0 1)
    (hp₁ : p₁ x ∈ Set.Icc 0 1) (D : Set (Fin d → ℝ))
    (hD : MeasurableSet D) :
    completionAt B e p₀ p₁ x {ω | ω.1 ∈ D ∧ ω.2.1 = true} =
      (Measure.dirac x) D * ENNReal.ofReal (e x) := by
  classical
  letI := realBernoulli_probability (e x) he
  letI := scaledBernoulli_probability B (p₀ x) hp₀
  letI := scaledBernoulli_probability B (p₁ x) hp₁
  unfold completionAt
  rw [Measure.map_apply]
  · change ((realBernoulli (e x)).prod
        ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x))))
          {z | x ∈ D ∧ z.1 = true} =
        (Measure.dirac x) D * ENNReal.ofReal (e x)
    by_cases hx : x ∈ D
    · simp only [hx, true_and, if_pos]
      rw [show {a : Bool × ℝ × ℝ | a.1 = true} =
          ({true} : Set Bool) ×ˢ Set.univ by ext z; simp]
      rw [Measure.prod_prod]
      simp [realBernoulli, Measure.dirac_apply' _ hD, hx]
    · simp [hx, Measure.dirac_apply' _ hD]
  · have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  · exact (hD.preimage measurable_fst).inter
      ((measurable_fst.comp measurable_snd) (MeasurableSet.singleton true))

/-- At fixed covariate `x`, the `(X,A)` marginal is the product of the point
mass at `x` and the displayed Bernoulli treatment law. [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,x,he,hp₀,hp₁), [the asserted conclusion holds](goal). -/
lemma completionAt_covariate_treatment_map {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc 0 1) (hp₀ : p₀ x ∈ Set.Icc 0 1)
    (hp₁ : p₁ x ∈ Set.Icc 0 1) :
    (completionAt B e p₀ p₁ x).map (fun ω => (ω.1, ω.2.1)) =
      (Measure.dirac x).prod (realBernoulli (e x)) := by
  let ν := (scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x))
  let μ := (realBernoulli (e x)).prod ν
  letI : IsProbabilityMeasure (realBernoulli (e x)) := realBernoulli_probability _ he
  letI : IsProbabilityMeasure (scaledBernoulli B (p₀ x)) :=
    scaledBernoulli_probability _ _ hp₀
  letI : IsProbabilityMeasure (scaledBernoulli B (p₁ x)) :=
    scaledBernoulli_probability _ _ hp₁
  letI : IsProbabilityMeasure ν := inferInstance
  unfold completionAt
  have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
      if z.1 then z.2.2 else z.2.1) :=
    Measurable.ite (measurable_fst (MeasurableSet.singleton true))
      (by fun_prop) (by fun_prop)
  rw [Measure.map_map (by fun_prop) (by fun_prop (disch := assumption))]
  change Measure.map (fun z : Bool × (ℝ × ℝ) => (x, z.1)) μ = _
  rw [Measure.dirac_prod]
  calc
    Measure.map (fun z : Bool × (ℝ × ℝ) => (x, z.1)) μ =
        Measure.map (fun a : Bool => (x, a)) (Measure.map Prod.fst μ) := by
      rw [Measure.map_map (by fun_prop) measurable_fst]
      congr 1
    _ = Measure.map (fun a : Bool => (x, a)) (realBernoulli (e x)) := by
      congr 1
      dsimp [μ]
      rw [Measure.map_fst_prod]
      simp

/-- The joint `(X,A)` law of a completion bind is the covariate law composed
with its explicit Bernoulli treatment kernel. [For the stated inputs and conditions](hyp:d,mu,B,e,p₀,p₁,he,hp₀,hp₁,hvalid), [the asserted conclusion holds](goal). -/
lemma completionBind_covariate_treatment_compProd {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1) :
    let k : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
      ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
        (by unfold realBernoulli; fun_prop)
    (mu.bind (completionAt B e p₀ p₁)).map (fun ω => (ω.1, ω.2.1)) =
      Measure.compProd mu k := by
  dsimp
  let k : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel k :=
    ⟨fun x => realBernoulli_probability (e x) (hvalid x).1⟩
  have hk : Measurable (completionAt B e p₀ p₁) :=
    completionAt_measurable_of_measurable B e p₀ p₁ he hp₀ hp₁ hvalid
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.bind_apply
    (hs.preimage (by fun_prop)) hk.aemeasurable, Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  have hfix := completionAt_covariate_treatment_map B e p₀ p₁ x
    (hvalid x).1 (hvalid x).2.1 (hvalid x).2.2
  have happ := congrArg (fun m : Measure ((Fin d → ℝ) × Bool) => m s) hfix
  rw [Measure.dirac_prod] at happ
  have happ' := happ.trans (Measure.map_apply (by fun_prop) hs)
  have happ'' := (Measure.map_apply (by fun_prop) hs).symm.trans happ'
  simpa [k] using happ''

/-- The displayed Bernoulli parameter is a version of the propensity of the
observed completion law. [For the stated inputs and conditions](hyp:d,mu,B,e,p₀,p₁,he,hp₀,hp₁,hvalid), [the asserted conclusion holds](goal). -/
lemma completionBind_propensity_ae {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [IsProbabilityMeasure mu] (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1)
    [IsFiniteMeasure ((mu.bind (completionAt B e p₀ p₁)).map observed)] :
    let P := (mu.bind (completionAt B e p₀ p₁)).map observed
    ∀ᵐ x ∂mu, (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
      (fun z => z.1) P x
      {true}).toReal = e x := by
  dsimp
  let P := (mu.bind (completionAt B e p₀ p₁)).map observed
  let k : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  have hk : Measurable (completionAt B e p₀ p₁) :=
    completionAt_measurable_of_measurable B e p₀ p₁ he hp₀ hp₁ hvalid
  have hpoint : ∀ x, IsProbabilityMeasure (completionAt B e p₀ p₁ x) := by
    intro x
    letI := realBernoulli_probability (e x) (hvalid x).1
    letI := scaledBernoulli_probability B (p₀ x) (hvalid x).2.1
    letI := scaledBernoulli_probability B (p₁ x) (hvalid x).2.2
    let ν := (realBernoulli (e x)).prod
      ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))
    letI : IsProbabilityMeasure ν := inferInstance
    unfold completionAt
    change IsProbabilityMeasure (Measure.map _ ν)
    apply Measure.isProbabilityMeasure_map
    apply Measurable.aemeasurable
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  letI : IsProbabilityMeasure (mu.bind (completionAt B e p₀ p₁)) :=
    isProbabilityMeasure_bind hk.aemeasurable (Filter.Eventually.of_forall hpoint)
  have hobs : Measurable (@observed d) := by
    unfold observed
    fun_prop
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    apply Measure.isProbabilityMeasure_map hobs.aemeasurable
  letI : ProbabilityTheory.IsMarkovKernel k :=
    ⟨fun x => realBernoulli_probability (e x) (hvalid x).1⟩
  have hcov : P.map Prod.fst = mu := by
    dsimp [P]
    rw [Measure.map_map (by fun_prop) hobs]
    exact completionBind_covariate_marginal mu B e p₀ p₁ hk.aemeasurable
      (Filter.Eventually.of_forall hvalid)
  have hpair : P.map (fun z => (z.1, z.2.1)) = Measure.compProd mu k := by
    dsimp [P]
    rw [Measure.map_map (by fun_prop) hobs]
    exact completionBind_covariate_treatment_compProd mu B e p₀ p₁
      he hp₀ hp₁ hvalid
  have hae := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := P) (X := fun z : Obs d => z.1) (Y := fun z : Obs d => z.2.1)
    (κ := k) (by fun_prop) (by fun_prop) (by simpa [hcov] using hpair)
  rw [hcov] at hae
  filter_upwards [hae] with x hx
  have hx' := congrArg (fun ν : Measure Bool => (ν {true}).toReal) hx
  change (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1)
    (fun z => z.1) P x
    {true}).toReal = e x
  rw [hx']
  simp [k, realBernoulli, (hvalid x).1.1]

/-- When the two response arms have the same Bernoulli law, selecting the
observed response leaves that law independent of the treatment draw. [For the stated inputs and conditions](hyp:d,B,e,p,x,he,hp), [the asserted conclusion holds](goal). -/
lemma completionAt_observed_joint_map_equal_arms {d : ℕ} (B : ℝ)
    (e p : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc 0 1) (hp : p x ∈ Set.Icc 0 1) :
    (completionAt B e p p x).map
        (fun ω => ((ω.1, ω.2.1), ω.2.2.2.2)) =
      ((Measure.dirac x).prod (realBernoulli (e x))).prod
        (scaledBernoulli B (p x)) := by
  letI := realBernoulli_probability (e x) he
  letI := scaledBernoulli_probability B (p x) hp
  unfold completionAt
  rw [Measure.map_map (by fun_prop) (by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption))]
  rw [Measure.dirac_prod]
  let g : Bool × ℝ × ℝ → ((Fin d → ℝ) × Bool) × ℝ :=
    fun z => ((x, z.1), if z.1 then z.2.2 else z.2.1)
  change Measure.map g ((realBernoulli (e x)).prod
      ((scaledBernoulli B (p x)).prod (scaledBernoulli B (p x)))) = _
  have hg : Measurable g := by
    dsimp [g]
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  unfold realBernoulli
  rw [Measure.add_prod, Measure.map_add _ _ hg,
    Measure.map_add _ _ (by fun_prop), Measure.add_prod]
  congr 1
  · have hbase :
      Measure.map g ((Measure.dirac false).prod
          ((scaledBernoulli B (p x)).prod (scaledBernoulli B (p x)))) =
        (Measure.dirac (x, false)).prod (scaledBernoulli B (p x)) := by
      rw [Measure.dirac_prod, Measure.map_map hg (by fun_prop)]
      change Measure.map ((Prod.mk (x, false)) ∘ (Prod.fst : ℝ × ℝ → ℝ))
          ((scaledBernoulli B (p x)).prod (scaledBernoulli B (p x))) = _
      rw [← Measure.map_map (by fun_prop : Measurable (Prod.mk (x, false)))
        measurable_fst, Measure.map_fst_prod]
      simpa using (Measure.dirac_prod (x := (x, false))
        (ν := scaledBernoulli B (p x))).symm
    calc
      Measure.map g ((ENNReal.ofReal (1 - e x) • Measure.dirac false).prod
          ((scaledBernoulli B (p x)).prod (scaledBernoulli B (p x)))) =
          ENNReal.ofReal (1 - e x) • Measure.map g ((Measure.dirac false).prod
            ((scaledBernoulli B (p x)).prod (scaledBernoulli B (p x)))) := by
        rw [Measure.prod_smul_left, Measure.map_smul]
      _ = ENNReal.ofReal (1 - e x) •
          ((Measure.dirac (x, false)).prod (scaledBernoulli B (p x))) := by rw [hbase]
      _ = (ENNReal.ofReal (1 - e x) • Measure.dirac (x, false)).prod
          (scaledBernoulli B (p x)) := by rw [Measure.prod_smul_left]
      _ = (Measure.map (Prod.mk x)
          (ENNReal.ofReal (1 - e x) • Measure.dirac false)).prod
          (scaledBernoulli B (p x)) := by simp
  · have hbase :
      Measure.map g ((Measure.dirac true).prod
          ((scaledBernoulli B (p x)).prod (scaledBernoulli B (p x)))) =
        (Measure.dirac (x, true)).prod (scaledBernoulli B (p x)) := by
      rw [Measure.dirac_prod, Measure.map_map hg (by fun_prop)]
      change Measure.map ((Prod.mk (x, true)) ∘ (Prod.snd : ℝ × ℝ → ℝ))
          ((scaledBernoulli B (p x)).prod (scaledBernoulli B (p x))) = _
      rw [← Measure.map_map (by fun_prop : Measurable (Prod.mk (x, true)))
        measurable_snd, Measure.map_snd_prod]
      simpa using (Measure.dirac_prod (x := (x, true))
        (ν := scaledBernoulli B (p x))).symm
    calc
      Measure.map g ((ENNReal.ofReal (e x) • Measure.dirac true).prod
          ((scaledBernoulli B (p x)).prod (scaledBernoulli B (p x)))) =
          ENNReal.ofReal (e x) • Measure.map g ((Measure.dirac true).prod
            ((scaledBernoulli B (p x)).prod (scaledBernoulli B (p x)))) := by
        rw [Measure.prod_smul_left, Measure.map_smul]
      _ = ENNReal.ofReal (e x) •
          ((Measure.dirac (x, true)).prod (scaledBernoulli B (p x))) := by rw [hbase]
      _ = (ENNReal.ofReal (e x) • Measure.dirac (x, true)).prod
          (scaledBernoulli B (p x)) := by rw [Measure.prod_smul_left]
      _ = (Measure.map (Prod.mk x)
          (ENNReal.ofReal (e x) • Measure.dirac true)).prod
          (scaledBernoulli B (p x)) := by simp

/-- Mixing the equal-arm fixed-covariate identity gives the joint observed
law as the composition-product of the `(X,A)` law and its response kernel. [For the stated inputs and conditions](hyp:d,mu,B,e,p,he,hp,hvalid), [the asserted conclusion holds](goal). -/
lemma completionBind_observed_joint_compProd_equal_arms {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B : ℝ)
    (e p : (Fin d → ℝ) → ℝ) (he : Measurable e) (hp : Measurable p)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p x ∈ Set.Icc 0 1) :
    let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
      ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
        (by unfold realBernoulli; fun_prop)
    let kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ :=
      ProbabilityTheory.Kernel.mk (fun xa => scaledBernoulli B (p xa.1))
        (by unfold scaledBernoulli realBernoulli; fun_prop)
    (mu.bind (completionAt B e p p)).map
        (fun ω => ((ω.1, ω.2.1), ω.2.2.2.2)) =
      Measure.compProd (Measure.compProd mu kA) kY := by
  dsimp
  let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  let kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ :=
    ProbabilityTheory.Kernel.mk (fun xa => scaledBernoulli B (p xa.1))
      (by unfold scaledBernoulli realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun x => realBernoulli_probability (e x) (hvalid x).1⟩
  letI : ProbabilityTheory.IsMarkovKernel kY :=
    ⟨fun xa => scaledBernoulli_probability B (p xa.1) (hvalid xa.1).2⟩
  have hk : Measurable (completionAt B e p p) :=
    completionAt_measurable_of_measurable B e p p he hp hp
      (fun x => ⟨(hvalid x).1, (hvalid x).2, (hvalid x).2⟩)
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.bind_apply (hs.preimage (by fun_prop)) hk.aemeasurable,
    Measure.compProd_apply hs, Measure.lintegral_compProd]
  swap
  · exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hs
  apply lintegral_congr
  intro x
  letI := realBernoulli_probability (e x) (hvalid x).1
  letI := scaledBernoulli_probability B (p x) (hvalid x).2
  have hfix := completionAt_observed_joint_map_equal_arms B e p x
    (hvalid x).1 (hvalid x).2
  have happ := congrArg (fun m : Measure (((Fin d → ℝ) × Bool) × ℝ) => m s) hfix
  rw [Measure.map_apply (by fun_prop) hs] at happ
  rw [Measure.prod_apply hs] at happ
  rw [lintegral_prod _ (measurable_measure_prodMk_left hs).aemeasurable,
    lintegral_dirac] at happ
  simpa [kA, kY] using happ

/-- The conditional observed-response kernel in the equal-arm completion is
the displayed scaled Bernoulli kernel. [For the stated inputs and conditions](hyp:d,mu,B,e,p,he,hp,hvalid), [the asserted conclusion holds](goal). -/
lemma completionBind_observed_responseKernel_ae_equal_arms {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B : ℝ)
    (e p : (Fin d → ℝ) → ℝ) (he : Measurable e) (hp : Measurable p)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p x ∈ Set.Icc 0 1)
    [IsFiniteMeasure ((mu.bind (completionAt B e p p)).map observed)] :
    let P := (mu.bind (completionAt B e p p)).map observed
    let kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ :=
      ProbabilityTheory.Kernel.mk (fun xa => scaledBernoulli B (p xa.1))
        (by unfold scaledBernoulli realBernoulli; fun_prop)
    ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
      (fun z : Obs d => (z.1, z.2.1)) P =ᵐ[P.map (fun z => (z.1, z.2.1))] kY := by
  dsimp
  let P := (mu.bind (completionAt B e p p)).map observed
  let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  let kY : ProbabilityTheory.Kernel ((Fin d → ℝ) × Bool) ℝ :=
    ProbabilityTheory.Kernel.mk (fun xa => scaledBernoulli B (p xa.1))
      (by unfold scaledBernoulli realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun x => realBernoulli_probability (e x) (hvalid x).1⟩
  letI : ProbabilityTheory.IsMarkovKernel kY :=
    ⟨fun xa => scaledBernoulli_probability B (p xa.1) (hvalid xa.1).2⟩
  have hobs : Measurable (@observed d) := by unfold observed; fun_prop
  have hxa : P.map (fun z => (z.1, z.2.1)) = Measure.compProd mu kA := by
    dsimp [P]
    rw [Measure.map_map (by fun_prop) hobs]
    exact completionBind_covariate_treatment_compProd mu B e p p he hp hp
      (fun x => ⟨(hvalid x).1, (hvalid x).2, (hvalid x).2⟩)
  have hjoint : P.map (fun z => ((z.1, z.2.1), z.2.2)) =
      Measure.compProd (Measure.compProd mu kA) kY := by
    dsimp [P]
    rw [Measure.map_map (by fun_prop) hobs]
    exact completionBind_observed_joint_compProd_equal_arms mu B e p he hp hvalid
  exact ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := P) (X := fun z : Obs d => (z.1, z.2.1))
    (Y := fun z : Obs d => z.2.2) (κ := kY) (by fun_prop) (by fun_prop)
      (by simpa [hxa] using hjoint)

/-- An almost-sure Bernoulli property holds at `true` when its success mass
is positive. [For the stated inputs and conditions](hyp:r,hr,q,hq), [the asserted conclusion holds](goal). -/
lemma realBernoulli_ae_at_true_of_pos (r : ℝ) (hr : 0 < r)
    (q : Bool → Prop) (hq : ∀ᵐ a ∂realBernoulli r, q a) : q true := by
  by_contra htrue
  have hzero : (realBernoulli r) {a | ¬ q a} = 0 := by
    simpa only [Set.compl_setOf, Classical.not_not] using (mem_ae_iff.mp hq)
  have hle : (realBernoulli r) ({true} : Set Bool) ≤
      (realBernoulli r) {a | ¬ q a} := by
    apply measure_mono
    intro a ha
    have ha' : a = true := by simpa using ha
    subst a
    exact htrue
  have hmass : (realBernoulli r) ({true} : Set Bool) = ENNReal.ofReal r := by
    simp [realBernoulli]
  rw [hzero, hmass] at hle
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hr)) hle

/-- Positive treatment mass promotes the equal-arm response-kernel identity
to the treated fibre over almost every covariate. [For the stated inputs and conditions](hyp:d,mu,B,e,p,he,hp,hvalid,hpos), [the asserted conclusion holds](goal). -/
lemma completionBind_treatedKernel_ae_equal_arms {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B : ℝ)
    (e p : (Fin d → ℝ) → ℝ) (he : Measurable e) (hp : Measurable p)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p x ∈ Set.Icc 0 1)
    (hpos : ∀ᵐ x ∂mu, 0 < e x)
    [IsFiniteMeasure ((mu.bind (completionAt B e p p)).map observed)] :
    let P := (mu.bind (completionAt B e p p)).map observed
    ∀ᵐ x ∂mu, treatedKernel P x = scaledBernoulli B (p x) := by
  dsimp
  let P := (mu.bind (completionAt B e p p)).map observed
  let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun x => realBernoulli_probability (e x) (hvalid x).1⟩
  have hobs : Measurable (@observed d) := by unfold observed; fun_prop
  have hxa : P.map (fun z => (z.1, z.2.1)) = Measure.compProd mu kA := by
    dsimp [P]
    rw [Measure.map_map (by fun_prop) hobs]
    exact completionBind_covariate_treatment_compProd mu B e p p he hp hp
      (fun x => ⟨(hvalid x).1, (hvalid x).2, (hvalid x).2⟩)
  have hk := completionBind_observed_responseKernel_ae_equal_arms
    mu B e p he hp hvalid
  dsimp at hk
  rw [hxa] at hk
  have hsections := Measure.ae_ae_of_ae_compProd hk
  filter_upwards [hsections, hpos] with x hx hxp
  have htrue := realBernoulli_ae_at_true_of_pos (e x) hxp
    (fun a => ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
      (fun z : Obs d => (z.1, z.2.1)) P (x, a) = scaledBernoulli B (p x))
    (by simpa [kA] using hx)
  simpa [treatedKernel] using htrue

/-- The mean of the scaled Bernoulli law is its scale times its success
probability. [For the stated inputs and conditions](hyp:B,r,hr), [the asserted conclusion holds](goal). -/
lemma scaledBernoulli_integral_id (B r : ℝ) (hr : r ∈ Set.Icc 0 1) :
    ∫ y, y ∂scaledBernoulli B r = B * r := by
  letI := realBernoulli_probability r hr
  unfold scaledBernoulli
  rw [integral_map (μ := realBernoulli r)
    (φ := fun b : Bool => if b then B else 0) (f := fun y : ℝ => y)
    (by fun_prop) (by fun_prop)]
  unfold realBernoulli
  rw [integral_add_measure
    ((integrable_dirac (by simp)).smul_measure (by simp))
    ((integrable_dirac (by simp)).smul_measure (by simp))]
  simp [ENNReal.toReal_ofReal, hr.1, mul_comm]

/-- The treated regression of the equal-arm completion is `B * p`. [For the stated inputs and conditions](hyp:d,mu,B,e,p,he,hp,hvalid,hpos), [the asserted conclusion holds](goal). -/
lemma completionBind_treatedRegression_ae_equal_arms {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B : ℝ)
    (e p : (Fin d → ℝ) → ℝ) (he : Measurable e) (hp : Measurable p)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p x ∈ Set.Icc 0 1)
    (hpos : ∀ᵐ x ∂mu, 0 < e x)
    [IsFiniteMeasure ((mu.bind (completionAt B e p p)).map observed)] :
    let P := (mu.bind (completionAt B e p p)).map observed
    ∀ᵐ x ∂mu, treatedRegression P x = B * p x := by
  dsimp
  filter_upwards [completionBind_treatedKernel_ae_equal_arms
    mu B e p he hp hvalid hpos] with x hx
  rw [treatedRegression, hx, scaledBernoulli_integral_id B (p x) (hvalid x).2]

/-- A `[0,B]`-valued scaled Bernoulli variable satisfies the model's looser
`B²` centered MGF envelope. [For the stated inputs and conditions](hyp:B,r,t,hB,hr), [the asserted conclusion holds](goal). -/
lemma scaledBernoulli_centered_mgf_bound (B r t : ℝ) (hB : 0 < B)
    (hr : r ∈ Set.Icc 0 1) :
    Integrable (fun y : ℝ => Real.exp (t * (y - B * r)))
        (scaledBernoulli B r) ∧
      ProbabilityTheory.mgf (fun y : ℝ => y - B * r)
        (scaledBernoulli B r) t ≤ Real.exp (B ^ 2 * t ^ 2 / 2) := by
  letI := scaledBernoulli_probability B r hr
  have hsupp : ∀ᵐ y ∂scaledBernoulli B r, y ∈ Set.Icc (0 : ℝ) B := by
    filter_upwards [scaledBernoulli_supported_on_endpoints B r] with y hy
    rcases hy with rfl | rfl
    · exact ⟨le_rfl, hB.le⟩
    · exact ⟨hB.le, le_rfl⟩
  have hsg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    (X := fun y : ℝ => y) (μ := scaledBernoulli B r)
    measurable_id.aemeasurable hsupp
  have hmean := scaledBernoulli_integral_id B r hr
  constructor
  · simpa [hmean] using hsg.integrable_exp_mul t
  · have hle := hsg.mgf_le t
    rw [hmean] at hle
    refine hle.trans (Real.exp_le_exp.mpr ?_)
    rw [show ‖B - 0‖₊ = ⟨B, hB.le⟩ by
      apply Subtype.ext
      simp [Real.norm_eq_abs, abs_of_pos hB]]
    change (B / 2) ^ 2 * t ^ 2 / 2 ≤ B ^ 2 * t ^ 2 / 2
    nlinarith [sq_nonneg B, sq_nonneg t]

/-- Equal bounded Bernoulli arms satisfy the model's treated mean and
sub-Gaussian residual condition. [For the stated inputs and conditions](hyp:d,mu,B,hB,e,p,he,hp,hvalid,hpos), [the asserted conclusion holds](goal). -/
lemma completionBind_boundedMeanSubGaussian_equal_arms {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B : ℝ) (hB : 0 < B)
    (e p : (Fin d → ℝ) → ℝ) (he : Measurable e) (hp : Measurable p)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p x ∈ Set.Icc 0 1)
    (hpos : ∀ᵐ x ∂mu, 0 < e x)
    [IsFiniteMeasure ((mu.bind (completionAt B e p p)).map observed)] :
    let P := (mu.bind (completionAt B e p p)).map observed
    BoundedMeanSubGaussianResidual P B := by
  dsimp
  let P := (mu.bind (completionAt B e p p)).map observed
  have hk := completionBind_treatedKernel_ae_equal_arms
    mu B e p he hp hvalid hpos
  have hm := completionBind_treatedRegression_ae_equal_arms
    mu B e p he hp hvalid hpos
  have hobs : Measurable (@observed d) := by unfold observed; fun_prop
  have hcomp : Measurable (completionAt B e p p) :=
    completionAt_measurable_of_measurable B e p p he hp hp
      (fun x => ⟨(hvalid x).1, (hvalid x).2, (hvalid x).2⟩)
  have hcov : covariateLaw P = mu := by
    dsimp [P, covariateLaw]
    rw [Measure.map_map (by fun_prop) hobs]
    exact completionBind_covariate_marginal mu B e p p hcomp.aemeasurable
      (Filter.Eventually.of_forall (fun x =>
        ⟨(hvalid x).1, (hvalid x).2, (hvalid x).2⟩))
  unfold BoundedMeanSubGaussianResidual
  rw [hcov]
  filter_upwards [hk, hm] with x hkx hmx
  constructor
  · rw [hmx, abs_of_nonneg (mul_nonneg hB.le (hvalid x).2.1)]
    exact (mul_le_of_le_one_right hB.le (hvalid x).2.2)
  · intro t
    rw [hkx, hmx]
    exact scaledBernoulli_centered_mgf_bound B (p x) t hB (hvalid x).2

/-- At fixed covariates, the potential-outcome pair and treatment factor as
the product used by the completion construction. [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,x,he,hp₀,hp₁), [the asserted conclusion holds](goal). -/
lemma completionAt_potential_treatment_factorization {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc 0 1) (hp₀ : p₀ x ∈ Set.Icc 0 1)
    (hp₁ : p₁ x ∈ Set.Icc 0 1) :
    (completionAt B e p₀ p₁ x).map
        (fun ω => (ω.1, ((ω.2.2.1, ω.2.2.2.1), ω.2.1))) =
      (Measure.dirac x).prod
        (((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x))).prod
          (realBernoulli (e x))) := by
  letI := realBernoulli_probability (e x) he
  letI := scaledBernoulli_probability B (p₀ x) hp₀
  letI := scaledBernoulli_probability B (p₁ x) hp₁
  unfold completionAt
  rw [Measure.map_map (by fun_prop) (by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption))]
  rw [Measure.dirac_prod]
  change Measure.map ((Prod.mk x) ∘ Prod.swap)
      ((realBernoulli (e x)).prod
        ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))) = _
  rw [← Measure.map_map (by fun_prop) measurable_swap, Measure.prod_swap]

/-- [For the stated inputs and conditions](hyp:d,B,p₀,p₁,hp₀,hp₁,hvalid), [the asserted conclusion holds](goal). -/

lemma scaledBernoulli_pair_measurable {d : ℕ} (B : ℝ)
    (p₀ p₁ : (Fin d → ℝ) → ℝ) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hvalid : ∀ x, p₀ x ∈ Set.Icc 0 1 ∧ p₁ x ∈ Set.Icc 0 1) :
    Measurable (fun x =>
      (scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x))) := by
  let μ₀ : (Fin d → ℝ) → ProbabilityMeasure ℝ := fun x =>
    ⟨scaledBernoulli B (p₀ x), scaledBernoulli_probability B (p₀ x) (hvalid x).1⟩
  let μ₁ : (Fin d → ℝ) → ProbabilityMeasure ℝ := fun x =>
    ⟨scaledBernoulli B (p₁ x), scaledBernoulli_probability B (p₁ x) (hvalid x).2⟩
  have hμ₀ : Measurable μ₀ := by
    apply Measurable.subtype_mk
    unfold scaledBernoulli realBernoulli
    fun_prop
  have hμ₁ : Measurable μ₁ := by
    apply Measurable.subtype_mk
    unfold scaledBernoulli realBernoulli
    fun_prop
  exact ProbabilityMeasure.measurable_fun_prod.comp (hμ₀.prodMk hμ₁)

/-- Mixing the fixed-covariate factorization preserves the conditional
product of the potential-outcome pair and treatment. [For the stated inputs and conditions](hyp:d,mu,B,e,p₀,p₁,he,hp₀,hp₁,hvalid), [the asserted conclusion holds](goal). -/
lemma completionBind_potential_treatment_factorization {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1) :
    let kY : ProbabilityTheory.Kernel (Fin d → ℝ) (ℝ × ℝ) :=
      ProbabilityTheory.Kernel.mk (fun x =>
        (scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))
        (scaledBernoulli_pair_measurable B p₀ p₁ hp₀ hp₁
          (fun x => ⟨(hvalid x).2.1, (hvalid x).2.2⟩))
    let kA : ProbabilityTheory.Kernel ((Fin d → ℝ) × (ℝ × ℝ)) Bool :=
      ProbabilityTheory.Kernel.mk (fun xy => realBernoulli (e xy.1))
        (by unfold realBernoulli; fun_prop)
    (mu.bind (completionAt B e p₀ p₁)).map
        (fun ω => (ω.1, ((ω.2.2.1, ω.2.2.2.1), ω.2.1))) =
      Measure.compProd mu (ProbabilityTheory.Kernel.compProd kY kA) := by
  dsimp
  let kY : ProbabilityTheory.Kernel (Fin d → ℝ) (ℝ × ℝ) :=
    ProbabilityTheory.Kernel.mk (fun x =>
      (scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))
      (scaledBernoulli_pair_measurable B p₀ p₁ hp₀ hp₁
        (fun x => ⟨(hvalid x).2.1, (hvalid x).2.2⟩))
  let kA : ProbabilityTheory.Kernel ((Fin d → ℝ) × (ℝ × ℝ)) Bool :=
    ProbabilityTheory.Kernel.mk (fun xy => realBernoulli (e xy.1))
      (by unfold realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kY := ⟨fun x => by
    letI := scaledBernoulli_probability B (p₀ x) (hvalid x).2.1
    letI := scaledBernoulli_probability B (p₁ x) (hvalid x).2.2
    exact Measure.prod.instIsProbabilityMeasure _ _⟩
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun xy => realBernoulli_probability (e xy.1) (hvalid xy.1).1⟩
  have hk : Measurable (completionAt B e p₀ p₁) :=
    completionAt_measurable_of_measurable B e p₀ p₁ he hp₀ hp₁ hvalid
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.bind_apply (hs.preimage (by fun_prop)) hk.aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  letI := realBernoulli_probability (e x) (hvalid x).1
  letI := scaledBernoulli_probability B (p₀ x) (hvalid x).2.1
  letI := scaledBernoulli_probability B (p₁ x) (hvalid x).2.2
  have hfix := completionAt_potential_treatment_factorization
    B e p₀ p₁ x (hvalid x).1 (hvalid x).2.1 (hvalid x).2.2
  have happ := congrArg
    (fun m : Measure ((Fin d → ℝ) × ((ℝ × ℝ) × Bool)) => m s) hfix
  rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply hs] at happ
  rw [lintegral_dirac] at happ
  rw [Measure.prod_apply (hs.preimage (by fun_prop))] at happ
  rw [ProbabilityTheory.Kernel.compProd_apply]
  · simpa [kY, kA] using happ
  · exact hs.preimage (by fun_prop)

/-- [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,x,he,hp₀,hp₁), [the asserted conclusion holds](goal). -/

lemma completionAt_covariate_potential_map {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc 0 1) (hp₀ : p₀ x ∈ Set.Icc 0 1)
    (hp₁ : p₁ x ∈ Set.Icc 0 1) :
    (completionAt B e p₀ p₁ x).map
        (fun ω => (ω.1, (ω.2.2.1, ω.2.2.2.1))) =
      (Measure.dirac x).prod
        ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x))) := by
  letI := realBernoulli_probability (e x) he
  letI := scaledBernoulli_probability B (p₀ x) hp₀
  letI := scaledBernoulli_probability B (p₁ x) hp₁
  unfold completionAt
  rw [Measure.map_map (by fun_prop) (by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption))]
  rw [Measure.dirac_prod]
  calc
    Measure.map (fun z : Bool × (ℝ × ℝ) => (x, z.2))
        ((realBernoulli (e x)).prod
          ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))) =
        Measure.map (Prod.mk x) (Measure.map Prod.snd
          ((realBernoulli (e x)).prod
            ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x))))) := by
      rw [Measure.map_map (by fun_prop) measurable_snd]
      congr 1
    _ = _ := by
      rw [Measure.map_snd_prod]
      rw [measure_univ, one_smul]

/-- [For the stated inputs and conditions](hyp:d,mu,B,e,p₀,p₁,he,hp₀,hp₁,hvalid), [the asserted conclusion holds](goal). -/

lemma completionBind_covariate_potential_compProd {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1) :
    let kY : ProbabilityTheory.Kernel (Fin d → ℝ) (ℝ × ℝ) :=
      ProbabilityTheory.Kernel.mk (fun x =>
        (scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))
        (scaledBernoulli_pair_measurable B p₀ p₁ hp₀ hp₁
          (fun x => ⟨(hvalid x).2.1, (hvalid x).2.2⟩))
    (mu.bind (completionAt B e p₀ p₁)).map
        (fun ω => (ω.1, (ω.2.2.1, ω.2.2.2.1))) =
      Measure.compProd mu kY := by
  dsimp
  let kY : ProbabilityTheory.Kernel (Fin d → ℝ) (ℝ × ℝ) :=
    ProbabilityTheory.Kernel.mk (fun x =>
      (scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))
      (scaledBernoulli_pair_measurable B p₀ p₁ hp₀ hp₁
        (fun x => ⟨(hvalid x).2.1, (hvalid x).2.2⟩))
  letI : ProbabilityTheory.IsMarkovKernel kY := ⟨fun x => by
    letI := scaledBernoulli_probability B (p₀ x) (hvalid x).2.1
    letI := scaledBernoulli_probability B (p₁ x) (hvalid x).2.2
    exact Measure.prod.instIsProbabilityMeasure _ _⟩
  have hk : Measurable (completionAt B e p₀ p₁) :=
    completionAt_measurable_of_measurable B e p₀ p₁ he hp₀ hp₁ hvalid
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.bind_apply (hs.preimage (by fun_prop)) hk.aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  letI := scaledBernoulli_probability B (p₀ x) (hvalid x).2.1
  letI := scaledBernoulli_probability B (p₁ x) (hvalid x).2.2
  have hfix := completionAt_covariate_potential_map B e p₀ p₁ x
    (hvalid x).1 (hvalid x).2.1 (hvalid x).2.2
  have happ := congrArg (fun m : Measure ((Fin d → ℝ) × (ℝ × ℝ)) => m s) hfix
  rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply hs,
    lintegral_dirac] at happ
  simpa [kY] using happ

/-- The product completion makes its treatment conditionally independent of
the potential-outcome pair given the covariates. [For the stated inputs and conditions](hyp:d,mu,B,e,p₀,p₁,he,hp₀,hp₁,hvalid), [the asserted conclusion holds](goal). -/
lemma completionBind_condExchangeable {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1)
    [IsFiniteMeasure (mu.bind (completionAt B e p₀ p₁))] :
    CondExchangeable (mu.bind (completionAt B e p₀ p₁)) := by
  let Pc := mu.bind (completionAt B e p₀ p₁)
  let X : Completion d → (Fin d → ℝ) := fun ω => ω.1
  let Y : Completion d → (ℝ × ℝ) := fun ω => (ω.2.2.1, ω.2.2.2.1)
  let A : Completion d → Bool := fun ω => ω.2.1
  let kY : ProbabilityTheory.Kernel (Fin d → ℝ) (ℝ × ℝ) :=
    ProbabilityTheory.Kernel.mk (fun x =>
      (scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))
      (scaledBernoulli_pair_measurable B p₀ p₁ hp₀ hp₁
        (fun x => ⟨(hvalid x).2.1, (hvalid x).2.2⟩))
  let kAx : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  let kA : ProbabilityTheory.Kernel ((Fin d → ℝ) × (ℝ × ℝ)) Bool :=
    ProbabilityTheory.Kernel.mk (fun xy => realBernoulli (e xy.1))
      (by unfold realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kY := ⟨fun x => by
    letI := scaledBernoulli_probability B (p₀ x) (hvalid x).2.1
    letI := scaledBernoulli_probability B (p₁ x) (hvalid x).2.2
    exact Measure.prod.instIsProbabilityMeasure _ _⟩
  letI : ProbabilityTheory.IsMarkovKernel kAx :=
    ⟨fun x => realBernoulli_probability (e x) (hvalid x).1⟩
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun xy => realBernoulli_probability (e xy.1) (hvalid xy.1).1⟩
  have hk : Measurable (completionAt B e p₀ p₁) :=
    completionAt_measurable_of_measurable B e p₀ p₁ he hp₀ hp₁ hvalid
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hcov : Pc.map X = mu := by
    dsimp [Pc, X]
    exact completionBind_covariate_marginal mu B e p₀ p₁ hk.aemeasurable
      (Filter.Eventually.of_forall hvalid)
  have hYmap : Pc.map (fun ω => (X ω, Y ω)) = Measure.compProd mu kY := by
    dsimp [Pc, X, Y]
    exact completionBind_covariate_potential_compProd
      mu B e p₀ p₁ he hp₀ hp₁ hvalid
  have hAmap : Pc.map (fun ω => (X ω, A ω)) = Measure.compProd mu kAx := by
    dsimp [Pc, X, A]
    exact completionBind_covariate_treatment_compProd
      mu B e p₀ p₁ he hp₀ hp₁ hvalid
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
      Measure.compProd mu (ProbabilityTheory.Kernel.prod kY kAx) := by
    dsimp [Pc, X, Y, A]
    rw [← hkprod]
    exact completionBind_potential_treatment_factorization
      mu B e p₀ p₁ he hp₀ hp₁ hvalid
  unfold CondExchangeable
  change ProbabilityTheory.CondIndepFun (MeasurableSpace.comap X inferInstance)
    (Measurable.comap_le hX) Y A Pc
  apply (ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    hY hA hX).2
  rw [← Measure.compProd_eq_comp_prod]
  rw [hcov]
  calc
    Pc.map (fun ω => (X ω, Y ω, A ω)) =
        Measure.compProd mu (ProbabilityTheory.Kernel.prod kY kAx) := hfactor
    _ = Measure.compProd mu (ProbabilityTheory.Kernel.prod
          (ProbabilityTheory.condDistrib Y X Pc)
          (ProbabilityTheory.condDistrib A X Pc)) := by
      symm
      apply Measure.compProd_congr
      filter_upwards [hYcond, hAcond] with x hxy hxa
      rw [ProbabilityTheory.Kernel.prod_apply
          (ProbabilityTheory.condDistrib Y X Pc)
          (ProbabilityTheory.condDistrib A X Pc) x,
        ProbabilityTheory.Kernel.prod_apply kY kAx x, hxy, hxa]

/-- Integrating a nonnegative covariate function over treated observations of
a completion bind weights the base covariate law by the displayed propensity. [For the stated inputs and conditions](hyp:d,μ,B,e,p₀,p₁,f,he,hp₀,hp₁,hf,hfnn,hvalid,D,hD), [the asserted conclusion holds](goal). -/
lemma completionBind_observed_treated_setLIntegral {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (B : ℝ)
    (e p₀ p₁ f : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hf : Measurable f) (hfnn : ∀ x, 0 ≤ f x)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1)
    (D : Set (Fin d → ℝ)) (hD : MeasurableSet D) :
    (∫⁻ z in {z : Obs d | z.2.1 = true ∧ z.1 ∈ D}, ENNReal.ofReal (f z.1)
        ∂(μ.bind (completionAt B e p₀ p₁)).map observed) =
      ∫⁻ x in D, ENNReal.ofReal (f x) * ENNReal.ofReal (e x) ∂μ := by
  let E : Set (Obs d) := {z | z.2.1 = true ∧ z.1 ∈ D}
  have hE : MeasurableSet E :=
    ((measurable_fst.comp measurable_snd) (MeasurableSet.singleton true)).inter
      (hD.preimage measurable_fst)
  have hobs : Measurable (@observed d) := by unfold observed; fun_prop
  have hk : Measurable (completionAt B e p₀ p₁) :=
    completionAt_measurable_of_measurable B e p₀ p₁ he hp₀ hp₁ hvalid
  have hg : Measurable (fun z : Obs d => E.indicator
      (fun z => ENNReal.ofReal (f z.1)) z) := by
    exact (hf.comp measurable_fst).ennreal_ofReal.indicator hE
  rw [← lintegral_indicator hE]
  change (∫⁻ z, E.indicator (fun z => ENNReal.ofReal (f z.1)) z
      ∂(μ.bind (completionAt B e p₀ p₁)).map observed) = _
  rw [lintegral_map hg hobs]
  rw [Measure.lintegral_bind (μ := completionAt B e p₀ p₁)
    (f := fun ω => E.indicator (fun z => ENNReal.ofReal (f z.1)) (observed ω))
    hk.aemeasurable (hg.comp hobs).aemeasurable]
  rw [← lintegral_indicator hD]
  apply lintegral_congr
  intro x
  have hcov : ∀ᵐ ω ∂completionAt B e p₀ p₁ x, ω.1 = x := by
    change ∀ᵐ ω ∂completionAt B e p₀ p₁ x,
      ω.1 ∈ ({x} : Set (Fin d → ℝ))
    apply (ae_map_iff measurable_fst.aemeasurable (measurableSet_singleton x)).1
    rw [completionAt_covariate_marginal B e p₀ p₁ x
      (hvalid x).1 (hvalid x).2.1 (hvalid x).2.2]
    filter_upwards [ae_eq_dirac (fun y : Fin d → ℝ => y)] with y hy
    change y = x
    exact hy
  have hind : (fun ω : Completion d =>
      E.indicator (fun z => ENNReal.ofReal (f z.1)) (observed ω)) =ᵐ[
        completionAt B e p₀ p₁ x]
      ({ω : Completion d | ω.1 ∈ D ∧ ω.2.1 = true}).indicator
        (fun _ => ENNReal.ofReal (f x)) := by
    filter_upwards [hcov] with ω hω
    subst x
    by_cases hωD : ω.1 ∈ D <;> by_cases hωA : ω.2.1 = true <;>
      simp [E, observed, hωD, hωA]
  rw [lintegral_congr_ae hind]
  have hset : MeasurableSet {ω : Completion d | ω.1 ∈ D ∧ ω.2.1 = true} :=
    (hD.preimage measurable_fst).inter
      ((measurable_fst.comp measurable_snd) (MeasurableSet.singleton true))
  rw [lintegral_indicator_const hset]
  rw [completionAt_treated_covariate_event B e p₀ p₁ x
    (hvalid x).1 (hvalid x).2.1 (hvalid x).2.2 D hD]
  by_cases hx : x ∈ D
  · simp [Set.indicator_of_mem hx, Measure.dirac_apply' _ hD, mul_assoc, mul_comm]
  · simp [Set.indicator_of_notMem hx, Measure.dirac_apply' _ hD]

/-- Bochner-integral form of `completionBind_observed_treated_setLIntegral`. [For the stated inputs and conditions](hyp:d,μ,B,e,p₀,p₁,f,he,hp₀,hp₁,hf,hfnn,hvalid,D,hD,hleft,hright), [the asserted conclusion holds](goal). -/
lemma completionBind_observed_treated_setIntegral {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (B : ℝ)
    (e p₀ p₁ f : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hf : Measurable f) (hfnn : ∀ x, 0 ≤ f x)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1)
    (D : Set (Fin d → ℝ)) (hD : MeasurableSet D)
    (hleft : Integrable (fun z : Obs d => f z.1)
      (((μ.bind (completionAt B e p₀ p₁)).map observed).restrict
        {z : Obs d | z.2.1 = true ∧ z.1 ∈ D}))
    (hright : Integrable (fun x => f x * e x) (μ.restrict D)) :
    (∫ z in {z : Obs d | z.2.1 = true ∧ z.1 ∈ D}, f z.1
      ∂(μ.bind (completionAt B e p₀ p₁)).map observed) =
      ∫ x in D, f x * e x ∂μ := by
  let ν := (μ.bind (completionAt B e p₀ p₁)).map observed
  let E : Set (Obs d) := {z | z.2.1 = true ∧ z.1 ∈ D}
  have hlnn : 0 ≤ ∫ z in E, f z.1 ∂ν :=
    integral_nonneg_of_ae (μ := ν.restrict E)
      (Filter.Eventually.of_forall (fun z => hfnn z.1))
  have hrnn : 0 ≤ ∫ x in D, f x * e x ∂μ :=
    integral_nonneg_of_ae (μ := μ.restrict D)
      (Filter.Eventually.of_forall (fun x =>
        mul_nonneg (hfnn x) (hvalid x).1.1))
  change (∫ z in E, f z.1 ∂ν) = ∫ x in D, f x * e x ∂μ
  apply (ENNReal.ofReal_eq_ofReal_iff
    hlnn hrnn).mp
  rw [ofReal_integral_eq_lintegral_ofReal hleft
    (Filter.Eventually.of_forall (fun z => hfnn z.1))]
  rw [ofReal_integral_eq_lintegral_ofReal hright
    (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (hfnn x) (hvalid x).1.1))]
  rw [completionBind_observed_treated_setLIntegral μ B e p₀ p₁ f
    he hp₀ hp₁ hf hfnn hvalid D hD]
  apply setLIntegral_congr_fun hD
  intro x hx
  exact (ENNReal.ofReal_mul (hfnn x)).symm

/-- The thin-strip treatment probability is a valid Bernoulli parameter. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ,x), [the asserted conclusion holds](goal). -/
lemma stripPropensity_mem_Icc (d : ℕ) (hd : 2 ≤ d) (γ a : ℝ)
    (hγ : 1 < γ) (x : Fin d → ℝ) :
    stripPropensity d hd γ a x ∈ Set.Icc 0 1 := by
  classical
  have hbase : 0 ≤ centreRadiusCDF d (centreRadius x) := by
    unfold centreRadiusCDF
    exact le_min (by norm_num) (pow_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) _)
  have hexp : 0 ≤ (1 : ℝ) / (γ - 1) := by positivity
  have hq : 0 ≤ (centreRadiusCDF d (centreRadius x)) ^ ((1 : ℝ) / (γ - 1)) :=
    Real.rpow_nonneg hbase _
  have hbump : 0 ≤ (1 / 4 : ℝ) * if x ∈ thinStrip d hd a then 1 else 0 := by
    split_ifs <;> norm_num
  constructor
  · unfold stripPropensity
    exact le_min (by norm_num) (add_nonneg hq hbump)
  · unfold stripPropensity
    exact min_le_left _ _

/-- The strip component supplies a fixed positive treated mass. [For the stated inputs and conditions](hyp:d,hd,γ,a,_hγ,x,hx), [the asserted conclusion holds](goal). -/
lemma stripPropensity_ge_quarter_on_strip (d : ℕ) (hd : 2 ≤ d) (γ a : ℝ)
    (_hγ : 1 < γ) (x : Fin d → ℝ) (hx : x ∈ thinStrip d hd a) :
    (1 / 4 : ℝ) ≤ stripPropensity d hd γ a x := by
  have hbase : 0 ≤ centreRadiusCDF d (centreRadius x) := by
    unfold centreRadiusCDF
    exact le_min (by norm_num) (pow_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) _)
  have hq : 0 ≤ (centreRadiusCDF d (centreRadius x)) ^ ((1 : ℝ) / (γ - 1)) :=
    Real.rpow_nonneg hbase _
  simp only [stripPropensity, if_pos hx, mul_one]
  exact le_min (by norm_num) (by linarith)

/-- The strip bump raises propensity by at most one quarter. [For the stated inputs and conditions](hyp:d,hd,γ,a,x), [the asserted conclusion holds](goal). -/
lemma stripPropensity_le_radial_add_quarter (d : ℕ) (hd : 2 ≤ d) (γ a : ℝ)
    (x : Fin d → ℝ) :
    stripPropensity d hd γ a x ≤
      (centreRadiusCDF d (centreRadius x)) ^ ((1 : ℝ) / (γ - 1)) + 1 / 4 := by
  classical
  unfold stripPropensity
  apply le_trans (min_le_right _ _)
  split_ifs <;> norm_num

/-- The strip adjustment only increases the radial propensity. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ,x), [the asserted conclusion holds](goal). -/
lemma stripPropensity_ge_radial (d : ℕ) (hd : 2 ≤ d) (γ a : ℝ)
    (hγ : 1 < γ) (x : Fin d → ℝ) :
    (centreRadiusCDF d (centreRadius x)) ^ ((1 : ℝ) / (γ - 1)) ≤
      stripPropensity d hd γ a x := by
  classical
  let q := (centreRadiusCDF d (centreRadius x)) ^ ((1 : ℝ) / (γ - 1))
  have hbase : 0 ≤ centreRadiusCDF d (centreRadius x) := by
    unfold centreRadiusCDF
    exact le_min (by norm_num) (pow_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) _)
  have hbase_le : centreRadiusCDF d (centreRadius x) ≤ 1 := by
    unfold centreRadiusCDF
    exact min_le_left _ _
  have hexp : 0 ≤ (1 : ℝ) / (γ - 1) := by positivity
  have hq : q ≤ 1 := by
    dsimp [q]
    exact Real.rpow_le_one hbase hbase_le hexp
  have hbump : 0 ≤ (1 / 4 : ℝ) * if x ∈ thinStrip d hd a then 1 else 0 := by
    split_ifs <;> norm_num
  unfold stripPropensity
  exact le_min hq (by dsimp [q] at *; linarith)

/-- Every low-propensity event lies inside the corresponding radial event. [For the stated inputs and conditions](hyp:d,hd,γ,a,t,hγ), [the asserted conclusion holds](goal). -/
lemma stripTail_subset_radial (d : ℕ) (hd : 2 ≤ d) (γ a t : ℝ)
    (hγ : 1 < γ) :
    {x | stripPropensity d hd γ a x ≤ t} ⊆
      {x | (centreRadiusCDF d (centreRadius x)) ^ ((1 : ℝ) / (γ - 1)) ≤ t} := by
  intro x hx
  exact (stripPropensity_ge_radial d hd γ a hγ x).trans hx

/-- A propensity sublevel is contained in the corresponding radial CDF
sublevel. This is the event inclusion behind the exact global tail bound. [For the stated inputs and conditions](hyp:d,hd,γ,a,t,hγ), [the asserted conclusion holds](goal). -/
lemma stripTail_subset_radiusCDF_sublevel (d : ℕ) (hd : 2 ≤ d)
    (γ a t : ℝ) (hγ : 1 < γ) :
    {x | stripPropensity d hd γ a x ≤ t} ⊆
      {x | centreRadiusCDF d (centreRadius x) ≤ t ^ (γ - 1)} := by
  intro x hx
  have hbase : 0 ≤ centreRadiusCDF d (centreRadius x) := by
    unfold centreRadiusCDF
    exact le_min (by norm_num)
      (pow_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) _)
  have hpow := Real.rpow_le_rpow
    (Real.rpow_nonneg hbase ((1 : ℝ) / (γ - 1)))
    ((stripTail_subset_radial d hd γ a t hγ) hx) (by linarith : 0 ≤ γ - 1)
  simpa [Real.rpow_inv_rpow hbase (by linarith : γ - 1 ≠ 0)] using hpow

/-- The thin strip carries a fixed treatment probability at its centre. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ,ha), [the asserted conclusion holds](goal). -/
lemma stripPropensity_centre (d : ℕ) (hd : 2 ≤ d) (γ a : ℝ)
    (hγ : 1 < γ) (ha : 0 < a) :
    stripPropensity d hd γ a (fun _ => (1 / 2 : ℝ)) = 1 / 4 := by
  have hmem : (fun _ : Fin d => (1 / 2 : ℝ)) ∈ thinStrip d hd a := by
    simp [thinStrip, Real.zero_rpow ha.ne']
  have hdpos : 0 < d := by omega
  have hexp : (γ - 1 : ℝ)⁻¹ ≠ 0 := by positivity
  simp only [stripPropensity, centreRadius, centreRadiusCDF]
  rw [if_pos hmem]
  simp [Real.zero_rpow hexp, zero_pow hdpos.ne']
  norm_num

/-- Outside the strip, the propensity is exactly its radial component. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ,x,hx), [the asserted conclusion holds](goal). -/
lemma stripPropensity_off_strip (d : ℕ) (hd : 2 ≤ d) (γ a : ℝ)
    (hγ : 1 < γ) (x : Fin d → ℝ) (hx : x ∉ thinStrip d hd a) :
    stripPropensity d hd γ a x =
      (centreRadiusCDF d (centreRadius x)) ^ ((1 : ℝ) / (γ - 1)) := by
  have hbase : 0 ≤ centreRadiusCDF d (centreRadius x) := by
    unfold centreRadiusCDF
    exact le_min (by norm_num) (pow_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) _)
  have hbase_le : centreRadiusCDF d (centreRadius x) ≤ 1 := by
    unfold centreRadiusCDF
    exact min_le_left _ _
  have hexp : 0 ≤ (1 : ℝ) / (γ - 1) := by positivity
  have hq : (centreRadiusCDF d (centreRadius x)) ^ ((1 : ℝ) / (γ - 1)) ≤ 1 :=
    Real.rpow_le_one hbase hbase_le hexp
  simp only [stripPropensity, if_neg hx, mul_zero, add_zero]
  exact min_eq_right hq

/-- The radial treatment probability on a small cube is bounded by its outer radius. [For the stated inputs and conditions](hyp:d,hd,γ,a,h,hγ,x,hx,hr), [the asserted conclusion holds](goal). -/
lemma stripPropensity_off_strip_radius_bound (d : ℕ) (hd : 2 ≤ d)
    (γ a h : ℝ) (hγ : 1 < γ) (x : Fin d → ℝ)
    (hx : x ∉ thinStrip d hd a) (hr : centreRadius x ≤ h) :
    stripPropensity d hd γ a x ≤
      ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) := by
  rw [stripPropensity_off_strip d hd γ a hγ x hx]
  apply Real.rpow_le_rpow
  · unfold centreRadiusCDF
    exact le_min (by norm_num) (pow_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) _)
  · unfold centreRadiusCDF
    calc
      min 1 ((2 * centreRadius x) ^ d) ≤ (2 * centreRadius x) ^ d := min_le_right _ _
      _ ≤ (2 * h) ^ d := by
        exact pow_le_pow_left₀
          (mul_nonneg (by norm_num) (by unfold centreRadius; exact norm_nonneg _))
          (by linarith) _
  · positivity

/-- At a sufficiently small radius, a propensity level above a quarter-scale
threshold can occur only inside the thin strip. [For the stated inputs and conditions](hyp:d,hd,γ,a,h,ρ,hγ,hsmall), [the asserted conclusion holds](goal). -/
lemma stripSuperlevel_subset_strip (d : ℕ) (hd : 2 ≤ d)
    (γ a h ρ : ℝ) (hγ : 1 < γ)
    (hsmall : ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) < ρ / 4) :
    {x | centreRadius x ≤ h ∧ ρ / 4 ≤ stripPropensity d hd γ a x} ⊆
      thinStrip d hd a := by
  intro x hx
  by_contra hnot
  have hbound := stripPropensity_off_strip_radius_bound d hd γ a h hγ x hnot hx.1
  linarith [hx.2]

/-- Every ball centered at the strip center has propensity supremum at least one quarter. [For the stated inputs and conditions](hyp:d,hd,γ,a,h,hγ,ha), [the asserted conclusion holds](goal). -/
lemma stripPropensity_ball_sup_ge_quarter (d : ℕ) (hd : 2 ≤ d)
    (γ a h : ℝ) (hγ : 1 < γ) (ha : 0 < a) :
    (1 / 4 : ℝ) ≤ sSup
      (stripPropensity d hd γ a '' ball2 (fun _ => (1 / 2 : ℝ)) h) := by
  let x₀ : Fin d → ℝ := fun _ => 1 / 2
  have hx : x₀ ∈ ball2 x₀ h := by
    simp [ball2, x₀, sq_nonneg]
  have hupper : BddAbove (stripPropensity d hd γ a '' ball2 x₀ h) := by
    refine ⟨1, ?_⟩
    rintro y ⟨x, -, rfl⟩
    exact (stripPropensity_mem_Icc d hd γ a hγ x).2
  have hmem : stripPropensity d hd γ a x₀ ∈
      stripPropensity d hd γ a '' ball2 x₀ h := ⟨x₀, hx, rfl⟩
  have hcentre : stripPropensity d hd γ a x₀ = 1 / 4 :=
    stripPropensity_centre d hd γ a hγ ha
  rw [← hcentre]
  exact le_csSup hupper hmem

/-- The centre also witnesses the quarter lower bound when the local ball is
restricted to the covariate cube, as in Dorn's A3. [For the stated inputs and conditions](hyp:d,hd,γ,a,h,hγ,ha), [the asserted conclusion holds](goal). -/
lemma stripPropensity_ball_cube_sup_ge_quarter (d : ℕ) (hd : 2 ≤ d)
    (γ a h : ℝ) (hγ : 1 < γ) (ha : 0 < a) :
    (1 / 4 : ℝ) ≤ sSup
      (stripPropensity d hd γ a ''
        (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ cube d)) := by
  let x₀ : Fin d → ℝ := fun _ => 1 / 2
  have hx : x₀ ∈ ball2 x₀ h ∩ cube d := by
    constructor
    · simp [ball2, x₀, sq_nonneg]
    · simp [cube, x₀, Pi.le_def]
      intro i
      norm_num
  have hupper : BddAbove
      (stripPropensity d hd γ a '' (ball2 x₀ h ∩ cube d)) := by
    refine ⟨1, ?_⟩
    rintro y ⟨x, -, rfl⟩
    exact (stripPropensity_mem_Icc d hd γ a hγ x).2
  have hmem : stripPropensity d hd γ a x₀ ∈
      stripPropensity d hd γ a '' (ball2 x₀ h ∩ cube d) :=
    ⟨x₀, hx, rfl⟩
  rw [← stripPropensity_centre d hd γ a hγ ha]
  exact le_csSup hupper hmem

/-- A sufficiently small radial bound confines Dorn's local superlevel event
to the thin strip, for every proposed A3 level `ρ`. [For the stated inputs and conditions](hyp:d,hd,γ,a,h,ρ,hγ,ha,hρ,hsmall), [the asserted conclusion holds](goal). -/
lemma stripSuperlevel_ball_cube_subset_strip (d : ℕ) (hd : 2 ≤ d)
    (γ a h ρ : ℝ) (hγ : 1 < γ) (ha : 0 < a) (hρ : 0 < ρ)
    (hsmall : ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) < ρ / 4) :
    {x | centreRadius x ≤ h ∧
      ρ * sSup (stripPropensity d hd γ a ''
        (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ cube d)) ≤
        stripPropensity d hd γ a x} ⊆ thinStrip d hd a := by
  have hsup := stripPropensity_ball_cube_sup_ge_quarter d hd γ a h hγ ha
  apply Set.Subset.trans ?_ (stripSuperlevel_subset_strip d hd γ a h ρ hγ hsmall)
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hlevel := (mul_le_mul_of_nonneg_left hsup (le_of_lt hρ)).trans hx.2
  nlinarith [hlevel]

/-- A vanishing local fraction of the strip defeats every proposed numerical
anti-concentration triple. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ,ha,P,hlocal), [the asserted conclusion holds](goal). -/
lemma strip_not_dornA3AntiConcentration_of_local_strip_ratio (d : ℕ) (hd : 2 ≤ d)
    (γ a : ℝ) (hγ : 1 < γ) (ha : 0 < a)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hlocal : ∀ (ρ ν h₀ : ℝ), 0 < ρ → 0 < ν → 0 < h₀ →
      ∃ h : ℝ, 0 < h ∧ h ≤ h₀ ∧
        ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) < ρ / 4 ∧
        0 < (covariateLaw P).real
          (ball2 (fun _ => (1 / 2 : ℝ)) h) ∧
        (covariateLaw P).real
          (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) /
          (covariateLaw P).real
            (ball2 (fun _ => (1 / 2 : ℝ)) h) ≤ ν) :
    ¬ DornA3AntiConcentrationOnCube P (stripPropensity d hd γ a) := by
  intro hA3
  obtain ⟨ρ, ν, h₀, hρ, hν, hh₀, hA3bound⟩ := hA3
  obtain ⟨h, hh, hh₀', hsmall, hball, hratio⟩ := hlocal ρ ν h₀ hρ hν hh₀
  have hx₀ : (fun _ : Fin d => (1 / 2 : ℝ)) ∈ cube d := by
    simp [cube, Pi.le_def]
    intro i
    norm_num
  have hbound := hA3bound (fun _ => (1 / 2 : ℝ)) hx₀ h ⟨hh, hh₀'⟩
  have hsubset :
      {x | stripPropensity d hd γ a x ≥
          ρ * sSup (stripPropensity d hd γ a ''
            (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ cube d))} ∩
        ball2 (fun _ => (1 / 2 : ℝ)) h ⊆
      thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h := by
    intro x hx
    refine ⟨?_, hx.2⟩
    apply stripSuperlevel_ball_cube_subset_strip d hd γ a h ρ hγ ha hρ hsmall
    constructor
    · have hcoord : centreRadius x ≤ h := by
        unfold centreRadius
        letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
        apply (pi_norm_le_iff_of_nonempty _).2
        intro i
        have hi : (x i - (1 / 2 : ℝ)) ^ 2 ≤
            ∑ j : Fin d, (x j - 1 / 2) ^ 2 := by
          exact Finset.single_le_sum
            (fun j _ => sq_nonneg (x j - 1 / 2)) (Finset.mem_univ i)
        have hball' : (∑ j : Fin d, (x j - 1 / 2) ^ 2) ≤ h ^ 2 := hx.2
        have habs : |x i - 1 / 2| ≤ h := by
          nlinarith [sq_abs (x i - (1 / 2 : ℝ)), abs_nonneg (x i - (1 / 2 : ℝ))]
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using habs
      exact hcoord
    · exact hx.1
  have hmono : (covariateLaw P).real
      ({x | stripPropensity d hd γ a x ≥
          ρ * sSup (stripPropensity d hd γ a ''
            (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ cube d))} ∩
        ball2 (fun _ => (1 / 2 : ℝ)) h) ≤
      (covariateLaw P).real
        (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) := by
    have : IsProbabilityMeasure (covariateLaw P) := by
      unfold covariateLaw
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    exact measureReal_mono hsubset
  have hdiv := (div_le_div_of_nonneg_right hmono hball.le).trans hratio
  exact (not_lt_of_ge hdiv) hbound

/-- Dorn's full A3 property implies its numerical anti-concentration clause. [For the stated inputs and conditions](hyp:d,P,e), [the asserted conclusion holds](goal). -/
lemma dornA3AntiConcentrationOnCube_of_dornA3OnCube {d : ℕ}
    (P : Measure (Obs d)) (e : (Fin d → ℝ) → ℝ) :
    DornA3OnCube P e → DornA3AntiConcentrationOnCube P e := by
  intro hA3
  change DornA3 (cube d)
    ({(P, (fun _ => 0), (fun _ => 0), e)} : Set (DornSourceLaw d)) at hA3
  obtain ⟨_, _, _, ρ, ν, h₀, hρ, hν, hh₀, hA3bound⟩ := hA3
  refine ⟨ρ, ν, h₀, hρ, hν, hh₀, ?_⟩
  intro x₀ hx₀ h hh
  exact hA3bound (P, (fun _ => 0), (fun _ => 0), e)
    (Set.mem_singleton _) x₀ hx₀ h hh

/-- Failure of the numerical anti-concentration clause rules out full Dorn A3. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ,ha,P,hlocal), [the asserted conclusion holds](goal). -/
lemma strip_not_dornA3_of_local_strip_ratio (d : ℕ) (hd : 2 ≤ d)
    (γ a : ℝ) (hγ : 1 < γ) (ha : 0 < a)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hlocal : ∀ (ρ ν h₀ : ℝ), 0 < ρ → 0 < ν → 0 < h₀ →
      ∃ h : ℝ, 0 < h ∧ h ≤ h₀ ∧
        ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) < ρ / 4 ∧
        0 < (covariateLaw P).real
          (ball2 (fun _ => (1 / 2 : ℝ)) h) ∧
        (covariateLaw P).real
          (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) /
          (covariateLaw P).real
            (ball2 (fun _ => (1 / 2 : ℝ)) h) ≤ ν) :
    ¬ DornA3OnCube P (stripPropensity d hd γ a) := by
  intro hA3
  exact strip_not_dornA3AntiConcentration_of_local_strip_ratio
    d hd γ a hγ ha P hlocal
      (dornA3AntiConcentrationOnCube_of_dornA3OnCube P
        (stripPropensity d hd γ a) hA3)

/-- The off-strip radial propensity bound vanishes as the neighborhood shrinks. [For the stated inputs and conditions](hyp:d,hd,γ,hγ), [the asserted conclusion holds](goal). -/
lemma stripRadialBound_tendsto_zero (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : 1 < γ) :
    Filter.Tendsto (fun h : ℝ => ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hpow : Filter.Tendsto (fun h : ℝ => (2 * h) ^ d)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc : Continuous (fun h : ℝ => (2 * h) ^ d) := by fun_prop
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp [zero_pow (by omega : d ≠ 0)]
  have hexp : 0 ≤ (1 : ℝ) / (γ - 1) := by positivity
  have hne : (1 : ℝ) / (γ - 1) ≠ 0 := by positivity
  convert hpow.rpow_const (Or.inr hexp) using 1
  rw [Real.zero_rpow hne]

/-- A neighborhood can be chosen below both a proposed A3 radius and its
superlevel threshold. [For the stated inputs and conditions](hyp:d,hd,γ,ρ,h₀,hγ,hρ,hh₀), [the asserted conclusion holds](goal). -/
lemma stripRadialBound_small (d : ℕ) (hd : 2 ≤ d)
    (γ ρ h₀ : ℝ) (hγ : 1 < γ) (hρ : 0 < ρ) (hh₀ : 0 < h₀) :
    ∃ h : ℝ, 0 < h ∧ h ≤ h₀ ∧
      ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) < ρ / 4 := by
  have hlim := stripRadialBound_tendsto_zero d hd γ hγ
  have hsmall : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) < ρ / 4 :=
    hlim.eventually (eventually_lt_nhds (by positivity))
  have hwidth : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), h < h₀ :=
    (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds hh₀)
  have hpos : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < h :=
    self_mem_nhdsWithin
  obtain ⟨h, hh, hbound, hrad⟩ :=
    (hpos.and (hwidth.and hsmall)).exists
  exact ⟨h, hh, hbound.le, hrad⟩

/-- In a centered cube, the strip's transverse coordinate has width `h ^ a`.
This is the geometric bound used for its vanishing local mass and second moment. [For the stated inputs and conditions](hyp:d,hd,a,h,ha,hh,x,hx,hr), [the asserted conclusion holds](goal). -/
lemma thinStrip_transverse_coordinate_bound (d : ℕ) (hd : 2 ≤ d)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) (x : Fin d → ℝ)
    (hx : x ∈ thinStrip d hd a) (hr : centreRadius x ≤ h) :
    |x ⟨1, by omega⟩ - 1 / 2| ≤ h ^ a := by
  have hfirst : |x ⟨0, by omega⟩ - 1 / 2| ≤ h := by
    have hcoord := norm_le_pi_norm
      (x - (fun _ : Fin d => (1 / 2 : ℝ))) ⟨0, by omega⟩
    have hcoord' : |x ⟨0, by omega⟩ - 1 / 2| ≤ centreRadius x := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs, centreRadius] using hcoord
    exact hcoord'.trans hr
  calc
    |x ⟨1, by omega⟩ - 1 / 2| ≤
        |x ⟨0, by omega⟩ - 1 / 2| ^ a := hx
    _ ≤ h ^ a := Real.rpow_le_rpow (abs_nonneg _) hfirst ha

/-- The same transverse-width bound holds in a centered Euclidean ball. [For the stated inputs and conditions](hyp:d,hd,a,h,ha,hh,x,hx,hball), [the asserted conclusion holds](goal). -/
lemma thinStrip_ball_transverse_coordinate_bound (d : ℕ) (hd : 2 ≤ d)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) (x : Fin d → ℝ)
    (hx : x ∈ thinStrip d hd a)
    (hball : x ∈ ball2 (fun _ => (1 / 2 : ℝ)) h) :
    |x ⟨1, by omega⟩ - 1 / 2| ≤ h ^ a := by
  have hr : centreRadius x ≤ h := by
    unfold centreRadius
    letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    apply (pi_norm_le_iff_of_nonempty _).2
    intro i
    have hi : (x i - (1 / 2 : ℝ)) ^ 2 ≤
        ∑ j : Fin d, (x j - 1 / 2) ^ 2 :=
      Finset.single_le_sum
        (fun j _ => sq_nonneg (x j - 1 / 2)) (Finset.mem_univ i)
    have hball' : (∑ j : Fin d, (x j - 1 / 2) ^ 2) ≤ h ^ 2 := hball
    have habs : |x i - 1 / 2| ≤ h := by
      nlinarith [sq_abs (x i - (1 / 2 : ℝ)), abs_nonneg (x i - (1 / 2 : ℝ))]
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using habs
  exact thinStrip_transverse_coordinate_bound d hd a h ha hh x hx hr

/-- A one-sided product box inside the thin strip. Its first coordinate is
kept away from the centre so the transverse width has a uniform lower scale. For [the stated inputs and conditions](hyp:d,hd,a,h), [the `thinStripCoreBox` object being defined](goal). -/
noncomputable def thinStripCoreBox (d : ℕ) (hd : 2 ≤ d) (a h : ℝ) :
    Set (Fin d → ℝ) :=
  let r := h / (4 * d)
  Set.Icc
    (fun i => if i = ⟨1, by omega⟩ then 1 / 2 - r ^ a else 1 / 2 + r)
    (fun i => if i = ⟨1, by omega⟩ then 1 / 2 + r ^ a else 1 / 2 + 2 * r)

/-- For a small positive radius, the core box lies in both the strip and the
centered Euclidean ball. [For the stated inputs and conditions](hyp:d,hd,a,h,ha,hh,hh1), [the asserted conclusion holds](goal). -/
lemma thinStripCoreBox_subset (d : ℕ) (hd : 2 ≤ d) (a h : ℝ)
    (ha : 1 < a) (hh : 0 < h) (hh1 : h ≤ 1) :
    thinStripCoreBox d hd a h ⊆
      thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h := by
  let r : ℝ := h / (4 * d)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * d)).2
    nlinarith
  have hra : r ^ a ≤ r := Real.rpow_le_self_of_le_one hr.le hr1 ha.le
  intro x hx
  have hx' := hx
  change (fun i => if i = ⟨1, by omega⟩ then 1 / 2 - r ^ a else 1 / 2 + r) ≤ x ∧
    x ≤ (fun i => if i = ⟨1, by omega⟩ then 1 / 2 + r ^ a else 1 / 2 + 2 * r) at hx'
  constructor
  · unfold thinStrip
    have hzeroLo := hx'.1 ⟨0, by omega⟩
    have honeLo := hx'.1 ⟨1, by omega⟩
    have honeHi := hx'.2 ⟨1, by omega⟩
    simp at hzeroLo honeLo honeHi
    have hzero : r ≤ |x ⟨0, by omega⟩ - 1 / 2| := by
      rw [le_abs]
      left
      linarith
    have hone : |x ⟨1, by omega⟩ - 1 / 2| ≤ r ^ a := by
      rw [abs_le]
      constructor <;> linarith
    exact hone.trans (Real.rpow_le_rpow hr.le hzero (by linarith : 0 ≤ a))
  · unfold ball2
    have hcoord : ∀ i : Fin d, |x i - 1 / 2| ≤ 2 * r := by
      intro i
      have hlo := hx'.1 i
      have hhi := hx'.2 i
      by_cases hi1 : i = ⟨1, by omega⟩
      · subst i
        simp at hlo hhi
        rw [abs_le]
        constructor <;> nlinarith
      · simp only [hi1, if_false] at hlo hhi
        rw [abs_le]
        constructor <;> linarith
    calc
      (∑ i : Fin d, (x i - 1 / 2) ^ 2) ≤ ∑ _i : Fin d, (2 * r) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [sq_abs] using
          (pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2)
      _ = (d : ℝ) * (2 * r) ^ 2 := by simp
      _ ≤ h ^ 2 := by
        dsimp [r]
        field_simp
        nlinarith

/-- The core box has one transverse side of length `2 r^a` and `d-1`
ordinary sides of length `r`, where `r = h/(4d)`. [For the stated inputs and conditions](hyp:d,hd,a,h,ha,hh), [the asserted conclusion holds](goal). -/
lemma thinStripCoreBox_volume_real (d : ℕ) (hd : 2 ≤ d) (a h : ℝ)
    (ha : 0 ≤ a) (hh : 0 ≤ h) :
    volume.real (thinStripCoreBox d hd a h) =
      (2 * (h / (4 * d)) ^ a) * (h / (4 * d)) ^ (d - 1) := by
  let r : ℝ := h / (4 * d)
  let j : Fin d := ⟨1, by omega⟩
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hprod : (∏ i : Fin d, ENNReal.ofReal (if i = j then 2 * r ^ a else r)) =
      ENNReal.ofReal (2 * r ^ a) * ENNReal.ofReal r ^ (d - 1) := by
    calc
      (∏ i : Fin d, ENNReal.ofReal (if i = j then 2 * r ^ a else r)) =
          ENNReal.ofReal (2 * r ^ a) *
            ∏ i ∈ Finset.univ.erase j, ENNReal.ofReal r := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        simp only [if_pos]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg (Finset.ne_of_mem_erase hi)]
      _ = ENNReal.ofReal (2 * r ^ a) * ENNReal.ofReal r ^ (d - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_fin]
  have hvol : volume (thinStripCoreBox d hd a h) =
      ∏ i : Fin d, ENNReal.ofReal (if i = j then 2 * r ^ a else r) := by
    rw [thinStripCoreBox, Real.volume_Icc_pi]
    congr 1
    ext i
    congr 1
    dsimp [r, j]
    split_ifs <;> ring
  rw [measureReal_def, hvol, hprod, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  all_goals positivity

/-- The strip bump supplies treated mass of the sharp order
`h^a h^(d-1)` on a centered ball. [For the stated inputs and conditions](hyp:d,hd,gamma,a,h,hgamma,ha,hh,hh1), [the asserted conclusion holds](goal). -/
lemma thinStrip_treated_ball_mass_lower (d : ℕ) (hd : 2 ≤ d)
    (gamma a h : ℝ) (hgamma : 1 < gamma) (ha : 1 < a)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    (1 / 4 : ℝ) * ((2 * (h / (4 * d)) ^ a) * (h / (4 * d)) ^ (d - 1)) ≤
      ∫ x in ball2 (fun _ => (1 / 2 : ℝ)) h,
        stripPropensity d hd gamma a x ∂(volume.restrict (cube d)) := by
  let C := thinStripCoreBox d hd a h
  let B := ball2 (fun _ : Fin d => (1 / 2 : ℝ)) h
  let mu := volume.restrict (cube d)
  have hCmeas : MeasurableSet C := by
    dsimp [C, thinStripCoreBox]
    exact measurableSet_Icc
  have hCB := thinStripCoreBox_subset d hd a h ha hh hh1
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hr : 0 < h / (4 * d) := by positivity
  have hr8 : h / (4 * d) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * d)).2
    nlinarith
  have hra : (h / (4 * d)) ^ a ≤ h / (4 * d) := by
    apply Real.rpow_le_self_of_le_one hr.le
    · linarith
    · linarith
  have hCcube : C ⊆ cube d := by
    intro x hx
    rw [cube, Set.mem_pi]
    intro i _hi
    constructor
    · have hlo := hx.1 i
      dsimp [C, thinStripCoreBox] at hlo
      by_cases hi : i = ⟨1, by omega⟩
      · simp [hi] at hlo
        rw [hi]
        linarith
      · simp [hi] at hlo
        linarith
    · have hhi := hx.2 i
      dsimp [C, thinStripCoreBox] at hhi
      by_cases hi : i = ⟨1, by omega⟩
      · simp [hi] at hhi
        rw [hi]
        linarith
      · simp [hi] at hhi
        linarith
  have hmu_fin (S : Set (Fin d → ℝ)) : mu S ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono (Set.subset_univ S))
    dsimp [mu]
    rw [Measure.restrict_apply MeasurableSet.univ]
    apply ne_top_of_le_ne_top _ (measure_mono Set.inter_subset_right)
    have hcube : cube d =
        Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  have heint : IntegrableOn (stripPropensity d hd gamma a) B mu := by
    apply (integrableOn_const (C := (1 : ℝ)) (hs := hmu_fin B)).mono'
    · exact (stripPropensity_measurable d hd gamma a).aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg
        (stripPropensity_mem_Icc d hd gamma a hgamma x).1]
      exact (stripPropensity_mem_Icc d hd gamma a hgamma x).2
  have hconstint : IntegrableOn (fun _ : Fin d → ℝ => (1 / 4 : ℝ)) C mu :=
    integrableOn_const (hs := hmu_fin C)
  calc
    (1 / 4 : ℝ) * ((2 * (h / (4 * d)) ^ a) * (h / (4 * d)) ^ (d - 1)) =
        ∫ _x in C, (1 / 4 : ℝ) ∂mu := by
      rw [setIntegral_const, smul_eq_mul]
      have hrestrict : mu.real C = volume.real C := by
        rw [measureReal_def, Measure.restrict_apply hCmeas,
          Set.inter_eq_left.mpr hCcube, ← measureReal_def]
      rw [hrestrict, show volume.real C =
          (2 * (h / (4 * d)) ^ a) * (h / (4 * d)) ^ (d - 1) by
        exact thinStripCoreBox_volume_real d hd a h (by linarith) hh.le]
      ring
    _ ≤ ∫ x in C, stripPropensity d hd gamma a x ∂mu := by
      apply setIntegral_mono_on hconstint (heint.mono_set (fun x hx => hCB hx |>.2)) hCmeas
      intro x hx
      exact stripPropensity_ge_quarter_on_strip d hd gamma a hgamma x (hCB hx).1
    _ ≤ ∫ x in B, stripPropensity d hd gamma a x ∂mu := by
      apply setIntegral_mono_set heint
      · filter_upwards [] with x
        exact (stripPropensity_mem_Icc d hd gamma a hgamma x).1
      · exact Filter.Eventually.of_forall (fun x hx => hCB hx |>.2)

/-- A centered ball cuts the strip into a box with transverse half-width `h ^ a`. [For the stated inputs and conditions](hyp:d,hd,a,h,ha,hh), [the asserted conclusion holds](goal). -/
lemma thinStrip_ball_volume_le_box (d : ℕ) (hd : 2 ≤ d)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) :
    volume (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) ≤
      ∏ i : Fin d, ENNReal.ofReal
        (if i = ⟨1, by omega⟩ then 2 * h ^ a else 2 * h) := by
  let w : Fin d → ℝ := fun i =>
    if i = ⟨1, by omega⟩ then h ^ a else h
  have hsubset : thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h ⊆
      Set.Icc (fun i => (1 / 2 : ℝ) - w i)
        (fun i => (1 / 2 : ℝ) + w i) := by
    intro x hx
    rw [Set.mem_Icc]
    constructor <;> intro i
    · have hi : |x i - 1 / 2| ≤ w i := by
        by_cases heq : i = ⟨1, by omega⟩
        · subst i
          simpa [w] using thinStrip_ball_transverse_coordinate_bound
            d hd a h ha hh x hx.1 hx.2
        · have hsum : (x i - (1 / 2 : ℝ)) ^ 2 ≤
              ∑ j : Fin d, (x j - 1 / 2) ^ 2 :=
            Finset.single_le_sum
              (fun j _ => sq_nonneg (x j - 1 / 2)) (Finset.mem_univ i)
          have hball : (∑ j : Fin d, (x j - 1 / 2) ^ 2) ≤ h ^ 2 := hx.2
          have : |x i - 1 / 2| ≤ h := by
            nlinarith [sq_abs (x i - (1 / 2 : ℝ)), abs_nonneg (x i - (1 / 2 : ℝ))]
          simpa [w, heq] using this
      dsimp
      linarith [(abs_le.mp hi).1]
    · have hi : |x i - 1 / 2| ≤ w i := by
        by_cases heq : i = ⟨1, by omega⟩
        · subst i
          simpa [w] using thinStrip_ball_transverse_coordinate_bound
            d hd a h ha hh x hx.1 hx.2
        · have hsum : (x i - (1 / 2 : ℝ)) ^ 2 ≤
              ∑ j : Fin d, (x j - 1 / 2) ^ 2 :=
            Finset.single_le_sum
              (fun j _ => sq_nonneg (x j - 1 / 2)) (Finset.mem_univ i)
          have hball : (∑ j : Fin d, (x j - 1 / 2) ^ 2) ≤ h ^ 2 := hx.2
          have : |x i - 1 / 2| ≤ h := by
            nlinarith [sq_abs (x i - (1 / 2 : ℝ)), abs_nonneg (x i - (1 / 2 : ℝ))]
          simpa [w, heq] using this
      dsimp
      linarith [(abs_le.mp hi).2]
  calc
    volume (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) ≤
        volume (Set.Icc (fun i => (1 / 2 : ℝ) - w i)
          (fun i => (1 / 2 : ℝ) + w i)) := measure_mono hsubset
    _ = ∏ i : Fin d, ENNReal.ofReal
          (if i = ⟨1, by omega⟩ then 2 * h ^ a else 2 * h) := by
      rw [Real.volume_Icc_pi]
      congr 1
      ext i
      congr 1
      dsimp [w]
      split_ifs <;> ring

/-- The box estimate has one transverse factor `2 h^a` and `d-1`
ordinary factors `2 h`. [For the stated inputs and conditions](hyp:d,hd,a,h,ha,hh), [the asserted conclusion holds](goal). -/
lemma thinStrip_ball_volume_real_upper (d : ℕ) (hd : 2 ≤ d)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) :
    volume.real (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) ≤
      (2 * h ^ a) * (2 * h) ^ (d - 1) := by
  let j : Fin d := ⟨1, by omega⟩
  have hprod : (∏ i : Fin d, ENNReal.ofReal
      (if i = j then 2 * h ^ a else 2 * h)) =
      ENNReal.ofReal (2 * h ^ a) * ENNReal.ofReal (2 * h) ^ (d - 1) := by
    calc
      (∏ i : Fin d, ENNReal.ofReal (if i = j then 2 * h ^ a else 2 * h)) =
          ENNReal.ofReal (if j = j then 2 * h ^ a else 2 * h) *
            ∏ i ∈ Finset.univ.erase j,
              ENNReal.ofReal (if i = j then 2 * h ^ a else 2 * h) := by
        exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
      _ = ENNReal.ofReal (2 * h ^ a) *
          ∏ _i ∈ Finset.univ.erase j, ENNReal.ofReal (2 * h) := by
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg (Finset.ne_of_mem_erase hi)]
      _ = ENNReal.ofReal (2 * h ^ a) * ENNReal.ofReal (2 * h) ^ (d - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_fin]
  have hvol := thinStrip_ball_volume_le_box d hd a h ha hh
  rw [show (∏ i : Fin d, ENNReal.ofReal
      (if i = ⟨1, by omega⟩ then 2 * h ^ a else 2 * h)) =
      ENNReal.ofReal (2 * h ^ a) * ENNReal.ofReal (2 * h) ^ (d - 1) by
        simpa [j] using hprod] at hvol
  rw [measureReal_def]
  calc
    (volume (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h)).toReal ≤
        (ENNReal.ofReal (2 * h ^ a) * ENNReal.ofReal (2 * h) ^ (d - 1)).toReal := by
      apply ENNReal.toReal_mono
      · finiteness
      · exact hvol
    _ = (2 * h ^ a) * (2 * h) ^ (d - 1) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
      · positivity
      · positivity

/-- The normalized transverse second moment is uniformly small on the strip. [For the stated inputs and conditions](hyp:d,hd,a,h,ha,hh,x,hx,hr), [the asserted conclusion holds](goal). -/
lemma thinStrip_normalized_transverse_square_bound (d : ℕ) (hd : 2 ≤ d)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 < h) (x : Fin d → ℝ)
    (hx : x ∈ thinStrip d hd a) (hr : centreRadius x ≤ h) :
    ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 ≤ (h ^ a / h) ^ 2 := by
  have hwidth := thinStrip_transverse_coordinate_bound d hd a h ha hh.le x hx hr
  have hratio : |(x ⟨1, by omega⟩ - 1 / 2) / h| ≤ h ^ a / h := by
    rw [abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right hwidth hh.le
  simpa only [sq_abs] using
    (pow_le_pow_left₀ (abs_nonneg _) hratio 2)

/-- The radial treatment part contributes its small radius bound; the strip
part contributes only its vanishing transverse width. [For the stated inputs and conditions](hyp:d,hd,γ,a,h,hγ,ha,hh,x,hr), [the asserted conclusion holds](goal). -/
lemma thinStrip_treated_second_integrand_bound (d : ℕ) (hd : 2 ≤ d)
    (γ a h : ℝ) (hγ : 1 < γ) (ha : 0 ≤ a) (hh : 0 < h)
    (x : Fin d → ℝ) (hr : centreRadius x ≤ h) :
    ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd γ a x ≤
      ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) + (h ^ a / h) ^ 2 := by
  classical
  have hrad : 0 ≤ ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) := by positivity
  by_cases hx : x ∈ thinStrip d hd a
  · have hsquare := thinStrip_normalized_transverse_square_bound
      d hd a h ha hh x hx hr
    have he := (stripPropensity_mem_Icc d hd γ a hγ x).2
    have hsq : 0 ≤ ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 := sq_nonneg _
    nlinarith
  · have he := stripPropensity_off_strip_radius_bound d hd γ a h hγ x hx hr
    have hcoord := norm_le_pi_norm
      (x - (fun _ : Fin d => (1 / 2 : ℝ))) ⟨1, by omega⟩
    have habs : |x ⟨1, by omega⟩ - 1 / 2| ≤ h := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs, centreRadius] using hcoord.trans hr
    have hdiv : |(x ⟨1, by omega⟩ - 1 / 2) / h| ≤ 1 := by
      rw [abs_div, abs_of_pos hh]
      exact (div_le_iff₀ hh).2 (by simpa using habs)
    have hsq : ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using
        (pow_le_pow_left₀ (abs_nonneg _) hdiv 2)
    have hnonneg := (stripPropensity_mem_Icc d hd γ a hγ x).1
    nlinarith [sq_nonneg (h ^ a / h)]

/-- Pointwise split retaining the small strip volume for the transverse term. [For the stated inputs and conditions](hyp:d,hd,gamma,a,h,hgamma,ha,hh,x,hr), [the asserted conclusion holds](goal). -/
lemma thinStrip_treated_second_integrand_split_bound (d : ℕ) (hd : 2 ≤ d)
    (gamma a h : ℝ) (hgamma : 1 < gamma) (ha : 0 ≤ a) (hh : 0 < h)
    (x : Fin d → ℝ) (hr : centreRadius x ≤ h) :
    ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd gamma a x ≤
      ((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1)) +
        (thinStrip d hd a).indicator (fun _ => (h ^ a / h) ^ 2) x := by
  classical
  by_cases hx : x ∈ thinStrip d hd a
  · rw [Set.indicator_of_mem hx]
    have hsquare := thinStrip_normalized_transverse_square_bound
      d hd a h ha hh x hx hr
    have he := (stripPropensity_mem_Icc d hd gamma a hgamma x).2
    have hrad : 0 ≤ ((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1)) := by positivity
    have hsq : 0 ≤ ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 := sq_nonneg _
    nlinarith
  · simp only [Set.indicator, hx, if_false, Pi.zero_apply, add_zero]
    have he := stripPropensity_off_strip_radius_bound d hd gamma a h hgamma x hx hr
    have hcoord := norm_le_pi_norm
      (x - (fun _ : Fin d => (1 / 2 : ℝ))) ⟨1, by omega⟩
    have habs : |x ⟨1, by omega⟩ - 1 / 2| ≤ h := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs, centreRadius] using hcoord.trans hr
    have hdiv : |(x ⟨1, by omega⟩ - 1 / 2) / h| ≤ 1 := by
      rw [abs_div, abs_of_pos hh]
      exact (div_le_iff₀ hh).2 (by simpa using habs)
    have hsq : ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using
        (pow_le_pow_left₀ (abs_nonneg _) hdiv 2)
    have hnonneg := (stripPropensity_mem_Icc d hd gamma a hgamma x).1
    calc
      ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd gamma a x ≤
          1 * stripPropensity d hd gamma a x :=
        mul_le_mul_of_nonneg_right hsq hnonneg
      _ = stripPropensity d hd gamma a x := one_mul _
      _ ≤ ((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1)) := he

/-- Integrated numerator split, before inserting the two geometric volume bounds. [For the stated inputs and conditions](hyp:d,hd,gamma,a,h,hgamma,ha,hh), [the asserted conclusion holds](goal). -/
lemma thinStrip_treated_second_setIntegral_split (d : ℕ) (hd : 2 ≤ d)
    (gamma a h : ℝ) (hgamma : 1 < gamma) (ha : 0 ≤ a) (hh : 0 < h) :
    (∫ x in ball2 (fun _ => (1 / 2 : ℝ)) h,
        ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd gamma a x
          ∂(volume.restrict (cube d))) ≤
      ((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1)) *
          (volume.restrict (cube d)).real (ball2 (fun _ => (1 / 2 : ℝ)) h) +
        (h ^ a / h) ^ 2 *
          (volume.restrict (cube d)).real
            (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ thinStrip d hd a) := by
  let B := ball2 (fun _ : Fin d => (1 / 2 : ℝ)) h
  let mu := volume.restrict (cube d)
  let R : ℝ := ((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1))
  let S : ℝ := (h ^ a / h) ^ 2
  have hB : MeasurableSet B := by
    dsimp [B]
    unfold ball2
    exact measurableSet_le (by fun_prop) (by fun_prop)
  have hstrip := thinStrip_measurableSet d hd a
  have hfin : mu B ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono (Set.subset_univ B))
    dsimp [mu]
    rw [Measure.restrict_apply MeasurableSet.univ]
    apply ne_top_of_le_ne_top _ (measure_mono Set.inter_subset_right)
    have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  have hfint : IntegrableOn (fun x : Fin d → ℝ =>
      ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd gamma a x) B mu := by
    apply (integrableOn_const (C := (1 : ℝ)) (hs := hfin)).mono'
    · have hm : Measurable (fun x : Fin d → ℝ =>
          ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2) := by fun_prop
      exact (hm.mul (stripPropensity_measurable d hd gamma a)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hB] with x hx
      have hsum : (x ⟨1, by omega⟩ - (1 / 2 : ℝ)) ^ 2 ≤
          ∑ i : Fin d, (x i - 1 / 2) ^ 2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg (x i - 1 / 2))
          (Finset.mem_univ _)
      have habs : |x ⟨1, by omega⟩ - 1 / 2| ≤ h := by
        dsimp [B, ball2] at hx
        nlinarith [sq_abs (x ⟨1, by omega⟩ - (1 / 2 : ℝ)),
          abs_nonneg (x ⟨1, by omega⟩ - (1 / 2 : ℝ))]
      have hdiv : |(x ⟨1, by omega⟩ - 1 / 2) / h| ≤ 1 := by
        rw [abs_div, abs_of_pos hh]
        exact (div_le_iff₀ hh).2 (by simpa using habs)
      have he := stripPropensity_mem_Icc d hd gamma a hgamma x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) he.1)]
      have hsq : ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using
          (pow_le_pow_left₀ (abs_nonneg _) hdiv 2)
      calc
        ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd gamma a x ≤
            1 * stripPropensity d hd gamma a x :=
          mul_le_mul_of_nonneg_right hsq he.1
        _ ≤ 1 := by simpa using he.2
  have hRint : IntegrableOn (fun _ : Fin d → ℝ => R) B mu :=
    integrableOn_const (hs := hfin)
  have hSint : IntegrableOn
      ((thinStrip d hd a).indicator (fun _ : Fin d → ℝ => S)) B mu :=
    (integrableOn_const (C := S) (hs := hfin)).indicator hstrip
  calc
    (∫ x in B, ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 *
        stripPropensity d hd gamma a x ∂mu) ≤
        ∫ x in B, R + (thinStrip d hd a).indicator (fun _ => S) x ∂mu := by
      apply setIntegral_mono_on hfint (hRint.add hSint) hB
      intro x hx
      have hr : centreRadius x ≤ h := by
        rw [centreRadius, pi_norm_le_iff_of_nonneg hh.le]
        intro i
        have hsum : (x i - (1 / 2 : ℝ)) ^ 2 ≤
            ∑ j : Fin d, (x j - 1 / 2) ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (x j - 1 / 2))
            (Finset.mem_univ _)
        dsimp [B, ball2] at hx
        rw [Pi.sub_apply, Real.norm_eq_abs]
        nlinarith [sq_abs (x i - (1 / 2 : ℝ)), abs_nonneg (x i - (1 / 2 : ℝ))]
      exact thinStrip_treated_second_integrand_split_bound d hd gamma a h
        hgamma ha hh x hr
    _ = R * mu.real B + S * mu.real (B ∩ thinStrip d hd a) := by
      rw [integral_add hRint hSint, setIntegral_const, smul_eq_mul,
        setIntegral_indicator hstrip, setIntegral_const, smul_eq_mul]
      ring

/-- A centered Euclidean ball is contained in its coordinate box. [For the stated inputs and conditions](hyp:d,h,hh), [the asserted conclusion holds](goal). -/
lemma uniformCube_ball_volume_real_upper (d : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    (volume.restrict (cube d)).real (ball2 (fun _ => (1 / 2 : ℝ)) h) ≤
      (2 * h) ^ d := by
  let B := ball2 (fun _ : Fin d => (1 / 2 : ℝ)) h
  let Q := Set.Icc (fun _ : Fin d => (1 / 2 : ℝ) - h) (fun _ => 1 / 2 + h)
  have hBQ : B ⊆ Q := by
    intro x hx
    rw [Set.mem_Icc]
    constructor <;> intro i
    · have hsum : (x i - (1 / 2 : ℝ)) ^ 2 ≤
          ∑ j : Fin d, (x j - 1 / 2) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j - 1 / 2))
          (Finset.mem_univ _)
      dsimp [B, ball2] at hx
      nlinarith [sq_abs (x i - (1 / 2 : ℝ)), abs_nonneg (x i - (1 / 2 : ℝ))]
    · have hsum : (x i - (1 / 2 : ℝ)) ^ 2 ≤
          ∑ j : Fin d, (x j - 1 / 2) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j - 1 / 2))
          (Finset.mem_univ _)
      dsimp [B, ball2] at hx
      nlinarith [sq_abs (x i - (1 / 2 : ℝ)), abs_nonneg (x i - (1 / 2 : ℝ))]
  have hmeasure : (volume.restrict (cube d)) B ≤ volume Q := by
    calc
      (volume.restrict (cube d)) B ≤ volume B :=
        (Measure.restrict_le_self : volume.restrict (cube d) ≤ volume) B
      _ ≤ volume Q := measure_mono hBQ
  have hQ : volume Q = ENNReal.ofReal ((2 * h) ^ d) := by
    dsimp [Q]
    rw [Real.volume_Icc_pi]
    simp only [add_sub_sub_cancel, Finset.prod_const, Finset.card_fin]
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1
    ring
  change ((volume.restrict (cube d)) B).toReal ≤ (2 * h) ^ d
  rw [hQ] at hmeasure
  calc
    ((volume.restrict (cube d)) B).toReal ≤ (ENNReal.ofReal ((2 * h) ^ d)).toReal := by
      apply ENNReal.toReal_mono
      · simp
      · exact hmeasure
    _ = (2 * h) ^ d := ENNReal.toReal_ofReal (by positivity)

/-- The numerator has the two sharp powers needed after division by treated mass. [For the stated inputs and conditions](hyp:d,hd,gamma,a,h,hgamma,ha,hh), [the asserted conclusion holds](goal). -/
lemma thinStrip_treated_second_setIntegral_power_bound (d : ℕ) (hd : 2 ≤ d)
    (gamma a h : ℝ) (hgamma : 1 < gamma) (ha : 0 ≤ a) (hh : 0 < h) :
    (∫ x in ball2 (fun _ => (1 / 2 : ℝ)) h,
        ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd gamma a x
          ∂(volume.restrict (cube d))) ≤
      ((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1)) * (2 * h) ^ d +
        (h ^ a / h) ^ 2 * ((2 * h ^ a) * (2 * h) ^ (d - 1)) := by
  have hsplit := thinStrip_treated_second_setIntegral_split d hd gamma a h
    hgamma ha hh
  have hball := uniformCube_ball_volume_real_upper d h hh.le
  have hstrip : (volume.restrict (cube d)).real
      (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ thinStrip d hd a) ≤
      (2 * h ^ a) * (2 * h) ^ (d - 1) := by
    rw [Set.inter_comm]
    have hvolfin : volume
        (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) ≠ ⊤ := by
      apply ne_top_of_le_ne_top _
        (thinStrip_ball_volume_le_box d hd a h ha hh.le)
      apply ENNReal.prod_ne_top
      intro i hi
      exact ENNReal.ofReal_ne_top
    calc
      (volume.restrict (cube d)).real
          (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) ≤
          volume.real (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) := by
        rw [measureReal_def, measureReal_def]
        apply ENNReal.toReal_mono
        · exact hvolfin
        · exact (Measure.restrict_le_self :
            volume.restrict (cube d) ≤ volume) _
      _ ≤ (2 * h ^ a) * (2 * h) ^ (d - 1) :=
        thinStrip_ball_volume_real_upper d hd a h ha hh.le
  have hR : 0 ≤ ((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1)) := by positivity
  have hS : 0 ≤ (h ^ a / h) ^ 2 := sq_nonneg _
  calc
    _ ≤ ((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1)) *
          (volume.restrict (cube d)).real (ball2 (fun _ => (1 / 2 : ℝ)) h) +
        (h ^ a / h) ^ 2 * (volume.restrict (cube d)).real
          (ball2 (fun _ => (1 / 2 : ℝ)) h ∩ thinStrip d hd a) := hsplit
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hball hR)
      (mul_le_mul_of_nonneg_left hstrip hS)

/-- The deterministic strip contribution to the normalized second moment vanishes. [For the stated inputs and conditions](hyp:a,ha), [the asserted conclusion holds](goal). -/
lemma thinStrip_normalized_transverse_square_tendsto_zero (a : ℝ) (ha : 1 < a) :
    Filter.Tendsto (fun h : ℝ => (h ^ a / h) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hexp : 0 < a - 1 := by linarith
  have hpow : Filter.Tendsto (fun h : ℝ => h ^ (a - 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hid : Filter.Tendsto (fun h : ℝ => h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    convert hid.rpow_const (Or.inr hexp.le) using 1
    rw [Real.zero_rpow (ne_of_gt hexp)]
  have hsq := hpow.pow 2
  have heq : (fun h : ℝ => (h ^ a / h) ^ 2) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun h : ℝ => (h ^ (a - 1)) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa only [Set.mem_Ioi] using congrArg (fun z : ℝ => z ^ 2)
      (Real.rpow_sub_one (ne_of_gt hh) a).symm
  simpa using hsq.congr' heq.symm

/-- The pointwise envelope for the normalized treated second moment vanishes. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ,ha), [the asserted conclusion holds](goal). -/
lemma thinStrip_second_integrand_envelope_tendsto_zero
    (d : ℕ) (hd : 2 ≤ d) (γ a : ℝ) (hγ : 1 < γ) (ha : 1 < a) :
    Filter.Tendsto
      (fun h : ℝ =>
        ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) + (h ^ a / h) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa using (stripRadialBound_tendsto_zero d hd γ hγ).add
    (thinStrip_normalized_transverse_square_tendsto_zero a ha)

/-- A closed cube of radius `r` around the design centre has volume `(2*r)^d`. [For the stated inputs and conditions](hyp:d,r,hr), [the asserted conclusion holds](goal). -/
lemma centreCube_volume (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    volume (Set.Icc (fun _ : Fin d => (1 / 2 : ℝ) - r)
      (fun _ => (1 / 2 : ℝ) + r)) = ENNReal.ofReal ((2 * r) ^ d) := by
  rw [Real.volume_Icc_pi]
  simp only [add_sub_sub_cancel, Finset.prod_const, Finset.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity)]
  congr 1
  ring

/-- A coordinate box of half-width `h / d` gives a quantitative lower bound
for the uniform-cube mass of a centered Euclidean ball. [For the stated inputs and conditions](hyp:d,hd,h,hh,hhhalf), [the asserted conclusion holds](goal). -/
lemma uniformCube_centered_ball_mass_lower (d : ℕ) (hd : 1 ≤ d)
    (h : ℝ) (hh : 0 < h) (hhhalf : h ≤ 1 / 2) :
    (2 * (h / d)) ^ d ≤
      (volume.restrict (cube d)).real
        (ball2 (fun _ => (1 / 2 : ℝ)) h) := by
  let r : ℝ := h / d
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdR
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrhalf : r ≤ 1 / 2 := by
    calc
      r ≤ h := by
        dsimp [r]
        exact (div_le_iff₀ hdpos).2 (by nlinarith)
      _ ≤ 1 / 2 := hhhalf
  let Q : Set (Fin d → ℝ) :=
    Set.Icc (fun _ => (1 / 2 : ℝ) - r) (fun _ => (1 / 2 : ℝ) + r)
  have hQ : Q ⊆ ball2 (fun _ => (1 / 2 : ℝ)) h ∩ cube d := by
    intro x hx
    have hx' : (fun _ : Fin d => (1 / 2 : ℝ) - r) ≤ x ∧
        x ≤ (fun _ : Fin d => (1 / 2 : ℝ) + r) := hx
    constructor
    · change (∑ i : Fin d, (x i - 1 / 2) ^ 2) ≤ h ^ 2
      calc
        (∑ i : Fin d, (x i - 1 / 2) ^ 2) ≤ ∑ _i : Fin d, r ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hlo := hx'.1 i
          have hhi := hx'.2 i
          have habs : |x i - 1 / 2| ≤ r := by
            rw [abs_le]
            constructor <;> dsimp at hlo hhi ⊢ <;> linarith
          simpa only [sq_abs] using
            (pow_le_pow_left₀ (abs_nonneg _) habs 2)
        _ = (d : ℝ) * r ^ 2 := by simp
        _ ≤ h ^ 2 := by
          dsimp [r]
          rw [div_pow]
          field_simp
          nlinarith [hdR]
    · simp only [cube]
      intro i hi
      simp only [Set.mem_Icc]
      constructor
      · have hlo := hx'.1 i
        dsimp at hlo
        linarith
      · have hhi := hx'.2 i
        dsimp at hhi
        linarith
  have hball : MeasurableSet (ball2 (fun _ : Fin d => (1 / 2 : ℝ)) h) := by
    unfold ball2
    exact measurableSet_le (by fun_prop) (by fun_prop)
  rw [measureReal_restrict_apply hball]
  have hcubevol : volume (cube d) = 1 := by
    have hcube : cube d =
        Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  have hcubeFin : volume (cube d) ≠ ⊤ := by
    rw [hcubevol]
    exact ENNReal.one_ne_top
  have hfin : volume (ball2 (fun _ : Fin d => (1 / 2 : ℝ)) h ∩ cube d) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hcubeFin (measure_mono Set.inter_subset_right)
  have hmono : volume.real Q ≤
      volume.real (ball2 (fun _ : Fin d => (1 / 2 : ℝ)) h ∩ cube d) :=
    measureReal_mono (h₂ := hfin) hQ
  have hQvol : volume.real Q = (2 * r) ^ d := by
    rw [measureReal_def]
    rw [show volume Q = ENNReal.ofReal ((2 * r) ^ d) by
      exact centreCube_volume d r hr]
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [hQvol] at hmono
  simpa [r] using hmono

/-- Under uniform cube volume, the strip occupies at most a constant times
`h^(a-1)` of a sufficiently small centered ball. [For the stated inputs and conditions](hyp:d,hd,a,h,ha,hh,hhhalf), [the asserted conclusion holds](goal). -/
lemma uniformCube_thinStrip_local_ratio_bound (d : ℕ) (hd : 2 ≤ d)
    (a h : ℝ) (ha : 1 < a) (hh : 0 < h) (hhhalf : h ≤ 1 / 2) :
    (volume.restrict (cube d)).real
        (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) /
      (volume.restrict (cube d)).real
        (ball2 (fun _ => (1 / 2 : ℝ)) h) ≤
      (d : ℝ) ^ d * h ^ (a - 1) := by
  let S := thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h
  have hS : MeasurableSet S := by
    apply (thinStrip_measurableSet d hd a).inter
    unfold ball2
    exact measurableSet_le (by fun_prop) (by fun_prop)
  have hnum : (volume.restrict (cube d)).real S ≤
      (2 * h ^ a) * (2 * h) ^ (d - 1) := by
    rw [measureReal_restrict_apply hS]
    have hraw := thinStrip_ball_volume_le_box d hd a h
      (le_trans zero_le_one ha.le) hh.le
    have hSfin : volume S ≠ ⊤ := by
      have htop : (∏ i : Fin d, ENNReal.ofReal
          (if i = ⟨1, by omega⟩ then 2 * h ^ a else 2 * h)) < ⊤ := by
        classical
        induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            rw [Finset.prod_insert hi]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ih
      exact ne_top_of_le_ne_top (ne_of_lt htop) hraw
    exact (measureReal_mono (h₂ := hSfin) Set.inter_subset_left).trans
      (thinStrip_ball_volume_real_upper d hd a h
        (le_trans zero_le_one ha.le) hh.le)
  have hden := uniformCube_centered_ball_mass_lower d (by omega) h hh hhhalf
  have hbasepos : 0 < (2 * (h / d)) ^ d := by positivity
  calc
    (volume.restrict (cube d)).real S /
          (volume.restrict (cube d)).real
            (ball2 (fun _ => (1 / 2 : ℝ)) h) ≤
        ((2 * h ^ a) * (2 * h) ^ (d - 1)) /
          (volume.restrict (cube d)).real
            (ball2 (fun _ => (1 / 2 : ℝ)) h) :=
      div_le_div_of_nonneg_right hnum (measureReal_nonneg)
    _ ≤ ((2 * h ^ a) * (2 * h) ^ (d - 1)) /
          (2 * (h / d)) ^ d :=
      div_le_div_of_nonneg_left (by positivity) hbasepos hden
    _ = (d : ℝ) ^ d * h ^ (a - 1) := by
      have hdpos : (0 : ℝ) < d := by positivity
      have hhne : h ≠ 0 := ne_of_gt hh
      have hpow : (2 * h) ^ d = (2 * h) ^ (d - 1) * (2 * h) := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
      have hdeneq : 2 * (h / (d : ℝ)) = (2 * h) / (d : ℝ) := by ring
      rw [hdeneq, div_pow, div_div_eq_mul_div,
        div_eq_iff (pow_ne_zero d (mul_ne_zero (by norm_num) hhne))]
      rw [Real.rpow_sub_one hhne]
      field_simp
      rw [hpow]
      ring

/-- The transverse exponent `a > 1` makes the strip's fraction of centered
balls vanish under uniform cube volume. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ,ha), [the asserted conclusion holds](goal). -/
lemma uniformCube_thinStrip_local_ratio (d : ℕ) (hd : 2 ≤ d)
    (γ a : ℝ) (hγ : 1 < γ) (ha : 1 < a) :
    ∀ (ρ ν h₀ : ℝ), 0 < ρ → 0 < ν → 0 < h₀ →
      ∃ h : ℝ, 0 < h ∧ h ≤ h₀ ∧
        ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) < ρ / 4 ∧
        0 < (volume.restrict (cube d)).real
          (ball2 (fun _ => (1 / 2 : ℝ)) h) ∧
        (volume.restrict (cube d)).real
          (thinStrip d hd a ∩ ball2 (fun _ => (1 / 2 : ℝ)) h) /
          (volume.restrict (cube d)).real
            (ball2 (fun _ => (1 / 2 : ℝ)) h) ≤ ν := by
  intro ρ ν h₀ hρ hν hh₀
  have hid : Filter.Tendsto (fun h : ℝ => h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hpow : Filter.Tendsto (fun h : ℝ => h ^ (a - 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    convert hid.rpow_const (Or.inr (by linarith : 0 ≤ a - 1)) using 1
    rw [Real.zero_rpow (by linarith : a - 1 ≠ 0)]
  have hratioLim : Filter.Tendsto (fun h : ℝ => (d : ℝ) ^ d * h ^ (a - 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow)
  have hratio : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (d : ℝ) ^ d * h ^ (a - 1) < ν :=
    hratioLim.eventually (eventually_lt_nhds hν)
  have hrad : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) < ρ / 4 :=
    (stripRadialBound_tendsto_zero d hd γ hγ).eventually
      (eventually_lt_nhds (by positivity))
  have hwidth : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), h < min h₀ (1 / 2) :=
    hid.eventually (eventually_lt_nhds (lt_min hh₀ (by norm_num)))
  have hpos : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < h :=
    self_mem_nhdsWithin
  obtain ⟨h, hh, hsmall, hrad', hratio'⟩ :=
    (hpos.and (hwidth.and (hrad.and hratio))).exists
  have hsmall' : h < h₀ ∧ h < 1 / 2 := (lt_min_iff.mp hsmall)
  have hhhalf : h ≤ 1 / 2 := hsmall'.2.le
  have hden := uniformCube_centered_ball_mass_lower d (by omega) h hh hhhalf
  have hball : 0 < (volume.restrict (cube d)).real
      (ball2 (fun _ => (1 / 2 : ℝ)) h) :=
    lt_of_lt_of_le (by positivity : 0 < (2 * (h / d)) ^ d) hden
  refine ⟨h, hh, hsmall'.1.le, hrad', hball, ?_⟩
  exact (uniformCube_thinStrip_local_ratio_bound d hd a h ha hh hhhalf).trans
    hratio'.le

/-- The sup-norm radius sublevel set is the centred coordinate cube. [For the stated inputs and conditions](hyp:d,r,hr), [the asserted conclusion holds](goal). -/
lemma centreRadius_sublevel_eq_cube (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    {x : Fin d → ℝ | centreRadius x ≤ r} =
      Set.Icc (fun _ => (1 / 2 : ℝ) - r) (fun _ => (1 / 2 : ℝ) + r) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def]
  constructor
  · intro hx
    constructor <;> intro i
    · have hi := (norm_le_pi_norm (x - fun _ : Fin d => (1 / 2 : ℝ)) i).trans hx
      change |x i - 1 / 2| ≤ r at hi
      have := (abs_le.mp hi).1
      linarith
    · have hi := (norm_le_pi_norm (x - fun _ : Fin d => (1 / 2 : ℝ)) i).trans hx
      change |x i - 1 / 2| ≤ r at hi
      have := (abs_le.mp hi).2
      linarith
  · rintro ⟨hlo, hhi⟩
    unfold centreRadius
    apply (pi_norm_le_iff_of_nonneg hr).2
    intro i
    change |x i - 1 / 2| ≤ r
    apply abs_le.mpr
    constructor <;> linarith [hlo i, hhi i]

/-- The centred radial CDF has the stated elementary volume formula. [For the stated inputs and conditions](hyp:d,r,hr), [the asserted conclusion holds](goal). -/
lemma centreRadius_sublevel_volume (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    volume {x : Fin d → ℝ | centreRadius x ≤ r} =
      ENNReal.ofReal ((2 * r) ^ d) := by
  rw [centreRadius_sublevel_eq_cube d r hr, centreCube_volume d r hr]

/-- The thin strip inside a sup-norm ball has one side of width `2 h^a`
and `d-1` sides of width `2 h`. [For the stated inputs and conditions](hyp:d,hd,a,h,ha,hh), [the asserted conclusion holds](goal). -/
lemma thinStrip_centreRadius_volume_real_upper (d : ℕ) (hd : 2 ≤ d)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) :
    volume.real (thinStrip d hd a ∩ {x | centreRadius x ≤ h}) ≤
      (2 * h ^ a) * (2 * h) ^ (d - 1) := by
  let j : Fin d := ⟨1, by omega⟩
  let w : Fin d → ℝ := fun i => if i = j then h ^ a else h
  have hsubset : thinStrip d hd a ∩ {x | centreRadius x ≤ h} ⊆
      Set.Icc (fun i => (1 / 2 : ℝ) - w i)
        (fun i => (1 / 2 : ℝ) + w i) := by
    intro x hx
    rw [Set.mem_Icc]
    constructor <;> intro i
    · have hi : |x i - 1 / 2| ≤ w i := by
        by_cases heq : i = j
        · subst i
          simpa [w, j] using thinStrip_transverse_coordinate_bound
            d hd a h ha hh x hx.1 hx.2
        · have hi := (norm_le_pi_norm
              (x - fun _ : Fin d => (1 / 2 : ℝ)) i).trans hx.2
          simpa [w, heq, centreRadius, Pi.sub_apply, Real.norm_eq_abs] using hi
      linarith [(abs_le.mp hi).1]
    · have hi : |x i - 1 / 2| ≤ w i := by
        by_cases heq : i = j
        · subst i
          simpa [w, j] using thinStrip_transverse_coordinate_bound
            d hd a h ha hh x hx.1 hx.2
        · have hi := (norm_le_pi_norm
              (x - fun _ : Fin d => (1 / 2 : ℝ)) i).trans hx.2
          simpa [w, heq, centreRadius, Pi.sub_apply, Real.norm_eq_abs] using hi
      linarith [(abs_le.mp hi).2]
  have hvol : volume (thinStrip d hd a ∩ {x | centreRadius x ≤ h}) ≤
      ∏ i : Fin d, ENNReal.ofReal (if i = j then 2 * h ^ a else 2 * h) := by
    calc
      volume (thinStrip d hd a ∩ {x | centreRadius x ≤ h}) ≤
          volume (Set.Icc (fun i => (1 / 2 : ℝ) - w i)
            (fun i => (1 / 2 : ℝ) + w i)) := measure_mono hsubset
      _ = ∏ i : Fin d, ENNReal.ofReal
          (if i = j then 2 * h ^ a else 2 * h) := by
        rw [Real.volume_Icc_pi]
        congr 1
        ext i
        congr 1
        dsimp [w]
        split_ifs <;> ring
  have hprod : (∏ i : Fin d, ENNReal.ofReal
      (if i = j then 2 * h ^ a else 2 * h)) =
      ENNReal.ofReal (2 * h ^ a) * ENNReal.ofReal (2 * h) ^ (d - 1) := by
    calc
      (∏ i : Fin d, ENNReal.ofReal (if i = j then 2 * h ^ a else 2 * h)) =
          ENNReal.ofReal (2 * h ^ a) *
            ∏ i ∈ Finset.univ.erase j, ENNReal.ofReal (2 * h) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        simp only [if_pos]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg (Finset.ne_of_mem_erase hi)]
      _ = ENNReal.ofReal (2 * h ^ a) * ENNReal.ofReal (2 * h) ^ (d - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_fin]
  rw [hprod] at hvol
  rw [measureReal_def]
  calc
    (volume (thinStrip d hd a ∩ {x | centreRadius x ≤ h})).toReal ≤
        (ENNReal.ofReal (2 * h ^ a) * ENNReal.ofReal (2 * h) ^ (d - 1)).toReal := by
      apply ENNReal.toReal_mono
      · finiteness
      · exact hvol
    _ = (2 * h ^ a) * (2 * h) ^ (d - 1) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
      · positivity
      · positivity

/-- The integrated pointwise split on the sup-norm event used by
`stripSecondMoment`. [For the stated inputs and conditions](hyp:d,hd,gamma,a,h,hgamma,ha,hh), [the asserted conclusion holds](goal). -/
lemma thinStrip_treated_second_sup_setIntegral_split (d : ℕ) (hd : 2 ≤ d)
    (gamma a h : ℝ) (hgamma : 1 < gamma) (ha : 0 ≤ a) (hh : 0 < h) :
    (∫ x in {x : Fin d → ℝ | centreRadius x ≤ h},
        ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd gamma a x
          ∂(volume.restrict (cube d))) ≤
      ((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1)) *
          (volume.restrict (cube d)).real {x : Fin d → ℝ | centreRadius x ≤ h} +
        (h ^ a / h) ^ 2 * (volume.restrict (cube d)).real
          ({x : Fin d → ℝ | centreRadius x ≤ h} ∩ thinStrip d hd a) := by
  let D : Set (Fin d → ℝ) := {x | centreRadius x ≤ h}
  let mu := volume.restrict (cube d)
  let R : ℝ := ((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1))
  let S : ℝ := (h ^ a / h) ^ 2
  have hD : MeasurableSet D := measurableSet_le
    (by unfold centreRadius; fun_prop) measurable_const
  have hfin : mu D ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono (Set.subset_univ D))
    dsimp [mu]
    rw [Measure.restrict_apply MeasurableSet.univ]
    apply ne_top_of_le_ne_top _ (measure_mono Set.inter_subset_right)
    have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  have hfint : IntegrableOn (fun x : Fin d → ℝ =>
      ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd gamma a x) D mu := by
    apply (integrableOn_const (C := (1 : ℝ)) (hs := hfin)).mono'
    · have hm : Measurable (fun x : Fin d → ℝ =>
          ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2) := by fun_prop
      exact (hm.mul (stripPropensity_measurable d hd gamma a)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hD] with x hx
      have hcoord := (norm_le_pi_norm
        (x - fun _ : Fin d => (1 / 2 : ℝ)) ⟨1, by omega⟩).trans hx
      have habs : |x ⟨1, by omega⟩ - 1 / 2| ≤ h := by
        simpa [centreRadius, Pi.sub_apply, Real.norm_eq_abs] using hcoord
      have hdiv : |(x ⟨1, by omega⟩ - 1 / 2) / h| ≤ 1 := by
        rw [abs_div, abs_of_pos hh]
        exact (div_le_iff₀ hh).2 (by simpa using habs)
      have hsq : ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using
          (pow_le_pow_left₀ (abs_nonneg _) hdiv 2)
      have he := stripPropensity_mem_Icc d hd gamma a hgamma x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) he.1)]
      calc
        _ ≤ 1 * stripPropensity d hd gamma a x :=
          mul_le_mul_of_nonneg_right hsq he.1
        _ ≤ 1 := by simpa using he.2
  have hRint : IntegrableOn (fun _ : Fin d → ℝ => R) D mu :=
    integrableOn_const (hs := hfin)
  have hstrip := thinStrip_measurableSet d hd a
  have hSint : IntegrableOn
      ((thinStrip d hd a).indicator (fun _ : Fin d → ℝ => S)) D mu :=
    (integrableOn_const (C := S) (hs := hfin)).indicator hstrip
  calc
    (∫ x in D, ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 *
        stripPropensity d hd gamma a x ∂mu) ≤
        ∫ x in D, R + (thinStrip d hd a).indicator (fun _ => S) x ∂mu := by
      apply setIntegral_mono_on hfint (hRint.add hSint) hD
      intro x hx
      exact thinStrip_treated_second_integrand_split_bound d hd gamma a h
        hgamma ha hh x hx
    _ = R * mu.real D + S * mu.real (D ∩ thinStrip d hd a) := by
      rw [integral_add hRint hSint, setIntegral_const, smul_eq_mul,
        setIntegral_indicator hstrip, setIntegral_const, smul_eq_mul]
      ring

/-- Quantitative numerator bound on the actual sup-norm event. [For the stated inputs and conditions](hyp:d,hd,gamma,a,h,hgamma,ha,hh,hhhalf), [the asserted conclusion holds](goal). -/
lemma thinStrip_treated_second_sup_power_bound (d : ℕ) (hd : 2 ≤ d)
    (gamma a h : ℝ) (hgamma : 1 < gamma) (ha : 0 ≤ a)
    (hh : 0 < h) (hhhalf : h ≤ 1 / 2) :
    (∫ x in {x : Fin d → ℝ | centreRadius x ≤ h},
        ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd gamma a x
          ∂(volume.restrict (cube d))) ≤
      ((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1)) * (2 * h) ^ d +
        (h ^ a / h) ^ 2 * ((2 * h ^ a) * (2 * h) ^ (d - 1)) := by
  have hs := thinStrip_treated_second_sup_setIntegral_split d hd gamma a h
    hgamma ha hh
  have hmass : (volume.restrict (cube d)).real
      {x : Fin d → ℝ | centreRadius x ≤ h} = (2 * h) ^ d := by
    have hD : MeasurableSet {x : Fin d → ℝ | centreRadius x ≤ h} :=
      measurableSet_le (by unfold centreRadius; fun_prop) measurable_const
    have hsub : {x : Fin d → ℝ | centreRadius x ≤ h} ⊆ cube d := by
      rw [centreRadius_sublevel_eq_cube d h hh.le]
      intro x hx
      simp only [Set.mem_Icc, Pi.le_def] at hx
      simp only [cube, Set.mem_univ_pi, Set.mem_Icc]
      intro i
      constructor <;> linarith [(hx.1 i), (hx.2 i)]
    rw [measureReal_def, Measure.restrict_apply hD,
      Set.inter_eq_self_of_subset_left hsub,
      centreRadius_sublevel_volume d h hh.le, ENNReal.toReal_ofReal]
    positivity
  have hstrip : (volume.restrict (cube d)).real
      ({x : Fin d → ℝ | centreRadius x ≤ h} ∩ thinStrip d hd a) ≤
      (2 * h ^ a) * (2 * h) ^ (d - 1) := by
    rw [Set.inter_comm]
    calc
      (volume.restrict (cube d)).real
          (thinStrip d hd a ∩ {x : Fin d → ℝ | centreRadius x ≤ h}) ≤
          volume.real (thinStrip d hd a ∩ {x : Fin d → ℝ | centreRadius x ≤ h}) := by
        rw [measureReal_def, measureReal_def]
        apply ENNReal.toReal_mono
        · apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          rw [← centreRadius_sublevel_volume d h hh.le]
          exact measure_mono Set.inter_subset_right
        · exact (Measure.restrict_le_self : volume.restrict (cube d) ≤ volume) _
      _ ≤ _ := thinStrip_centreRadius_volume_real_upper d hd a h ha hh.le
  rw [hmass] at hs
  exact hs.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hstrip (sq_nonneg _)) _)

/-- The core-box treated-mass lower bound transfers to the sup-norm event. [For the stated inputs and conditions](hyp:d,hd,gamma,a,h,hgamma,ha,hh,hh1), [the asserted conclusion holds](goal). -/
lemma thinStrip_treated_sup_mass_lower (d : ℕ) (hd : 2 ≤ d)
    (gamma a h : ℝ) (hgamma : 1 < gamma) (ha : 1 < a)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    (1 / 4 : ℝ) * ((2 * (h / (4 * d)) ^ a) * (h / (4 * d)) ^ (d - 1)) ≤
      ∫ x in {x : Fin d → ℝ | centreRadius x ≤ h},
        stripPropensity d hd gamma a x ∂(volume.restrict (cube d)) := by
  have hlower := thinStrip_treated_ball_mass_lower d hd gamma a h
    hgamma ha hh hh1
  let D : Set (Fin d → ℝ) := {x | centreRadius x ≤ h}
  let B := ball2 (fun _ : Fin d => (1 / 2 : ℝ)) h
  let mu := volume.restrict (cube d)
  have hD : MeasurableSet D := measurableSet_le
    (by unfold centreRadius; fun_prop) measurable_const
  have hfin : mu D ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono (Set.subset_univ D))
    dsimp [mu]
    rw [Measure.restrict_apply MeasurableSet.univ]
    apply ne_top_of_le_ne_top _ (measure_mono Set.inter_subset_right)
    have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  have heint : IntegrableOn (stripPropensity d hd gamma a) D mu := by
    apply (integrableOn_const (C := (1 : ℝ)) (hs := hfin)).mono'
    · exact (stripPropensity_measurable d hd gamma a).aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg
        (stripPropensity_mem_Icc d hd gamma a hgamma x).1]
      exact (stripPropensity_mem_Icc d hd gamma a hgamma x).2
  have hBD : B ⊆ D := by
    intro x hx
    rw [show x ∈ D ↔ centreRadius x ≤ h by rfl]
    rw [centreRadius, pi_norm_le_iff_of_nonneg hh.le]
    intro i
    have hsum : (x i - (1 / 2 : ℝ)) ^ 2 ≤
        ∑ j : Fin d, (x j - 1 / 2) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j - 1 / 2))
        (Finset.mem_univ _)
    dsimp [B, ball2] at hx
    rw [Pi.sub_apply, Real.norm_eq_abs]
    nlinarith [sq_abs (x i - (1 / 2 : ℝ)), abs_nonneg (x i - (1 / 2 : ℝ))]
  exact hlower.trans (setIntegral_mono_set heint
    (Filter.Eventually.of_forall (fun x =>
      (stripPropensity_mem_Icc d hd gamma a hgamma x).1))
    (Filter.Eventually.of_forall (fun x hx => hBD hx)))

/-- A centred radius at most one half stays in the covariate cube. [For the stated inputs and conditions](hyp:d,r,hr,hrhalf), [the asserted conclusion holds](goal). -/
lemma centreRadius_sublevel_subset_cube (d : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    {x : Fin d → ℝ | centreRadius x ≤ r} ⊆ cube d := by
  rw [centreRadius_sublevel_eq_cube d r hr]
  intro x hx
  simp only [Set.mem_Icc, Pi.le_def] at hx
  simp only [cube, Set.mem_univ_pi, Set.mem_Icc]
  intro i
  constructor <;> linarith [(hx.1 i), (hx.2 i)]

/-- The uniform design assigns the centred radius sublevel its cube volume. [For the stated inputs and conditions](hyp:d,r,hr,hrhalf), [the asserted conclusion holds](goal). -/
lemma centreRadius_uniform_sublevel_mass (d : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    (volume.restrict (cube d)) {x : Fin d → ℝ | centreRadius x ≤ r} =
      ENNReal.ofReal ((2 * r) ^ d) := by
  have hsub := centreRadius_sublevel_subset_cube d r hr hrhalf
  have hmeas : MeasurableSet {x : Fin d → ℝ | centreRadius x ≤ r} :=
    measurableSet_le (by unfold centreRadius; fun_prop) measurable_const
  rw [Measure.restrict_apply hmeas, Set.inter_eq_self_of_subset_left hsub]
  exact centreRadius_sublevel_volume d r hr

/-- On the support of the uniform cube design, the radial CDF has its
unsaturated polynomial form. [For the stated inputs and conditions](hyp:d,r,hr,hrhalf), [the asserted conclusion holds](goal). -/
lemma centreRadiusCDF_of_le_half (d : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    centreRadiusCDF d r = (2 * r) ^ d := by
  unfold centreRadiusCDF
  apply min_eq_right
  have htwo : 0 ≤ 2 * r := by positivity
  have hone : 2 * r ≤ 1 := by linarith
  exact pow_le_one₀ htwo hone

/-- The radius CDF evaluated at an interior radius has precisely its stated
probability under the uniform covariate design. [For the stated inputs and conditions](hyp:d,r,hr,hrhalf), [the asserted conclusion holds](goal). -/
lemma centreRadiusCDF_uniform_sublevel_mass (d : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    (volume.restrict (cube d)) {x : Fin d → ℝ | centreRadius x ≤ r} =
      ENNReal.ofReal (centreRadiusCDF d r) := by
  rw [centreRadiusCDF_of_le_half d r hr hrhalf]
  exact centreRadius_uniform_sublevel_mass d r hr hrhalf

/-- The centre-radius CDF is uniform under the cube design, in the sublevel
form needed for the thin-strip global tail argument. [For the stated inputs and conditions](hyp:d,hd,u,hu), [the asserted conclusion holds](goal). -/
lemma centreRadiusCDF_uniform_distribution_bound (d : ℕ) (hd : 0 < d)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (volume.restrict (cube d)).real
      {x | centreRadiusCDF d (centreRadius x) ≤ u} ≤ u := by
  have hvol : volume (cube d) = 1 := by
    have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  have : IsFiniteMeasure (volume.restrict (cube d)) := by
    rw [isFiniteMeasure_restrict]
    simp [hvol]
  by_cases hu1 : u = 1
  · subst u
    have hprob : (volume.restrict (cube d)).real Set.univ = 1 := by
      simp [measureReal_def, hvol]
    calc
      _ ≤ (volume.restrict (cube d)).real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := hprob
  · have hult : u < 1 := lt_of_le_of_ne hu.2 hu1
    let r : ℝ := u ^ ((d : ℝ)⁻¹) / 2
    have hdne : d ≠ 0 := by omega
    have hrpow : (2 * r) ^ d = u := by
      dsimp [r]
      have heq : 2 * (u ^ ((d : ℝ)⁻¹) / 2) = u ^ ((d : ℝ)⁻¹) := by ring
      rw [heq]
      exact Real.rpow_inv_natCast_pow hu.1 hdne
    have hr : 0 ≤ r := by
      dsimp [r]
      exact div_nonneg (Real.rpow_nonneg hu.1 _) (by norm_num)
    have hrhalf : r ≤ 1 / 2 := by
      dsimp [r]
      have hpow : u ^ ((d : ℝ)⁻¹) ≤ 1 :=
        Real.rpow_le_one hu.1 hu.2 (by positivity)
      linarith
    have hsub : {x : Fin d → ℝ | centreRadiusCDF d (centreRadius x) ≤ u} ⊆
        {x : Fin d → ℝ | centreRadius x ≤ r} := by
      intro x hx
      have hrad : 0 ≤ centreRadius x := norm_nonneg _
      have hpow : (2 * centreRadius x) ^ d ≤ u := by
        change min 1 ((2 * centreRadius x) ^ d) ≤ u at hx
        by_cases hle : (2 * centreRadius x) ^ d ≤ 1
        · rw [min_eq_right hle] at hx
          exact hx
        · have hmin : min 1 ((2 * centreRadius x) ^ d) = 1 :=
            min_eq_left (le_of_not_ge hle)
          rw [hmin] at hx
          linarith
      have hle : 2 * centreRadius x ≤ 2 * r :=
        le_of_pow_le_pow_left₀ hdne (by positivity) (by simpa only [hrpow] using hpow)
      change centreRadius x ≤ r
      linarith
    calc
      _ ≤ (volume.restrict (cube d)).real {x | centreRadius x ≤ r} :=
        measureReal_mono hsub
      _ = u := by
        rw [measureReal_def, centreRadius_uniform_sublevel_mass d r hr hrhalf]
        rw [ENNReal.toReal_ofReal (by positivity)]
        exact hrpow

/-- The displayed thin-strip propensity obeys the sharp global tail bound
under the uniform covariate design. [For the stated inputs and conditions](hyp:d,hd,γ,a,t,hγ,ht), [the asserted conclusion holds](goal). -/
lemma stripPropensity_uniform_tail_bound (d : ℕ) (hd : 2 ≤ d)
    (γ a t : ℝ) (hγ : 1 < γ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (volume.restrict (cube d)).real
      {x | stripPropensity d hd γ a x ≤ t} ≤ t ^ (γ - 1) := by
  have hvol : volume (cube d) = 1 := by
    have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  have : IsFiniteMeasure (volume.restrict (cube d)) := by
    rw [isFiniteMeasure_restrict]
    simp [hvol]
  have hpow : t ^ (γ - 1) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨Real.rpow_nonneg ht.1 _, ?_⟩
    exact Real.rpow_le_one ht.1 ht.2 (by linarith)
  exact (measureReal_mono (stripTail_subset_radiusCDF_sublevel
    d hd γ a t hγ)).trans
      (centreRadiusCDF_uniform_distribution_bound d (by omega) _ hpow)

/-- The causal thin-strip completion retains the uniform cube covariate law. [For the stated inputs and conditions](hyp:d,hd,γ,L,B,a,hγ,hB,hL), [the asserted conclusion holds](goal). -/
lemma thinStripCompletion_covariate_marginal (d : ℕ) (hd : 2 ≤ d)
    (γ L B a : ℝ) (hγ : 1 < γ) (hB : 0 < B) (hL : 0 < L) :
    (thinStripCompletion d hd γ L B a).map Prod.fst =
      volume.restrict (cube d) := by
  unfold thinStripCompletion
  apply completionBind_covariate_marginal
  · apply Measurable.aemeasurable
    apply completionAt_measurable_of_measurable
    · exact stripPropensity_measurable d hd γ a
    · fun_prop
    · fun_prop
    · intro x
      refine ⟨stripPropensity_mem_Icc d hd γ a hγ x, ?_, ?_⟩
      · have hb := baselineSuccess_bounds B L hB hL
        exact ⟨hb.1.le, hb.2.1.trans (by norm_num)⟩
      · have hb := baselineSuccess_bounds B L hB hL
        exact ⟨hb.1.le, hb.2.1.trans (by norm_num)⟩
  · filter_upwards [] with x
    refine ⟨stripPropensity_mem_Icc d hd γ a hγ x, ?_, ?_⟩
    · have hb := baselineSuccess_bounds B L hB hL
      exact ⟨hb.1.le, hb.2.1.trans (by norm_num)⟩
    · have hb := baselineSuccess_bounds B L hB hL
      exact ⟨hb.1.le, hb.2.1.trans (by norm_num)⟩

/-- The explicit completion is a probability measure. [For the stated inputs and conditions](hyp:d,hd,gamma,L,B,a,hgamma,hB,hL), [the asserted conclusion holds](goal). -/
lemma thinStripCompletion_probability (d : ℕ) (hd : 2 ≤ d)
    (gamma L B a : ℝ) (hgamma : 1 < gamma) (hB : 0 < B) (hL : 0 < L) :
    IsProbabilityMeasure (thinStripCompletion d hd gamma L B a) := by
  apply isProbabilityMeasure_iff.mpr
  have hm := congrArg (fun mu : Measure (Fin d → ℝ) => mu Set.univ)
    (thinStripCompletion_covariate_marginal d hd gamma L B a hgamma hB hL)
  rw [Measure.map_apply measurable_fst MeasurableSet.univ] at hm
  have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
    ext x
    simp [cube, Set.mem_Icc, Pi.le_def]
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    hcube, Real.volume_Icc_pi] at hm
  simpa using hm

/-- The observed outcome coordinate is definitionally selected from the two
potential outcomes in the explicit completion. [For the stated inputs and conditions](hyp:d,hd,gamma,L,B,a,hgamma,hB,hL), [the asserted conclusion holds](goal). -/
lemma thinStripCompletion_consistency (d : ℕ) (hd : 2 ≤ d)
    (gamma L B a : ℝ) (hgamma : 1 < gamma) (hB : 0 < B) (hL : 0 < L) :
    OutcomeConsistency (thinStripCompletion d hd gamma L B a) := by
  unfold thinStripCompletion
  apply completionBind_consistency
  exact (completionAt_measurable_of_measurable B
    (stripPropensity d hd gamma a) (fun _ => baselineSuccess B L)
    (fun _ => baselineSuccess B L)
    (stripPropensity_measurable d hd gamma a) measurable_const measurable_const
    (fun x => ⟨stripPropensity_mem_Icc d hd gamma a hgamma x,
      ⟨(baselineSuccess_bounds B L hB hL).1.le,
        (baselineSuccess_bounds B L hB hL).2.1.trans (by norm_num)⟩,
      ⟨(baselineSuccess_bounds B L hB hL).1.le,
        (baselineSuccess_bounds B L hB hL).2.1.trans (by norm_num)⟩⟩)).aemeasurable

/-- The observed thin-strip witness has the uniform cube covariate marginal. [For the stated inputs and conditions](hyp:d,hd,γ,L,B,a,ha,hγ,hB,hL), [the asserted conclusion holds](goal). -/
lemma thinStripLaw_covariateLaw (d : ℕ) (hd : 2 ≤ d)
    (γ L B a : ℝ) (ha : 1 < a ∧ a < 1 + d / (γ - 1))
    (hγ : 1 < γ) (hB : 0 < B) (hL : 0 < L) :
    covariateLaw (thinStripLaw d hd γ L B a ha) =
      volume.restrict (cube d) := by
  unfold covariateLaw thinStripLaw
  have hobs : Measurable (@observed d) := by
    unfold observed
    fun_prop
  rw [Measure.map_map (by fun_prop) hobs]
  exact thinStripCompletion_covariate_marginal d hd γ L B a hγ hB hL

/-- [For the stated inputs and conditions](hyp:d,hd,gamma,L,B,a,ha,hgamma,hB,hL), [the asserted conclusion holds](goal). -/

lemma thinStripLaw_cubeSupport (d : ℕ) (hd : 2 ≤ d)
    (gamma L B a : ℝ) (ha : 1 < a ∧ a < 1 + d / (gamma - 1))
    (hgamma : 1 < gamma) (hB : 0 < B) (hL : 0 < L) :
    covariateLaw (thinStripLaw d hd gamma L B a ha) (cube d) = 1 := by
  have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
    ext x
    simp [cube, Set.mem_Icc, Pi.le_def]
  rw [thinStripLaw_covariateLaw d hd gamma L B a ha hgamma hB hL,
    Measure.restrict_apply (hcube.symm ▸ measurableSet_Icc), Set.inter_self]
  rw [hcube, Real.volume_Icc_pi]
  simp

/-- [For the stated inputs and conditions](hyp:d,hd,gamma,L,B,a,ha,hgamma,hB,hL), [the asserted conclusion holds](goal). -/

lemma thinStripLaw_covariateAC (d : ℕ) (hd : 2 ≤ d)
    (gamma L B a : ℝ) (ha : 1 < a ∧ a < 1 + d / (gamma - 1))
    (hgamma : 1 < gamma) (hB : 0 < B) (hL : 0 < L) :
    covariateLaw (thinStripLaw d hd gamma L B a ha) ≪ volume.restrict (cube d) := by
  rw [thinStripLaw_covariateLaw d hd gamma L B a ha hgamma hB hL]

/-- [For the stated inputs and conditions](hyp:d,hd,gamma,L,B,a,c_f,ha,hgamma,hB,hL,hcf), [the asserted conclusion holds](goal). -/

lemma thinStripLaw_density_lower (d : ℕ) (hd : 2 ≤ d)
    (gamma L B a c_f : ℝ) (ha : 1 < a ∧ a < 1 + d / (gamma - 1))
    (hgamma : 1 < gamma) (hB : 0 < B) (hL : 0 < L) (hcf : c_f ≤ 1) :
    CovariateDensityLowerBound (thinStripLaw d hd gamma L B a ha) c_f := by
  unfold CovariateDensityLowerBound covariateDensity
  rw [thinStripLaw_covariateLaw d hd gamma L B a ha hgamma hB hL]
  filter_upwards [Measure.rnDeriv_self (volume.restrict (cube d))] with x hx
  rw [hx, ENNReal.toReal_one]
  exact hcf

/-- The observed thin-strip witness is a probability law. [For the stated inputs and conditions](hyp:d,hd,γ,L,B,a,ha,hγ,hB,hL), [the asserted conclusion holds](goal). -/
lemma thinStripLaw_probability (d : ℕ) (hd : 2 ≤ d)
    (γ L B a : ℝ) (ha : 1 < a ∧ a < 1 + d / (γ - 1))
    (hγ : 1 < γ) (hB : 0 < B) (hL : 0 < L) :
    IsProbabilityMeasure (thinStripLaw d hd γ L B a ha) := by
  apply isProbabilityMeasure_iff.mpr
  have hX := thinStripLaw_covariateLaw d hd γ L B a ha hγ hB hL
  have hm := congrArg (fun μ : Measure (Fin d → ℝ) => μ Set.univ) hX
  rw [covariateLaw, Measure.map_apply measurable_fst MeasurableSet.univ,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hm
  have hcube : cube d =
      Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
    ext x
    simp [cube, Set.mem_Icc, Pi.le_def]
  rw [hcube, Real.volume_Icc_pi] at hm
  simpa using hm

/-- Disintegration of the frozen treated second-moment numerator onto the
uniform covariate law. [For the stated inputs and conditions](hyp:d,hd,gamma,L,B,a,ha,hgamma,hB,hL,h,hh), [the asserted conclusion holds](goal). -/
lemma thinStripLaw_treated_second_integral_identity (d : ℕ) (hd : 2 ≤ d)
    (gamma L B a : ℝ) (ha : 1 < a ∧ a < 1 + d / (gamma - 1))
    (hgamma : 1 < gamma) (hB : 0 < B) (hL : 0 < L)
    (h : ℝ) (hh : 0 < h) :
    (∫ z in {z : Obs d | z.2.1 = true ∧ centreRadius z.1 ≤ h},
        ((z.1 ⟨1, by omega⟩ - 1 / 2) / h) ^ 2
          ∂thinStripLaw d hd gamma L B a ha) =
      ∫ x in {x : Fin d → ℝ | centreRadius x ≤ h},
        ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 *
          stripPropensity d hd gamma a x ∂(volume.restrict (cube d)) := by
  let D : Set (Fin d → ℝ) := {x | centreRadius x ≤ h}
  let f : (Fin d → ℝ) → ℝ := fun x => ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2
  let p := baselineSuccess B L
  have hD : MeasurableSet D := measurableSet_le
    (by unfold centreRadius; fun_prop) measurable_const
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hvalid : ∀ x, stripPropensity d hd gamma a x ∈ Set.Icc 0 1 ∧
      p ∈ Set.Icc 0 1 ∧ p ∈ Set.Icc 0 1 := by
    intro x
    have hb := baselineSuccess_bounds B L hB hL
    exact ⟨stripPropensity_mem_Icc d hd gamma a hgamma x,
      ⟨hb.1.le, hb.2.1.trans (by norm_num)⟩,
      ⟨hb.1.le, hb.2.1.trans (by norm_num)⟩⟩
  let P := thinStripLaw d hd gamma L B a ha
  letI : IsProbabilityMeasure P :=
    thinStripLaw_probability d hd gamma L B a ha hgamma hB hL
  have hleft : Integrable (fun z : Obs d => f z.1)
      (P.restrict {z : Obs d | z.2.1 = true ∧ z.1 ∈ D}) := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact (hf.comp measurable_fst).aestronglyMeasurable
    · have hE : MeasurableSet {z : Obs d | z.2.1 = true ∧ z.1 ∈ D} := by
        have hA : Measurable (fun z : Obs d => z.2.1) :=
          measurable_fst.comp measurable_snd
        have hAt : MeasurableSet {z : Obs d | z.2.1 = true} :=
          (measurableSet_singleton true).preimage hA
        have hXD : MeasurableSet {z : Obs d | z.1 ∈ D} := hD.preimage measurable_fst
        exact hAt.inter hXD
      filter_upwards [ae_restrict_mem hE] with z hz
      have hr := hz.2
      have hc := (norm_le_pi_norm
        (z.1 - fun _ : Fin d => (1 / 2 : ℝ)) ⟨1, by omega⟩).trans hr
      have habs : |z.1 ⟨1, by omega⟩ - 1 / 2| ≤ h := by
        simpa [centreRadius, Pi.sub_apply, Real.norm_eq_abs] using hc
      have hdiv : |(z.1 ⟨1, by omega⟩ - 1 / 2) / h| ≤ 1 := by
        rw [abs_div, abs_of_pos hh]
        exact (div_le_iff₀ hh).2 (by simpa using habs)
      dsimp [f]
      rw [abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs, one_pow] using
        (pow_le_pow_left₀ (abs_nonneg _) hdiv 2)
  have hright : Integrable (fun x => f x * stripPropensity d hd gamma a x)
      ((volume.restrict (cube d)).restrict D) := by
    have hfin : (volume.restrict (cube d)) D ≠ ⊤ := by
      apply ne_top_of_le_ne_top _ (measure_mono (Set.subset_univ D))
      have hcube : volume (cube d) = 1 := by
        have hc : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
          ext x
          simp [cube, Set.mem_Icc, Pi.le_def]
        rw [hc, Real.volume_Icc_pi]
        simp
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hcube]
      exact ENNReal.one_ne_top
    apply (integrableOn_const (C := (1 : ℝ)) (hs := hfin)).mono'
    · exact (hf.mul (stripPropensity_measurable d hd gamma a)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hD] with x hx
      have hc := (norm_le_pi_norm
        (x - fun _ : Fin d => (1 / 2 : ℝ)) ⟨1, by omega⟩).trans hx
      have habs : |x ⟨1, by omega⟩ - 1 / 2| ≤ h := by
        simpa [centreRadius, Pi.sub_apply, Real.norm_eq_abs] using hc
      have hdiv : |(x ⟨1, by omega⟩ - 1 / 2) / h| ≤ 1 := by
        rw [abs_div, abs_of_pos hh]
        exact (div_le_iff₀ hh).2 (by simpa using habs)
      have hsq : f x ≤ 1 := by
        dsimp [f]
        simpa only [sq_abs, one_pow] using
          (pow_le_pow_left₀ (abs_nonneg _) hdiv 2)
      have he := stripPropensity_mem_Icc d hd gamma a hgamma x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) he.1)]
      exact (mul_le_mul_of_nonneg_right hsq he.1).trans (by simpa using he.2)
  change (∫ z in {z : Obs d | z.2.1 = true ∧ z.1 ∈ D}, f z.1 ∂P) = _
  unfold P thinStripLaw thinStripCompletion
  exact completionBind_observed_treated_setIntegral
    (volume.restrict (cube d)) B (stripPropensity d hd gamma a)
    (fun _ => p) (fun _ => p) f
    (stripPropensity_measurable d hd gamma a) measurable_const measurable_const hf
    (fun x => sq_nonneg _) hvalid D hD hleft hright

/-- Disintegration of the denominator of `stripSecondMoment`. [For the stated inputs and conditions](hyp:d,hd,gamma,L,B,a,ha,hgamma,hB,hL,h), [the asserted conclusion holds](goal). -/
lemma thinStripLaw_treated_mass_identity (d : ℕ) (hd : 2 ≤ d)
    (gamma L B a : ℝ) (ha : 1 < a ∧ a < 1 + d / (gamma - 1))
    (hgamma : 1 < gamma) (hB : 0 < B) (hL : 0 < L) (h : ℝ) :
    (thinStripLaw d hd gamma L B a ha).real
        {z : Obs d | z.2.1 = true ∧ centreRadius z.1 ≤ h} =
      ∫ x in {x : Fin d → ℝ | centreRadius x ≤ h},
        stripPropensity d hd gamma a x ∂(volume.restrict (cube d)) := by
  let D : Set (Fin d → ℝ) := {x | centreRadius x ≤ h}
  let p := baselineSuccess B L
  have hD : MeasurableSet D := measurableSet_le
    (by unfold centreRadius; fun_prop) measurable_const
  have hvalid : ∀ x, stripPropensity d hd gamma a x ∈ Set.Icc 0 1 ∧
      p ∈ Set.Icc 0 1 ∧ p ∈ Set.Icc 0 1 := by
    intro x
    have hb := baselineSuccess_bounds B L hB hL
    exact ⟨stripPropensity_mem_Icc d hd gamma a hgamma x,
      ⟨hb.1.le, hb.2.1.trans (by norm_num)⟩,
      ⟨hb.1.le, hb.2.1.trans (by norm_num)⟩⟩
  let P := thinStripLaw d hd gamma L B a ha
  letI : IsProbabilityMeasure P :=
    thinStripLaw_probability d hd gamma L B a ha hgamma hB hL
  have hE : MeasurableSet {z : Obs d | z.2.1 = true ∧ z.1 ∈ D} := by
    have hA : Measurable (fun z : Obs d => z.2.1) := measurable_fst.comp measurable_snd
    exact ((measurableSet_singleton true).preimage hA).inter
      (hD.preimage measurable_fst)
  have hleft : Integrable (fun _z : Obs d => (1 : ℝ))
      (P.restrict {z : Obs d | z.2.1 = true ∧ z.1 ∈ D}) := integrable_const _
  have hright : Integrable (fun x => (1 : ℝ) * stripPropensity d hd gamma a x)
      ((volume.restrict (cube d)).restrict D) := by
    have hfin : (volume.restrict (cube d)) D ≠ ⊤ := by
      apply ne_top_of_le_ne_top _ (measure_mono (Set.subset_univ D))
      have hcube : volume (cube d) = 1 := by
        have hc : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
          ext x
          simp [cube, Set.mem_Icc, Pi.le_def]
        rw [hc, Real.volume_Icc_pi]
        simp
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hcube]
      exact ENNReal.one_ne_top
    apply (integrableOn_const (C := (1 : ℝ)) (hs := hfin)).mono'
    · simpa only [one_mul] using
        (stripPropensity_measurable d hd gamma a).aestronglyMeasurable
    · filter_upwards [] with x
      rw [one_mul, Real.norm_eq_abs, abs_of_nonneg
        (stripPropensity_mem_Icc d hd gamma a hgamma x).1]
      exact (stripPropensity_mem_Icc d hd gamma a hgamma x).2
  have hid := completionBind_observed_treated_setIntegral
    (volume.restrict (cube d)) B (stripPropensity d hd gamma a)
    (fun _ => p) (fun _ => p) (fun _ => (1 : ℝ))
    (stripPropensity_measurable d hd gamma a) measurable_const measurable_const
    measurable_const (fun _ => zero_le_one) hvalid D hD hleft hright
  change P.real {z : Obs d | z.2.1 = true ∧ z.1 ∈ D} = _
  calc
    P.real {z : Obs d | z.2.1 = true ∧ z.1 ∈ D} =
        ∫ _z in {z : Obs d | z.2.1 = true ∧ z.1 ∈ D}, (1 : ℝ) ∂P := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
    _ = _ := by
      unfold P thinStripLaw thinStripCompletion
      simpa only [one_mul] using hid

/-- [For the stated inputs and conditions](hyp:d,hd,a,h,hh), [the asserted conclusion holds](goal). -/

lemma thinStrip_denominator_power_factor (d : ℕ) (hd : 2 ≤ d)
    (a h : ℝ) (hh : 0 < h) :
    (1 / 4 : ℝ) * (2 * (h / (4 * d)) ^ a) * (h / (4 * d)) ^ (d - 1) =
      ((1 / 2 : ℝ) / (((4 * d : ℝ) ^ a) * (4 * d) ^ (d - 1))) *
        h ^ (a + (d - 1 : ℕ)) := by
  have hk : (0 : ℝ) < 4 * d := by positivity
  rw [Real.div_rpow hh.le hk.le, div_pow]
  rw [← Real.rpow_natCast h (d - 1), Real.rpow_add hh]
  field_simp <;> ring

/-- [For the stated inputs and conditions](hyp:d,gamma,h,hh), [the asserted conclusion holds](goal). -/

lemma thinStrip_radial_numerator_power_factor (d : ℕ) (gamma h : ℝ)
    (hh : 0 < h) :
    (((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1))) * (2 * h) ^ d =
      (((2 : ℝ) ^ d) ^ ((1 : ℝ) / (gamma - 1)) * (2 : ℝ) ^ d) *
        h ^ ((d : ℝ) / (gamma - 1) + d) := by
  rw [mul_pow, Real.mul_rpow (pow_nonneg (by norm_num) _) (pow_nonneg hh.le _)]
  rw [← Real.rpow_natCast h d, ← Real.rpow_mul hh.le]
  rw [Real.rpow_add hh]
  ring_nf

/-- [For the stated inputs and conditions](hyp:d,hd,a,h,hh), [the asserted conclusion holds](goal). -/

lemma thinStrip_strip_numerator_power_factor (d : ℕ) (hd : 2 ≤ d)
    (a h : ℝ) (hh : 0 < h) :
    (h ^ a / h) ^ 2 * ((2 * h ^ a) * (2 * h) ^ (d - 1)) =
      ((2 : ℝ) * (2 : ℝ) ^ (d - 1)) * h ^ (3 * a + d - 3) := by
  rw [← Real.rpow_sub_one (ne_of_gt hh) a]
  rw [mul_pow]
  rw [← Real.rpow_natCast (h ^ (a - 1)) 2, ← Real.rpow_mul hh.le]
  rw [← Real.rpow_natCast h (d - 1)]
  ring_nf
  rw [← Real.rpow_add hh, ← Real.rpow_add hh]
  congr 2
  push_cast [Nat.cast_sub (by omega : 1 ≤ d)]
  ring

/-- [For the stated inputs and conditions](hyp:c,b,u,v,h,hb,hh), [the asserted conclusion holds](goal). -/

lemma positive_rpow_quotient_factor (c b u v h : ℝ)
    (hb : 0 < b) (hh : 0 < h) :
    (c * h ^ u) / (b * h ^ v) = (c / b) * h ^ (u - v) := by
  rw [Real.rpow_sub hh]
  field_simp

/-- [For the stated inputs and conditions](hyp:d,hd,gamma,a,hgamma,ha), [the asserted conclusion holds](goal). -/

lemma thinStrip_raw_second_envelope_tendsto_zero (d : ℕ) (hd : 2 ≤ d)
    (gamma a : ℝ) (hgamma : 1 < gamma)
    (ha : 1 < a ∧ a < 1 + d / (gamma - 1)) :
    Filter.Tendsto
      (fun h : ℝ =>
        ((((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1))) * (2 * h) ^ d +
          (h ^ a / h) ^ 2 * ((2 * h ^ a) * (2 * h) ^ (d - 1))) /
        ((1 / 4 : ℝ) * (2 * (h / (4 * d)) ^ a) *
          (h / (4 * d)) ^ (d - 1)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let b : ℝ := (1 / 2 : ℝ) /
    (((4 * d : ℝ) ^ a) * (4 * d) ^ (d - 1))
  let c₁ : ℝ := ((2 : ℝ) ^ d) ^ ((1 : ℝ) / (gamma - 1)) * (2 : ℝ) ^ d
  let c₂ : ℝ := (2 : ℝ) * (2 : ℝ) ^ (d - 1)
  let p : ℝ := 1 + d / (gamma - 1) - a
  let q : ℝ := 2 * a - 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hp : 0 < p := by dsimp [p]; linarith [ha.2]
  have hq : 0 < q := by dsimp [q]; linarith [ha.1]
  have hpow (r : ℝ) (hr : 0 < r) : Filter.Tendsto (fun h : ℝ => h ^ r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hid : Filter.Tendsto (fun h : ℝ => h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    simpa [Real.zero_rpow (ne_of_gt hr)] using hid.rpow_const (Or.inr hr.le)
  have hlim : Filter.Tendsto
      (fun h : ℝ => (c₁ / b) * h ^ p + (c₂ / b) * h ^ q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (hpow p hp)).add
      (tendsto_const_nhds.mul (hpow q hq))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhpos : 0 < h := hh
  rw [thinStrip_radial_numerator_power_factor d gamma h hhpos,
    thinStrip_strip_numerator_power_factor d hd a h hhpos,
    thinStrip_denominator_power_factor d hd a h hhpos, add_div,
    positive_rpow_quotient_factor c₁ b _ _ h hb hhpos,
    positive_rpow_quotient_factor c₂ b _ _ h hb hhpos]
  dsimp [c₁, c₂, p, q]
  congr 1
  · congr 1
    push_cast [Nat.cast_sub (by omega : 1 ≤ d)]
    ring
  · congr 1
    push_cast [Nat.cast_sub (by omega : 1 ≤ d)]
    ring

/-- The uniform thin-strip witness violates Dorn's numerical local mass
condition. [For the stated inputs and conditions](hyp:d,hd,γ,L,B,a,ha,hγ,hB,hL), [the asserted conclusion holds](goal). -/
lemma thinStripLaw_not_dornA3AntiConcentration (d : ℕ) (hd : 2 ≤ d)
    (γ L B a : ℝ) (ha : 1 < a ∧ a < 1 + d / (γ - 1))
    (hγ : 1 < γ) (hB : 0 < B) (hL : 0 < L) :
    ¬ DornA3AntiConcentrationOnCube (thinStripLaw d hd γ L B a ha)
      (stripPropensity d hd γ a) := by
  let P := thinStripLaw d hd γ L B a ha
  letI : IsProbabilityMeasure P :=
    thinStripLaw_probability d hd γ L B a ha hγ hB hL
  apply strip_not_dornA3AntiConcentration_of_local_strip_ratio
    d hd γ a hγ (by linarith) P
  intro ρ ν h₀ hρ hν hh₀
  have hX : covariateLaw P = volume.restrict (cube d) :=
    thinStripLaw_covariateLaw d hd γ L B a ha hγ hB hL
  simpa only [hX] using
    uniformCube_thinStrip_local_ratio d hd γ a hγ ha.1 ρ ν h₀ hρ hν hh₀

/-- The uniform thin-strip witness violates full Dorn A3 because it violates
the numerical local mass condition. [For the stated inputs and conditions](hyp:d,hd,γ,L,B,a,ha,hγ,hB,hL), [the asserted conclusion holds](goal). -/
lemma thinStripLaw_not_dornA3 (d : ℕ) (hd : 2 ≤ d)
    (γ L B a : ℝ) (ha : 1 < a ∧ a < 1 + d / (γ - 1))
    (hγ : 1 < γ) (hB : 0 < B) (hL : 0 < L) :
    ¬ DornA3OnCube (thinStripLaw d hd γ L B a ha)
      (stripPropensity d hd γ a) := by
  intro hA3
  exact thinStripLaw_not_dornA3AntiConcentration d hd γ L B a ha hγ hB hL
    (dornA3AntiConcentrationOnCube_of_dornA3OnCube
      (thinStripLaw d hd γ L B a ha) (stripPropensity d hd γ a) hA3)

/-- Transfer the sharp strip tail bound from uniform cube volume to any
observed law with that covariate marginal. [For the stated inputs and conditions](hyp:d,hd,P,γ,a,hγ,hX,t,ht), [the asserted conclusion holds](goal). -/
lemma stripPropensity_tail_of_uniform_covariateLaw (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (Obs d)) (γ a : ℝ) (hγ : 1 < γ)
    (hX : covariateLaw P = volume.restrict (cube d))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (covariateLaw P).real {x | stripPropensity d hd γ a x ≤ t} ≤
      t ^ (γ - 1) := by
  rw [hX]
  exact stripPropensity_uniform_tail_bound d hd γ a t hγ ht

/-- The selected strip propensity satisfies the numerical tail inequality for
every admissible model coefficient. [For the stated inputs and conditions](hyp:d,hd,gamma,L,B,a,C,ha,hgamma,hB,hL,hC), [the asserted conclusion holds](goal). -/
lemma thinStripLaw_selected_tail_bound (d : ℕ) (hd : 2 ≤ d)
    (gamma L B a C : ℝ) (ha : 1 < a ∧ a < 1 + d / (gamma - 1))
    (hgamma : 1 < gamma) (hB : 0 < B) (hL : 0 < L) (hC : 1 ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (covariateLaw (thinStripLaw d hd gamma L B a ha)).real
          {x | stripPropensity d hd gamma a x ≤ t} ≤ C * t ^ (gamma - 1) := by
  intro t ht
  have htail := stripPropensity_tail_of_uniform_covariateLaw d hd
    (thinStripLaw d hd gamma L B a ha) gamma a hgamma
    (thinStripLaw_covariateLaw d hd gamma L B a ha hgamma hB hL) t ht
  exact htail.trans (by
    have hp : 0 ≤ t ^ (gamma - 1) := Real.rpow_nonneg ht.1 _
    nlinarith)

/-- Under the uniform design, the displayed propensity vanishes only on a
null set, as follows from its sharp lower-tail bound. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ), [the asserted conclusion holds](goal). -/
lemma stripPropensity_uniform_zero_null (d : ℕ) (hd : 2 ≤ d)
    (γ a : ℝ) (hγ : 1 < γ) :
    (volume.restrict (cube d)) {x | stripPropensity d hd γ a x = 0} = 0 := by
  let μ := volume.restrict (cube d)
  have hvol : volume (cube d) = 1 := by
    have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    rw [isFiniteMeasure_restrict]
    simp [hvol]
  have htail := stripPropensity_uniform_tail_bound d hd γ a 0 hγ
    (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
  rw [Real.zero_rpow (ne_of_gt (sub_pos.mpr hγ))] at htail
  have hreal : μ.real {x | stripPropensity d hd γ a x = 0} = 0 := by
    apply le_antisymm _ (ENNReal.toReal_nonneg)
    exact (measureReal_mono (by intro x hx; exact le_of_eq hx)).trans htail
  have hfin : μ {x | stripPropensity d hd γ a x = 0} ≠ ⊤ := measure_ne_top _ _
  exact (ENNReal.toReal_eq_zero_iff _).mp hreal |>.resolve_right hfin

/-- The sharp tail bound gives almost-everywhere positivity under uniform
design. [For the stated inputs and conditions](hyp:d,hd,γ,a,hγ), [the asserted conclusion holds](goal). -/
lemma stripPropensity_uniform_pos_ae (d : ℕ) (hd : 2 ≤ d)
    (γ a : ℝ) (hγ : 1 < γ) :
    ∀ᵐ x ∂volume.restrict (cube d), 0 < stripPropensity d hd γ a x := by
  have hzero := stripPropensity_uniform_zero_null d hd γ a hγ
  have hne : ∀ᵐ x ∂volume.restrict (cube d),
      stripPropensity d hd γ a x ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hne] with x hx
  exact lt_of_le_of_ne (stripPropensity_mem_Icc d hd γ a hγ x).1 (Ne.symm hx)

/-- At fixed covariates, the covariate and treated potential outcome have the
product law determined by the treated Bernoulli arm. [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,x,he,hp₀,hp₁), [the asserted conclusion holds](goal). -/
lemma completionAt_covariate_treatedPotential_map {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc 0 1) (hp₀ : p₀ x ∈ Set.Icc 0 1)
    (hp₁ : p₁ x ∈ Set.Icc 0 1) :
    (completionAt B e p₀ p₁ x).map (fun ω => (ω.1, ω.2.2.2.1)) =
      (Measure.dirac x).prod (scaledBernoulli B (p₁ x)) := by
  letI := realBernoulli_probability (e x) he
  letI := scaledBernoulli_probability B (p₀ x) hp₀
  letI := scaledBernoulli_probability B (p₁ x) hp₁
  unfold completionAt
  rw [Measure.map_map (by fun_prop) (by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption))]
  rw [Measure.dirac_prod]
  calc
    Measure.map (fun z : Bool × (ℝ × ℝ) => (x, z.2.2))
        ((realBernoulli (e x)).prod
          ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))) =
        Measure.map (Prod.mk x) (Measure.map (fun z : Bool × (ℝ × ℝ) => z.2.2)
          ((realBernoulli (e x)).prod
            ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x))))) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [show (fun z : Bool × (ℝ × ℝ) => z.2.2) = Prod.snd ∘ Prod.snd by rfl]
      rw [← Measure.map_map (by fun_prop) (by fun_prop), Measure.map_snd_prod,
        measure_univ, one_smul, Measure.map_snd_prod, measure_univ, one_smul]

/-- Mixing the fixed-covariate identity identifies the joint covariate and
treated-potential-outcome law as a kernel product. [For the stated inputs and conditions](hyp:d,mu,B,e,p₀,p₁,he,hp₀,hp₁,hvalid), [the asserted conclusion holds](goal). -/
lemma completionBind_covariate_treatedPotential_compProd {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1) :
    let k₁ : ProbabilityTheory.Kernel (Fin d → ℝ) ℝ :=
      ProbabilityTheory.Kernel.mk (fun x => scaledBernoulli B (p₁ x))
        (by unfold scaledBernoulli realBernoulli; fun_prop)
    (mu.bind (completionAt B e p₀ p₁)).map (fun ω => (ω.1, ω.2.2.2.1)) =
      Measure.compProd mu k₁ := by
  dsimp
  let k₁ : ProbabilityTheory.Kernel (Fin d → ℝ) ℝ :=
    ProbabilityTheory.Kernel.mk (fun x => scaledBernoulli B (p₁ x))
      (by unfold scaledBernoulli realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel k₁ :=
    ⟨fun x => scaledBernoulli_probability B (p₁ x) (hvalid x).2.2⟩
  have hk : Measurable (completionAt B e p₀ p₁) :=
    completionAt_measurable_of_measurable B e p₀ p₁ he hp₀ hp₁ hvalid
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.bind_apply (hs.preimage (by fun_prop)) hk.aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  letI := scaledBernoulli_probability B (p₁ x) (hvalid x).2.2
  have hfix := completionAt_covariate_treatedPotential_map B e p₀ p₁ x
    (hvalid x).1 (hvalid x).2.1 (hvalid x).2.2
  have happ := congrArg (fun m : Measure ((Fin d → ℝ) × ℝ) => m s) hfix
  rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply hs,
    lintegral_dirac] at happ
  simpa [k₁] using happ

/-- A constant response whose magnitude is at most the radius belongs to the
paper's intrinsic Hölder ball. [For the stated inputs and conditions](hyp:d,β,L,c,hβ,hL,hc), [the asserted conclusion holds](goal). -/
lemma constant_holderBall {d : ℕ} (β L c : ℝ) (hβ : 0 < β)
    (hL : 0 ≤ L) (hc : |c| ≤ L) :
    HolderBall (d := d) β L (fun _ => c) := by
  open Causalean.Mathlib.Analysis.Calculus.CubeExtension in
    obtain ⟨A, hA, hscaled⟩ :=
      exists_uniform_scaledProductBump_holderBallOn (d := d) β hβ
  open Causalean.Mathlib.Analysis.Calculus.CubeExtension in
    have hconst := holderBallOn_unitCube_add_const_mul hA.le
      (hscaled 1 zero_lt_one le_rfl (fun _ => 0)) c 0
  have hbase :
      Causalean.Mathlib.Analysis.Calculus.CubeExtension.HolderBallOn
        (cube d) (polynomialDegree β) (β - (polynomialDegree β : ℝ)) |c|
        (fun _ => c) := by
    simpa [polynomialDegree, cube,
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.unitCube] using hconst
  refine ⟨hbase.regularity, ?_, ?_⟩
  · intro j hj f x hx
    exact (hbase.derivBound j hj f x hx).trans hc
  · intro f x hx y hy
    exact (hbase.modulus f x hx y hy).trans
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (norm_nonneg _) _))

/-- In an equal-arm completion with a constant Bernoulli success probability,
the constant scaled mean is a Hölder representative of the treated potential
outcome conditional mean. [For the stated inputs and conditions](hyp:d,mu,B,p,β,L,e,he,hvalid,hβ,hL,hmean), [the asserted conclusion holds](goal). -/
lemma completionBind_holderResponse_constant_equal_arms {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B p β L : ℝ)
    (e : (Fin d → ℝ) → ℝ) (he : Measurable e)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p ∈ Set.Icc 0 1)
    [IsFiniteMeasure (mu.bind (completionAt B e (fun _ => p) (fun _ => p)))]
    (hβ : 0 < β) (hL : 0 ≤ L) (hmean : |B * p| ≤ L) :
    HolderResponse (mu.bind (completionAt B e (fun _ => p) (fun _ => p)))
      (fun _ => B * p) β L := by
  let Pc := mu.bind (completionAt B e (fun _ => p) (fun _ => p))
  let X : Completion d → (Fin d → ℝ) := fun ω => ω.1
  let Y₁ : Completion d → ℝ := fun ω => ω.2.2.2.1
  let k₁ : ProbabilityTheory.Kernel (Fin d → ℝ) ℝ :=
    ProbabilityTheory.Kernel.mk (fun _ => scaledBernoulli B p)
      (by fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel k₁ :=
    ⟨fun _ => scaledBernoulli_probability B p (hvalid (fun _ => 0)).2⟩
  have hcomp : Measurable (completionAt B e (fun _ => p) (fun _ => p)) :=
    completionAt_measurable_of_measurable B e (fun _ => p) (fun _ => p)
      he measurable_const measurable_const
      (fun x => ⟨(hvalid x).1, (hvalid x).2, (hvalid x).2⟩)
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hY₁ : Measurable Y₁ := by dsimp [Y₁]; fun_prop
  have hcov : Pc.map X = mu := by
    dsimp [Pc, X]
    exact completionBind_covariate_marginal mu B e (fun _ => p) (fun _ => p)
      hcomp.aemeasurable
      (Filter.Eventually.of_forall (fun x =>
        ⟨(hvalid x).1, (hvalid x).2, (hvalid x).2⟩))
  have hjoint : Pc.map (fun ω => (X ω, Y₁ ω)) = Measure.compProd mu k₁ := by
    dsimp [Pc, X, Y₁, k₁]
    exact completionBind_covariate_treatedPotential_compProd mu B e
      (fun _ => p) (fun _ => p) he measurable_const measurable_const
      (fun x => ⟨(hvalid x).1, (hvalid x).2, (hvalid x).2⟩)
  have hcond : ProbabilityTheory.condDistrib Y₁ X Pc =ᵐ[mu] k₁ := by
    have h := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := Pc) (X := X) (Y := Y₁) (κ := k₁) hX hY₁
        (by simpa [hcov] using hjoint)
    simpa [hcov] using h
  have hY₁int : Integrable Y₁ Pc := by
    apply Integrable.mono' (integrable_const |B|) hY₁.aestronglyMeasurable
    filter_upwards [completionBind_supported_on_endpoints mu B e
      (fun _ => p) (fun _ => p)
      (Filter.Eventually.of_forall (fun x =>
        ⟨(hvalid x).1, (hvalid x).2, (hvalid x).2⟩))] with ω hω
    rcases hω.2 with hzero | hBval
    · simp [Y₁, hzero]
    · dsimp [Y₁]
      rw [Set.mem_singleton_iff.mp hBval]
  have hce : Pc[Y₁ | MeasurableSpace.comap X inferInstance] =ᵐ[Pc]
      fun ω => ∫ y : ℝ, y ∂ProbabilityTheory.condDistrib Y₁ X Pc (X ω) := by
    simpa using ProbabilityTheory.condExp_ae_eq_integral_condDistrib' hX hY₁int
  have hkernel_comp : ∀ᵐ ω ∂Pc,
      ProbabilityTheory.condDistrib Y₁ X Pc (X ω) = k₁ (X ω) := by
    have hcond' : ProbabilityTheory.condDistrib Y₁ X Pc =ᵐ[Pc.map X] k₁ := by
      rw [hcov]
      exact hcond
    exact ae_eq_comp hX.aemeasurable hcond'
  have hmean_cond : (fun ω : Completion d =>
      ∫ y : ℝ, y ∂ProbabilityTheory.condDistrib Y₁ X Pc (X ω)) =ᵐ[Pc]
      fun _ => B * p := by
    filter_upwards [hkernel_comp] with ω hω
    rw [hω]
    exact scaledBernoulli_integral_id B p (hvalid (X ω)).2
  refine ⟨constant_holderBall β L (B * p) hβ hL hmean, ?_⟩
  exact hmean_cond.symm.trans hce.symm

/-- All fields of the thin-strip global-tail model other than the explicitly
supplied Hölder response follow from the completion construction. [For the stated inputs and conditions](hyp:d,hd,β,B,L,C,c_f,γ,a,ha,hγ,hB,hL,hC,hcf,μ₁,hholder), [the asserted conclusion holds](goal). -/
lemma thinStrip_globalTailModel_of_holder (d : ℕ) (hd : 2 ≤ d)
    (β B L C c_f γ a : ℝ) (ha : 1 < a ∧ a < 1 + d / (γ - 1))
    (hγ : 1 < γ) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : c_f ≤ 1)
    (μ₁ : (Fin d → ℝ) → ℝ)
    (hholder : HolderResponse (thinStripCompletion d hd γ L B a) μ₁ β L) :
    @GlobalTailModel d β B L C c_f γ
      (thinStripCompletion d hd γ L B a)
      (thinStripCompletion_probability d hd γ L B a hγ hB hL)
      μ₁ (stripPropensity d hd γ a) := by
  let mu := volume.restrict (cube d)
  let Pc := thinStripCompletion d hd γ L B a
  let P := Pc.map observed
  let p := baselineSuccess B L
  have hb := baselineSuccess_bounds B L hB hL
  have hvalid : ∀ x, stripPropensity d hd γ a x ∈ Set.Icc 0 1 ∧
      p ∈ Set.Icc 0 1 ∧ p ∈ Set.Icc 0 1 := fun x =>
    ⟨stripPropensity_mem_Icc d hd γ a hγ x,
      ⟨hb.1.le, hb.2.1.trans (by norm_num)⟩,
      ⟨hb.1.le, hb.2.1.trans (by norm_num)⟩⟩
  letI : IsProbabilityMeasure Pc :=
    thinStripCompletion_probability d hd γ L B a hγ hB hL
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    apply Measure.isProbabilityMeasure_map
    unfold observed
    fun_prop
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
  letI : IsFiniteMeasure
      (mu.bind (completionAt B (stripPropensity d hd γ a)
        (fun _ => p) (fun _ => p))) := by
    change IsFiniteMeasure Pc
    infer_instance
  letI : IsFiniteMeasure
      ((mu.bind (completionAt B (stripPropensity d hd γ a)
        (fun _ => p) (fun _ => p))).map observed) := by
    change IsFiniteMeasure P
    infer_instance
  letI : IsProbabilityMeasure (thinStripLaw d hd γ L B a ha) :=
    thinStripLaw_probability d hd γ L B a ha hγ hB hL
  have hPdef : P = thinStripLaw d hd γ L B a ha := by
    rfl
  refine {
    cubeSupport := ?_
    covariateAC := ?_
    density := ?_
    consistency := ?_
    exchangeability := ?_
    tail := ?_
    outcome := ?_
    smooth := hholder }
  · simpa [thinStripLaw] using
      thinStripLaw_cubeSupport d hd γ L B a ha hγ hB hL
  · simpa [thinStripLaw] using
      thinStripLaw_covariateAC d hd γ L B a ha hγ hB hL
  · simpa [thinStripLaw] using
      thinStripLaw_density_lower d hd γ L B a c_f ha hγ hB hL hcf
  · exact thinStripCompletion_consistency d hd γ L B a hγ hB hL
  · dsimp [Pc, thinStripCompletion, mu, p]
    exact completionBind_condExchangeable (volume.restrict (cube d)) B
      (stripPropensity d hd γ a) (fun _ => baselineSuccess B L)
      (fun _ => baselineSuccess B L) (stripPropensity_measurable d hd γ a)
      measurable_const measurable_const hvalid
  · constructor
    · have hpraw := completionBind_propensity_ae mu B
        (stripPropensity d hd γ a) (fun _ => p) (fun _ => p)
        (stripPropensity_measurable d hd γ a) measurable_const measurable_const hvalid
      dsimp [mu, p] at hpraw
      have hcov := thinStripLaw_covariateLaw d hd γ L B a ha hγ hB hL
      change ∀ᵐ x ∂covariateLaw (thinStripLaw d hd γ L B a ha),
        stripPropensity d hd γ a x =
          propensity (thinStripLaw d hd γ L B a ha) x
      rw [hcov]
      filter_upwards [hpraw] with x hx
      exact hx.symm
    · intro t ht
      simpa [thinStripLaw] using
        thinStripLaw_selected_tail_bound d hd γ L B a C ha hγ hB hL hC t ht
  · have hout := completionBind_boundedMeanSubGaussian_equal_arms mu B hB
      (stripPropensity d hd γ a) (fun _ => p)
      (stripPropensity_measurable d hd γ a) measurable_const
      (fun x => ⟨(hvalid x).1, (hvalid x).2.1⟩)
      (stripPropensity_uniform_pos_ae d hd γ a hγ)
    simpa [mu, Pc, P, p, thinStripCompletion] using hout

/-- Treated-design second moment in the normalized second direction. For [the stated inputs and conditions](hyp:d,hd,γ,L,B,a,ha,h), [the `stripSecondMoment` object being defined](goal). -/
noncomputable def stripSecondMoment (d : ℕ) (hd : 2 ≤ d) (γ L B a : ℝ)
    (ha : 1 < a ∧ a < 1 + d / (γ - 1)) (h : ℝ) : ℝ :=
  let P := thinStripLaw d hd γ L B a ha
  let E : Set (Obs d) := {z | z.2.1 = true ∧ ‖z.1 - (fun _ => (1 / 2 : ℝ))‖ ≤ h}
  (∫ z in E, ((z.1 ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 ∂P) / P.real E

/-- [For the stated inputs and conditions](hyp:d,hd,gamma,L,B,a,ha,hgamma,hB,hL), [the asserted conclusion holds](goal). -/

lemma stripSecondMoment_tendsto_zero (d : ℕ) (hd : 2 ≤ d)
    (gamma L B a : ℝ) (ha : 1 < a ∧ a < 1 + d / (gamma - 1))
    (hgamma : 1 < gamma) (hB : 0 < B) (hL : 0 < L) :
    Filter.Tendsto (stripSecondMoment d hd gamma L B a ha)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let G : ℝ → ℝ := fun h =>
    ((((2 * h) ^ d) ^ ((1 : ℝ) / (gamma - 1))) * (2 * h) ^ d +
      (h ^ a / h) ^ 2 * ((2 * h ^ a) * (2 * h) ^ (d - 1))) /
    ((1 / 4 : ℝ) * (2 * (h / (4 * d)) ^ a) *
      (h / (4 * d)) ^ (d - 1))
  have hG : Filter.Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    thinStrip_raw_second_envelope_tendsto_zero d hd gamma a hgamma ha
  refine squeeze_zero' (g := G) ?_ ?_ hG
  · filter_upwards [self_mem_nhdsWithin] with h hh
    unfold stripSecondMoment
    exact div_nonneg (integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun z => sq_nonneg _))) (measureReal_nonneg)
  · have hsmall : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), h ≤ 1 / 2 := by
      filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with h hh
      exact hh.2
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhhalf
    have hhpos : 0 < h := hh
    have hnum := thinStrip_treated_second_sup_power_bound d hd gamma a h
      hgamma (by linarith [ha.1] : 0 ≤ a) hhpos hhhalf
    have hden := thinStrip_treated_sup_mass_lower d hd gamma a h
      hgamma ha.1 hhpos (hhhalf.trans (by norm_num))
    have hdenpos : 0 < (1 / 4 : ℝ) *
        ((2 * (h / (4 * d)) ^ a) * (h / (4 * d)) ^ (d - 1)) := by positivity
    have hnum_nonneg : 0 ≤ ∫ x in {x : Fin d → ℝ | centreRadius x ≤ h},
        ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd gamma a x
          ∂(volume.restrict (cube d)) := by
      apply integral_nonneg_of_ae
      filter_upwards [] with x
      exact mul_nonneg (sq_nonneg _)
        (stripPropensity_mem_Icc d hd gamma a hgamma x).1
    change ((∫ z in {z : Obs d | z.2.1 = true ∧ centreRadius z.1 ≤ h},
        ((z.1 ⟨1, by omega⟩ - 1 / 2) / h) ^ 2
          ∂thinStripLaw d hd gamma L B a ha) /
        (thinStripLaw d hd gamma L B a ha).real
          {z : Obs d | z.2.1 = true ∧ centreRadius z.1 ≤ h}) ≤ G h
    rw [thinStripLaw_treated_second_integral_identity d hd gamma L B a ha
      hgamma hB hL h hhpos,
      thinStripLaw_treated_mass_identity d hd gamma L B a ha hgamma hB hL h]
    calc
      _ ≤ (∫ x in {x : Fin d → ℝ | centreRadius x ≤ h},
          ((x ⟨1, by omega⟩ - 1 / 2) / h) ^ 2 * stripPropensity d hd gamma a x
            ∂(volume.restrict (cube d))) /
          ((1 / 4 : ℝ) * ((2 * (h / (4 * d)) ^ a) *
            (h / (4 * d)) ^ (d - 1))) :=
        div_le_div_of_nonneg_left hnum_nonneg hdenpos hden
      _ ≤ G h := by
        dsimp [G]
        convert div_le_div_of_nonneg_right hnum hdenpos.le using 1
        congr 1
        ring

-- @node: prop:strict-enlargement
/-- A centred thin-strip propensity satisfies the global tail bound, yet it
fails Dorn's numerical anti-concentration clause even when propensity one is
allowed. Its normalized treated design also loses its second direction. [For the stated inputs and conditions](hyp:d,hd,β,B,L,C,c_f,γ,hβ,hB,hL,hC,hcf,hγ), [the asserted conclusion holds](goal). -/
theorem thinStrip_mem_model_not_dornA3 (d : ℕ) (hd : 2 ≤ d)
    (β B L C c_f γ : ℝ) (hβ : 1 < β) (hB : 0 < B)
    (hL : 0 < L) (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγ : 1 < γ) :
    ∀ a : ℝ, ∀ ha : 1 < a ∧ a < 1 + d / (γ - 1),
      let P := thinStripLaw d hd γ L B a ha
      P ∈ ModelClass d β B L C c_f γ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        (covariateLaw P).real {x | stripPropensity d hd γ a x ≤ t} ≤
          t ^ (γ - 1)) ∧
      ¬ DornA3AntiConcentrationOnCube P (stripPropensity d hd γ a) ∧
      ¬ DornA3OnCube P (stripPropensity d hd γ a) ∧
      Filter.Tendsto (stripSecondMoment d hd γ L B a ha)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∃ Q ∈ ModelClass d β B L C c_f γ,
        ¬ DornA3OnCube Q (stripPropensity d hd γ a) := by
  intro a ha
  dsimp only
  let p := baselineSuccess B L
  let μ₁ : (Fin d → ℝ) → ℝ := fun _ => B * p
  let Pc := thinStripCompletion d hd γ L B a
  let P := thinStripLaw d hd γ L B a ha
  letI : IsProbabilityMeasure Pc :=
    thinStripCompletion_probability d hd γ L B a hγ hB hL
  letI : IsProbabilityMeasure P :=
    thinStripLaw_probability d hd γ L B a ha hγ hB hL
  have hb := baselineSuccess_bounds B L hB hL
  have hvalid : ∀ x, stripPropensity d hd γ a x ∈ Set.Icc 0 1 ∧
      p ∈ Set.Icc 0 1 := fun x =>
    ⟨stripPropensity_mem_Icc d hd γ a hγ x,
      ⟨hb.1.le, hb.2.1.trans (by norm_num)⟩⟩
  have hmean : |B * p| ≤ L := by
    rw [abs_of_pos (mul_pos hB hb.1)]
    exact hb.2.2.trans (by linarith)
  letI : IsFiniteMeasure
      ((volume.restrict (cube d)).bind
        (completionAt B (stripPropensity d hd γ a) (fun _ => p) (fun _ => p))) := by
    change IsFiniteMeasure Pc
    infer_instance
  have hholder : HolderResponse Pc μ₁ β L := by
    have hraw := completionBind_holderResponse_constant_equal_arms
      (volume.restrict (cube d)) B p β L (stripPropensity d hd γ a)
      (stripPropensity_measurable d hd γ a) hvalid
      (lt_trans zero_lt_one hβ) hL.le hmean
    simpa [Pc, μ₁, p, thinStripCompletion] using hraw
  have hmodel : @GlobalTailModel d β B L C c_f γ Pc inferInstance μ₁
      (stripPropensity d hd γ a) :=
    thinStrip_globalTailModel_of_holder d hd β B L C c_f γ a ha hγ hB hL
      hC hcf.2 μ₁ hholder
  have hparams : ModelParameterDomain d β B L C c_f :=
    ⟨by omega, hβ, hB, hL, hC, hcf⟩
  have hmem : P ∈ ModelClass d β B L C c_f γ := by
    refine ⟨hparams, hγ, Pc, inferInstance, μ₁,
      stripPropensity d hd γ a, ?_, hmodel⟩
    rfl
  have htail : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (covariateLaw P).real {x | stripPropensity d hd γ a x ≤ t} ≤
        t ^ (γ - 1) := by
    intro t ht
    exact stripPropensity_tail_of_uniform_covariateLaw d hd P γ a hγ
      (by simpa [P] using
        thinStripLaw_covariateLaw d hd γ L B a ha hγ hB hL) t ht
  have hnotAnti : ¬ DornA3AntiConcentrationOnCube P
      (stripPropensity d hd γ a) := by
    simpa [P] using
      thinStripLaw_not_dornA3AntiConcentration d hd γ L B a ha hγ hB hL
  have hnot : ¬ DornA3OnCube P (stripPropensity d hd γ a) := by
    intro hA3
    exact hnotAnti
      (dornA3AntiConcentrationOnCube_of_dornA3OnCube P
        (stripPropensity d hd γ a) hA3)
  have htend : Filter.Tendsto (stripSecondMoment d hd γ L B a ha)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    stripSecondMoment_tendsto_zero d hd γ L B a ha hγ hB hL
  exact ⟨hmem, htail, hnotAnti, hnot, htend, ⟨P, hmem, hnot⟩⟩
end CausalSmith.Stat.WeakOverlap
