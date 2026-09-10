import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Statements
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CapBridge
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.SeparableMeasure

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- For [the stated conditions](hyp:e,P,R), [the conditionalCanonicalKernel object](goal) is defined as specified. -/
-- @node: conditionalCanonicalKernel
noncomputable def conditionalCanonicalKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : Bool → X → ℝ) (he : ∀ a, Measurable (e a))
    (P R : Bool → Kernel X Y) : Kernel X (Bool × Y × Y) :=
  let K0 := ((P false).prod (R true)).map (fun z => (false, z))
  let K1 := ((R false).prod (P true)).map (fun z => (true, z))
  { toFun := fun x => ENNReal.ofReal (e false x) • K0 x +
      ENNReal.ofReal (e true x) • K1 x
    measurable' := by
      apply Measure.measurable_of_measurable_coe
      intro s hs
      simp only [Measure.add_apply, Measure.smul_apply, hs]
      have hK0 : Measurable fun x => K0 x s := Kernel.measurable_coe K0 hs
      have hK1 : Measurable fun x => K1 x s := Kernel.measurable_coe K1 hs
      fun_prop }

/-- For the specified model objects, [the stated conditions](hyp:he), [the stated mathematical relationship holds](goal). -/
-- @node: conditionalCanonicalKernel_apply
lemma conditionalCanonicalKernel_apply {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : Bool → X → ℝ) (he : ∀ a, Measurable (e a))
    (P R : Bool → Kernel X Y) (x : X) :
    conditionalCanonicalKernel e he P R x =
      ENNReal.ofReal (e false x) •
          (((P false).prod (R true)).map (fun z => (false, z))) x +
      ENNReal.ofReal (e true x) •
          (((R false).prod (P true)).map (fun z => (true, z))) x := by
  rfl

/-- For the specified model objects, [the stated conditions](hyp:he,hP,hR), [the stated mathematical relationship holds](goal). -/
-- @node: conditionalCanonicalKernel_markov
lemma conditionalCanonicalKernel_markov {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : Bool → X → ℝ) (P R : Bool → Kernel X Y)
    (he : PropensitySystem e) (hP : ∀ a, IsMarkovKernel (P a))
    (hR : ∀ a, IsMarkovKernel (R a)) : IsMarkovKernel (conditionalCanonicalKernel e he.1 P R) := by
  constructor
  intro x
  rw [isProbabilityMeasure_iff, conditionalCanonicalKernel_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply]
  all_goals try measurability
  have h0 : (((P false).prod (R true)).map (fun z => (false, z))) x Set.univ = 1 := by
    letI := hP false
    letI := hR true
    rw [Kernel.map_apply _ (by fun_prop)]
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    exact measure_univ
  have h1 : (((R false).prod (P true)).map (fun z => (true, z))) x Set.univ = 1 := by
    letI := hR false
    letI := hP true
    rw [Kernel.map_apply _ (by fun_prop)]
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    exact measure_univ
  rw [h0, h1]
  simp only [smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (he.2.1 x false).1, he.2.2]
  · simp
  · exact (he.2.1 x true).1

/-- For the specified model objects, [the stated conditions](hyp:he,hP,hR), [the stated mathematical relationship holds](goal). -/
-- @node: conditionalCanonicalKernel_arm
lemma conditionalCanonicalKernel_arm {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : Bool → X → ℝ) (he : ∀ a, Measurable (e a))
    (P R : Bool → Kernel X Y) (hP : ∀ a, IsMarkovKernel (P a))
    (hR : ∀ a, IsMarkovKernel (R a)) (x : X) (a : Bool) :
    conditionalCanonicalKernel e he P R x {z | z.1 = a} = ENNReal.ofReal (e a x) := by
  have hm0 : Measurable fun z : Y × Y => (false, z) := by fun_prop
  have hm1 : Measurable fun z : Y × Y => (true, z) := by fun_prop
  have hs : MeasurableSet {z : Bool × Y × Y | z.1 = a} :=
    (measurableSet_singleton a).preimage measurable_fst
  rw [conditionalCanonicalKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Kernel.map_apply' _ hm0 _ hs, Kernel.map_apply' _ hm1 _ hs]
  all_goals try measurability
  cases a
  ·
    letI := hP false
    letI := hR true
    simp [Kernel.prod_apply, Measure.map_apply, hm0, hm1]
  · letI := hR false
    letI := hP true
    simp [measure_univ]

/-- For the specified model objects, [the stated conditions](hyp:he,hP,hR,hB), [the stated mathematical relationship holds](goal). -/
-- @node: conditionalCanonicalKernel_armOutcome
lemma conditionalCanonicalKernel_armOutcome {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : Bool → X → ℝ) (he : ∀ a, Measurable (e a))
    (P R : Bool → Kernel X Y) (hP : ∀ a, IsMarkovKernel (P a))
    (hR : ∀ a, IsMarkovKernel (R a)) (x : X) (a : Bool)
    (B : Set Y) (hB : MeasurableSet B) :
    conditionalCanonicalKernel e he P R x {z | z.1 = a ∧
      (if z.1 then z.2.2 else z.2.1) ∈ B} =
      ENNReal.ofReal (e a x) * P a x B := by
  have hm0 : Measurable fun z : Y × Y => (false, z) := by fun_prop
  have hm1 : Measurable fun z : Y × Y => (true, z) := by fun_prop
  have hsel : Measurable (fun z : Bool × Y × Y =>
      if z.1 then z.2.2 else z.2.1) := by
    apply Measurable.ite (p := fun z : Bool × Y × Y => z.1 = true)
    · exact (measurableSet_singleton true).preimage measurable_fst
    · fun_prop
    · fun_prop
  have hs : MeasurableSet {z : Bool × Y × Y | z.1 = a ∧
      (if z.1 then z.2.2 else z.2.1) ∈ B} :=
    ((measurableSet_singleton a).preimage measurable_fst).inter (hB.preimage hsel)
  rw [conditionalCanonicalKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Kernel.map_apply' _ hm0 _ hs, Kernel.map_apply' _ hm1 _ hs]
  all_goals try measurability
  cases a
  · letI := hP false
    letI := hR true
    simp [Kernel.prod_apply, show {a : Y × Y | a.1 ∈ B} = B ×ˢ Set.univ by
      ext
      simp, Measure.prod_prod]
  · letI := hR false
    letI := hP true
    simp [Kernel.prod_apply, show {a : Y × Y | a.2 ∈ B} = Set.univ ×ˢ B by
      ext
      simp, Measure.prod_prod]

/-- For the specified model objects, [the stated conditions](hyp:he,hP,hR,hB), [the stated mathematical relationship holds](goal). -/
-- @node: conditionalCanonicalKernel_potential
lemma conditionalCanonicalKernel_potential {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : Bool → X → ℝ) (he : ∀ a, Measurable (e a))
    (P R : Bool → Kernel X Y) (hP : ∀ a, IsMarkovKernel (P a))
    (hR : ∀ a, IsMarkovKernel (R a)) (x : X) (a : Bool)
    (B : Set Y) (hB : MeasurableSet B) :
    conditionalCanonicalKernel e he P R x
        {z | potentialOutcome a (z.1, z.2.1, z.2.2) ∈ B} =
      ENNReal.ofReal (e a x) * P a x B +
        ENNReal.ofReal (e (!a) x) * R a x B := by
  have hm0 : Measurable fun z : Y × Y => (false, z) := by fun_prop
  have hm1 : Measurable fun z : Y × Y => (true, z) := by fun_prop
  have hs : MeasurableSet
      {z : Bool × Y × Y | potentialOutcome a (z.1, z.2.1, z.2.2) ∈ B} := by
    cases a
    · change MeasurableSet {z : Bool × Y × Y | z.2.1 ∈ B}
      exact hB.preimage (measurable_fst.comp measurable_snd)
    · change MeasurableSet {z : Bool × Y × Y | z.2.2 ∈ B}
      exact hB.preimage (measurable_snd.comp measurable_snd)
  rw [conditionalCanonicalKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Kernel.map_apply' _ hm0 _ hs, Kernel.map_apply' _ hm1 _ hs]
  all_goals try measurability
  cases a
  · letI := hP false
    letI := hR true
    letI := hR false
    simp [potentialOutcome, Kernel.prod_apply,
      show {a : Y × Y | a.1 ∈ B} = B ×ˢ Set.univ by ext; simp,
      Measure.prod_prod]
  · letI := hP false
    letI := hR true
    letI := hP true
    simp [potentialOutcome, Kernel.prod_apply,
      show {a : Y × Y | a.2 ∈ B} = Set.univ ×ˢ B by ext; simp,
      Measure.prod_prod]
    ac_rfl

/-- For [the stated conditions](hyp:e,P,R,a), [the conditionalCanonicalMixtureKernel object](goal) is defined as specified. -/
-- @node: conditionalCanonicalMixtureKernel
noncomputable def conditionalCanonicalMixtureKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : Bool → X → ℝ) (he : ∀ a, Measurable (e a))
    (P R : Bool → Kernel X Y) (a : Bool) : Kernel X Y :=
  { toFun := fun x => ENNReal.ofReal (e a x) • P a x +
      ENNReal.ofReal (e (!a) x) • R a x
    measurable' := by
      apply Measure.measurable_of_measurable_coe
      intro B hB
      simp only [Measure.add_apply, Measure.smul_apply]
      have hPm : Measurable fun x => P a x B := Kernel.measurable_coe (P a) hB
      have hRm : Measurable fun x => R a x B := Kernel.measurable_coe (R a) hB
      fun_prop }

/-- For the specified model objects, [the stated conditions](hyp:he), [the stated mathematical relationship holds](goal). -/
-- @node: conditionalCanonicalMixtureKernel_apply
lemma conditionalCanonicalMixtureKernel_apply {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : Bool → X → ℝ) (he : ∀ a, Measurable (e a))
    (P R : Bool → Kernel X Y) (a : Bool) (x : X) :
    conditionalCanonicalMixtureKernel e he P R a x =
      ENNReal.ofReal (e a x) • P a x + ENNReal.ofReal (e (!a) x) • R a x := rfl

/-- For the specified model objects, [the stated conditions](hyp:he,hP,hR), [the stated mathematical relationship holds](goal). -/
-- @node: conditionalCanonicalMixtureKernel_markov
lemma conditionalCanonicalMixtureKernel_markov {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : Bool → X → ℝ) (P R : Bool → Kernel X Y)
    (he : PropensitySystem e) (hP : ∀ a, IsMarkovKernel (P a))
    (hR : ∀ a, IsMarkovKernel (R a)) (a : Bool) :
    IsMarkovKernel (conditionalCanonicalMixtureKernel e he.1 P R a) := by
  constructor
  intro x
  rw [isProbabilityMeasure_iff, conditionalCanonicalMixtureKernel_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply]
  all_goals try measurability
  letI := hP a
  letI := hR a
  rw [measure_univ, measure_univ]
  simp only [smul_eq_mul, mul_one]
  cases a
  · simp only [Bool.not_false]
    rw [← ENNReal.ofReal_add (he.2.1 x false).1, he.2.2]
    · simp
    · exact (he.2.1 x true).1
  · simp only [Bool.not_true]
    rw [add_comm, ← ENNReal.ofReal_add (he.2.1 x false).1, he.2.2]
    · simp
    · exact (he.2.1 x true).1

/-- For [the stated conditions](hyp:muX,e,P,R), [the conditionalCanonicalBowWitness object](goal) is defined as specified. -/
-- @node: conditionalCanonicalBowWitness
noncomputable def conditionalCanonicalBowWitness {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (muX : Measure X) [IsProbabilityMeasure muX]
    (e : Bool → X → ℝ) (P R : Bool → Kernel X Y)
    (he : PropensitySystem e) (hP : ∀ a, IsMarkovKernel (P a))
    (hR : ∀ a, IsMarkovKernel (R a)) : CondBowWitness X Y where
  law := muX.compProd (conditionalCanonicalKernel e he.1 P R)
  probability := by
    letI := conditionalCanonicalKernel_markov e P R he hP hR
    infer_instance
  realizedOutcome := fun z => if z.2.1 then z.2.2.2 else z.2.2.1
  covariateLaw := muX
  condProp := e
  condArmLaw := P
  condIntervLaw := fun a => conditionalCanonicalMixtureKernel e he.1 P R a
  condArmLaw_markov := hP
  condIntervLaw_markov := conditionalCanonicalMixtureKernel_markov e P R he hP hR

/-- For the specified model objects, [the stated conditions](hyp:he,hP,hR), [the stated mathematical relationship holds](goal). -/
-- @node: conditionalCanonicalBowWitness_consistency
lemma conditionalCanonicalBowWitness_consistency {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (muX : Measure X) [IsProbabilityMeasure muX]
    (e : Bool → X → ℝ) (P R : Bool → Kernel X Y)
    (he : PropensitySystem e) (hP : ∀ a, IsMarkovKernel (P a))
    (hR : ∀ a, IsMarkovKernel (R a)) :
    CondConsistency (conditionalCanonicalBowWitness muX e P R he hP hR) := by
  filter_upwards [] with z
  rfl

/-- For the specified model objects, [the stated conditions](hyp:he,hP,hR), [the stated mathematical relationship holds](goal). -/
-- @node: conditionalCanonicalBowWitness_architecture
lemma conditionalCanonicalBowWitness_architecture {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (muX : Measure X) [IsProbabilityMeasure muX]
    (e : Bool → X → ℝ) (P R : Bool → Kernel X Y)
    (he : PropensitySystem e) (hP : ∀ a, IsMarkovKernel (P a))
    (hR : ∀ a, IsMarkovKernel (R a)) :
    CondBowArchitecture (conditionalCanonicalBowWitness muX e P R he hP hR) := by
  have heMeas : ∀ a, Measurable (e a) := he.1
  letI := conditionalCanonicalKernel_markov e P R he hP hR
  simp only [conditionalCanonicalBowWitness]
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · intro C hC
    rw [show {z : X × Bool × Y × Y | z.1 ∈ C} =
        C ×ˢ Set.univ by ext; simp, Measure.compProd_apply_prod hC MeasurableSet.univ]
    simp
  · intro C a hC
    change (muX.compProd (conditionalCanonicalKernel e heMeas P R))
        {z : X × Bool × Y × Y | z.1 ∈ C ∧ z.2.1 = a} =
      ∫⁻ x in C, ENNReal.ofReal (e a x) ∂muX
    have hT : MeasurableSet {u : Bool × Y × Y | u.1 = a} :=
      (measurableSet_singleton a).preimage measurable_fst
    rw [show {z : X × Bool × Y × Y | z.1 ∈ C ∧ z.2.1 = a} =
        C ×ˢ {u : Bool × Y × Y | u.1 = a} by ext; simp]
    calc
      _ = ∫⁻ x in C, conditionalCanonicalKernel e heMeas P R x {u : Bool × Y × Y | u.1 = a}
          ∂muX := Measure.compProd_apply_prod hC hT
      _ = _ := by simp_rw [conditionalCanonicalKernel_arm e heMeas P R hP hR]
  · intro C B a hC hB
    change (muX.compProd (conditionalCanonicalKernel e heMeas P R))
        {z : X × Bool × Y × Y | z.1 ∈ C ∧ z.2.1 = a ∧
          (if z.2.1 then z.2.2.2 else z.2.2.1) ∈ B} =
      ∫⁻ x in C, ENNReal.ofReal (e a x) * P a x B ∂muX
    have hsel : Measurable (fun u : Bool × Y × Y =>
        if u.1 then u.2.2 else u.2.1) := by
      apply Measurable.ite (p := fun u : Bool × Y × Y => u.1 = true)
      · exact (measurableSet_singleton true).preimage measurable_fst
      · fun_prop
      · fun_prop
    have hT : MeasurableSet {u : Bool × Y × Y | u.1 = a ∧
        (if u.1 then u.2.2 else u.2.1) ∈ B} :=
      ((measurableSet_singleton a).preimage measurable_fst).inter (hB.preimage hsel)
    rw [show {z : X × Bool × Y × Y | z.1 ∈ C ∧ z.2.1 = a ∧
          (if z.2.1 then z.2.2.2 else z.2.2.1) ∈ B} =
        C ×ˢ {u : Bool × Y × Y | u.1 = a ∧
          (if u.1 then u.2.2 else u.2.1) ∈ B} by ext; rfl]
    calc
      _ = ∫⁻ x in C, conditionalCanonicalKernel e heMeas P R x
          {u : Bool × Y × Y | u.1 = a ∧
            (if u.1 then u.2.2 else u.2.1) ∈ B} ∂muX :=
        Measure.compProd_apply_prod hC hT
      _ = _ := by
        simp_rw [conditionalCanonicalKernel_armOutcome e heMeas P R hP hR _ _ B hB]
  · intro C B a hC hB
    change (muX.compProd (conditionalCanonicalKernel e heMeas P R))
        {z : X × Bool × Y × Y | z.1 ∈ C ∧
          potentialOutcome a (z.2.1, z.2.2.1, z.2.2.2) ∈ B} =
      ∫⁻ x in C, conditionalCanonicalMixtureKernel e heMeas P R a x B ∂muX
    have hT : MeasurableSet {u : Bool × Y × Y |
        potentialOutcome a (u.1, u.2.1, u.2.2) ∈ B} := by
      cases a
      · change MeasurableSet {u : Bool × Y × Y | u.2.1 ∈ B}
        exact hB.preimage (measurable_fst.comp measurable_snd)
      · change MeasurableSet {u : Bool × Y × Y | u.2.2 ∈ B}
        exact hB.preimage (measurable_snd.comp measurable_snd)
    rw [show {z : X × Bool × Y × Y | z.1 ∈ C ∧
          potentialOutcome a (z.2.1, z.2.2.1, z.2.2.2) ∈ B} =
        C ×ˢ {u : Bool × Y × Y |
          potentialOutcome a (u.1, u.2.1, u.2.2) ∈ B} by ext; rfl]
    calc
      _ = ∫⁻ x in C, conditionalCanonicalKernel e heMeas P R x
          {u : Bool × Y × Y |
            potentialOutcome a (u.1, u.2.1, u.2.2) ∈ B} ∂muX :=
        Measure.compProd_apply_prod hC hT
      _ = _ := by
        simp_rw [conditionalCanonicalKernel_potential e heMeas P R hP hR _ a B hB]
        rfl

/-- For [the stated conditions](hyp:S,e,P,Q), [the conditionalResidualKernel object](goal) is defined as specified. -/
-- @node: conditionalResidualKernel
noncomputable def conditionalResidualKernel {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : Set X) (hS : MeasurableSet S) (e : X → ℝ) (heMeas : Measurable e)
    (P Q : Kernel X Y) (hP : IsMarkovKernel P) (hQ : IsMarkovKernel Q)
    (hle : ∀ x ∈ S, ENNReal.ofReal (e x) • P x ≤ Q x) :
    Kernel X Y := by
  classical
  letI := hP
  letI := hQ
  exact
    { toFun := fun x => if x ∈ S then
        (ENNReal.ofReal (1 - e x))⁻¹ • (Q x - ENNReal.ofReal (e x) • P x)
      else Q x
      measurable' := by
        apply Measure.measurable_of_measurable_coe
        intro B hB
        have hPm : Measurable (fun x => P x B) := Kernel.measurable_coe P hB
        have hQm : Measurable (fun x => Q x B) := Kernel.measurable_coe Q hB
        have hFormula : Measurable (fun x =>
            (ENNReal.ofReal (1 - e x))⁻¹ *
              (Q x B - ENNReal.ofReal (e x) * P x B)) := by fun_prop
        rw [show (fun x => (if x ∈ S then
              (ENNReal.ofReal (1 - e x))⁻¹ •
                (Q x - ENNReal.ofReal (e x) • P x) else Q x) B) =
            fun x => if x ∈ S then
              (ENNReal.ofReal (1 - e x))⁻¹ *
                (Q x B - ENNReal.ofReal (e x) * P x B) else Q x B by
          funext x
          by_cases hx : x ∈ S
          · simp only [hx, ↓reduceIte, Measure.smul_apply]
            letI : IsFiniteMeasure (ENNReal.ofReal (e x) • P x) :=
              (P x).smul_finite ENNReal.ofReal_ne_top
            rw [Measure.sub_apply hB (hle x hx), Measure.smul_apply]
            simp only [smul_eq_mul]
          · simp [hx]]
        exact hFormula.piecewise hS hQm }

/-- For the specified model objects, [the stated conditions](hyp:hS,heMeas,hle,he,hP,hQ), [the stated mathematical relationship holds](goal). -/
-- @node: conditionalResidualKernel_markov
lemma conditionalResidualKernel_markov {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : Set X) (hS : MeasurableSet S) (e : X → ℝ) (heMeas : Measurable e)
    (P Q : Kernel X Y) (hle : ∀ x ∈ S, ENNReal.ofReal (e x) • P x ≤ Q x)
    (he : ∀ x, e x ∈ Set.Ioo 0 1)
    (hP : IsMarkovKernel P) (hQ : IsMarkovKernel Q) :
    IsMarkovKernel (conditionalResidualKernel S hS e heMeas P Q hP hQ hle) := by
  classical
  letI := hP
  letI := hQ
  constructor
  intro x
  rw [isProbabilityMeasure_iff]
  by_cases hx : x ∈ S
  · rw [show conditionalResidualKernel S hS e heMeas P Q hP hQ hle x =
        (ENNReal.ofReal (1 - e x))⁻¹ •
          (Q x - ENNReal.ofReal (e x) • P x) by
            simp [conditionalResidualKernel, hx],
      Measure.smul_apply]
    letI : IsFiniteMeasure (ENNReal.ofReal (e x) • P x) :=
      (P x).smul_finite ENNReal.ofReal_ne_top
    rw [Measure.sub_apply MeasurableSet.univ (hle x hx),
      measure_univ, Measure.smul_apply]
    rw [measure_univ]
    simp only [smul_eq_mul, mul_one]
    have he0 : 0 ≤ e x := (he x).1.le
    have he1 : 0 < 1 - e x := sub_pos.mpr (he x).2
    rw [show 1 - ENNReal.ofReal (e x) = ENNReal.ofReal (1 - e x) by
      rw [ENNReal.ofReal_sub 1 he0, ENNReal.ofReal_one],
      ENNReal.inv_mul_cancel]
    exacts [ENNReal.ofReal_ne_zero_iff.mpr he1, ENNReal.ofReal_ne_top]
  · rw [show conditionalResidualKernel S hS e heMeas P Q hP hQ hle x = Q x by
      simp [conditionalResidualKernel, hx]]
    exact measure_univ

/-- For the specified model objects, [the stated conditions](hyp:hS,heMeas,hle,hP,hQ,he,hx), [the stated mathematical relationship holds](goal). -/
-- @node: conditionalResidualKernel_mixture
lemma conditionalResidualKernel_mixture {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : Set X) (hS : MeasurableSet S) (e : X → ℝ) (heMeas : Measurable e)
    (P Q : Kernel X Y) (hle : ∀ x ∈ S, ENNReal.ofReal (e x) • P x ≤ Q x)
    (hP : IsMarkovKernel P) (hQ : IsMarkovKernel Q)
    (he : ∀ x, e x ∈ Set.Ioo 0 1) (x : X) (hx : x ∈ S) :
    Q x = ENNReal.ofReal (e x) • P x +
      ENNReal.ofReal (1 - e x) •
        conditionalResidualKernel S hS e heMeas P Q hP hQ hle x := by
  classical
  letI := hP
  letI := hQ
  ext B hB
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  all_goals try measurability
  rw [show conditionalResidualKernel S hS e heMeas P Q hP hQ hle x =
      (ENNReal.ofReal (1 - e x))⁻¹ •
        (Q x - ENNReal.ofReal (e x) • P x) by
          simp [conditionalResidualKernel, hx],
    Measure.smul_apply]
  letI : IsFiniteMeasure (ENNReal.ofReal (e x) • P x) :=
    (P x).smul_finite ENNReal.ofReal_ne_top
  rw [Measure.sub_apply hB (hle x hx), Measure.smul_apply]
  simp only [smul_eq_mul]
  have hc0 : ENNReal.ofReal (1 - e x) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr (he x).2)
  have hcT : ENNReal.ofReal (1 - e x) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hcT, one_mul]
  have hleB : ENNReal.ofReal (e x) * P x B ≤ Q x B := by
    simpa only [Measure.smul_apply, smul_eq_mul] using (hle x hx) B
  exact (add_tsub_cancel_of_le hleB).symm

/-- For the specified model objects, [the stated conditions](hyp:hAm,hd,hA), [the stated mathematical relationship holds](goal). -/
-- @node: measure_le_of_measureDense
lemma measure_le_of_measureDense {Y : Type*} [MeasurableSpace Y]
    (mu nu : Measure Y) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (A : Set (Set Y)) (hAm : ∀ B ∈ A, MeasurableSet B)
    (hd : Measure.MeasureDense (mu + nu) A)
    (hA : ∀ B ∈ A, mu B ≤ nu B) : mu ≤ nu := by
  rw [Measure.le_iff]
  intro B hB
  apply (ENNReal.toReal_le_toReal (measure_ne_top mu B) (measure_ne_top nu B)).mp
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨C, hCA, hclose⟩ := hd.approx B hB (measure_ne_top (mu + nu) B) (eps / 2)
    (half_pos heps)
  have hC := hAm C hCA
  have hcloseR : ENNReal.toReal ((mu + nu) (symmDiff B C)) < eps / 2 := by
    rw [← ENNReal.toReal_ofReal (half_pos heps).le]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top (mu + nu) (symmDiff B C))
      ENNReal.ofReal_ne_top).mpr hclose
  have hmuDiff : |mu.real B - mu.real C| < eps / 2 :=
    (abs_measureReal_sub_le_measureReal_symmDiff hB.nullMeasurableSet
      hC.nullMeasurableSet).trans_lt <|
        ((ENNReal.toReal_le_toReal (measure_ne_top mu (symmDiff B C))
          (measure_ne_top (mu + nu) (symmDiff B C))).mpr
          ((Measure.le_add_right (le_refl mu)) (symmDiff B C))).trans_lt hcloseR
  have hnuDiff : |nu.real B - nu.real C| < eps / 2 :=
    (abs_measureReal_sub_le_measureReal_symmDiff hB.nullMeasurableSet
      hC.nullMeasurableSet).trans_lt <|
        ((ENNReal.toReal_le_toReal (measure_ne_top nu (symmDiff B C))
          (measure_ne_top (mu + nu) (symmDiff B C))).mpr
          ((Measure.le_add_left (le_refl nu)) (symmDiff B C))).trans_lt hcloseR
  have hmuC : mu.real C ≤ nu.real C :=
    (ENNReal.toReal_le_toReal (measure_ne_top mu C) (measure_ne_top nu C)).mpr (hA C hCA)
  have h1 : mu.real B < mu.real C + eps / 2 := by
    linarith [(abs_lt.mp hmuDiff).2]
  have h2 : nu.real C < nu.real B + eps / 2 := by
    linarith [(abs_lt.mp hnuDiff).1]
  simp only [measureReal_def] at hmuC h1 h2
  linarith

/-- For the specified model objects, [the stated conditions](hyp:hArch,hCons,hgMeas,hgEq), [the stated mathematical relationship holds](goal). -/
-- @node: conditional_measureCap_ae
lemma conditional_measureCap_ae {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (w : CondBowWitness X Y) (hArch : CondBowArchitecture w)
    (hCons : CondConsistency w) (a : Bool) (g : X → ℝ) (hgMeas : Measurable g)
    (hgEq : g =ᵐ[w.covariateLaw] w.condProp a) :
    ∀ᵐ x ∂w.covariateLaw,
      ENNReal.ofReal (g x) • w.condArmLaw a x ≤ w.condIntervLaw a x := by
  letI := hArch.1
  letI := w.condArmLaw_markov a
  letI := w.condIntervLaw_markov a
  let G := MeasurableSpace.countableGeneratingSet Y
  let A := generateSetAlgebra G
  have hAc : A.Countable := countable_generateSetAlgebra
    MeasurableSpace.countable_countableGeneratingSet
  have hAm : ∀ B ∈ A, MeasurableSet B := by
    intro B hB
    rw [← MeasurableSpace.generateFrom_countableGeneratingSet (α := Y),
      ← generateFrom_generateSetAlgebra_eq]
    exact MeasurableSpace.measurableSet_generateFrom hB
  have hOne (B : Set Y) (hB : MeasurableSet B) :
      ∀ᵐ x ∂w.covariateLaw,
        ENNReal.ofReal (g x) * w.condArmLaw a x B ≤
          w.condIntervLaw a x B := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    · exact (ENNReal.measurable_ofReal.comp hgMeas).mul
        (Kernel.measurable_coe (w.condArmLaw a) hB)
    intro C hC _
    calc
      ∫⁻ x in C, ENNReal.ofReal (g x) * w.condArmLaw a x B ∂w.covariateLaw =
          ∫⁻ x in C, ENNReal.ofReal (w.condProp a x) * w.condArmLaw a x B
            ∂w.covariateLaw := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae hgEq] with x hx
        rw [hx]
      _ = w.law {z | z.1 ∈ C ∧ z.2.1 = a ∧ w.realizedOutcome z ∈ B} :=
        (hArch.2.2.2.1 C B a hC hB).symm
      _ ≤ w.law {z | z.1 ∈ C ∧
          potentialOutcome a (z.2.1, z.2.2.1, z.2.2.2) ∈ B} := by
        apply measure_mono_ae
        filter_upwards [hCons] with z hz
        intro hmem
        refine ⟨hmem.1, ?_⟩
        have hy := hmem.2.2
        rw [hz, hmem.2.1] at hy
        exact hy
      _ = ∫⁻ x in C, w.condIntervLaw a x B ∂w.covariateLaw :=
        hArch.2.2.2.2 C B a hC hB
  have hAll : ∀ᵐ x ∂w.covariateLaw, ∀ B : A,
      ENNReal.ofReal (g x) * w.condArmLaw a x B ≤
        w.condIntervLaw a x B := by
    letI := hAc.to_subtype
    rw [ae_all_iff]
    intro B
    exact hOne B (hAm B B.property)
  filter_upwards [hAll] with x hx
  let mu := ENNReal.ofReal (g x) • w.condArmLaw a x
  let nu := w.condIntervLaw a x
  letI : IsFiniteMeasure mu := (w.condArmLaw a x).smul_finite ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure nu := inferInstance
  apply measure_le_of_measureDense mu nu A hAm
  · exact Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite (mu + nu)
      isSetAlgebra_generateSetAlgebra <| by
        rw [generateFrom_generateSetAlgebra_eq,
          MeasurableSpace.generateFrom_countableGeneratingSet]
  intro B hBA
  simpa only [mu, nu, Measure.smul_apply, smul_eq_mul] using hx ⟨B, hBA⟩

end CausalSmith.SCM.PropensityLvSharpnessFrontier
