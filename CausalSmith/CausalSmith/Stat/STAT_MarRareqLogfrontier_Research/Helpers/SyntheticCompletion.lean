module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.BoundedRisk
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.Parameters
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Law-independent fair-coin completion of a discrete observational record. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

namespace SyntheticCompletion

open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def categoryLaw {d : ℕ} (P : ZengLaw d) : Measure (Fin d) :=
  P.1.map (fun r => r.1)

/-- For [the specified inputs and assumptions](hyp:d,P,x), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def propensity {d : ℕ} (P : ZengLaw d) (x : Fin d) : ℝ :=
  if 0 < zengCategory P x then zengArm P x true / zengCategory P x else 0

/-- For [the specified inputs and assumptions](hyp:d,P,x,b), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def outcomeMean {d : ℕ} (P : ZengLaw d) (x : Fin d) (b : Bool) : ℝ :=
  if 0 < zengArm P x b then
    P.1.real {r | r.1 = x ∧ r.2.1 = b ∧ r.2.2 = true} / zengArm P x b
  else 0

/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def parameters {d : ℕ} (P : ZengLaw d) : Parameters (Fin d) where
  μ := categoryLaw P
  μ_prob := by
    letI : IsProbabilityMeasure P.1 := P.2
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  e := propensity P
  q₀ := fun x => outcomeMean P x false
  q₁ := fun x => outcomeMean P x true
  he := by fun_prop
  hq₀ := by fun_prop
  hq₁ := by fun_prop
  he01 := by
    letI : IsProbabilityMeasure P.1 := P.2
    intro x
    rw [Set.mem_Icc]
    by_cases hx : 0 < zengCategory P x
    · simp only [propensity, if_pos hx]
      constructor
      · exact div_nonneg measureReal_nonneg (le_of_lt hx)
      · apply (div_le_one hx).2
        exact measureReal_mono (by intro r hr; exact hr.1) (measure_ne_top P.1 _)
    · simp [propensity, hx]
  hq₀01 := by
    letI : IsProbabilityMeasure P.1 := P.2
    intro x
    rw [Set.mem_Icc]
    by_cases hb : 0 < zengArm P x false
    · simp only [outcomeMean, if_pos hb]
      constructor
      · exact div_nonneg measureReal_nonneg (le_of_lt hb)
      · apply (div_le_one hb).2
        exact measureReal_mono (by intro r hr; exact ⟨hr.1, hr.2.1⟩)
          (measure_ne_top P.1 _)
    · simp [outcomeMean, hb]
  hq₁01 := by
    letI : IsProbabilityMeasure P.1 := P.2
    intro x
    rw [Set.mem_Icc]
    by_cases hb : 0 < zengArm P x true
    · simp only [outcomeMean, if_pos hb]
      constructor
      · exact div_nonneg measureReal_nonneg (le_of_lt hb)
      · apply (div_le_one hb).2
        exact measureReal_mono (by intro r hr; exact ⟨hr.1, hr.2.1⟩)
          (measure_ne_top P.1 _)
    · simp [outcomeMean, hb]

/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def fairCoin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true

/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
instance : IsProbabilityMeasure fairCoin := by
  refine ⟨?_⟩
  simp [fairCoin, ENNReal.inv_two_add_inv_two]

/-- For [the specified inputs and assumptions](hyp:d,z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def toFullRecord {d : ℕ}
    (z : FullCoord (Fin d) × Bool) : FullRecord d :=
  ⟨z.1.1, z.2, false, false, z.1.2.2.1, z.1.2.2.2, z.2 == z.1.2.1⟩

/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def fullMeasure {d : ℕ} (P : ZengLaw d) : Measure (FullRecord d) :=
  (((parameters P).fullLaw).prod fairCoin).map toFullRecord

/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma fullMeasure_probability {d : ℕ} (P : ZengLaw d) :
    IsProbabilityMeasure (fullMeasure P) := by
  letI : IsProbabilityMeasure (parameters P).fullLaw :=
    (parameters P).fullLaw_probability
  unfold fullMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def fullLaw {d : ℕ} (P : ZengLaw d) : FullLaw d :=
  ⟨fullMeasure P, fullMeasure_probability P⟩

/-- Given [the specified inputs and assumptions](hyp:d,P,x), [the stated mathematical conclusion holds](goal). -/
lemma arm_sum {d : ℕ} (P : ZengLaw d) (x : Fin d) :
    zengArm P x false + zengArm P x true = zengCategory P x := by
  letI : IsProbabilityMeasure P.1 := P.2
  rw [zengArm, zengArm, zengCategory, ← measureReal_union]
  · congr 1
    ext r
    cases h : r.2.1 <;> simp [h]
  · rw [Set.disjoint_left]
    simp
  · measurability

/-- Given [the specified inputs and assumptions](hyp:d,q,P,hP,x,hx,b), [the stated mathematical conclusion holds](goal). -/
lemma arm_pos {d : ℕ} {q : ℝ} (P : ZengLaw d)
    (hP : P ∈ zengDiscreteClass d q) (x : Fin d)
    (hx : 0 < zengCategory P x) (b : Bool) : 0 < zengArm P x b := by
  rcases hP with ⟨hq, hqhalf, hd, hbounds⟩
  cases b with
  | true => exact lt_of_lt_of_le (mul_pos hq hx) (hbounds x hx).1
  | false =>
      have hu := (hbounds x hx).2
      have hs := arm_sum P x
      have : q < 1 := by linarith
      nlinarith

/-- Given [the specified inputs and assumptions](hyp:d,P,x), [the stated mathematical conclusion holds](goal). -/
lemma categoryLaw_singleton_real {d : ℕ} (P : ZengLaw d) (x : Fin d) :
    (categoryLaw P).real {x} = zengCategory P x := by
  letI : IsProbabilityMeasure P.1 := P.2
  rw [categoryLaw, Measure.real, Measure.map_apply (by fun_prop) (by simp),
    zengCategory, measureReal_def]
  rfl

/-- Given [the specified inputs and assumptions](hyp:d,q,P,hP,x,hx,b), [the stated mathematical conclusion holds](goal). -/
lemma outcomeMean_eq_zengMean {d : ℕ} {q : ℝ} (P : ZengLaw d)
    (hP : P ∈ zengDiscreteClass d q) (x : Fin d)
    (hx : 0 < zengCategory P x) (b : Bool) :
    outcomeMean P x b = zengMean P x b hx := by
  have hb := arm_pos P hP x hx b
  simp [outcomeMean, zengMean, hb]

/-- Given [the specified inputs and assumptions](hyp:d,P,x,b), [the stated mathematical conclusion holds](goal). -/
lemma success_real_singleton {d : ℕ} (P : ZengLaw d) (x : Fin d) (b : Bool) :
    P.1.real {r | r.1 = x ∧ r.2.1 = b ∧ r.2.2 = true} =
      P.1.real (Set.singleton (x, b, true)) := by
  congr 1
  ext r
  rcases r with ⟨x', b', y'⟩
  change (x' = x ∧ b' = b ∧ y' = true) ↔
    (x', b', y') = (x, b, true)
  cases y' <;> simp

/-- Given [the specified inputs and assumptions](hyp:d,P,x,b), [the stated mathematical conclusion holds](goal). -/
lemma arm_real_split {d : ℕ} (P : ZengLaw d) (x : Fin d) (b : Bool) :
    zengArm P x b =
      P.1.real (Set.singleton (x, b, false)) +
      P.1.real (Set.singleton (x, b, true)) := by
  letI : IsProbabilityMeasure P.1 := P.2
  rw [zengArm, ← measureReal_union]
  · congr 1
    ext r
    rcases r with ⟨x', b', y'⟩
    change (x' = x ∧ b' = b) ↔
      (x', b', y') = (x, b, false) ∨ (x', b', y') = (x, b, true)
    cases y' <;> simp
  · rw [Set.disjoint_left]
    intro r hr₀ hr₁
    change r = (x, b, false) at hr₀
    change r = (x, b, true) at hr₁
    subst r
    exact Bool.noConfusion (congrArg (fun z => z.2.2) hr₁)
  · exact MeasurableSet.singleton _

/-- Given [the specified inputs and assumptions](hyp:d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma selected_eq {d : ℕ} {q : ℝ} (P : ZengLaw d)
    (hP : P ∈ zengDiscreteClass d q) :
    (parameters P).selected = P.1 := by
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure (parameters P).selected :=
    (parameters P).selected_probability
  apply Measure.ext_of_measureReal_singleton
  rintro ⟨x, b, y⟩
  have hcell := (parameters P).selected_cell ({x} : Set (Fin d)) (by simp) b y
  have hset : {z : SelectedCoord (Fin d) | z.1 ∈ ({x} : Set (Fin d)) ∧
      z.2.1 = b ∧ z.2.2 = y} = {(x, b, y)} := by
    ext z
    rcases z with ⟨x', b', y'⟩
    simp
  rw [hset] at hcell
  rw [MeasureTheory.lintegral_singleton] at hcell
  have hcellReal := congrArg ENNReal.toReal hcell
  rw [Measure.real, hcellReal, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  · change cellMass (propensity P x) (outcomeMean P x false)
      (outcomeMean P x true) b y * ((categoryLaw P) {x}).toReal = _
    change _ = P.1.real (Set.singleton (x, b, y))
    rw [show ((categoryLaw P) {x}).toReal = zengCategory P x by
      simpa [Measure.real] using categoryLaw_singleton_real P x]
    by_cases hx : 0 < zengCategory P x
    · have hbpos := arm_pos P hP x hx b
      have hcatne : zengCategory P x ≠ 0 := ne_of_gt hx
      have hbne : zengArm P x b ≠ 0 := ne_of_gt hbpos
      rw [show propensity P x = zengArm P x true / zengCategory P x by
        simp [propensity, hx]]
      rw [show outcomeMean P x false = zengMean P x false hx from
        outcomeMean_eq_zengMean P hP x hx false]
      rw [show outcomeMean P x true = zengMean P x true hx from
        outcomeMean_eq_zengMean P hP x hx true]
      have hsfalse := arm_real_split P x false
      have hstrue := arm_real_split P x true
      have hcat := arm_sum P x
      cases b <;> cases y <;>
        simp [cellMass, bitMass, zengMean, success_real_singleton] <;>
        field_simp <;>
        first
        | (rw [← hcat, hsfalse, hstrue]; ring)
        | (rw [← hcat, hsfalse]; ring)
        | (rw [hstrue]; ring)
        | (rw [hsfalse]; ring)
        | ring
    · have hcat0 : zengCategory P x = 0 :=
        le_antisymm (le_of_not_gt hx) measureReal_nonneg
      have hatom : P.1.real (Set.singleton (x, b, y)) = 0 := by
        have hsub : Set.singleton (x, b, y) ⊆ {r | r.1 = x} := by
          intro r hr
          change r = (x, b, y) at hr
          subst r
          rfl
        apply le_antisymm _ measureReal_nonneg
        apply le_trans (measureReal_mono hsub (measure_ne_top P.1 _))
        simpa [zengCategory] using le_of_eq hcat0
      simp [hcat0, hatom]
  · unfold cellMass
    apply mul_nonneg
    · exact bitMass_nonneg _ ((parameters P).he01 x) _
    · split
      · exact bitMass_nonneg _ ((parameters P).hq₁01 x) _
      · exact bitMass_nonneg _ ((parameters P).hq₀01 x) _

/-- Given [the specified inputs and assumptions](hyp:α,β,γ,μ,ν,f,hf), [the stated mathematical conclusion holds](goal). -/
lemma bind_map_eq_prod_map {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [Countable α]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (f : α → β → γ) (hf : Measurable (fun z : α × β => f z.1 z.2)) :
    μ.bind (fun x => ν.map (f x)) =
      (μ.prod ν).map (fun z => f z.1 z.2) := by
  ext s hs
  rw [Measure.bind_apply hs (measurable_of_countable _).aemeasurable,
    Measure.map_apply hf hs,
    Measure.prod_apply (hs.preimage hf)]
  apply lintegral_congr
  intro x
  have hfx : Measurable (f x) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hfx hs]
  rfl

/-- Given [the specified inputs and assumptions](hyp:p,q,hp,hq,y), [the stated mathematical conclusion holds](goal). -/
lemma ofReal_bernoulli_marginal (p q : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (y : Bool) :
    ENNReal.ofReal (p * bitMass q y) +
        ENNReal.ofReal ((1 - p) * bitMass q y) =
      ENNReal.ofReal (bitMass q y) := by
  have hbp : 0 ≤ bitMass p false := bitMass_nonneg p hp false
  have hpt : 0 ≤ bitMass p true := bitMass_nonneg p hp true
  have hbq : 0 ≤ bitMass q y := bitMass_nonneg q hq y
  rw [← ENNReal.ofReal_add (mul_nonneg hp.1 hbq)
    (mul_nonneg (sub_nonneg.mpr hp.2) hbq)]
  congr 1
  cases y <;> simp [bitMass] <;> ring

/-- Given [the specified inputs and assumptions](hyp:q₀,q₁,hq₀,hq₁,a,y), [the stated mathematical conclusion holds](goal). -/
lemma remainingPairSetMass_selected (q₀ q₁ : ℝ)
    (hq₀ : q₀ ∈ Set.Icc (0 : ℝ) 1) (hq₁ : q₁ ∈ Set.Icc (0 : ℝ) 1)
    (a y : Bool) :
    remainingPairSetMass q₀ q₁ {v | (if a then v.2 else v.1) = y} =
      ENNReal.ofReal (bitMass (if a then q₁ else q₀) y) := by
  cases a with
  | false =>
      simpa [remainingPairSetMass, bitMass, mul_comm] using
        (ofReal_bernoulli_marginal q₁ q₀ hq₁ hq₀ y)
  | true =>
      simpa [remainingPairSetMass, bitMass, add_comm] using
        (ofReal_bernoulli_marginal q₀ q₁ hq₀ hq₁ y)

/-- Given [the specified inputs and assumptions](hyp:d,P,x,b,a,y), [the stated mathematical conclusion holds](goal). -/
lemma latent_cell_mass {d : ℕ} (P : ZengLaw d)
    (x : Fin d) (b a y : Bool) :
    (parameters P).fullLaw
        {z | z.1 = x ∧ z.2.1 = b ∧
          (if a then z.2.2.2 else z.2.2.1) = y} =
      ENNReal.ofReal
        (bitMass (propensity P x) b *
          bitMass (if a then outcomeMean P x true else outcomeMean P x false) y) *
        (categoryLaw P) {x} := by
  let t : Set (Bool × Bool) :=
    {v | (if a then v.2 else v.1) = y}
  have h := (parameters P).conditional_independence_finite
    ({x} : Set (Fin d)) (by simp) ({b} : Set Bool) t
  have hset : {z : FullCoord (Fin d) |
      z.1 ∈ ({x} : Set (Fin d)) ∧ z.2.1 ∈ ({b} : Set Bool) ∧ z.2.2 ∈ t} =
      {z | z.1 = x ∧ z.2.1 = b ∧
        (if a then z.2.2.2 else z.2.2.1) = y} := by
    ext z
    simp [t]
  rw [hset] at h
  rw [h, MeasureTheory.lintegral_singleton]
  have he := (parameters P).he01 x
  have hq₀ := (parameters P).hq₀01 x
  have hq₁ := (parameters P).hq₁01 x
  rw [show t = {v | (if a then v.2 else v.1) = y} from rfl,
    remainingPairSetMass_selected _ _ hq₀ hq₁]
  have hb : 0 ≤ bitMass (propensity P x) b :=
    bitMass_nonneg _ he b
  rw [show firstMarkSetMass ((parameters P).e x) {b} =
      ENNReal.ofReal (bitMass (propensity P x) b) by
        change firstMarkSetMass (propensity P x) {b} = _
        cases b <;> simp [firstMarkSetMass, bitMass]]
  rw [← ENNReal.ofReal_mul hb]
  rfl

/-- Given [the specified inputs and assumptions](hyp:d,P,a,x,r,y), [the stated mathematical conclusion holds](goal). -/
lemma full_joint_mass {d : ℕ} (P : ZengLaw d)
    (a : Bool) (x : Fin d) (r y : Bool) :
    (fullMeasure P)
        {w | inCell w (a, x, false) ∧ w.R = r ∧ w.Y = y} =
      (parameters P).fullLaw
          {z | z.1 = x ∧ z.2.1 = (if r then a else !a) ∧
            (if a then z.2.2.2 else z.2.2.1) = y} *
        fairCoin {a} := by
  let E : Set (FullCoord (Fin d)) :=
    {z | z.1 = x ∧ z.2.1 = (if r then a else !a) ∧
      (if a then z.2.2.2 else z.2.2.1) = y}
  have hpre : toFullRecord ⁻¹'
      {w | inCell w (a, x, false) ∧ w.R = r ∧ w.Y = y} =
      E ×ˢ ({a} : Set Bool) := by
    ext z
    rcases z with ⟨⟨x', b, y₀, y₁⟩, a'⟩
    cases a <;> cases a' <;> cases b <;> cases r <;>
      cases y₀ <;> cases y₁ <;> cases y <;>
      simp [E, toFullRecord, inCell, FullRecord.S, FullRecord.Y]
  rw [fullMeasure, Measure.map_apply (by fun_prop) (by simp), hpre,
    Measure.prod_prod]

/-- Given [the specified inputs and assumptions](hyp:d,P,a,x,r,y), [the stated mathematical conclusion holds](goal). -/
lemma full_joint_mass_real {d : ℕ} (P : ZengLaw d)
    (a : Bool) (x : Fin d) (r y : Bool) :
    (fullMeasure P).real
        {w | inCell w (a, x, false) ∧ w.R = r ∧ w.Y = y} =
      (1 / 2 : ℝ) * zengCategory P x *
        bitMass (propensity P x) (if r then a else !a) *
        bitMass (if a then outcomeMean P x true else outcomeMean P x false) y := by
  rw [Measure.real, full_joint_mass, latent_cell_mass]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  · rw [show ((categoryLaw P) {x}).toReal = zengCategory P x by
      simpa [Measure.real] using categoryLaw_singleton_real P x]
    have hcoin : (fairCoin {a}).toReal = (1 / 2 : ℝ) := by
      cases a <;> simp [fairCoin]
    rw [hcoin]
    ring
  · exact mul_nonneg
      (bitMass_nonneg _ ((parameters P).he01 x) _)
      (bitMass_nonneg _ (by
        split
        · exact (parameters P).hq₁01 x
        · exact (parameters P).hq₀01 x) _)

/-- Given [the specified inputs and assumptions](hyp:α,μ,E,hE,f,hf), [the stated mathematical conclusion holds](goal). -/
lemma measureReal_split_bool {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (E : Set α) (hE : MeasurableSet E)
    (f : α → Bool) (hf : Measurable f) :
    μ.real E = ∑ b : Bool, μ.real {w | w ∈ E ∧ f w = b} := by
  rw [Fintype.sum_bool, ← measureReal_union]
  · congr 1
    ext w
    cases h : f w <;> simp [h]
  · rw [Set.disjoint_left]
    intro a ha hb
    simp only [Set.mem_setOf_eq] at ha hb
    simp [ha.2] at hb
  · exact hE.inter (measurableSet_eq_fun hf measurable_const)

/-- Given [the specified inputs and assumptions](hyp:d,P,a,x), [the stated mathematical conclusion holds](goal). -/
lemma full_cellProb_false {d : ℕ} (P : ZengLaw d) (a : Bool) (x : Fin d) :
    cellProb (fullLaw P) (a, x, false) =
      (1 / 2 : ℝ) * zengCategory P x := by
  letI : IsProbabilityMeasure (fullMeasure P) := fullMeasure_probability P
  unfold cellProb
  change (fullMeasure P).real {r | inCell r (a, x, false)} = _
  rw [measureReal_split_bool (fullMeasure P)
    {w | inCell w (a, x, false)} (by simp) FullRecord.R (by fun_prop)]
  simp only [Fintype.sum_bool, Set.mem_setOf_eq, and_assoc]
  rw [measureReal_split_bool (fullMeasure P)
      {w | inCell w (a, x, false) ∧ w.R = false} (by simp)
      FullRecord.Y (by fun_prop),
    measureReal_split_bool (fullMeasure P)
      {w | inCell w (a, x, false) ∧ w.R = true} (by simp)
      FullRecord.Y (by fun_prop)]
  simp only [Fintype.sum_bool, Set.mem_setOf_eq, and_assoc]
  simp_rw [full_joint_mass_real]
  cases a <;> simp [bitMass] <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,P,a,x), [the stated mathematical conclusion holds](goal). -/
lemma full_arrived_false {d : ℕ} (P : ZengLaw d) (a : Bool) (x : Fin d) :
    arrivedCell (fullLaw P) (a, x, false) =
      (1 / 2 : ℝ) * zengCategory P x * bitMass (propensity P x) a := by
  letI : IsProbabilityMeasure (fullMeasure P) := fullMeasure_probability P
  unfold arrivedCell
  change (fullMeasure P).real {r | inCell r (a, x, false) ∧ r.R = true} = _
  rw [measureReal_split_bool (fullMeasure P)
    {w | inCell w (a, x, false) ∧ w.R = true} (by simp)
    FullRecord.Y (by fun_prop)]
  simp only [Fintype.sum_bool, Set.mem_setOf_eq, and_assoc]
  simp_rw [full_joint_mass_real]
  cases a <;> simp [bitMass] <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,P,a,x,r), [the stated mathematical conclusion holds](goal). -/
lemma full_cellR_false {d : ℕ} (P : ZengLaw d)
    (a : Bool) (x : Fin d) (r : Bool) :
    (fullMeasure P).real {w | inCell w (a, x, false) ∧ w.R = r} =
      (1 / 2 : ℝ) * zengCategory P x *
        bitMass (propensity P x) (if r then a else !a) := by
  letI : IsProbabilityMeasure (fullMeasure P) := fullMeasure_probability P
  rw [measureReal_split_bool (fullMeasure P)
    {w | inCell w (a, x, false) ∧ w.R = r} (by simp)
    FullRecord.Y (by fun_prop)]
  simp only [Fintype.sum_bool, Set.mem_setOf_eq, and_assoc]
  simp_rw [full_joint_mass_real]
  cases a <;> cases r <;> simp [bitMass] <;> ring

/-- Given [the specified inputs and assumptions](hyp:d,P,a,x,y), [the stated mathematical conclusion holds](goal). -/
lemma full_cellY_false {d : ℕ} (P : ZengLaw d)
    (a : Bool) (x : Fin d) (y : Bool) :
    (fullMeasure P).real {w | inCell w (a, x, false) ∧ w.Y = y} =
      (1 / 2 : ℝ) * zengCategory P x *
        bitMass (if a then outcomeMean P x true else outcomeMean P x false) y := by
  letI : IsProbabilityMeasure (fullMeasure P) := fullMeasure_probability P
  rw [measureReal_split_bool (fullMeasure P)
    {w | inCell w (a, x, false) ∧ w.Y = y} (by simp)
    FullRecord.R (by fun_prop)]
  simp only [Fintype.sum_bool, Set.mem_setOf_eq, and_assoc]
  have hreorder (r : Bool) :
      (fullMeasure P).real
          {w | inCell w (a, x, false) ∧ w.Y = y ∧ w.R = r} =
        (fullMeasure P).real
          {w | inCell w (a, x, false) ∧ w.R = r ∧ w.Y = y} := by
    congr 1
    ext w
    simp [and_left_comm, and_comm]
  rw [hreorder false, hreorder true, full_joint_mass_real, full_joint_mass_real]
  cases a <;> cases y <;>
    simp [Fintype.sum_bool, bitMass] <;> try ring_nf

/-- Given [the specified inputs and assumptions](hyp:Ω,X,Y,Z,μ,φ,f,g,hφ,hf,hg,h), [the stated mathematical conclusion holds](goal). -/
lemma indepFun_map {Ω X Y Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {μ : Measure Ω} {φ : Ω → X} {f : X → Y} {g : X → Z}
    (hφ : Measurable φ) (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun (f ∘ φ) (g ∘ φ) μ) : IndepFun f g (μ.map φ) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  rw [Measure.map_apply hφ ((hs.preimage hf).inter (ht.preimage hg)),
    Measure.map_apply hφ (hs.preimage hf), Measure.map_apply hφ (ht.preimage hg)]
  exact h s t hs ht

/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma fullLaw_randomized {d : ℕ} (P : ZengLaw d) :
    RandomizedIndependence (fullLaw P) := by
  let L := (parameters P).fullLaw
  letI : IsProbabilityMeasure L := (parameters P).fullLaw_probability
  have hsource : IndepFun (fun z : FullCoord (Fin d) × Bool => z.2)
      (fun z => z.1) (L.prod fairCoin) :=
    (indepFun_prod (μ := L) (ν := fairCoin) measurable_id measurable_id).symm
  apply indepFun_map (φ := toFullRecord) (by fun_prop) (by fun_prop) (by fun_prop)
  convert hsource.comp measurable_id
    (measurable_of_finite (fun z : FullCoord (Fin d) =>
      (z.1, false, false, z.2.2.1, z.2.2.2))) using 1 <;> rfl

/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma fullLaw_balanced {d : ℕ} (P : ZengLaw d) :
    BalancedRandomization (fullLaw P) := by
  letI : IsProbabilityMeasure (parameters P).fullLaw :=
    (parameters P).fullLaw_probability
  rw [BalancedRandomization]
  change (fullMeasure P).real {r : FullRecord d | r.A = true} = 1 / 2
  rw [Measure.real, fullMeasure,
    Measure.map_apply (by fun_prop) (by simp)]
  have hpre : toFullRecord ⁻¹' {r : FullRecord d | r.A = true} =
      Set.univ ×ˢ ({true} : Set Bool) := by
    ext z
    simp [toFullRecord]
  rw [hpre, Measure.prod_prod]
  simp [fairCoin]

/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma fullLaw_surrogate {d : ℕ} (P : ZengLaw d) :
    SurrogateConsistency (fullLaw P) := by
  filter_upwards [] with r
  rfl

/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma fullLaw_outcome {d : ℕ} (P : ZengLaw d) :
    OutcomeConsistency (fullLaw P) := by
  filter_upwards [] with r
  rfl

/-- Given [the specified inputs and assumptions](hyp:d,P,E,hE,htrue), [the stated mathematical conclusion holds](goal). -/
lemma fullMeasure_real_of_surrogate_true {d : ℕ} (P : ZengLaw d)
    (E : Set (FullRecord d)) (hE : MeasurableSet E)
    (htrue : ∀ w, w ∈ E → w.S = true) : (fullMeasure P).real E = 0 := by
  rw [Measure.real, fullMeasure, Measure.map_apply (by fun_prop) hE]
  have hpre : toFullRecord ⁻¹' E = ∅ := by
    ext z
    constructor
    · intro hz
      have h := htrue (toFullRecord z) hz
      have hf : (false : Bool) = true := by
        change (if z.2 then false else false) = true at h
        simpa using h
      exact Bool.noConfusion hf
    · simp
  rw [hpre]
  simp

/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma fullLaw_mar {d : ℕ} (P : ZengLaw d) : ArrivalMAR (fullLaw P) := by
  rintro ⟨a, x, s⟩ y r
  cases s with
  | false =>
      change (fullMeasure P).real
          {w | inCell w (a, x, false) ∧ w.R = r ∧ w.Y = y} *
          cellProb (fullLaw P) (a, x, false) =
        (fullMeasure P).real {w | inCell w (a, x, false) ∧ w.R = r} *
          (fullMeasure P).real {w | inCell w (a, x, false) ∧ w.Y = y}
      rw [full_joint_mass_real, full_cellProb_false, full_cellR_false,
        full_cellY_false]
      ring
  | true =>
      have hzero (E : Set (FullRecord d)) (hE : MeasurableSet E)
          (hsub : ∀ w, w ∈ E → inCell w (a, x, true)) :
          (fullMeasure P).real E = 0 :=
        fullMeasure_real_of_surrogate_true P E hE
          (fun w hw => (hsub w hw).2.2)
      change (fullMeasure P).real
          {w | inCell w (a, x, true) ∧ w.R = r ∧ w.Y = y} *
          cellProb (fullLaw P) (a, x, true) =
        (fullMeasure P).real {w | inCell w (a, x, true) ∧ w.R = r} *
          (fullMeasure P).real {w | inCell w (a, x, true) ∧ w.Y = y}
      rw [hzero _ (by simp) (by intro w hw; exact hw.1),
        hzero _ (by simp) (by intro w hw; exact hw.1),
        hzero _ (by simp) (by intro w hw; exact hw.1)]
      simp

/-- Given [the specified inputs and assumptions](hyp:d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma fullLaw_arrival {d : ℕ} {q : ℝ} (P : ZengLaw d)
    (hP : P ∈ zengDiscreteClass d q) : OccupiedCellArrival q (fullLaw P) := by
  rintro ⟨a, x, s⟩ hcell
  cases s with
  | true =>
      have hz : cellProb (fullLaw P) (a, x, true) = 0 := by
        unfold cellProb
        change (fullMeasure P).real {w | inCell w (a, x, true)} = 0
        exact fullMeasure_real_of_surrogate_true P _ (by simp)
          (by intro w hw; exact hw.2.2)
      rw [hz] at hcell
      exact (lt_irrefl 0 hcell).elim
  | false =>
      rw [full_cellProb_false, full_arrived_false]
      rw [full_cellProb_false] at hcell
      have hx : 0 < zengCategory P x := by nlinarith
      have hb := hP.2.2.2 x hx
      have hprop : propensity P x = zengArm P x true / zengCategory P x := by
        simp [propensity, hx]
      rw [hprop]
      cases a with
      | false =>
          simp only [bitMass, Bool.false_eq_true, if_false]
          have hdiv : q ≤ 1 - zengArm P x true / zengCategory P x := by
            have hu : zengArm P x true / zengCategory P x ≤ 1 - q :=
              (div_le_iff₀ hx).2 (by simpa [mul_comm] using hb.2)
            linarith
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left hdiv (le_of_lt hcell)
      | true =>
          simp only [bitMass, Bool.true_eq, if_true]
          have hdiv : q ≤ zengArm P x true / zengCategory P x :=
            (le_div_iff₀ hx).2 (by simpa [mul_comm] using hb.1)
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left hdiv (le_of_lt hcell)

/-- Given [the specified inputs and assumptions](hyp:d,q,P,hP,a,x), [the stated mathematical conclusion holds](goal). -/
lemma full_cellContribution_false {d : ℕ} {q : ℝ} (P : ZengLaw d)
    (hP : P ∈ zengDiscreteClass d q) (a : Bool) (x : Fin d) :
    cellContribution (fullLaw P) (a, x, false) =
      (1 / 2 : ℝ) * zengCategory P x *
        (if a then outcomeMean P x true else outcomeMean P x false) := by
  by_cases hx : 0 < zengCategory P x
  · have harr : 0 < arrivedCell (fullLaw P) (a, x, false) := by
      rw [full_arrived_false]
      have hb := hP.2.2.2 x hx
      have hq := hP.1
      have hbit : 0 < bitMass (propensity P x) a := by
        rw [show propensity P x = zengArm P x true / zengCategory P x by
          simp [propensity, hx]]
        cases a with
        | false =>
            simp only [bitMass, Bool.false_eq_true, if_false]
            have hu : zengArm P x true / zengCategory P x < 1 := by
              apply (div_lt_one hx).2
              nlinarith [hb.2]
            linarith
        | true =>
            simp only [bitMass, Bool.true_eq, if_true]
            exact div_pos (lt_of_lt_of_le (mul_pos hq hx) hb.1) hx
      positivity
    unfold cellContribution cellMean
    rw [if_pos harr, if_pos harr, full_cellProb_false]
    change (1 / 2 : ℝ) * zengCategory P x *
        ((fullMeasure P).real
          {r | inCell r (a, x, false) ∧ r.R = true ∧ r.Y = true} /
            arrivedCell (fullLaw P) (a, x, false)) = _
    rw [full_joint_mass_real, full_arrived_false]
    have hmass : (1 / 2 : ℝ) * zengCategory P x *
        bitMass (propensity P x) a ≠ 0 := by
      rw [← full_arrived_false]
      exact ne_of_gt harr
    have hcatne : zengCategory P x ≠ 0 := ne_of_gt hx
    have hbitne : bitMass (propensity P x) a ≠ 0 := by
      intro hz
      apply hmass
      rw [hz]
      ring
    cases a <;> simp [bitMass] at hbitne ⊢ <;>
      field_simp [hcatne, hbitne] <;> simp
  · have hx0 : zengCategory P x = 0 :=
      le_antisymm (le_of_not_gt hx) measureReal_nonneg
    have harr : arrivedCell (fullLaw P) (a, x, false) = 0 := by
      rw [full_arrived_false, hx0]
      ring
    simp [cellContribution, harr, hx0]

/-- Given [the specified inputs and assumptions](hyp:d,P,a,x), [the stated mathematical conclusion holds](goal). -/
lemma full_cellContribution_true {d : ℕ} (P : ZengLaw d)
    (a : Bool) (x : Fin d) : cellContribution (fullLaw P) (a, x, true) = 0 := by
  have harr : arrivedCell (fullLaw P) (a, x, true) = 0 := by
    unfold arrivedCell
    change (fullMeasure P).real {w | inCell w (a, x, true) ∧ w.R = true} = 0
    exact fullMeasure_real_of_surrogate_true P _ (by simp)
      (by intro w hw; exact hw.1.2.2)
  simp [cellContribution, harr]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hq,hqhalf,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma fullLaw_ate {n d : ℕ} {q : ℝ} (hn : 1 ≤ n)
    (hq : 0 < q) (hqhalf : q < 1 / 2) (P : ZengLaw d)
    (hP : P ∈ zengDiscreteClass d q) : ate (fullLaw P) = zengATE P := by
  have hmodel : UnrestrictedArrivalModelClass n d q (fullLaw P) :=
    { n_pos := hn
      d_pos := hP.2.2.1
      q_pos := hq
      q_le_one := by linarith
      randomized := fullLaw_randomized P
      balanced := fullLaw_balanced P
      surrogate := fullLaw_surrogate P
      outcome := fullLaw_outcome P
      mar := fullLaw_mar P
      arrival := fullLaw_arrival P hP }
  rw [unrestricted_cell_identification (fullLaw P) hmodel]
  unfold cellFunctional zengATE
  simp only [Fintype.sum_prod_type, Fintype.sum_bool,
    full_cellContribution_false P hP, full_cellContribution_true P,
    armSign, Bool.false_eq_true, if_true, if_false, zero_mul, mul_zero,
    add_zero, zero_add, one_mul, neg_one_mul]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hxmem
  by_cases hx : 0 < zengCategory P x
  · rw [dif_pos hx, outcomeMean_eq_zengMean P hP x hx false,
      outcomeMean_eq_zengMean P hP x hx true]
    ring
  · have hx0 : zengCategory P x = 0 :=
      le_antisymm (le_of_not_gt hx) measureReal_nonneg
    simp [hx, hx0]

end SyntheticCompletion

end CausalSmith.Stat.MarRareqLogfrontier
