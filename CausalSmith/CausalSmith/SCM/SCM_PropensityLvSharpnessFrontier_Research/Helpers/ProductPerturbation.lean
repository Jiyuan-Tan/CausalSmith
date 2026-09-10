import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Statements
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.BowConstruction

/-! # Product bounds for the paper's two-point perturbations -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

/-- For a [scalar weight](hyp:c) [below infinity](hyp:hc), [the product measure of identically scaled coordinates equals the original product measure scaled by the corresponding power](goal). -/
-- @node: pi_const_smul
lemma pi_const_smul {X : Type*} [MeasurableSpace X] (n : ℕ) (c : ℝ≥0∞)
    (hc : c ≠ ∞) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    Measure.pi (fun _ : Fin n => c • μ) = c ^ n • Measure.pi (fun _ : Fin n => μ) := by
  letI : IsFiniteMeasure (c • μ) := ⟨by simpa using (lt_top_iff_ne_top.mpr hc)⟩
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  simp

/-- For [two scalar weights](hyp:a,b) [below infinity](hyp:ha,hb), [the product of coordinatewise two-component measure sums expands as the sum over all coordinate subsets](goal). -/
-- @node: pi_add_smul_expand
lemma pi_add_smul_expand {X : Type*} [MeasurableSpace X] (n : ℕ) (a b : ℝ≥0∞)
    (ha : a ≠ ∞) (hb : b ≠ ∞)
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Measure.pi (fun _ : Fin n => a • μ + b • ν) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
        Measure.pi (fun i : Fin n => if i ∈ t then a • μ else b • ν) := by
  letI : IsFiniteMeasure (a • μ) := ⟨by simpa using (lt_top_iff_ne_top.mpr ha)⟩
  letI : IsFiniteMeasure (b • ν) := ⟨by simpa using (lt_top_iff_ne_top.mpr hb)⟩
  letI : IsFiniteMeasure (a • μ + b • ν) := inferInstance
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro t ht
  letI : ∀ i : Fin n, SigmaFinite (if i ∈ t then a • μ else b • ν) := fun i => by
    split <;> infer_instance
  rw [Measure.pi_pi]
  have heval (i : Fin n) :
      (if i ∈ t then a • μ else b • ν) (s i) =
        if i ∈ t then a * μ (s i) else b * ν (s i) := by
    split <;> simp_all [Measure.smul_apply]
  simp_rw [heval]
  rw [Finset.prod_ite]
  have hcomp : (Finset.univ : Finset (Fin n)).filter (fun x => x ∉ t) =
      Finset.univ \ t := by ext; simp
  rw [hcomp]
  simp only [Finset.filter_mem_eq_inter]
  simp only [Finset.univ_inter]

/-- For [two scalar weights](hyp:a,b) that are [below infinity](hyp:ha,hb) and [sum to one](hyp:hab), [the product mixture splits into its all-common component plus a residual of the complementary mass](goal). -/
-- @node: pi_mixture_common_part
lemma pi_mixture_common_part {X : Type*} [MeasurableSpace X]
    (n : ℕ) (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) (hab : a + b = 1)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ R : Measure (Fin n → X),
      Measure.pi (fun _ : Fin n => a • μ + b • ν) =
        a ^ n • Measure.pi (fun _ : Fin n => μ) + R ∧
      R Set.univ = 1 - a ^ n := by
  let term (t : Finset (Fin n)) : Measure (Fin n → X) :=
    Measure.pi (fun i : Fin n => if i ∈ t then a • μ else b • ν)
  let R : Measure (Fin n → X) :=
    ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset.erase Finset.univ, term t
  refine ⟨R, ?_, ?_⟩
  · rw [pi_add_smul_expand n a b ha hb μ ν]
    have hu : (Finset.univ : Finset (Fin n)) ∈
        (Finset.univ : Finset (Fin n)).powerset := Finset.mem_powerset.mpr (by simp)
    rw [← Finset.sum_erase_add _ term hu]
    have hterm : term Finset.univ = Measure.pi (fun _ : Fin n => a • μ) := by
      simp [term]
    rw [hterm, pi_const_smul n a ha μ]
    simp [R, add_comm]
  · have hdecomp : Measure.pi (fun _ : Fin n => a • μ + b • ν) =
        a ^ n • Measure.pi (fun _ : Fin n => μ) + R := by
      rw [pi_add_smul_expand n a b ha hb μ ν]
      have hu : (Finset.univ : Finset (Fin n)) ∈
          (Finset.univ : Finset (Fin n)).powerset := Finset.mem_powerset.mpr (by simp)
      rw [← Finset.sum_erase_add _ term hu]
      have hterm : term Finset.univ = Measure.pi (fun _ : Fin n => a • μ) := by
        simp [term]
      rw [hterm, pi_const_smul n a ha μ]
      simp [R, add_comm]
    have hmixprob : IsProbabilityMeasure (a • μ + b • ν) := by
      rw [isProbabilityMeasure_iff]
      simp [hab]
    letI : IsProbabilityMeasure (a • μ + b • ν) := hmixprob
    have hu := congrArg (fun m : Measure (Fin n → X) => m Set.univ) hdecomp
    simp only [measure_univ, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      mul_one] at hu
    exact ENNReal.eq_sub_of_add_eq (ENNReal.pow_ne_top ha) (by simpa [add_comm] using hu.symm)

/-- For the specified model objects, [the stated conditions](hyp:hp), [the stated mathematical relationship holds](goal). -/
-- @node: one_sub_pow_le_nat_mul
lemma one_sub_pow_le_nat_mul (p : ℝ) (hp : p ∈ Set.Icc 0 1) (n : ℕ) :
    1 - (1 - p) ^ n ≤ n * p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpow : 0 ≤ (1 - p) ^ n := pow_nonneg (sub_nonneg.mpr hp.2) _
      calc
        1 - (1 - p) ^ n * (1 - p) =
            (1 - (1 - p) ^ n) + (1 - p) ^ n * p := by ring
        _ ≤ n * p + 1 * p := by
          exact add_le_add ih (mul_le_mul_of_nonneg_right
            (pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1])) hp.1)
        _ = ((n : ℝ) + 1) * p := by ring
        _ = (Nat.succ n : ℝ) * p := by rw [Nat.cast_succ]

/-- For the specified model objects, [the stated conditions](hyp:hp), [the stated mathematical relationship holds](goal). -/
-- @node: product_mixture_allSet_bound
lemma product_mixture_allSet_bound {X : Type*} [MeasurableSpace X]
    (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sSup {d : ℝ | ∃ C : Set (Fin n → X),
      d = |(Measure.pi (fun _ : Fin n =>
        ENNReal.ofReal (1 - p) • μ + ENNReal.ofReal p • ν) C).toReal -
        (Measure.pi (fun _ : Fin n => μ) C).toReal|} ≤ n * p := by
  let a := ENNReal.ofReal (1 - p)
  let b := ENNReal.ofReal p
  have ha : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hb : b ≠ ∞ := ENNReal.ofReal_ne_top
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp.2) hp.1]
    simp
  obtain ⟨R, hdecomp, hRmass⟩ := pi_mixture_common_part n a b ha hb hab μ ν
  have hnonempty : {d : ℝ | ∃ C : Set (Fin n → X),
      d = |(Measure.pi (fun _ : Fin n => a • μ + b • ν) C).toReal -
        (Measure.pi (fun _ : Fin n => μ) C).toReal|}.Nonempty := by
    refine ⟨0, ∅, ?_⟩
    simp
  apply csSup_le hnonempty
  intro d hd
  obtain ⟨C, rfl⟩ := hd
  rw [hdecomp, Measure.add_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  have hRtop : R Set.univ ≠ ∞ := by
    rw [hRmass]
    exact ENNReal.sub_ne_top ENNReal.one_ne_top
  letI : IsFiniteMeasure R := ⟨lt_top_iff_ne_top.mpr hRtop⟩
  have hmuC : (Measure.pi (fun _ : Fin n => μ) C) ≠ ∞ := measure_ne_top _ _
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.pow_ne_top ha) hmuC) (measure_ne_top _ _),
    ENNReal.toReal_mul]
  have hRle : (R C).toReal ≤ (R Set.univ).toReal :=
    ENNReal.toReal_mono hRtop (measure_mono (Set.subset_univ C))
  have hmu_le : (Measure.pi (fun _ : Fin n => μ) C).toReal ≤ 1 := by
    have hle := measure_mono (μ := Measure.pi (fun _ : Fin n => μ))
      (Set.subset_univ C)
    rw [measure_univ] at hle
    exact ENNReal.toReal_mono ENNReal.one_ne_top hle
  have haReal : a.toReal = 1 - p := by simp [a, hp.2]
  have hRreal : (R Set.univ).toReal = 1 - (1 - p) ^ n := by
    rw [hRmass, ENNReal.toReal_sub_of_le]
    · simp [haReal]
    · simpa [← ENNReal.toReal_le_toReal (ENNReal.pow_ne_top ha) ENNReal.one_ne_top,
        haReal] using pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1])
    · exact ENNReal.one_ne_top
  have hdiff : |(a ^ n).toReal * (Measure.pi (fun _ : Fin n => μ) C).toReal +
        (R C).toReal - (Measure.pi (fun _ : Fin n => μ) C).toReal| ≤
      1 - (1 - p) ^ n := by
    rw [ENNReal.toReal_pow, haReal]
    have hpow : (1 - p) ^ n ≤ 1 :=
      pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1])
    have hRnonneg : 0 ≤ (R C).toReal := ENNReal.toReal_nonneg
    have hmu_nonneg : 0 ≤ (Measure.pi (fun _ : Fin n => μ) C).toReal :=
      ENNReal.toReal_nonneg
    rw [hRreal] at hRle
    rw [abs_le]
    constructor <;> nlinarith
  exact hdiff.trans (one_sub_pow_le_nat_mul p hp n)

/-- The observed law of the canonical bow witness when its two arm laws agree. -/
-- @node: canonicalObservedMeasure
noncomputable def canonicalObservedMeasure (a : Bool) (e : ℝ) (P : Measure ℝ) :
    Measure (Bool × ℝ) :=
  ENNReal.ofReal e • P.map (fun y => (a, y)) +
    ENNReal.ofReal (1 - e) • P.map (fun y => (!a, y))

/-- For the specified model objects, [the stated conditions](hyp:he0,he1), [the stated mathematical relationship holds](goal). -/
-- @node: observedLaw_canonicalBowWitness_self
lemma observedLaw_canonicalBowWitness_self (a : Bool) (e : ℝ) (P : Measure ℝ)
    [IsProbabilityMeasure P] (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    observedLaw (canonicalBowWitness a e P P he0 he1) =
      canonicalObservedMeasure a e P := by
  have hobs : Measurable (fun z : Bool × ℝ × ℝ =>
      (treatment z, potentialOutcome (treatment z) z)) := by
    exact measurable_fst.prodMk measurable_selectedPotentialOutcome
  change Measure.map (fun z : Bool × ℝ × ℝ =>
    (treatment z, potentialOutcome (treatment z) z)) (canonicalBowLaw a e P P) = _
  rw [canonicalBowLaw]
  rw [Measure.map_add _ _ hobs, Measure.map_smul, Measure.map_smul,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  cases a <;> simp [canonicalObservedMeasure, Function.comp_def, treatment, potentialOutcome]

/-- For the specified model objects, [the stated mathematical relationship holds](goal). -/
-- @node: canonicalObservedMeasure_mixture
lemma canonicalObservedMeasure_mixture (a : Bool) (e p : ℝ)
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    canonicalObservedMeasure a e
      (ENNReal.ofReal (1 - p) • P + ENNReal.ofReal p • Q) =
    ENNReal.ofReal (1 - p) • canonicalObservedMeasure a e P +
      ENNReal.ofReal p • canonicalObservedMeasure a e Q := by
  ext C
  simp only [canonicalObservedMeasure]
  rw [Measure.map_add, Measure.map_add, Measure.map_smul, Measure.map_smul,
    Measure.map_smul, Measure.map_smul]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  ring
  all_goals fun_prop

/-- For the specified model objects, [the stated conditions](hyp:he0,he1), [the stated mathematical relationship holds](goal). -/
-- @node: canonicalObservedMeasure_isProbabilityMeasure
lemma canonicalObservedMeasure_isProbabilityMeasure (a : Bool) (e : ℝ)
    (P : Measure ℝ) [IsProbabilityMeasure P] (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    IsProbabilityMeasure (canonicalObservedMeasure a e P) := by
  rw [isProbabilityMeasure_iff]
  simp only [canonicalObservedMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp [ENNReal.ofReal_sub 1 he0, ENNReal.ofReal_le_one.mpr he1]

/-- For the specified model objects, [the stated conditions](hyp:hp,he0,he1,hrate), [the stated mathematical relationship holds](goal). -/
-- @node: productTVLocal_of_canonical_mixture
lemma productTVLocal_of_canonical_mixture (a : Bool) (e : ℝ)
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p : ℕ → ℝ) (hp : ∀ n, p n ∈ Set.Icc 0 1)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (nhds 0)) :
    ProductTVLocal (canonicalObservedMeasure a e P)
      (fun n => canonicalObservedMeasure a e
        (ENNReal.ofReal (1 - p n) • P + ENNReal.ofReal (p n) • Q)) := by
  have hPobs := canonicalObservedMeasure_isProbabilityMeasure a e P he0 he1
  have hQobs := canonicalObservedMeasure_isProbabilityMeasure a e Q he0 he1
  letI : IsProbabilityMeasure (canonicalObservedMeasure a e P) := hPobs
  letI : IsProbabilityMeasure (canonicalObservedMeasure a e Q) := hQobs
  unfold ProductTVLocal iidProductLaw
  have hlower : ∀ n, 0 ≤ sSup {d : ℝ | ∃ C : Set (ObservedSample n),
      d = |((Measure.pi fun _ : Fin n => canonicalObservedMeasure a e
          (ENNReal.ofReal (1 - p n) • P + ENNReal.ofReal (p n) • Q)) C).toReal -
        ((Measure.pi fun _ : Fin n => canonicalObservedMeasure a e P) C).toReal|} := by
    intro n
    rw [canonicalObservedMeasure_mixture]
    have hmix : IsProbabilityMeasure
        (ENNReal.ofReal (1 - p n) • canonicalObservedMeasure a e P +
          ENNReal.ofReal (p n) • canonicalObservedMeasure a e Q) := by
      rw [isProbabilityMeasure_iff]
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
      simp only [measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr (hp n).2) (hp n).1]
      simp
    letI : IsProbabilityMeasure
        (ENNReal.ofReal (1 - p n) • canonicalObservedMeasure a e P +
          ENNReal.ofReal (p n) • canonicalObservedMeasure a e Q) := hmix
    apply le_csSup
    · refine ⟨1, ?_⟩
      intro d hd
      obtain ⟨C, rfl⟩ := hd
      have hx : ((Measure.pi fun _ : Fin n =>
          ENNReal.ofReal (1 - p n) • canonicalObservedMeasure a e P +
            ENNReal.ofReal (p n) • canonicalObservedMeasure a e Q) C).toReal ≤ 1 := by
        exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      have hy : ((Measure.pi fun _ : Fin n => canonicalObservedMeasure a e P) C).toReal ≤
          1 := ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      have hx0 : 0 ≤ ((Measure.pi fun _ : Fin n =>
          ENNReal.ofReal (1 - p n) • canonicalObservedMeasure a e P +
            ENNReal.ofReal (p n) • canonicalObservedMeasure a e Q) C).toReal :=
        ENNReal.toReal_nonneg
      have hy0 : 0 ≤ ((Measure.pi fun _ : Fin n =>
          canonicalObservedMeasure a e P) C).toReal := ENNReal.toReal_nonneg
      rw [abs_le]
      constructor <;> linarith
    · refine ⟨∅, ?_⟩
      simp
  have hupper : ∀ n, sSup {d : ℝ | ∃ C : Set (ObservedSample n),
      d = |((Measure.pi fun _ : Fin n => canonicalObservedMeasure a e
          (ENNReal.ofReal (1 - p n) • P + ENNReal.ofReal (p n) • Q)) C).toReal -
        ((Measure.pi fun _ : Fin n => canonicalObservedMeasure a e P) C).toReal|} ≤
      (n : ℝ) * p n := by
    intro n
    rw [canonicalObservedMeasure_mixture]
    exact product_mixture_allSet_bound n (p n) (hp n)
      (canonicalObservedMeasure a e P) (canonicalObservedMeasure a e Q)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate
    (Filter.Eventually.of_forall hlower) (Filter.Eventually.of_forall hupper)

end CausalSmith.SCM.PropensityLvSharpnessFrontier
