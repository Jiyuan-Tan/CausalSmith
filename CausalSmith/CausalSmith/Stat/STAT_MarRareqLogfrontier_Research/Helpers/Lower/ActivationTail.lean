module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationMixture
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment.FixedCount

/-! Reduction of the actual activation-cutoff probability to a finite union
under the parameter-independent iid membership, arm and flag distribution.
These identities isolate the binomial tail calculation in equation (6). -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hn,hd,hb,hq,hslice,hz,A), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_sample_membership_activation_event
lemma activated_sample_membership_activation_event (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hb : 0 < rareMass η n q) (hq : 0 < q) (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q))
    (A : Set (Fin n → Fin d × Bool × Bool)) :
    (Measure.pi (fun _ : Fin n => augmentedOneRecord η n d q z hz)).real
      {s | (fun i => ((s i).2.X, (s i).2.A, (s i).1)) ∈ A} =
    (Measure.pi (fun _ : Fin n =>
      ∑ x : Fin d, ∑ a : Bool, ∑ flag : Bool,
        ENNReal.ofReal (baselineMass η n d q x / 2 *
          bernWeight (q * lowerEndpoint n q) flag) • Measure.dirac (x, a, flag))).real A := by
  have hf : Measurable (fun s : Fin n → Bool × ObsRecord d =>
      fun i => ((s i).2.X, (s i).2.A, (s i).1)) := by fun_prop
  rw [← activated_sample_membership_activation_map η n d q z hn hd hb hq hslice hz,
    map_measureReal_apply hf (MeasurableSet.of_discrete)]
  rfl

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice,π,hπ,A), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_membership_activation_event
lemma activatedAugmentedMixture_membership_activation_event (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π)
    (A : Set (Fin n → Fin d × Bool × Bool)) :
    (activatedAugmentedMixture η n d q π).real
      {s | (fun i => ((s i).2.X, (s i).2.A, (s i).1)) ∈ A} =
    (Measure.pi (fun _ : Fin n =>
      ∑ x : Fin d, ∑ a : Bool, ∑ flag : Bool,
        ENNReal.ofReal (baselineMass η n d q x / 2 *
          bernWeight (q * lowerEndpoint n q) flag) • Measure.dirac (x, a, flag))).real A := by
  let := hπ.1
  rw [activatedAugmentedMixture_real_event η n d q hn hd hb hq hslice hπ]
  calc
    _ = ∫ _z : Fin d → ℝ,
        (Measure.pi (fun _ : Fin n =>
          ∑ x : Fin d, ∑ a : Bool, ∑ flag : Bool,
            ENNReal.ofReal (baselineMass η n d q x / 2 *
              bernWeight (q * lowerEndpoint n q) flag) • Measure.dirac (x, a, flag))).real A
        ∂Measure.pi (fun _ : Fin d => π) := by
      apply integral_congr_ae
      filter_upwards [finiteReciprocalPrior_pi_ae_support hπ d] with z hz
      rw [activatedAugmentedSample, dif_pos hz]
      exact activated_sample_membership_activation_event η n d q z hn hd hb hq hslice hz A
    _ = _ := by simp

/-- Given [the specified inputs and assumptions](hyp:η,n,d,K,q,hn,hd,hb,hq,hslice,π,hπ), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_cutoff_probability
lemma activatedAugmentedMixture_cutoff_probability (η : ℝ) (n d K : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π) :
    (activatedAugmentedMixture η n d q π).real
      {s | ¬ ∀ x : Fin d, x.val < rareCount η n d q →
        (∑ i ∈ Finset.univ.filter (fun i => (s i).2.X = x),
          if (s i).1 then 1 else 0) ≤ K} =
    (Measure.pi (fun _ : Fin n =>
      ∑ x : Fin d, ∑ a : Bool, ∑ flag : Bool,
        ENNReal.ofReal (baselineMass η n d q x / 2 *
          bernWeight (q * lowerEndpoint n q) flag) • Measure.dirac (x, a, flag))).real
      {s | ¬ ∀ x : Fin d, x.val < rareCount η n d q →
        (∑ i ∈ Finset.univ.filter (fun i => (s i).1 = x),
          if (s i).2.2 then 1 else 0) ≤ K} := by
  exact activatedAugmentedMixture_membership_activation_event η n d q hn hd hb hq hslice hπ
    {s | ¬ ∀ x : Fin d, x.val < rareCount η n d q →
      (∑ i ∈ Finset.univ.filter (fun i => (s i).1 = x),
        if (s i).2.2 then 1 else 0) ≤ K}

/-- Given [the specified inputs and assumptions](hyp:η,n,d,K,q,ε,μ,htail), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_cutoff_union_bound
lemma activation_cutoff_union_bound (η : ℝ) (n d K : ℕ) (q ε : ℝ)
    (μ : Measure (Fin n → Fin d × Bool × Bool))
    (htail : ∀ x : Fin d, x.val < rareCount η n d q →
      μ.real {s | K < (∑ i ∈ Finset.univ.filter (fun i => (s i).1 = x),
        if (s i).2.2 then 1 else 0)} ≤ ε) :
    μ.real {s | ¬ ∀ x : Fin d, x.val < rareCount η n d q →
      (∑ i ∈ Finset.univ.filter (fun i => (s i).1 = x),
        if (s i).2.2 then 1 else 0) ≤ K} ≤ (rareCount η n d q : ℝ) * ε := by
  classical
  have hJ : rareCount η n d q ≤ d :=
    (min_le_left _ _).trans (Nat.sub_le d 1)
  let cell : Fin (rareCount η n d q) → Fin d := fun x => ⟨x.val, lt_of_lt_of_le x.isLt hJ⟩
  let E (x : Fin (rareCount η n d q)) : Set (Fin n → Fin d × Bool × Bool) :=
    {s | K < (∑ i ∈ Finset.univ.filter (fun i => (s i).1 = cell x),
      if (s i).2.2 then 1 else 0)}
  have heq : {s | ¬ ∀ x : Fin d, x.val < rareCount η n d q →
      (∑ i ∈ Finset.univ.filter (fun i => (s i).1 = x),
        if (s i).2.2 then 1 else 0) ≤ K} = ⋃ x, E x := by
    ext s
    simp only [Set.mem_ofPred_eq, not_forall, not_le, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hcount⟩
      exact ⟨⟨x.val, hx⟩, hcount⟩
    · rintro ⟨x, hx⟩
      exact ⟨cell x, x.isLt, hx⟩
  rw [heq]
  calc
    _ ≤ ∑ x, μ.real (E x) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _x : Fin (rareCount η n d q), ε :=
      Finset.sum_le_sum (fun x _ => htail (cell x) x.isLt)
    _ = _ := by simp

/-- Given [the specified inputs and assumptions](hyp:X,A,n,K,s), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_event_descFactorial_eq_weighted
lemma activation_event_descFactorial_eq_weighted {X : Type*} [MeasurableSpace X]
    (A : Set X) (n K : ℕ) (s : Fin n → X) :
    ((eventCount
      (fixedSizeEmbed n s) A).descFactorial
        (K + 1) : ℝ) =
    weightedFactorial
      A A (K + 1)
      (fixedSizeEmbed n s) := by
  unfold weightedFactorial
  simp only [Nat.add_sub_cancel]
  generalize eventCount
    (fixedSizeEmbed n s) A = c
  cases c with
  | zero => simp
  | succ c =>
    rw [Nat.succ_descFactorial_succ]
    simp only [Nat.add_sub_cancel, Nat.cast_mul]

/-- Given [the specified inputs and assumptions](hyp:X,P,A,hA,n,K), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_event_descFactorial_integral
lemma activation_event_descFactorial_integral {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (A : Set X) (hA : MeasurableSet A)
    (n K : ℕ) :
    (∫ s : Fin n → X,
      ((eventCount
        (fixedSizeEmbed n s) A).descFactorial
          (K + 1) : ℝ) ∂Measure.pi (fun _ : Fin n => P)) =
      (n.descFactorial (K + 1) : ℝ) * P.real A ^ (K + 1) := by
  simp_rw [activation_event_descFactorial_eq_weighted]
  rw [integral_weightedFactorial_fixedCount
    P A A hA hA (Subset.rfl) (K + 1) n (by omega)]
  simp only [Nat.add_sub_cancel, Measure.real, pow_succ]
  ring

/-- Given [the specified inputs and assumptions](hyp:X,P,A,hA,n,K), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_event_factorial_tail
lemma activation_event_factorial_tail {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Finite X]
    (P : Measure X) [IsProbabilityMeasure P] (A : Set X) (hA : MeasurableSet A)
    (n K : ℕ) :
    (Measure.pi (fun _ : Fin n => P)).real
      {s | K < eventCount
        (fixedSizeEmbed n s) A} ≤
      ((n : ℝ) * P.real A) ^ (K + 1) / ((K + 1).factorial : ℝ) := by
  let μ := Measure.pi (fun _ : Fin n => P)
  let f (s : Fin n → X) : ℝ :=
    ((eventCount
      (fixedSizeEmbed n s) A).descFactorial
        (K + 1) : ℝ)
  have hsubset : {s | K < eventCount
      (fixedSizeEmbed n s) A} ⊆
      {s | ((K + 1).factorial : ℝ) ≤ f s} := by
    intro s hs
    have h := Nat.descFactorial_le (K + 1) (Nat.succ_le_of_lt hs)
    rw [Nat.descFactorial_self] at h
    change ((K + 1).factorial : ℝ) ≤
      ((eventCount
        (fixedSizeEmbed n s) A).descFactorial
          (K + 1) : ℝ)
    exact_mod_cast h
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Filter.Eventually.of_forall fun s => (Nat.cast_nonneg _ : 0 ≤ f s))
    (Integrable.of_finite : Integrable f μ) ((K + 1).factorial : ℝ)
  have hmono := measureReal_mono (μ := μ) hsubset
  have hfac : (0 : ℝ) < ((K + 1).factorial : ℝ) := by positivity
  apply (le_div_iff₀ hfac).mpr
  have hmoment := activation_event_descFactorial_integral P A hA n K
  have hpow : (n.descFactorial (K + 1) : ℝ) ≤ (n : ℝ) ^ (K + 1) := by
    exact_mod_cast Nat.descFactorial_le_pow n (K + 1)
  have hbound : (∫ s, f s ∂μ) ≤ ((n : ℝ) * P.real A) ^ (K + 1) := by
    rw [show (∫ s, f s ∂μ) = (n.descFactorial (K + 1) : ℝ) * P.real A ^ (K + 1)
      from hmoment, mul_pow]
    exact mul_le_mul_of_nonneg_right hpow (by positivity)
  exact (by nlinarith : _ ≤ ∫ s, f s ∂μ).trans hbound

/-- Given [the specified inputs and assumptions](hyp:n,d,x,s), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_count_eq_eventCount
lemma activation_count_eq_eventCount (n d : ℕ)
    (x : Fin d) (s : Fin n → Fin d × Bool × Bool) :
    (∑ i ∈ Finset.univ.filter (fun i => (s i).1 = x),
      if (s i).2.2 then 1 else 0) =
    eventCount
      (fixedSizeEmbed n s)
      {r | r.1 = x ∧ r.2.2 = true} := by
  classical
  unfold eventCount
    fixedSizeEmbed
    FiniteSample.count
    FiniteSample.points
  simp only [Finset.sum_boole, Finset.filter_filter, Set.mem_ofPred_eq, Nat.cast_id]

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hb,hq,hslice,x), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_membership_flag_probability
lemma activation_membership_flag_probability (η : ℝ) (n d : ℕ) (q : ℝ)
    (hb : 0 < rareMass η n q) (hq : 0 < q) (hslice : RareArrivalSlice n q)
    (x : Fin d) :
    (∑ y : Fin d, ∑ a : Bool, ∑ flag : Bool,
      ENNReal.ofReal (baselineMass η n d q y / 2 *
        bernWeight (q * lowerEndpoint n q) flag) • Measure.dirac (y, a, flag)).real
      {r | r.1 = x ∧ r.2.2 = true} =
        baselineMass η n d q x * (q * lowerEndpoint n q) := by
  classical
  have hb0 := baselineMass_nonneg η n d q hb x
  have hH : 0 ≤ q * lowerEndpoint n q := by
    unfold lowerEndpoint
    positivity
  have hweight : 0 ≤ baselineMass η n d q x / 2 * (q * lowerEndpoint n q) :=
    mul_nonneg (div_nonneg hb0 (by norm_num)) hH
  have hevent : MeasurableSet {r : Fin d × Bool × Bool | r.1 = x ∧ r.2.2 = true} :=
    MeasurableSet.of_discrete
  simp only [Measure.real]
  simp [bernWeight, Set.indicator]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hweight]
  ring

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hn,hd,hb,hq,hslice), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_membership_flag_isProbabilityMeasure
lemma activation_membership_flag_isProbabilityMeasure (η : ℝ) (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) :
    IsProbabilityMeasure
      (∑ x : Fin d, ∑ a : Bool, ∑ flag : Bool,
        ENNReal.ofReal (baselineMass η n d q x / 2 *
          bernWeight (q * lowerEndpoint n q) flag) • Measure.dirac (x, a, flag)) := by
  have hz : ∀ x : Fin d, (fun _ : Fin d => (1 : ℝ)) x ∈ Icc (1 : ℝ) (lowerEndpoint n q) :=
    fun _ => ⟨le_rfl, lowerEndpoint_one_le n q hq.le⟩
  let := augmentedOneRecord_isProbabilityMeasure η n d q (fun _ => 1)
    hn hd hb hq hslice hz
  rw [← augmentedOneRecord_membership_activation_map η n d q (fun _ => 1) hz]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Given [the specified inputs and assumptions](hyp:η,n,d,K,q,hn,hd,hb,hq,hslice,π,hπ), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedAugmentedMixture_factorial_cutoff_bound
lemma activatedAugmentedMixture_factorial_cutoff_bound (η : ℝ) (n d K : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hb : 0 < rareMass η n q)
    (hq : 0 < q) (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π) :
    (activatedAugmentedMixture η n d q π).real
      {s | ¬ ∀ x : Fin d, x.val < rareCount η n d q →
        (∑ i ∈ Finset.univ.filter (fun i => (s i).2.X = x),
          if (s i).1 then 1 else 0) ≤ K} ≤
      (rareCount η n d q : ℝ) *
        (((n : ℝ) * (rareMass η n q * (q * lowerEndpoint n q))) ^ (K + 1) /
          ((K + 1).factorial : ℝ)) := by
  let P : Measure (Fin d × Bool × Bool) :=
    ∑ x : Fin d, ∑ a : Bool, ∑ flag : Bool,
      ENNReal.ofReal (baselineMass η n d q x / 2 *
        bernWeight (q * lowerEndpoint n q) flag) • Measure.dirac (x, a, flag)
  let : IsProbabilityMeasure P :=
    activation_membership_flag_isProbabilityMeasure η n d q hn hd hb hq hslice
  rw [activatedAugmentedMixture_cutoff_probability η n d K q hn hd hb hq hslice hπ]
  apply activation_cutoff_union_bound
  intro x hx
  simp_rw [activation_count_eq_eventCount]
  have htail := activation_event_factorial_tail P
    {r | r.1 = x ∧ r.2.2 = true} (MeasurableSet.of_discrete) n K
  have hprob : P.real {r | r.1 = x ∧ r.2.2 = true} =
      rareMass η n q * (q * lowerEndpoint n q) := by
    rw [activation_membership_flag_probability η n d q hb hq hslice x]
    simp [baselineMass, hx]
  simpa only [hprob] using htail

end CausalSmith.Stat.MarRareqLogfrontier
