module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.FinitePrefixTransfer
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridPoolLaw
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridTunedRisk

/-!
The three independent hybrid pools as a finite family, and exact finite-prefix risk transfer.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped BigOperators NNReal

/-- Three singleton coordinates distinguish the complete, pilot, and factorial pools. -/
-- @node: HybridPoolIndex
abbrev HybridPoolIndex := Unit ⊕ (Unit ⊕ Unit)

/-- Evaluation identifies a three-coordinate dependent family with its ordered triple. -/
-- @node: hybridTripleEquiv
def hybridTripleEquiv (X : HybridPoolIndex → Type) [∀ i, MeasurableSpace (X i)] :
    (∀ i, X i) ≃ᵐ (X (.inl ()) × X (.inr (.inl ())) × X (.inr (.inr ()))) where
  toFun s := (s (.inl ()), s (.inr (.inl ())), s (.inr (.inr ())))
  invFun s := fun i => match i with
    | .inl () => s.1
    | .inr (.inl ()) => s.2.1
    | .inr (.inr ()) => s.2.2
  left_inv s := by funext i; rcases i with ⟨⟨⟩⟩ | ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩⟩ <;> rfl
  right_inv s := rfl
  measurable_toFun := by
    change Measurable (fun s : (∀ i, X i) =>
      (s (.inl ()), s (.inr (.inl ())), s (.inr (.inr ()))))
    fun_prop
  measurable_invFun := by
    apply measurable_pi_lambda
    intro i
    rcases i with ⟨⟨⟩⟩ | ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩⟩ <;> dsimp <;> fun_prop

/-- [Under the stated inputs and conditions](hyp:X,mu), The triple equivalence preserves the independent product law.  This gives [the stated result](goal).-/
-- @node: hybrid_triple_pi_law
lemma hybrid_triple_pi_law (X : HybridPoolIndex → Type) [∀ i, MeasurableSpace (X i)]
    (mu : ∀ i, Measure (X i)) [∀ i, SigmaFinite (mu i)] :
    MeasurePreserving (hybridTripleEquiv X) (Measure.pi mu)
      ((mu (.inl ())).prod ((mu (.inr (.inl ()))).prod (mu (.inr (.inr ()))))) := by
  have hsplit := measurePreserving_sumPiEquivProdPi mu
  have hinner := measurePreserving_sumPiEquivProdPi (fun i => mu (.inr i))
  have hu0 := measurePreserving_piUnique (fun i : Unit => mu (.inl i))
  have hu1 := measurePreserving_piUnique (fun i : Unit => mu (.inr (.inl i)))
  have hu2 := measurePreserving_piUnique (fun i : Unit => mu (.inr (.inr i)))
  convert (hu0.prod ((hu1.prod hu2).comp hinner)).comp hsplit using 1
  funext s
  rfl

/-- The alphabet family retains the two marginal pools as different coordinates. -/
-- @node: HybridPoolAlphabet
abbrev HybridPoolAlphabet (d : Nat) : HybridPoolIndex → Type :=
  fun i => match i with
    | .inl () => Obs d
    | .inr (.inl ()) => AuxObs d
    | .inr (.inr ()) => AuxObs d

/-- Each coordinate inherits its finite observation alphabet's measurable structure. -/
-- @node: hybridPoolAlphabet_measurableSpace
instance hybridPoolAlphabet_measurableSpace (d : Nat) :
    ∀ i, MeasurableSpace (HybridPoolAlphabet d i)
  | .inl () => (inferInstance : MeasurableSpace (Obs d))
  | .inr (.inl ()) => (inferInstance : MeasurableSpace (AuxObs d))
  | .inr (.inr ()) => (inferInstance : MeasurableSpace (AuxObs d))

/-- The observation-law family assigns the complete law and its two marginal copies. -/
-- @node: hybridPoolObservationLaw
noncomputable def hybridPoolObservationLaw {d : Nat} (P : DiscreteLaw d) :
    ∀ i, Measure (HybridPoolAlphabet d i)
  | .inl () => obsLaw P
  | .inr (.inl ()) => (auxMarginal P).toMeasure
  | .inr (.inr ()) => (auxMarginal P).toMeasure

/-- Each pool's observation law is a probability measure. -/
-- @node: hybridPoolObservationLaw_probability
instance hybridPoolObservationLaw_probability {d : Nat} (P : DiscreteLaw d) :
    ∀ i, IsProbabilityMeasure (hybridPoolObservationLaw P i)
  | .inl () => by dsimp [hybridPoolObservationLaw, obsLaw]; infer_instance
  | .inr (.inl ()) => by dsimp [hybridPoolObservationLaw]; infer_instance
  | .inr (.inr ()) => by dsimp [hybridPoolObservationLaw]; infer_instance

/-- The family capacities are exactly the three public hybrid pool lengths. -/
-- @node: hybridPoolCapacity
noncomputable abbrev hybridPoolCapacity (n m : Nat) (eps : Real) : HybridPoolIndex → Nat :=
  fun i => match i with
    | .inl () => (hybridTuning n m eps).h0
    | .inr (.inl ()) => (hybridTuning n m eps).Mp
    | .inr (.inr ()) => (hybridTuning n m eps).Mf

/-- Prefix-family readback computes the same ordered clipped hybrid contrast. -/
-- @node: hybridFamilyStatistic
noncomputable def hybridFamilyStatistic (n m d : Nat) (eps : Real) :
    PrefixFamily (HybridPoolAlphabet d) → Real :=
  hybridOrderedPrefixStatistic (hybridTuning n m eps) ∘
    hybridTripleEquiv (fun i => FiniteSample (HybridPoolAlphabet d i))

/-- Prefix-family readback is measurable. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: hybridFamilyStatistic_measurable
lemma hybridFamilyStatistic_measurable (n m d : Nat) (eps : Real) :
    Measurable (hybridFamilyStatistic n m d eps) :=
  (hybridOrderedPrefixStatistic_measurable d _).comp (hybridTripleEquiv _).measurable

/-- [Under the stated inputs and conditions](hyp:eps,s,n,m,d), The family statistic retains the clipped interval at every prefix.  This gives [the stated result](goal).-/
-- @node: hybridFamilyStatistic_mem_Icc
lemma hybridFamilyStatistic_mem_Icc (n m d : Nat) (eps : Real)
    (s : PrefixFamily (HybridPoolAlphabet d)) :
    hybridFamilyStatistic n m d eps s ∈ Set.Icc (-1) 1 :=
  hybridOrderedPrefixStatistic_mem_Icc _ _

/-- Under the stated inputs and conditions, The ideal prefix-family risk is exactly the already established triple-prefix risk.  This gives [the stated result](goal). -/
-- @node: hybrid_family_prefix_risk_eq
lemma hybrid_family_prefix_risk_eq (n m d : Nat) (eps : Real) (P : DiscreteLaw d) :
    Causalean.Stat.sqRisk
      (independentPoissonPrefixLaw (hybridPoolObservationLaw P)
        (fun i => (hybridPoolCapacity n m eps i : NNReal) / 8))
      (hybridFamilyStatistic n m d eps) (ateFunctional P) =
    Causalean.Stat.sqRisk
      (hybridPoissonPrefixLaw P ((hybridTuning n m eps).h0 / 8 : NNReal)
        ((hybridTuning n m eps).Mp / 8 : NNReal)
        ((hybridTuning n m eps).Mf / 8 : NNReal))
      (hybridOrderedPrefixStatistic (hybridTuning n m eps)) (ateFunctional P) := by
  have hmap := hybrid_triple_pi_law (fun i => FiniteSample (HybridPoolAlphabet d i))
    (fun i => finitePoissonSampleLaw (hybridPoolObservationLaw P i)
      ((hybridPoolCapacity n m eps i : NNReal) / 8))
  unfold Causalean.Stat.sqRisk hybridFamilyStatistic
  exact hmap.integral_comp' (fun s =>
    (hybridOrderedPrefixStatistic (hybridTuning n m eps) s - ateFunctional P) ^ 2)

/-- [Under the stated inputs and conditions](hyp:eps,P,n,m,d), Extracting and packing the original three pools gives the finite-family iid law.  This gives [the stated result](goal).-/
-- @node: hybrid_family_fixed_pools_law
lemma hybrid_family_fixed_pools_law (n m d : Nat) (eps : Real) (P : DiscreteLaw d) :
    MeasurePreserving
      ((hybridTripleEquiv (fun i => Fin (hybridPoolCapacity n m eps i) →
        HybridPoolAlphabet d i)).symm ∘ hybridFixedPools eps)
      (annotationLaw P n m)
      (fixedPoolsLaw (hybridPoolObservationLaw P) (hybridPoolCapacity n m eps)) := by
  have hpi := hybrid_triple_pi_law
    (fun i => Fin (hybridPoolCapacity n m eps i) → HybridPoolAlphabet d i)
    (fun i => Measure.pi (fun _ : Fin (hybridPoolCapacity n m eps i) =>
      hybridPoolObservationLaw P i))
  exact hpi.symm.comp (hybrid_fixed_pools_law eps P)

/-- [Under the stated inputs and conditions](hyp:eps,s,k,n,m,d), Valid requests have identical family and triple readback; overflow resets both to zero.  This gives [the stated result](goal).-/
-- @node: hybrid_family_capped_statistic_eq
lemma hybrid_family_capped_statistic_eq (n m d : Nat) (eps : Real)
    (s : FixedPools (HybridPoolAlphabet d) (hybridPoolCapacity n m eps))
    (k : HybridPoolIndex → Nat) :
    cappedPrefixStatistic (hybridFamilyStatistic n m d eps) 0 (fun i => (s i, k i)) =
      hybridCappedFixedStatistic eps (hybridTripleEquiv _ s) (hybridTripleEquiv _ k) := by
  have hv : (∀ i, k i ≤ hybridPoolCapacity n m eps i) ↔
      k (.inl ()) ≤ (hybridTuning n m eps).h0 ∧
      k (.inr (.inl ())) ≤ (hybridTuning n m eps).Mp ∧
      k (.inr (.inr ())) ≤ (hybridTuning n m eps).Mf := by
    constructor
    · intro h; exact ⟨h (.inl ()), h (.inr (.inl ())), h (.inr (.inr ()))⟩
    · rintro ⟨h0, hp, hf⟩ i
      rcases i with ⟨⟨⟩⟩ | ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩⟩
      · exact h0
      · exact hp
      · exact hf
  by_cases hk : ∀ i, k i ≤ hybridPoolCapacity n m eps i
  · rw [cappedPrefixStatistic, dif_pos hk]
    change _ = if h : k (.inl ()) ≤ (hybridTuning n m eps).h0 ∧
      k (.inr (.inl ())) ≤ (hybridTuning n m eps).Mp ∧
      k (.inr (.inr ())) ≤ (hybridTuning n m eps).Mf then _ else 0
    rw [dif_pos (hv.mp hk)]
    rfl
  · have hn := mt hv.mpr hk
    rw [cappedPrefixStatistic, dif_neg hk]
    change 0 = if h : k (.inl ()) ≤ (hybridTuning n m eps).h0 ∧
      k (.inr (.inl ())) ≤ (hybridTuning n m eps).Mp ∧
      k (.inr (.inr ())) ≤ (hybridTuning n m eps).Mf then _ else 0
    rw [dif_neg hn]

/-- [Under the stated hypotheses](hyp:hS), The estimator is precisely the finite-family conditional prefix average.  This gives [the stated result](goal). -/
-- @node: hybrid_estimator_eq_family_average
lemma hybrid_estimator_eq_family_average (n m d : Nat) (eps : Real) (s : Sample n m d)
    (hS : Real.exp 4096 ≤ (n : Real) * eps) :
    hybridEstimator n m d eps s =
      prefixRaoBlackwellStatistic (fun i => (hybridPoolCapacity n m eps i : NNReal) / 8)
        (hybridFamilyStatistic n m d eps) 0
        ((hybridTripleEquiv (fun i => Fin (hybridPoolCapacity n m eps i) →
          HybridPoolAlphabet d i)).symm (hybridFixedPools eps s)) := by
  rw [hybrid_estimator_eq_poisson_integral eps s hS,
    prefixRaoBlackwellStatistic_eq_integral _ _
      (hybridFamilyStatistic_measurable n m d eps) 0]
  have hcount := hybrid_triple_pi_law (fun _ => Nat)
    (fun i => poissonMeasure ((hybridPoolCapacity n m eps i : NNReal) / 8))
  have hm : Measurable (fun k : Nat × Nat × Nat =>
      hybridCappedFixedStatistic eps (hybridFixedPools eps s) k) := by fun_prop
  have hi := hcount.integral_comp' (fun k : Nat × Nat × Nat =>
    hybridCappedFixedStatistic eps (hybridFixedPools eps s) k)
  change (∫ k, hybridCappedFixedStatistic eps (hybridFixedPools eps s)
      (hybridTripleEquiv (fun _ => Nat) k) ∂Measure.pi
        (fun i => poissonMeasure ((hybridPoolCapacity n m eps i : NNReal) / 8))) =
    (∫ k, hybridCappedFixedStatistic eps (hybridFixedPools eps s) k
      ∂hybridRequestLaw n m eps) at hi
  simp_rw [hybrid_capped_array_eq_fixed]
  rw [← hi]
  apply integral_congr_ae
  filter_upwards with k
  rw [hybrid_family_capped_statistic_eq]
  simp only [MeasurableEquiv.apply_symm_apply]

/-- [Under the stated hypotheses](hyp:hS), Original-record risk equals the finite-family Rao--Blackwell risk.  This gives [the stated result](goal). -/
-- @node: hybrid_ruleRisk_eq_family_average_risk
lemma hybrid_ruleRisk_eq_family_average_risk (n m d : Nat) (eps : Real)
    (P : DiscreteLaw d) (hS : Real.exp 4096 ≤ (n : Real) * eps) :
    ruleRisk (liftRule (hybridEstimator n m d eps)) P =
      Causalean.Stat.sqRisk
        (fixedPoolsLaw (hybridPoolObservationLaw P) (hybridPoolCapacity n m eps))
        (prefixRaoBlackwellStatistic
          (fun i => (hybridPoolCapacity n m eps i : NNReal) / 8)
          (hybridFamilyStatistic n m d eps) 0) (ateFunctional P) := by
  rw [hybrid_ruleRisk_eq_sqRisk]
  unfold Causalean.Stat.sqRisk
  simp_rw [hybrid_estimator_eq_family_average n m d eps _ hS]
  have hmap := hybrid_family_fixed_pools_law n m d eps P
  rw [← hmap.map_eq]
  exact (integral_map hmap.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x =>
      (prefixRaoBlackwellStatistic
        (fun i => (hybridPoolCapacity n m eps i : NNReal) / 8)
        (hybridFamilyStatistic n m d eps) 0 x - ateFunctional P) ^ 2) _ from
      (by fun_prop : Measurable _).aestronglyMeasurable)).symm

/-- Under the stated inputs and conditions, Finite-prefix averaging transfers the exact-tuning bound to the original records.  This gives [the stated result](goal). -/
-- @node: hybrid_large_information_risk
lemma hybrid_large_information_risk :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat) (eps : Real) (P : DiscreteLaw d),
      1 ≤ n → 2 ≤ d → 0 < eps → eps ≤ 1 / 4 →
      Real.exp 4096 ≤ (n : Real) * eps → ModelClass d eps P →
      ruleRisk (liftRule (hybridEstimator n m d eps)) P ≤
        C * (1 / ((n : Real) * eps) +
          ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := hybrid_tuned_prefix_and_overflow_rate
  refine ⟨C, hC, ?_⟩
  intro n m d eps P hn hd heps heps4 hS hP
  obtain ⟨_, _, _, h0, hp, hf, _, _⟩ := hybrid_finite_pool_sizes n m eps
    (hybrid_large_sample_size n eps heps4 hS)
  have hcap : ∀ i, 1 ≤ hybridPoolCapacity n m eps i := by
    intro i
    rcases i with ⟨⟨⟩⟩ | ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩⟩
    · exact h0
    · exact hp
    · exact hf
  have ht := (finite_prefix_transfer (hybridPoolObservationLaw P)
    (hybridPoolCapacity n m eps) hcap
    (hybridFamilyStatistic_measurable n m d eps)
    (hybridFamilyStatistic_mem_Icc n m d eps)
    (ateFunctional_mem_Icc P) le_rfl).2.2
  rw [← hybrid_ruleRisk_eq_family_average_risk n m d eps P hS,
    hybrid_family_prefix_risk_eq] at ht
  have hsum : (∑ i : HybridPoolIndex, Real.exp (-(hybridPoolCapacity n m eps i : Real))) =
      Real.exp (-((hybridTuning n m eps).h0 : Real)) +
      Real.exp (-((hybridTuning n m eps).Mp : Real)) +
      Real.exp (-((hybridTuning n m eps).Mf : Real)) := by
    simp [Fintype.sum_sum_type, hybridPoolCapacity, add_assoc]
  rw [hsum] at ht
  exact ht.trans (hbound n m d eps P hn hd heps heps4 hS hP)

end CausalSmith.Stat.AnnotationRarearmFrontier
