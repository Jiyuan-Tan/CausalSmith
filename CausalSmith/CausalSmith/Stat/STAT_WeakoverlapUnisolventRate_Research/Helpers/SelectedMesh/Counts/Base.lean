module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass
public import Mathlib.Probability.Distributions.Binomial
public import Causalean.Stat.Concentration.TailBounds.BinomialCount
public import Causalean.Stat.Concentration.TailBounds.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Simultaneous treated-count event for the selected mesh -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory
open scoped Classical

/-- A full-sample event depends only on the covariates and treatment arms. For [the stated inputs and conditions](hyp:E), [the `CountDesignSaturated` object being defined](goal). -/
@[expose] def CountDesignSaturated {d n : ℕ} (E : Set (Fin n → Obs d)) : Prop :=
  ∀ ω ξ, (fun i => ((ξ i).1, (ξ i).2.1)) =
    (fun i => ((ω i).1, (ω i).2.1)) → (ω ∈ E ↔ ξ ∈ E)

/-- The treated microcell count is the sum of its Bernoulli indicators. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,ℓ), [the asserted conclusion holds](goal). -/
lemma treatedCount_eq_indicator_sum {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1)) :
    (treatedCount m j ω k ℓ : ℝ) =
      ∑ i : Fin n,
        if (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ
          then (1 : ℝ) else 0 := by
  classical
  simp [treatedCount]

/-- The treated microcell indicator is measurable. [For the stated inputs and conditions](hyp:d,m,j,k,ℓ), [the asserted conclusion holds](goal). -/
lemma treatedMicrocellIndicator_measurable {d : ℕ} (m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)) :
    Measurable (fun z : Obs d =>
      if z.2.1 = true ∧ z.1 ∈ scaledMicroCell d m j k ℓ
        then (1 : ℝ) else 0) := by
  classical
  have hs : MeasurableSet {z : Obs d | z.2.1 = true ∧
      z.1 ∈ scaledMicroCell d m j k ℓ} := by
    exact ((measurableSet_singleton true).preimage
      (measurable_fst.comp measurable_snd)).inter
      ((orderedMass_scaledMicroCell_measurable d m j k ℓ).preimage measurable_fst)
  exact Measurable.ite hs measurable_const measurable_const

/-- Each treated microcell count is measurable on the finite product sample. [For the stated inputs and conditions](hyp:d,n,m,j,k,ℓ), [the asserted conclusion holds](goal). -/
lemma treatedCount_measurable {d n : ℕ} (m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)) :
    Measurable (fun ω : Fin n → Obs d => (treatedCount m j ω k ℓ : ℝ)) := by
  classical
  have hsum : Measurable (fun ω : Fin n → Obs d =>
      ∑ i : Fin n,
        if (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ
          then (1 : ℝ) else 0) := by
    apply Finset.measurable_fun_sum
    intro i hi
    exact (treatedMicrocellIndicator_measurable m j k ℓ).comp
      (measurable_pi_apply i)
  convert hsum using 1
  funext ω
  exact treatedCount_eq_indicator_sum m j ω k ℓ

/-- Bernstein deviation for a Bernoulli count on the finite product law. [For the stated inputs and conditions](hyp:N,X,P,f,hf,hf01,hN,p,η,hp,hη,hmean), [the asserted conclusion holds](goal). -/
lemma finiteProduct_bernoulliCount_deviation
    {N : ℕ} {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (f : X → ℝ)
    (hf : Measurable f) (hf01 : ∀ x, f x = 0 ∨ f x = 1)
    (hN : 0 < N) (p η : ℝ) (hp : 0 < p) (hη : 0 < η)
    (hmean : ∫ x, f x ∂P = p) :
    (Measure.pi (fun _ : Fin N => P)).real
      {ω | η ≤ |(∑ i, f (ω i)) - (N : ℝ) * p|} ≤
      2 * Real.exp (-η ^ 2 / (2 * (2 * (N : ℝ) * p + η))) := by
  have hfIcc : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    rcases hf01 x with hx | hx <;> simp [hx]
  have hfint : Integrable f P := by
    refine Integrable.of_bound hf.aestronglyMeasurable 1 ?_
    filter_upwards with x
    rcases hf01 x with hx | hx <;> simp [hx]
  have hp_le : p ≤ 1 := by
    calc
      p = ∫ x, f x ∂P := hmean.symm
      _ ≤ ∫ _x, (1 : ℝ) ∂P := integral_mono_ae hfint (integrable_const 1)
        (ae_of_all _ fun x => (hfIcc x).2)
      _ = 1 := by simp
  have henvelope : ∀ᵐ x ∂P, |f x - ∫ y, f y ∂P| ≤ 1 := by
    filter_upwards with x
    rw [hmean]
    exact abs_le.2 ⟨by linarith [(hfIcc x).1], by linarith [(hfIcc x).2]⟩
  have hvariance : ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P ≤ p := by
    rw [hmean]
    have hf2int : Integrable (fun x => f x ^ 2) P := by
      exact Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable 1
        (ae_of_all _ fun x => by rcases hf01 x with hx | hx <;> simp [hx])
    calc
      ∫ x, (f x - p) ^ 2 ∂P =
          (∫ x, f x ^ 2 ∂P) - 2 * p * (∫ x, f x ∂P) + p ^ 2 := by
        rw [show (fun x => (f x - p) ^ 2) =
            fun x => f x ^ 2 - 2 * p * f x + p ^ 2 by funext x; ring]
        integral_linearity
        rw [integral_const]
        simp
      _ = p - p ^ 2 := by
        rw [show (∫ x, f x ^ 2 ∂P) = p by
          rw [← hmean]
          apply integral_congr_ae
          filter_upwards with x
          rcases hf01 x with hx | hx <;> simp [hx]]
        rw [hmean]
        ring
      _ ≤ p := by nlinarith [sq_nonneg p]
  let g : Unit → X → ℝ := fun _ => f
  let b : Unit → ℝ := fun _ => 1
  let sigma2 : Unit → ℝ := fun _ => p
  let eta : Unit → ℝ := fun _ => η
  have hbern := Causalean.Stat.Concentration.iid_sum_bernstein_union_bound
    P g (fun _ => hf) (fun _ => hfint) b sigma2 eta
    (fun _ => by simp [b]) (fun _ => hp.le) (fun _ => hη)
    hN (fun _ => by simpa [g] using henvelope)
    (fun _ => by simpa [g] using hvariance)
  simpa [eta, sigma2, b, g, hmean] using hbern

/-- The one-observation treated microcell indicator has the population cell mass as mean. [For the stated inputs and conditions](hyp:d,P,m,j,k,ℓ), [the asserted conclusion holds](goal). -/
lemma treatedMicrocellIndicator_mean {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)) :
    ∫ z : Obs d, (if z.2.1 = true ∧ z.1 ∈ scaledMicroCell d m j k ℓ
      then (1 : ℝ) else 0) ∂P = microcellMass P m j k ℓ := by
  classical
  have hs : MeasurableSet {z : Obs d | z.2.1 = true ∧
      z.1 ∈ scaledMicroCell d m j k ℓ} := by
    exact ((measurableSet_singleton true).preimage
      (measurable_fst.comp measurable_snd)).inter
      ((orderedMass_scaledMicroCell_measurable d m j k ℓ).preimage measurable_fst)
  simpa [Set.indicator, microcellMass] using
    (integral_indicator_one (μ := P) hs)

/-- Bernstein deviation for one treated microcell count. [For the stated inputs and conditions](hyp:d,n,P,m,j,k,ℓ,hn,hq,η,hη), [the asserted conclusion holds](goal). -/
lemma treatedCount_deviation {d n : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1))
    (hn : 0 < n) (hq : 0 < microcellMass P m j k ℓ)
    (η : ℝ) (hη : 0 < η) :
    (Measure.pi (fun _ : Fin n => P)).real
      {ω | η ≤ |(treatedCount m j ω k ℓ : ℝ) -
        (n : ℝ) * microcellMass P m j k ℓ|} ≤
      2 * Real.exp (-η ^ 2 /
        (2 * (2 * (n : ℝ) * microcellMass P m j k ℓ + η))) := by
  let f : Obs d → ℝ := fun z =>
    if z.2.1 = true ∧ z.1 ∈ scaledMicroCell d m j k ℓ then 1 else 0
  have hf : Measurable f := treatedMicrocellIndicator_measurable m j k ℓ
  have hf01 : ∀ z, f z = 0 ∨ f z = 1 := by
    intro z
    dsimp [f]
    split_ifs <;> simp
  have hmean : ∫ z, f z ∂P = microcellMass P m j k ℓ :=
    treatedMicrocellIndicator_mean P m j k ℓ
  have htail := finiteProduct_bernoulliCount_deviation P f hf hf01 hn
    (microcellMass P m j k ℓ) η hq hη hmean
  convert htail using 1
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [treatedCount_eq_indicator_sum]

/-- A deviation threshold linear in the mean and the logarithmic budget. [For the stated inputs and conditions](hyp:d,n,P,m,j,k,ℓ,hn,hq,s,hs), [the asserted conclusion holds](goal). -/
lemma treatedCount_linear_deviation {d n : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1))
    (hn : 0 < n) (hq : 0 < microcellMass P m j k ℓ)
    (s : ℝ) (hs : 0 < s) :
    (Measure.pi (fun _ : Fin n => P)).real
      {ω | (n : ℝ) * microcellMass P m j k ℓ / 2 + 4 * s ≤
        |(treatedCount m j ω k ℓ : ℝ) -
          (n : ℝ) * microcellMass P m j k ℓ|} ≤
      2 * Real.exp (-s) := by
  let lam : ℝ := (n : ℝ) * microcellMass P m j k ℓ
  let η : ℝ := lam / 2 + 4 * s
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hden : 0 < 2 * (2 * lam + η) := by positivity
  have hquad : 2 * s * (2 * lam + η) ≤ η ^ 2 := by
    dsimp [η]
    nlinarith [sq_nonneg (lam / 2 - s), sq_nonneg s]
  have hexp : -η ^ 2 / (2 * (2 * lam + η)) ≤ -s := by
    apply (div_le_iff₀ hden).2
    nlinarith [hquad]
  have htail := treatedCount_deviation P m j k ℓ hn hq η hη
  have hbound := Real.exp_le_exp.mpr hexp
  dsimp [η, lam] at htail hbound ⊢
  simp only [mul_assoc] at htail hbound ⊢
  exact htail.trans (mul_le_mul_of_nonneg_left hbound (by norm_num))

/-- One design-measurable event controls any finite collection of treated
microcell counts, including cells taken from different candidate meshes. [For the stated inputs and conditions](hyp:d,n,P,Q,hIID,hn,ι,m,j,k,ℓ,hq,s,hs), [the asserted conclusion holds](goal). -/
lemma finiteFamily_treatedCount_event {d n : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (Q : Measure (Fin n → Obs d))
    (hIID : IIDSampleLaw Q P) (hn : 0 < n)
    {ι : Type*} [Fintype ι] (m : ℕ) (j : ι → ℕ)
    (k : ∀ a, Fin d → Fin (2 ^ j a))
    (ℓ : ∀ _a, Fin d → Fin (m + 1))
    (hq : ∀ a, 0 < microcellMass P m (j a) (k a) (ℓ a))
    (s : ℝ) (hs : 0 < s) :
    ∃ E : Set (Fin n → Obs d), MeasurableSet E ∧
      Q.real Eᶜ ≤ 2 * (Fintype.card ι : ℝ) * Real.exp (-s) ∧
      ∀ ω ∈ E, ∀ a : ι,
        |(treatedCount m (j a) ω (k a) (ℓ a) : ℝ) -
          (n : ℝ) * microcellMass P m (j a) (k a) (ℓ a)| <
        (n : ℝ) * microcellMass P m (j a) (k a) (ℓ a) / 2 + 4 * s := by
  let bad (a : ι) : Set (Fin n → Obs d) :=
    {ω | (n : ℝ) * microcellMass P m (j a) (k a) (ℓ a) / 2 + 4 * s ≤
      |(treatedCount m (j a) ω (k a) (ℓ a) : ℝ) -
        (n : ℝ) * microcellMass P m (j a) (k a) (ℓ a)|}
  let E : Set (Fin n → Obs d) := (⋃ a, bad a)ᶜ
  have hbadMeas (a : ι) : MeasurableSet (bad a) := by
    dsimp [bad]
    exact measurableSet_le measurable_const
      ((treatedCount_measurable m (j a) (k a) (ℓ a)).sub measurable_const).abs
  have hE : MeasurableSet E := by
    dsimp [E]
    exact (MeasurableSet.iUnion hbadMeas).compl
  refine ⟨E, hE, ?_, ?_⟩
  · dsimp [E]
    rw [compl_compl]
    calc
      Q.real (⋃ a, bad a) ≤ ∑ a : ι, Q.real (bad a) :=
        measureReal_iUnion_fintype_le bad
      _ ≤ ∑ _a : ι, 2 * Real.exp (-s) := by
        apply Finset.sum_le_sum
        intro a _
        rw [hIID]
        exact treatedCount_linear_deviation P m (j a) (k a) (ℓ a)
          hn (hq a) s hs
      _ = 2 * (Fintype.card ι : ℝ) * Real.exp (-s) := by
        simp [mul_assoc, mul_comm]
  · intro ω hω a
    have hnot : ω ∉ bad a := by
      intro ha
      exact hω (Set.mem_iUnion.mpr ⟨a, ha⟩)
    exact not_le.mp hnot

/-- The explicit simultaneous count event can be chosen saturated with
respect to the complete covariate-and-treatment design. [For the stated inputs and conditions](hyp:d,n,P,Q,hIID,hn,ι,m,j,k,ℓ,hq,s,hs), [the asserted conclusion holds](goal). -/
lemma finiteFamily_treatedCount_event_design_saturated {d n : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) (hIID : IIDSampleLaw Q P) (hn : 0 < n)
    {ι : Type*} [Fintype ι] (m : ℕ) (j : ι → ℕ)
    (k : ∀ a, Fin d → Fin (2 ^ j a))
    (ℓ : ∀ _a, Fin d → Fin (m + 1))
    (hq : ∀ a, 0 < microcellMass P m (j a) (k a) (ℓ a))
    (s : ℝ) (hs : 0 < s) :
    ∃ E : Set (Fin n → Obs d), MeasurableSet E ∧
      Q.real Eᶜ ≤ 2 * (Fintype.card ι : ℝ) * Real.exp (-s) ∧
      (∀ ω ∈ E, ∀ a : ι,
        |(treatedCount m (j a) ω (k a) (ℓ a) : ℝ) -
          (n : ℝ) * microcellMass P m (j a) (k a) (ℓ a)| <
        (n : ℝ) * microcellMass P m (j a) (k a) (ℓ a) / 2 + 4 * s) ∧
      ∀ ω ξ, (fun i => ((ξ i).1, (ξ i).2.1)) =
        (fun i => ((ω i).1, (ω i).2.1)) → (ω ∈ E ↔ ξ ∈ E) := by
  let bad (a : ι) : Set (Fin n → Obs d) :=
    {ω | (n : ℝ) * microcellMass P m (j a) (k a) (ℓ a) / 2 + 4 * s ≤
      |(treatedCount m (j a) ω (k a) (ℓ a) : ℝ) -
        (n : ℝ) * microcellMass P m (j a) (k a) (ℓ a)|}
  let E : Set (Fin n → Obs d) := (⋃ a, bad a)ᶜ
  have hbadMeas (a : ι) : MeasurableSet (bad a) := by
    dsimp [bad]
    exact measurableSet_le measurable_const
      ((treatedCount_measurable m (j a) (k a) (ℓ a)).sub measurable_const).abs
  have hE : MeasurableSet E := by
    dsimp [E]
    exact (MeasurableSet.iUnion hbadMeas).compl
  have hcountEq (ω ξ : Fin n → Obs d)
      (hdesign : (fun i => ((ξ i).1, (ξ i).2.1)) =
        (fun i => ((ω i).1, (ω i).2.1))) (a : ι) :
      treatedCount m (j a) ξ (k a) (ℓ a) =
        treatedCount m (j a) ω (k a) (ℓ a) := by
    classical
    unfold treatedCount
    congr 1
    ext i
    have hi := congrFun hdesign i
    have hx : (ξ i).1 = (ω i).1 :=
      congrArg (fun z : (Fin d → ℝ) × Bool => z.1) hi
    have ha : (ξ i).2.1 = (ω i).2.1 :=
      congrArg (fun z : (Fin d → ℝ) × Bool => z.2) hi
    simp [hx, ha]
  refine ⟨E, hE, ?_, ?_, ?_⟩
  · dsimp [E]
    rw [compl_compl]
    calc
      Q.real (⋃ a, bad a) ≤ ∑ a : ι, Q.real (bad a) :=
        measureReal_iUnion_fintype_le bad
      _ ≤ ∑ _a : ι, 2 * Real.exp (-s) := by
        apply Finset.sum_le_sum
        intro a _
        rw [hIID]
        exact treatedCount_linear_deviation P m (j a) (k a) (ℓ a)
          hn (hq a) s hs
      _ = 2 * (Fintype.card ι : ℝ) * Real.exp (-s) := by
        simp [mul_assoc, mul_comm]
  · intro ω hω a
    have hnot : ω ∉ bad a := by
      intro ha
      exact hω (Set.mem_iUnion.mpr ⟨a, ha⟩)
    exact not_le.mp hnot
  · intro ω ξ hdesign
    have hbadIff (a : ι) : ω ∈ bad a ↔ ξ ∈ bad a := by
      dsimp [bad]
      rw [hcountEq ω ξ hdesign a]
    constructor
    · intro hω hξ
      apply hω
      rcases Set.mem_iUnion.mp hξ with ⟨a, ha⟩
      exact Set.mem_iUnion.mpr ⟨a, (hbadIff a).mpr ha⟩
    · intro hξ hω
      apply hξ
      rcases Set.mem_iUnion.mp hω with ⟨a, ha⟩
      exact Set.mem_iUnion.mpr ⟨a, (hbadIff a).mp ha⟩

/-- A feasible count that exceeds the uniform deviation threshold also
controls its population mean from below. [For the stated inputs and conditions](hyp:N,q,t,ht,hlarge,hdeviation), [the asserted conclusion holds](goal). -/
lemma selectedCount_lower_of_uniform_deviation (N q t : ℝ)
    (ht : 0 ≤ t) (hlarge : 6 * t ≤ N)
    (hdeviation : |N - q| ≤ q / 2 + t) : q / 5 ≤ N := by
  rcases abs_le.mp hdeviation with ⟨hlower, hupper⟩
  linarith

/-- On a feasible mesh, a uniform count deviation yields the selected-cell
population lower bound once the feasibility threshold dominates the tail budget. [For the stated inputs and conditions](hyp:d,n,m,j,β,s,P,ω,k,ℓ,hfeasible,hbudget,hdeviation,hs), [the asserted conclusion holds](goal). -/
lemma selectedCount_lower_on_feasible_mesh {d n : ℕ} (m j : ℕ) (β s : ℝ)
    (P : Measure (Obs d)) [IsProbabilityMeasure P] (ω : Fin n → Obs d)
    (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1))
    (hfeasible : meshFeasible m β ω j)
    (hbudget : 24 * s ≤ meshWidth j ^ (-2 * β))
    (hdeviation : |(treatedCount m j ω k ℓ : ℝ) -
      (n : ℝ) * microcellMass P m j k ℓ| ≤
        (n : ℝ) * microcellMass P m j k ℓ / 2 + 4 * s)
    (hs : 0 ≤ s) :
    (n : ℝ) * microcellMass P m j k ℓ / 5 ≤
      treatedCount m j ω k ℓ := by
  have hcount : meshWidth j ^ (-2 * β) ≤
      (treatedCount m j ω k ℓ : ℝ) := hfeasible.2 k ℓ
  exact selectedCount_lower_of_uniform_deviation
    _ _ (4 * s) (by positivity) (by linarith) hdeviation

/-- An oracle-scale candidate is feasible when every expected treated count
dominates its feasibility threshold and the simultaneous deviation budget. [For the stated inputs and conditions](hyp:d,n,m,j,β,s,P,ω,hcandidate,hbudget,hmass,hdeviation), [the asserted conclusion holds](goal). -/
lemma oracleWitness_feasible_of_deviation {d n : ℕ} (m j : ℕ) (β s : ℝ)
    (P : Measure (Obs d)) [IsProbabilityMeasure P] (ω : Fin n → Obs d)
    (hcandidate : j ∈ meshIndices d n β)
    (hbudget : 4 * s ≤ meshWidth j ^ (-2 * β))
    (hmass : ∀ (k : Fin d → Fin (2 ^ j))
      (ℓ : Fin d → Fin (m + 1)),
      4 * meshWidth j ^ (-2 * β) ≤
        (n : ℝ) * microcellMass P m j k ℓ)
    (hdeviation : ∀ (k : Fin d → Fin (2 ^ j))
      (ℓ : Fin d → Fin (m + 1)),
      |(treatedCount m j ω k ℓ : ℝ) -
        (n : ℝ) * microcellMass P m j k ℓ| ≤
        (n : ℝ) * microcellMass P m j k ℓ / 2 + 4 * s) :
    meshFeasible m β ω j := by
  refine ⟨hcandidate, ?_⟩
  intro k ℓ
  have h := (abs_le.mp (hdeviation k ℓ)).1
  have hm := hmass k ℓ
  linarith

/-- A feasible oracle-scale witness and simultaneous count deviations imply
the selected mesh and selected-cell count bounds. [For the stated inputs and conditions](hyp:d,n,m,β,s,H,P,ω,j₀,hwitness,hwidth,hβ,hbudget,hs,hdeviation), [the asserted conclusion holds](goal). -/
lemma selectedCount_deterministic_bridge {d n : ℕ} (m : ℕ) (β s H : ℝ)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (ω : Fin n → Obs d) (j₀ : ℕ)
    (hwitness : meshFeasible m β ω j₀)
    (hwidth : meshWidth j₀ ≤ H)
    (hβ : 0 ≤ β)
    (hbudget : 24 * s ≤ meshWidth j₀ ^ (-2 * β))
    (hs : 0 ≤ s)
    (hdeviation : ∀ j ∈ meshIndices d n β,
      ∀ (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)),
        |(treatedCount m j ω k ℓ : ℝ) -
          (n : ℝ) * microcellMass P m j k ℓ| ≤
          (n : ℝ) * microcellMass P m j k ℓ / 2 + 4 * s) :
    0 < countSelectedMesh m β ω ∧
      countSelectedMesh m β ω ≤ H ∧
      ∀ (k : Fin d → Fin (2 ^ ((feasibleIndices m β ω).sup id)))
        (ℓ : Fin d → Fin (m + 1)),
        (n : ℝ) * microcellMass P m ((feasibleIndices m β ω).sup id) k ℓ / 5 ≤
          treatedCount m ((feasibleIndices m β ω).sup id) ω k ℓ := by
  classical
  let F := feasibleIndices m β ω
  have hj₀ : j₀ ∈ F := by
    simp only [F, feasibleIndices, Finset.mem_filter]
    exact ⟨hwitness.1, hwitness⟩
  have hF : F.Nonempty := ⟨j₀, hj₀⟩
  have hsup : j₀ ≤ F.sup id := Finset.le_sup (f := id) hj₀
  have hselected : countSelectedMesh m β ω = meshWidth (F.sup id) := by
    simp [countSelectedMesh, F, hF]
  have hwidthmono : meshWidth (F.sup id) ≤ meshWidth j₀ := by
    unfold meshWidth
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact neg_le_neg (by exact_mod_cast hsup)
  have hselectedBudget : 24 * s ≤ meshWidth (F.sup id) ^ (-2 * β) := by
    apply hbudget.trans
    exact Real.rpow_le_rpow_of_nonpos
      (by unfold meshWidth; positivity) hwidthmono (by linarith)
  have hfeasible : meshFeasible m β ω (F.sup id) := by
    have hmem : F.sup id ∈ F := by
      rw [← Finset.sup'_eq_sup hF id, ← Finset.max'_eq_sup' F hF]
      exact Finset.max'_mem F hF
    exact (Finset.mem_filter.mp hmem).2
  refine ⟨?_, ?_, ?_⟩
  · rw [hselected]
    unfold meshWidth
    positivity
  · rw [hselected]
    exact hwidthmono.trans hwidth
  · intro k ℓ
    exact selectedCount_lower_on_feasible_mesh m (F.sup id) β s P ω k ℓ
      hfeasible hselectedBudget
      (hdeviation (F.sup id) hfeasible.1 k ℓ) hs

/-- The density floor and global propensity tail give a quantitative lower
bound for each treated template microcell. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,P,hP,m,j,k,ℓ), [the asserted conclusion holds](goal). -/
lemma model_microcellMass_lower {d : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (m j : ℕ) (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1)) :
    ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * (templateEta d m * meshWidth j) ^ d) ^ (γ / (γ - 1)) ≤
      microcellMass P m j k ℓ := by
  rcases hP with ⟨hparams, hγ, Pc, hPc, μ₁, e, hEq, hmodel⟩
  have hC : 1 ≤ C := hparams.2.2.2.2.1
  have hcf : 0 < c_f := hparams.2.2.2.2.2.1
  have hη : 0 < templateEta d m := templateEta_pos d m
  have hh : 0 < meshWidth j := by unfold meshWidth; positivity
  letI : IsProbabilityMeasure Pc := hPc
  have hlower := orderedMass_microcell_lower β B L C c_f γ
    (c_f * (templateEta d m * meshWidth j) ^ d) Pc μ₁ e hmodel
    hC hγ (by positivity)
    (scaledMicroCell d m j k ℓ)
    (orderedMass_scaledMicroCell_measurable d m j k ℓ)
    (by
      convert orderedMass_microcell_covariate_lower d m j β B L C c_f γ
        Pc μ₁ e hmodel k ℓ using 1
      rw [orderedMass_microcell_volume_toReal d m j hη.le])
  rw [← hEq] at hlower
  exact hlower

/-- Every template microcell has positive treated mass under the model's
density floor and global propensity-tail condition. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,P,hP,m,j,k,ℓ), [the asserted conclusion holds](goal). -/
lemma model_microcellMass_pos {d : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (m j : ℕ) (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1)) :
    0 < microcellMass P m j k ℓ := by
  have hparams := hP.1
  have hγ := hP.2.1
  have hC : 1 ≤ C := hparams.2.2.2.2.1
  have hcf : 0 < c_f := hparams.2.2.2.2.2.1
  have hη : 0 < templateEta d m := templateEta_pos d m
  have hh : 0 < meshWidth j := by unfold meshWidth; positivity
  have hpositive : 0 < ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * (templateEta d m * meshWidth j) ^ d) ^ (γ / (γ - 1)) := by
    positivity
  exact lt_of_lt_of_le hpositive (model_microcellMass_lower P hP m j k ℓ)

/-- Express the model's treated microcell lower bound as a coefficient times
the effective-dimension power of the dyadic width. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,P,hP,m,j,k,ℓ), [the asserted conclusion holds](goal). -/
lemma model_microcellMass_effectiveDimension_lower
    {d : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (m j : ℕ) (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1)) :
    ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)) *
      meshWidth j ^ effectiveDimension d γ ≤
      microcellMass P m j k ℓ := by
  have hcf : 0 ≤ c_f := hP.1.2.2.2.2.2.1.le
  have hη : 0 ≤ templateEta d m := (templateEta_pos d m).le
  have hh : 0 ≤ meshWidth j := by unfold meshWidth; positivity
  have hpow : (meshWidth j ^ d) ^ (γ / (γ - 1)) =
      meshWidth j ^ effectiveDimension d γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh]
    congr 1
    unfold effectiveDimension
    ring
  have heq :
      (c_f * (templateEta d m * meshWidth j) ^ d) ^ (γ / (γ - 1)) =
        (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)) *
          meshWidth j ^ effectiveDimension d γ := by
    rw [mul_pow, ← mul_assoc,
      Real.mul_rpow (mul_nonneg hcf (pow_nonneg hη _)) (pow_nonneg hh _)]
    rw [hpow]
  simpa only [heq, mul_assoc] using model_microcellMass_lower P hP m j k ℓ
end CausalSmith.Stat.WeakOverlap
