module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Information
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Occupancy events and coupling transport for converse bounds -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

lemma pi_singleton_core_event {α : Type*} [MeasurableSpace α] {N : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ]
    (S Q : Set α) (i : Fin N) :
    (Measure.pi fun _ : Fin N => μ)
        {x | x i ∈ S ∧ ∀ k, k ≠ i → x k ∉ Q} =
      ∏ k : Fin N, if k = i then μ S else μ Qᶜ := by
  have hevent : {x : Fin N → α | x i ∈ S ∧ ∀ k, k ≠ i → x k ∉ Q} =
      Set.pi Set.univ (fun k => if k = i then S else Qᶜ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨hi, hk⟩ k
      by_cases hki : k = i
      · simpa [hki] using hi
      · simp [hki, hk k hki]
    · intro hx
      constructor
      · simpa using hx i
      · intro k hki
        simpa [hki] using hx k
  rw [hevent, MeasureTheory.Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hki : k = i <;> simp [hki]

lemma measurableSet_singleton_core_event {α : Type*} [MeasurableSpace α]
    {N : ℕ} (S Q : Set α) (hS : MeasurableSet S) (hQ : MeasurableSet Q)
    (i : Fin N) :
    MeasurableSet {x : Fin N → α | x i ∈ S ∧ ∀ k, k ≠ i → x k ∉ Q} := by
  rw [show {x : Fin N → α | x i ∈ S ∧ ∀ k, k ≠ i → x k ∉ Q} =
      Set.pi Set.univ (fun k => if k = i then S else Qᶜ) by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨hi, hk⟩ k
      by_cases hki : k = i
      · simpa [hki] using hi
      · simp [hki, hk k hki]
    · intro hx
      constructor
      · simpa using hx i
      · intro k hki
        simpa [hki] using hx k]
  exact MeasurableSet.univ_pi
    (fun k => by by_cases hki : k = i <;> simp [hki, hS, hQ])

lemma pairwiseDisjoint_singleton_core_event {α : Type*} {N : ℕ}
    (S Q : Set α) (hSQ : S ⊆ Q) :
    Pairwise fun i j : Fin N => Disjoint
      {x : Fin N → α | x i ∈ S ∧ ∀ k, k ≠ i → x k ∉ Q}
      {x : Fin N → α | x j ∈ S ∧ ∀ k, k ≠ j → x k ∉ Q} := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact (hxi.2 j hij.symm) (hSQ hxj.1)

/-- Exact mass of the event that a unique labelled observation lies in the
core `S`, while all other observations avoid its containing cell `Q`. -/
lemma pi_exists_unique_core_event {α : Type*} [MeasurableSpace α] {N : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ]
    (S Q : Set α) (hS : MeasurableSet S) (hQ : MeasurableSet Q)
    (hSQ : S ⊆ Q) :
    (Measure.pi fun _ : Fin N => μ)
        (⋃ i : Fin N, {x | x i ∈ S ∧ ∀ k, k ≠ i → x k ∉ Q}) =
      ∑' i : Fin N, ∏ k : Fin N, if k = i then μ S else μ Qᶜ := by
  rw [measure_iUnion (pairwiseDisjoint_singleton_core_event S Q hSQ)
    (fun i => measurableSet_singleton_core_event S Q hS hQ i)]
  apply tsum_congr
  exact fun i => pi_singleton_core_event μ S Q i

/-- Real-valued form of `pi_exists_unique_core_event`, convenient for
Bernoulli lower bounds. -/
lemma pi_exists_unique_core_event_real {α : Type*} [MeasurableSpace α] {N : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ]
    (S Q : Set α) (hS : MeasurableSet S) (hQ : MeasurableSet Q)
    (hSQ : S ⊆ Q) :
    (Measure.pi fun _ : Fin N => μ).real
        (⋃ i : Fin N, {x | x i ∈ S ∧ ∀ k, k ≠ i → x k ∉ Q}) =
      ∑ i : Fin N, ∏ k : Fin N,
        if k = i then μ.real S else μ.real Qᶜ := by
  rw [measureReal_def, pi_exists_unique_core_event μ S Q hS hQ hSQ,
    tsum_fintype, ENNReal.toReal_sum (fun i _ =>
      ENNReal.prod_ne_top fun k _ => by
        by_cases hki : k = i <;> simp [hki] <;> finiteness)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hki : k = i <;> simp [hki, measureReal_def]

lemma fin_prod_ite_eq_mul_pow {N : ℕ} (i : Fin N) (a b : ℝ) :
    (∏ k : Fin N, if k = i then a else b) = a * b ^ (N - 1) := by
  calc
    (∏ k : Fin N, if k = i then a else b) =
        (if i = i then a else b) *
          ∏ k ∈ Finset.univ.erase i, (if k = i then a else b) :=
      (Finset.mul_prod_erase Finset.univ
        (fun k : Fin N => if k = i then a else b) (Finset.mem_univ i)).symm
    _ = a * ∏ _k ∈ Finset.univ.erase i, b := by
      congr 1
      · simp
      · apply Finset.prod_congr rfl
        intro k hk
        simp [Finset.mem_erase.mp hk |>.1]
    _ = a * b ^ (N - 1) := by
      rw [Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp

lemma probability_compl_pow_ge_half {α : Type*} [MeasurableSpace α]
    {N : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (Q : Set α) (hQ : MeasurableSet Q) (hN : 1 ≤ N)
    (hsmall : (N : ℝ) * μ.real Q ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ (μ.real Qᶜ) ^ (N - 1) := by
  have hQ0 : 0 ≤ μ.real Q := measureReal_nonneg
  have hQ1 : μ.real Q ≤ 1 := by
    simpa using (measureReal_le_prob : μ.real Q ≤ 1)
  have hcomp : μ.real Qᶜ = 1 - μ.real Q := by
    rw [measureReal_compl hQ, probReal_univ]
  have hcomp0 : 0 ≤ μ.real Qᶜ := measureReal_nonneg
  have hbern := one_add_mul_sub_le_pow
    (a := μ.real Qᶜ) (by linarith : (-1 : ℝ) ≤ μ.real Qᶜ) (N - 1)
  have hNm1 : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
  have hprod : ((N - 1 : ℕ) : ℝ) * μ.real Q ≤ 1 / 2 := by
    exact (mul_le_mul_of_nonneg_right hNm1 hQ0).trans hsmall
  rw [hcomp] at hbern
  have hlower : (1 / 2 : ℝ) ≤
      1 + ((N - 1 : ℕ) : ℝ) * ((1 - μ.real Q) - 1) := by
    nlinarith
  rw [hcomp]
  exact hlower.trans hbern

/-- If the expected number of observations in `Q` is at most one half, the
probability of a unique observation in the measurable core `S` is at least
half its first-moment value. -/
lemma pi_exists_unique_core_event_real_lower {α : Type*} [MeasurableSpace α]
    {N : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (S Q : Set α) (hS : MeasurableSet S) (hQ : MeasurableSet Q)
    (hSQ : S ⊆ Q) (hN : 1 ≤ N)
    (hsmall : (N : ℝ) * μ.real Q ≤ 1 / 2) :
    (N : ℝ) * μ.real S / 2 ≤
      (Measure.pi fun _ : Fin N => μ).real
        (⋃ i : Fin N, {x | x i ∈ S ∧ ∀ k, k ≠ i → x k ∉ Q}) := by
  rw [pi_exists_unique_core_event_real μ S Q hS hQ hSQ]
  simp_rw [fin_prod_ite_eq_mul_pow]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hp := probability_compl_pow_ge_half μ Q hQ hN hsmall
  have hS0 : 0 ≤ μ.real S := measureReal_nonneg
  have hmul : μ.real S * (1 / 2 : ℝ) ≤
      μ.real S * (μ.real Qᶜ) ^ (N - 1) :=
    mul_le_mul_of_nonneg_left hp hS0
  calc
    (N : ℝ) * μ.real S / 2 =
        (N : ℝ) * (μ.real S * (1 / 2 : ℝ)) := by ring
    _ ≤ (N : ℝ) * (μ.real S * (μ.real Qᶜ) ^ (N - 1)) :=
      mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg N)

lemma exists_pilot_overlap_coupling
    {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hB : 0 ≤ B)
    (hKL : InformationTheory.klDiv μ ν ≤ ENNReal.ofReal B) :
    ∃ Γ : Measure (Z × Z), Causalean.Stat.IsCoupling Γ μ ν ∧
      ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-B)) ≤ Γ {z | z.1 = z.2} := by
  letI : MeasurableEq Z := Causalean.Stat.measurableEqOfStandardBorel Z
  let Γ := Causalean.Stat.overlapCoupling μ ν
  refine ⟨Γ, ?_, ?_⟩
  · exact ⟨inferInstance,
      Causalean.Stat.overlapCoupling_map_fst μ ν,
      Causalean.Stat.overlapCoupling_map_snd μ ν⟩
  · have hreal := Causalean.Stat.overlap_ge_exp_neg_klBudget μ ν hB hKL
    exact (ENNReal.ofReal_le_ofReal hreal).trans
      (Causalean.Stat.overlapCoupling_eq_mass_ge μ ν)

/-- Adding independent common randomness to a coupling preserves each
marginal.  This is the transport identity used for the two adjacent risks. -/
lemma coupling_prod_map_left {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (μ ν : Measure A) (η : Measure B)
    (Γ : Measure (A × A)) [SFinite Γ] [SFinite η]
    (hΓ : Causalean.Stat.IsCoupling Γ μ ν) :
    (Γ.prod η).map (fun z : (A × A) × B => (z.1.1, z.2)) = μ.prod η := by
  have h := Measure.map_prod_map Γ η measurable_fst measurable_id
  rw [hΓ.map_fst, Measure.map_id] at h
  have hfun : (fun z : (A × A) × B => (z.1.1, z.2)) =
      Prod.map Prod.fst id := by
    funext z
    rfl
  rw [hfun]
  exact h.symm

lemma coupling_prod_map_right {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (μ ν : Measure A) (η : Measure B)
    (Γ : Measure (A × A)) [SFinite Γ] [SFinite η]
    (hΓ : Causalean.Stat.IsCoupling Γ μ ν) :
    (Γ.prod η).map (fun z : (A × A) × B => (z.1.2, z.2)) = ν.prod η := by
  have h := Measure.map_prod_map Γ η measurable_snd measurable_id
  rw [hΓ.map_snd, Measure.map_id] at h
  have hfun : (fun z : (A × A) × B => (z.1.2, z.2)) =
      Prod.map Prod.snd id := by
    funext z
    rfl
  rw [hfun]
  exact h.symm

lemma integral_coupling_prod_left {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (μ ν : Measure A) (η : Measure B)
    (Γ : Measure (A × A)) [SFinite Γ] [SFinite η]
    (hΓ : Causalean.Stat.IsCoupling Γ μ ν) (f : A × B → ℝ)
    (hf : AEStronglyMeasurable f (μ.prod η)) :
    (∫ z, f (z.1.1, z.2) ∂Γ.prod η) = ∫ z, f z ∂μ.prod η := by
  let φ : (A × A) × B → A × B := fun z => (z.1.1, z.2)
  have hφ : Measurable φ :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hmap : (Γ.prod η).map φ = μ.prod η :=
    coupling_prod_map_left μ ν η Γ hΓ
  have hfmap : AEStronglyMeasurable f ((Γ.prod η).map φ) := by
    rw [hmap]
    exact hf
  have hi := integral_map hφ.aemeasurable hfmap
  rw [hmap] at hi
  exact hi.symm

lemma integral_coupling_prod_right {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (μ ν : Measure A) (η : Measure B)
    (Γ : Measure (A × A)) [SFinite Γ] [SFinite η]
    (hΓ : Causalean.Stat.IsCoupling Γ μ ν) (f : A × B → ℝ)
    (hf : AEStronglyMeasurable f (ν.prod η)) :
    (∫ z, f (z.1.2, z.2) ∂Γ.prod η) = ∫ z, f z ∂ν.prod η := by
  let φ : (A × A) × B → A × B := fun z => (z.1.2, z.2)
  have hφ : Measurable φ :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hmap : (Γ.prod η).map φ = ν.prod η :=
    coupling_prod_map_right μ ν η Γ hΓ
  have hfmap : AEStronglyMeasurable f ((Γ.prod η).map φ) := by
    rw [hmap]
    exact hf
  have hi := integral_map hφ.aemeasurable hfmap
  rw [hmap] at hi
  exact hi.symm

/-- Integrate a pointwise two-risk lower bound that is available only on a
measurable event.  This small wrapper keeps the coupling argument focused on
constructing the event and proving its mass. -/
lemma measureReal_mul_le_integral_add_of_event
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (f g : Ω → ℝ) (S : Set Ω) (c : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hS : MeasurableSet S) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfg : ∀ x ∈ S, c ≤ f x + g x) :
    c * μ.real S ≤ (∫ x, f x ∂μ) + ∫ x, g x ∂μ := by
  have hind : Integrable (S.indicator fun _ => c) μ :=
    (integrable_const c).indicator hS
  have hpoint (x : Ω) : S.indicator (fun _ => c) x ≤ f x + g x := by
    by_cases hx : x ∈ S
    · simpa [Set.indicator_of_mem hx] using hfg x hx
    · rw [Set.indicator_of_notMem hx]
      exact add_nonneg (hf0 x) (hg0 x)
  have hmono := integral_mono hind (hf.add hg) hpoint
  rw [integral_indicator_const c hS] at hmono
  change μ.real S • c ≤ ∫ x, f x + g x ∂μ at hmono
  rw [integral_add hf hg] at hmono
  simpa [smul_eq_mul, mul_comm] using hmono

/-- The event that a coupling agrees and an independent draw belongs to `E`
has the product of the agreement mass and the mass of `E`. -/
lemma coupling_agreement_prod_event_mass
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableEq A]
    (Γ : Measure (A × A)) (η : Measure B) [SFinite Γ] [SFinite η]
    (E : Set B) (hE : MeasurableSet E) :
    (Γ.prod η).real {z : (A × A) × B | z.1.1 = z.1.2 ∧ z.2 ∈ E} =
      Γ.real {z : A × A | z.1 = z.2} * η.real E := by
  have hset : {z : (A × A) × B | z.1.1 = z.1.2 ∧ z.2 ∈ E} =
      {z : A × A | z.1 = z.2} ×ˢ E := by
    ext z
    rfl
  rw [hset, measureReal_prod_prod]

/-- Transport two integrable marginal losses to a coupling with common
randomness, then integrate a lower bound valid on a coupled event. -/
lemma coupling_integral_add_lower_of_event
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ ν : Measure A) (η : Measure B)
    (Γ : Measure (A × A)) [SFinite Γ] [IsFiniteMeasure η]
    (hΓ : Causalean.Stat.IsCoupling Γ μ ν)
    (f g : A × B → ℝ) (S : Set ((A × A) × B)) (c : ℝ)
    (hf : Integrable f (μ.prod η)) (hg : Integrable g (ν.prod η))
    (hS : MeasurableSet S)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z)
    (hfg : ∀ z ∈ S, c ≤ f (z.1.1, z.2) + g (z.1.2, z.2)) :
    c * (Γ.prod η).real S ≤
      (∫ z, f z ∂μ.prod η) + ∫ z, g z ∂ν.prod η := by
  letI : IsProbabilityMeasure Γ := hΓ.isProbabilityMeasure
  let φ₀ : (A × A) × B → A × B := fun z => (z.1.1, z.2)
  let φ₁ : (A × A) × B → A × B := fun z => (z.1.2, z.2)
  have hφ₀ : Measurable φ₀ :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hφ₁ : Measurable φ₁ :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hmap₀ : (Γ.prod η).map φ₀ = μ.prod η :=
    coupling_prod_map_left μ ν η Γ hΓ
  have hmap₁ : (Γ.prod η).map φ₁ = ν.prod η :=
    coupling_prod_map_right μ ν η Γ hΓ
  have hf' : Integrable (fun z => f (z.1.1, z.2)) (Γ.prod η) := by
    change Integrable (f ∘ φ₀) (Γ.prod η)
    exact (show Integrable f ((Γ.prod η).map φ₀) by
      rw [hmap₀]
      exact hf).comp_aemeasurable hφ₀.aemeasurable
  have hg' : Integrable (fun z => g (z.1.2, z.2)) (Γ.prod η) := by
    change Integrable (g ∘ φ₁) (Γ.prod η)
    exact (show Integrable g ((Γ.prod η).map φ₁) by
      rw [hmap₁]
      exact hg).comp_aemeasurable hφ₁.aemeasurable
  have hlower := measureReal_mul_le_integral_add_of_event
    (fun z => f (z.1.1, z.2)) (fun z => g (z.1.2, z.2)) S c
    hf' hg' hS (fun z => hf0 _) (fun z => hg0 _) hfg
  rw [integral_coupling_prod_left μ ν η Γ hΓ f hf.aestronglyMeasurable,
    integral_coupling_prod_right μ ν η Γ hΓ g hg.aestronglyMeasurable] at hlower
  exact hlower

end CausalSmith.Experimentation.PilotscorePairingFrontier
