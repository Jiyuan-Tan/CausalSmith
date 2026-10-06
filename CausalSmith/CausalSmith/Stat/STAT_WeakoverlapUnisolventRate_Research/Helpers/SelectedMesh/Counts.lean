module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass.Setwise
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Counts.Budget

/-! # Oracle witness and simultaneous selected-count event -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory
open scoped Classical

/-- A single event controls treated counts over every candidate dyadic mesh
and every template cell. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,Q,hIID,hn,s,hs), [the asserted conclusion holds](goal). -/
lemma model_all_treatedCount_deviation {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (Q : Measure (Fin n → Obs d)) (hIID : IIDSampleLaw Q P)
    (hn : 0 < n) (s : ℝ) (hs : 0 < s) :
    ∃ E : Set (Fin n → Obs d), MeasurableSet E ∧
      Q.real Eᶜ ≤ 2 * (Fintype.card
        (Σ j : {j // j ∈ meshIndices d n β},
          (Fin d → Fin (2 ^ j.val)) ×
            (Fin d → Fin (polynomialDegree β + 1))) : ℝ) * Real.exp (-s) ∧
      ∀ ω ∈ E, ∀ j ∈ meshIndices d n β,
        ∀ (k : Fin d → Fin (2 ^ j))
          (ℓ : Fin d → Fin (polynomialDegree β + 1)),
        |(treatedCount (polynomialDegree β) j ω k ℓ : ℝ) -
          (n : ℝ) * microcellMass P (polynomialDegree β) j k ℓ| <
        (n : ℝ) * microcellMass P (polynomialDegree β) j k ℓ / 2 + 4 * s := by
  classical
  let ι := Σ j : {j // j ∈ meshIndices d n β},
    (Fin d → Fin (2 ^ j.val)) × (Fin d → Fin (polynomialDegree β + 1))
  let jf : ι → ℕ := fun a => a.1.val
  let kf : ∀ a : ι, Fin d → Fin (2 ^ jf a) := fun a => a.2.1
  let ℓf : ∀ _a : ι, Fin d → Fin (polynomialDegree β + 1) := fun a => a.2.2
  obtain ⟨E, hE, hbad, hdev⟩ :=
    finiteFamily_treatedCount_event P Q hIID hn (polynomialDegree β)
      jf kf ℓf (fun a => model_microcellMass_pos P hP _ _ _ _) s hs
  refine ⟨E, hE, hbad, ?_⟩
  intro ω hω j hj k ℓ
  let a : ι := ⟨⟨j, hj⟩, (k, ℓ)⟩
  simpa [jf, kf, ℓf, a] using hdev ω hω a

/-- The all-candidate count deviation event can be retained together with
its saturation under equality of covariates and treatment arms. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,Q,hIID,hn,s,hs), [the asserted conclusion holds](goal). -/
lemma model_all_treatedCount_deviation_design_saturated
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (Q : Measure (Fin n → Obs d)) (hIID : IIDSampleLaw Q P)
    (hn : 0 < n) (s : ℝ) (hs : 0 < s) :
    ∃ E : Set (Fin n → Obs d), MeasurableSet E ∧
      Q.real Eᶜ ≤ 2 * (Fintype.card
        (Σ j : {j // j ∈ meshIndices d n β},
          (Fin d → Fin (2 ^ j.val)) ×
            (Fin d → Fin (polynomialDegree β + 1))) : ℝ) * Real.exp (-s) ∧
      (∀ ω ∈ E, ∀ j ∈ meshIndices d n β,
        ∀ (k : Fin d → Fin (2 ^ j))
          (ℓ : Fin d → Fin (polynomialDegree β + 1)),
        |(treatedCount (polynomialDegree β) j ω k ℓ : ℝ) -
          (n : ℝ) * microcellMass P (polynomialDegree β) j k ℓ| <
        (n : ℝ) * microcellMass P (polynomialDegree β) j k ℓ / 2 + 4 * s) ∧
      ∀ ω ξ, (fun i => ((ξ i).1, (ξ i).2.1)) =
        (fun i => ((ω i).1, (ω i).2.1)) → (ω ∈ E ↔ ξ ∈ E) := by
  classical
  let ι := Σ j : {j // j ∈ meshIndices d n β},
    (Fin d → Fin (2 ^ j.val)) × (Fin d → Fin (polynomialDegree β + 1))
  let jf : ι → ℕ := fun a => a.1.val
  let kf : ∀ a : ι, Fin d → Fin (2 ^ jf a) := fun a => a.2.1
  let ℓf : ∀ _a : ι, Fin d → Fin (polynomialDegree β + 1) := fun a => a.2.2
  obtain ⟨E, hE, hbad, hdev, hsat⟩ :=
    finiteFamily_treatedCount_event_design_saturated P Q hIID hn
      (polynomialDegree β) jf kf ℓf
      (fun a => model_microcellMass_pos P hP _ _ _ _) s hs
  refine ⟨E, hE, hbad, ?_, hsat⟩
  intro ω hω j hj k ℓ
  let a : ι := ⟨⟨j, hj⟩, (k, ℓ)⟩
  simpa [jf, kf, ℓf, a] using hdev ω hω a

/-- The simultaneous deviation event gives the selected-mesh count envelope
once an oracle-scale candidate satisfies the deterministic mass and budget
bounds. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,Q,hIID,hn,hβ,s,K,hs,hfailure,j₀,hcandidate,hwidth,hbudget,hmass), [the asserted conclusion holds](goal). -/
lemma selectedCountEvent_of_oracle_witness {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (Q : Measure (Fin n → Obs d)) (hIID : IIDSampleLaw Q P)
    (hn : 0 < n) (hβ : 0 ≤ β) (s K : ℝ) (hs : 0 < s)
    (hfailure : 2 * (Fintype.card
      (Σ j : {j // j ∈ meshIndices d n β},
        (Fin d → Fin (2 ^ j.val)) ×
          (Fin d → Fin (polynomialDegree β + 1))) : ℝ) *
        Real.exp (-s) ≤ (n : ℝ) ^ (-2 : ℝ))
    (j₀ : ℕ) (hcandidate : j₀ ∈ meshIndices d n β)
    (hwidth : meshWidth j₀ ≤ K * oracleMesh d n β γ)
    (hbudget : 24 * s ≤ meshWidth j₀ ^ (-2 * β))
    (hmass : ∀ (k : Fin d → Fin (2 ^ j₀))
      (ℓ : Fin d → Fin (polynomialDegree β + 1)),
      4 * meshWidth j₀ ^ (-2 * β) ≤
        (n : ℝ) * microcellMass P (polynomialDegree β) j₀ k ℓ) :
    ∃ E : Set (Fin n → Obs d),
      MeasurableSet E ∧ Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
      ∀ ω ∈ E,
        0 < countSelectedMesh (polynomialDegree β) β ω ∧
        countSelectedMesh (polynomialDegree β) β ω ≤ K * oracleMesh d n β γ ∧
        ∀ (k : Fin d → Fin (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)))
          (ℓ : Fin d → Fin (polynomialDegree β + 1)),
          (n : ℝ) * microcellMass P (polynomialDegree β)
            ((feasibleIndices (polynomialDegree β) β ω).sup id) k ℓ / 5 ≤
            treatedCount (polynomialDegree β)
              ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k ℓ := by
  obtain ⟨E, hE, hbad, hdev⟩ :=
    model_all_treatedCount_deviation P hP Q hIID hn s hs
  refine ⟨E, hE, hbad.trans hfailure, ?_⟩
  intro ω hω
  have hwitness : meshFeasible (polynomialDegree β) β ω j₀ :=
    oracleWitness_feasible_of_deviation (polynomialDegree β) j₀ β s P ω
      hcandidate (by linarith) hmass
      (fun k ℓ => (hdev ω hω j₀ hcandidate k ℓ).le)
  exact selectedCount_deterministic_bridge (polynomialDegree β) β s
    (K * oracleMesh d n β γ) P ω j₀ hwitness hwidth hβ hbudget
    hs.le (fun j hj k ℓ => (hdev ω hω j hj k ℓ).le)

/-- The oracle selected-count event can be chosen design-saturated. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,Q,hIID,hn,hβ,s,K,hs,hfailure,j₀,hcandidate,hwidth,hbudget,hmass), [the asserted conclusion holds](goal). -/
lemma selectedCountEvent_of_oracle_witness_design_saturated
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (Q : Measure (Fin n → Obs d)) (hIID : IIDSampleLaw Q P)
    (hn : 0 < n) (hβ : 0 ≤ β) (s K : ℝ) (hs : 0 < s)
    (hfailure : 2 * (Fintype.card
      (Σ j : {j // j ∈ meshIndices d n β},
        (Fin d → Fin (2 ^ j.val)) ×
          (Fin d → Fin (polynomialDegree β + 1))) : ℝ) *
        Real.exp (-s) ≤ (n : ℝ) ^ (-2 : ℝ))
    (j₀ : ℕ) (hcandidate : j₀ ∈ meshIndices d n β)
    (hwidth : meshWidth j₀ ≤ K * oracleMesh d n β γ)
    (hbudget : 24 * s ≤ meshWidth j₀ ^ (-2 * β))
    (hmass : ∀ (k : Fin d → Fin (2 ^ j₀))
      (ℓ : Fin d → Fin (polynomialDegree β + 1)),
      4 * meshWidth j₀ ^ (-2 * β) ≤
        (n : ℝ) * microcellMass P (polynomialDegree β) j₀ k ℓ) :
    ∃ E : Set (Fin n → Obs d),
      MeasurableSet E ∧ Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
      (∀ ω ∈ E,
        0 < countSelectedMesh (polynomialDegree β) β ω ∧
        countSelectedMesh (polynomialDegree β) β ω ≤
          K * oracleMesh d n β γ ∧
        ∀ (k : Fin d → Fin
            (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)))
          (ℓ : Fin d → Fin (polynomialDegree β + 1)),
          (n : ℝ) * microcellMass P (polynomialDegree β)
            ((feasibleIndices (polynomialDegree β) β ω).sup id) k ℓ / 5 ≤
            treatedCount (polynomialDegree β)
              ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k ℓ) ∧
      ∀ ω ξ, (fun i => ((ξ i).1, (ξ i).2.1)) =
        (fun i => ((ω i).1, (ω i).2.1)) → (ω ∈ E ↔ ξ ∈ E) := by
  obtain ⟨E, hE, hbad, hdev, hsat⟩ :=
    model_all_treatedCount_deviation_design_saturated
      P hP Q hIID hn s hs
  refine ⟨E, hE, hbad.trans hfailure, ?_, hsat⟩
  intro ω hω
  have hwitness : meshFeasible (polynomialDegree β) β ω j₀ :=
    oracleWitness_feasible_of_deviation (polynomialDegree β) j₀ β s P ω
      hcandidate (by linarith) hmass
      (fun k ℓ => (hdev ω hω j₀ hcandidate k ℓ).le)
  exact selectedCount_deterministic_bridge (polynomialDegree β) β s
    (K * oracleMesh d n β γ) P ω j₀ hwitness hwidth hβ hbudget
    hs.le (fun j hj k ℓ => (hdev ω hω j hj k ℓ).le)

/-- Once the oracle candidate meets its deterministic mass and budget
conditions, the logarithmic finite-family budget gives the desired event. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,Q,hIID,hn,hβ,K,j₀,hcandidate,hwidth,hbudget,hmass), [the asserted conclusion holds](goal). -/
lemma selectedCountEvent_of_log_oracle_witness
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (Q : Measure (Fin n → Obs d)) (hIID : IIDSampleLaw Q P)
    (hn : 2 ≤ n) (hβ : 0 ≤ β) (K : ℝ)
    (j₀ : ℕ) (hcandidate : j₀ ∈ meshIndices d n β)
    (hwidth : meshWidth j₀ ≤ K * oracleMesh d n β γ)
    (hbudget : 24 * Real.log (2 *
      ((Fintype.card
        (Σ j : {j // j ∈ meshIndices d n β},
          (Fin d → Fin (2 ^ j.val)) ×
            (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
        (n : ℝ) ^ 2) ≤ meshWidth j₀ ^ (-2 * β))
    (hmass : ∀ (k : Fin d → Fin (2 ^ j₀))
      (ℓ : Fin d → Fin (polynomialDegree β + 1)),
      4 * meshWidth j₀ ^ (-2 * β) ≤
        (n : ℝ) * microcellMass P (polynomialDegree β) j₀ k ℓ) :
    ∃ E : Set (Fin n → Obs d),
      MeasurableSet E ∧ Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
      ∀ ω ∈ E,
        0 < countSelectedMesh (polynomialDegree β) β ω ∧
        countSelectedMesh (polynomialDegree β) β ω ≤ K * oracleMesh d n β γ ∧
        ∀ (k : Fin d → Fin (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)))
          (ℓ : Fin d → Fin (polynomialDegree β + 1)),
          (n : ℝ) * microcellMass P (polynomialDegree β)
            ((feasibleIndices (polynomialDegree β) β ω).sup id) k ℓ / 5 ≤
            treatedCount (polynomialDegree β)
              ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k ℓ := by
  obtain ⟨hs, hfailure⟩ := selectedCount_log_budget d n β hn
  exact selectedCountEvent_of_oracle_witness P hP Q hIID (by omega)
    hβ _ K hs hfailure j₀ hcandidate hwidth hbudget hmass

/-- Log-budget specialization retaining design saturation. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,Q,hIID,hn,hβ,K,j₀,hcandidate,hwidth,hbudget,hmass), [the asserted conclusion holds](goal). -/
lemma selectedCountEvent_of_log_oracle_witness_design_saturated
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (Q : Measure (Fin n → Obs d)) (hIID : IIDSampleLaw Q P)
    (hn : 2 ≤ n) (hβ : 0 ≤ β) (K : ℝ)
    (j₀ : ℕ) (hcandidate : j₀ ∈ meshIndices d n β)
    (hwidth : meshWidth j₀ ≤ K * oracleMesh d n β γ)
    (hbudget : 24 * Real.log (2 *
      ((Fintype.card
        (Σ j : {j // j ∈ meshIndices d n β},
          (Fin d → Fin (2 ^ j.val)) ×
            (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
        (n : ℝ) ^ 2) ≤ meshWidth j₀ ^ (-2 * β))
    (hmass : ∀ (k : Fin d → Fin (2 ^ j₀))
      (ℓ : Fin d → Fin (polynomialDegree β + 1)),
      4 * meshWidth j₀ ^ (-2 * β) ≤
        (n : ℝ) * microcellMass P (polynomialDegree β) j₀ k ℓ) :
    ∃ E : Set (Fin n → Obs d), MeasurableSet E ∧
      Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
      (∀ ω ∈ E,
        0 < countSelectedMesh (polynomialDegree β) β ω ∧
        countSelectedMesh (polynomialDegree β) β ω ≤ K * oracleMesh d n β γ ∧
        ∀ (k : Fin d → Fin
            (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)))
          (ℓ : Fin d → Fin (polynomialDegree β + 1)),
          (n : ℝ) * microcellMass P (polynomialDegree β)
            ((feasibleIndices (polynomialDegree β) β ω).sup id) k ℓ / 5 ≤
            treatedCount (polynomialDegree β)
              ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k ℓ) ∧
      CountDesignSaturated E := by
  obtain ⟨hs, hfailure⟩ := selectedCount_log_budget d n β hn
  obtain ⟨E, hE, hbad, hprop, hsat⟩ :=
    selectedCountEvent_of_oracle_witness_design_saturated
      P hP Q hIID (by omega) hβ _ K hs hfailure j₀ hcandidate
        hwidth hbudget hmass
  refine ⟨E, hE, hbad, hprop, ?_⟩
  change ∀ ω ξ, (fun i => ((ξ i).1, (ξ i).2.1)) =
    (fun i => ((ω i).1, (ω i).2.1)) → (ω ∈ E ↔ ξ ∈ E)
  exact hsat

/-- At the oracle scale, expected counts at the effective dimension balance
the inverse-squared smoothness threshold. [For the stated inputs and conditions](hyp:d,n,β,γ,hn,hden), [the asserted conclusion holds](goal). -/
lemma oracleMesh_count_balance (d n : ℕ) (β γ : ℝ)
    (hn : 0 < n) (hden : 0 < 2 * β + effectiveDimension d γ) :
    (n : ℝ) * (oracleMesh d n β γ) ^ (effectiveDimension d γ) =
      (oracleMesh d n β γ) ^ (-2 * β) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he : -(1 : ℝ) / (2 * β + effectiveDimension d γ) *
      (2 * β + effectiveDimension d γ) = -1 := by
    field_simp
  have hpow : (oracleMesh d n β γ) ^
      (2 * β + effectiveDimension d γ) = (n : ℝ)⁻¹ := by
    rw [oracleMesh, ← Real.rpow_mul hn'.le, he]
    exact Real.rpow_neg_one (n : ℝ)
  rw [Real.rpow_add (by unfold oracleMesh; positivity)] at hpow
  have hmeshpos : 0 < oracleMesh d n β γ := by
    unfold oracleMesh
    exact Real.rpow_pos_of_pos hn' _
  have hpos : 0 < (oracleMesh d n β γ) ^ (2 * β) := by
    exact Real.rpow_pos_of_pos hmeshpos _
  have hneg : -2 * β = -(2 * β) := by ring
  rw [hneg]
  rw [Real.rpow_neg hmeshpos.le]
  rw [inv_eq_one_div]
  apply (eq_div_iff hpos.ne').2
  calc
    ((n : ℝ) * (oracleMesh d n β γ) ^ (effectiveDimension d γ)) *
        (oracleMesh d n β γ) ^ (2 * β) =
      (n : ℝ) * ((oracleMesh d n β γ) ^ (2 * β) *
        (oracleMesh d n β γ) ^ (effectiveDimension d γ)) := by ring
    _ = 1 := by rw [hpow]; exact mul_inv_cancel₀ hn'.ne'

/-- Oracle-scale lower mass and a dyadic width comparison imply the
feasibility count threshold. [For the stated inputs and conditions](hyp:d,n,β,γ,κ,A,h,hn,hden,hκ,hA,hh,hmesh,hcoeff), [the asserted conclusion holds](goal). -/
lemma oracleScale_mass_feasibility (d n : ℕ) (β γ κ A h : ℝ)
    (hn : 0 < n)
    (hden : 0 < 2 * β + effectiveDimension d γ)
    (hκ : 0 < κ) (hA : 0 < A) (hh : 0 < h)
    (hmesh : A * oracleMesh d n β γ ≤ h)
    (hcoeff : 4 ≤ κ * A ^ (2 * β + effectiveDimension d γ)) :
    4 * h ^ (-2 * β) ≤ (n : ℝ) * κ * h ^ (effectiveDimension d γ) := by
  let o := oracleMesh d n β γ
  let e := 2 * β + effectiveDimension d γ
  have ho : 0 < o := by dsimp [o, oracleMesh]; positivity
  have he : 0 ≤ e := le_of_lt hden
  have hbalance : (n : ℝ) * o ^ e = 1 := by
    have hb := oracleMesh_count_balance d n β γ hn hden
    dsimp [o, e]
    change 0 < oracleMesh d n β γ at ho
    rw [Real.rpow_add ho]
    calc
      (n : ℝ) * (oracleMesh d n β γ ^ (2 * β) *
          oracleMesh d n β γ ^ effectiveDimension d γ) =
          ((n : ℝ) * oracleMesh d n β γ ^ effectiveDimension d γ) *
            oracleMesh d n β γ ^ (2 * β) := by ring
      _ = oracleMesh d n β γ ^ (-2 * β) *
          oracleMesh d n β γ ^ (2 * β) := by rw [hb]
      _ = 1 := by rw [← Real.rpow_add ho]; simp
  have hmass : 4 ≤ (n : ℝ) * κ * h ^ e := by
    calc
      4 ≤ κ * A ^ e := hcoeff
      _ = (n : ℝ) * κ * (A * o) ^ e := by
        rw [Real.mul_rpow hA.le ho.le]
        nlinarith [hbalance]
      _ ≤ (n : ℝ) * κ * h ^ e := by
        gcongr
  have hβpow : 0 < h ^ (2 * β) := Real.rpow_pos_of_pos hh _
  have hmass' : 4 ≤ ((n : ℝ) * κ * h ^ effectiveDimension d γ) *
      h ^ (2 * β) := by
    have heq : e = effectiveDimension d γ + 2 * β := by dsimp [e]; ring
    rw [heq, Real.rpow_add hh] at hmass
    nlinarith [hmass]
  rw [show -2 * β = -(2 * β) by ring, Real.rpow_neg hh.le,
    ← div_eq_mul_inv]
  exact (div_le_iff₀ hβpow).2 (by nlinarith [hmass'])

/-- A candidate whose width is above a fixed multiple of the oracle width
has enough expected treated observations in every template microcell. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,j,A,hn,hden,hA,hmesh,hcoeff), [the asserted conclusion holds](goal). -/
lemma model_oracleCandidate_count_mass
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (j : ℕ) (A : ℝ) (hn : 0 < n)
    (hden : 0 < 2 * β + effectiveDimension d γ)
    (hA : 0 < A)
    (hmesh : A * oracleMesh d n β γ ≤ meshWidth j)
    (hcoeff : 4 ≤
      (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        (c_f * templateEta d (polynomialDegree β) ^ d) ^ (γ / (γ - 1))) *
        A ^ (2 * β + effectiveDimension d γ)) :
    ∀ (k : Fin d → Fin (2 ^ j))
      (ℓ : Fin d → Fin (polynomialDegree β + 1)),
      4 * meshWidth j ^ (-2 * β) ≤
        (n : ℝ) * microcellMass P (polynomialDegree β) j k ℓ := by
  intro k ℓ
  let κ : ℝ := ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
    (c_f * templateEta d (polynomialDegree β) ^ d) ^ (γ / (γ - 1))
  have hκ : 0 < κ := by
    dsimp [κ]
    have hγ := hP.2.1
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one hP.1.2.2.2.2.1
    have hcf : 0 < c_f := hP.1.2.2.2.2.2.1
    have hη : 0 < templateEta d (polynomialDegree β) := templateEta_pos _ _
    positivity
  have hh : 0 < meshWidth j := by unfold meshWidth; positivity
  have hmass := oracleScale_mass_feasibility d n β γ κ A (meshWidth j)
    hn hden hκ hA hh hmesh (by simpa only [κ] using hcoeff)
  have hlower := model_microcellMass_effectiveDimension_lower P hP
    (polynomialDegree β) j k ℓ
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  exact hmass.trans (by
    simpa only [κ, mul_assoc] using mul_le_mul_of_nonneg_left hlower hn')

/-- A positive lower bound for the model's mass coefficient is enough for
the oracle-candidate count lower bound. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,j,A,κ,hn,hden,hA,hκ,hκle,hmesh,hcoeff), [the asserted conclusion holds](goal). -/
lemma model_oracleCandidate_count_mass_of_coefficient_lower
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (j : ℕ) (A κ : ℝ) (hn : 0 < n)
    (hden : 0 < 2 * β + effectiveDimension d γ)
    (hA : 0 < A) (hκ : 0 < κ)
    (hκle : κ ≤
      ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        (c_f * templateEta d (polynomialDegree β) ^ d) ^ (γ / (γ - 1)))
    (hmesh : A * oracleMesh d n β γ ≤ meshWidth j)
    (hcoeff : 4 ≤ κ * A ^ (2 * β + effectiveDimension d γ)) :
    ∀ (k : Fin d → Fin (2 ^ j))
      (ℓ : Fin d → Fin (polynomialDegree β + 1)),
      4 * meshWidth j ^ (-2 * β) ≤
        (n : ℝ) * microcellMass P (polynomialDegree β) j k ℓ := by
  have hcoeff' : 4 ≤
      (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        (c_f * templateEta d (polynomialDegree β) ^ d) ^ (γ / (γ - 1))) *
        A ^ (2 * β + effectiveDimension d γ) := by
    exact hcoeff.trans (mul_le_mul_of_nonneg_right hκle (by positivity))
  exact model_oracleCandidate_count_mass P hP j A hn hden hA hmesh hcoeff'

/-- The model mass inequality discharges the oracle witness mass premise in
the finite-family count event. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,Q,hIID,hn,hβ,hden,A,K,hA,j₀,hcandidate,hmesh,hwidth,hbudget,hcoeff), [the asserted conclusion holds](goal). -/
lemma selectedCountEvent_of_oracle_candidate
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (Q : Measure (Fin n → Obs d)) (hIID : IIDSampleLaw Q P)
    (hn : 2 ≤ n) (hβ : 0 ≤ β) (hden : 0 < 2 * β + effectiveDimension d γ)
    (A K : ℝ) (hA : 0 < A)
    (j₀ : ℕ) (hcandidate : j₀ ∈ meshIndices d n β)
    (hmesh : A * oracleMesh d n β γ ≤ meshWidth j₀)
    (hwidth : meshWidth j₀ ≤ K * oracleMesh d n β γ)
    (hbudget : 24 * Real.log (2 *
      ((Fintype.card
        (Σ j : {j // j ∈ meshIndices d n β},
          (Fin d → Fin (2 ^ j.val)) ×
            (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
        (n : ℝ) ^ 2) ≤ meshWidth j₀ ^ (-2 * β))
    (hcoeff : 4 ≤
      (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        (c_f * templateEta d (polynomialDegree β) ^ d) ^ (γ / (γ - 1))) *
        A ^ (2 * β + effectiveDimension d γ)) :
    ∃ E : Set (Fin n → Obs d),
      MeasurableSet E ∧ Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
      ∀ ω ∈ E,
        0 < countSelectedMesh (polynomialDegree β) β ω ∧
        countSelectedMesh (polynomialDegree β) β ω ≤ K * oracleMesh d n β γ ∧
        ∀ (k : Fin d → Fin (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)))
          (ℓ : Fin d → Fin (polynomialDegree β + 1)),
          (n : ℝ) * microcellMass P (polynomialDegree β)
            ((feasibleIndices (polynomialDegree β) β ω).sup id) k ℓ / 5 ≤
            treatedCount (polynomialDegree β)
              ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k ℓ := by
  exact selectedCountEvent_of_log_oracle_witness P hP Q hIID hn hβ K j₀
    hcandidate hwidth hbudget
    (model_oracleCandidate_count_mass P hP j₀ A (by omega)
      hden hA hmesh hcoeff)

/-- The common conclusion of the design-saturated selected-count wrappers. For [the stated inputs and conditions](hyp:β,K,γ,P,Q,E), [the `SaturatedSelectedCountEvent` object being defined](goal). -/
@[expose] def SaturatedSelectedCountEvent {d n : ℕ} (β K γ : ℝ)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d))
    (E : Set (Fin n → Obs d)) : Prop :=
  MeasurableSet E ∧ Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
  (∀ ω ∈ E,
    0 < countSelectedMesh (polynomialDegree β) β ω ∧
    countSelectedMesh (polynomialDegree β) β ω ≤ K * oracleMesh d n β γ ∧
    ∀ (k : Fin d → Fin
        (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)))
      (ℓ : Fin d → Fin (polynomialDegree β + 1)),
      (n : ℝ) * microcellMass P (polynomialDegree β)
        ((feasibleIndices (polynomialDegree β) β ω).sup id) k ℓ / 5 ≤
        treatedCount (polynomialDegree β)
          ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k ℓ) ∧
  CountDesignSaturated E

/-- Oracle-candidate specialization retaining the saturated event. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,Q,hIID,hn,hβ,hden,A,K,hA,j₀,hcandidate,hmesh,hwidth,hbudget,hcoeff), [the asserted conclusion holds](goal). -/
lemma selectedCountEvent_of_oracle_candidate_design_saturated
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (Q : Measure (Fin n → Obs d)) (hIID : IIDSampleLaw Q P)
    (hn : 2 ≤ n) (hβ : 0 ≤ β) (hden : 0 < 2 * β + effectiveDimension d γ)
    (A K : ℝ) (hA : 0 < A)
    (j₀ : ℕ) (hcandidate : j₀ ∈ meshIndices d n β)
    (hmesh : A * oracleMesh d n β γ ≤ meshWidth j₀)
    (hwidth : meshWidth j₀ ≤ K * oracleMesh d n β γ)
    (hbudget : 24 * Real.log (2 *
      ((Fintype.card
        (Σ j : {j // j ∈ meshIndices d n β},
          (Fin d → Fin (2 ^ j.val)) ×
            (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
        (n : ℝ) ^ 2) ≤ meshWidth j₀ ^ (-2 * β))
    (hcoeff : 4 ≤
      (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        (c_f * templateEta d (polynomialDegree β) ^ d) ^ (γ / (γ - 1))) *
        A ^ (2 * β + effectiveDimension d γ)) :
    ∃ E, SaturatedSelectedCountEvent β K γ P Q E := by
  obtain ⟨E, hE, hbad, hprop, hsat⟩ :=
    selectedCountEvent_of_log_oracle_witness_design_saturated
      P hP Q hIID hn hβ K j₀ hcandidate hwidth hbudget
        (model_oracleCandidate_count_mass P hP j₀ A (by omega)
          hden hA hmesh hcoeff)
  exact ⟨E, hE, hbad, hprop, hsat⟩

/-- The oracle-candidate event accepts any positive uniform lower bound for
the model's overlap-mass coefficient. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,Q,hIID,hn,hβ,hden,A,K,κ,hA,hκ,hκle,j₀,hcandidate,hmesh,hwidth,hbudget,hcoeff), [the asserted conclusion holds](goal). -/
lemma selectedCountEvent_of_oracle_candidate_coefficient_lower
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (Q : Measure (Fin n → Obs d)) (hIID : IIDSampleLaw Q P)
    (hn : 2 ≤ n) (hβ : 0 ≤ β) (hden : 0 < 2 * β + effectiveDimension d γ)
    (A K κ : ℝ) (hA : 0 < A) (hκ : 0 < κ)
    (hκle : κ ≤
      ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        (c_f * templateEta d (polynomialDegree β) ^ d) ^ (γ / (γ - 1)))
    (j₀ : ℕ) (hcandidate : j₀ ∈ meshIndices d n β)
    (hmesh : A * oracleMesh d n β γ ≤ meshWidth j₀)
    (hwidth : meshWidth j₀ ≤ K * oracleMesh d n β γ)
    (hbudget : 24 * Real.log (2 *
      ((Fintype.card
        (Σ j : {j // j ∈ meshIndices d n β},
          (Fin d → Fin (2 ^ j.val)) ×
            (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
        (n : ℝ) ^ 2) ≤ meshWidth j₀ ^ (-2 * β))
    (hcoeff : 4 ≤ κ * A ^ (2 * β + effectiveDimension d γ)) :
    ∃ E : Set (Fin n → Obs d),
      MeasurableSet E ∧ Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
      ∀ ω ∈ E,
        0 < countSelectedMesh (polynomialDegree β) β ω ∧
        countSelectedMesh (polynomialDegree β) β ω ≤ K * oracleMesh d n β γ ∧
        ∀ (k : Fin d → Fin (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)))
          (ℓ : Fin d → Fin (polynomialDegree β + 1)),
          (n : ℝ) * microcellMass P (polynomialDegree β)
            ((feasibleIndices (polynomialDegree β) β ω).sup id) k ℓ / 5 ≤
            treatedCount (polynomialDegree β)
              ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k ℓ := by
  exact selectedCountEvent_of_log_oracle_witness P hP Q hIID hn hβ K j₀
    hcandidate hwidth hbudget
    (model_oracleCandidate_count_mass_of_coefficient_lower P hP j₀ A κ
      (by omega) hden hA hκ hκle hmesh hcoeff)

/-- Positive-coefficient oracle specialization retaining saturation. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,P,hP,Q,hIID,hn,hβ,hden,A,K,κ,hA,hκ,hκle,j₀,hcandidate,hmesh,hwidth,hbudget,hcoeff), [the asserted conclusion holds](goal). -/
lemma selectedCountEvent_of_oracle_candidate_coefficient_lower_design_saturated
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (Q : Measure (Fin n → Obs d)) (hIID : IIDSampleLaw Q P)
    (hn : 2 ≤ n) (hβ : 0 ≤ β) (hden : 0 < 2 * β + effectiveDimension d γ)
    (A K κ : ℝ) (hA : 0 < A) (hκ : 0 < κ)
    (hκle : κ ≤ ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d (polynomialDegree β) ^ d) ^ (γ / (γ - 1)))
    (j₀ : ℕ) (hcandidate : j₀ ∈ meshIndices d n β)
    (hmesh : A * oracleMesh d n β γ ≤ meshWidth j₀)
    (hwidth : meshWidth j₀ ≤ K * oracleMesh d n β γ)
    (hbudget : 24 * Real.log (2 *
      ((Fintype.card
        (Σ j : {j // j ∈ meshIndices d n β},
          (Fin d → Fin (2 ^ j.val)) ×
            (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
        (n : ℝ) ^ 2) ≤ meshWidth j₀ ^ (-2 * β))
    (hcoeff : 4 ≤ κ * A ^ (2 * β + effectiveDimension d γ)) :
    ∃ E, SaturatedSelectedCountEvent β K γ P Q E := by
  obtain ⟨E, hE, hbad, hprop, hsat⟩ :=
    selectedCountEvent_of_log_oracle_witness_design_saturated
      P hP Q hIID hn hβ K j₀ hcandidate hwidth hbudget
        (model_oracleCandidate_count_mass_of_coefficient_lower P hP j₀ A κ
          (by omega) hden hA hκ hκle hmesh hcoeff)
  exact ⟨E, hE, hbad, hprop, hsat⟩

/-- Feasibility and the selected count event give both variance scales for a
single treated microcell. [For the stated inputs and conditions](hyp:N,n,q,h,β,hn,hq,hh,hfeasible,hselected), [the asserted conclusion holds](goal). -/
lemma selectedCount_inverse_two_bounds (N : ℕ) (n : ℕ) (q h β : ℝ)
    (hn : 0 < n) (hq : 0 < q) (hh : 0 < h)
    (hfeasible : h ^ (-2 * β) ≤ (N : ℝ))
    (hselected : (n : ℝ) * q / 5 ≤ (N : ℝ)) :
    (N : ℝ)⁻¹ ≤ min (h ^ (2 * β)) (5 / ((n : ℝ) * q)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcount : 0 < (N : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hh _) hfeasible
  have hpop : 0 < (n : ℝ) * q / 5 := by positivity
  apply le_min
  · have h := one_div_le_one_div_of_le
        (Real.rpow_pos_of_pos hh _) hfeasible
    rw [one_div, one_div, ← Real.rpow_neg hh.le] at h
    convert h using 1 <;> ring
  · have h := one_div_le_one_div_of_le hpop hselected
    rw [one_div, one_div] at h
    convert h using 1
    field_simp

/-- The selected-count event controls the sum of inverse counts in a cube.
This is the design-dependent factor in every coefficient variance proxy. [For the stated inputs and conditions](hyp:d,n,m,j,β,P,ω,k,hn,hfeasible,hselected,hq), [the asserted conclusion holds](goal). -/
lemma selectedCount_cube_inverse_sum_bounds {d n : ℕ} (m j : ℕ) (β : ℝ)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hn : 0 < n) (hfeasible : meshFeasible m β ω j)
    (hselected : ∀ ℓ : Fin d → Fin (m + 1),
      (n : ℝ) * microcellMass P m j k ℓ / 5 ≤
        treatedCount m j ω k ℓ)
    (hq : 0 < cubeMass P m j k) :
    (∑ ℓ : Fin d → Fin (m + 1),
        (treatedCount m j ω k ℓ : ℝ)⁻¹) ≤
      (tensorCount d m : ℝ) *
        min (meshWidth j ^ (2 * β))
          (5 / ((n : ℝ) * cubeMass P m j k)) := by
  classical
  have hh : 0 < meshWidth j := by unfold meshWidth; positivity
  calc
    (∑ ℓ : Fin d → Fin (m + 1),
        (treatedCount m j ω k ℓ : ℝ)⁻¹) ≤
      ∑ _ℓ : Fin d → Fin (m + 1),
        min (meshWidth j ^ (2 * β))
          (5 / ((n : ℝ) * cubeMass P m j k)) := by
      apply Finset.sum_le_sum
      intro ℓ _
      have hqℓ : 0 < microcellMass P m j k ℓ :=
        lt_of_lt_of_le hq (orderedMass_cubeMass_le_microcellMass P m j k ℓ)
      have hb := selectedCount_inverse_two_bounds
        (treatedCount m j ω k ℓ) n (microcellMass P m j k ℓ)
        (meshWidth j) β hn hqℓ hh (hfeasible.2 k ℓ) (hselected ℓ)
      apply hb.trans
      apply min_le_min_left
      gcongr
      exact orderedMass_cubeMass_le_microcellMass P m j k ℓ
    _ = (tensorCount d m : ℝ) *
        min (meshWidth j ^ (2 * β))
          (5 / ((n : ℝ) * cubeMass P m j k)) := by
      simp [tensorCount]

/-- Insert an ordered-mass lower bound into the inverse-count variance factor. [For the stated inputs and conditions](hyp:d,n,m,j,β,D,α,κ,r,P,ω,k,hn,hκ,hr,hfeasible,hselected,hmass), [the asserted conclusion holds](goal). -/
lemma selectedCount_cube_inverse_rank_bounds {d n : ℕ} (m j : ℕ)
    (β D α κ : ℝ) (r : ℕ)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hn : 0 < n) (hκ : 0 < κ) (hr : 0 < r)
    (hfeasible : meshFeasible m β ω j)
    (hselected : ∀ ℓ : Fin d → Fin (m + 1),
      (n : ℝ) * microcellMass P m j k ℓ / 5 ≤
        treatedCount m j ω k ℓ)
    (hmass : κ * meshWidth j ^ D * (r : ℝ) ^ α ≤ cubeMass P m j k) :
    (∑ ℓ : Fin d → Fin (m + 1),
        (treatedCount m j ω k ℓ : ℝ)⁻¹) ≤
      (tensorCount d m : ℝ) *
        min (meshWidth j ^ (2 * β))
          (5 / ((n : ℝ) * κ * meshWidth j ^ D * (r : ℝ) ^ α)) := by
  have hh : 0 < meshWidth j := by unfold meshWidth; positivity
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hq : 0 < cubeMass P m j k :=
    lt_of_lt_of_le (by positivity : 0 < κ * meshWidth j ^ D * (r : ℝ) ^ α) hmass
  have hbase := selectedCount_cube_inverse_sum_bounds m j β P ω k hn
    hfeasible hselected hq
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply min_le_min_left
  have hden : 0 < (n : ℝ) * κ * meshWidth j ^ D * (r : ℝ) ^ α := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hqden : 0 < (n : ℝ) * cubeMass P m j k := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  apply div_le_div_of_nonneg_left (by norm_num) hden
  nlinarith [mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ n from Nat.cast_nonneg _)]

/-! A dyadic width rounds an arbitrary target lying in the candidate range. -/
/-- [For the stated inputs and conditions](hyp:J,x,hx,hx1,hJ), [the asserted conclusion holds](goal). -/
lemma meshWidth_dyadic_rounding (J : ℕ) (x : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hJ : meshWidth J ≤ x) :
    ∃ j ≤ J, x ≤ meshWidth j ∧ meshWidth j ≤ 2 * x := by
  induction J with
  | zero =>
      refine ⟨0, le_refl _, ?_, ?_⟩
      · simpa [meshWidth] using hx1
      · simpa [meshWidth] using (show (1 : ℝ) ≤ 2 * x by
          have h : (1 : ℝ) ≤ x := by simpa [meshWidth] using hJ
          linarith)
  | succ J ih =>
      by_cases h : meshWidth J ≤ x
      · obtain ⟨j, hj, hjx, hj2⟩ := ih h
        exact ⟨j, hj.trans (Nat.le_succ J), hjx, hj2⟩
      · have hstep : meshWidth J = 2 * meshWidth (J + 1) := by
          unfold meshWidth
          rw [Nat.cast_add, Nat.cast_one]
          have he : -(↑J + (1 : ℝ)) = -(↑J : ℝ) + (-1) := by ring
          rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          norm_num
          ring
        refine ⟨J, Nat.le_succ J, le_of_not_ge h, ?_⟩
        rw [hstep]
        exact mul_le_mul_of_nonneg_left hJ (by norm_num)

/-! Apply dyadic rounding inside the sample's finite candidate range. -/
/-- [For the stated inputs and conditions](hyp:d,n,β,hn,hden), [the asserted conclusion holds](goal). -/
lemma maxMeshIndex_width_le (d n : ℕ) (β : ℝ)
    (hn : 0 < n) (hden : 0 < 2 * β + d) :
    meshWidth (maxMeshIndex d n β) ≤
      2 * (n : ℝ) ^ (-(1 : ℝ) / (2 * β + d)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let x : ℝ := Real.log n / Real.log 2 / (2 * β + d)
  have hfloor : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  have hexp : -(Nat.floor x : ℝ) ≤ 1 - x := by linarith
  have hmono : (2 : ℝ) ^ (-(Nat.floor x : ℝ)) ≤ (2 : ℝ) ^ (1 - x) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hpow : (2 : ℝ) ^ (1 - x) =
      2 * (n : ℝ) ^ (-(1 : ℝ) / (2 * β + d)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hn']
    rw [show Real.log (2 : ℝ) * (1 - x) =
        Real.log 2 + Real.log (n : ℝ) * (-(1 : ℝ) / (2 * β + d)) by
          dsimp [x]
          field_simp
          ring]
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simpa only [maxMeshIndex, meshWidth, x] using hmono.trans_eq hpow

/-- [For the stated inputs and conditions](hyp:d,n,β,hn,hden), [the asserted conclusion holds](goal). -/

lemma maxMeshIndex_width_ge (d n : ℕ) (β : ℝ)
    (hn : 0 < n) (hden : 0 < 2 * β + d) :
    (n : ℝ) ^ (-(1 : ℝ) / (2 * β + d)) ≤
      meshWidth (maxMeshIndex d n β) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let x : ℝ := Real.log n / Real.log 2 / (2 * β + d)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hfloor : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx
  have hmono : (2 : ℝ) ^ (-x) ≤ (2 : ℝ) ^ (-(Nat.floor x : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hpow : (2 : ℝ) ^ (-x) =
      (n : ℝ) ^ (-(1 : ℝ) / (2 * β + d)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hn']
    congr 1
    dsimp [x]
    field_simp
  simpa only [maxMeshIndex, meshWidth, x] using hpow.symm.le.trans hmono

/-- The finest dyadic candidate width eventually lies below any fixed multiple of
the oracle width when the effective dimension is strictly larger. [For the stated inputs and conditions](hyp:d,β,γ,A,hden,hdim,hA), [the asserted conclusion holds](goal). -/
lemma maxMeshIndex_width_le_oracle_eventually (d : ℕ) (β γ A : ℝ)
    (hden : 0 < 2 * β + d)
    (hdim : (d : ℝ) < effectiveDimension d γ) (hA : 0 < A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      meshWidth (maxMeshIndex d n β) ≤ A * oracleMesh d n β γ := by
  have hden' : 0 < 2 * β + effectiveDimension d γ := by linarith
  have hgap : (1 : ℝ) / (2 * β + effectiveDimension d γ) <
      1 / (2 * β + d) := by
    apply (div_lt_div_iff₀ hden' hden).2
    nlinarith
  obtain ⟨n₀, hn₀⟩ := selectedCount_power_gap
    (1 / (2 * β + effectiveDimension d γ))
    (1 / (2 * β + d)) A hgap hA
  refine ⟨max n₀ 1, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  calc
    meshWidth (maxMeshIndex d n β) ≤
        2 * (n : ℝ) ^ (-(1 : ℝ) / (2 * β + d)) :=
      maxMeshIndex_width_le d n β hnpos hden
    _ ≤ A * oracleMesh d n β γ := by
      simpa only [oracleMesh, neg_div] using
        hn₀ n (le_trans (Nat.le_max_left _ _) hn)

/-- [For the stated inputs and conditions](hyp:d,n,β,A,γ,hA,ho,hlarge,hsmall), [the asserted conclusion holds](goal). -/

lemma meshIndices_oracleCandidate_of_bounds (d n : ℕ) (β A γ : ℝ)
    (hA : 0 < A) (ho : 0 < oracleMesh d n β γ)
    (hlarge : A * oracleMesh d n β γ ≤ 1)
    (hsmall : meshWidth (maxMeshIndex d n β) ≤ A * oracleMesh d n β γ) :
    ∃ j ∈ meshIndices d n β,
      A * oracleMesh d n β γ ≤ meshWidth j ∧
      meshWidth j ≤ (2 * A) * oracleMesh d n β γ := by
  obtain ⟨j, hj, hjlo, hjhi⟩ :=
    meshWidth_dyadic_rounding (maxMeshIndex d n β)
      (A * oracleMesh d n β γ) (mul_pos hA ho) hlarge hsmall
  refine ⟨j, ?_, hjlo, ?_⟩
  · simpa [meshIndices] using Nat.lt_succ_of_le hj
  · convert hjhi using 1 <;> ring

/-- Effective dimension decreases as the overlap-tail exponent increases. [For the stated inputs and conditions](hyp:d,a,b,ha,hab), [the asserted conclusion holds](goal). -/
lemma effectiveDimension_antitone (d : ℕ) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) :
    effectiveDimension d b ≤ effectiveDimension d a := by
  have hb : 0 < b - 1 := by linarith
  have ha' : 0 < a - 1 := by linarith
  have hinv : (b - 1)⁻¹ ≤ (a - 1)⁻¹ := by
    have hsub : a - 1 ≤ b - 1 := sub_le_sub_right hab 1
    simpa only [one_div] using one_div_le_one_div_of_le ha' hsub
  have haid : a / (a - 1) = 1 + (a - 1)⁻¹ := by
    field_simp
    ring
  have hbid : b / (b - 1) = 1 + (b - 1)⁻¹ := by
    field_simp
    ring
  unfold effectiveDimension
  rw [mul_div_assoc, mul_div_assoc]
  rw [haid, hbid]
  gcongr

/-- Over a compact overlap range, every oracle width lies between the two
endpoint oracle widths. [For the stated inputs and conditions](hyp:d,n,β,γ_min,γ,γ_max,hn,hβ,hγmin,hγ), [the asserted conclusion holds](goal). -/
lemma oracleMesh_between_adaptation_endpoints (d n : ℕ) (β γ_min γ γ_max : ℝ)
    (hn : 1 ≤ n) (hβ : 0 < β) (hγmin : 1 < γ_min)
    (hγ : γ ∈ Set.Icc γ_min γ_max) :
    oracleMesh d n β γ_max ≤ oracleMesh d n β γ ∧
      oracleMesh d n β γ ≤ oracleMesh d n β γ_min := by
  have hγpos : 1 < γ := lt_of_lt_of_le hγmin hγ.1
  have hγmax : 1 < γ_max := lt_of_lt_of_le hγpos hγ.2
  have hDlo := effectiveDimension_antitone d hγpos hγ.2
  have hDhi := effectiveDimension_antitone d hγmin hγ.1
  have hdnonneg : 0 ≤ effectiveDimension d γ_max := by
    unfold effectiveDimension
    positivity
  have hdenMax : 0 < 2 * β + effectiveDimension d γ_max := by positivity
  have hden : 0 < 2 * β + effectiveDimension d γ := by linarith
  have hdenMin : 0 < 2 * β + effectiveDimension d γ_min := by linarith
  have hexpLo : -(1 : ℝ) / (2 * β + effectiveDimension d γ_max) ≤
      -(1 : ℝ) / (2 * β + effectiveDimension d γ) := by
    have hdenle : 2 * β + effectiveDimension d γ_max ≤
        2 * β + effectiveDimension d γ := by linarith
    have hrec := one_div_le_one_div_of_le hdenMax hdenle
    simpa only [neg_div, one_div] using neg_le_neg hrec
  have hexpHi : -(1 : ℝ) / (2 * β + effectiveDimension d γ) ≤
      -(1 : ℝ) / (2 * β + effectiveDimension d γ_min) := by
    have hdenle : 2 * β + effectiveDimension d γ ≤
        2 * β + effectiveDimension d γ_min := by linarith
    have hrec := one_div_le_one_div_of_le hden hdenle
    simpa only [neg_div, one_div] using neg_le_neg hrec
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor <;>
    unfold oracleMesh <;>
    exact Real.rpow_le_rpow_of_exponent_le hn' (by assumption)

/-- One selected-count constant and one sample-size threshold work uniformly
over the compact overlap-exponent range. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hd,hβ,hB,hL,hC,hcf,hγmin,hγrange), [the asserted conclusion holds](goal). -/
lemma selectedCountEvent_uniform
    (d : ℕ) (β B L C c_f γ_min γ_max : ℝ)
    (hd : 1 ≤ d) (hβ : 1 < β) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
      ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P],
        P ∈ ModelClass d β B L C c_f γ →
      ∀ (Q : Measure (Fin n → Obs d)), IIDSampleLaw Q P →
      ∃ E : Set (Fin n → Obs d),
        MeasurableSet E ∧ Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
        ∀ ω ∈ E,
          0 < countSelectedMesh (polynomialDegree β) β ω ∧
          countSelectedMesh (polynomialDegree β) β ω ≤
            K * oracleMesh d n β γ ∧
          ∀ (k : Fin d →
              Fin (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)))
            (ℓ : Fin d → Fin (polynomialDegree β + 1)),
            (n : ℝ) * microcellMass P (polynomialDegree β)
              ((feasibleIndices (polynomialDegree β) β ω).sup id) k ℓ / 5 ≤
              treatedCount (polynomialDegree β)
                ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k ℓ := by
  let m := polynomialDegree β
  let a := c_f * templateEta d m ^ d
  have ha : 0 < a := by
    dsimp [a, m]
    exact mul_pos hcf.1 (pow_pos (templateEta_pos d (polynomialDegree β)) d)
  obtain ⟨κ, hκ, hκle⟩ := orderedMass_uniform_coefficient C a γ_min γ_max
    (lt_of_lt_of_le zero_lt_one hC) ha hγmin hγrange
  have hden₀ : 0 < 2 * β + (d : ℝ) := by positivity
  have hden₁ : 1 ≤ 2 * β + (d : ℝ) := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hγmax : 1 < γ_max := hγmin.trans hγrange
  have hdenMin : 0 < 2 * β + effectiveDimension d γ_max := by
    unfold effectiveDimension
    positivity
  have hdenMax : 0 < 2 * β + effectiveDimension d γ_min := by
    unfold effectiveDimension
    positivity
  obtain ⟨A, hA₁, hcoeffMin⟩ := selectedCount_oracle_enlargement κ
    (2 * β + effectiveDimension d γ_max) hκ hdenMin
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one hA₁
  have hdimMax : (d : ℝ) < effectiveDimension d γ_max := by
    unfold effectiveDimension
    apply (lt_div_iff₀ (by linarith : 0 < γ_max - 1)).2
    have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    nlinarith
  obtain ⟨nsmall, hnsmall⟩ :=
    maxMeshIndex_width_le_oracle_eventually d β γ_max A hden₀ hdimMax hA
  obtain ⟨nlarge, hnlarge⟩ :=
    selectedCount_power_eventually_le_one
      (1 / (2 * β + effectiveDimension d γ_min)) A (by positivity) hA
  let U : ℝ := 24 * ((d : ℝ) + 3)
  let V : ℝ := 24 * Real.log
    (8 * ((polynomialDegree β + 1 : ℝ) ^ d + 1))
  obtain ⟨nbudget, hnbudget⟩ :=
    selectedCount_oracle_inverse_log_budget (2 * A) β
      (2 * β + effectiveDimension d γ_min) U V (by positivity)
      (by linarith) hdenMax (by dsimp [U]; positivity)
  refine ⟨2 * A, by positivity,
    max 2 (max nsmall (max nlarge nbudget)), ?_⟩
  intro n hn γ hγ P _ hP Q hIID
  have hn₂ : 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hns : nsmall ≤ n :=
    (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)).trans hn
  have hnl : nlarge ≤ n :=
    (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)).trans
      ((Nat.le_max_right _ _).trans hn)
  have hnb : nbudget ≤ n :=
    (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)).trans
      ((Nat.le_max_right _ _).trans hn)
  have hγIcc : γ ∈ Set.Icc γ_min γ_max := by
    simpa only [adaptationRange] using hγ
  have hγpos : 1 < γ := hγmin.trans_le hγIcc.1
  have hden : 0 < 2 * β + effectiveDimension d γ := by
    unfold effectiveDimension
    positivity
  have horacle := oracleMesh_between_adaptation_endpoints
    d n β γ_min γ γ_max (by omega) (by linarith) hγmin hγIcc
  have ho : 0 < oracleMesh d n β γ := by
    unfold oracleMesh
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hlargeMin : A * oracleMesh d n β γ_min ≤ 1 := by
    simpa only [oracleMesh, neg_div] using hnlarge n hnl
  have hlarge : A * oracleMesh d n β γ ≤ 1 :=
    (mul_le_mul_of_nonneg_left horacle.2 hA.le).trans hlargeMin
  have hsmallMax := hnsmall n hns
  have hsmall : meshWidth (maxMeshIndex d n β) ≤
      A * oracleMesh d n β γ :=
    hsmallMax.trans (mul_le_mul_of_nonneg_left horacle.1 hA.le)
  obtain ⟨j₀, hj₀, hjlo, hjhi⟩ :=
    meshIndices_oracleCandidate_of_bounds d n β A γ hA ho hlarge hsmall
  have hbudget : 24 * Real.log (2 *
      ((Fintype.card
        (Σ j : {j // j ∈ meshIndices d n β},
          (Fin d → Fin (2 ^ j.val)) ×
            (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
        (n : ℝ) ^ 2) ≤ meshWidth j₀ ^ (-2 * β) := by
    have hlog := selectedCount_log_card_bound d n
      (polynomialDegree β) β hn₂ hden₁
    have hh : 0 < meshWidth j₀ := by unfold meshWidth; positivity
    have hscale : (2 * A) * oracleMesh d n β γ ≤
        (2 * A) * oracleMesh d n β γ_min := by
      exact mul_le_mul_of_nonneg_left horacle.2 (by positivity)
    calc
      24 * Real.log (2 *
          ((Fintype.card
            (Σ j : {j // j ∈ meshIndices d n β},
              (Fin d → Fin (2 ^ j.val)) ×
                (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
            (n : ℝ) ^ 2) ≤ U * Real.log n + V := by
        dsimp [U, V]
        nlinarith
      _ ≤ ((2 * A) * oracleMesh d n β γ_min) ^ (-2 * β) := by
        simpa only [oracleMesh, U, V] using hnbudget n hnb
      _ ≤ ((2 * A) * oracleMesh d n β γ) ^ (-2 * β) := by
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hscale (by linarith)
      _ ≤ meshWidth j₀ ^ (-2 * β) :=
        Real.rpow_le_rpow_of_nonpos hh hjhi (by linarith)
  have hD : effectiveDimension d γ_max ≤ effectiveDimension d γ :=
    effectiveDimension_antitone d hγpos hγIcc.2
  have hcoeff : 4 ≤ κ * A ^ (2 * β + effectiveDimension d γ) := by
    exact hcoeffMin.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hA₁ (by linarith)) hκ.le)
  have hκle' : κ ≤
      ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        (c_f * templateEta d (polynomialDegree β) ^ d) ^ (γ / (γ - 1)) := by
    simpa only [a, m] using hκle γ hγIcc
  exact selectedCountEvent_of_oracle_candidate_coefficient_lower
    P hP Q hIID hn₂ (by linarith) hden A (2 * A) κ hA hκ hκle'
      j₀ hj₀ hjlo hjhi hbudget hcoeff


/-- Uniform selected-count control with an explicitly design-saturated event. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hd,hβ,hB,hL,hC,hcf,hγmin,hγrange), [the asserted conclusion holds](goal). -/
lemma selectedCountEvent_uniform_design_saturated
    (d : ℕ) (β B L C c_f γ_min γ_max : ℝ)
    (hd : 1 ≤ d) (hβ : 1 < β) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
      ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P],
        P ∈ ModelClass d β B L C c_f γ →
      ∀ (Q : Measure (Fin n → Obs d)), IIDSampleLaw Q P →
      ∃ E, SaturatedSelectedCountEvent β K γ P Q E := by
  let m := polynomialDegree β
  let a := c_f * templateEta d m ^ d
  have ha : 0 < a := by
    dsimp [a, m]
    exact mul_pos hcf.1 (pow_pos (templateEta_pos d (polynomialDegree β)) d)
  obtain ⟨κ, hκ, hκle⟩ := orderedMass_uniform_coefficient C a γ_min γ_max
    (lt_of_lt_of_le zero_lt_one hC) ha hγmin hγrange
  have hden₀ : 0 < 2 * β + (d : ℝ) := by positivity
  have hden₁ : 1 ≤ 2 * β + (d : ℝ) := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hγmax : 1 < γ_max := hγmin.trans hγrange
  have hdenMin : 0 < 2 * β + effectiveDimension d γ_max := by
    unfold effectiveDimension
    positivity
  have hdenMax : 0 < 2 * β + effectiveDimension d γ_min := by
    unfold effectiveDimension
    positivity
  obtain ⟨A, hA₁, hcoeffMin⟩ := selectedCount_oracle_enlargement κ
    (2 * β + effectiveDimension d γ_max) hκ hdenMin
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one hA₁
  have hdimMax : (d : ℝ) < effectiveDimension d γ_max := by
    unfold effectiveDimension
    apply (lt_div_iff₀ (by linarith : 0 < γ_max - 1)).2
    have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    nlinarith
  obtain ⟨nsmall, hnsmall⟩ :=
    maxMeshIndex_width_le_oracle_eventually d β γ_max A hden₀ hdimMax hA
  obtain ⟨nlarge, hnlarge⟩ :=
    selectedCount_power_eventually_le_one
      (1 / (2 * β + effectiveDimension d γ_min)) A (by positivity) hA
  let U : ℝ := 24 * ((d : ℝ) + 3)
  let V : ℝ := 24 * Real.log
    (8 * ((polynomialDegree β + 1 : ℝ) ^ d + 1))
  obtain ⟨nbudget, hnbudget⟩ :=
    selectedCount_oracle_inverse_log_budget (2 * A) β
      (2 * β + effectiveDimension d γ_min) U V (by positivity)
      (by linarith) hdenMax (by dsimp [U]; positivity)
  refine ⟨2 * A, by positivity,
    max 2 (max nsmall (max nlarge nbudget)), ?_⟩
  intro n hn γ hγ P _ hP Q hIID
  have hn₂ : 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hns : nsmall ≤ n :=
    (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)).trans hn
  have hnl : nlarge ≤ n :=
    (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)).trans
      ((Nat.le_max_right _ _).trans hn)
  have hnb : nbudget ≤ n :=
    (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)).trans
      ((Nat.le_max_right _ _).trans hn)
  have hγIcc : γ ∈ Set.Icc γ_min γ_max := by
    simpa only [adaptationRange] using hγ
  have hγpos : 1 < γ := hγmin.trans_le hγIcc.1
  have hden : 0 < 2 * β + effectiveDimension d γ := by
    unfold effectiveDimension
    positivity
  have horacle := oracleMesh_between_adaptation_endpoints
    d n β γ_min γ γ_max (by omega) (by linarith) hγmin hγIcc
  have ho : 0 < oracleMesh d n β γ := by
    unfold oracleMesh
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hlargeMin : A * oracleMesh d n β γ_min ≤ 1 := by
    simpa only [oracleMesh, neg_div] using hnlarge n hnl
  have hlarge : A * oracleMesh d n β γ ≤ 1 :=
    (mul_le_mul_of_nonneg_left horacle.2 hA.le).trans hlargeMin
  have hsmallMax := hnsmall n hns
  have hsmall : meshWidth (maxMeshIndex d n β) ≤
      A * oracleMesh d n β γ :=
    hsmallMax.trans (mul_le_mul_of_nonneg_left horacle.1 hA.le)
  obtain ⟨j₀, hj₀, hjlo, hjhi⟩ :=
    meshIndices_oracleCandidate_of_bounds d n β A γ hA ho hlarge hsmall
  have hbudget : 24 * Real.log (2 *
      ((Fintype.card
        (Σ j : {j // j ∈ meshIndices d n β},
          (Fin d → Fin (2 ^ j.val)) ×
            (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
        (n : ℝ) ^ 2) ≤ meshWidth j₀ ^ (-2 * β) := by
    have hlog := selectedCount_log_card_bound d n
      (polynomialDegree β) β hn₂ hden₁
    have hh : 0 < meshWidth j₀ := by unfold meshWidth; positivity
    have hscale : (2 * A) * oracleMesh d n β γ ≤
        (2 * A) * oracleMesh d n β γ_min := by
      exact mul_le_mul_of_nonneg_left horacle.2 (by positivity)
    calc
      24 * Real.log (2 *
          ((Fintype.card
            (Σ j : {j // j ∈ meshIndices d n β},
              (Fin d → Fin (2 ^ j.val)) ×
                (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
            (n : ℝ) ^ 2) ≤ U * Real.log n + V := by
        dsimp [U, V]
        nlinarith
      _ ≤ ((2 * A) * oracleMesh d n β γ_min) ^ (-2 * β) := by
        simpa only [oracleMesh, U, V] using hnbudget n hnb
      _ ≤ ((2 * A) * oracleMesh d n β γ) ^ (-2 * β) := by
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hscale (by linarith)
      _ ≤ meshWidth j₀ ^ (-2 * β) :=
        Real.rpow_le_rpow_of_nonpos hh hjhi (by linarith)
  have hD : effectiveDimension d γ_max ≤ effectiveDimension d γ :=
    effectiveDimension_antitone d hγpos hγIcc.2
  have hcoeff : 4 ≤ κ * A ^ (2 * β + effectiveDimension d γ) := by
    exact hcoeffMin.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hA₁ (by linarith)) hκ.le)
  have hκle' : κ ≤
      ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        (c_f * templateEta d (polynomialDegree β) ^ d) ^ (γ / (γ - 1)) := by
    simpa only [a, m] using hκle γ hγIcc
  exact selectedCountEvent_of_oracle_candidate_coefficient_lower_design_saturated
    P hP Q hIID hn₂ (by linarith) hden A (2 * A) κ hA hκ hκle'
      j₀ hj₀ hjlo hjhi hbudget hcoeff

/-- Fixed-overlap selected-count control with an explicitly design-saturated event. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,P,hP), [the asserted conclusion holds](goal). -/
lemma selectedCountEvent_design_saturated (d : ℕ) (β B L C c_f γ : ℝ)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (Q : Measure (Fin n → Obs d)), IIDSampleLaw Q P →
      ∃ E, SaturatedSelectedCountEvent β K γ P Q E := by
  have hdom := hP.1
  rcases hdom with ⟨hd, hβ, hB, hL, hC, hcf, hcf1⟩
  have hγ : 1 < γ := hP.2.1
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hden : 0 < 2 * β + effectiveDimension d γ := by
    unfold effectiveDimension
    positivity
  have hden₀ : 0 < 2 * β + (d : ℝ) := by positivity
  have hden₁ : 1 ≤ 2 * β + (d : ℝ) := by linarith
  have hdim : (d : ℝ) < effectiveDimension d γ := by
    unfold effectiveDimension
    apply (lt_div_iff₀ (by linarith : 0 < γ - 1)).2
    nlinarith
  let κ : ℝ := ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
    (c_f * templateEta d (polynomialDegree β) ^ d) ^ (γ / (γ - 1))
  have hκ : 0 < κ := by
    dsimp [κ]
    have hη := templateEta_pos d (polynomialDegree β)
    positivity
  obtain ⟨A, hA₁, hcoeff⟩ := selectedCount_oracle_enlargement κ
    (2 * β + effectiveDimension d γ) hκ hden
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one hA₁
  obtain ⟨nsmall, hnsmall⟩ :=
    maxMeshIndex_width_le_oracle_eventually d β γ A hden₀ hdim hA
  obtain ⟨nlarge, hnlarge⟩ :=
    selectedCount_power_eventually_le_one
      (1 / (2 * β + effectiveDimension d γ)) A (by positivity) hA
  let U : ℝ := 24 * ((d : ℝ) + 3)
  let V : ℝ := 24 * Real.log
    (8 * ((polynomialDegree β + 1 : ℝ) ^ d + 1))
  obtain ⟨nbudget, hnbudget⟩ :=
    selectedCount_oracle_inverse_log_budget (2 * A) β
      (2 * β + effectiveDimension d γ) U V (by positivity)
      (by linarith) hden (by dsimp [U]; positivity)
  refine ⟨2 * A, by positivity, max 2 (max nsmall (max nlarge nbudget)), ?_⟩
  intro n hn Q hIID
  have hn₂ : 2 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hns : nsmall ≤ n :=
    (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)).trans hn
  have hnl : nlarge ≤ n :=
    (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)).trans
      ((Nat.le_max_right _ _).trans hn)
  have hnb : nbudget ≤ n :=
    (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)).trans
      ((Nat.le_max_right _ _).trans hn)
  have ho : 0 < oracleMesh d n β γ := by
    unfold oracleMesh
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hlarge : A * oracleMesh d n β γ ≤ 1 := by
    simpa only [oracleMesh, neg_div] using hnlarge n hnl
  have hsmall := hnsmall n hns
  obtain ⟨j₀, hj₀, hjlo, hjhi⟩ :=
    meshIndices_oracleCandidate_of_bounds d n β A γ hA ho hlarge hsmall
  have hbudget : 24 * Real.log (2 *
      ((Fintype.card
        (Σ j : {j // j ∈ meshIndices d n β},
          (Fin d → Fin (2 ^ j.val)) ×
            (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
        (n : ℝ) ^ 2) ≤ meshWidth j₀ ^ (-2 * β) := by
    have hlog := selectedCount_log_card_bound d n
      (polynomialDegree β) β hn₂ hden₁
    have hh : 0 < meshWidth j₀ := by unfold meshWidth; positivity
    calc
      24 * Real.log (2 *
          ((Fintype.card
            (Σ j : {j // j ∈ meshIndices d n β},
              (Fin d → Fin (2 ^ j.val)) ×
                (Fin d → Fin (polynomialDegree β + 1))) : ℝ) + 1) *
            (n : ℝ) ^ 2) ≤ U * Real.log n + V := by
        dsimp [U, V]
        nlinarith
      _ ≤ ((2 * A) * oracleMesh d n β γ) ^ (-2 * β) := by
        simpa only [oracleMesh, U, V] using hnbudget n hnb
      _ ≤ meshWidth j₀ ^ (-2 * β) :=
        Real.rpow_le_rpow_of_nonpos hh hjhi (by linarith)
  exact selectedCountEvent_of_oracle_candidate_design_saturated P hP Q hIID hn₂ (by linarith)
    hden A (2 * A) hA j₀ hj₀ hjlo hjhi hbudget
    (by simpa only [κ] using hcoeff)

end CausalSmith.Stat.WeakOverlap
