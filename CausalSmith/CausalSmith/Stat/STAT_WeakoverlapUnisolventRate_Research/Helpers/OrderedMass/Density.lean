module
public import Causalean.Mathlib.MeasureTheory.RnDerivBounds
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass.Geometry

/-! # Density lower bounds for covariate mass -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory
set_option linter.style.haveILetI false

/-- An almost-everywhere lower density bound controls the mass of every
measurable set. [For the stated inputs and conditions](hyp:α,μ,ν,hAC,c,hden,E), [the asserted conclusion holds](goal). -/
lemma orderedMass_measure_lower_of_rnDeriv_lower {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hAC : μ ≪ ν) (c : ℝ)
    (hden : ∀ᵐ x ∂ν, c ≤ (μ.rnDeriv ν x).toReal)
    (E : Set α) :
    c * ν.real E ≤ μ.real E :=
  Causalean.Mathlib.MeasureTheory.measureReal_lower_of_rnDeriv_lower
    μ ν hAC c hden E

/-- The model's density condition gives a setwise lower covariate mass bound. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,E), [the asserted conclusion holds](goal). -/
lemma orderedMass_covariate_volume_lower {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (E : Set (Fin d → ℝ)) :
    c_f * (volume.restrict (cube d)).real E ≤
      (covariateLaw (Pc.map observed)).real E := by
  let ν := volume.restrict (cube d)
  have hvol : volume (cube d) = 1 := by
    have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  haveI : IsFiniteMeasure ν := by
    rw [isFiniteMeasure_restrict]
    simp [hvol]
  haveI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  haveI : IsProbabilityMeasure (covariateLaw (Pc.map observed)) := by
    unfold covariateLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  exact orderedMass_measure_lower_of_rnDeriv_lower
    (covariateLaw (Pc.map observed)) ν hmodel.covariateAC c_f
    hmodel.density E

/-- Each scaled microcell has covariate mass at least its volume times the
model's density floor. [For the stated inputs and conditions](hyp:d,m,j,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,k,ℓ), [the asserted conclusion holds](goal). -/
lemma orderedMass_microcell_covariate_lower (d m j : ℕ)
    (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)) :
    c_f * (ENNReal.ofReal (templateEta d m * meshWidth j) ^ d).toReal ≤
      (covariateLaw (Pc.map observed)).real (scaledMicroCell d m j k ℓ) := by
  have hinside : scaledMicroCell d m j k ℓ ⊆ cube d := by
    intro x hx
    exact (orderedMass_scaledMicroCell_inside_dyadicCube d m j k ℓ hx).1
  have hmeas : MeasurableSet (scaledMicroCell d m j k ℓ) :=
    orderedMass_scaledMicroCell_measurable d m j k ℓ
  have hrestrict : (volume.restrict (cube d)).real (scaledMicroCell d m j k ℓ) =
      (volume (scaledMicroCell d m j k ℓ)).toReal := by
    rw [measureReal_def, Measure.restrict_apply hmeas, Set.inter_eq_self_of_subset_left hinside]
  rw [← orderedMass_scaledMicroCell_volume d m j k ℓ, ← hrestrict]
  exact orderedMass_covariate_volume_lower β B L C c_f γ Pc μ₁ e hmodel _

/-- Treated mass adds over one selected microcell in each distinct macro-cube. [For the stated inputs and conditions](hyp:d,P,m,j,S,ℓ), [the asserted conclusion holds](goal). -/
lemma orderedMass_selectedMicrocells_treated_additive {d : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P] (m j : ℕ)
    (S : Finset (Fin d → Fin (2 ^ j)))
    (ℓ : (Fin d → Fin (2 ^ j)) → Fin d → Fin (m + 1)) :
    P.real {z | z.2.1 = true ∧
      z.1 ∈ ⋃ k ∈ S, scaledMicroCell d m j k (ℓ k)} =
      ∑ k ∈ S, microcellMass P m j k (ℓ k) := by
  let F : (Fin d → Fin (2 ^ j)) → Set (Obs d) :=
    fun k => {z | z.2.1 = true ∧ z.1 ∈ scaledMicroCell d m j k (ℓ k)}
  have hdisj : (S : Set (Fin d → Fin (2 ^ j))).PairwiseDisjoint F := by
    intro k hk k' hk' hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (Set.disjoint_left.mp
      (orderedMass_scaledMicroCell_disjoint_macro d m j k k' hne (ℓ k) (ℓ k')))
      hz.2 hz'.2
  have hmeas : ∀ k ∈ S, MeasurableSet (F k) := by
    intro k hk
    dsimp [F]
    exact (measurableSet_singleton _).preimage (by fun_prop) |>.inter
      ((orderedMass_scaledMicroCell_measurable d m j k (ℓ k)).preimage (by fun_prop))
  have hsum := measureReal_biUnion_finset (μ := P) hdisj hmeas
  have hset : {z : Obs d | z.2.1 = true ∧
      z.1 ∈ ⋃ k ∈ S, scaledMicroCell d m j k (ℓ k)} = ⋃ k ∈ S, F k := by
    ext z
    simp only [F, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hz, k, hk, hcell⟩
      exact ⟨k, hk, hz, hcell⟩
    · rintro ⟨k, hk, hz, hcell⟩
      exact ⟨hz, k, hk, hcell⟩
  rw [hset]
  simpa only [F, microcellMass] using hsum

/-- The same disjointness gives additivity of covariate mass over selected cells. [For the stated inputs and conditions](hyp:d,P,m,j,S,ℓ), [the asserted conclusion holds](goal). -/
lemma orderedMass_selectedMicrocells_covariate_additive {d : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P] (m j : ℕ)
    (S : Finset (Fin d → Fin (2 ^ j)))
    (ℓ : (Fin d → Fin (2 ^ j)) → Fin d → Fin (m + 1)) :
    (covariateLaw P).real (⋃ k ∈ S, scaledMicroCell d m j k (ℓ k)) =
      ∑ k ∈ S, (covariateLaw P).real (scaledMicroCell d m j k (ℓ k)) := by
  letI : IsProbabilityMeasure (covariateLaw P) := by
    unfold covariateLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  let F : (Fin d → Fin (2 ^ j)) → Set (Fin d → ℝ) :=
    fun k => scaledMicroCell d m j k (ℓ k)
  have hdisj : (S : Set (Fin d → Fin (2 ^ j))).PairwiseDisjoint F := by
    intro k hk k' hk' hne
    exact orderedMass_scaledMicroCell_disjoint_macro d m j k k' hne (ℓ k) (ℓ k')
  have hmeas : ∀ k ∈ S, MeasurableSet (F k) := by
    intro k hk
    exact orderedMass_scaledMicroCell_measurable d m j k (ℓ k)
  simpa only [F] using measureReal_biUnion_finset (μ := covariateLaw P) hdisj hmeas

/-- A set of distinct selected cells carries at least its cardinality times the
single-cell density lower bound. [For the stated inputs and conditions](hyp:d,m,j,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,S,ℓ), [the asserted conclusion holds](goal). -/
lemma orderedMass_selectedMicrocells_covariate_lower (d m j : ℕ)
    (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (S : Finset (Fin d → Fin (2 ^ j)))
    (ℓ : (Fin d → Fin (2 ^ j)) → Fin d → Fin (m + 1)) :
    (S.card : ℝ) * (c_f *
        (ENNReal.ofReal (templateEta d m * meshWidth j) ^ d).toReal) ≤
      (covariateLaw (Pc.map observed)).real
        (⋃ k ∈ S, scaledMicroCell d m j k (ℓ k)) := by
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  rw [orderedMass_selectedMicrocells_covariate_additive]
  calc
    (S.card : ℝ) * (c_f *
        (ENNReal.ofReal (templateEta d m * meshWidth j) ^ d).toReal) =
        ∑ _k ∈ S, c_f *
          (ENNReal.ofReal (templateEta d m * meshWidth j) ^ d).toReal := by simp
    _ ≤ ∑ k ∈ S,
        (covariateLaw (Pc.map observed)).real (scaledMicroCell d m j k (ℓ k)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact orderedMass_microcell_covariate_lower d m j β B L C c_f γ
            Pc μ₁ e hmodel k (ℓ k)

end CausalSmith.Stat.WeakOverlap
