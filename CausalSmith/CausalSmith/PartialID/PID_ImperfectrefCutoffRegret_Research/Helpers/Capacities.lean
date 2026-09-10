import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.DerivedMargins
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Capped allocations, interval filling, and support-dual auxiliaries. -/

open MeasureTheory
open scoped BigOperators

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

def stratumLower (M : ImperfectReferenceModel) (r : Bool) (I : BorelScoreSet) : ℝ :=
  max 0 (diseaseMass M r - obsMass M r + stratumMass M r I)

def stratumUpper (M : ImperfectReferenceModel) (r : Bool) (I : BorelScoreSet) : ℝ :=
  min (diseaseMass M r) (stratumMass M r I)

lemma dominated_stratum_mass_mem_Icc (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) (hν : DominatedAllocation M ν)
    (r : Bool) (I : BorelScoreSet) :
    (ν r).real I ∈ Set.Icc (stratumLower M r I) (stratumUpper M r I) := by
  let _ : IsFiniteMeasure (ν r) :=
    isFiniteMeasure_of_le (obsMeasure M r) (hν.domination r)
  have hdom (A : Set ℝ) : (ν r).real A ≤ (obsMeasure M r).real A := by
    exact ENNReal.toReal_mono (by finiteness) ((hν.domination r) A)
  have htotal : (ν r).real Set.univ = diseaseMass M r := hν.mass r
  have hobsTotal : (obsMeasure M r).real Set.univ = obsMass M r := rfl
  have hcompl := hdom (I : Set ℝ)ᶜ
  rw [measureReal_compl I.property, measureReal_compl I.property,
    htotal, hobsTotal] at hcompl
  change diseaseMass M r - (ν r).real I ≤
    obsMass M r - stratumMass M r I at hcompl
  constructor
  · apply max_le measureReal_nonneg
    linarith
  · exact le_min (by
      calc
        (ν r).real I ≤ (ν r).real Set.univ :=
          measureReal_mono (Set.subset_univ (I : Set ℝ))
        _ = diseaseMass M r := htotal) (hdom I)

noncomputable def mixedAllocation (M : ImperfectReferenceModel)
    (r : Bool) (I : BorelScoreSet) (x : ℝ) : Measure ℝ :=
  ((ENNReal.ofReal
      (if stratumMass M r I = 0 then 0 else x / stratumMass M r I)) •
      (obsMeasure M r).restrict I) +
    ((ENNReal.ofReal
      (if obsMass M r - stratumMass M r I = 0 then 0
       else (diseaseMass M r - x) /
         (obsMass M r - stratumMass M r I))) •
      (obsMeasure M r).restrict (I : Set ℝ)ᶜ)

lemma mixedAllocation_real (M : ImperfectReferenceModel) (r : Bool)
    (I : BorelScoreSet) (x : ℝ)
    (hx : x ∈ Set.Icc (stratumLower M r I) (stratumUpper M r I)) :
    (mixedAllocation M r I x).real I = x := by
  have hp : 0 ≤ stratumMass M r I := measureReal_nonneg
  have hxp : x ≤ stratumMass M r I := le_trans hx.2 (min_le_right _ _)
  have hx0 : 0 ≤ x := le_trans (le_max_left _ _) hx.1
  change ENNReal.toReal ((mixedAllocation M r I x) I) = x
  have hdis : (I : Set ℝ) ∩ (I : Set ℝ)ᶜ = ∅ := by ext; simp
  have hcoef : 0 ≤ (if stratumMass M r I = 0 then 0
      else x / stratumMass M r I) := by
    split <;> positivity
  rw [mixedAllocation, Measure.add_apply]
  simp only [Measure.smul_apply, Measure.restrict_apply I.property,
    Set.inter_self, hdis, measure_empty, smul_zero, add_zero]
  rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef]
  change (if stratumMass M r I = 0 then 0 else x / stratumMass M r I) *
      stratumMass M r I = x
  by_cases hpi : stratumMass M r I = 0
  · have hxz : x = 0 := le_antisymm (hpi ▸ hxp) hx0
    simp [hpi, hxz]
  · simp [hpi]

-- @node: mixedAllocation_dominated
lemma mixedAllocation_dominated (M : ImperfectReferenceModel) (r : Bool)
    (I : BorelScoreSet) (x : ℝ)
    (hx : x ∈ Set.Icc (stratumLower M r I) (stratumUpper M r I)) :
    mixedAllocation M r I x ≤ obsMeasure M r := by
  have hp : 0 ≤ stratumMass M r I := measureReal_nonneg
  have hpq : stratumMass M r I ≤ obsMass M r :=
    measureReal_mono (Set.subset_univ (I : Set ℝ))
  have hx0 : 0 ≤ x := le_trans (le_max_left _ _) hx.1
  have hxp : x ≤ stratumMass M r I := le_trans hx.2 (min_le_right _ _)
  have hxa : x ≤ diseaseMass M r := le_trans hx.2 (min_le_left _ _)
  have hax0 : 0 ≤ diseaseMass M r - x := sub_nonneg.mpr hxa
  have haxq : diseaseMass M r - x ≤ obsMass M r - stratumMass M r I := by
    have := le_trans (le_max_right 0
      (diseaseMass M r - obsMass M r + stratumMass M r I)) hx.1
    linarith
  let k : ℝ := if stratumMass M r I = 0 then 0 else x / stratumMass M r I
  let ρ : ℝ := if obsMass M r - stratumMass M r I = 0 then 0
    else (diseaseMass M r - x) / (obsMass M r - stratumMass M r I)
  have hk0 : 0 ≤ k := by simp only [k]; split <;> positivity
  have hk1 : k ≤ 1 := by
    simp only [k]
    split
    · norm_num
    · exact (div_le_one (lt_of_le_of_ne hp (Ne.symm ‹_›))).2 hxp
  have hρ0 : 0 ≤ ρ := by simp only [ρ]; split <;> positivity
  have hρ1 : ρ ≤ 1 := by
    simp only [ρ]
    split
    · norm_num
    · exact (div_le_one (lt_of_le_of_ne (sub_nonneg.mpr hpq) (Ne.symm ‹_›))).2 haxq
  change (ENNReal.ofReal k • (obsMeasure M r).restrict I) +
      (ENNReal.ofReal ρ • (obsMeasure M r).restrict (I : Set ℝ)ᶜ) ≤ obsMeasure M r
  have hpart := Measure.restrict_add_restrict_compl
    (μ := obsMeasure M r) I.property
  calc
    _ ≤ (obsMeasure M r).restrict I +
        (obsMeasure M r).restrict (I : Set ℝ)ᶜ := by
      apply add_le_add
      · rw [Measure.le_iff]
        intro A hA
        rw [Measure.smul_apply]
        exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.mpr hk1)
      · rw [Measure.le_iff]
        intro A hA
        rw [Measure.smul_apply]
        exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.mpr hρ1)
    _ = obsMeasure M r := hpart

-- @node: mixedAllocation_mass
lemma mixedAllocation_mass (M : ImperfectReferenceModel) (r : Bool)
    (I : BorelScoreSet) (x : ℝ)
    (hx : x ∈ Set.Icc (stratumLower M r I) (stratumUpper M r I)) :
    (mixedAllocation M r I x).real Set.univ = diseaseMass M r := by
  have hdom := mixedAllocation_dominated M r I x hx
  letI : IsFiniteMeasure (mixedAllocation M r I x) :=
    isFiniteMeasure_of_le (obsMeasure M r) hdom
  have hp : 0 ≤ stratumMass M r I := measureReal_nonneg
  have hpq : stratumMass M r I ≤ obsMass M r :=
    measureReal_mono (Set.subset_univ (I : Set ℝ))
  have hx0 : 0 ≤ x := le_trans (le_max_left _ _) hx.1
  have hxp : x ≤ stratumMass M r I := le_trans hx.2 (min_le_right _ _)
  have hxa : x ≤ diseaseMass M r := le_trans hx.2 (min_le_left _ _)
  have hax0 : 0 ≤ diseaseMass M r - x := sub_nonneg.mpr hxa
  have haxq : diseaseMass M r - x ≤ obsMass M r - stratumMass M r I := by
    have := le_trans (le_max_right 0
      (diseaseMass M r - obsMass M r + stratumMass M r I)) hx.1
    linarith
  rw [mixedAllocation, measureReal_add_apply
    (by
      rw [Measure.smul_apply]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (by
      rw [Measure.smul_apply]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  change ENNReal.toReal (ENNReal.ofReal
      (if stratumMass M r ↑I = 0 then 0 else x / stratumMass M r ↑I) *
        (obsMeasure M r).restrict ↑I Set.univ) +
    ENNReal.toReal (ENNReal.ofReal
      (if obsMass M r - stratumMass M r ↑I = 0 then 0
       else (diseaseMass M r - x) / (obsMass M r - stratumMass M r ↑I)) *
        (obsMeasure M r).restrict (↑I)ᶜ Set.univ) = diseaseMass M r
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [Measure.restrict_apply MeasurableSet.univ,
    Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter]
  rw [ENNReal.toReal_ofReal (by split <;> positivity),
    ENNReal.toReal_ofReal (by split <;> positivity)]
  rw [show ENNReal.toReal ((obsMeasure M r) I) = stratumMass M r I by rfl]
  rw [show ENNReal.toReal ((obsMeasure M r) (I : Set ℝ)ᶜ) =
      obsMass M r - stratumMass M r I by
    exact measureReal_compl I.property]
  by_cases hpi : stratumMass M r I = 0
  · have hxz : x = 0 := le_antisymm (hpi ▸ hxp) hx0
    by_cases hq : obsMass M r = 0
    · have ha0 : diseaseMass M r = 0 := by
        have : diseaseMass M r ≤ 0 := by simpa [hpi, hxz, hq] using haxq
        linarith
      simp [hpi, hq, ha0]
    · simp [hpi, hxz, hq]
  · by_cases hpci : obsMass M r - stratumMass M r I = 0
    · have haxz : diseaseMass M r - x = 0 :=
        le_antisymm (hpci ▸ haxq) hax0
      have : x = diseaseMass M r := by linarith
      simp [hpi, hpci, this]
    · simp [hpi, hpci]

lemma minkowski_two_Icc {l₀ u₀ l₁ u₁ y : ℝ}
    (h₀ : l₀ ≤ u₀) (h₁ : l₁ ≤ u₁)
    (hy : y ∈ Set.Icc (l₀ + l₁) (u₀ + u₁)) :
    ∃ x₀ ∈ Set.Icc l₀ u₀, ∃ x₁ ∈ Set.Icc l₁ u₁, y = x₀ + x₁ := by
  rcases hy with ⟨hyl, hyu⟩
  by_cases h : y - l₁ ≤ u₀
  · exact ⟨y - l₁, ⟨by linarith, h⟩, l₁, ⟨le_rfl, h₁⟩, by ring⟩
  · exact ⟨u₀, ⟨h₀, le_rfl⟩, y - u₀, ⟨by linarith, by linarith⟩, by ring⟩

lemma mem_dominatedAllocation_image (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (I : BorelScoreSet) {y : ℝ} (hy : y ∈ Set.Icc (massLower M I) (massUpper M I)) :
    ∃ ν, DominatedAllocation M ν ∧
      (∑ r : Bool, (ν r).real I) = y := by
  have hstratum (r : Bool) : stratumLower M r I ≤ stratumUpper M r I := by
    have ha := diseaseMass_nonneg_le_obsMass M hg hπ r
    have hp0 : 0 ≤ stratumMass M r I := measureReal_nonneg
    have hpq : stratumMass M r I ≤ obsMass M r :=
      measureReal_mono (Set.subset_univ (I : Set ℝ))
    apply max_le
    · exact le_min ha.1 hp0
    · exact le_min (by linarith) (by linarith)
  have hy' : y ∈ Set.Icc
      (stratumLower M true I + stratumLower M false I)
      (stratumUpper M true I + stratumUpper M false I) := by
    simpa [massLower, massUpper, massEndpoints, stratumLower, stratumUpper,
      Fintype.sum_bool] using hy
  obtain ⟨x₁, hx₁, x₀, hx₀, hsum⟩ :=
    minkowski_two_Icc (hstratum true) (hstratum false) hy'
  let ν : Bool → Measure ℝ := fun r =>
    if r then mixedAllocation M true I x₁ else mixedAllocation M false I x₀
  refine ⟨ν, ?_, ?_⟩
  · constructor
    · intro r
      cases r <;> simp [ν, mixedAllocation_dominated, hx₀, hx₁]
    · intro r
      cases r <;> simp [ν, mixedAllocation_mass, hx₀, hx₁]
  · simp [ν, mixedAllocation_real, hx₀, hx₁]
    linarith

-- @node: dominatedAllocation_image_eq_Icc
lemma dominatedAllocation_image_eq_Icc (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M) (I : BorelScoreSet) :
    Causalean.PartialID.IdentifiedInterval
      (fun ν : Bool → Measure ℝ => ∑ r : Bool, (ν r).real I)
      (DominatedAllocation M) = Set.Icc (massLower M I) (massUpper M I) := by
  ext y
  constructor
  · rintro ⟨ν, rfl⟩
    have h₀ := dominated_stratum_mass_mem_Icc M ν.1 ν.2 false I
    have h₁ := dominated_stratum_mass_mem_Icc M ν.1 ν.2 true I
    simpa [massLower, massUpper, massEndpoints, stratumLower, stratumUpper,
      Fintype.sum_bool] using
      (show stratumLower M true I + stratumLower M false I ≤
          (ν.1 true).real I + (ν.1 false).real I ∧
        (ν.1 true).real I + (ν.1 false).real I ≤
          stratumUpper M true I + stratumUpper M false I by
        constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2])
  · intro hy
    obtain ⟨ν, hν, hval⟩ := mem_dominatedAllocation_image M hg hπ I hy
    exact ⟨⟨ν, hν⟩, hval⟩

lemma dominatedAllocation_image_ordConnected (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M) (I : BorelScoreSet) :
    (Causalean.PartialID.IdentifiedInterval
      (fun ν : Bool → Measure ℝ => ∑ r : Bool, (ν r).real I)
      (DominatedAllocation M)).OrdConnected := by
  rw [dominatedAllocation_image_eq_Icc M hg hπ I]
  exact Set.ordConnected_Icc

noncomputable def allocationIntegral (ν : Measure ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ s, f s ∂ν

noncomputable def cappedDualValue (μ : Measure ℝ) (a l : ℝ)
    (f : ℝ → ℝ) : ℝ :=
  a * l + ∫ s, max (f s - l) 0 ∂μ

lemma support_dual_stratum (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : ℝ) (f : ℝ → ℝ) (hf : Measurable f) (hbounded : ∃ C, ∀ x, |f x| ≤ C) :
    sSup {x : ℝ | ∃ ν : Measure ℝ, ν ≤ μ ∧ ν.real Set.univ = a ∧
      x = allocationIntegral ν f} =
      sInf {x : ℝ | ∃ l : ℝ,
        x = cappedDualValue μ a l f} := by sorry

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
