import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Basic

/-! Algebra and boundedness consequences shared by the main results. -/

open MeasureTheory
open scoped BigOperators

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

lemma obsMass_false_add_true (M : ImperfectReferenceModel) :
    obsMass M false + obsMass M true = 1 := by
  rw [obsMass_eq_reference_event, obsMass_eq_reference_event]
  have hd : Disjoint {z : ℝ × Bool | z.2 = false} {z | z.2 = true} := by
    simp [Set.disjoint_left]
  have hm : MeasurableSet {z : ℝ × Bool | z.2 = true} :=
    measurable_snd (MeasurableSet.singleton true)
  have hu : {z : ℝ × Bool | z.2 = false} ∪ {z | z.2 = true} = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (Bool.eq_false_or_eq_true z.2).symm
  calc
    M.P.real {z : ℝ × Bool | z.2 = false} + M.P.real {z | z.2 = true} =
        M.P.real ({z | z.2 = false} ∪ {z | z.2 = true}) :=
      (measureReal_union hd hm).symm
    _ = M.P.real Set.univ := congrArg M.P.real hu
    _ = 1 := by simp

lemma observed_minus_disease_true (M : ImperfectReferenceModel)
    (hg : InformativeReference M) :
    obsMass M true - diseaseMass M true =
      (1 - M.beta) * (1 - prevalence M) := by
  have hgne : youden M ≠ 0 := ne_of_gt hg
  simp only [diseaseMass, ↓reduceIte]
  unfold prevalence
  field_simp [hgne]
  unfold youden at *
  ring

lemma observed_minus_disease_false (M : ImperfectReferenceModel)
    (hg : InformativeReference M) :
    obsMass M false - diseaseMass M false =
      M.beta * (1 - prevalence M) := by
  have hgne : youden M ≠ 0 := ne_of_gt hg
  have hfalse : obsMass M false = 1 - obsMass M true := by
    linarith [obsMass_false_add_true M]
  rw [hfalse]
  simp only [diseaseMass, Bool.false_eq_true, ↓reduceIte]
  unfold prevalence
  field_simp [hgne]
  unfold youden at *
  ring

lemma diseaseMass_nonneg_le_obsMass (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M) (r : Bool) :
    0 ≤ diseaseMass M r ∧ diseaseMass M r ≤ obsMass M r := by
  cases r with
  | false =>
      constructor
      · simp only [diseaseMass, Bool.false_eq_true, ↓reduceIte]
        exact mul_nonneg (sub_nonneg.mpr M.alpha_mem_Icc.2) (le_of_lt hπ.1)
      · have hnonneg : 0 ≤ M.beta * (1 - prevalence M) :=
          mul_nonneg M.beta_mem_Icc.1 (sub_nonneg.mpr (le_of_lt hπ.2))
        linarith [observed_minus_disease_false M hg]
  | true =>
      constructor
      · simp only [diseaseMass, ↓reduceIte]
        exact mul_nonneg M.alpha_mem_Icc.1 (le_of_lt hπ.1)
      · have hnonneg : 0 ≤ (1 - M.beta) * (1 - prevalence M) :=
          mul_nonneg (sub_nonneg.mpr M.beta_mem_Icc.2)
            (sub_nonneg.mpr (le_of_lt hπ.2))
        linarith [observed_minus_disease_true M hg]

lemma diseaseMassRange_of_assumptions (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M) :
    DiseaseMassRange M := by
  intro r
  exact ⟨(diseaseMass_nonneg_le_obsMass M hg hπ r).1,
    (diseaseMass_nonneg_le_obsMass M hg hπ r).2.trans (obsMass_mem_Icc M r).2⟩
  -- @realizes \(a_r\)(derived range [0,1] under the paper model assumptions)

-- @node: diseaseMass_sum
lemma diseaseMass_sum (M : ImperfectReferenceModel) :
    ∑ r : Bool, diseaseMass M r = prevalence M := by
  simp [diseaseMass]
  ring

lemma massEndpoints_mem_Icc (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (I : BorelScoreSet) :
    massLower M I ∈ Set.Icc (0 : ℝ) 1 ∧
      massUpper M I ∈ Set.Icc (0 : ℝ) 1 := by
  have hmass (r : Bool) : 0 ≤ diseaseMass M r :=
    (diseaseMass_nonneg_le_obsMass M hg hπ r).1
  have hstratum (r : Bool) :
      stratumMass M r I ≤ obsMass M r := by
    exact measureReal_mono (Set.subset_univ (I : Set ℝ))
  have hlower (r : Bool) :
      0 ≤ max 0 (diseaseMass M r - obsMass M r + stratumMass M r I) ∧
      max 0 (diseaseMass M r - obsMass M r + stratumMass M r I) ≤
        diseaseMass M r := by
    constructor
    · exact le_max_left _ _
    · exact max_le (hmass r) (by linarith [hstratum r])
  have hupper (r : Bool) :
      0 ≤ min (diseaseMass M r) (stratumMass M r I) ∧
      min (diseaseMass M r) (stratumMass M r I) ≤ diseaseMass M r := by
    constructor
    · exact le_min (hmass r) measureReal_nonneg
    · exact min_le_left _ _
  constructor
  · constructor
    · simp only [massLower, massEndpoints]
      exact Finset.sum_nonneg fun r _ => (hlower r).1
    · calc
        massLower M I ≤ ∑ r : Bool, diseaseMass M r := by
          simp only [massLower, massEndpoints]
          exact Finset.sum_le_sum fun r _ => (hlower r).2
        _ = prevalence M := diseaseMass_sum M
        _ ≤ 1 := le_of_lt hπ.2
  · constructor
    · simp only [massUpper, massEndpoints]
      exact Finset.sum_nonneg fun r _ => (hupper r).1
    · calc
        massUpper M I ≤ ∑ r : Bool, diseaseMass M r := by
          simp only [massUpper, massEndpoints]
          exact Finset.sum_le_sum fun r _ => (hupper r).2
        _ = prevalence M := diseaseMass_sum M
        _ ≤ 1 := le_of_lt hπ.2
  -- @realizes \(L(I)\)(range [0,1]) @realizes \(U(I)\)(range [0,1])

lemma netValue_bounds (M : ImperfectReferenceModel)
    (Q : Measure (ℝ × Bool × Bool)) (hQ : CompatibleLaw M Q) (t : EReal)
    (hb : PositiveBenefit M) (hc : PositiveCost M) :
    -M.c ≤ netValueAt M ⟨Q, hQ⟩ t ∧ netValueAt M ⟨Q, hQ⟩ t ≤ M.b := by
  letI := hQ.probability
  let diseasedReferred : Set (ℝ × Bool × Bool) :=
    {z | z.2.2 = true ∧ z.1 ∈ referSet t}
  let healthyReferred : Set (ℝ × Bool × Bool) :=
    {z | z.2.2 = false ∧ z.1 ∈ referSet t}
  have hd_nonneg : 0 ≤ Q.real diseasedReferred := measureReal_nonneg
  have hh_nonneg : 0 ≤ Q.real healthyReferred := measureReal_nonneg
  have hd_le : Q.real diseasedReferred ≤ 1 := by
    calc
      Q.real diseasedReferred ≤ Q.real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hh_le : Q.real healthyReferred ≤ 1 := by
    calc
      Q.real healthyReferred ≤ Q.real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  change 0 < M.b at hb
  change 0 < M.c at hc
  change -M.c ≤ M.b * Q.real diseasedReferred - M.c * Q.real healthyReferred ∧
    M.b * Q.real diseasedReferred - M.c * Q.real healthyReferred ≤ M.b
  constructor <;> nlinarith [hb, hc]

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
