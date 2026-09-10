import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TSharpMassSupport

/-! Exact coherent worst-case regret formula. -/

open MeasureTheory
open scoped BigOperators

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

def leftRegretTerm (M : ImperfectReferenceModel) (u t : Cutoff M) : ℝ :=
  (M.b + M.c) * massUpper M (cutoffInterval u.1 t.1) -
    M.c * ∑ r : Bool, stratumMass M r (cutoffInterval u.1 t.1)

def rightRegretTerm (M : ImperfectReferenceModel) (t u : Cutoff M) : ℝ :=
  M.c * ∑ r : Bool, stratumMass M r (cutoffInterval t.1 u.1) -
    (M.b + M.c) * massLower M (cutoffInterval t.1 u.1)

def sharpRegretRhs (M : ImperfectReferenceModel) (t : Cutoff M) : ℝ :=
  max 0 (max
    (sSup {x : ℝ | ∃ u : Cutoff M, u.1 < t.1 ∧ x = leftRegretTerm M u t})
    (sSup {x : ℝ | ∃ u : Cutoff M, t.1 < u.1 ∧ x = rightRegretTerm M t u}))

def JointComparatorAttainment (M : ImperfectReferenceModel) (t : Cutoff M) : Prop :=
  ∀ u : Cutoff M,
    ((u.1 < t.1 ∧ leftRegretTerm M u t = sharpRegretRhs M t) ∨
      (u = t ∧ sharpRegretRhs M t = 0) ∨
      (t.1 < u.1 ∧ rightRegretTerm M t u = sharpRegretRhs M t)) →
    ∃ Q : CompatibleCompletion M,
      netValueAt M Q u.1 - netValueAt M Q t.1 = sharpRegretRhs M t

-- @node: referSet_eq_cutoffInterval_union
lemma referSet_eq_cutoffInterval_union {u t : EReal} (hut : u < t) :
    (referSet u : Set ℝ) = cutoffInterval u t ∪ referSet t := by
  ext s
  simp only [referSet, cutoffInterval]
  constructor
  · intro hus
    by_cases hst : (s : EReal) < t
    · exact Or.inl ⟨hus, hst⟩
    · exact Or.inr (le_of_not_gt hst)
  · rintro (⟨hus, _⟩ | hts)
    · exact hus
    · exact le_trans (le_of_lt hut) hts

-- @node: measureReal_referSet_decomposition
lemma measureReal_referSet_decomposition (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u t : EReal} (hut : u < t) :
    μ.real (referSet u) = μ.real (cutoffInterval u t) + μ.real (referSet t) := by
  rw [referSet_eq_cutoffInterval_union hut]
  change μ.real ((cutoffInterval u t : Set ℝ) ∪ referSet t) = _
  rw [measureReal_union]
  · exact Set.disjoint_left.2 (by
      intro s hsI hst
      exact (not_lt_of_ge hst) hsI.2)
  · exact (referSet t).property

-- @node: netValue_contrast_of_lt
lemma netValue_contrast_of_lt (M : ImperfectReferenceModel)
    (Q : CompatibleCompletion M) (u t : EReal) (hut : u < t) :
    netValueAt M Q u - netValueAt M Q t =
      (M.b + M.c) * allocationMass (cutoffInterval u t) (completionAllocation Q.1) -
        M.c * ∑ r : Bool, stratumMass M r (cutoffInterval u t) := by
  letI := Q.2.probability
  rw [netValueAt, netValueAt, netValue_allocation_identity,
    netValue_allocation_identity]
  change ((M.b + M.c) * (∑ r : Bool, (latentSubmeasure Q r).real (referSet u)) -
      M.c * ∑ r : Bool, stratumMass M r (referSet u)) -
    ((M.b + M.c) * (∑ r : Bool, (latentSubmeasure Q r).real (referSet t)) -
      M.c * ∑ r : Bool, stratumMass M r (referSet t)) = _
  have hlatent (r : Bool) :
      (latentSubmeasure Q r).real (referSet u) =
        (latentSubmeasure Q r).real (cutoffInterval u t) +
          (latentSubmeasure Q r).real (referSet t) := by
    letI : IsFiniteMeasure (latentSubmeasure Q r) := by
      dsimp [latentSubmeasure]
      infer_instance
    apply measureReal_referSet_decomposition _ hut
  have hobs (r : Bool) :
      stratumMass M r (referSet u) =
        stratumMass M r (cutoffInterval u t) + stratumMass M r (referSet t) := by
    apply measureReal_referSet_decomposition _ hut
  simp_rw [hlatent, hobs]
  simp only [allocationMass, completionAllocation, latentSubmeasure,
    Fintype.sum_bool]
  ring

-- @node: netValue_contrast_of_gt
lemma netValue_contrast_of_gt (M : ImperfectReferenceModel)
    (Q : CompatibleCompletion M) (t u : EReal) (htu : t < u) :
    netValueAt M Q u - netValueAt M Q t =
      M.c * ∑ r : Bool, stratumMass M r (cutoffInterval t u) -
        (M.b + M.c) * allocationMass (cutoffInterval t u) (completionAllocation Q.1) := by
  have h := netValue_contrast_of_lt M Q t u htu
  linarith

-- @node: exists_completion_allocationMass_eq_lower
lemma exists_completion_allocationMass_eq_lower (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (I : BorelScoreSet) :
    ∃ Q : CompatibleCompletion M,
      allocationMass I (completionAllocation Q.1) = massLower M I := by
  let f0 : Bool → BoundedBorelFunction := fun _ =>
    ⟨fun _ => 0, measurable_const, ⟨0, by simp⟩⟩
  obtain ⟨_, ⟨ν, hν, hmass⟩, _, _⟩ := sharp_mass_support M hg hπ I f0
  let Q0 := allocationCompletion M ν
  have hQ0 := allocationCompletion_compatible M hg hπ ν hν
  refine ⟨⟨Q0, hQ0⟩, ?_⟩
  rw [allocationCompletion_allocation M ν hν]
  exact hmass

-- @node: exists_completion_allocationMass_eq_upper
lemma exists_completion_allocationMass_eq_upper (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (I : BorelScoreSet) :
    ∃ Q : CompatibleCompletion M,
      allocationMass I (completionAllocation Q.1) = massUpper M I := by
  let f0 : Bool → BoundedBorelFunction := fun _ =>
    ⟨fun _ => 0, measurable_const, ⟨0, by simp⟩⟩
  obtain ⟨_, _, ⟨ν, hν, hmass⟩, _⟩ := sharp_mass_support M hg hπ I f0
  let Q0 := allocationCompletion M ν
  have hQ0 := allocationCompletion_compatible M hg hπ ν hν
  refine ⟨⟨Q0, hQ0⟩, ?_⟩
  rw [allocationCompletion_allocation M ν hν]
  exact hmass

-- @node: compatible_netValue_bounds
lemma compatible_netValue_bounds (M : ImperfectReferenceModel)
    (hb : PositiveBenefit M) (hc : PositiveCost M)
    (Q : CompatibleCompletion M) (t : EReal) :
    -M.c ≤ netValueAt M Q t ∧ netValueAt M Q t ≤ M.b := by
  letI := Q.2.probability
  have hD0 : 0 ≤ Q.1.real {z | z.2.2 = true ∧ z.1 ∈ referSet t} :=
    measureReal_nonneg
  have hD1 : Q.1.real {z | z.2.2 = true ∧ z.1 ∈ referSet t} ≤ 1 := by
    calc
      _ ≤ Q.1.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hH0 : 0 ≤ Q.1.real {z | z.2.2 = false ∧ z.1 ∈ referSet t} :=
    measureReal_nonneg
  have hH1 : Q.1.real {z | z.2.2 = false ∧ z.1 ∈ referSet t} ≤ 1 := by
    calc
      _ ≤ Q.1.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hb0 : 0 < M.b := hb
  have hc0 : 0 < M.c := hc
  change -M.c ≤ M.b * _ - M.c * _ ∧ M.b * _ - M.c * _ ≤ M.b
  constructor <;> nlinarith

-- @node: compatible_netValue_contrast_le
lemma compatible_netValue_contrast_le (M : ImperfectReferenceModel)
    (hb : PositiveBenefit M) (hc : PositiveCost M)
    (Q : CompatibleCompletion M) (u t : EReal) :
    netValueAt M Q u - netValueAt M Q t ≤ M.b + M.c := by
  have hu := compatible_netValue_bounds M hb hc Q u
  have ht := compatible_netValue_bounds M hb hc Q t
  linarith

-- @node: completion_allocationMass_mem_Icc
lemma completion_allocationMass_mem_Icc (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (Q : CompatibleCompletion M) (I : BorelScoreSet) :
    allocationMass I (completionAllocation Q.1) ∈
      Set.Icc (massLower M I) (massUpper M I) := by
  have hν := compatible_allocation M Q.1 Q.2
  have hmem : allocationMass I (completionAllocation Q.1) ∈
      Causalean.PartialID.IdentifiedInterval
        (fun ν : Bool → Measure ℝ => ∑ r : Bool, (ν r).real I)
        (DominatedAllocation M) := by
    exact ⟨⟨completionAllocation Q.1, hν⟩, rfl⟩
  rw [dominatedAllocation_image_eq_Icc M hg hπ I] at hmem
  exact hmem

-- @node: thm:sharp-regret-formula
theorem sharp_regret_formula (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (hb : PositiveBenefit M) (hc : PositiveCost M) (t : Cutoff M) :
    regretAt M t = sharpRegretRhs M t ∧
      JointComparatorAttainment M t ∧
      optimizerSet M = {u ∈ M.T | ∃ hu : u ∈ M.T,
        regretAt M ⟨u, hu⟩ = minimaxRegretValue M} := by
  let W : Set ℝ := {x | ∃ Q : CompatibleCompletion M, ∃ u : Cutoff M,
    x = netValueAt M Q u.1 - netValueAt M Q t.1}
  let L : Set ℝ := {x | ∃ u : Cutoff M,
    u.1 < t.1 ∧ x = leftRegretTerm M u t}
  let R : Set ℝ := {x | ∃ u : Cutoff M,
    t.1 < u.1 ∧ x = rightRegretTerm M t u}
  obtain ⟨Qbase, _⟩ := exists_completion_allocationMass_eq_lower M hg hπ (referSet t.1)
  have hWzero : (0 : ℝ) ∈ W := by
    exact ⟨Qbase, t, by simp⟩
  have hWne : W.Nonempty := ⟨0, hWzero⟩
  have hWbdd : BddAbove W := by
    refine ⟨M.b + M.c, ?_⟩
    rintro x ⟨Q, u, rfl⟩
    exact compatible_netValue_contrast_le M hb hc Q u.1 t.1
  have hLbdd : BddAbove L := by
    refine ⟨M.b + M.c, ?_⟩
    rintro x ⟨u, hut, rfl⟩
    obtain ⟨Q, hQ⟩ := exists_completion_allocationMass_eq_upper M hg hπ
      (cutoffInterval u.1 t.1)
    change (M.b + M.c) * massUpper M (cutoffInterval u.1 t.1) -
      M.c * ∑ r : Bool, stratumMass M r (cutoffInterval u.1 t.1) ≤ _
    rw [← hQ]
    rw [← netValue_contrast_of_lt M Q u.1 t.1 hut]
    exact compatible_netValue_contrast_le M hb hc Q u.1 t.1
  have hRbdd : BddAbove R := by
    refine ⟨M.b + M.c, ?_⟩
    rintro x ⟨u, htu, rfl⟩
    obtain ⟨Q, hQ⟩ := exists_completion_allocationMass_eq_lower M hg hπ
      (cutoffInterval t.1 u.1)
    change M.c * ∑ r : Bool, stratumMass M r (cutoffInterval t.1 u.1) -
      (M.b + M.c) * massLower M (cutoffInterval t.1 u.1) ≤ _
    rw [← hQ]
    rw [← netValue_contrast_of_gt M Q t.1 u.1 htu]
    exact compatible_netValue_contrast_le M hb hc Q u.1 t.1
  have hLsup : sSup L ≤ sSup W := by
    by_cases hL : L.Nonempty
    · apply csSup_le hL
      intro x hx
      rcases hx with ⟨u, hut, rfl⟩
      obtain ⟨Q, hQ⟩ := exists_completion_allocationMass_eq_upper M hg hπ
        (cutoffInterval u.1 t.1)
      apply le_csSup hWbdd
      refine ⟨Q, u, ?_⟩
      rw [netValue_contrast_of_lt M Q u.1 t.1 hut, hQ]
      rfl
    · rw [Set.not_nonempty_iff_eq_empty.mp hL]
      simpa using le_csSup hWbdd hWzero
  have hRsup : sSup R ≤ sSup W := by
    by_cases hR : R.Nonempty
    · apply csSup_le hR
      intro x hx
      rcases hx with ⟨u, htu, rfl⟩
      obtain ⟨Q, hQ⟩ := exists_completion_allocationMass_eq_lower M hg hπ
        (cutoffInterval t.1 u.1)
      apply le_csSup hWbdd
      refine ⟨Q, u, ?_⟩
      rw [netValue_contrast_of_gt M Q t.1 u.1 htu, hQ]
      rfl
    · rw [Set.not_nonempty_iff_eq_empty.mp hR]
      simpa using le_csSup hWbdd hWzero
  have hregret : regretAt M t = sharpRegretRhs M t := by
    change sSup W = max 0 (max (sSup L) (sSup R))
    apply le_antisymm
    · apply csSup_le hWne
      intro x hx
      rcases hx with ⟨Q, u, rfl⟩
      rcases lt_trichotomy u.1 t.1 with hut | hut | htu
      · have hmass := (completion_allocationMass_mem_Icc M hg hπ Q
          (cutoffInterval u.1 t.1)).2
        rw [netValue_contrast_of_lt M Q u.1 t.1 hut]
        calc
          _ ≤ leftRegretTerm M u t := by
            dsimp [leftRegretTerm]
            have hbc : 0 ≤ M.b + M.c := by
              have hb0 : 0 < M.b := hb
              have hc0 : 0 < M.c := hc
              linarith
            gcongr
          _ ≤ sSup L := le_csSup hLbdd ⟨u, hut, rfl⟩
          _ ≤ max 0 (max (sSup L) (sSup R)) :=
            le_trans (le_max_left _ _) (le_max_right _ _)
      · have heu : u = t := Subtype.ext hut
        subst u
        simp
      · have hmass := (completion_allocationMass_mem_Icc M hg hπ Q
          (cutoffInterval t.1 u.1)).1
        rw [netValue_contrast_of_gt M Q t.1 u.1 htu]
        calc
          _ ≤ rightRegretTerm M t u := by
            dsimp [rightRegretTerm]
            have hbc : 0 ≤ M.b + M.c := by
              have hb0 : 0 < M.b := hb
              have hc0 : 0 < M.c := hc
              linarith
            nlinarith
          _ ≤ sSup R := le_csSup hRbdd ⟨u, htu, rfl⟩
          _ ≤ max 0 (max (sSup L) (sSup R)) :=
            le_trans (le_max_right _ _) (le_max_right _ _)
    · apply max_le
      · exact le_csSup hWbdd hWzero
      · exact max_le hLsup hRsup
  refine ⟨hregret, ?_, ?_⟩
  · intro u hu
    rcases hu with hu | hu | hu
    · obtain ⟨Q, hQ⟩ := exists_completion_allocationMass_eq_upper M hg hπ
        (cutoffInterval u.1 t.1)
      refine ⟨Q, ?_⟩
      rw [netValue_contrast_of_lt M Q u.1 t.1 hu.1, hQ, ← hu.2]
      rfl
    · obtain ⟨Q, _⟩ := exists_completion_allocationMass_eq_lower M hg hπ (referSet t.1)
      refine ⟨Q, ?_⟩
      rw [hu.1, sub_self, hu.2]
    · obtain ⟨Q, hQ⟩ := exists_completion_allocationMass_eq_lower M hg hπ
        (cutoffInterval t.1 u.1)
      refine ⟨Q, ?_⟩
      rw [netValue_contrast_of_gt M Q t.1 u.1 hu.1, hQ, ← hu.2]
      rfl
  · ext u
    simp only [optimizerSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hu, hopt⟩
      exact ⟨hu, hu, hopt⟩
    · rintro ⟨hu, _, hopt⟩
      exact ⟨hu, hopt⟩

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
