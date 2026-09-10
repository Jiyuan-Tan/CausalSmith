import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.OverlapUniqueness

/-!
# The affine deletion threshold

Finite-set lemmas identifying positive affine-minor separation with deletion distance.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set

noncomputable section

-- @node: maxAffineMinor_pos_iff_not_collinear
/-- The largest absolute affine minor is positive exactly when the indexed planar cloud is
not collinear. [This is the asserted conclusion](goal). -/
lemma maxAffineMinor_pos_iff_not_collinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (S : Finset ι) (s : ι → Fin p → ℝ) (k l : Fin p) :
    0 < maxAffineMinor S s k l ↔ ¬ CollinearPairs s k l S := by
  rw [maxAffineMinor, Finset.lt_fold_max]
  simp only [lt_self_iff_false, false_or]
  constructor
  · rintro ⟨efg, hefg, hpos⟩ hcol
    rcases Finset.mem_filter.mp hefg with ⟨hefgS, _⟩
    rcases Finset.mem_product.mp hefgS with ⟨heS, hfgS⟩
    rcases Finset.mem_product.mp hfgS with ⟨hfS, hgS⟩
    rw [hcol _ heS _ hfS _ hgS, abs_zero] at hpos
    exact (lt_irrefl 0 hpos).elim
  · intro hnc
    unfold CollinearPairs at hnc
    push Not at hnc
    obtain ⟨e, he, f, hf, g, hg, hminor⟩ := hnc
    have hef : e ≠ f := by
      intro h
      subst f
      simp [affineMinor] at hminor
    have heg : e ≠ g := by
      intro h
      subst g
      simp [affineMinor] at hminor
    have hfg : f ≠ g := by
      intro h
      subst g
      simp [affineMinor] at hminor
    refine ⟨(e, f, g), ?_, abs_pos.mpr hminor⟩
    simp [indexTriples, he, hf, hg, hef, heg, hfg]

-- @node: envDeletionDistance_gt_iff_affineSeparation_pos
/-- Deletion distance exceeds the corruption budget exactly when the worst retained-subset
affine-minor separation is positive. [Under the stated hypotheses](hyp:hp,hH,hs) [this conclusion](goal) applies. -/
lemma envDeletionDistance_gt_iff_affineSeparation_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι] {p m c : ℕ}
    (hp : 2 ≤ p) (H : Finset ι) (hH : H.card = honestCount m c)
    (s : ι → Fin p → ℝ) (hs : ∀ e ∈ H, ∀ k, 0 ≤ s e k) :
    envDeletionDistance H s > c ↔ 0 < affineSeparation hp H hH s hs := by
  classical
  let q := H.card - c
  let values : Finset ℝ := (offDiagPairs p).biUnion fun kl ↦
    (H.powersetCard q).image fun S ↦ maxAffineMinor S s kl.1 kl.2
  have hpairs : (offDiagPairs p).Nonempty := by
    let k : Fin p := ⟨0, by omega⟩
    let l : Fin p := ⟨1, by omega⟩
    exact ⟨(k, l), by simp [offDiagPairs, k, l]⟩
  have hq_le : q ≤ H.card := by simp [q]
  have hsubsets : (H.powersetCard q).Nonempty := by
    obtain ⟨S, hSH, hScard⟩ := Finset.exists_subset_card_eq hq_le
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨hSH, hScard⟩⟩
  have hvalues : values.Nonempty := by
    obtain ⟨kl, hkl⟩ := hpairs
    obtain ⟨S, hS⟩ := hsubsets
    refine ⟨maxAffineMinor S s kl.1 kl.2, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨kl, hkl, ?_⟩
    exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
  have hset : (↑values : Set ℝ) =
      {x : ℝ | ∃ kl ∈ offDiagPairs p,
        ∃ S ∈ H.powersetCard (H.card - c), x = maxAffineMinor S s kl.1 kl.2} := by
    ext x
    simp [values, q, eq_comm]
  rw [envDeletionDistance_gt_iff hp H s c]
  unfold affineSeparation
  by_cases hq3 : H.card - c < 3
  · rw [if_pos hq3]
    simp only [lt_self_iff_false]
    let k : Fin p := ⟨0, by omega⟩
    let l : Fin p := ⟨1, by omega⟩
    constructor
    · intro hall
      have hkl := hall k l (by simp [k, l])
      have htwo : min 2 H.card ≤ maxLineOccupancy H s k l := by
        unfold maxLineOccupancy
        by_cases hcard : 2 ≤ H.card
        · obtain ⟨S, hSH, hScard⟩ := Finset.exists_subset_card_eq hcard
          have hmem : S ∈ H.powerset.filter (CollinearPairs s k l) := by
            simp only [Finset.mem_filter, Finset.mem_powerset]
            refine ⟨hSH, ?_⟩
            intro e he f hf g hg
            have : e = f ∨ e = g ∨ f = g := by
              by_contra hn
              push Not at hn
              have hthree : ({e, f, g} : Finset ι).card = 3 := by simp [hn]
              have hle : ({e, f, g} : Finset ι).card ≤ S.card :=
                Finset.card_le_card (by simp only [Finset.insert_subset_iff,
                  Finset.singleton_subset_iff]; exact ⟨he, hf, hg⟩)
              omega
            rcases this with rfl | rfl | rfl <;> simp [affineMinor]
          have hle' : S.card ≤
              (H.powerset.filter (CollinearPairs s k l)).sup Finset.card :=
            Finset.le_sup hmem
          calc
            min 2 H.card = 2 := Nat.min_eq_left hcard
            _ = S.card := hScard.symm
            _ ≤ _ := hle'
        · have hle : H.card ≤ 1 := by omega
          have hmem : H ∈ H.powerset.filter (CollinearPairs s k l) := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr subset_rfl, ?_⟩
            intro e he f hf g hg
            have : e = f := by
              by_contra hef
              have h2 : 2 ≤ H.card := by
                have hsub : {e, f} ⊆ H := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl
                  · exact he
                  · exact hf
                have hpair := Finset.card_le_card hsub
                have hpaircard : ({e, f} : Finset ι).card = 2 := by simp [hef]
                omega
              omega
            subst f
            simp [affineMinor]
          have hle' : H.card ≤
              (H.powerset.filter (CollinearPairs s k l)).sup Finset.card :=
            Finset.le_sup hmem
          calc
            min 2 H.card = H.card := Nat.min_eq_right (by omega)
            _ ≤ _ := hle'
      have hq : H.card - c ≤ 2 := by omega
      omega
    · exact False.elim
  · rw [if_neg hq3, ← hset]
    have hsInf_mem : sInf (↑values : Set ℝ) ∈ values :=
      Set.Nonempty.csInf_mem (by simpa using hvalues) values.finite_toSet
    constructor
    · intro hall
      have hpositive : ∀ x ∈ values, 0 < x := by
        intro x hx
        simp only [values, Finset.mem_biUnion, Finset.mem_image] at hx
        obtain ⟨kl, hkl, S, hS, rfl⟩ := hx
        rw [maxAffineMinor_pos_iff_not_collinear]
        intro hcol
        have hocc := hall kl.1 kl.2 (Finset.mem_filter.mp hkl).2
        have hSsub := (Finset.mem_powersetCard.mp hS).1
        have hScard := (Finset.mem_powersetCard.mp hS).2
        have hle : S.card ≤ maxLineOccupancy H s kl.1 kl.2 := by
          unfold maxLineOccupancy
          exact Finset.le_sup (by simp [hSsub, hcol])
        omega
      exact hpositive _ hsInf_mem
    · intro hgamma k l hkl
      by_contra hocc
      push Not at hocc
      unfold maxLineOccupancy at hocc
      have hqpos : 0 < H.card - c := by omega
      obtain ⟨T, hTmem, hTcard⟩ :=
        (Finset.le_sup_iff hqpos).mp (show H.card - c ≤
          (H.powerset.filter (CollinearPairs s k l)).sup Finset.card by omega)
      obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq hTcard
      have hSmem : S ⊆ H :=
        hST.trans (Finset.mem_powerset.mp (Finset.mem_filter.mp hTmem).1)
      have hcol : CollinearPairs s k l S := by
        intro e he f hf g hg
        exact (Finset.mem_filter.mp hTmem).2 e (hST he) f (hST hf) g (hST hg)
      have hz : maxAffineMinor S s k l = 0 := by
        apply le_antisymm
        · rw [maxAffineMinor, Finset.fold_max_le]
          refine ⟨le_rfl, ?_⟩
          intro efg hefg
          rcases Finset.mem_filter.mp hefg with ⟨hefgS, _⟩
          rcases Finset.mem_product.mp hefgS with ⟨he, hfg⟩
          rcases Finset.mem_product.mp hfg with ⟨hf, hg⟩
          simp [hcol _ he _ hf _ hg]
        · exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
      have hzero_mem : 0 ∈ values := by
        refine Finset.mem_biUnion.mpr ⟨(k, l), ?_, ?_⟩
        · simp [offDiagPairs, hkl]
        · exact Finset.mem_image.mpr ⟨S,
            Finset.mem_powersetCard.mpr ⟨hSmem, hScard⟩, hz⟩
      have hinf_le : sInf (↑values : Set ℝ) ≤ 0 := csInf_le (by
        exact values.finite_toSet.bddBelow) hzero_mem
      exact (not_lt_of_ge hinf_le) hgamma

-- @node: compatibleSet_eq_singleton_of_deletionDistance_gt
/-- An honest BACKSHIFT explanation is the unique compatible normalized structure whenever its
pairwise affine deletion distance exceeds the replacement budget. [Under the stated hypotheses](hyp:honest_covariance_model,hdelta) [this conclusion](goal) applies. -/
lemma compatibleSet_eq_singleton_of_deletionDistance_gt {p m c : ℕ}
    (W : BackshiftSystem p m c)
    (backshift_normalization : BackshiftNormalization W)
    (nonnegative_shifts : NonnegativeShifts W)
    (honest_covariance_model : HonestCovarianceModel W)
    (invariant_noise_psd : W.invariantNoise.PosSemidef)
    (hdelta : envDeletionDistance W.honest W.shifts > c) :
    compatibleSet p m c ⟨W.covariance, W.covariance_psd⟩ = {W.structural} := by
  classical
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · refine ⟨backshift_normalization, W.honest, ?_, W.invariantNoise,
      invariant_noise_psd, W.shifts, nonnegative_shifts, honest_covariance_model⟩
    exact W.honest_card.ge
  · intro A hA
    rcases hA with ⟨hAnorm, K, hKcard, Psi, hPsi, t, ht, hcov⟩
    let first : BackshiftExplanation p m c W.covariance :=
      { fitted := W.honest
        fitted_card := W.honest_card.ge
        structural := W.structural
        structural_invertible := backshift_normalization.1
        structural_unit_diagonal := backshift_normalization.2.1
        cycle_bound := backshift_normalization.2.2.le
        cycle_strict := backshift_normalization.2.2
        invariantNoise := W.invariantNoise
        invariantNoise_psd := invariant_noise_psd
        shifts := W.shifts
        shifts_nonnegative := nonnegative_shifts
        covariance_eq := honest_covariance_model }
    let second : BackshiftExplanation p m c W.covariance :=
      { fitted := K
        fitted_card := hKcard
        structural := A
        structural_invertible := hAnorm.1
        structural_unit_diagonal := hAnorm.2.1
        cycle_bound := hAnorm.2.2.le
        cycle_strict := hAnorm.2.2
        invariantNoise := Psi
        invariantNoise_psd := hPsi
        shifts := t
        shifts_nonnegative := ht
        covariance_eq := hcov }
    have hoccupancy :=
      (envDeletionDistance_gt_iff W.dimension_at_least_two W.honest W.shifts c).mp hdelta
    have hnc : ∀ k l : Fin p, k < l →
        ¬ CollinearPairs first.shifts k l (first.fitted ∩ second.fitted) := by
      intro k l hkl hcol
      have hover := overlap_card_lower_bound W.honest K W.honest_card.ge hKcard
      have hsubset : W.honest ∩ K ⊆ W.honest := Finset.inter_subset_left
      have hle : (W.honest ∩ K).card ≤
          maxLineOccupancy W.honest W.shifts k l := by
        unfold maxLineOccupancy
        exact Finset.le_sup (by simp [hsubset, hcol, first, second])
      have hlt := hoccupancy k l hkl
      simp only [first, second] at hcol ⊢
      have hcard := W.honest_card
      simp only [honestCount] at hcard
      omega
    exact (overlap_uniqueness W.dimension_at_least_two W.corruption_lt
      W.covariance W.covariance_psd first second).2 hnc |>.symm

end

end CausalSmith.ExactID.RobustBackshiftUniformDistance
