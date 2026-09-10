import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.GlobalCollinearAmbiguity

/-!
# Sharp replacement radius

The population singleton-recovery threshold and its positive-definite ambiguity witness.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity

noncomputable section

-- @node: thm:sharp-replacement-radius
/-- Affine deletion distance strictly exceeding the corruption budget is equivalent to positive
affine separation and gives singleton replacement compatibility; in the positive-definite
interior failure has a matching ambiguity witness. [Under the stated hypotheses](hyp:honest_covariance_model) [this conclusion](goal) applies. -/
theorem sharp_replacement_radius {p m c : ℕ} (W : BackshiftSystem p m c)
    (backshift_normalization : BackshiftNormalization W)
    (nonnegative_shifts : NonnegativeShifts W)
    (honest_covariance_model : HonestCovarianceModel W)
    (invariant_noise_psd : W.invariantNoise.PosSemidef) :
    let delta := envDeletionDistance W.honest W.shifts
      -- @realizes delta(exact deletion distance of the honest design)
    let gamma := affineSeparation W.dimension_at_least_two W.honest W.honest_card
      W.shifts nonnegative_shifts
      -- @realizes gamma(worst-overlap affine-minor separation)
    (delta > c ↔ gamma > 0) ∧
    (delta > c → compatibleSet p m c ⟨W.covariance, W.covariance_psd⟩ = {W.structural}) ∧
    (W.invariantNoise.PosDef → delta ≤ c →
      ∃ (replacementCovariance : PSDCovarianceFamily p m)
        (D' : RealMatrix p) (Omega' : RealMatrix p)
        (H' : Finset (Environment m)) (s' : Environment m → Fin p → ℝ),
        (∀ e ∈ W.honest, replacementCovariance.1 e = W.covariance e) ∧
        (∀ e ∉ W.honest, (replacementCovariance.1 e).PosDef) ∧
        D' ∈ admissibleSet p ∧ D' ≠ W.structural ∧ Omega'.PosDef ∧
        H'.card = honestCount m c ∧
        (∀ e ∈ H', ∀ k, 0 ≤ s' e k) ∧
        (∀ e ∈ H', replacementCovariance.1 e =
          D'⁻¹ * (Omega' + Matrix.diagonal (s' e)) * D'⁻¹.transpose) ∧
        W.structural ∈ compatibleSet p m c replacementCovariance ∧
        D' ∈ compatibleSet p m c replacementCovariance) ∧
    (delta ≤ c →
      ∃ (interiorInstance : BackshiftSystem p m c) (D' : RealMatrix p),
        interiorInstance.honest = W.honest ∧
        interiorInstance.shifts = W.shifts ∧
        interiorInstance.invariantNoise.PosDef ∧
        (∀ e, (interiorInstance.covariance e).PosDef) ∧
        BackshiftNormalization interiorInstance ∧
        NonnegativeShifts interiorInstance ∧
        HonestCovarianceModel interiorInstance ∧
        D' ≠ interiorInstance.structural ∧
        interiorInstance.structural ∈
          compatibleSet p m c
            ⟨interiorInstance.covariance, interiorInstance.covariance_psd⟩ ∧
        D' ∈ compatibleSet p m c
          ⟨interiorInstance.covariance, interiorInstance.covariance_psd⟩) := by
  dsimp only
  let fixedWitness : ∀ (V : BackshiftSystem p m c),
      BackshiftNormalization V → NonnegativeShifts V → HonestCovarianceModel V →
      V.invariantNoise.PosDef → envDeletionDistance V.honest V.shifts ≤ c →
      ∃ (replacementCovariance : PSDCovarianceFamily p m)
        (D' : RealMatrix p) (Omega' : RealMatrix p)
        (H' : Finset (Environment m)) (s' : Environment m → Fin p → ℝ),
        (∀ e ∈ V.honest, replacementCovariance.1 e = V.covariance e) ∧
        (∀ e ∉ V.honest, (replacementCovariance.1 e).PosDef) ∧
        D' ∈ admissibleSet p ∧ D' ≠ V.structural ∧ Omega'.PosDef ∧
        H'.card = honestCount m c ∧
        (∀ e ∈ H', ∀ k, 0 ≤ s' e k) ∧
        (∀ e ∈ H', replacementCovariance.1 e =
          D'⁻¹ * (Omega' + Matrix.diagonal (s' e)) * D'⁻¹.transpose) ∧
        V.structural ∈ compatibleSet p m c replacementCovariance ∧
        D' ∈ compatibleSet p m c replacementCovariance := by
    intro V hnorm hnonneg hmodel hOmega hdelta
    classical
    let q := V.honest.card - c
    have hnotall : ¬ ∀ k l : Fin p, k < l →
        maxLineOccupancy V.honest V.shifts k l < q := by
      intro hall
      have hgt := (envDeletionDistance_gt_iff V.dimension_at_least_two
        V.honest V.shifts c).2 (by simpa [q] using hall)
      omega
    push Not at hnotall
    obtain ⟨k, l, hkl, hocc⟩ := hnotall
    have hij : k ≠ l := ne_of_lt hkl
    by_cases hq : q = 0
    · let s0 : PUnit.{1} → Fin p → ℝ := fun _ _ ↦ 0
      let cert0 : @AffineLineCertificate p PUnit.{1} s0 k l :=
        { u := 1, v := 0, c := 0, normal_ne := Or.inl one_ne_zero,
          equation := by intro e; simp [s0] }
      obtain ⟨D', Omega', s1, hD'adm, hD'ne, hOmega'pd, hs1nonneg,
          _hcovpd, _hcov⟩ :=
        exists_globally_admissible_collinear_ambiguity V.structural V.invariantNoise
          s0 hij hnorm hOmega (by intro e j; simp [s0]) cert0
      have hcompcard : V.honestᶜ.card = c := by
        rw [Finset.card_compl, Fintype.card_fin]
        rw [V.honest_card]
        unfold honestCount
        have hc := V.corruption_lt
        omega
      have hh_le : honestCount m c ≤ V.honestᶜ.card := by
        rw [hcompcard]
        have : V.honest.card ≤ c := Nat.sub_eq_zero_iff_le.mp hq
        rw [V.honest_card] at this
        exact this
      obtain ⟨H', hH'comp, hH'card⟩ := Finset.exists_subset_card_eq hh_le
      let outsideCov : Environment m → RealMatrix p := fun e ↦
        representedCovariance D' Omega' (s1 PUnit.unit)
      have houtsidepd : ∀ e, (outsideCov e).PosDef := by
        intro e
        exact representedCovariance_posDef D' Omega' (s1 PUnit.unit)
          hD'adm.1 hOmega'pd (hs1nonneg PUnit.unit)
      let replacementCovariance : PSDCovarianceFamily p m :=
        ⟨fun e ↦ if e ∈ V.honest then V.covariance e else outsideCov e,
          fun e ↦ by
            by_cases he : e ∈ V.honest
            · simpa [he] using V.covariance_psd e
            · simpa [he] using (houtsidepd e).posSemidef⟩
      let s' : Environment m → Fin p → ℝ := fun _ ↦ s1 PUnit.unit
      refine ⟨replacementCovariance, D', Omega', H', s', ?_, ?_, hD'adm,
        hD'ne, hOmega'pd, hH'card, ?_, ?_, ?_, ?_⟩
      · intro e he
        simp [replacementCovariance, he]
      · intro e he
        simpa [replacementCovariance, he] using houtsidepd e
      · intro e he j
        exact hs1nonneg PUnit.unit j
      · intro e he
        have henot : e ∉ V.honest := by
          exact Finset.mem_compl.mp (hH'comp he)
        rw [show replacementCovariance.1 e = outsideCov e by
          simp [replacementCovariance, henot]]
        rfl
      · refine ⟨hnorm, V.honest, V.honest_card.ge, V.invariantNoise,
          hOmega.posSemidef, V.shifts, hnonneg, ?_⟩
        intro e he
        simpa [replacementCovariance, he] using hmodel e he
      · refine ⟨hD'adm, H', hH'card.ge, Omega', hOmega'pd.posSemidef,
          s', ?_, ?_⟩
        · exact fun e he j ↦ hs1nonneg PUnit.unit j
        · intro e he
          have henot : e ∉ V.honest := by
            exact Finset.mem_compl.mp (hH'comp he)
          rw [show replacementCovariance.1 e = outsideCov e by
            simp [replacementCovariance, henot]]
          rfl
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      have hc_lt_honest : c < V.honest.card := by
        exact Nat.sub_pos_iff_lt.mp (by simpa [q] using hqpos)
      unfold maxLineOccupancy at hocc
      obtain ⟨T, hTmem, hTcard⟩ := (Finset.le_sup_iff hqpos).mp hocc
      obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq hTcard
      have hSH : S ⊆ V.honest :=
        hST.trans (Finset.mem_powerset.mp (Finset.mem_filter.mp hTmem).1)
      have hScol : CollinearPairs V.shifts k l S := by
        intro e he f hf g hg
        exact (Finset.mem_filter.mp hTmem).2 e (hST he) f (hST hf) g (hST hg)
      have hSnonempty : S.Nonempty := Finset.card_pos.mp (by simpa [hScard] using hqpos)
      let cert := affineLineCertificate_of_collinearPairs V.shifts k l S hSnonempty hScol
      let sS : {e // e ∈ S} → Fin p → ℝ := fun e ↦ V.shifts e.1
      letI : Nonempty {e // e ∈ S} := ⟨⟨hSnonempty.choose, hSnonempty.choose_spec⟩⟩
      obtain ⟨D', Omega', sS', hD'adm, hD'ne, hOmega'pd, hsS'nonneg,
          _hcovpd, hcov⟩ :=
        exists_globally_admissible_collinear_ambiguity V.structural V.invariantNoise
          sS hij hnorm hOmega (by
            intro e j
            exact hnonneg e.1 (hSH e.2) j) cert
      have hcompcard : V.honestᶜ.card = c := by
        rw [Finset.card_compl, Fintype.card_fin]
        rw [V.honest_card]
        unfold honestCount
        have hc := V.corruption_lt
        omega
      let H' := S ∪ V.honestᶜ
      have hdisjoint : Disjoint S V.honestᶜ := by
        rw [Finset.disjoint_left]
        intro e heS hecomp
        exact (Finset.mem_compl.mp hecomp) (hSH heS)
      have hH'card : H'.card = honestCount m c := by
        change (S ∪ V.honestᶜ).card = honestCount m c
        rw [Finset.card_union_of_disjoint hdisjoint, hScard, hcompcard]
        change V.honest.card - c + c = honestCount m c
        rw [Nat.sub_add_cancel (Nat.le_of_lt hc_lt_honest), V.honest_card]
      let s' : Environment m → Fin p → ℝ := fun e ↦
        if he : e ∈ S then sS' ⟨e, he⟩ else 0
      let outsideCov : Environment m → RealMatrix p := fun _ ↦
        representedCovariance D' Omega' 0
      have houtsidepd : ∀ e, (outsideCov e).PosDef := by
        intro e
        exact representedCovariance_posDef D' Omega' 0 hD'adm.1 hOmega'pd
          (by intro j; simp)
      let replacementCovariance : PSDCovarianceFamily p m :=
        ⟨fun e ↦ if e ∈ V.honest then V.covariance e else outsideCov e,
          fun e ↦ by
            by_cases he : e ∈ V.honest
            · simpa [he] using V.covariance_psd e
            · simpa [he] using (houtsidepd e).posSemidef⟩
      refine ⟨replacementCovariance, D', Omega', H', s', ?_, ?_, hD'adm,
        hD'ne, hOmega'pd, hH'card, ?_, ?_, ?_, ?_⟩
      · intro e he
        simp [replacementCovariance, he]
      · intro e he
        simpa [replacementCovariance, he] using houtsidepd e
      · intro e he j
        dsimp [s']
        split_ifs with heS
        · exact hsS'nonneg ⟨e, heS⟩ j
        · simp
      · intro e he
        rcases Finset.mem_union.mp he with heS | hecomp
        · have heH := hSH heS
          rw [show replacementCovariance.1 e = V.covariance e by
            simp [replacementCovariance, heH]]
          rw [hmodel e heH]
          have hcove := hcov ⟨e, heS⟩
          dsimp [sS] at hcove
          dsimp [s']
          simp only [dif_pos heS]
          exact hcove.symm
        · have henot : e ∉ V.honest := Finset.mem_compl.mp hecomp
          have heSnot : e ∉ S := fun hSmem ↦ henot (hSH hSmem)
          rw [show replacementCovariance.1 e = outsideCov e by
            simp [replacementCovariance, henot]]
          rw [show s' e = 0 by simp [s', heSnot]]
          rfl
      · refine ⟨hnorm, V.honest, V.honest_card.ge, V.invariantNoise,
          hOmega.posSemidef, V.shifts, hnonneg, ?_⟩
        intro e he
        simpa [replacementCovariance, he] using hmodel e he
      · refine ⟨hD'adm, H', hH'card.ge, Omega', hOmega'pd.posSemidef,
          s', ?_, ?_⟩
        · intro e he j
          dsimp [s']
          split_ifs with heS
          · exact hsS'nonneg ⟨e, heS⟩ j
          · simp
        · exact fun e he ↦ by
            rcases Finset.mem_union.mp he with heS | hecomp
            · have heH := hSH heS
              rw [show replacementCovariance.1 e = V.covariance e by
                simp [replacementCovariance, heH]]
              rw [hmodel e heH]
              have hcove := hcov ⟨e, heS⟩
              dsimp [sS] at hcove
              dsimp [s']
              simp only [dif_pos heS]
              exact hcove.symm
            · have henot : e ∉ V.honest := Finset.mem_compl.mp hecomp
              have heSnot : e ∉ S := fun hSmem ↦ henot (hSH hSmem)
              rw [show replacementCovariance.1 e = outsideCov e by
                simp [replacementCovariance, henot]]
              rw [show s' e = 0 by simp [s', heSnot]]
              rfl
  refine ⟨envDeletionDistance_gt_iff_affineSeparation_pos
      W.dimension_at_least_two W.honest W.honest_card W.shifts nonnegative_shifts,
    compatibleSet_eq_singleton_of_deletionDistance_gt W backshift_normalization
      nonnegative_shifts honest_covariance_model invariant_noise_psd, ?_, ?_⟩
  · exact fixedWitness W backshift_normalization nonnegative_shifts honest_covariance_model
  · intro hdelta
    let Sigma0 : Environment m → RealMatrix p := fun e ↦
      if e ∈ W.honest then
        Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity.representedCovariance
          W.structural 1 (W.shifts e)
      else 1
    have hSigma0pd : ∀ e, (Sigma0 e).PosDef := by
      intro e
      by_cases he : e ∈ W.honest
      · simp only [Sigma0, if_pos he]
        exact
          Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity.representedCovariance_posDef
            W.structural 1 (W.shifts e) W.structural_invertible Matrix.PosDef.one
            (fun k ↦ nonnegative_shifts e he k)
      · simpa [Sigma0, he] using (Matrix.PosDef.one : (1 : RealMatrix p).PosDef)
    let W0 : BackshiftSystem p m c :=
      { dimension_at_least_two := W.dimension_at_least_two
        environment_nonempty := W.environment_nonempty
        corruption_lt := W.corruption_lt
        honest := W.honest
        honest_card := W.honest_card
        covariance := Sigma0
        covariance_psd := fun e ↦ (hSigma0pd e).posSemidef
        structural := W.structural
        structural_invertible := W.structural_invertible
        invariantNoise := 1
        invariantNoise_symmetric := by simp
        shifts := W.shifts }
    have hW0norm : BackshiftNormalization W0 := backshift_normalization
    have hW0nonneg : NonnegativeShifts W0 := nonnegative_shifts
    have hW0model : HonestCovarianceModel W0 := by
      intro e he
      simp [W0, Sigma0, he,
        Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity.representedCovariance]
    have hdelta0 : envDeletionDistance W0.honest W0.shifts ≤ c := hdelta
    obtain ⟨replacementCovariance, D', Omega', H', s', hagree, houtside,
        hD'adm, hD'ne, hOmega'pd, hH'card, hs'nonneg, hs'model, hDmem, hD'mem⟩ :=
      fixedWitness W0 hW0norm hW0nonneg hW0model Matrix.PosDef.one hdelta0
    let interiorInstance : BackshiftSystem p m c :=
      { dimension_at_least_two := W.dimension_at_least_two
        environment_nonempty := W.environment_nonempty
        corruption_lt := W.corruption_lt
        honest := W.honest
        honest_card := W.honest_card
        covariance := replacementCovariance.1
        covariance_psd := replacementCovariance.2
        structural := W.structural
        structural_invertible := W.structural_invertible
        invariantNoise := 1
        invariantNoise_symmetric := by simp
        shifts := W.shifts }
    refine ⟨interiorInstance, D', rfl, rfl, Matrix.PosDef.one, ?_, hW0norm,
      hW0nonneg, ?_, hD'ne, hDmem, hD'mem⟩
    · intro e
      by_cases he : e ∈ W.honest
      · rw [show interiorInstance.covariance e = Sigma0 e by
          exact hagree e he]
        exact hSigma0pd e
      · exact houtside e he
    · intro e he
      rw [show interiorInstance.covariance e = Sigma0 e by exact hagree e he]
      exact hW0model e he

end

end CausalSmith.ExactID.RobustBackshiftUniformDistance
