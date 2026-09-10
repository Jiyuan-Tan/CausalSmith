import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.GenericAffineOccupancy
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.TSharpReplacementRadius

/-!
# Uniform support-deletion radius

The ex-ante corruption budget certified by a full-environment binary support design.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open MeasureTheory Set

/-- Maximum generic pairwise occupancy of a full support design. -/
def fullDesignOccupancy {p m : ℕ} (Z : Environment m → Fin p → Bool) : ℕ :=
  (offDiagPairs p).sup fun kl ↦ genericOccupancy Finset.univ Z kl.1 kl.2

-- @node: maxLineOccupancy_mono_index
/-- Restricting the indexed cloud cannot increase its maximum affine-line occupancy. [Under the stated hypotheses](hyp:hIJ) [this conclusion](goal) applies. -/
lemma maxLineOccupancy_mono_index {ι : Type*} {p : ℕ}
    {I J : Finset ι} (hIJ : I ⊆ J) (s : ι → Fin p → ℝ)
    (k l : Fin p) :
    maxLineOccupancy I s k l ≤ maxLineOccupancy J s k l := by
  classical
  unfold maxLineOccupancy
  apply Finset.sup_le
  intro S hS
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  exact ⟨fun e he ↦ hIJ (hS.1 he), hS.2⟩

-- @node: prop:uniform-support-deletion-radius
/-- Almost surely, uniform robustness after every `c`-environment deletion is equivalent to the
full-design forced occupancy being below `m-2c`, with the exact integer budget formula and the
all-active specialization. [Under the stated hypotheses](hyp:hp,hm,hc) [this conclusion](goal) applies. -/
theorem uniform_support_deletion_radius {Ωsample : Type*} [MeasurableSpace Ωsample]
    (μ : Measure Ωsample) [IsProbabilityMeasure μ]
    {p m c : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) (hc : c < m)
    (Zbar : Environment m → Fin p → Bool)
    (abar : Ωsample → Environment m → Fin p → ℝ)
    (generic_active_amplitudes :
      GenericActiveAmplitudes (Finset.univ : Finset (Environment m)) Zbar μ abar) :
    ∀ᵐ ω ∂μ,
      let T := fullDesignOccupancy Zbar
      let uniformAfterDeletion :=
        ∀ F : Finset (Environment m), F.card = c →
          let H := Finset.univ \ F
          ∀ W : BackshiftSystem p m c,
            W.honest = H →
            SupportFactorization H Zbar (abar ω) W.shifts →
            BackshiftNormalization W → NonnegativeShifts W → HonestCovarianceModel W →
            W.invariantNoise.PosSemidef →
            compatibleSet p m c ⟨W.covariance, W.covariance_psd⟩ = {W.structural}
      (uniformAfterDeletion ↔ T < m - 2 * c) ∧
      (T < m → (T < m - 2 * c ↔ c ≤ (m - T - 1) / 2)) ∧
      (T = m → ¬ T < m - 2 * c) ∧
      ((∀ e k, Zbar e k = true) → 3 ≤ m →
        fullDesignOccupancy Zbar = 2) := by
  filter_upwards
    [generic_affine_occupancy hp (Finset.univ : Finset (Environment m))
      Zbar abar μ generic_active_amplitudes,
      genericActiveAmplitudes_ae_positive
        (Finset.univ : Finset (Environment m)) Zbar abar μ
          generic_active_amplitudes]
    with ω hoccupancy hpositive
  dsimp only
  let sbar : Environment m → Fin p → ℝ := fun e j ↦
    if Zbar e j then abar ω e j else 0
  have hsbar : ∀ e j, 0 ≤ sbar e j := by
    intro e j
    by_cases hZ : Zbar e j = true
    · exact le_of_lt (by
        simpa [sbar, hZ, activeProjection] using
          hpositive ⟨(e, j), Finset.mem_univ e, hZ⟩)
    · simp [sbar, hZ]
  have hfull (k l : Fin p) (hkl : k < l) :
      maxLineOccupancy (Finset.univ : Finset (Environment m)) sbar k l =
        genericOccupancy Finset.univ Zbar k l := by
    simpa [sbar] using hoccupancy k l hkl
  let k0 : Fin p := ⟨0, by omega⟩
  let k1 : Fin p := ⟨1, by omega⟩
  have hk01 : k0 < k1 := Fin.mk_lt_mk.mpr (by omega)
  have hpairs : (offDiagPairs p).Nonempty :=
    ⟨(k0, k1), by simp [offDiagPairs, hk01]⟩
  have hgeneric_le_full (k l : Fin p) (hkl : k < l) :
      genericOccupancy Finset.univ Zbar k l ≤ fullDesignOccupancy Zbar := by
    unfold fullDesignOccupancy
    exact Finset.le_sup
      (f := fun kl : Fin p × Fin p ↦
        genericOccupancy Finset.univ Zbar kl.1 kl.2)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (k, l), hkl⟩)
  have hW_of_threshold
      (hthreshold : fullDesignOccupancy Zbar < m - 2 * c)
      (F : Finset (Environment m)) (hF : F.card = c)
      (W : BackshiftSystem p m c) (hWH : W.honest = Finset.univ \ F)
      (hfactor : SupportFactorization (Finset.univ \ F) Zbar (abar ω) W.shifts)
      (hnorm : BackshiftNormalization W) (hnonneg : NonnegativeShifts W)
      (hmodel : HonestCovarianceModel W) (hpsd : W.invariantNoise.PosSemidef) :
      compatibleSet p m c ⟨W.covariance, W.covariance_psd⟩ = {W.structural} := by
    have hmasked : ∀ e ∈ W.honest, W.shifts e = sbar e := by
      intro e he
      funext j
      rw [hfactor.1 e (by simpa [hWH] using he) j]
    have hdelta : envDeletionDistance W.honest W.shifts > c :=
      (envDeletionDistance_gt_iff hp W.honest W.shifts c).2 (by
        intro k l hkl
        calc
          maxLineOccupancy W.honest W.shifts k l =
              maxLineOccupancy W.honest sbar k l :=
                maxLineOccupancy_congr_on W.honest W.shifts sbar hmasked k l
          _ ≤ maxLineOccupancy (Finset.univ : Finset (Environment m)) sbar k l :=
                maxLineOccupancy_mono_index (Finset.subset_univ _) sbar k l
          _ = genericOccupancy Finset.univ Zbar k l := hfull k l hkl
          _ ≤ fullDesignOccupancy Zbar := hgeneric_le_full k l hkl
          _ < m - 2 * c := hthreshold
          _ = W.honest.card - c := by
            simp only [W.honest_card, honestCount]
            omega)
    exact (sharp_replacement_radius W hnorm hnonneg hmodel hpsd).2.1 hdelta
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro huniform
      by_contra hnot
      have hTge : m - 2 * c ≤ fullDesignOccupancy Zbar := Nat.le_of_not_gt hnot
      obtain ⟨kl, hklmem, hklmax⟩ := Finset.sup_mem_of_nonempty
        (f := fun kl : Fin p × Fin p ↦
          genericOccupancy Finset.univ Zbar kl.1 kl.2) hpairs
      have hkl : kl.1 < kl.2 := (Finset.mem_filter.mp hklmem).2
      have hlineFull :
          maxLineOccupancy (Finset.univ : Finset (Environment m)) sbar kl.1 kl.2 =
            fullDesignOccupancy Zbar := by
        rw [hfull kl.1 kl.2 hkl]
        exact hklmax
      let lineFamilies :=
        ((Finset.univ : Finset (Environment m)).powerset.filter
          (CollinearPairs sbar kl.1 kl.2))
      have hlineFamilies : lineFamilies.Nonempty := by
        refine ⟨∅, ?_⟩
        simp [lineFamilies, CollinearPairs]
      obtain ⟨S, hSfam, hScard⟩ := Finset.sup_mem_of_nonempty
        (f := Finset.card) hlineFamilies
      have hScardT : S.card = fullDesignOccupancy Zbar := by
        rw [← hlineFull]
        exact hScard
      have hqS : m - 2 * c ≤ S.card := by omega
      obtain ⟨Q, hQS, hQcard⟩ := Finset.exists_subset_card_eq hqS
      have hqh : m - 2 * c ≤ honestCount m c := by
        simp only [honestCount]
        omega
      have hhcard : honestCount m c ≤ Fintype.card (Environment m) := by
        simp [honestCount]
      obtain ⟨H, hQH, hHcard⟩ :=
        Finset.exists_superset_card_eq (s := Q) (n := honestCount m c)
          (by simpa [hQcard] using hqh) hhcard
      let F : Finset (Environment m) := Finset.univ \ H
      have hHuniv : Finset.univ \ F = H := by simp [F]
      have hFcard : F.card = c := by
        calc
          F.card = m - H.card := by
            dsimp [F]
            rw [Finset.card_sdiff_of_subset (Finset.subset_univ H)]
            simp
          _ = c := by rw [hHcard]; simp only [honestCount]; omega
      let Sigma0 : Environment m → RealMatrix p := fun e ↦
        1 + Matrix.diagonal (sbar e)
      have hSigma0pd : ∀ e, (Sigma0 e).PosDef := by
        intro e
        exact Matrix.PosDef.one.add_posSemidef (Matrix.PosSemidef.diagonal (hsbar e))
      let W0 : BackshiftSystem p m c :=
        { dimension_at_least_two := hp
          environment_nonempty := hm
          corruption_lt := hc
          honest := H
          honest_card := hHcard
          covariance := Sigma0
          covariance_psd := fun e ↦ (hSigma0pd e).posSemidef
          structural := 1
          structural_invertible := by simp
          invariantNoise := 1
          invariantNoise_symmetric := by simp
          shifts := sbar }
      have hW0norm : BackshiftNormalization W0 := by
        dsimp [BackshiftNormalization, W0, admissibleSet]
        refine ⟨by simp, by simp, ?_⟩
        rw [sub_self]
        unfold cycleProduct
        have hz : simpleCycleWeight (0 : RealMatrix p) = fun _ ↦ 0 := by
          funext σ
          by_cases hσ : σ.IsCycle ∧ 2 ≤ σ.support.card
          · simp only [simpleCycleWeight, if_pos hσ]
            obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < σ.support.card)
            rw [Finset.prod_eq_zero hi]
            simp
          · simp [simpleCycleWeight, hσ]
        rw [hz]
        generalize (Finset.univ : Finset (Equiv.Perm (Fin p))) = R
        induction R using Finset.induction_on with
        | empty => simp
        | @insert σ R hσ ih => simp [Finset.fold_insert hσ, ih]
      have hW0nonneg : NonnegativeShifts W0 := by
        intro e he j
        exact hsbar e j
      have hW0model : HonestCovarianceModel W0 := by
        intro e he
        simp [W0, Sigma0]
      have hW0psd : W0.invariantNoise.PosSemidef := Matrix.PosDef.one.posSemidef
      have hdelta0 : envDeletionDistance W0.honest W0.shifts ≤ c := by
        apply Nat.le_of_not_gt
        intro hdelta
        have hocc := (envDeletionDistance_gt_iff hp W0.honest W0.shifts c).1
          hdelta kl.1 kl.2 hkl
        have hQcol : CollinearPairs sbar kl.1 kl.2 Q := by
          have hScol : CollinearPairs sbar kl.1 kl.2 S :=
            (Finset.mem_filter.mp hSfam).2
          intro e he f hf g hg
          exact hScol e (hQS he) f (hQS hf) g (hQS hg)
        have hQmem : Q ∈
            (W0.honest.powerset.filter (CollinearPairs W0.shifts kl.1 kl.2)) := by
          simp only [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hQH, hQcol⟩
        have hQle : Q.card ≤ maxLineOccupancy W0.honest W0.shifts kl.1 kl.2 := by
          unfold maxLineOccupancy
          exact Finset.le_sup hQmem
        simp only [W0, hHcard, honestCount, hQcard] at hocc hQle
        omega
      obtain ⟨Winterior, D', hIH, hIs, hIpd, hcovpd, hInorm, hInonneg,
          hImodel, hD'ne, hImem, hD'mem⟩ :=
        (sharp_replacement_radius W0 hW0norm hW0nonneg hW0model hW0psd).2.2.2
          hdelta0
      have hIfactor : SupportFactorization (Finset.univ \ F) Zbar (abar ω)
          Winterior.shifts := by
        rw [hHuniv, hIs]
        constructor
        · intro e he j
          simp [W0, sbar]
        · intro e he j hZ
          exact hpositive ⟨(e, j), Finset.mem_univ e, hZ⟩
      have hsingleton := huniform F hFcard Winterior (by simpa [hHuniv] using hIH)
        hIfactor hInorm hInonneg hImodel hIpd.posSemidef
      have hEq : D' = Winterior.structural := by
        have : D' ∈ ({Winterior.structural} : Set (RealMatrix p)) := by
          rwa [← hsingleton]
        simpa using this
      exact hD'ne hEq
    · exact hW_of_threshold
  · intro hTm
    omega
  · intro hTm
    omega
  · intro hall hm3
    have hgen : ∀ kl ∈ offDiagPairs p,
        genericOccupancy Finset.univ Zbar kl.1 kl.2 = 2 := by
      intro kl hkl
      have hmpos : 0 < m := by omega
      have hmin : min 2 m = 2 := by omega
      simp [genericOccupancy, incidenceCount, hall, hmpos, hmin]
    have hfullEq : fullDesignOccupancy Zbar = 2 := by
      unfold fullDesignOccupancy
      calc
        (offDiagPairs p).sup
            (fun kl ↦ genericOccupancy Finset.univ Zbar kl.1 kl.2) =
            (offDiagPairs p).sup (fun _ ↦ 2) :=
              Finset.sup_congr rfl hgen
        _ = 2 := Finset.sup_const hpairs 2
    exact hfullEq

end CausalSmith.ExactID.RobustBackshiftUniformDistance
