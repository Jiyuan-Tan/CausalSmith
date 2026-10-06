module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TNoUniformNoisyIncompleteSharpness
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.NoisyRecovery
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.RateBounds

/-! Exact target sets under a declared nonzero-coordinate support margin. -/

public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: thm:separated-noisy-incomplete-target-sets
theorem separated_noisy_incomplete_target_sets :
    (∀ (p M : ℕ) (Ω : Type) (ms : MeasurableSpace Ω)
      (μ : Measure Ω),
      letI : MeasurableSpace Ω := ms
      ∀ (𝔐 : AtomicCountModel p M Ω μ)
        (dhat : Fin M → Fin p → ℝ) (ε β : ℝ),
        0 < ε → 2 * ε < β → β ≤ supportMargin (obsShift μ 𝔐) →
        (∀ m i, |dhat m i - obsShift μ 𝔐 m i| ≤ ε) →
        ∃ r : ProjectiveReduction (obsShift μ 𝔐),
          recoveredCompatible dhat β ∧
          (∀ m,
            recoveredSupport dhat β m =
              Finset.univ.filter (fun i => obsShift μ 𝔐 m i ≠ 0)) ∧
          (∀ m m',
            recoveredSupport dhat β m = recoveredSupport dhat β m' ↔
              ProjSim (obsShift μ 𝔐) m m') ∧
          (∀ m,
            (↑(noisyIncompleteHandle dhat ε β m) : Set (Fin p)) =
              targetSet r.v (r.κ m)) ∧
          (costedNoisyIncompleteHandle dhat ε β).1 =
            noisyIncompleteHandle dhat ε β ∧
          (costedNoisyIncompleteHandle dhat ε β).2 ≤
            10 * (M * M * p + r.q *
              (p + r.q + ∑ g : Fin r.q, (support r.v g).card)) ∧
          (∀ m, noisyIncompleteDelay dhat ε β m ≤
            11 * (M * M * p + r.q *
              (p + r.q + ∑ g : Fin r.q, (support r.v g).card)))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (ℓ v δ : ℝ), 0 < ℓ → ℓ ≤ Real.exp (1 / 2) →
        0 < v → (hδpos : 0 < δ) → (hδlt : δ < 1 / 2) →
        (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
          ∀ (p n : ℕ), 2 ≤ p → 0 < n →
            c₁ * Real.sqrt (Real.log p / n) ≤
              epsN C p n v ℓ δ ∧
            epsN C p n v ℓ δ ≤
              c₂ * Real.sqrt (Real.log p / n)) ∧
        ∀ (p n : ℕ), 0 < p → 0 < n →
          (n : ℝ) ≥ C * max 1 (v * ℓ⁻¹ ^ 4) *
            Real.log (4 * p * (p + 1) / δ) →
          ∀ (Ω : Type) (ms : MeasurableSpace Ω)
            (μ : Measure Ω),
            letI : MeasurableSpace Ω := ms
            ∀ (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
              (Ω' : Type) (ms' : MeasurableSpace Ω')
              (μ' : Measure Ω'),
              letI : MeasurableSpace Ω' := ms'
              ∀ (𝔐 : AtomicCountModel p p Ω' μ') (β : ℝ),
                μ Set.univ = 1 →
                β ≤ supportMargin (obsShift μ' 𝔐) →
                2 * epsN C p n v ℓ δ < β →
                (∀ e r,
                  μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
                    obsLaw μ' 𝔐 e) →
                ∃ r : ProjectiveReduction (obsShift μ' 𝔐),
                  μ {ω | ∀ m,
                    (↑(noisyIncompleteHandle
                      (robustShiftEstimator ℓ ⟨δ, hδpos, hδlt⟩
                        (fun e r => 𝒬.S e r ω)
                        (fun e r => 𝒬.X e r ω))
                      (epsN C p n v ℓ δ) β m) : Set (Fin p)) =
                        targetSet r.v (r.κ m)} ≥ ENNReal.ofReal (1 - δ)) ∧
    (∀ (p : ℕ) [NeZero p] (h : ℝ)
      (d : Fin p → Fin p → ℝ),
      4 ≤ p → 0 < h → h ≤ 1 →
      (∀ m, m ≠ 1 → d m = Pi.single 0 1) →
      (∃ j : Fin p, j ≠ 0 ∧
        d 1 = (fun i => (Pi.single 0 (1 : ℝ) : Fin p → ℝ) i +
          h * (Pi.single j (1 : ℝ) : Fin p → ℝ) i)) →
      supportMargin d = h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p M Ω ms μ
    letI : MeasurableSpace Ω := ms
    intro 𝔐 dhat ε β hε hβ hmargin happrox
    have hM : 0 < M := 𝔐.M_pos
    have hnonzero : ∀ m, obsShift μ 𝔐 m ≠ 0 :=
      ((compatibility_completion 𝔐.p_pos).1 M Ω ms μ 𝔐).2
    let r := projectiveReduction (obsShift μ 𝔐) hnonzero
    have hcompat : (assignmentFiber r.v).Nonempty :=
      model_projectiveReduction_assignment_nonempty μ 𝔐 r
    let K := M * M * p + r.q *
      (p + r.q + ∑ g : Fin r.q, (support r.v g).card)
    have hcost : (costedNoisyIncompleteHandle dhat ε β).2 ≤ 10 * K := by
      classical
      let T : Finset (Finset (Fin p)) :=
        Finset.univ.image (recoveredSupport dhat β)
      let G := {s : Finset (Fin p) // s ∈ T}
      let S : G → Finset (Fin p) := Subtype.val
      obtain ⟨e, he⟩ := recoveredGroupEquiv
        (obsShift μ 𝔐) dhat r hcompat ε β hε hβ hmargin happrox
      have hcard : Fintype.card G = r.q := by
        simpa [G, T] using (Fintype.card_congr e).symm
      have hsum : (∑ g : G, (S g).card) =
          ∑ g : Fin r.q, (support r.v g).card := by
        symm
        exact Fintype.sum_equiv e _ _
          (fun g => congrArg Finset.card (he g).symm)
      let I := ∑ g : G, (S g).card
      have hI : I ≤ Fintype.card G * p := by
        calc
          I ≤ ∑ _g : G, p := by
            apply Finset.sum_le_sum
            intro g _
            simpa using Finset.card_le_card (Finset.subset_univ (S g))
          _ = Fintype.card G * p := by simp
      have hbase := incidencePeelRun_budget_le S none
      have hinit := incidencePeelInit_budget_le S none
      have hbasecost : (incidencePeelRun S none).cost ≤
          p + 6 * Fintype.card G + 9 * I := by
        have hle : (incidencePeelRun S none).cost ≤
            incidencePeelBudget S (incidencePeelRun S none) := by
          unfold incidencePeelBudget
          omega
        change incidencePeelBudget S (incidencePeelInit S none) ≤
          p + 5 * Fintype.card G + 9 * I at hinit
        omega
      have hfrozen : (∑ g : G, (costedFrozenPeeling S g).2) ≤
          Fintype.card G * (p + 6 * Fintype.card G + 10 * I) + I := by
        calc
          (∑ g : G, (costedFrozenPeeling S g).2) ≤
              ∑ g : G, (p + 6 * Fintype.card G + 10 * I + (S g).card) := by
                apply Finset.sum_le_sum
                intro g _
                exact costedFrozenPeeling_cost_le_refined S g
          _ = Fintype.card G * (p + 6 * Fintype.card G + 10 * I) + I := by
                simp [I, Finset.sum_add_distrib]
      have hqM : r.q ≤ M := by
        simpa using Fintype.card_le_of_surjective r.κ r.κ_surj
      have hp : 0 < p := 𝔐.p_pos
      have htotal : (costedNoisyIncompleteHandle dhat ε β).2 =
          M * M * p + (incidencePeelRun S none).cost +
            ∑ g : G, (costedFrozenPeeling S g).2 := by
        unfold costedNoisyIncompleteHandle
        dsimp only
        split_ifs <;> rfl
      rw [htotal]
      rw [hcard] at hI hbasecost hfrozen
      have hIeq : I = ∑ g : Fin r.q, (support r.v g).card := hsum
      rw [hIeq] at hI hbasecost hfrozen
      dsimp [K]
      have hM1 : 1 ≤ M := hM
      have hp1 : 1 ≤ p := hp
      have hP : p ≤ M * M * p := by
        calc
          p = 1 * 1 * p := by omega
          _ ≤ M * M * p := Nat.mul_le_mul_right p
            (Nat.mul_le_mul hM1 hM1)
      have hQP : r.q * p ≤ M * M * p := by
        have hsq : r.q ≤ M * M := by
          calc
            r.q ≤ M := hqM
            _ = M * 1 := by omega
            _ ≤ M * M := Nat.mul_le_mul_left M hM1
        exact Nat.mul_le_mul_right p hsq
      have hQ : r.q ≤ M * M * p := by
        have hsmall : r.q ≤ r.q * p := by
          simpa using Nat.mul_le_mul_left r.q hp1
        omega
      have hbig :
          p + 6 * r.q + 10 * (∑ g : Fin r.q, (support r.v g).card) ≤
            9 * (M * M * p) + 9 * (r.q * p) + 4 * (r.q * r.q) := by
        omega
      nlinarith [hbig]
    refine ⟨r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact recoveredCompatible_of_margin _ _ r hcompat ε β
        hε hβ hmargin happrox
    · intro m
      exact recoveredSupport_eq_of_margin _ _ ε β hε hβ
        hmargin happrox m
    · intro m m'
      exact recovered_support_eq_iff_proj _ _ r hcompat ε β
        hε hβ hmargin happrox m m'
    · intro m
      exact noisyIncompleteHandle_eq_targetSet _ _ r hcompat ε β
        hε hβ hmargin happrox m
    · exact costedNoisyIncompleteHandle_eq_of_margin
        (obsShift μ 𝔐) dhat r hcompat ε β hε hβ hmargin happrox
    · exact hcost
    · intro m
      have hM : 0 < M := Nat.pos_of_ne_zero (by
        intro h
        subst M
        exact Fin.elim0 m)
      have hK : 0 < K := by
        dsimp [K]
        have hprod : 0 < M * M * p :=
          Nat.mul_pos (Nat.mul_pos hM hM) 𝔐.p_pos
        omega
      unfold noisyIncompleteDelay
      split_ifs <;> omega
  · obtain ⟨C, hC, hcertificate⟩ := bounded_moment_certificate
    refine ⟨C, hC, ?_⟩
    intro ℓ v δ hℓ hℓupper hv hδpos hδlt
    refine ⟨epsN_bounds C ℓ v δ hC hℓ hv hδpos hδlt, ?_⟩
    intro p n hp hn hsample Ω ms μ
    letI : MeasurableSpace Ω := ms
    intro 𝒬 Ω' ms' μ'
    letI : MeasurableSpace Ω' := ms'
    intro 𝔐 β hprob hmargin hβ hLaw
    let r₀ : Fin n := ⟨0, hn⟩
    have hcert := hcertificate p n ℓ v δ hp hn hℓ hℓupper hv
      hδpos hδlt hsample Ω ms μ 𝒬 r₀ hprob
    have hε : 0 < epsN C p n v ℓ δ := hcert.2.1
    have hnonzero : ∀ m, obsShift μ' 𝔐 m ≠ 0 :=
      ((compatibility_completion 𝔐.p_pos).1 p Ω' ms' μ' 𝔐).2
    let r := projectiveReduction (obsShift μ' 𝔐) hnonzero
    have hcompat : (assignmentFiber r.v).Nonempty :=
      model_projectiveReduction_assignment_nonempty μ' 𝔐 r
    refine ⟨r, ?_⟩
    apply le_trans hcert.1
    apply MeasureTheory.measure_mono
    intro ω hω
    intro m
    have happrox : ∀ m i,
        |robustShiftEstimator ℓ ⟨δ, hδpos, hδlt⟩
            (fun e r => 𝒬.S e r ω) (fun e r => 𝒬.X e r ω) m i -
          obsShift μ' 𝔐 m i| ≤ epsN C p n v ℓ δ := by
      intro m' i
      rw [← balancedObsShift_eq_obsShift_of_law μ μ' 𝒬 𝔐 r₀ hLaw m' i]
      exact hω m' i
    exact noisyIncompleteHandle_eq_targetSet _ _ r hcompat
      (epsN C p n v ℓ δ) β hε hβ hmargin happrox m
  · intro p _ h d hp hh hh1 hbase halt
    exact duplicateAlternative_supportMargin p h d hp hh hh1 hbase halt

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
