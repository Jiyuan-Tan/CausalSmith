module
public import Causalean.Mathlib.Analysis.Quantization.Companding
public import Causalean.Mathlib.Analysis.Quantization.LowerAggregate
public import Mathlib.Algebra.Order.Chebyshev

/-! Uniform high-rate lower bounds over all finite measurable partitions,
including disconnected cells and separate reproduction points. -/

public section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

/-- In any measurable partition of `[a,b]` into `k` cells, the sum of squared
cell masses is at least the squared interval length divided by `k`. -/
theorem measurable_partition_mass_square_lower (a b : ℝ) (hab : a ≤ b)
    (k : ℕ) (B : Fin k → Set ℝ)
    (hB : IsMeasurablePartition a b k B) :
    (b - a) ^ 2 ≤ (k : ℝ) * ∑ j : Fin k, (volume.real (B j)) ^ 2 := by
  -- Add the masses of the disjoint cells, then apply finite Cauchy-Schwarz
  -- to their sum. Each cell has finite measure because it lies in Icc a b.
  have hsub (j : Fin k) : B j ⊆ Set.Icc a b := by
    intro x hx
    rw [← hB.2.2]
    exact Set.mem_iUnion.2 ⟨j, hx⟩
  have hfin (j : Fin k) : volume (B j) ≠ ⊤ :=
    (measure_lt_top_of_subset (hsub j) (measure_Icc_lt_top (μ := volume)).ne).ne
  have hsum : ∑ j : Fin k, volume.real (B j) = b - a := by
    rw [← measureReal_iUnion_fintype (fun i j hij => hB.2.1 i j hij) hB.1 hfin,
      hB.2.2, Real.volume_real_Icc_of_le hab]
  rw [← hsum]
  simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun j : Fin k => volume.real (B j)))

/-- For constant nonnegative coefficients, every measurable partition and
separate reproduction array obey the exact quarter-square lower bound. -/
theorem constant_weights_partition_lower (a b : ℝ) (hab : a ≤ b)
    (S k : ℕ) (γ : Fin S → ℝ)
    (hγ : ∀ s, 0 ≤ γ s) (B : Fin k → Set ℝ)
    (z : Fin k → Fin S → ℝ)
    (hB : IsMeasurablePartition a b k B) :
    (∑ s : Fin S, γ s) * (b - a) ^ 2 / 4 ≤
      (k : ℝ) * weightedCost S k (fun s _ _ => γ s) B z := by
  -- Sum weighted_measurable_cell_moment over cells and combine with
  -- measurable_partition_mass_square_lower. No interval-cell assumption.
  have hsub (j : Fin k) : B j ⊆ Set.Icc a b := by
    intro x hx
    rw [← hB.2.2]
    exact Set.mem_iUnion.2 ⟨j, hx⟩
  have hmass := measurable_partition_mass_square_lower a b hab k B hB
  have hγsum : 0 ≤ ∑ s : Fin S, γ s :=
    Finset.sum_nonneg (fun s _ => hγ s)
  have hkreal : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  calc
    (∑ s : Fin S, γ s) * (b - a) ^ 2 / 4 ≤
        (∑ s : Fin S, γ s) * ((k : ℝ) *
          ∑ j : Fin k, (volume.real (B j)) ^ 2) / 4 := by
      gcongr
    _ = (k : ℝ) * ∑ j : Fin k,
        ((∑ s : Fin S, γ s) * (volume.real (B j)) ^ 2 / 4) := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
      ring
    _ ≤ (k : ℝ) * ∑ j : Fin k,
        ∑ s : Fin S, γ s * (∫ x in B j, |x - z j s|) := by
      apply mul_le_mul_of_nonneg_left _ hkreal
      apply Finset.sum_le_sum
      intro j hj
      exact weighted_measurable_cell_moment a b hab (B j) (hB.1 j)
        (hsub j) S γ hγ (z j)
    _ = (k : ℝ) * weightedCost S k (fun s _ _ => γ s) B z := by
      simp only [weightedCost, integral_const_mul]

/-- On [a nondegenerate interval from a to b](hyp:a,b,hab), for [a nonempty finite
weight family](hyp:S,hS) with [continuous strictly positive weights](hyp:β,hcont,hpos),
[for every positive tolerance ε there is a cell count K such that, for every k ≥ K, every
measurable partition of the interval into k cells and every array of reproduction points in the
interval, k times the paired weighted cost is at least one quarter of the square of the integral
of the square root of the diagonal weight, minus ε](goal). -/
theorem arbitrary_partition_lower_eventually (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < k →
      ∀ (B : Fin k → Set ℝ) (z : Fin k → Fin S → ℝ),
        IsMeasurablePartition a b k B →
        (∀ j s, z j s ∈ Set.Icc a b) →
        (1 / 4 : ℝ) *
            (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) ^ 2 - ε ≤
          (k : ℝ) * weightedCost S k β B z := by
  -- Let A = (∫ sqrt w)^2/4. For fixed ε, choose η∈(0,1) so that
  -- (1-η)*A is close to A, and obtain δ from partition_good_mass_lower.
  -- Candidates with k*cost greater than A satisfy the goal directly.
  -- For the others, bad_region_mass_small_of_scaled_cost_bound makes the
  -- removed square-root mass uniformly small for large k. Positivity of
  -- ∫ sqrt w and the bad-mass integrals then converts the aggregate
  -- quarter-square estimate into A-ε ≤ k*cost.
  intro ε hε
  let I : ℝ := ∫ x in a..b, Real.sqrt (diagonalWeight S β x)
  let A : ℝ := I ^ 2 / 4
  have hI : 0 < I := (sqrt_mass_regular a b hab S hS β hcont hpos).2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let η : ℝ := ε / (ε + I ^ 2 + 1)
  have hηden : 0 < ε + I ^ 2 + 1 := by positivity
  have hη : 0 < η := div_pos hε hηden
  have hη1 : η < 1 := by
    apply (div_lt_iff₀ hηden).2
    nlinarith [sq_nonneg I]
  have hηbound : η * I ^ 2 ≤ ε := by
    have hsq : I ^ 2 ≤ ε + I ^ 2 + 1 := by linarith
    calc
      η * I ^ 2 ≤ η * (ε + I ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left hsq hη.le
      _ = ε := by dsimp [η]; field_simp
  let t : ℝ := ε / (ε + I + 1)
  have htden : 0 < ε + I + 1 := by positivity
  have ht : 0 < t := div_pos hε htden
  have htbound : I * t ≤ ε := by
    have hle : I ≤ ε + I + 1 := by linarith
    calc
      I * t ≤ (ε + I + 1) * t :=
        mul_le_mul_of_nonneg_right hle ht.le
      _ = ε := by dsimp [t]; field_simp
  obtain ⟨δ, hδ, hagg⟩ :=
    partition_good_mass_lower a b hab S hS β hcont hpos η hη hη1
  obtain ⟨K, hK⟩ :=
    bad_region_mass_small_of_scaled_cost_bound a b hab S hS β hcont hpos
      δ A t hδ ht
  refine ⟨K, ?_⟩
  intro k hkK hk B z hB hz
  let bad : ℝ := ∑ j : Fin k,
    ∫ x in badRegion S k δ B z j,
      Real.sqrt (diagonalWeight S β x)
  by_cases hlarge : A ≤ (k : ℝ) * weightedCost S k β B z
  · dsimp [A, I] at hlarge ⊢
    linarith
  have hcost : (k : ℝ) * weightedCost S k β B z ≤ A :=
    le_of_lt (lt_of_not_ge hlarge)
  have hbad : bad ≤ t := hK k hkK hk B z hB hz hcost
  have hbadnonneg : 0 ≤ bad := by
    dsimp [bad]
    apply Finset.sum_nonneg
    intro j hj
    exact integral_nonneg (fun x => Real.sqrt_nonneg _)
  have hIbad : I * bad ≤ ε :=
    (mul_le_mul_of_nonneg_left hbad hI.le).trans htbound
  have hagg' : (1 - η) * (I - bad) ^ 2 / 4 ≤
      (k : ℝ) * weightedCost S k β B z := by
    simpa only [I, bad] using hagg k hk B z hB hz
  have hsq : 0 ≤ (1 - η) * bad ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hη1.le) (sq_nonneg bad)
  have hcross : 0 ≤ η * I * bad :=
    mul_nonneg (mul_nonneg hη.le hI.le) hbadnonneg
  have hgoal : A - ε ≤ (k : ℝ) * weightedCost S k β B z := by
    dsimp [A]
    nlinarith
  convert hgoal using 1 <;> dsimp [A, I] <;> ring

/-- The same universal lower bound holds for the optimal value, since the
feasible cost set is nonempty and all its members obey the uniform estimate. -/
theorem optimal_lower_eventually (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < k →
      (1 / 4 : ℝ) *
          (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) ^ 2 - ε ≤
        (k : ℝ) * optimalCost a b S k β := by
  -- Use arbitrary_partition_lower_eventually and le_csInf; the feasible
  -- companding code witnesses nonemptiness of the cost set.
  intro ε hε
  obtain ⟨K, hK⟩ :=
    arbitrary_partition_lower_eventually a b hab S hS β hcont hpos ε hε
  refine ⟨K, ?_⟩
  intro k hkK hk
  have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hfeas := companding_feasible a b hab S k hS hk β hcont hpos
  have hne : {v : ℝ | ∃ (B : Fin k → Set ℝ) (z : Fin k → Fin S → ℝ),
      IsMeasurablePartition a b k B ∧
      (∀ j s, z j s ∈ Set.Icc a b) ∧
      v = weightedCost S k β B z}.Nonempty := by
    exact ⟨weightedCost S k β (compandingCell a b S k β)
      (compandingMidpoint a b S k β),
      compandingCell a b S k β, compandingMidpoint a b S k β,
      hfeas.1, hfeas.2, rfl⟩
  let A : ℝ := (1 / 4 : ℝ) *
    (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) ^ 2
  have hlim : (A - ε) / (k : ℝ) ≤ optimalCost a b S k β := by
    unfold optimalCost
    apply le_csInf hne
    rintro v ⟨B, z, hB, hz, rfl⟩
    apply (div_le_iff₀ hkreal).2
    simpa only [mul_comm] using hK k hkK hk B z hB hz
  calc
    A - ε = (k : ℝ) * ((A - ε) / (k : ℝ)) := by
      field_simp
    _ ≤ (k : ℝ) * optimalCost a b S k β :=
      mul_le_mul_of_nonneg_left hlim hkreal.le

end Causalean.Mathlib.Analysis.Quantization
