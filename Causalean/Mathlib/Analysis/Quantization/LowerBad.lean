module
public import Causalean.Mathlib.Analysis.Quantization.LowerLocal

/-! The mass of source points far from at least one reproduction point is
controlled by paired distortion, uniformly over arbitrary measurable cells. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

/-- The bad region of a cell contains points at distance at least `δ` from
one of that cell's reproduction points. -/
def badRegion (S k : ℕ) (δ : ℝ) (B : Fin k → Set ℝ)
    (z : Fin k → Fin S → ℝ) (j : Fin k) : Set ℝ :=
  B j ∩ {x | ∃ s : Fin S, δ ≤ |x - z j s|}

/-- The bad region of each measurable cell is measurable, even when the cell
is disconnected. -/
theorem badRegion_measurable (S k : ℕ) (δ : ℝ) (B : Fin k → Set ℝ)
    (z : Fin k → Fin S → ℝ) (hB : ∀ j, MeasurableSet (B j)) :
    ∀ j, MeasurableSet (badRegion S k δ B z j) := by
  intro j
  unfold badRegion
  measurability

/-- On [a nondegenerate interval](hyp:a,b,hab), a [nonempty weight
family](hyp:S,hS), [continuous positive weights](hyp:β,hcont,hpos),
and [a positive-cell feasible partition](hyp:k,hk,B,z,hB,hz),
together with [coefficient bounds](hyp:c,hc,hlower) and
[diagonal-mass bounds](hyp:Q,δ,hQ,hδ,hupper),
give [a distortion bound for the total bad-region square-root mass](goal). -/
theorem bad_region_sqrt_mass_cost (a b : ℝ) (hab : a < b)
    (S k : ℕ) (hS : 0 < S) (hk : 0 < k)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z)
    (B : Fin k → Set ℝ) (z : Fin k → Fin S → ℝ)
    (hB : IsMeasurablePartition a b k B)
    (hz : ∀ j s, z j s ∈ Set.Icc a b)
    (c Q δ : ℝ) (hc : 0 < c) (hQ : 0 ≤ Q) (hδ : 0 < δ)
    (hlower : ∀ s x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → c ≤ β s x y)
    (hupper : ∀ x ∈ Set.Icc a b, Real.sqrt (diagonalWeight S β x) ≤ Q) :
    c * δ * (∑ j : Fin k,
      ∫ x in badRegion S k δ B z j, Real.sqrt (diagonalWeight S β x)) ≤
        Q * weightedCost S k β B z := by
  -- Apply far_region_measure_cost to each bad region. Integrate the
  -- pointwise square-root bound there and sum over cells.
  have hsub (j : Fin k) : B j ⊆ Set.Icc a b := by
    intro x hx
    rw [← hB.2.2]
    exact Set.mem_iUnion.mpr ⟨j, hx⟩
  have hroot := (sqrt_mass_regular a b hab S hS β hcont hpos).1
  have hcell (j : Fin k) :
      c * δ * (∫ x in badRegion S k δ B z j,
        Real.sqrt (diagonalWeight S β x)) ≤
        Q * (∑ s : Fin S, ∫ x in B j, β s x (z j s) * |x - z j s|) := by
    let G := badRegion S k δ B z j
    have hG : MeasurableSet G := badRegion_measurable S k δ B z hB.1 j
    have hGB : G ⊆ B j := fun x hx => hx.1
    have hGsub : G ⊆ Set.Icc a b := hGB.trans (hsub j)
    have hGfin : volume G ≠ ⊤ :=
      (measure_lt_top_of_subset hGsub (measure_Icc_lt_top (μ := volume)).ne).ne
    have hInt : IntegrableOn (fun x => Real.sqrt (diagonalWeight S β x)) G volume :=
      (hroot.integrableOn_compact isCompact_Icc).mono_set hGsub
    have hmass : (∫ x in G, Real.sqrt (diagonalWeight S β x)) ≤
        Q * volume.real G := by
      calc
        (∫ x in G, Real.sqrt (diagonalWeight S β x)) ≤ ∫ _x in G, Q := by
          apply setIntegral_mono_on hInt (integrableOn_const hGfin) hG
          intro x hx
          exact hupper x (hGsub hx)
        _ = Q * volume.real G := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
    have hIntCost (s : Fin S) : IntegrableOn
        (fun x => β s x (z j s) * |x - z j s|) (B j) volume :=
      weighted_cell_integrable a b hab.le (β s) (hcont s)
        (B j) (hB.1 j) (hsub j) (z j s) (hz j s)
    have hcost := far_region_measure_cost a b hab.le S β (z j)
      (B j) G (hB.1 j) hG (hsub j) hGB c δ hc.le hδ.le
      (by intro x hx s; exact hlower s x (z j s) (hGsub hx) (hz j s))
      (by intro x hx s; exact (hlower s x (z j s) (hsub j hx) (hz j s)).trans' hc.le)
      (by intro x hx; exact hx.2) hIntCost
    calc
      c * δ * (∫ x in G, Real.sqrt (diagonalWeight S β x)) ≤
          c * δ * (Q * volume.real G) :=
        mul_le_mul_of_nonneg_left hmass (mul_nonneg hc.le hδ.le)
      _ = Q * (c * δ * volume.real G) := by ring
      _ ≤ Q * (∑ s : Fin S, ∫ x in B j, β s x (z j s) * |x - z j s|) :=
        mul_le_mul_of_nonneg_left hcost hQ
  calc
    c * δ * (∑ j : Fin k, ∫ x in badRegion S k δ B z j,
      Real.sqrt (diagonalWeight S β x)) =
        ∑ j : Fin k, c * δ * (∫ x in badRegion S k δ B z j,
          Real.sqrt (diagonalWeight S β x)) := by rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin k, Q * (∑ s : Fin S,
        ∫ x in B j, β s x (z j s) * |x - z j s|) :=
      Finset.sum_le_sum (fun j _ => hcell j)
    _ = Q * weightedCost S k β B z := by
      simp only [weightedCost, Finset.mul_sum]

/-- Among candidates whose scaled cost is bounded by a fixed constant, the
total square-root mass of points far from at least one reproduction point
vanishes uniformly as the number of cells grows. -/
theorem bad_region_mass_small_of_scaled_cost_bound (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z)
    (δ M ε : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < k →
      ∀ (B : Fin k → Set ℝ) (z : Fin k → Fin S → ℝ),
        IsMeasurablePartition a b k B →
        (∀ j s, z j s ∈ Set.Icc a b) →
        (k : ℝ) * weightedCost S k β B z ≤ M →
        ∑ j : Fin k,
          ∫ x in badRegion S k δ B z j,
            Real.sqrt (diagonalWeight S β x) ≤ ε := by
  -- Compact extrema give c>0 and Q≥0 for bad_region_sqrt_mass_cost.
  -- Choose K > Q*M/(c*δ*ε), then multiply the distortion bound by k.
  obtain ⟨c, _C, hc, hcoeff⟩ :=
    coefficient_bounds a b hab S hS β hcont hpos
  have hroot := (sqrt_mass_regular a b hab S hS β hcont hpos).1
  obtain ⟨q, hq, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn
      (s := Set.Icc a b) ⟨a, le_refl a, hab.le⟩ hroot
  let Q : ℝ := Real.sqrt (diagonalWeight S β q)
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hupper : ∀ x ∈ Set.Icc a b,
      Real.sqrt (diagonalWeight S β x) ≤ Q := by
    intro x hx
    exact hmax hx
  have hden : 0 < c * δ * ε := mul_pos (mul_pos hc hδ) hε
  obtain ⟨K, hK⟩ := exists_nat_gt (Q * M / (c * δ * ε))
  refine ⟨K, ?_⟩
  intro k hkK hk B z hB hz hcost
  let bad : ℝ := ∑ j : Fin k,
    ∫ x in badRegion S k δ B z j,
      Real.sqrt (diagonalWeight S β x)
  have hbad : c * δ * bad ≤ Q * weightedCost S k β B z := by
    exact bad_region_sqrt_mass_cost a b hab S k hS hk β hcont hpos
      B z hB hz c Q δ hc hQ hδ
      (by intro s x y hx hy; exact (hcoeff s x hx y hy).1)
      hupper
  have hmul : (k : ℝ) * (c * δ * bad) ≤ Q * M := by
    calc
      (k : ℝ) * (c * δ * bad) ≤
          (k : ℝ) * (Q * weightedCost S k β B z) :=
        mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg k)
      _ = Q * ((k : ℝ) * weightedCost S k β B z) := by ring
      _ ≤ Q * M := mul_le_mul_of_nonneg_left hcost hQ
  have hkR : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkK
  have hthreshold : Q * M < (k : ℝ) * (c * δ * ε) := by
    exact (div_lt_iff₀ hden).mp (lt_of_lt_of_le hK hkR)
  by_contra hnot
  have hgt : ε < bad := lt_of_not_ge hnot
  have hkd : 0 < (k : ℝ) * (c * δ) :=
    mul_pos (Nat.cast_pos.mpr hk) (mul_pos hc hδ)
  have hstrict : (k : ℝ) * (c * δ * ε) <
      (k : ℝ) * (c * δ * bad) := by
    nlinarith [mul_lt_mul_of_pos_left hgt hkd]
  linarith

end Causalean.Mathlib.Analysis.Quantization
