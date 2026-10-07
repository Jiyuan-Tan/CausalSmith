module
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.LaplaceRate
public import Causalean.Stat.Sample.PiTransport

/-!
# Uniform usable-occupancy controls

These estimates concern only the finite observed design law on cell-arm pairs.
The constants are chosen before the cell alphabet, its masses, and sample size.
The finite-product transport lemma moves them to any measurable observed law.
-/

public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

open MeasureTheory Causalean.Stat

/-- Applying the measured cell and arm labels to every iid observation gives iid
draws from the observed cell-arm marginal. -/
theorem iid_design_marginal {Ω κ : Type} [MeasurableSpace Ω]
    [MeasurableSpace κ] (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (hX : Measurable X) (hA : Measurable A) :
    (Measure.pi (fun _ : Fin n => μ)).map
      (fun z : Fin n → Ω => fun i => (X (z i), A (z i))) =
    Measure.pi (fun _ : Fin n => μ.map (fun ω => (X ω, A ω))) := by
  exact Causalean.Stat.map_pi_finCoordinatewise n μ (hX.prodMk hA)

/-- The fixed-size Laplace transform of usable occupancy has a birthday-scale
bound for every finite measurable cell alphabet, including null cells. The
constant depends only on occupied-cell overlap.

Proof route: relabel the finite cell type by `Fintype.equivFin`, push the
observed pair law and iid product through this equivalence, and apply
`fixed_design_laplace_le_poisson` and `poissonized_design_laplace_rate`.
All singleton sets are measurable by `MeasurableSingletonClass`; an arbitrary
subset of this finite type is therefore measurable. Check explicitly that
arm-cell and cell masses, guarded counts, and zero totals survive relabeling. -/
theorem fixed_design_laplace_rate (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_half : epsilon < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
        [MeasurableSpace κ] [MeasurableSingletonClass κ]
        (ν : Measure (κ × Bool)) [IsProbabilityMeasure ν]
        (n : ℕ), 0 < n →
        (∀ a k,
          0 < cellMass ν (fun z : κ × Bool => z.1) k →
          epsilon * cellMass ν (fun z : κ × Bool => z.1) k ≤
            armCellMass ν (fun z => z.1) (fun z => z.2) a k) →
        (∫ z : Fin n → κ × Bool,
          Real.exp (-(usableTotal (fun v : κ × Bool => v.1)
            (fun v => v.2) z : ℝ))
          ∂Measure.pi (fun _ : Fin n => ν)) ≤
          2 * Real.exp (-(c * (n : ℝ) ^ 2 /
            max (n : ℝ) (Fintype.card κ : ℝ))) := by
  classical
  obtain ⟨c, hc, hrate⟩ :=
    poissonized_design_laplace_rate epsilon hepsilon hepsilon_half
  refine ⟨c, hc, ?_⟩
  intro κ _ _ _ _ ν _ n hn hoverlap
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let em : κ ≃ᵐ Fin (Fintype.card κ) :=
    MeasurableEquiv.mk e (measurable_of_countable _) (measurable_of_countable _)
  let ep : (κ × Bool) ≃ᵐ (Fin (Fintype.card κ) × Bool) :=
    em.prodCongr (MeasurableEquiv.refl Bool)
  let ν' : Measure (Fin (Fintype.card κ) × Bool) := ν.map ep
  have : IsProbabilityMeasure ν' := Measure.isProbabilityMeasure_map ep.measurable.aemeasurable
  have hcell (k : κ) :
      cellMass ν' (fun v : Fin (Fintype.card κ) × Bool => v.1) (e k) =
        cellMass ν (fun v : κ × Bool => v.1) k := by
    unfold cellMass ν'
    rw [Measure.map_apply ep.measurable (Set.Finite.measurableSet (Set.toFinite _))]
    congr 1
    apply congrArg ν
    ext v
    change e v.1 = e k ↔ v.1 = k
    exact e.injective.eq_iff
  have harm (a : Bool) (k : κ) :
      armCellMass ν' (fun v : Fin (Fintype.card κ) × Bool => v.1)
        (fun v => v.2) a (e k) =
        armCellMass ν (fun v : κ × Bool => v.1) (fun v => v.2) a k := by
    unfold armCellMass ν'
    rw [Measure.map_apply ep.measurable (Set.Finite.measurableSet (Set.toFinite _))]
    congr 1
    apply congrArg ν
    ext v
    change e v.1 = e k ∧ v.2 = a ↔ v.1 = k ∧ v.2 = a
    simp only [e.injective.eq_iff]
  have hoverlap' : ∀ a k,
      0 < cellMass ν' (fun v : Fin (Fintype.card κ) × Bool => v.1) k →
      epsilon * cellMass ν' (fun v => v.1) k ≤
        armCellMass ν' (fun v => v.1) (fun v => v.2) a k := by
    intro a k hk
    obtain ⟨j, rfl⟩ := e.surjective k
    rw [hcell, harm]
    exact hoverlap a j (hcell j ▸ hk)
  have hcount (z : Fin n → κ × Bool) (a : Bool) (k : κ) :
      groupArmCount (fun v : Fin (Fintype.card κ) × Bool => v.1) (fun v => v.2)
        (fun i => ep (z i)) a (e k) =
      groupArmCount (fun v : κ × Bool => v.1) (fun v => v.2) z a k := by
    unfold groupArmCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change e (z i).1 = e k ∧ (z i).2 = a ↔ (z i).1 = k ∧ (z i).2 = a
    simp only [e.injective.eq_iff]
  have htotal (z : Fin n → κ × Bool) :
      usableTotal (fun v : Fin (Fintype.card κ) × Bool => v.1)
        (fun v => v.2) (fun i => ep (z i)) =
      usableTotal (fun v : κ × Bool => v.1) (fun v => v.2) z := by
    unfold usableTotal usableGroupTotal
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro k _
    simp only [usableGroup, groupCount, hcount]
    by_cases h : 0 < groupArmCount (fun v : κ × Bool => v.1) (fun v => v.2) z false k ∧
        0 < groupArmCount (fun v : κ × Bool => v.1) (fun v => v.2) z true k
    · simp [h]
    · simp [h]
  have hpi := Causalean.Stat.map_pi_finCoordinatewise n ν ep.measurable
  have htransport :
      (∫ z : Fin n → Fin (Fintype.card κ) × Bool,
        Real.exp (-(usableTotal (fun v : Fin (Fintype.card κ) × Bool => v.1)
          (fun v => v.2) z : ℝ)) ∂Measure.pi (fun _ : Fin n => ν')) =
      (∫ z : Fin n → κ × Bool,
        Real.exp (-(usableTotal (fun v : κ × Bool => v.1)
          (fun v => v.2) z : ℝ)) ∂Measure.pi (fun _ : Fin n => ν)) := by
    rw [← hpi]
    let es : (Fin n → κ × Bool) ≃ᵐ
        (Fin n → Fin (Fintype.card κ) × Bool) :=
      MeasurableEquiv.piCongrRight (fun _ => ep)
    rw [show (fun z : Fin n → κ × Bool => fun i => ep (z i)) = es from rfl]
    rw [integral_map_equiv es]
    have hes (z : Fin n → κ × Bool) : es z = fun i => ep (z i) := rfl
    simp only [hes, htotal]
  rw [← htransport]
  exact (fixed_design_laplace_le_poisson ν').trans
    (mul_le_mul_of_nonneg_left (hrate _ ν' n hn hoverlap') (by norm_num))

/-- Under occupied-cell overlap, the probability of no matched cell is bounded
uniformly by a constant depending only on the overlap margin times
`1/n + card(κ)/n²`, including null cells and the zero-usable case.

Proof route: apply `fixed_design_laplace_rate`; the zero indicator is at most
the Laplace transform, and `exp(-t) ≤ 1/t` converts the birthday-scale
exponent to the stated rate. Use `integral_indicator_one` for the event
measure. The finite design sample space has a finite type, so the Laplace
kernel is integrable; `measurable_usableGroupTotal` makes the event measurable.
Apply `birthday_laplace_rate` to absorb the exponential constant. -/
theorem bad_occupancy_rate (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_half : epsilon < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
        [MeasurableSpace κ] [MeasurableSingletonClass κ]
        (ν : Measure (κ × Bool)) [IsProbabilityMeasure ν]
        (n : ℕ), 0 < n →
        (∀ a k,
          0 < cellMass ν (fun z : κ × Bool => z.1) k →
          epsilon * cellMass ν (fun z : κ × Bool => z.1) k ≤
            armCellMass ν (fun z => z.1) (fun z => z.2) a k) →
        ((Measure.pi (fun _ : Fin n => ν))
          {z | usableTotal (fun v : κ × Bool => v.1) (fun v => v.2) z = 0}).toReal ≤
          B * (1 / (n : ℝ) + (Fintype.card κ : ℝ) / (n : ℝ) ^ 2) := by
  classical
  obtain ⟨c, hc, hlap⟩ := fixed_design_laplace_rate epsilon hepsilon hepsilon_half
  obtain ⟨B, hB, hrate⟩ := birthday_laplace_rate c hc
  refine ⟨B, hB, ?_⟩
  intro κ _ _ _ _ ν _ n hn hoverlap
  let P : Measure (Fin n → κ × Bool) := Measure.pi (fun _ : Fin n => ν)
  let T (z : Fin n → κ × Bool) :=
    usableTotal (fun v : κ × Bool => v.1) (fun v => v.2) z
  let E : Set (Fin n → κ × Bool) := {z | T z = 0}
  have hE : MeasurableSet E := by
    exact measurableSet_eq_fun
      (measurable_usableGroupTotal (n := n) (fun v : κ × Bool => v.1)
        (fun v => v.2) measurable_fst measurable_snd) measurable_const
  have hmono : (∫ z, E.indicator (1 : (Fin n → κ × Bool) → ℝ) z ∂P) ≤
      ∫ z, Real.exp (-(T z : ℝ)) ∂P := by
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro z
    simpa [E, T, Set.indicator, Set.indicator_apply] using zero_indicator_le_exp (T z)
  have hprob : P.real E = ∫ z, E.indicator (1 : (Fin n → κ × Bool) → ℝ) z ∂P :=
    (integral_indicator_one hE).symm
  change P.real E ≤ _
  calc
    P.real E = ∫ z, E.indicator (1 : (Fin n → κ × Bool) → ℝ) z ∂P := hprob
    _ ≤ ∫ z, Real.exp (-(T z : ℝ)) ∂P := hmono
    _ ≤ 2 * Real.exp (-(c * (n : ℝ) ^ 2 /
        max (n : ℝ) (Fintype.card κ : ℝ))) := hlap κ ν n hn hoverlap
    _ ≤ B * (1 / (n : ℝ) + (Fintype.card κ : ℝ) / (n : ℝ) ^ 2) :=
      hrate n (Fintype.card κ) hn

/-- For an [overlap margin ε strictly between zero and one half](hyp:epsilon,hepsilon,hepsilon_half),
[there is a positive constant B, depending only on ε, such that the following
holds for every finite set of cells, every probability law on cell-arm pairs,
and every positive sample size n: if in each cell of positive mass both
arm-cell pairs have mass at least ε times the cell mass, then under n
independent draws the expectation of the reciprocal of the usable total (the
number of observations in cells containing both arms), with the reciprocal
read as zero when the usable total is zero, is at most B·(1/n + card(κ)/n²),
where card(κ) is the number of cells](goal).

Proof route: apply `fixed_design_laplace_rate`. For a positive threshold `t`,
the guarded reciprocal is pointwise at most `1/t + exp(t) * exp(-usableTotal)`;
take `t` as half the birthday-scale exponent and absorb the exponential by
`exp(-t) ≤ 1/t`. `guarded_inverse_le_exp` handles the zero denominator
without a separate positivity assumption. Integrate the pointwise bound,
use `integral_const` and `integral_const_mul`, then apply
`birthday_reciprocal_rate` to the resulting scalar bound. -/
theorem reciprocal_occupancy_rate (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_half : epsilon < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
        [MeasurableSpace κ] [MeasurableSingletonClass κ]
        (ν : Measure (κ × Bool)) [IsProbabilityMeasure ν]
        (n : ℕ), 0 < n →
        (∀ a k,
          0 < cellMass ν (fun z : κ × Bool => z.1) k →
          epsilon * cellMass ν (fun z : κ × Bool => z.1) k ≤
            armCellMass ν (fun z => z.1) (fun z => z.2) a k) →
        (∫ z : Fin n → κ × Bool,
          inverseUsableGroupTotal (fun v => v.1) (fun v => v.2) z
          ∂Measure.pi (fun _ : Fin n => ν)) ≤
          B * (1 / (n : ℝ) + (Fintype.card κ : ℝ) / (n : ℝ) ^ 2) := by
  classical
  obtain ⟨c, hc, hlap⟩ := fixed_design_laplace_rate epsilon hepsilon hepsilon_half
  obtain ⟨B, hB, hrate⟩ := birthday_reciprocal_rate c hc
  refine ⟨B, hB, ?_⟩
  intro κ _ _ _ _ ν _ n hn hoverlap
  let P : Measure (Fin n → κ × Bool) := Measure.pi (fun _ : Fin n => ν)
  let T (z : Fin n → κ × Bool) :=
    usableTotal (fun v : κ × Bool => v.1) (fun v => v.2) z
  let t : ℝ := c * (n : ℝ) ^ 2 /
    (2 * max (n : ℝ) (Fintype.card κ : ℝ))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hpoint (z : Fin n → κ × Bool) :
      inverseUsableGroupTotal (fun v : κ × Bool => v.1) (fun v => v.2) z ≤
        t⁻¹ + Real.exp t * Real.exp (-(T z : ℝ)) := by
    simpa [inverseUsableGroupTotal, T, usableTotal] using
      guarded_inverse_le_exp t ht (T z)
  have hmono :
      (∫ z, inverseUsableGroupTotal (fun v : κ × Bool => v.1)
        (fun v => v.2) z ∂P) ≤
      ∫ z, t⁻¹ + Real.exp t * Real.exp (-(T z : ℝ)) ∂P := by
    exact integral_mono Integrable.of_finite Integrable.of_finite hpoint
  have hP : IsProbabilityMeasure P := inferInstance
  have hint :
      (∫ z, t⁻¹ + Real.exp t * Real.exp (-(T z : ℝ)) ∂P) =
      t⁻¹ + Real.exp t * ∫ z, Real.exp (-(T z : ℝ)) ∂P := by
    rw [integral_add (integrable_const _) Integrable.of_finite]
    rw [integral_const_mul]
    simp
  have hbound :
      t⁻¹ + Real.exp t * (∫ z, Real.exp (-(T z : ℝ)) ∂P) ≤
      t⁻¹ + Real.exp t * (2 * Real.exp (-(c * (n : ℝ) ^ 2 /
        max (n : ℝ) (Fintype.card κ : ℝ)))) := by
    have hmul := mul_le_mul_of_nonneg_left (show
      (∫ z, Real.exp (-(T z : ℝ)) ∂P) ≤
        2 * Real.exp (-(c * (n : ℝ) ^ 2 /
          max (n : ℝ) (Fintype.card κ : ℝ))) from
      hlap κ ν n hn hoverlap) (Real.exp_nonneg t)
    linarith
  have hscalar :
      t⁻¹ + Real.exp t * (2 * Real.exp (-(c * (n : ℝ) ^ 2 /
        max (n : ℝ) (Fintype.card κ : ℝ)))) =
      2 * max (n : ℝ) (Fintype.card κ : ℝ) / (c * (n : ℝ) ^ 2) +
        2 * Real.exp (-(c * (n : ℝ) ^ 2 /
          (2 * max (n : ℝ) (Fintype.card κ : ℝ)))) := by
    have hM : 0 < max (n : ℝ) (Fintype.card κ : ℝ) :=
      lt_of_lt_of_le hnR (le_max_left _ _)
    have hnum : c * (n : ℝ) ^ 2 ≠ 0 := ne_of_gt (mul_pos hc (sq_pos_of_pos hnR))
    have hden : 2 * max (n : ℝ) (Fintype.card κ : ℝ) ≠ 0 := by positivity
    have hrec : t⁻¹ = 2 * max (n : ℝ) (Fintype.card κ : ℝ) /
        (c * (n : ℝ) ^ 2) := by
      dsimp [t]
      field_simp
    have harg : -(c * (n : ℝ) ^ 2 /
        max (n : ℝ) (Fintype.card κ : ℝ)) = -t + -t := by
      dsimp [t]
      ring
    rw [hrec, harg, Real.exp_add]
    congr 1
    calc
      Real.exp t * (2 * (Real.exp (-t) * Real.exp (-t))) =
          2 * (Real.exp t * Real.exp (-t)) * Real.exp (-t) := by ring
      _ = 2 * Real.exp (-t) := by rw [← Real.exp_add]; simp
      _ = 2 * Real.exp (-(c * (n : ℝ) ^ 2 /
          (2 * max (n : ℝ) (Fintype.card κ : ℝ)))) := rfl
  change (∫ z, inverseUsableGroupTotal (fun v : κ × Bool => v.1)
    (fun v => v.2) z ∂P) ≤ _
  calc
    _ ≤ ∫ z, t⁻¹ + Real.exp t * Real.exp (-(T z : ℝ)) ∂P := hmono
    _ = t⁻¹ + Real.exp t * ∫ z, Real.exp (-(T z : ℝ)) ∂P := hint
    _ ≤ t⁻¹ + Real.exp t * (2 * Real.exp (-(c * (n : ℝ) ^ 2 /
        max (n : ℝ) (Fintype.card κ : ℝ)))) := hbound
    _ = 2 * max (n : ℝ) (Fintype.card κ : ℝ) / (c * (n : ℝ) ^ 2) +
        2 * Real.exp (-(c * (n : ℝ) ^ 2 /
          (2 * max (n : ℝ) (Fintype.card κ : ℝ)))) := hscalar
    _ ≤ B * (1 / (n : ℝ) + (Fintype.card κ : ℝ) / (n : ℝ) ^ 2) :=
      hrate n (Fintype.card κ) hn

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk
