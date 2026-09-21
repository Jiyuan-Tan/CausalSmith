module
public import CausalSmith.Substrate.Archive.FiniteSideInformationMinimaxConvergence.Coordinates
public import Causalean.Stat.Concentration.TailBounds.Hoeffding
public import Causalean.Stat.Sample.PiTransport
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite-category empirical concentration

This module defines empirical atom frequencies and proves a uniform L1 tail
bound from coordinatewise Hoeffding inequalities and a finite union bound.
-/

@[expose] public section

open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory

namespace CausalSmith.Substrate.FiniteSideInformationMinimaxConvergence

variable (C : Type*) [Fintype C] [DecidableEq C]

/-- Given a [positive sample size](hyp:hm), an [ordered finite sample](hyp:z), and an
[atom](hyp:c), the [empirical atom frequency](goal) is its sample count divided by the sample
size. -/
noncomputable def empiricalFrequency {m : ℕ} (hm : 0 < m) (z : Fin m → C) (c : C) : ℝ :=
  (∑ i, if z i = c then (1 : ℝ) else 0) / m

/-- Given a [positive sample size](hyp:hm), a [sample](hyp:z), and a [side law](hyp:w), the
[empirical L1 error](goal) is the sum of the absolute atom-frequency errors. -/
noncomputable def empiricalL1 {m : ℕ} (hm : 0 < m) (z : Fin m → C) (w : FinitePmf C) : ℝ :=
  ∑ c, |empiricalFrequency C hm z c - w.1 c|

/-- Every [empirical atom frequency](hyp:hm,z,c) is [nonnegative](goal). -/
theorem empiricalFrequency_nonneg {m : ℕ} (hm : 0 < m) (z : Fin m → C) (c : C) :
    0 ≤ empiricalFrequency C hm z c := by
  unfold empiricalFrequency
  exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity) (Nat.cast_nonneg _)

/-- Over a [finite nonempty alphabet](hyp:C), the [empirical atom frequencies of a positive
sample](hyp:hm,z) [sum to one](goal). -/
theorem sum_empiricalFrequency [Nonempty C] {m : ℕ} (hm : 0 < m) (z : Fin m → C) :
    ∑ c, empiricalFrequency C hm z c = 1 := by
  unfold empiricalFrequency
  rw [← Finset.sum_div, Finset.sum_comm]
  simp [Finset.sum_ite_eq, Nat.ne_of_gt hm]

/-- A [positive finite sample](hyp:hm,z) determines the [probability-simplex point](goal)
whose coordinates are its empirical atom frequencies. -/
noncomputable def empiricalPmf [Nonempty C] {m : ℕ} (hm : 0 < m)
    (z : Fin m → C) : FinitePmf C :=
  ⟨empiricalFrequency C hm z,
    ⟨empiricalFrequency_nonneg C hm z, sum_empiricalFrequency C hm z⟩⟩

/-- Every [atom coordinate](hyp:c) of the [empirical probability vector](hyp:hm,z)
is its empirical frequency. -/
@[simp]
theorem empiricalPmf_apply [Nonempty C] {m : ℕ} (hm : 0 < m)
    (z : Fin m → C) (c : C) :
    (empiricalPmf C hm z).1 c = empiricalFrequency C hm z c :=
  rfl

/-- For a [finite nonempty alphabet](hyp:C), a [positive sample](hyp:hm,z), and a
[probability vector](hyp:w), the [distance from the empirical simplex point to the vector
is at most their coordinatewise L1 error](goal). -/
theorem dist_empiricalPmf_le_empiricalL1 [Nonempty C] {m : ℕ} (hm : 0 < m)
    (z : Fin m → C) (w : FinitePmf C) :
    dist (empiricalPmf C hm z) w ≤ empiricalL1 C hm z w := by
  change dist (empiricalFrequency C hm z) w.1 ≤
    ∑ c, |empiricalFrequency C hm z c - w.1 c|
  rw [dist_pi_le_iff']
  intro c
  rw [Real.dist_eq]
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun c ↦ |empiricalFrequency C hm z c - w.1 c|)
    (fun c _ ↦ abs_nonneg _) (Finset.mem_univ c)

private theorem exists_large_empirical_coordinate [Nonempty C] {m : ℕ} (hm : 0 < m)
    (z : Fin m → C) (w : FinitePmf C) {ε : ℝ}
    (h : ε ≤ empiricalL1 C hm z w) :
    ∃ c, ε / Fintype.card C ≤ |empiricalFrequency C hm z c - w.1 c| := by
  by_contra hn
  push Not at hn
  have hs : (∑ c, |empiricalFrequency C hm z c - w.1 c|) <
      ∑ _c : C, ε / (Fintype.card C : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun c _ ↦ hn c)
  have hcard : (Fintype.card C : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hlt : empiricalL1 C hm z w < ε := by
    rw [empiricalL1]
    calc
      (∑ c, |empiricalFrequency C hm z c - w.1 c|) <
          ∑ _c : C, ε / (Fintype.card C : ℝ) := hs
      _ = ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  exact (not_lt_of_ge h) hlt

private theorem measureReal_iUnion_fintype_le {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ] (A : ι → Set Ω) :
    μ.real (⋃ i, A i) ≤ ∑ i, μ.real (A i) := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_sum (s := Finset.univ)
    (fun i _ ↦ measure_ne_top μ (A i))]
  exact ENNReal.toReal_mono (by simp [measure_ne_top])
    (measure_iUnion_fintype_le μ A)

/-- For a [finite nonempty alphabet](hyp:C), a [probability vector](hyp:w), a [positive sample
size](hyp:hm), and a [positive tolerance](hyp:hε), the [total product probability of samples
whose empirical L1 error is at least the tolerance](goal) is at most the finite-union
Hoeffding bound `2 |C| exp (-2 m (ε/|C|)^2)`. -/
theorem empiricalL1_tail [Nonempty C] {m : ℕ} (hm : 0 < m) (w : FinitePmf C)
    {ε : ℝ} (hε : 0 < ε) :
    (∑ z : Fin m → C,
      if ε ≤ empiricalL1 C hm z w then productProbability C w z else 0)
      ≤ 2 * Fintype.card C * Real.exp (-2 * m * (ε / Fintype.card C) ^ 2) := by
  open Causalean.Stat in
    letI : MeasurableSpace C := ⊤
    have hw : ∑ c, ENNReal.ofReal (w.1 c) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg
          (fun c _ ↦ FinitePmf.nonneg C w c),
        FinitePmf.sum_eq_one C w]
      norm_num
    let p : PMF C := PMF.ofFintype (fun c ↦ ENNReal.ofReal (w.1 c)) hw
    let P : Measure C := p.toMeasure
    haveI : IsProbabilityMeasure P := inferInstance
    have hP (c : C) : P.real {c} = w.1 c := by
      change ENNReal.toReal (p.toMeasure {c}) = w.1 c
      rw [PMF.toMeasure_apply_fintype]
      simp [p, FinitePmf.nonneg C w c]
    have hint (c : C) :
        (∫ x, (if x = c then (1 : ℝ) else 0) ∂P) = w.1 c := by
      rw [show (fun x ↦ if x = c then (1 : ℝ) else 0) =
        Set.indicator {c} (1 : C → ℝ) by
          funext x
          by_cases h : x = c <;> simp [h]]
      rw [MeasureTheory.integral_indicator_one (measurableSet_singleton c)]
      exact hP c
    let S := iidSample_infinitePi P
    let μ : Measure (ℕ → C) := Measure.infinitePi (fun _ : ℕ ↦ P)
    let Φ : (ℕ → C) → (Fin m → C) := fun ω i ↦ ω i
    have hmean (c : C) (ω : ℕ → C) :
        S.sampleMean (fun x ↦ if x = c then (1 : ℝ) else 0) m ω =
          empiricalFrequency C hm (Φ ω) c := by
      rw [IIDSample.sampleMean, empiricalFrequency,
        Fin.sum_univ_eq_sum_range (fun i ↦ if ω i = c then (1 : ℝ) else 0) m]
      simp only [S, Φ, iidSample_infinitePi]
      ring
    let A : C → Set (ℕ → C) := fun c ↦
      {ω | ε / Fintype.card C ≤
        |empiricalFrequency C hm (Φ ω) c - w.1 c|}
    have hcoord (c : C) :
        μ.real (A c) ≤ 2 * Real.exp (-2 * m * (ε / Fintype.card C) ^ 2) := by
      have hb : ∀ᵐ x ∂P, (if x = c then (1 : ℝ) else 0) ∈ Set.Icc 0 1 := by
        filter_upwards with x
        by_cases hx : x = c <;> simp [hx]
      have hh := Causalean.Stat.Concentration.hoeffding_abs_ge S
        (f := fun x ↦ if x = c then (1 : ℝ) else 0)
        (by fun_prop) (a := 0) (b := 1) zero_lt_one hb m hm
        (div_nonneg (le_of_lt hε)
          (by positivity : (0 : ℝ) ≤ Fintype.card C))
      rw [hint c] at hh
      simpa only [μ, hmean, sub_zero, one_pow, div_one, A] using hh
    let B : Set (ℕ → C) := {ω | ε ≤ empiricalL1 C hm (Φ ω) w}
    have hsub : B ⊆ ⋃ c, A c := by
      intro ω hω
      rcases exists_large_empirical_coordinate C hm (Φ ω) w hω with ⟨c, hc⟩
      exact Set.mem_iUnion.2 ⟨c, hc⟩
    have hB : μ.real B ≤
        2 * Fintype.card C * Real.exp (-2 * m * (ε / Fintype.card C) ^ 2) := by
      calc
        μ.real B ≤ μ.real (⋃ c, A c) := measureReal_mono hsub
        _ ≤ ∑ c, μ.real (A c) := measureReal_iUnion_fintype_le μ A
        _ ≤ ∑ _c : C, 2 * Real.exp
            (-2 * m * (ε / Fintype.card C) ^ 2) :=
          Finset.sum_le_sum fun c _ ↦ hcoord c
        _ = 2 * Fintype.card C * Real.exp
            (-2 * m * (ε / Fintype.card C) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
    let E : Finset (Fin m → C) :=
      Finset.univ.filter (fun z ↦ ε ≤ empiricalL1 C hm z w)
    have hmap : μ.map Φ = Measure.pi (fun _ : Fin m ↦ P) := by
      simpa only [μ, Φ, S, iidSample_infinitePi] using iidSample_finN_pushforward S m
    have hBE : B = Φ ⁻¹' (E : Set (Fin m → C)) := by
      ext ω
      simp only [B, E, Φ, Set.mem_ofPred_eq, Set.mem_preimage, Finset.mem_coe,
        Finset.mem_filter, Finset.mem_univ, true_and]
    have htransport :
        μ.real B = (Measure.pi (fun _ : Fin m ↦ P)).real (E : Set (Fin m → C)) := by
      simp only [Measure.real]
      congr 1
      rw [hBE, ← Measure.map_apply (by fun_prop) (by measurability), hmap]
    have hsingleton (z : Fin m → C) :
        (Measure.pi (fun _ : Fin m ↦ P)).real {z} = productProbability C w z := by
      simp only [Measure.real, Measure.pi_singleton]
      rw [ENNReal.toReal_prod]
      change (∏ i, P.real {z i}) = _
      simp_rw [hP]
      rfl
    have hsumE :
        (∑ z : Fin m → C,
          if ε ≤ empiricalL1 C hm z w then productProbability C w z else 0) =
        (Measure.pi (fun _ : Fin m ↦ P)).real (E : Set (Fin m → C)) := by
      rw [← Finset.sum_filter]
      calc
        ∑ z ∈ E, productProbability C w z =
            ∑ z ∈ E, (Measure.pi (fun _ : Fin m ↦ P)).real {z} := by
          apply Finset.sum_congr rfl
          intro z _
          exact (hsingleton z).symm
        _ = (Measure.pi (fun _ : Fin m ↦ P)).real (E : Set (Fin m → C)) :=
          MeasureTheory.sum_measureReal_singleton E
    rw [hsumE, ← htransport]
    exact hB

/-- For every [positive tolerance](hyp:hε), the [uniform finite-category empirical L1 tail
bound](goal) tends to zero as the sample size tends to infinity. -/
theorem empiricalL1_tail_bound_tendsto_zero [Nonempty C] {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m : ℕ ↦
      2 * Fintype.card C * Real.exp (-2 * m * (ε / Fintype.card C) ^ 2))
      Filter.atTop (nhds 0) := by
  have hcard : (0 : ℝ) < Fintype.card C := by
    exact_mod_cast Fintype.card_pos
  have ha : 0 < 2 * (ε / (Fintype.card C : ℝ)) ^ 2 := by positivity
  have harg : Tendsto (fun m : ℕ ↦ (m : ℝ) *
      (2 * (ε / (Fintype.card C : ℝ)) ^ 2)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const ha
  have hexp : Tendsto (fun m : ℕ ↦ Real.exp
      (-((m : ℝ) * (2 * (ε / (Fintype.card C : ℝ)) ^ 2)))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp harg
  have hmul := hexp.const_mul (2 * (Fintype.card C : ℝ))
  convert hmul using 1
  · funext m
    congr 2
    ring
  · simp

end CausalSmith.Substrate.FiniteSideInformationMinimaxConvergence
