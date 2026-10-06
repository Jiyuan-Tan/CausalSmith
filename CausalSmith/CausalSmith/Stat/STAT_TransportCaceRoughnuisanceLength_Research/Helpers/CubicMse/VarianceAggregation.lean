module
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Finite conditional second-moment aggregation

This module supplies the finite-family Cauchy--Schwarz step used to assemble
the nonempty residual subsets in the quadratic and cubic statistics.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Adding an integrable quantity measurable with respect to the conditioning
sigma algebra does not change conditional centering.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,hm,f,g,hf,hg,hgm), [the stated conclusion holds](goal). -/
lemma sub_condExp_add_stronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hgm : StronglyMeasurable[m] g) :
    (fun x => (f x + g x) - condExp m μ (f + g) x) =ᵐ[μ]
      (fun x => f x - condExp m μ f x) := by
  have hadd := condExp_add hf hg m
  have hfix := condExp_of_stronglyMeasurable hm hgm hg
  rw [hfix] at hadd
  filter_upwards [hadd] with x hadd
  simp only [Pi.add_apply] at hadd
  rw [hadd]
  ring

/-- A uniform conditional second-moment bound for a finite family controls
the conditional second moment of its sum with the square of the family size.
No independence between different family members is required.  Under [the displayed assumptions and inputs](hyp:Ω,m,s,Y,B,hY,hb), [the stated conclusion holds](goal). -/
lemma condExp_sq_finsetSum_le
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : MeasurableSpace Ω} (s : Finset ι) (Y : ι → Ω → ℝ) (B : ℝ)
    (hY : ∀ i ∈ s, MemLp (Y i) 2 μ)
    (hb : ∀ i ∈ s, ∀ᵐ x ∂μ,
      condExp m μ (fun y => (Y i y) ^ 2) x ≤ B) :
    ∀ᵐ x ∂μ,
      condExp m μ (fun y => (∑ i ∈ s, Y i y) ^ 2) x ≤
        (s.card : ℝ) ^ 2 * B := by
  have hYsq : ∀ i ∈ s, Integrable (fun x => (Y i x) ^ 2) μ :=
    fun i hi => (hY i hi).integrable_sq
  let Q : Ω → ℝ := (s.card : ℝ) • (fun y => ∑ i ∈ s, (Y i y) ^ 2)
  have hsumSq : Integrable (fun y => ∑ i ∈ s, (Y i y) ^ 2) μ :=
    integrable_finsetSum s hYsq
  have hQ : Integrable Q μ := hsumSq.const_mul _
  have hsumLp : MemLp (fun y => ∑ i ∈ s, Y i y) 2 μ :=
    memLp_finsetSum s hY
  have hleft : Integrable (fun y => (∑ i ∈ s, Y i y) ^ 2) μ :=
    hsumLp.integrable_sq
  have hmono := condExp_mono hleft hQ (by
    filter_upwards [] with y
    exact sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => Y i y)) (m := m)
  have hsum := condExp_finsetSum (μ := μ) (s := s)
    (f := fun i y => (Y i y) ^ 2) hYsq m
  have hscale := condExp_smul (μ := μ) (s.card : ℝ)
    (fun y => ∑ i ∈ s, (Y i y) ^ 2) m
  have hall : ∀ᵐ x ∂μ, ∀ i ∈ s,
      condExp m μ (fun y => (Y i y) ^ 2) x ≤ B := by
    exact (eventually_finset_ball).2 hb
  filter_upwards [hmono, hsum, hscale, hall] with x hmono hsum hscale hall
  change condExp m μ Q x = _ at hscale
  simp only [Pi.smul_apply, smul_eq_mul] at hscale
  have hsum' : condExp m μ (fun y => ∑ i ∈ s, (Y i y) ^ 2) x =
      ∑ i ∈ s, condExp m μ (fun y => (Y i y) ^ 2) x := by
    simpa only [Finset.sum_fn, Finset.sum_apply] using hsum
  rw [hscale, hsum'] at hmono
  have hsumle : (∑ i ∈ s, condExp m μ (fun y => (Y i y) ^ 2) x) ≤
      ∑ _i ∈ s, B := Finset.sum_le_sum fun i hi => hall i hi
  calc
    condExp m μ (fun y => (∑ i ∈ s, Y i y) ^ 2) x ≤
        (s.card : ℝ) * ∑ i ∈ s, condExp m μ (fun y => (Y i y) ^ 2) x := hmono
    _ ≤ (s.card : ℝ) * ∑ _i ∈ s, B :=
      mul_le_mul_of_nonneg_left hsumle (Nat.cast_nonneg _)
    _ = (s.card : ℝ) ^ 2 * B := by
      simp [pow_two]
      ring

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
