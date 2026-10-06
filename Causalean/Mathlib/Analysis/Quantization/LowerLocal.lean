module
public import Causalean.Mathlib.Analysis.Quantization.LowerGeometry
public import Causalean.Mathlib.Analysis.Quantization.Moment

/-! Local integral estimates for the universal lower bound. They apply to
arbitrary measurable subsets of a cell, without connectedness assumptions. -/

public section

open MeasureTheory Set
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

/-- A continuous weighted absolute-distance integrand is integrable on every
measurable subset of the compact source interval when its reproduction point
also lies in that interval. -/
theorem weighted_cell_integrable (a b : ℝ) (hab : a ≤ b)
    (β : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => β p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (B : Set ℝ) (hB : MeasurableSet B) (hsub : B ⊆ Set.Icc a b)
    (z : ℝ) (hz : z ∈ Set.Icc a b) :
    IntegrableOn (fun x => β x z * |x - z|) B volume := by
  have hpair : ContinuousOn (fun x : ℝ => (x, z)) (Set.Icc a b) := by
    fun_prop
  have hβ' : ContinuousOn (fun x : ℝ => β x z) (Set.Icc a b) :=
    hcont.comp hpair (fun x hx => ⟨hx, hz⟩)
  have hdist : ContinuousOn (fun x : ℝ => |x - z|) (Set.Icc a b) := by
    fun_prop
  exact (hβ'.mul hdist).integrableOn_compact isCompact_Icc |>.mono_set hsub

/-- If all points in a measurable region are at least `δ` from one of the
reproduction points, its paired cost is at least its volume times `c*δ`,
provided every coefficient there is at least `c`. -/
theorem far_region_measure_cost (a b : ℝ) (hab : a ≤ b)
    (S : ℕ) (β : Fin S → ℝ → ℝ → ℝ) (z : Fin S → ℝ)
    (B G : Set ℝ) (hB : MeasurableSet B) (hG : MeasurableSet G)
    (hsub : B ⊆ Set.Icc a b) (hGB : G ⊆ B)
    (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hβ : ∀ x ∈ G, ∀ s, c ≤ β s x (z s))
    (hβnonneg : ∀ x ∈ B, ∀ s, 0 ≤ β s x (z s))
    (hfar : ∀ x ∈ G, ∃ s, δ ≤ |x - z s|)
    (hInt : ∀ s, IntegrableOn (fun x => β s x (z s) * |x - z s|) B volume) :
    c * δ * volume.real G ≤
      ∑ s : Fin S, ∫ x in B, β s x (z s) * |x - z s| := by
  -- Integrate far_point_cost_lower on G. Finite measure follows from
  -- G ⊆ B ⊆ Icc a b. Compare each nonnegative integrand on G and B,
  -- then exchange the finite sum and the integral.
  have hGsub : G ⊆ Set.Icc a b := hGB.trans hsub
  have hGfin : volume G ≠ ⊤ :=
    (measure_lt_top_of_subset hGsub (measure_Icc_lt_top (μ := volume)).ne).ne
  have hsumInt : IntegrableOn
      (fun x => ∑ s : Fin S, β s x (z s) * |x - z s|) G volume := by
    apply integrable_finsetSum
    intro s hs
    exact (hInt s).mono_set hGB
  have hpoint : ∀ x ∈ G,
      c * δ ≤ ∑ s : Fin S, β s x (z s) * |x - z s| := by
    intro x hx
    exact far_point_cost_lower S β z x c δ hc hδ (hβ x hx) (hfar x hx)
  calc
    c * δ * volume.real G = ∫ _x in G, c * δ := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ x in G, ∑ s : Fin S, β s x (z s) * |x - z s| := by
      exact setIntegral_mono_on (integrableOn_const hGfin) hsumInt hG hpoint
    _ = ∑ s : Fin S, ∫ x in G, β s x (z s) * |x - z s| := by
      exact integral_finsetSum Finset.univ (fun s _ => (hInt s).mono_set hGB)
    _ ≤ ∑ s : Fin S, ∫ x in B, β s x (z s) * |x - z s| := by
      apply Finset.sum_le_sum
      intro s hs
      apply setIntegral_mono_set (hInt s)
      · filter_upwards [ae_restrict_mem hB] with x hx
        exact mul_nonneg (hβnonneg x hx s) (abs_nonneg _)
      · exact hGB.eventuallyLE

/-- For [ordered interval endpoints](hyp:a,b,hab), [a finite weight
family and its weights](hyp:S,β), [reproductions](hyp:z), [measurable source
and target regions](hyp:B,G,hB,hG,hsub,hGB), and [nonnegative lower
weights](hyp:γ,hγ) with [comparison and integrability bounds](hyp:hβ,hβnonneg,hInt),
[the exact quarter-square lower bound holds for the paired cell cost](goal). -/
theorem near_region_moment_lower (a b : ℝ) (hab : a ≤ b)
    (S : ℕ) (β : Fin S → ℝ → ℝ → ℝ) (z : Fin S → ℝ)
    (B G : Set ℝ) (hB : MeasurableSet B) (hG : MeasurableSet G)
    (hsub : B ⊆ Set.Icc a b) (hGB : G ⊆ B)
    (γ : Fin S → ℝ) (hγ : ∀ s, 0 ≤ γ s)
    (hβ : ∀ x ∈ G, ∀ s, γ s ≤ β s x (z s))
    (hβnonneg : ∀ x ∈ B, ∀ s, 0 ≤ β s x (z s))
    (hInt : ∀ s, IntegrableOn (fun x => β s x (z s) * |x - z s|) B volume) :
    (∑ s : Fin S, γ s) * volume.real G ^ 2 / 4 ≤
      ∑ s : Fin S, ∫ x in B, β s x (z s) * |x - z s| := by
  -- Apply weighted_measurable_cell_moment to G. On G compare the
  -- constant-weight integrands with the actual ones; nonnegativity on
  -- B permits enlargement of the integration domain from G to B.
  have hGsub : G ⊆ Set.Icc a b := hGB.trans hsub
  have hdistInt (s : Fin S) : IntegrableOn (fun x => |x - z s|) G volume := by
    have hcont : Continuous (fun x : ℝ => |x - z s|) := by fun_prop
    exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set hGsub
  have hbound (s : Fin S) :
      γ s * (∫ x in G, |x - z s|) ≤
        ∫ x in B, β s x (z s) * |x - z s| := by
    rw [← integral_const_mul]
    calc
      (∫ x in G, γ s * |x - z s|) ≤
          ∫ x in G, β s x (z s) * |x - z s| := by
        apply setIntegral_mono_on ((hdistInt s).const_mul (γ s))
          ((hInt s).mono_set hGB) hG
        intro x hx
        exact mul_le_mul_of_nonneg_right (hβ x hx s) (abs_nonneg _)
      _ ≤ ∫ x in B, β s x (z s) * |x - z s| := by
        apply setIntegral_mono_set (hInt s)
        · filter_upwards [ae_restrict_mem hB] with x hx
          exact mul_nonneg (hβnonneg x hx s) (abs_nonneg _)
        · exact hGB.eventuallyLE
  exact (weighted_measurable_cell_moment a b hab G hG hGsub S γ hγ z).trans
    (Finset.sum_le_sum (fun s _ => hbound s))

end Causalean.Mathlib.Analysis.Quantization
