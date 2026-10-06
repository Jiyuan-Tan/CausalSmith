module
public import Causalean.Mathlib.Analysis.Quantization.LowerLocal

/-! Local square-root-mass estimates for arbitrary measurable parts of a
quantization cell. These estimates require no interval shape or connectedness. -/

public section

open MeasureTheory Set
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

/-- On a sufficiently small good part of a cell, every actual coefficient is
uniformly close to the diagonal coefficient at any anchor point in that part,
and the square-root diagonal density is uniformly close at the same two points.
The radius works for all reproduction arrays in the source interval. -/
theorem good_cell_uniform_freeze (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (x y : ℝ) (z : Fin S → ℝ),
        x ∈ Set.Icc a b → y ∈ Set.Icc a b →
        (∀ s, z s ∈ Set.Icc a b) →
        (∀ s, |x - z s| ≤ δ ∧ |y - z s| ≤ δ) →
        (∀ s, |β s x (z s) - β s y y| < ε) ∧
          |Real.sqrt (diagonalWeight S β x) -
            Real.sqrt (diagonalWeight S β y)| < ε := by
  -- Take a common radius from coefficient_uniform_continuity and the
  -- compact uniform continuity of sqrt_mass_regular. The good_cell_diameter
  -- estimate bounds |x-y| by twice the chosen radius; shrink it once more
  -- so both the product-metric and scalar distances are strictly inside
  -- their respective continuity radii.
  intro ε hε
  obtain ⟨δc, hδc, hc⟩ :=
    coefficient_uniform_continuity a b hab S β hcont ε hε
  have hu := (isCompact_Icc.uniformContinuousOn_of_continuous
    (sqrt_mass_regular a b hab S hS β hcont hpos).1)
  obtain ⟨δr, hδr, hr⟩ := (Metric.uniformContinuousOn_iff.mp hu) ε hε
  let δ : ℝ := min δc δr / 4
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hsmallc : 2 * δ < δc := by
    dsimp [δ]
    have := min_le_left δc δr
    linarith
  have hsmallr : 2 * δ < δr := by
    dsimp [δ]
    have := min_le_right δc δr
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro x y z hx hy hz hnear
  have hdiam : |x - y| ≤ 2 * δ :=
    good_cell_diameter S hS z x y δ (fun s => (hnear s).1)
      (fun s => (hnear s).2)
  constructor
  · intro s
    have hpair : dist (x, z s) (y, y) < δc := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      apply max_lt
      · exact hdiam.trans_lt hsmallc
      · have hzy : |z s - y| ≤ δ := by
          simpa only [abs_sub_comm] using (hnear s).2
        linarith
    exact hc s (x, z s) (y, y) ⟨hx, hz s⟩ ⟨hy, hy⟩ hpair
  · have hdist : dist x y < δr := by
      rw [Real.dist_eq]
      exact hdiam.trans_lt hsmallr
    simpa only [Real.dist_eq] using hr x hx y hy hdist

/-- A frozen nonnegative coefficient family controls the square of the
square-root diagonal mass on any measurable part of a cell, provided that
the diagonal square root is bounded there by a compatible constant. -/
theorem frozen_cell_sqrt_mass_lower (a b : ℝ) (hab : a ≤ b)
    (S : ℕ) (β : Fin S → ℝ → ℝ → ℝ)
    (B G : Set ℝ) (hB : MeasurableSet B) (hG : MeasurableSet G)
    (hsub : B ⊆ Set.Icc a b) (hGB : G ⊆ B)
    (z : Fin S → ℝ) (γ : Fin S → ℝ) (hγ : ∀ s, 0 ≤ γ s)
    (hβ : ∀ x ∈ G, ∀ s, γ s ≤ β s x (z s))
    (hβnonneg : ∀ x ∈ B, ∀ s, 0 ≤ β s x (z s))
    (hInt : ∀ s, IntegrableOn (fun x => β s x (z s) * |x - z s|) B volume)
    (Q η : ℝ) (hQ : 0 ≤ Q) (hη : 0 ≤ η ∧ η < 1)
    (hq : ∀ x ∈ G, Real.sqrt (diagonalWeight S β x) ≤ Q)
    (hcoeff : (1 - η) * Q ^ 2 ≤ ∑ s : Fin S, γ s) :
    (1 - η) * (∫ x in G, Real.sqrt (diagonalWeight S β x)) ^ 2 / 4 ≤
      ∑ s : Fin S, ∫ x in B, β s x (z s) * |x - z s| := by
  -- Bound the square-root integral by Q*volume.real G, square using
  -- nonnegativity, then apply near_region_moment_lower with γ.
  have hGsub : G ⊆ Set.Icc a b := hGB.trans hsub
  have hGfin : volume G < ⊤ :=
    lt_of_le_of_lt (measure_mono hGsub) (measure_Icc_lt_top (μ := volume))
  have hnorm :
      |∫ x in G, Real.sqrt (diagonalWeight S β x)| ≤ Q * volume.real G := by
    simpa only [Real.norm_eq_abs] using
      (norm_setIntegral_le_of_norm_le_const
        (f := fun x : ℝ => Real.sqrt (diagonalWeight S β x))
        (s := G) (μ := volume) (C := Q) hGfin (fun x hx => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hq x hx))
  have hvol : 0 ≤ Q * volume.real G :=
    mul_nonneg hQ ENNReal.toReal_nonneg
  have hsq :
      (∫ x in G, Real.sqrt (diagonalWeight S β x)) ^ 2 ≤
        (Q * volume.real G) ^ 2 := by
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hvol] using hnorm)
  calc
    (1 - η) * (∫ x in G, Real.sqrt (diagonalWeight S β x)) ^ 2 / 4
        ≤ (1 - η) * (Q * volume.real G) ^ 2 / 4 := by
          gcongr
          linarith [hη.2]
    _ = ((1 - η) * Q ^ 2) * volume.real G ^ 2 / 4 := by ring
    _ ≤ (∑ s : Fin S, γ s) * volume.real G ^ 2 / 4 := by
      gcongr
    _ ≤ ∑ s : Fin S, ∫ x in B, β s x (z s) * |x - z s| :=
      near_region_moment_lower a b hab S β z B G hB hG hsub hGB γ hγ hβ hβnonneg hInt

/-- A single anchor in a short cell supplies nonnegative frozen coefficients
and a common square-root-density bound for every nearby source point, with a
uniform relative margin between their squared bound and coefficient sum. -/
theorem good_cell_relative_freeze (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ δ : ℝ, 0 < δ ∧
      ∀ (y : ℝ) (z : Fin S → ℝ),
        y ∈ Set.Icc a b →
        (∀ s, z s ∈ Set.Icc a b) →
        (∀ s, |y - z s| ≤ δ) →
        ∃ (γ : Fin S → ℝ) (Q : ℝ),
          (∀ s, 0 ≤ γ s) ∧ 0 ≤ Q ∧
          (1 - η) * Q ^ 2 ≤ ∑ s : Fin S, γ s ∧
          ∀ x ∈ Set.Icc a b,
            (∀ s, |x - z s| ≤ δ) →
            (∀ s, γ s ≤ β s x (z s)) ∧
              Real.sqrt (diagonalWeight S β x) ≤ Q := by
  -- Use coefficient_bounds to obtain a uniform positive minimum c and a
  -- finite upper bound on the diagonal weight. Choose a uniform continuity
  -- error e so (1-η)*(sqrt(w(y))+e)^2 ≤ w(y)-S*e for all y in Icc.
  -- good_cell_uniform_freeze then permits γ_s=β_s(y,y)-e and
  -- Q=sqrt(w(y))+e, uniformly in x and the reproduction array.
  classical
  intro η hη hη1
  obtain ⟨c, C, hc, hbounds⟩ := coefficient_bounds a b hab S hS β hcont hpos
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  have hC : 0 < C := by
    have ha : a ∈ Set.Icc a b := ⟨le_refl a, le_of_lt hab⟩
    exact lt_of_lt_of_le (lt_of_lt_of_le hc ((hbounds ⟨0, hS⟩ a ha a ha).1))
      ((hbounds ⟨0, hS⟩ a ha a ha).2)
  let R : ℝ := Real.sqrt ((S : ℝ) * C)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  let D : ℝ := 2 * R + 1 + (S : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  let e : ℝ := min (c / 2) (min 1 (η * ((S : ℝ) * c) / (2 * D)))
  have he : 0 < e := by dsimp [e]; positivity
  have hec : e ≤ c / 2 := min_le_left _ _
  have he1 : e ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have heD : e * D ≤ η * ((S : ℝ) * c) := by
    have h := min_le_right (c / 2) (min 1 (η * ((S : ℝ) * c) / (2 * D)))
    have h' := h.trans (min_le_right _ _)
    dsimp [e] at *
    have := mul_le_mul_of_nonneg_right h' (by positivity : 0 ≤ 2 * D)
    rw [div_mul_cancel₀ _ (by positivity : 2 * D ≠ 0)] at this
    nlinarith
  obtain ⟨δ, hδ, hfreeze⟩ :=
    good_cell_uniform_freeze a b hab S hS β hcont hpos e he
  refine ⟨δ, hδ, ?_⟩
  intro y z hy hz hyz
  let w := diagonalWeight S β y
  let t := Real.sqrt w
  have hwlow : (S : ℝ) * c ≤ w := by
    dsimp [w, diagonalWeight]
    simpa using (Finset.sum_le_sum (s := Finset.univ)
      (fun s hs => (hbounds s y hy y hy).1) :
        ∑ _s : Fin S, c ≤ ∑ s : Fin S, β s y y)
  have hwup : w ≤ (S : ℝ) * C := by
    dsimp [w, diagonalWeight]
    simpa using (Finset.sum_le_sum (s := Finset.univ)
      (fun s hs => (hbounds s y hy y hy).2) :
        (∑ s : Fin S, β s y y) ≤ ∑ _s : Fin S, C)
  have hw0 : 0 ≤ w := le_trans (mul_nonneg (le_of_lt hSreal) (le_of_lt hc)) hwlow
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = w := Real.sq_sqrt hw0
  have htR : t ≤ R := Real.sqrt_le_sqrt hwup
  have hmargin : (1 - η) * (t + e) ^ 2 ≤ w - (S : ℝ) * e := by
    have hte : t * e ≤ R * e := mul_le_mul_of_nonneg_right htR (le_of_lt he)
    have he2 : e ^ 2 ≤ e := by nlinarith
    have hcross : 0 ≤ 2 * t * e + e ^ 2 := by positivity
    have hcrossbound :
        (1 - η) * (2 * t * e + e ^ 2) ≤ 2 * t * e + e ^ 2 := by
      simpa using mul_le_mul_of_nonneg_right
        (show 1 - η ≤ 1 by linarith) hcross
    have hηw : η * ((S : ℝ) * c) ≤ η * w :=
      mul_le_mul_of_nonneg_left hwlow (le_of_lt hη)
    dsimp [D] at heD
    nlinarith
  refine ⟨(fun s => β s y y - e), t + e, ?_, ?_, ?_, ?_⟩
  · intro s
    have := (hbounds s y hy y hy).1
    linarith
  · exact add_nonneg ht0 (le_of_lt he)
  · have hsum : (∑ s : Fin S, (β s y y - e)) = w - (S : ℝ) * e := by
      simp [w, diagonalWeight, Finset.sum_sub_distrib]
    rw [hsum]
    exact hmargin
  · intro x hx hxz
    obtain ⟨hβ, hq⟩ := hfreeze x y z hx hy hz (fun s => ⟨hxz s, hyz s⟩)
    constructor
    · intro s
      have := (abs_lt.mp (hβ s)).1
      linarith
    · dsimp [t]
      have := (abs_lt.mp hq).2
      linarith

/-- On [a nondegenerate interval](hyp:a,b,hab), [a nonempty finite
weight family](hyp:S,hS) with [continuous strictly positive weights](hyp:β,hcont,hpos),
each relative error below one gives [a positive locality radius and
the sharp quarter-factor good-cell lower bound](goal). -/
theorem good_cell_sqrt_mass_lower (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ δ : ℝ, 0 < δ ∧
      ∀ (B G : Set ℝ) (z : Fin S → ℝ),
        MeasurableSet B → MeasurableSet G →
        B ⊆ Set.Icc a b → G ⊆ B →
        (∀ s, z s ∈ Set.Icc a b) →
        (∀ x ∈ G, ∀ s, |x - z s| ≤ δ) →
        (1 - η) * (∫ x in G, Real.sqrt (diagonalWeight S β x)) ^ 2 / 4 ≤
          ∑ s : Fin S, ∫ x in B, β s x (z s) * |x - z s| := by
  -- For nonempty G choose x₀∈G. Obtain one γ,Q for every x∈G from
  -- good_cell_relative_freeze, then apply frozen_cell_sqrt_mass_lower.
  -- The empty G case follows from cost nonnegativity.
  intro η hη hη1
  obtain ⟨δ, hδ, hfreeze⟩ :=
    good_cell_relative_freeze a b hab S hS β hcont hpos η hη hη1
  refine ⟨δ, hδ, ?_⟩
  intro B G z hB hG hsub hGB hz hnear
  have hnonneg : ∀ x ∈ B, ∀ s, 0 ≤ β s x (z s) := by
    intro x hx s
    exact (hpos s x (z s) (hsub hx) (hz s)).le
  have hInt : ∀ s, IntegrableOn (fun x => β s x (z s) * |x - z s|) B volume := by
    intro s
    exact weighted_cell_integrable a b hab.le (β s) (hcont s)
      B hB hsub (z s) (hz s)
  by_cases hne : G.Nonempty
  · obtain ⟨y, hy⟩ := hne
    obtain ⟨γ, Q, hγ, hQ, hcoeff, hpoint⟩ :=
      hfreeze y z (hsub (hGB hy)) hz (hnear y hy)
    apply frozen_cell_sqrt_mass_lower a b hab.le S β B G hB hG hsub hGB
      z γ hγ _ hnonneg hInt Q η hQ ⟨hη.le, hη1⟩ _ hcoeff
    · intro x hx s
      exact (hpoint x (hsub (hGB hx)) (hnear x hx)).1 s
    · intro x hx
      exact (hpoint x (hsub (hGB hx)) (hnear x hx)).2
  · have hempty : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [hempty, setIntegral_empty, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, zero_div]
    apply Finset.sum_nonneg
    intro s hs
    apply setIntegral_nonneg hB
    intro x hx
    exact mul_nonneg (hnonneg x hx s) (abs_nonneg _)

end Causalean.Mathlib.Analysis.Quantization
