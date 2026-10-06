module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedLinearFamily
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedFamilyGeometry

/-! # Packaging the folded constructions as a hypercube family -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

lemma FoldedGeometry.hypercubeFamily
    {hd : 0 < d} {q K : ℕ} {Q : Fin K → Set (XSpace d)}
    {psi : Fin K → XSpace d → ℝ} {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B) (hq24 : 24 ≤ q)
    {beta L cX CX cg Cg kappa eps A Bconst : ℝ}
    (hpars : ValidClassParameters d beta L cX CX cg Cg)
    (hkappa : 0 < kappa) (heps : 0 < eps) (heps128 : eps ≤ 1 / 128)
    (hDeps : (128 * (d : ℝ)) * eps ≤ 1)
    (hnonlinearHolder : beta < 1 → 1 / 2 + (128 * (d : ℝ)) * kappa ≤ L)
    (hnonlinearScale : beta < 1 →
      4 ≤ kappa * ((q : ℝ)⁻¹) ^ beta / (q : ℝ)⁻¹)
    (hnonlinearSmall : beta < 1 →
      kappa * ((q : ℝ)⁻¹) ^ beta * (1 + eps) ≤ 1 / 12)
    (hnonlinearError : beta < 1 →
      4 * (q : ℝ)⁻¹ / (kappa * ((q : ℝ)⁻¹) ^ beta) + 24 * eps ≤
        min (1 - cg / 2) (Cg / 2 - 1))
    (hlinearHolder : beta = 1 → 1 / 2 + 96 * (d : ℝ) * eps ≤ L)
    (hlinearError : beta = 1 → 256 * eps ≤ min (2 - cg) (Cg - 2)) :
    HypercubeFamily d beta L cX CX cg Cg (q : ℝ)⁻¹
      ((1 / 16 : ℝ) ^ d) (min (eps * kappa / 2) eps) 1
      (8 * eps ^ 2 * kappa ^ 2 + 32 * eps ^ 2) kappa eps A Bconst := by
  let g : (Fin K → Bool) → XSpace d → ℝ := fun theta =>
    foldedHypercube hd beta (q : ℝ)⁻¹ kappa eps K psi theta
  let base : XSpace d → ℝ := if beta < 1 then
    foldedBaseScore hd beta (q : ℝ)⁻¹ kappa
  else fun x => 1 / 4 + x ⟨0, hd⟩ / 2
  let amplitude : ℝ := if beta < 1 then
    eps * (kappa * ((q : ℝ)⁻¹) ^ beta) / 2
  else eps * (q : ℝ)⁻¹
  refine ⟨K, Q, psi, B, g, base, amplitude, ?_⟩
  have hcard := hgeo.card_power_bounds hq24
  refine ⟨hcard.1, ?_, fun j => hgeo.isSideCube j,
    fun i j hij => hgeo.pairwise_disjoint hij, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hcard.2
  · intro j
    exact ⟨hgeo.core_subset j, hgeo.core_power_lower j⟩
  · intro j x
    exact ⟨(hgeo.bump_bounds j x).1, (hgeo.bump_bounds j x).2,
      fun hx => hgeo.bump_eq_zero_off_cell j hx,
      fun hx => hgeo.bump_eq_one_on_core j hx⟩
  · dsimp [amplitude]
    split_ifs with hb
    · have hhpow : 0 < ((q : ℝ)⁻¹) ^ beta := by positivity
      have hmin := min_le_left (eps * kappa / 2) eps
      calc
        min (eps * kappa / 2) eps * ((q : ℝ)⁻¹) ^ beta ≤
            (eps * kappa / 2) * ((q : ℝ)⁻¹) ^ beta :=
          mul_le_mul_of_nonneg_right hmin hhpow.le
        _ = eps * (kappa * ((q : ℝ)⁻¹) ^ beta) / 2 := by ring
    · have hh : 0 < (q : ℝ)⁻¹ := by positivity
      have hb1 : beta = 1 := le_antisymm hpars.2.2.1 (not_lt.mp hb)
      rw [hb1, Real.rpow_one]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) hh.le
  · intro theta x
    dsimp [g, amplitude, base]
    by_cases hb : beta < 1
    · simp only [hb, if_true]
      exact hgeo.foldedRawScore_additive hb (by positivity)
        (by
          have hs := hnonlinearSmall hb
          have ha0 : 0 ≤ kappa * ((q : ℝ)⁻¹) ^ beta := by positivity
          have hae : 0 ≤ (kappa * ((q : ℝ)⁻¹) ^ beta) * eps :=
            mul_nonneg ha0 heps.le
          nlinarith)
        heps.le (heps128.trans (by norm_num)) theta x
    · simp only [hb, if_false]
      have hb1 : beta = 1 := le_antisymm hpars.2.2.1 (not_lt.mp hb)
      subst beta
      simpa [foldedHypercube, foldedRawScore] using
        hgeo.betaOne_rawScore_additive eps theta x
  · intro theta j x hx
    exact hgeo.foldedHypercube_flip_eq_off_cell beta kappa eps theta j x hx
  · intro hd' hb theta x
    rfl
  · intro theta
    by_cases hb : beta < 1
    · exact hgeo.regularScoreModel hpars hb hkappa.le heps.le
        (heps128.trans (by norm_num)) hDeps (hnonlinearHolder hb)
        (hnonlinearScale hb) (hnonlinearSmall hb) (hnonlinearError hb) theta
    · have hb1 : beta = 1 := le_antisymm hpars.2.2.1 (not_lt.mp hb)
      subst beta
      have hignore : g theta =
          foldedRawScore hd 1 (q : ℝ)⁻¹ 1 eps K psi theta := by
        funext x
        simp [g, foldedHypercube, foldedRawScore]
      rw [hignore]
      exact
        hgeo.betaOne_regularScoreModel hpars heps.le heps128
          (hlinearHolder rfl) (hlinearError rfl) theta
  · intro theta
    have hpsi : ∀ i, Measurable (psi i) := by
      intro i
      rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
      rw [(hdefs i).2.1]
      exact measurable_meshBump hd _ _
    have hg : Measurable (g theta) :=
      measurable_foldedRawScore_of_measurable_bumps hd beta _ kappa eps K psi hpsi theta
    have hrange : ∀ x ∈ cube d, 0 ≤ g theta x ∧ g theta x ≤ 1 := by
      intro x hx
      by_cases hb : beta < 1
      · have hf := triangularFold_mem_Icc
          (x ⟨0, hd⟩ + kappa * (q : ℝ)⁻¹ ^ beta *
            triangularWave (x ⟨0, hd⟩ / (q : ℝ)⁻¹) +
            eps * (kappa * (q : ℝ)⁻¹ ^ beta) *
              ∑ j, localSign (theta j) * psi j x)
        simp only [g, foldedHypercube, foldedRawScore, hb, if_true]
        constructor <;> nlinarith [hf.1, hf.2]
      · have hb1 : beta = 1 := le_antisymm hpars.2.2.1 (not_lt.mp hb)
        subst beta
        have hm := hgeo.betaOne_rawScore_mem_band heps.le heps128 theta x hx
        have hignore : g theta x =
            foldedRawScore hd 1 (q : ℝ)⁻¹ 1 eps K psi theta x := by
          simp [g, foldedHypercube, foldedRawScore]
        rw [hignore]
        exact ⟨(by norm_num : (0 : ℝ) ≤ 1 / 4).trans hm.1,
          hm.2.trans (by norm_num)⟩
    exact bernoulliUnitLaw_map_fst (g theta) hg hrange
  · intro m hm theta j
    by_cases hb : beta < 1
    · refine (hgeo.bernoulliPilotProduct_klDiv_flip_rpow_le hb (by positivity)
        (by
          have hs := hnonlinearSmall hb
          have ha0 : 0 ≤ kappa * ((q : ℝ)⁻¹) ^ beta := by positivity
          have hae : 0 ≤ (kappa * ((q : ℝ)⁻¹) ^ beta) * eps :=
            mul_nonneg ha0 heps.le
          nlinarith)
        heps.le (heps128.trans (by norm_num)) m theta j).trans ?_
      apply ENNReal.ofReal_le_ofReal
      have hc : 8 * eps ^ 2 * kappa ^ 2 ≤
          8 * eps ^ 2 * kappa ^ 2 + 32 * eps ^ 2 := by
        nlinarith [sq_nonneg eps]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by positivity))
        (Real.rpow_nonneg (by positivity) _)
    · have hb1 : beta = 1 := le_antisymm hpars.2.2.1 (not_lt.mp hb)
      subst beta
      have hignore (vartheta : Fin K → Bool) :
          g vartheta = foldedHypercube hd 1 (q : ℝ)⁻¹ 1 eps K psi vartheta := by
        funext x
        simp [g, foldedHypercube, foldedRawScore]
      rw [hignore theta, hignore (flipCoordinate theta j)]
      refine (hgeo.betaOne_bernoulliPilotProduct_klDiv_flip_rpow_le
        heps.le heps128 m theta j).trans ?_
      apply ENNReal.ofReal_le_ofReal
      norm_num
      have hc : 32 * eps ^ 2 ≤
          8 * eps ^ 2 * kappa ^ 2 + 32 * eps ^ 2 := by
        nlinarith [sq_nonneg eps, sq_nonneg kappa]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by positivity))
        (Real.rpow_nonneg (by positivity) _)

end CausalSmith.Experimentation.PilotscorePairingFrontier
