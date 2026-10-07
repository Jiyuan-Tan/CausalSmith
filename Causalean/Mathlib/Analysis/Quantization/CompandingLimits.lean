module
public import Causalean.Mathlib.Analysis.Quantization.Companding
public import Causalean.Mathlib.Analysis.Quantization.LowerLocal

/-! Finite mesh estimates and exact scaled limits for equal-mass companding
cells. The estimates isolate the analytic and algebraic steps of the limit. -/

public section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

noncomputable section

/-- The scaled sum of squared companding cell lengths is uniformly bounded
over every positive cell count. This follows from the equal-mass length
bound and the telescoping sum of cell lengths. -/
theorem companding_scaled_length_square_bound (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      (k : ℝ) * ∑ j : Fin k,
        (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 ≤ C := by
  classical
  obtain ⟨c, hc, hlen⟩ := companding_length_bound a b hab S hS β hcont hpos
  let M : ℝ := ∫ x in a..b, Real.sqrt (diagonalWeight S β x)
  refine ⟨M / c * (b - a) + 1, ?_, ?_⟩
  · have hM : 0 < M := (sqrt_mass_regular a b hab S hS β hcont hpos).2
    positivity
  intro k hk
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hord := (boundary_order a b hab S k hS hk β hcont hpos).2.2
  have hcell (j : Fin k) :
      (k : ℝ) * (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 ≤
        (M / c) * (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) := by
    have hp : 0 ≤ boundary a b S k (j.val + 1) β - boundary a b S k j.val β :=
      sub_nonneg.mpr ((hord j.val (j.val + 1) (by omega) (by omega)).le)
    have hb := hlen k hk j
    have hh : (k : ℝ) * (c * (boundary a b S k (j.val + 1) β -
        boundary a b S k j.val β)) ≤ M := by
      calc
        _ = c * (boundary a b S k (j.val + 1) β -
            boundary a b S k j.val β) * k := by ring
        _ ≤ M := (le_div_iff₀ hkreal).mp hb
    have hprod := mul_le_mul_of_nonneg_right hh hp
    calc
      _ ≤ M * (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) / c :=
        (le_div_iff₀ hc).2 (by nlinarith [hprod])
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcell j)
  have htel : (∑ j : Fin k, (boundary a b S k (j.val + 1) β -
      boundary a b S k j.val β)) = b - a := by
    calc
      _ = boundary a b S k k β - boundary a b S k 0 β := by
        simpa only [Finset.sum_range] using
          (Finset.sum_range_sub (fun n => boundary a b S k n β) k)
      _ = b - a := by
        obtain ⟨hfirst, hlast, _⟩ := boundary_order a b hab S k hS hk β hcont hpos
        rw [hfirst, hlast]
  rw [← Finset.mul_sum, ← Finset.mul_sum, htel] at hsum
  linarith

/-- The squared midpoint mass of each sufficiently fine companding cell
differs from the square of its exact equal mass by at most a prescribed
multiple of the squared cell length. -/
theorem companding_surrogate_cell_error_eventually (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < k →
      ∀ j : Fin k,
        |diagonalWeight S β
            ((boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2) *
            (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 -
          ((∫ x in a..b, Real.sqrt (diagonalWeight S β x)) / k) ^ 2| ≤
          η * (boundary a b S k (j.val + 1) β -
            boundary a b S k j.val β) ^ 2 := by
  intro η hη
  let f : ℝ → ℝ := fun x => Real.sqrt (diagonalWeight S β x)
  have hf := (sqrt_mass_regular a b hab S hS β hcont hpos).1
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hab.le) hf
  let B : ℝ := f x₀ + 1
  have hB : 0 < B := by
    have : 0 ≤ f x₀ := Real.sqrt_nonneg _
    dsimp [B]; linarith
  have hupper : ∀ x ∈ Set.Icc a b, f x ≤ B := by
    intro x hx
    exact (hmax hx).trans (by dsimp [B]; linarith)
  let δ : ℝ := min 1 (η / (2 * B + 1))
  have hδ : 0 < δ := lt_min_iff.mpr ⟨by norm_num, div_pos hη (by linarith)⟩
  obtain ⟨K, hK⟩ := companding_midpoint_mass_error_eventually
    a b hab S hS β hcont hpos δ hδ
  refine ⟨K, ?_⟩
  intro k hkK hk j
  let l := boundary a b S k j.val β
  let r := boundary a b S k (j.val + 1) β
  let m := (l + r) / 2
  let L := r - l
  let q := f m * L
  let t := (∫ x in a..b, f x) / k
  have hmem : m ∈ Set.Icc a b := by
    have hl := (boundary_equal_mass a b hab S k j.val hS hk j.isLt.le β hcont hpos).1
    have hr := (boundary_equal_mass a b hab S k (j.val + 1) hS hk (by omega) β hcont hpos).1
    dsimp [m]
    constructor <;> linarith [hl.1, hl.2, hr.1, hr.2]
  have hL : 0 ≤ L := by
    dsimp [L]
    exact sub_nonneg.mpr (((boundary_order a b hab S k hS hk β hcont hpos).2.2
      j.val (j.val + 1) (by omega) (by omega)).le)
  have hq : 0 ≤ q := mul_nonneg (Real.sqrt_nonneg _) hL
  have hqB : q ≤ B * L := mul_le_mul_of_nonneg_right (hupper m hmem) hL
  have he : |q - t| ≤ δ * L := hK k hkK hk j
  have ht : 0 ≤ t := by
    have hM := (sqrt_mass_regular a b hab S hS β hcont hpos).2
    exact div_nonneg hM.le (by exact_mod_cast (Nat.zero_le k))
  have htB : t ≤ (B + δ) * L := by
    have := (abs_le.mp he).1
    nlinarith
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδeta : δ * (2 * B + 1) ≤ η := by
    have h := min_le_right (1 : ℝ) (η / (2 * B + 1))
    exact (le_div_iff₀ (by linarith : 0 < 2 * B + 1)).mp h
  have hdiag : 0 ≤ diagonalWeight S β m :=
    ((diagonal_regular a b S hS β hcont hpos).2 m hmem).le
  have hsq : diagonalWeight S β m * L ^ 2 = q ^ 2 := by
    calc
      _ = (Real.sqrt (diagonalWeight S β m)) ^ 2 * L ^ 2 := by
        rw [Real.sq_sqrt hdiag]
      _ = q ^ 2 := by dsimp [q, f]; ring
  change |diagonalWeight S β m * L ^ 2 - t ^ 2| ≤ η * L ^ 2
  rw [hsq, show q ^ 2 - t ^ 2 = (q - t) * (q + t) by ring,
    abs_mul, abs_of_nonneg (add_nonneg hq ht)]
  have hsum : q + t ≤ (2 * B + 1) * L := by
    nlinarith
  have hprod := mul_le_mul he hsum (add_nonneg hq ht) (mul_nonneg hδ.le hL)
  have hlast : (δ * L) * ((2 * B + 1) * L) ≤ η * L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδeta) (sq_nonneg L)]
  exact hprod.trans hlast

/-- The true paired cost of one sufficiently fine companding cell differs
from its midpoint diagonal-weight surrogate by at most a prescribed multiple
of that cell's squared length. -/
theorem companding_integrand_cell_error_eventually (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < k →
      ∀ j : Fin k,
        |(∑ s : Fin S, ∫ x in compandingCell a b S k β j,
            β s x (compandingMidpoint a b S k β j s) *
              |x - compandingMidpoint a b S k β j s|) -
          diagonalWeight S β
            ((boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2) *
            (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 / 4| ≤
          η * (boundary a b S k (j.val + 1) β -
            boundary a b S k j.val β) ^ 2 := by
  classical
  intro η hη
  let δ : ℝ := 4 * η / S
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  have hδ : 0 < δ := div_pos (by positivity) hSreal
  obtain ⟨K, hK⟩ := companding_coefficient_error_eventually
    a b hab S hS β hcont hpos δ hδ
  refine ⟨K, ?_⟩
  intro k hkK hk j
  let C := compandingCell a b S k β j
  let m := (boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2
  let L := boundary a b S k (j.val + 1) β - boundary a b S k j.val β
  let H := L ^ 2 / 4
  have hH : 0 ≤ H := by dsimp [H]; positivity
  obtain ⟨hpart, hmid⟩ := companding_feasible a b hab S k hS hk β hcont hpos
  have hCmeas : MeasurableSet C := hpart.1 j
  have hCsub : C ⊆ Set.Icc a b := by
    intro x hx
    rw [← hpart.2.2]
    exact Set.mem_iUnion.mpr ⟨j, hx⟩
  have hm : m ∈ Set.Icc a b := by
    simpa only [m, compandingMidpoint] using hmid j ⟨0, hS⟩
  have hdistInt : IntegrableOn (fun x => |x - m|) C volume := by
    have hcont' : Continuous (fun x : ℝ => |x - m|) := by fun_prop
    exact (hcont'.continuousOn.integrableOn_compact isCompact_Icc).mono_set hCsub
  have hmoment : (∫ x in C, |x - m|) = H := by
    simpa only [C, m, H, compandingMidpoint] using
      (companding_cell_midpoint_moment a b hab S k hS hk β hcont hpos j ⟨0, hS⟩)
  have hconst (v : ℝ) : (∫ x in C, v * |x - m|) = v * H := by
    rw [integral_const_mul, hmoment]
  have hone (s : Fin S) :
      |(∫ x in C, β s x m * |x - m|) - β s m m * H| ≤ δ * H := by
    have hInt : IntegrableOn (fun x => β s x m * |x - m|) C volume :=
      weighted_cell_integrable a b (β s) (hcont s) C hCsub m hm
    have hpoint (x : ℝ) (hx : x ∈ C) : |β s x m - β s m m| ≤ δ := by
      simpa only [C, m, compandingMidpoint] using hK k hkK hk j s x hx
    have hlow : (β s m m - δ) * H ≤ ∫ x in C, β s x m * |x - m| := by
      rw [← hconst]
      apply setIntegral_mono_on (hdistInt.const_mul _) hInt hCmeas
      intro x hx
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      linarith [(abs_le.mp (hpoint x hx)).1]
    have hupp : (∫ x in C, β s x m * |x - m|) ≤ (β s m m + δ) * H := by
      rw [← hconst]
      apply setIntegral_mono_on hInt (hdistInt.const_mul _) hCmeas
      intro x hx
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      linarith [(abs_le.mp (hpoint x hx)).2]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hsum : |(∑ s : Fin S, ∫ x in C, β s x m * |x - m|) -
      diagonalWeight S β m * H| ≤ (S : ℝ) * (δ * H) := by
    rw [diagonalWeight, Finset.sum_mul, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ s : Fin S, |(∫ x in C, β s x m * |x - m|) - β s m m * H| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s : Fin S, δ * H := Finset.sum_le_sum (fun s _ => hone s)
      _ = (S : ℝ) * (δ * H) := by simp
  have hgoal : |(∑ s : Fin S, ∫ x in C, β s x m * |x - m|) -
      diagonalWeight S β m * H| ≤ η * L ^ 2 := by
    calc
      _ ≤ (S : ℝ) * (δ * H) := hsum
      _ = η * L ^ 2 := by dsimp [δ, H]; field_simp
  simpa only [C, m, L, H, compandingMidpoint, mul_div_assoc] using hgoal

/-- The scaled midpoint diagonal-weight surrogate converges to one quarter
of the squared total square-root diagonal mass. -/
theorem companding_surrogate_scaled_tendsto (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    Tendsto (fun k : ℕ => (k : ℝ) * compandingSurrogateCost a b S k β)
      atTop (nhds ((1 / 4 : ℝ) *
        (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) ^ 2)) := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    companding_scaled_length_square_bound a b hab S hS β hcont hpos
  let M : ℝ := ∫ x in a..b, Real.sqrt (diagonalWeight S β x)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η : ℝ := 4 * ε / (C + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK⟩ := companding_surrogate_cell_error_eventually
    a b hab S hS β hcont hpos η hη
  refine ⟨max K 1, ?_⟩
  intro k hk
  have hkK : K ≤ k := le_trans (le_max_left _ _) hk
  have hkpos : 0 < k := lt_of_lt_of_le (by omega : 0 < max K 1) hk
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hcell (j : Fin k) :
      |diagonalWeight S β
          ((boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2) *
          (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 -
        (M / k) ^ 2| ≤
        η * (boundary a b S k (j.val + 1) β -
          boundary a b S k j.val β) ^ 2 := hK k hkK hkpos j
  have hsum :
      |∑ j : Fin k, (diagonalWeight S β
          ((boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2) *
          (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 -
        (M / k) ^ 2)| ≤
        η * ∑ j : Fin k, (boundary a b S k (j.val + 1) β -
          boundary a b S k j.val β) ^ 2 := by
    calc
      _ ≤ ∑ j : Fin k, |diagonalWeight S β
          ((boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2) *
          (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 -
        (M / k) ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin k, η * (boundary a b S k (j.val + 1) β -
          boundary a b S k j.val β) ^ 2 := Finset.sum_le_sum (fun j _ => hcell j)
      _ = _ := by rw [Finset.mul_sum]
  have hid : (k : ℝ) * compandingSurrogateCost a b S k β - M ^ 2 / 4 =
      ((k : ℝ) / 4) * ∑ j : Fin k, (diagonalWeight S β
          ((boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2) *
          (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 -
        (M / k) ^ 2) := by
    simp only [compandingSurrogateCost, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [mul_sub]
    congr 1
    · conv_lhs => rw [Finset.mul_sum]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · field_simp
  have hfinal : |(k : ℝ) * compandingSurrogateCost a b S k β - M ^ 2 / 4| ≤
      η * C / 4 := by
    rw [hid, abs_mul, abs_of_nonneg (div_nonneg hkreal.le (by norm_num))]
    have hb := hbound k hkpos
    have hp := mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ (k : ℝ) / 4 by positivity)
    nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hb)]
  have hsmall : η * C / 4 < ε := by
    have hratio : C / (C + 1) < 1 :=
      (div_lt_iff₀ (by linarith : 0 < C + 1)).2 (by linarith)
    calc
      η * C / 4 = ε * (C / (C + 1)) := by dsimp [η]; ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := by ring
  have hquarter : (1 / 4 : ℝ) * M ^ 2 = M ^ 2 / 4 := by ring
  rw [Real.dist_eq, hquarter]
  exact lt_of_le_of_lt hfinal hsmall

/-- The scaled difference between the true paired midpoint cost and its
diagonal-weight surrogate tends to zero as the companding mesh vanishes. -/
theorem companding_surrogate_error_tendsto (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    Tendsto (fun k : ℕ => (k : ℝ) *
      (weightedCost S k β (compandingCell a b S k β)
        (compandingMidpoint a b S k β) - compandingSurrogateCost a b S k β))
      atTop (nhds 0) := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    companding_scaled_length_square_bound a b hab S hS β hcont hpos
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η : ℝ := ε / (C + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK⟩ := companding_integrand_cell_error_eventually
    a b hab S hS β hcont hpos η hη
  refine ⟨max K 1, ?_⟩
  intro k hk
  have hkK : K ≤ k := le_trans (le_max_left _ _) hk
  have hkpos : 0 < k := lt_of_lt_of_le (by omega : 0 < max K 1) hk
  have hkreal : (0 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hsum :
      |∑ j : Fin k, ((∑ s : Fin S, ∫ x in compandingCell a b S k β j,
            β s x (compandingMidpoint a b S k β j s) *
              |x - compandingMidpoint a b S k β j s|) -
          diagonalWeight S β
            ((boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2) *
            (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 / 4)| ≤
      η * ∑ j : Fin k, (boundary a b S k (j.val + 1) β -
        boundary a b S k j.val β) ^ 2 := by
    calc
      _ ≤ ∑ j : Fin k, |(∑ s : Fin S, ∫ x in compandingCell a b S k β j,
            β s x (compandingMidpoint a b S k β j s) *
              |x - compandingMidpoint a b S k β j s|) -
          diagonalWeight S β
            ((boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2) *
            (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 / 4| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin k, η * (boundary a b S k (j.val + 1) β -
          boundary a b S k j.val β) ^ 2 :=
        Finset.sum_le_sum (fun j _ => hK k hkK hkpos j)
      _ = _ := by rw [Finset.mul_sum]
  have hid : weightedCost S k β (compandingCell a b S k β)
      (compandingMidpoint a b S k β) - compandingSurrogateCost a b S k β =
      ∑ j : Fin k, ((∑ s : Fin S, ∫ x in compandingCell a b S k β j,
          β s x (compandingMidpoint a b S k β j s) *
            |x - compandingMidpoint a b S k β j s|) -
        diagonalWeight S β
          ((boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2) *
          (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 / 4) := by
    simp only [weightedCost, compandingSurrogateCost, Finset.sum_sub_distrib]
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hkreal, hid]
  have hb := hbound k hkpos
  have hp := mul_le_mul_of_nonneg_left hsum hkreal
  have hsmall : η * C < ε := by
    have hratio : C / (C + 1) < 1 :=
      (div_lt_iff₀ (by linarith : 0 < C + 1)).2 (by linarith)
    calc
      η * C = ε * (C / (C + 1)) := by dsimp [η]; ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := by ring
  exact lt_of_le_of_lt (by nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hb)]) hsmall

/-- On [a nondegenerate interval from a to b](hyp:a,b,hab), for [a nonempty finite
weight family](hyp:S,hS) that is [jointly continuous](hyp:β,hcont) and
[strictly positive](hyp:hpos) on the square, [k times the paired weighted cost of the k-cell
companding partition with midpoint reproduction points converges, as k tends to infinity, to one
quarter of the square of the integral over the interval of the square root of the diagonal
weight](goal). -/
theorem companding_scaled_cost_tendsto (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    Tendsto (fun k : ℕ => (k : ℝ) * weightedCost S k β
      (compandingCell a b S k β) (compandingMidpoint a b S k β))
      atTop (nhds ((1 / 4 : ℝ) *
        (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) ^ 2)) := by
  have hsurrogate := companding_surrogate_scaled_tendsto a b hab S hS β hcont hpos
  have herr := companding_surrogate_error_tendsto a b hab S hS β hcont hpos
  convert hsurrogate.add herr using 1
  · ext k
    ring
  · simp

end

end Causalean.Mathlib.Analysis.Quantization
