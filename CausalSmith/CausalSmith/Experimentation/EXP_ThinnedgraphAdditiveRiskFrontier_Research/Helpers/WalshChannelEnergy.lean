module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.WalshChannelBasics
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Weighted Walsh channel energy

Assembles finite Parseval, coefficient integrability, and the integrated flip bound.
-/

public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The order-weighted Walsh energy density equals one quarter of the total flip energy.  [For the stated data and conditions](hyp:d,h,w), [the stated conclusion holds](goal). -/
-- @node: walsh_weighted_density_parseval
lemma walsh_weighted_density_parseval (d : ℕ) (h w : ℝ) :
    (∑ s ∈ Finset.range (d + 1),
      (d.choose s : ℝ) * (s : ℝ) * (walshCoeff d h s w) ^ 2 * refDensity d h w) =
      (1 / 4 : ℝ) * ∑ j : Fin d, flipEnergy d h j w := by
  by_cases hz : refDensity d h w = 0
  · simp [hz, flipEnergy]
  have hg : 0 < refDensity d h w := lt_of_le_of_ne (refDensity_nonneg d h w) (Ne.symm hz)
  have hp := finite_walsh_weighted_parseval d (fun ε => rowDensity d h ε w / refDensity d h w)
  simp_rw [← walshCoeff_eq_subset_coefficient d h w _ hg] at hp
  have hc := Finset.sum_powerset_apply_card
    (fun s => (s : ℝ) * (walshCoeff d h s w) ^ 2)
    (x := (Finset.univ : Finset (Fin d)))
  simp only [Finset.powerset_univ, Fintype.card_fin, Finset.card_univ, nsmul_eq_mul] at hc
  rw [hc] at hp
  have hdif (ε : Fin d → Bool) (j : Fin d) :
      (rowDensity d h ε w / refDensity d h w -
        rowDensity d h (Function.update ε j (!(ε j))) w / refDensity d h w) ^ 2 *
        refDensity d h w =
      (rowDensity d h ε w - rowDensity d h (Function.update ε j (!(ε j))) w) ^ 2 /
        refDensity d h w := by field_simp
  have hm := congrArg (fun t : ℝ => t * refDensity d h w) hp
  simp only [Finset.sum_mul, mul_assoc] at hm
  simp_rw [← mul_assoc _ _ (refDensity d h w), hdif] at hm
  simpa only [flipEnergy, mul_assoc] using hm

/-- A Walsh likelihood coefficient has absolute value at most one.  [For the stated data and conditions](hyp:d,h,w,s), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_abs_le_one
lemma walshCoeff_abs_le_one (d : ℕ) (h w : ℝ) (s : ℕ) :
    |walshCoeff d h s w| ≤ 1 := by
  by_cases hz : refDensity d h w = 0
  · simp [walshCoeff, hz]
  have hc (ε : Fin d → Bool) :
      |rowDensity d h ε w / refDensity d h w *
        ∏ j ∈ Finset.univ.filter (fun j : Fin d => j.val < s), signOf (ε j)| =
      rowDensity d h ε w / refDensity d h w := by
    rw [abs_mul, Finset.abs_prod]
    have hs (j : Fin d) : |signOf (ε j)| = 1 := by cases ε j <;> norm_num [signOf]
    simp only [hs, Finset.prod_const_one, mul_one]
    exact abs_of_nonneg (div_nonneg (cosSqDensity_nonneg _) (refDensity_nonneg d h w))
  rw [walshCoeff, if_neg hz, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((2 : ℝ) ^ d)⁻¹)]
  calc
    _ ≤ ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool, rowDensity d h ε w / refDensity d h w := by
      gcongr
      simpa only [hc] using Finset.abs_sum_le_sum_abs
        (fun ε : Fin d → Bool => rowDensity d h ε w / refDensity d h w *
          ∏ j ∈ Finset.univ.filter (fun j : Fin d => j.val < s), signOf (ε j)) Finset.univ
    _ = 1 := by
      rw [← Finset.sum_div, ← mul_div_assoc]
      exact div_self hz

/-- [The coefficient convention at zero reference density preserves measurability](goal). -/
-- @node: walshCoeff_measurable
@[fun_prop]
lemma walshCoeff_measurable (d : ℕ) (h : ℝ) (s : ℕ) : Measurable (walshCoeff d h s) := by
  unfold walshCoeff
  apply Measurable.ite
    (measurableSet_eq_fun (refDensity_measurable d h) measurable_const)
  · fun_prop
  · fun_prop

/-- Squared coefficient densities are integrable, dominated by the normalized reference density.  [For the stated data and conditions](hyp:d,h,s), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_sq_density_integrable
lemma walshCoeff_sq_density_integrable (d : ℕ) (h : ℝ) (s : ℕ) :
    Integrable (fun w => (walshCoeff d h s w) ^ 2 * refDensity d h w) := by
  have hm : Measurable (fun w => (walshCoeff d h s w) ^ 2 * refDensity d h w) := by
    fun_prop
  apply (refDensity_integrable_normalized d h).1.mono' hm.aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (refDensity_nonneg d h w))]
  have hs : (walshCoeff d h s w) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr (walshCoeff_abs_le_one d h w s)
  simpa using mul_le_mul_of_nonneg_right hs (refDensity_nonneg d h w)

/-- Integrating the finite weighted Parseval formula gives the channel's weighted energy.  [For the stated data and conditions](hyp:d,h,hd,hh), [the stated conclusion holds](goal). -/
-- @node: walsh_weighted_integral_parseval
lemma walsh_weighted_integral_parseval (d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (hh : h ∈ Set.Icc 0 (1 / 4)) :
    etaOne d h = (1 / 4 : ℝ) * ∑ j : Fin d, (∫ w, flipEnergy d h j w) := by
  have hp := congrArg (fun f : ℝ → ℝ => ∫ w, f w)
    (funext (walsh_weighted_density_parseval d h))
  rw [integral_finsetSum] at hp
  · simp_rw [mul_assoc, integral_const_mul] at hp
    rw [integral_finsetSum Finset.univ
      (by intro j _; exact flipEnergy_integrable d h hd hh.1 j)] at hp
    simp_rw [← mul_assoc] at hp
    change (∑ s ∈ Finset.range (d + 1),
      (d.choose s : ℝ) * (s : ℝ) * gamma d h s) = _ at hp
    have hr : Finset.range (d + 1) = insert 0 (Finset.Icc 1 d) := by
      ext s
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hr, Finset.sum_insert (by simp)] at hp
    simpa [etaOne, mul_comm (d.choose _ : ℝ)] using hp
  · intro s _
    simpa only [mul_assoc] using
      (walshCoeff_sq_density_integrable d h s).const_mul ((d.choose s : ℝ) * s)

/-- At zero amplitude the order-weighted channel energy vanishes.  [For the stated data and conditions](hyp:d,hd), [the stated conclusion holds](goal). -/
-- @node: etaOne_zero_amplitude
lemma etaOne_zero_amplitude (d : ℕ) (hd : 1 ≤ d) : etaOne d 0 = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  have hz : gamma d 0 s = 0 := by
    simp [gamma, walshCoeff_zero_amplitude d s _ hd (Finset.mem_Icc.mp hs).1]
  rw [hz, mul_zero]

/-- Finite permutation-symmetric Walsh expansion, centered coefficients, and weighted channel
energy.  [For the stated data and conditions](hyp:d,h,hd,hh), [the stated conclusion holds](goal). -/
-- @node: lem:walsh-channel-energy
lemma walsh_channel_energy (d : ℕ) (h : ℝ) (hd : 1 ≤ d) (hh : h ∈ Set.Icc 0 (1 / 4)) :
    (∀ w, 0 < refDensity d h w → walshCoeff d h 0 w = 1 ∧
      ∀ ε : Fin d → Bool, rowDensity d h ε w / refDensity d h w =
        ∑ E : Finset (Fin d), walshCoeff d h E.card w * ∏ j ∈ E, signOf (ε j)) ∧
    (∀ s, 1 ≤ s → ∫ w, walshCoeff d h s w * refDensity d h w = 0) ∧
    0 ≤ eta d h ∧ eta d h ≤ etaOne d h ∧
    etaOne d h ≤ 12 * Real.pi ^ 2 * h ^ 2 / d := by
  refine ⟨?_, ?_, (eta_nonneg_le_etaOne d h).1, (eta_nonneg_le_etaOne d h).2, ?_⟩
  · intro w hw
    refine ⟨walshCoeff_zero d h w hw, ?_⟩
    exact rowDensity_walsh_expansion d h w hw
  · exact fun s hs => walshCoeff_centered d h hd s hs
  · by_cases hhzero : h = 0
    · subst h
      rw [etaOne_zero_amplitude d hd]
      simp
    · rw [walsh_weighted_integral_parseval d h hd hh]
      exact integrated_flip_sum_le d h hd hh

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
