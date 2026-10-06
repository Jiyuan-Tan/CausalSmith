module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.Mixture
public import Mathlib.Probability.Moments.Variance

/-!
# Product-prior target concentration

Mean, variance and escape bounds for the half absolute-norm target under
independent amplitude-supported coordinates. The causal symmetric target is
this statistic plus one half; the paired TV target is this statistic itself.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [the stated hnu condition](hyp:hnu). [An amplitude-supported scalar absolute value is square integrable](goal). -/
-- @node: amplitudePrior_abs_memLp
lemma amplitudePrior_abs_memLp (a : ℝ) (nu : Measure ℝ)
    (hnu : AmplitudePrior a nu) : MemLp (fun u : ℝ => |u|) 2 nu := by
  letI := hnu.1
  apply MemLp.of_bound (by fun_prop) a
  filter_upwards [ae_iff.mpr hnu.2] with u hu
  simpa only [Real.norm_eq_abs, abs_abs] using abs_le.mpr hu

/-- Assume [positive dimension](hyp:hd) and [the stated hnu condition](hyp:hnu). [The half-norm prior mean is one half of the scalar absolute moment](goal). -/
-- @node: productPrior_halfNorm_mean
lemma productPrior_halfNorm_mean (d : ℕ) (hd : 0 < d) (a : ℝ)
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    (∫ theta, signedNorm theta / 2 ∂productPrior d nu) =
      (∫ u, |u| ∂nu) / 2 := by
  letI := hnu.1
  have hmem := amplitudePrior_abs_memLp a nu hnu
  have hcoord (j : Fin d) :
      Integrable (fun theta : Fin d → ℝ => |theta j|) (productPrior d nu) :=
    (hmem.comp_measurePreserving (measurePreserving_eval (fun _ : Fin d => nu) j)).integrable
      (by norm_num)
  have hmean (j : Fin d) :
      (∫ theta : Fin d → ℝ, |theta j| ∂productPrior d nu) = ∫ u, |u| ∂nu := by
    have hm := (measurePreserving_eval (fun _ : Fin d => nu) j).map_eq
    calc
      _ = ∫ u, |u| ∂(productPrior d nu).map (fun theta => theta j) :=
        (integral_map (φ := fun theta : Fin d → ℝ => theta j)
          (f := fun u : ℝ => |u|) (measurable_pi_apply j).aemeasurable
          (by fun_prop)).symm
      _ = _ := by rw [show (productPrior d nu).map (fun theta => theta j) = nu from hm]
  simp only [signedNorm, div_eq_mul_inv]
  rw [integral_mul_const, integral_const_mul, integral_finset_sum _ (fun j _ => hcoord j)]
  simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

/-- Assume [positive dimension](hyp:hd) and [the stated hnu condition](hyp:hnu). [Independence of prior coordinates bounds the half-norm variance by the paper's amplitude-squared over four times the dimension](goal). -/
-- @node: productPrior_halfNorm_variance
lemma productPrior_halfNorm_variance (d : ℕ) (hd : 0 < d) (a : ℝ)
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    variance (fun theta => signedNorm theta / 2) (productPrior d nu) ≤ a^2/(4*d) := by
  letI := hnu.1
  have hmem := amplitudePrior_abs_memLp a nu hnu
  have hscalar : variance (fun u : ℝ => |u|) nu ≤ a^2 := by
    have hbound : ∀ᵐ u ∂nu, |u| ∈ Set.Icc 0 a := by
      filter_upwards [ae_iff.mpr hnu.2] with u hu
      exact ⟨abs_nonneg _, abs_le.mpr hu⟩
    have hv := variance_le_sq_of_bounded hbound (by fun_prop)
    exact hv.trans (by nlinarith [sq_nonneg a])
  have heq : (fun theta : Fin d → ℝ => signedNorm theta / 2) =
      fun theta => ((d : ℝ)⁻¹ / 2) * ∑ j, |theta j| := by
    funext theta
    simp only [signedNorm]
    ring
  rw [heq, variance_const_mul]
  have hsum : variance (fun theta : Fin d → ℝ => ∑ j, |theta j|)
      (productPrior d nu) = (d : ℝ) * variance (fun u : ℝ => |u|) nu := by
    have hv := variance_sum_pi (μ := fun _ : Fin d => nu)
      (X := fun _ => fun u : ℝ => |u|) (fun _ => hmem)
    convert hv using 1 <;> simp [productPrior]
    congr 1
    funext theta
    simp
  rw [hsum]
  calc
    _ ≤ ((d : ℝ)⁻¹ / 2)^2 * ((d : ℝ) * a^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hscalar (by positivity))
        (sq_nonneg _)
    _ = a^2/(4*d) := by
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      <;> ring

/-- Assume [positive dimension](hyp:hd), [the stated hnu condition](hyp:hnu), and [the stated ht condition](hyp:ht). [Chebyshev's inequality controls escape from the scalar absolute-moment center under the coordinate product prior](goal). -/
-- @node: productPrior_halfNorm_escape
lemma productPrior_halfNorm_escape (d : ℕ) (hd : 0 < d) (a : ℝ)
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) (t : ℝ) (ht : 0 < t) :
    (productPrior d nu) {theta | t ≤ |signedNorm theta / 2 - (∫ u, |u| ∂nu) / 2|} ≤
      ENNReal.ofReal (a^2 / (4*d*t^2)) := by
  letI := hnu.1
  letI : IsProbabilityMeasure (productPrior d nu) := by
    unfold productPrior
    infer_instance
  have hcoord (j : Fin d) : MemLp (fun theta : Fin d → ℝ => |theta j|) 2
      (productPrior d nu) :=
    (amplitudePrior_abs_memLp a nu hnu).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin d => nu) j)
  have hsum := memLp_finsetSum (s := Finset.univ) (fun j _ => hcoord j)
  have hmem : MemLp (fun theta : Fin d → ℝ => signedNorm theta / 2) 2
      (productPrior d nu) := by
    simpa only [signedNorm, div_eq_mul_inv] using (hsum.const_mul (d : ℝ)⁻¹).mul_const (2 : ℝ)⁻¹
  have hcheb := meas_ge_le_variance_div_sq hmem ht
  rw [productPrior_halfNorm_mean d hd a nu hnu] at hcheb
  refine hcheb.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (a^2/(4*d)) / t^2 :=
      div_le_div_of_nonneg_right (productPrior_halfNorm_variance d hd a nu hnu)
        (sq_nonneg _)
    _ = _ := by ring

/-- Assume [positive dimension](hyp:hd), [the stated hnu condition](hyp:hnu), and [the stated hgap condition](hyp:hgap). [At radius one eighth of a positive target gap, the escape probability is at most sixteen times amplitude squared divided by dimension and gap squared](goal). -/
-- @node: productPrior_halfNorm_gap_escape
lemma productPrior_halfNorm_gap_escape (d : ℕ) (hd : 0 < d) (a : ℝ)
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) (gap : ℝ) (hgap : 0 < gap) :
    (productPrior d nu) {theta | gap/8 ≤ |signedNorm theta/2 - (∫ u, |u| ∂nu)/2|} ≤
      ENNReal.ofReal (16*a^2/(d*gap^2)) := by
  have h := productPrior_halfNorm_escape d hd a nu hnu (gap/8) (by positivity)
  convert h using 1 <;> congr 1 <;> ring

end CausalSmith.Stat.LdpOptvalueUniformFrontier
