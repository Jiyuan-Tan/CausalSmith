module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Basic
public import Causalean.Stat.Minimax.TotalVariation

/-! # Finite paired total variation

Normalization, singleton masses and the half-L1 formula for the paired family.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

variable {d : ℕ}
/-- Fix [the dimension](hyp:d). [All probability laws on the finite paired alphabet](goal). -/
def simplexModel (d : ℕ) : Set (Measure (PairedSymbol d)) :=
  {p | IsProbabilityMeasure p}
  -- @realizes \Delta_{2d}(all 2d-symbol probability laws) @realizes \mathsf p(probability law)
/-- Fix [the dimension](hyp:d). [The closed paired contrast family](goal). -/
def pairedFamily (d : ℕ) : Set (Measure (PairedSymbol d)) :=
  pairedLaw '' parameterCube d -- @realizes \mathcal P_d^{\mathrm{pair}}(image of contrast cube)

-- @node: def:tv-corollary-models
/-- Fix [the probability law p](hyp:p). [Scalar total variation from the public uniform law on the paired alphabet](goal). -/
def tvFromUniform (p : Measure (PairedSymbol d)) : ℝ :=
  (1/2 : ℝ) * ∑ v : PairedSymbol d, |p.real {v} - 1/(2*d)|
  -- @realizes D_{\mathrm{TV}}(half finite absolute probability-mass sum)

/-- Assume [positive dimension](hyp:hd). [Probability membership of every paired law](goal). -/
-- @node: pairedFamily_subset_simplex
lemma pairedFamily_subset_simplex (hd : 0 < d) : pairedFamily d ⊆ simplexModel d := by
  rintro p ⟨theta, hTheta, rfl⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmass : ∀ v : PairedSymbol d,
      0 ≤ (1 + signVal v.2 * theta v.1) / (2 * d) := by
    intro v
    apply div_nonneg _ (by positivity)
    have h := hTheta v.1
    cases v.2 <;> simp only [signVal, Bool.false_eq_true, ↓reduceIte] <;> linarith [h.1, h.2]
  have hsum : ∑ v : PairedSymbol d,
      (1 + signVal v.2 * theta v.1) / (2 * d) = (1 : ℝ) := by
    rw [Fintype.sum_prod_type]
    have hcell : ∀ j : Fin d, ∑ s : Bool,
        (1 + signVal s * theta j) / (2 * d) = (d : ℝ)⁻¹ := by
      intro j
      simp only [Fintype.sum_bool, signVal, Bool.false_eq_true, ↓reduceIte]
      field_simp
      <;> ring
    simp_rw [hcell]
    simp [ne_of_gt hdR]
  change IsProbabilityMeasure (pairedLaw theta)
  constructor
  simp only [pairedLaw, atomLaw, Measure.finsetSum_apply, MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => hmass v), hsum]
  simp
/-- Assume [the stated hw condition](hyp:hw). [Singleton masses of a nonnegative finite atomic law](goal). -/
-- @node: atomLaw_real_singleton
lemma atomLaw_real_singleton {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (a : α) :
    (atomLaw w).real {a} = w a := by
  classical
  simp [Measure.real, atomLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply', Pi.single_apply, ENNReal.toReal_ofReal (hw a)]

/-- [A finite probability experiment attains its half-L1 distance on positive atoms](goal). -/
-- @node: finite_tvDist_eq_half_sum
lemma finite_tvDist_eq_half_sum {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : Measure α)
    [IsProbabilityMeasure p] [IsProbabilityMeasure q] :
    Causalean.Stat.tvDist p q = (1/2 : ℝ) * ∑ x, |p.real {x} - q.real {x}| := by
  classical
  let A : Set α := {x | 0 ≤ p.real {x} - q.real {x}}
  have hA : MeasurableSet A := Set.toFinite A |>.measurableSet
  have hzero : ∑ x : α, (p.real {x} - q.real {x}) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hp := Causalean.Stat.probability_real_singleton_tsum p
    have hq := Causalean.Stat.probability_real_singleton_tsum q
    simp only [tsum_fintype] at hp hq
    rw [hp, hq]; ring
  have hgap : p.real A - q.real A =
      (1/2 : ℝ) * ∑ x, |p.real {x} - q.real {x}| := by
    rw [Causalean.Stat.probability_measureReal_eq_tsum_singletons p A hA,
      Causalean.Stat.probability_measureReal_eq_tsum_singletons q A hA]
    simp only [tsum_fintype, ← Finset.sum_sub_distrib]
    have hpoint : ∀ x : α,
        A.indicator (fun x => p.real {x}) x - A.indicator (fun x => q.real {x}) x =
          (|p.real {x} - q.real {x}| + (p.real {x} - q.real {x}))/2 := by
      intro x
      by_cases hx : 0 ≤ p.real {x} - q.real {x}
      · simp [Set.indicator, A, sub_nonneg.mp hx, abs_of_nonneg hx]
      · simp [Set.indicator, A,
          show ¬ q.real {x} ≤ p.real {x} from fun h => hx (sub_nonneg.mpr h),
          abs_of_neg (lt_of_not_ge hx)]
    simp_rw [hpoint]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hzero]
    ring
  apply le_antisymm
  · simpa only [tsum_fintype] using Causalean.Stat.tvDist_le_half_tsum_singleton_abs p q
  · rw [← hgap]
    exact (le_abs_self _).trans (Causalean.Stat.abs_measureReal_sub_le_tvDist hA)

/-- Assume [positive dimension](hyp:hd). [Finite-sum TV agrees with the measure-theoretic testing distance](goal). -/
-- @node: tvFromUniform_eq_tvDist
lemma tvFromUniform_eq_tvDist (p : Measure (PairedSymbol d)) [IsProbabilityMeasure p] (hd : 0 < d) :
    tvFromUniform p = Causalean.Stat.tvDist p (pairedUniform d) := by
  have hcube : (fun _ : Fin d => (0 : ℝ)) ∈ parameterCube d := by
    intro j; norm_num
  have hprob := pairedFamily_subset_simplex hd (Set.mem_image_of_mem pairedLaw hcube)
  have : IsProbabilityMeasure (pairedUniform d) := hprob
  have hmass : ∀ v : PairedSymbol d, (pairedUniform d).real {v} = 1/(2*d) := by
    intro v
    unfold pairedUniform pairedLaw
    rw [atomLaw_real_singleton]
    · simp
    · intro a; simp
  rw [finite_tvDist_eq_half_sum]
  simp_rw [hmass]
  rfl

/-- Assume [the stated theta condition](hyp:hTheta) and [positive dimension](hyp:hd). [The paired target is one half of the signed norm](goal). -/
-- @node: tvFromUniform_pairedLaw
lemma tvFromUniform_pairedLaw (theta : Fin d → ℝ) (hTheta : theta ∈ parameterCube d) (hd : 0 < d) :
    tvFromUniform (pairedLaw theta) = signedNorm theta/2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmass : ∀ v : PairedSymbol d,
      0 ≤ (1 + signVal v.2 * theta v.1) / (2*d) := by
    intro v
    apply div_nonneg _ (by positivity)
    have h := hTheta v.1
    cases v.2 <;> simp only [signVal, Bool.false_eq_true, ↓reduceIte] <;> linarith [h.1, h.2]
  unfold tvFromUniform pairedLaw
  simp_rw [atomLaw_real_singleton _ hmass]
  rw [Fintype.sum_prod_type]
  have hcell : ∀ j : Fin d, ∑ s : Bool,
      |(1 + signVal s * theta j)/(2*d) - 1/(2*d)| = |theta j| / d := by
    intro j
    simp only [Fintype.sum_bool, signVal, Bool.false_eq_true, ↓reduceIte, one_mul]
    have hp : (1 + theta j)/(2*d) - 1/(2*d) = theta j/(2*d) := by ring
    have hn : (1 + -1 * theta j)/(2*d) - 1/(2*d) = -(theta j/(2*d)) := by ring
    rw [hp, hn, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2*d)]
    field_simp
    <;> ring
  simp_rw [hcell]
  rw [← Finset.sum_div]
  unfold signedNorm
  ring

end CausalSmith.Stat.LdpOptvalueUniformFrontier
