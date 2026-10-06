module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockLaw
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ElbowAlgebra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Good-event probability for hidden source counts
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Unrevealed source labels, counted in the source index type, are bounded by total capacity.  [For the stated data and conditions](hyp:n,B,d,H,hH), [the stated conclusion holds](goal). -/
-- @node: unrevealed_count_le_capacity
lemma unrevealed_count_le_capacity (n B d : ℕ) (H : OffDiag (Fin n) → Bool)
    (hH : ValidRetainedGraph n B d H) :
    (Finset.univ.filter (fun j => sourceReveals n B d H j = false)).card ≤
      undiscovered n B d H := by
  have hmn : B * d ≤ n := by have := hH.1; omega
  let emb : Fin (B * d) → Fin n := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hmn⟩
  have hc : (Finset.univ.filter (fun j => sourceReveals n B d H j = false)).card =
      hiddenTreated n B d H (fun _ => true) := by
    unfold hiddenTreated
    apply Finset.card_bij (fun j _ => emb j)
    · intro j hj
      have hnoreveal : ¬ ∃ i : Fin n, ∃ hji : emb j ≠ i, H ⟨(emb j,i),hji⟩ = true := by
        intro he
        have hf := (Finset.mem_filter.mp hj).2
        have ht : sourceReveals n B d H j = true := by
          simp only [sourceReveals, decide_eq_true_eq]
          exact ⟨emb j, rfl, he⟩
        rw [ht] at hf
        contradiction
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt, rfl, hnoreveal⟩
    · intro a ha b hb hab
      exact Fin.ext (congrArg (fun j : Fin n => j.val) hab)
    · intro j hj
      obtain ⟨hjlt, _, hjnone⟩ := (Finset.mem_filter.mp hj).2
      refine ⟨⟨j.val, hjlt⟩, ?_, Fin.ext rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [sourceReveals, decide_eq_false_iff_not]
      rintro ⟨v, hv, i, hvi, he⟩
      have hvj : v = j := Fin.ext hv
      subst v
      exact hjnone ⟨i, hvi, he⟩
  rw [hc]
  exact hiddenTreated_le n B d H hH (fun _ => true)

/-- The inverse-third moment of the hidden count factors over independent source reveals.  [For the stated data and conditions](hyp:m,p,hp), [the stated conclusion holds](goal). -/
-- @node: unrevealed_inverse_third_moment
lemma unrevealed_inverse_third_moment (m : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ r : Fin m → Bool,
      (1 / 3 : ℝ) ^ (Finset.univ.filter (fun j => r j = false)).card
      ∂(Measure.pi (fun _ : Fin m => bernoulliLaw p))) =
      (p + (1 - p) / 3) ^ m := by
  let := bernoulliLaw_probability p hp
  have hprod (r : Fin m → Bool) :
      (1 / 3 : ℝ) ^ (Finset.univ.filter (fun j => r j = false)).card =
        ∏ j, (if r j = false then (1 / 3 : ℝ) else 1) := by
    rw [← Finset.prod_const]
    rw [Finset.prod_filter]
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin m) (b : Bool) =>
    if b = false then (1 / 3 : ℝ) else 1)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [bernoulliLaw, integral_add_measure, integral_smul_measure, integral_smul_measure]
  · simp [ENNReal.toReal_ofReal hp.1, ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)]
    ring
  · exact (Integrable.of_finite (μ := Measure.dirac false)).smul_measure (by finiteness)
  · exact (Integrable.of_finite (μ := Measure.dirac true)).smul_measure (by finiteness)

/-- The fourth-power form avoids numerical approximations in the binomial tail constant.  [For the stated data and conditions](hyp:m,hm), [the stated conclusion holds](goal). -/
-- @node: inverse_third_tail_constant
lemma inverse_third_tail_constant (m : ℕ) (hm : 32 ≤ m) :
    (2 / 3 : ℝ) ^ m / (1 / 3 : ℝ) ^ ((m : ℝ) / 4) ≤ 1 / 16 := by
  have ht : 0 < (1 / 3 : ℝ) ^ ((m : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hfour : ((2 / 3 : ℝ) ^ m / (1 / 3 : ℝ) ^ ((m : ℝ) / 4)) ^ 4 =
      (16 / 27 : ℝ) ^ m := by
    rw [div_pow, ← Real.rpow_mul_natCast (by norm_num)]
    have he : (m : ℝ) / 4 * (4 : ℕ) = m := by push_cast; ring
    rw [he, Real.rpow_natCast, ← pow_mul, mul_comm m 4, pow_mul, ← div_pow]
    norm_num
  have hb : (16 / 27 : ℝ) ^ m ≤ (16 / 27 : ℝ) ^ 32 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hbound : (16 / 27 : ℝ) ^ 32 ≤ (1 / 16 : ℝ) ^ 4 := by norm_num
  have hpow := hfour ▸ hb.trans hbound
  exact le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 1 / 16) hpow

/-- Markov's inequality applied to the inverse-third count moment gives the required tail.  [For the stated data and conditions](hyp:m,p,hm,hp,hphalf), [the stated conclusion holds](goal). -/
-- @node: unrevealed_count_small_probability
lemma unrevealed_count_small_probability (m : ℕ) (p : ℝ)
    (hm : 32 ≤ m) (hp : p ∈ Set.Icc 0 1) (hphalf : p ≤ 1 / 2) :
    (Measure.pi (fun _ : Fin m => bernoulliLaw p)).real
      {r | ((Finset.univ.filter (fun j => r j = false)).card : ℝ) < (m : ℝ) / 4} ≤
        1 / 16 := by
  let := bernoulliLaw_probability p hp
  let μ := Measure.pi (fun _ : Fin m => bernoulliLaw p)
  let t : ℝ := (1 / 3 : ℝ) ^ ((m : ℝ) / 4)
  let f : (Fin m → Bool) → ℝ := fun r =>
    (1 / 3 : ℝ) ^ (Finset.univ.filter (fun j => r j = false)).card
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := f)
    (Filter.Eventually.of_forall (fun r => by dsimp [f]; positivity))
    (show Integrable f μ from Integrable.of_finite) t
  have hsub : {r : Fin m → Bool |
      ((Finset.univ.filter (fun j => r j = false)).card : ℝ) < (m : ℝ) / 4} ⊆
        {r | t ≤ f r} := by
    intro r hr
    dsimp [t, f]
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hr.le
  have htail := measureReal_mono (μ := μ) hsub
  have hmean : (∫ r, f r ∂μ) ≤ (2 / 3 : ℝ) ^ m := by
    rw [unrevealed_inverse_third_moment m p hp]
    apply pow_le_pow_left₀
    · have := hp.1; linarith
    · linarith
  have hdiv : μ.real {r | t ≤ f r} ≤ (2 / 3 : ℝ) ^ m / t := by
    apply (le_div_iff₀ ht).mpr
    simpa only [mul_comm] using hmarkov.trans hmean
  exact htail.trans (hdiv.trans (inverse_third_tail_constant m hm))

/-- In the low-retention regime with at least thirty-two sources, the bad hidden-count event has
probability at most one sixteenth.  [For the stated data and conditions](hyp:n,B,d,q,D,hB,hd,hfit,hq,hphalf,hm,ha,hw,hi), [the stated conclusion holds](goal). -/
-- @node: hidden_count_good_event_of_retention_half
lemma hidden_count_good_event_of_retention_half (n B d : ℕ) (q : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1) (hphalf : retentionP d q ≤ (1 / 2 : ℝ))
    (hm : 32 ≤ B * d) (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D) :
    (retainedGraphMarginal n B d D).real {H | (undiscovered n B d H : ℝ) < (B * d : ℕ) / 4} ≤
      (1 / 16 : ℝ) := by
  let := design_isProbabilityMeasure D q ha hw hi
  let p := retentionP d q
  have hp : p ∈ Set.Icc 0 1 := retentionP_mem_Icc d q hq
  let μ := retainedGraphMarginal n B d D
  have hlaw : μ.map (sourceReveals n B d) =
      Measure.pi (fun _ : Fin (B * d) => bernoulliLaw p) :=
    block_reveal_law n B d q D hB hd hfit hq ha hw hi
  have hsub : ∀ᵐ H ∂μ,
      H ∈ {H | (undiscovered n B d H : ℝ) < (B * d : ℕ) / 4} →
      H ∈ (sourceReveals n B d) ⁻¹'
        {r | ((Finset.univ.filter (fun j => r j = false)).card : ℝ) < (B * d : ℕ) / 4} := by
    filter_upwards [retainedGraphMarginal_valid n B d D hfit] with H hH
    intro hsmall
    have hc : ((Finset.univ.filter (fun j => sourceReveals n B d H j = false)).card : ℝ) ≤
        undiscovered n B d H := by exact_mod_cast unrevealed_count_le_capacity n B d H hH
    exact hc.trans_lt hsmall
  have hmeasure := measure_mono_ae hsub
  have hfinite : μ ((sourceReveals n B d) ⁻¹'
      {r | ((Finset.univ.filter (fun j => r j = false)).card : ℝ) < (B * d : ℕ) / 4}) ≠ ⊤ := by
    rw [← Measure.map_apply (measurable_of_finite _) (by measurability), hlaw]
    let := bernoulliLaw_probability p hp
    finiteness
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  have htail := unrevealed_count_small_probability (B * d) p hm hp hphalf
  rw [← hlaw, map_measureReal_apply (measurable_of_finite _) (by measurability)] at htail
  exact hreal.trans htail

/-- The audit-rate condition implies the source-retention condition used by the count tail.  [For the stated data and conditions](hyp:n,B,d,q,D,hB,hd,hfit,hq,hqd,hm,ha,hw,hi), [the stated conclusion holds](goal). -/
-- @node: hidden_count_good_event
lemma hidden_count_good_event (n B d : ℕ) (q : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1) (hqd : q * d ≤ (1 / 2 : ℝ))
    (hm : 32 ≤ B * d) (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D) :
    (retainedGraphMarginal n B d D).real {H | (undiscovered n B d H : ℝ) < (B * d : ℕ) / 4} ≤
      (1 / 16 : ℝ) := by
  apply hidden_count_good_event_of_retention_half n B d q D hB hd hfit hq _ hm ha hw hi
  exact (reveal_probability_le_mul d q hq).trans (by simpa [mul_comm] using hqd)

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
