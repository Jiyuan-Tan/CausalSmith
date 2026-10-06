module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.TestingPriors
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.TUniformPrivateUpper
/-! Matched private absolute-risk frontier over all total randomized mechanisms in the same
observation experiment, attained above by the explicit publicly tuned release. -/
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign
/-- A nonempty finite uniform prior is a probability measure.  [the theorem's stated inputs and assumptions](hyp:hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,s,F). -/
-- @node: finiteProductMixture_probability
lemma finiteProductMixture_probability (n s : ℕ) (F : Fin s → CausalLaw)
    (hs : 0 < s) : IsProbabilityMeasure (finiteProductMixture n s F) := by
  have hprob : ∀ i, IsProbabilityMeasure (dataLaw n (F i)) := by
    intro i
    let : IsProbabilityMeasure (Pobs (F i)) :=
      Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
    unfold dataLaw
    infer_instance
  constructor
  simp only [finiteProductMixture, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply, measure_univ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.ne_of_gt hs)) (by simp)

/-- Kernel composition distributes over a finite sum of input laws.  [the theorem's stated inputs and assumptions](hyp:n,M,s,Q), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,B). -/
-- @node: prior_comp_finsetSum
lemma prior_comp_finsetSum {ι B : Type*} [MeasurableSpace B]
    (n : ℕ) (M : Kernel (Dataset n) B) (s : Finset ι) (Q : ι → Measure (Dataset n)) :
    M ∘ₘ (∑ i ∈ s, Q i) = ∑ i ∈ s, M ∘ₘ Q i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, Measure.comp_add, ih]

/-- Prior-averaged loss at a common target is bounded by the maximal class risk,
including when the latter is infinite.  [the theorem's stated inputs and assumptions](hyp:hs,M,target,hF), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,s,F). -/
-- @node: finite_prior_loss_le_worstRisk
lemma finite_prior_loss_le_worstRisk (n s : ℕ) (F : Fin s → CausalLaw)
    (hs : 0 < s) (M : Kernel (Dataset n) ℝ) (target : ℝ)
    (hF : ∀ i, CompleteModel (F i) ∧ theta (F i) = target) :
    (∫⁻ u, ENNReal.ofReal |u - target| ∂(M ∘ₘ finiteProductMixture n s F)) ≤
      worstRisk n M := by
  rw [finiteProductMixture, Measure.comp_smul, prior_comp_finsetSum,
    lintegral_smul_measure, lintegral_finsetSum_measure]
  have hbound : ∀ i : Fin s,
      (∫⁻ u, ENNReal.ofReal |u - target| ∂(M ∘ₘ dataLaw n (F i))) ≤ worstRisk n M := by
    intro i
    rw [← (hF i).2]
    exact le_iSup_of_le (F i) (le_iSup_of_le (hF i).1 le_rfl)
  calc
    _ ≤ (s : ℝ≥0∞)⁻¹ * ∑ _i : Fin s, worstRisk n M :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hbound i) (zero_le)
    _ = worstRisk n M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, ENNReal.inv_mul_cancel
        (by exact_mod_cast (Nat.ne_of_gt hs)) (by simp), one_mul]

/-- A real error event of probability at least three eighths forces absolute loss.  [the theorem's stated inputs and assumptions](hyp:target,a,ha,hp), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:L). -/
-- @node: absolute_loss_of_error_probability
lemma absolute_loss_of_error_probability (L : Measure ℝ) [IsProbabilityMeasure L]
    (target a : ℝ) (ha : 0 ≤ a)
    (hp : 3 / 8 ≤ L.real {u | a ≤ dist u target}) :
    ENNReal.ofReal (a * (3 / 8)) ≤ ∫⁻ u, ENNReal.ofReal |u - target| ∂L := by
  have hm : Measurable (fun u : ℝ => ENNReal.ofReal |u - target|) := by fun_prop
  have hmarkov := mul_meas_ge_le_lintegral (μ := L) hm (ENNReal.ofReal a)
  have hset : {u : ℝ | ENNReal.ofReal a ≤ ENNReal.ofReal |u - target|} =
      {u | a ≤ dist u target} := by
    ext u
    simp only [Set.mem_setOf_eq, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  rw [hset] at hmarkov
  have hmass : ENNReal.ofReal (3 / 8 : ℝ) ≤ L {u | a ≤ dist u target} := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top L _)]
    exact ENNReal.ofReal_le_ofReal hp
  rw [ENNReal.ofReal_mul ha]
  exact (mul_le_mul_of_nonneg_left hmass (zero_le)).trans hmarkov

/-- Le Cam's two-error inequality and finite-prior averaging give the scalar converse.  [the theorem's stated inputs and assumptions](hyp:F0,F1,hs0,hs1,M,Delta,hd,hF0,hF1,htv), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,s0,s1). -/
-- @node: finite_priors_scalar_lower
lemma finite_priors_scalar_lower (n s0 s1 : ℕ)
    (F0 : Fin s0 → CausalLaw) (F1 : Fin s1 → CausalLaw)
    (hs0 : 0 < s0) (hs1 : 0 < s1) (M : Kernel (Dataset n) ℝ) [IsMarkovKernel M]
    (Delta : ℝ) (hd : 0 ≤ Delta)
    (hF0 : ∀ i, CompleteModel (F0 i) ∧ theta (F0 i) = 0)
    (hF1 : ∀ i, CompleteModel (F1 i) ∧ theta (F1 i) = Delta)
    (htv : TV (M ∘ₘ finiteProductMixture n s0 F0)
      (M ∘ₘ finiteProductMixture n s1 F1) ≤ 1 / 4) :
    ENNReal.ofReal (3 * Delta / 16) ≤ worstRisk n M := by
  let L0 := M ∘ₘ finiteProductMixture n s0 F0
  let L1 := M ∘ₘ finiteProductMixture n s1 F1
  let : IsProbabilityMeasure (finiteProductMixture n s0 F0) :=
    finiteProductMixture_probability n s0 F0 hs0
  let : IsProbabilityMeasure (finiteProductMixture n s1 F1) :=
    finiteProductMixture_probability n s1 F1 hs1
  have hsep : 2 * (Delta / 2) ≤ dist (0 : ℝ) Delta := by
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hd]
    linarith
  have htest := Causalean.Stat.one_sub_tvDist_le_error_sum
    (P₀ := L0) (P₁ := L1) measurable_id hsep
  have hsum : 3 / 4 ≤ L0.real {u | Delta / 2 ≤ dist u 0} +
      L1.real {u | Delta / 2 ≤ dist u Delta} := by
    change TV L0 L1 ≤ 1 / 4 at htv
    simp only [id_eq] at htest
    linarith
  have hcases : 3 / 8 ≤ L0.real {u | Delta / 2 ≤ dist u 0} ∨
      3 / 8 ≤ L1.real {u | Delta / 2 ≤ dist u Delta} := by
    by_contra h
    push_neg at h
    linarith
  have heq : 3 * Delta / 16 = (Delta / 2) * (3 / 8) := by ring
  rw [heq]
  rcases hcases with h0 | h1
  · exact (absolute_loss_of_error_probability L0 0 (Delta / 2) (by positivity) h0).trans
      (finite_prior_loss_le_worstRisk n s0 F0 hs0 M 0 hF0)
  · exact (absolute_loss_of_error_probability L1 Delta (Delta / 2) (by positivity) h1).trans
      (finite_prior_loss_le_worstRisk n s1 F1 hs1 M Delta hF1)

/-- [The minimax risk lies between the specified fixed multiples of the benchmark. The total
publicly tuned kernel attains the upper bound across the entire complete model.](goal)
The [public parameters and their domains](hyp:n,epsilon,hn,he) and
the [Efron--Stein gate](hyp:efronStein_of_gate),
[bounded-differences gate](hyp:boundedDifferences_of_gate), and
[Cayley gate](hyp:cayley_of_gate) specify the conditional scope. -/
-- @node: thm:matched-risk-frontier
theorem matched_risk_frontier (efronStein_of_gate : EfronSteinReplacement)
    (boundedDifferences_of_gate : BoundedDifferencesMGF) (cayley_of_gate : CayleyLabeledTreeCount)
    (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    ENNReal.ofReal ((2 : ℝ)^(-20 : ℤ)*rate n epsilon) ≤ privateMinimaxRisk n epsilon ∧
    privateMinimaxRisk n epsilon ≤ ENNReal.ofReal (2^18*rate n epsilon) ∧
    IsMarkovKernel (publicTunedRelease n epsilon) ∧
    PrivateKernel n epsilon (publicTunedRelease n epsilon) ∧
    worstRisk n (publicTunedRelease n epsilon) ≤ ENNReal.ofReal (2^18*rate n epsilon) := by
  obtain ⟨s0, s1, F0, F1, Delta, hs0, hs1, hd, hF0, hF1, _, htv⟩ :=
    frontier_testing_priors boundedDifferences_of_gate cayley_of_gate n epsilon hn he
  have hr : 0 < rate n epsilon := rate_pos n epsilon (by omega)
  have hd0 : 0 ≤ Delta := le_trans (by positivity) hd
  have hlower : ENNReal.ofReal ((2 : ℝ)^(-20 : ℤ) * rate n epsilon) ≤
      privateMinimaxRisk n epsilon := by
    unfold privateMinimaxRisk
    refine le_iInf fun M => le_iInf fun hM => ?_
    let : IsMarkovKernel M := hM.1
    have htest := finite_priors_scalar_lower n s0 s1 F0 F1 hs0 hs1 M Delta hd0
      hF0 hF1 (htv ℝ M hM.2)
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) htest
    have hscale : (2 : ℝ)^(-20 : ℤ) ≤ (3 / 16) * (2 : ℝ)^(-14 : ℤ) := by norm_num
    calc
      _ ≤ ((3 / 16) * (2 : ℝ)^(-14 : ℤ)) * rate n epsilon :=
        mul_le_mul_of_nonneg_right hscale hr.le
      _ = (3 / 16) * ((2 : ℝ)^(-14 : ℤ) * rate n epsilon) := by ring
      _ ≤ (3 / 16) * Delta := mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = _ := by ring
  obtain ⟨_, _, _, _, _, _, _, hmarkov, hprivate, _, _, hrisk, _, _⟩ :=
    uniform_private_upper efronStein_of_gate n 2 epsilon (1 / 4) hn (by omega) he
      ⟨by norm_num, le_rfl⟩
  have hupper : privateMinimaxRisk n epsilon ≤ worstRisk n (publicTunedRelease n epsilon) :=
    iInf_le_of_le (publicTunedRelease n epsilon)
      (iInf_le_of_le ⟨hmarkov, hprivate⟩ le_rfl)
  exact ⟨hlower, hupper.trans hrisk, hmarkov, hprivate, hrisk⟩
end CausalSmith.Stat.PrivateCateRoughdesign
