module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.LowerSplice
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.PairedKernel
public import Causalean.Stat.Minimax.MarkovKernelTransport

/-! Fixed-sample transport from paired L1 estimation to half-budget value. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory

/-- The parameter-free paired randomization as a Mathlib Markov kernel. -/
-- @node: pairedSampleMarkovKernel
@[no_expose]
noncomputable def pairedSampleMarkovKernel (n k : ℕ) :
    Kernel ((Fin n → Fin k) × (Fin n → Fin k)) (Fin n → Obs (2 * k)) :=
  Kernel.ofFunOfCountable (fun x => (pairedSampleKernel n x).toMeasure)

/-- For [n](hyp:n), this instance provides [the stated structure](goal). -/
instance pairedSampleMarkovKernel_isMarkov (n k : ℕ) :
    IsMarkovKernel (pairedSampleMarkovKernel n k) := by
  refine ⟨fun x => ?_⟩
  change IsProbabilityMeasure ((pairedSampleKernel n x).toMeasure)
  infer_instance

/-- The paired Markov kernel sends the fixed two-sample law exactly to the
observed iid law of the normalized paired causal construction. With [the specified inputs and conditions](hyp:n,k,R,S,r,theta,hr,htheta), [the stated relationship holds](goal). -/
-- @node: pairedSampleMarkovKernel_comp_twoSampleLaw
lemma pairedSampleMarkovKernel_comp_twoSampleLaw {n k : ℕ}
    (R S r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (hr : ∀ i, r.1 i = (R.1 i + S.1 i) / 2)
    (htheta : ∀ i, theta.1 i = if R.1 i + S.1 i = 0 then 0
      else (R.1 i - S.1 i) / (8 * (R.1 i + S.1 i))) :
    productLaw (observedMarginal (pairedLaw r theta)) n =
      pairedSampleMarkovKernel n k ∘ₘ twoSampleLaw n (R, S) := by
  apply Measure.ext_iff_singleton.2
  intro z
  rw [Measure.bind_apply (MeasurableSet.singleton z)
    (pairedSampleMarkovKernel n k).aemeasurable, lintegral_fintype]
  simp only [pairedSampleMarkovKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  simpa [mul_comm] using
    (pairedSampleKernel_reproduces R S r theta hr htheta z).symm

/-- Any positive paired-L1 minimax lower bound transfers, with the exact
`1/32` affine scale, to an even-alphabet capacity-active causal instance. With [the specified inputs and conditions](hyp:n,k,hk,epsilon,he,he',L,hL,hlower,T), [the stated relationship holds](goal). -/
-- @node: pairedL1_lower_transport_capacity
lemma pairedL1_lower_transport_capacity {n k : ℕ} (hk : 1 ≤ k)
    (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (L : ℝ) (hL : 0 < L) (hlower : L ≤ twoSampleL1MinimaxRisk n k)
    (T : {f : (Fin n → Obs (2 * k)) → ℝ // Measurable f}) :
    ∃ Q : PotentialLaw (2 * k), Q ∈ capacityHardClass (2 * k) epsilon ∧
      (1 / 32 : ℝ) ^ 2 * (L / 2) ≤
        Causalean.Stat.sqRisk (productLaw (observedMarginal Q) n) T.1
          (budgetValue Q (1 / 2)) := by
  classical
  let r : ProbabilitySimplex k × ProbabilitySimplex k → ProbabilitySimplex k :=
    fun RS => Classical.choose (normalizedPairedParameters RS.1 RS.2)
  let theta : ProbabilitySimplex k × ProbabilitySimplex k → PairedContrasts k :=
    fun RS => Classical.choose (Classical.choose_spec
      (normalizedPairedParameters RS.1 RS.2))
  have hr (RS : ProbabilitySimplex k × ProbabilitySimplex k) :
      ∀ i, (r RS).1 i = (RS.1.1 i + RS.2.1 i) / 2 :=
    (Classical.choose_spec (Classical.choose_spec
      (normalizedPairedParameters RS.1 RS.2))).1
  have ht (RS : ProbabilitySimplex k × ProbabilitySimplex k) :
      ∀ i, (theta RS).1 i = if RS.1.1 i + RS.2.1 i = 0 then 0
        else (RS.1.1 i - RS.2.1 i) / (8 * (RS.1.1 i + RS.2.1 i)) :=
    (Classical.choose_spec (Classical.choose_spec
      (normalizedPairedParameters RS.1 RS.2))).2
  let P := fun RS : ProbabilitySimplex k × ProbabilitySimplex k =>
    twoSampleLaw n RS
  let Q := fun RS : ProbabilitySimplex k × ProbabilitySimplex k =>
    productLaw (observedMarginal (pairedLaw (r RS) (theta RS))) n
  letI : NeZero k := ⟨by omega⟩
  let U : ProbabilitySimplex k :=
    ⟨fun _ => (k : ℝ)⁻¹, by
      constructor
      · intro i
        positivity
      · simp [Finset.sum_const, Fintype.card_fin]
        ⟩
  letI : Nonempty (ProbabilitySimplex k × ProbabilitySimplex k) := ⟨(U, U)⟩
  letI (RS : ProbabilitySimplex k × ProbabilitySimplex k) :
      IsProbabilityMeasure (P RS) := by
    dsimp [P, twoSampleLaw, simplexSampleLaw]
    infer_instance
  have hsource : ∀ sourceEst :
      ((Fin n → Fin k) × (Fin n → Fin k)) → ℝ,
      Measurable sourceEst → Causalean.Stat.UniformlyBounded sourceEst →
      ∃ RS, L / 2 ≤ Causalean.Stat.sqRisk (P RS) sourceEst
        (simplexL1 RS.1 RS.2) := by
    intro sourceEst hmeas _
    let est : TwoSampleEstimator n k := ⟨sourceEst, hmeas⟩
    have hmin : twoSampleL1MinimaxRisk n k ≤
        ⨆ RS, twoSampleL1Risk n est RS := by
      unfold twoSampleL1MinimaxRisk
      unfold Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleL1MinimaxRisk
      simpa [Causalean.Stat.worstCaseRiskReal] using
        (Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
          (fun _ _ => by
            unfold Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleL1Risk
            positivity) est)
    have hstrict : L / 2 < ⨆ RS, twoSampleL1Risk n est RS := by
      have : L / 2 < L := by linarith
      exact this.trans_le (hlower.trans hmin)
    obtain ⟨RS, hRS⟩ :=
      (lt_ciSup_iff (twoSampleL1Risk_bddAbove_all est)).mp hstrict
    exact ⟨RS, by simpa [P, twoSampleL1Risk,
      Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleL1Risk,
      est, Causalean.Stat.sqRisk]
      using hRS.le⟩
  have htransport :=
    Causalean.Stat.forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport
      P Q (pairedSampleMarkovKernel n k)
      (fun RS => simplexL1 RS.1 RS.2) (1 / 32) (3 / 8) (L / 2)
      (by norm_num)
      (fun RS => by simpa [P, Q] using
        (pairedSampleMarkovKernel_comp_twoSampleLaw (n := n)
          RS.1 RS.2 (r RS) (theta RS) (hr RS) (ht RS)))
      hsource T.1 T.2 (by
        obtain ⟨M, hM⟩ := Finite.bddAbove_range (fun z => |T.1 z|)
        refine ⟨max M 0, le_max_right _ _, fun z => ?_⟩
        exact (hM ⟨z, rfl⟩).trans (le_max_left _ _))
  obtain ⟨RS, hRS⟩ := htransport
  let Q0 := pairedLaw (r RS) (theta RS)
  have hcompletion : PairedCompletion Q0 (r RS) (theta RS) :=
    pairedLaw_completion (r RS) (theta RS)
  have hbinding := pairedCompletion_bindingValue Q0 (r RS) (theta RS)
    hcompletion epsilon he he' hk
  refine ⟨Q0, ?_, ?_⟩
  · exact ⟨pairedCompletion_modelClass hk epsilon he he' Q0 (r RS) (theta RS)
      hcompletion, pairedCompletion_budgetValue_one Q0 (r RS) (theta RS)
      hcompletion, fun j hj => pairedCompletion_effect_bounds Q0 (r RS)
      (theta RS) hcompletion j hj, hbinding.1⟩
  · rw [show budgetValue Q0 (1 / 2) =
        (1 / 32 : ℝ) * simplexL1 RS.1 RS.2 + 3 / 8 by
      rw [normalizedPairedBudgetValue hk epsilon he he' RS.1 RS.2
        (r RS) (theta RS) Q0 hcompletion (hr RS) (ht RS)]
      ring]
    simpa [Q, Q0] using hRS

/-- The same transport uses any supplied sampling-law family satisfying the
paper's `IidSampling` equality, rather than a definitionally chosen product. With [the specified inputs and conditions](hyp:n,k,hk,epsilon,he,he',L,hL,hlower,mu,hmu,T), [the stated relationship holds](goal). -/
-- @node: pairedL1_lower_transport_capacity_iid
lemma pairedL1_lower_transport_capacity_iid {n k : ℕ} (hk : 1 ≤ k)
    (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (L : ℝ) (hL : 0 < L) (hlower : L ≤ twoSampleL1MinimaxRisk n k)
    (mu : PotentialLaw (2 * k) → Measure (Fin n → Obs (2 * k)))
    (hmu : ∀ Q, IidSampling (observedMarginal Q) (mu Q))
    (T : {f : (Fin n → Obs (2 * k)) → ℝ // Measurable f}) :
    ∃ Q : PotentialLaw (2 * k), Q ∈ capacityHardClass (2 * k) epsilon ∧
      (1 / 32 : ℝ) ^ 2 * (L / 2) ≤
        Causalean.Stat.sqRisk (mu Q) T.1 (budgetValue Q (1 / 2)) := by
  obtain ⟨Q, hQ, hrisk⟩ := pairedL1_lower_transport_capacity hk epsilon he he'
    L hL hlower T
  refine ⟨Q, hQ, ?_⟩
  rw [hmu Q]
  exact hrisk

end CausalSmith.Stat.DiscreteBudgetvalueCurve
