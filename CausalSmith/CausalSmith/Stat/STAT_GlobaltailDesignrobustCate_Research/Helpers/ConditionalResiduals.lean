module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedCellTail
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedMeasurability
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.MassBudget

public import Mathlib.MeasureTheory.Integral.Pi

/-! # Centered bounded outcome residuals on single-observation design fibers

The probabilistic input to equations (10)--(13) of the finite-bandwidth
roadmap is derived from the law class. These lemmas establish the single-unit
conditional mean and boundedness before the independent-product transfer.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory ProbabilityTheory

/-- An almost-everywhere covariate fact also holds under the joint XA marginal. -/
-- @node: ae_design_of_ae_xLaw
lemma ae_design_of_ae_xLaw {d : ℕ} (P : Law d) {p : (Fin d → ℝ) → Prop}
    (hp : ∀ᵐ x ∂P.xLaw, p x) :
    ∀ᵐ xa ∂P.full.map (fun u : Full d => (u.1, u.2.1)), p xa.1 := by
  apply ae_of_ae_map (by fun_prop : AEMeasurable
    (Prod.fst : (Fin d → ℝ) × Bool → (Fin d → ℝ)) _)
  rw [Measure.map_map measurable_fst (by fun_prop)]
  exact hp

/-- The selected potential outcome inherits the common outcome bound. -/
-- @node: latent_observedResponse_abs_le
lemma latent_observedResponse_abs_le {d : ℕ} (P : Law d) (M : ℝ)
    (hbound : BoundedOutcomes P M) :
    ∀ᵐ u ∂P.full, |if u.2.1 then u.2.2.2 else u.2.2.1| ≤ M := by
  filter_upwards [hbound] with u hu
  cases u.2.1 <;> simp only [Bool.false_eq_true, if_false, if_true]
  · exact hu.1
  · exact hu.2

/-- Disintegration preserves the response bound on almost every XA fiber. -/
-- @node: conditional_observedResponse_abs_le
lemma conditional_observedResponse_abs_le {d : ℕ} (P : Law d) (M : ℝ)
    [IsProbabilityMeasure P.full] (hbound : BoundedOutcomes P M) :
    ∀ᵐ xa ∂P.full.map (fun u : Full d => (u.1, u.2.1)),
      ∀ᵐ y ∂condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full xa, |y| ≤ M := by
  have hY : Measurable (fun u : Full d =>
      if u.2.1 then u.2.2.2 else u.2.2.1) := by
    exact Measurable.ite
      ((measurableSet_singleton true).preimage (by fun_prop))
      (by fun_prop) (by fun_prop)
  apply Measure.ae_ae_of_ae_comp
  rw [condDistrib_comp_map (by fun_prop) hY.aemeasurable]
  exact (ae_map_iff hY.aemeasurable (measurableSet_le (by fun_prop) measurable_const)).2
    (latent_observedResponse_abs_le P M hbound)

/-- Causal identification gives the treated fiber mean under the full XA
marginal, including its treatment-false fibers through an implication. -/
-- @node: treated_conditional_mean_on_design
lemma treated_conditional_mean_on_design {d : ℕ} (β γ C L M : ℝ)
    (P : Law d) (hP : LawClass d β γ C L M P) :
    let : IsProbabilityMeasure P.full := hP.iid.1
    ∀ᵐ xa ∂P.full.map (fun u : Full d => (u.1, u.2.1)), xa.2 = true →
      (∫ y, y ∂condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full xa) = P.mu1 xa.1 := by
  let : IsProbabilityMeasure P.full := hP.iid.1
  have he : AEMeasurable P.e P.xLaw := by
    rw [hP.uniformDesign]
    exact (propensity_integrableOn_cube P hP.measurablePropensity).aemeasurable
  have hm : AEMeasurable P.mu1 P.xLaw := by
    rw [hP.uniformDesign]
    exact (holderOnCube_continuousOn hP.parameters.2.1 hP.treatedHolder).aemeasurable
      (by simp [cube])
  have hs : ∀ᵐ u ∂P.full, u.1 ∈ cube d := by
    apply ae_of_ae_map (by fun_prop : AEMeasurable (Prod.fst : Full d → _) P.full)
    change ∀ᵐ x ∂P.xLaw, x ∈ cube d
    rw [hP.uniformDesign]
    exact self_mem_ae_restrict (by simp [cube])
  have hid := (causal_identification P C γ M hP.semantics he hm hs
    hP.boundedOutcomes hP.consistency hP.exchangeability hP.globalTail
    hP.parameters.2.2.1).2
  filter_upwards [ae_design_of_ae_xLaw P hid] with xa hxa htreated
  rcases xa with ⟨x, a⟩
  change a = true at htreated
  subst a
  exact hxa

/-- The masked treated residual on almost every design fiber is measurable,
integrable, centered, and bounded by twice the outcome bound. Treatment-false
fibers contribute the zero residual. -/
-- @node: treated_conditional_residual_properties
lemma treated_conditional_residual_properties {d : ℕ} (β γ C L M : ℝ)
    (P : Law d) (hP : LawClass d β γ C L M P) :
    let : IsProbabilityMeasure P.full := hP.iid.1
    ∀ᵐ xa ∂P.full.map (fun u : Full d => (u.1, u.2.1)),
      let ν := condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full xa
      let ξ : ℝ → ℝ := fun y => if xa.2 = true then y - P.mu1 xa.1 else 0
      Measurable ξ ∧ Integrable ξ ν ∧ (∀ᵐ y ∂ν, |ξ y| ≤ 2 * M) ∧
        (∫ y, ξ y ∂ν) = 0 := by
  let : IsProbabilityMeasure P.full := hP.iid.1
  have hmu : ∀ᵐ x ∂P.xLaw, P.mu1 x ∈ Set.Icc (-M) M := by
    have hs : ∀ᵐ x ∂P.xLaw, x ∈ cube d := by
      rw [hP.uniformDesign]
      exact self_mem_ae_restrict (by simp [cube])
    exact hs.mono (fun x hx => hP.semantics.2.2.2.2.1 x hx)
  filter_upwards [conditional_observedResponse_abs_le P M hP.boundedOutcomes,
    treated_conditional_mean_on_design β γ C L M P hP,
    ae_design_of_ae_xLaw P hmu] with xa hbound hmean hmu
  dsimp only
  have hM : 0 ≤ M := hP.parameters.2.2.2.2.2.le
  by_cases ha : xa.2 = true
  · simp only [ha, if_true]
    have hy : Integrable (fun y : ℝ => y) (condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full xa) :=
      Integrable.of_mem_Icc (-M) M (by fun_prop)
        (hbound.mono (fun y hy => abs_le.mp hy))
    refine ⟨by fun_prop, hy.sub (integrable_const _), ?_, ?_⟩
    · filter_upwards [hbound] with y hy
      calc
        |y - P.mu1 xa.1| ≤ |y| + |P.mu1 xa.1| := by
          simpa using abs_sub_le y 0 (P.mu1 xa.1)
        _ ≤ M + M := add_le_add hy (abs_le.mpr hmu)
        _ = 2 * M := by ring
    · rw [integral_sub hy (integrable_const _), integral_const]
      simpa using sub_eq_zero.mpr (hmean ha)
  · simp only [ha]
    exact ⟨measurable_const, integrable_const _,
      Filter.Eventually.of_forall (fun _ => by
        simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)),
      integral_zero _ _⟩

/-- Independent outcome draws on the single-unit conditional fibers give
independent, centered, bounded masked residuals on almost every complete design.
The centering and bounds are derived, rather than supplied as fiber assumptions. -/
-- @node: treated_productFiber_residual_properties
lemma treated_productFiber_residual_properties {d n : ℕ} (β γ C L M : ℝ)
    (P : Law d) (hP : LawClass d β γ C L M P) :
    let : IsProbabilityMeasure P.full := hP.iid.1
    ∀ᵐ design : Fin n → (Fin d → ℝ) × Bool ∂Measure.pi
        (fun _ => P.full.map (fun u : Full d => (u.1, u.2.1))),
      let ν := fun i : Fin n => condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full (design i)
      let ξ := fun i (y : Fin n → ℝ) =>
        if (design i).2 = true then y i - P.mu1 (design i).1 else 0
      iIndepFun ξ (Measure.pi ν) ∧
        (∀ i, Measurable (ξ i)) ∧
        (∀ i, ∀ᵐ y ∂Measure.pi ν, |ξ i y| ≤ 2 * M) ∧
        (∀ i, ∫ y, ξ i y ∂Measure.pi ν = 0) := by
  let : IsProbabilityMeasure P.full := hP.iid.1
  let : IsProbabilityMeasure (P.full.map (fun u : Full d => (u.1, u.2.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hprops := treated_conditional_residual_properties β γ C L M P hP
  have hall : ∀ᵐ design : Fin n → (Fin d → ℝ) × Bool ∂Measure.pi
      (fun _ => P.full.map (fun u : Full d => (u.1, u.2.1))),
      ∀ i,
        let ν := condDistrib
          (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
          (fun u : Full d => (u.1, u.2.1)) P.full (design i)
        let ξ : ℝ → ℝ := fun y =>
          if (design i).2 = true then y - P.mu1 (design i).1 else 0
        Measurable ξ ∧ Integrable ξ ν ∧ (∀ᵐ y ∂ν, |ξ y| ≤ 2 * M) ∧
          (∫ y, ξ y ∂ν) = 0 :=
    Filter.eventually_all.mpr (fun i =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n =>
        P.full.map (fun u : Full d => (u.1, u.2.1))) (i := i)).eventually hprops)
  filter_upwards [hall] with design hd
  dsimp only at hd ⊢
  refine ⟨iIndepFun_pi (fun i => (hd i).1.aemeasurable), ?_, ?_, ?_⟩
  · intro i
    exact (hd i).1.comp (measurable_pi_apply i)
  · intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun i : Fin n => condDistrib
      (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
      (fun u : Full d => (u.1, u.2.1)) P.full (design i)) (i := i)).eventually
        (hd i).2.2.1
  · intro i
    exact (integral_comp_eval (μ := fun i : Fin n => condDistrib
      (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
      (fun u : Full d => (u.1, u.2.1)) P.full (design i))
      (i := i) (hd i).1.aestronglyMeasurable).trans (hd i).2.2.2

/-- The actual clipped estimator has the roadmap cell-tail bound on the
product outcome fiber of almost every complete design, including zero counts. -/
-- @node: treated_balancedEstimator_productFiber_cell_tail
lemma treated_balancedEstimator_productFiber_cell_tail (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : Law d, ∀ hP : LawClass d β γ C L M P,
      let : IsProbabilityMeasure P.full := hP.iid.1
      ∀ n j : ℕ, ∀ᵐ design : Fin n → (Fin d → ℝ) × Bool ∂Measure.pi
          (fun _ => P.full.map (fun u : Full d => (u.1, u.2.1))),
        let ν := fun i : Fin n => condDistrib
          (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
          (fun u : Full d => (u.1, u.2.1)) P.full (design i)
        let s : Fin n → Obs d := fun i => ((design i).1, (design i).2, 0)
        let S := fun (y : Fin n → ℝ) i => ((design i).1, (design i).2, y i)
        ∀ (Q : Fin d → Fin (2 ^ j)) (t : ℝ), 0 ≤ t →
          (Measure.pi ν).real {y | ∃ x ∈ cube d, cellIndex d j x = Q ∧
            B * L * (dyadicWidth j) ^ β + t <
              |balancedEstimator (S y) j β M x - P.mu1 x|} ≤
            (2 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)) *
              Real.exp (-(referenceLowerEigenvalue d (polynomialOrder β) ^ 2 /
                (32 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ))) *
                  (minimumCellCount s true j (polynomialOrder β)
                    (normingSubcells d β).radius Q : ℝ) * t ^ 2 / M ^ 2) := by
  obtain ⟨B, hB, htail⟩ := treated_balancedEstimator_fixedDesign_cell_tail
    d β γ C L M hparam
  refine ⟨B, hB, ?_⟩
  intro P hP
  let : IsProbabilityMeasure P.full := hP.iid.1
  dsimp only
  intro n j
  filter_upwards [treated_productFiber_residual_properties (n := n) β γ C L M P hP]
    with design hd
  dsimp only at hd ⊢
  let ν : Fin n → Measure ℝ := fun i => condDistrib
    (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
    (fun u : Full d => (u.1, u.2.1)) P.full (design i)
  exact htail P hP (Measure.pi ν) n j
    (fun i => ((design i).1, (design i).2, 0))
    (fun y i => ((design i).1, (design i).2, y i))
    (fun _ _ => rfl) (fun _ _ => rfl)
    hd.1 (fun i => (hd.2.1 i).aemeasurable) hd.2.2.1 hd.2.2.2

end CausalSmith.Stat.GlobalTailDesignRobustCate
