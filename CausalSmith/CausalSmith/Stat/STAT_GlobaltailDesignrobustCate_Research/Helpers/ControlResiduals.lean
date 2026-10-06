module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.ConditionalResiduals
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.ControlCellTail

/-! # Identified control residuals on independent outcome fibers

Roadmap (C4) and (C14): consistency and exchangeability identify the control
conditional mean. Product disintegration then supplies the independent,
centered, bounded residuals required by the control cell-tail bound.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory ProbabilityTheory

/-- On control design fibers, the observed mean equals the selected control
regression by consistency and conditional exchangeability (C4). -/
-- @node: control_conditional_mean_on_design
lemma control_conditional_mean_on_design {d : ℕ} (β γ C L M κ : ℝ)
    (P : Law d) (hP : CATEClass d β γ C L M κ P) :
    let : IsProbabilityMeasure P.full := hP.iid.1
    ∀ᵐ xa ∂P.full.map (fun u : Full d => (u.1, u.2.1)), xa.2 = false →
      (∫ y, y ∂condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full xa) = P.mu0 xa.1 := by
  let : IsProbabilityMeasure P.full := hP.iid.1
  have hmeasMu : AEMeasurable P.mu0 P.xLaw := by
    rw [hP.uniformDesign]
    exact (holderOnCube_continuousOn hP.parameters.2.1 hP.controlHolder).aemeasurable
      (by simp [cube])
  let Xv : Full d → (Fin d → ℝ) := fun u => u.1
  let Av : Full d → Bool := fun u => u.2.1
  let Y₀ : Full d → ℝ := fun u => u.2.2.1
  let Yv : Full d → ℝ := fun u => if u.2.1 then u.2.2.2 else u.2.2.1
  let T : Full d → (Fin d → ℝ) × Bool := fun u => (Xv u, Av u)
  have hX : Measurable Xv := by fun_prop
  have hA : Measurable Av := by fun_prop
  have hY₀ : Measurable Y₀ := by fun_prop
  have hY : Measurable Yv := by
    dsimp [Yv]
    exact Measurable.ite (hA (measurableSet_singleton true))
      (by fun_prop) (by fun_prop)
  have hfiber :=
    Causalean.Mathlib.Probability.Kernel.CondDistribFiber.condDistrib_congr_on_conditioning_fiber
      P.full Xv Av Yv Y₀ hX hA hY hY₀ false (by
        filter_upwards with u
        cases h : u.2.1 <;> simp [Av, Yv, Y₀, h])
  have hci : CondIndepFun (MeasurableSpace.comap Xv inferInstance)
      (Measurable.comap_le hX) Av Y₀ P.full := by
    have hc := (hP.exchangeability : Exchangeability P).comp
      (by fun_prop : Measurable (fun z : ℝ × ℝ => z.1))
      (by fun_prop : Measurable (fun a : Bool => a))
    simpa [Xv, Av, Y₀, Function.comp_def] using hc.symm
  have hexch' :
      (condDistrib Y₀ T P.full : (Fin d → ℝ) × Bool → Measure ℝ) =ᵐ[P.full.map T]
        (Kernel.prodMkRight Bool (condDistrib Y₀ Xv P.full) :
          (Fin d → ℝ) × Bool → Measure ℝ) := by
    exact (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY₀ hA hX).mp hci
  have hY₀int : Integrable Y₀ P.full := by
    apply Integrable.of_mem_Icc (-M) M (by fun_prop)
    filter_upwards [hP.boundedOutcomes] with u hu
    dsimp [Y₀]
    exact abs_le.mp hu.1
  let k : (Fin d → ℝ) → ℝ := fun x =>
    ∫ y : ℝ, y ∂condDistrib Y₀ Xv P.full x
  have hkmeas : StronglyMeasurable k := by
    dsimp [k]
    exact (measurable_snd : Measurable (fun p : (Fin d → ℝ) × ℝ => p.2)).stronglyMeasurable
      |>.integral_condDistrib
  have hce : P.full[Y₀ | MeasurableSpace.comap Xv inferInstance] =ᵐ[P.full]
      fun u => k (Xv u) := by
    simpa [k] using condExp_ae_eq_integral_condDistrib' hX hY₀int
  have hcomp : (fun u => P.mu0 (Xv u)) =ᵐ[P.full] fun u => k (Xv u) :=
    hP.semantics.2.2.1.symm.trans hce
  have hbase : P.mu0 =ᵐ[P.xLaw] k := by
    have hbaseMk : hmeasMu.mk P.mu0 =ᵐ[P.xLaw] k := by
      apply (ae_map_iff hX.aemeasurable
        (measurableSet_eq_fun hmeasMu.measurable_mk hkmeas.measurable)).2
      exact (ae_eq_comp hX.aemeasurable hmeasMu.ae_eq_mk).symm.trans hcomp
    exact hmeasMu.ae_eq_mk.trans hbaseMk
  have hbaseDesign := ae_design_of_ae_xLaw P hbase
  filter_upwards [hfiber, hexch', hbaseDesign] with xa hf he hb ha
  have hs : condDistrib Yv T P.full xa = condDistrib Y₀ Xv P.full xa.1 :=
    (hf ha).trans (he.trans (by simp))
  exact (congrArg (fun ν : Measure ℝ => ∫ y : ℝ, y ∂ν) hs).trans hb.symm

/-- The masked control residual on almost every design fiber is measurable,
integrable, centered, and bounded by twice the outcome bound. Treatment-true
fibers contribute the zero residual. -/
-- @node: control_conditional_residual_properties
lemma control_conditional_residual_properties {d : ℕ} (β γ C L M κ : ℝ)
    (P : Law d) (hP : CATEClass d β γ C L M κ P) :
    let : IsProbabilityMeasure P.full := hP.iid.1
    ∀ᵐ xa ∂P.full.map (fun u : Full d => (u.1, u.2.1)),
      let ν := condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full xa
      let ξ : ℝ → ℝ := fun y => if xa.2 = false then y - P.mu0 xa.1 else 0
      Measurable ξ ∧ Integrable ξ ν ∧ (∀ᵐ y ∂ν, |ξ y| ≤ 2 * M) ∧
        (∫ y, ξ y ∂ν) = 0 := by
  let : IsProbabilityMeasure P.full := hP.iid.1
  have hmu : ∀ᵐ x ∂P.xLaw, P.mu0 x ∈ Set.Icc (-M) M := by
    have hs : ∀ᵐ x ∂P.xLaw, x ∈ cube d := by
      rw [hP.uniformDesign]
      exact self_mem_ae_restrict (by simp [cube])
    exact hs.mono (fun x hx => hP.semantics.2.2.2.2.2 x hx)
  filter_upwards [conditional_observedResponse_abs_le P M hP.boundedOutcomes,
    control_conditional_mean_on_design β γ C L M κ P hP,
    ae_design_of_ae_xLaw P hmu] with xa hbound hmean hmu
  dsimp only
  have hM : 0 ≤ M := hP.parameters.2.2.2.2.2.le
  by_cases ha : xa.2 = false
  · simp only [ha, if_true]
    have hy : Integrable (fun y : ℝ => y) (condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full xa) :=
      Integrable.of_mem_Icc (-M) M (by fun_prop)
        (hbound.mono (fun y hy => abs_le.mp hy))
    refine ⟨by fun_prop, hy.sub (integrable_const _), ?_, ?_⟩
    · filter_upwards [hbound] with y hy
      calc
        |y - P.mu0 xa.1| ≤ |y| + |P.mu0 xa.1| := by
          simpa using abs_sub_le y 0 (P.mu0 xa.1)
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
-- @node: control_productFiber_residual_properties
lemma control_productFiber_residual_properties {d n : ℕ} (β γ C L M κ : ℝ)
    (P : Law d) (hP : CATEClass d β γ C L M κ P) :
    let : IsProbabilityMeasure P.full := hP.iid.1
    ∀ᵐ design : Fin n → (Fin d → ℝ) × Bool ∂Measure.pi
        (fun _ => P.full.map (fun u : Full d => (u.1, u.2.1))),
      let ν := fun i : Fin n => condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full (design i)
      let ξ := fun i (y : Fin n → ℝ) =>
        if (design i).2 = false then y i - P.mu0 (design i).1 else 0
      iIndepFun ξ (Measure.pi ν) ∧
        (∀ i, Measurable (ξ i)) ∧
        (∀ i, ∀ᵐ y ∂Measure.pi ν, |ξ i y| ≤ 2 * M) ∧
        (∀ i, ∫ y, ξ i y ∂Measure.pi ν = 0) := by
  let : IsProbabilityMeasure P.full := hP.iid.1
  let : IsProbabilityMeasure (P.full.map (fun u : Full d => (u.1, u.2.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hprops := control_conditional_residual_properties β γ C L M κ P hP
  have hall : ∀ᵐ design : Fin n → (Fin d → ℝ) × Bool ∂Measure.pi
      (fun _ => P.full.map (fun u : Full d => (u.1, u.2.1))),
      ∀ i,
        let ν := condDistrib
          (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
          (fun u : Full d => (u.1, u.2.1)) P.full (design i)
        let ξ : ℝ → ℝ := fun y =>
          if (design i).2 = false then y - P.mu0 (design i).1 else 0
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
-- @node: control_balancedEstimator_productFiber_cell_tail
lemma control_balancedEstimator_productFiber_cell_tail (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B : ℝ, 0 < B ∧ ∀ P : Law d, ∀ hP : CATEClass d β γ C L M κ P,
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
              |controlBalancedEstimator (S y) j β M x - P.mu0 x|} ≤
            (2 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)) *
              Real.exp (-(referenceLowerEigenvalue d (polynomialOrder β) ^ 2 /
                (32 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ))) *
                  (minimumCellCount s false j (polynomialOrder β)
                    (normingSubcells d β).radius Q : ℝ) * t ^ 2 / M ^ 2) := by
  obtain ⟨B, hB, htail⟩ := control_balancedEstimator_fixedDesign_cell_tail
    d β γ C L M κ hparam
  refine ⟨B, hB, ?_⟩
  intro P hP
  let : IsProbabilityMeasure P.full := hP.iid.1
  dsimp only
  intro n j
  filter_upwards [control_productFiber_residual_properties (n := n) β γ C L M κ P hP]
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
