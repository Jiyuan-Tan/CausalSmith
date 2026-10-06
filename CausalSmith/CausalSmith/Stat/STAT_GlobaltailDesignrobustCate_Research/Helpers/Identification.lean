module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Basic
public import Causalean.Mathlib.Probability.Kernel.CondDistribFiber
public import Mathlib.Probability.Kernel.CondDistrib

/-! # Identification of the treated conditional mean -/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

-- @node: ae_slice_of_ae_compProd_of_pos
/-- A positive conditional atom transfers a joint almost-everywhere fact to its fiber. -/
lemma ae_slice_of_ae_compProd_of_pos
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (PX : Measure X) [SFinite PX] (KA : Kernel X A) [IsSFiniteKernel KA]
    (a : A) (p : X × A → Prop)
    (hp : ∀ᵐ xa ∂PX ⊗ₘ KA, p xa)
    (hpos : ∀ᵐ x ∂PX, 0 < KA x {a}) :
    ∀ᵐ x ∂PX, p (x, a) := by
  have hs := Measure.ae_ae_of_ae_compProd hp
  filter_upwards [hs, hpos] with x hx hxpos
  by_contra hxa
  have hzero : KA x {b | ¬p (x, b)} = 0 := ae_iff.mp hx
  have hle : KA x {a} ≤ KA x {b | ¬p (x, b)} := by
    apply measure_mono
    intro b hb
    rcases hb with rfl
    exact hxa
  rw [hzero] at hle
  exact (not_lt_of_ge hle) hxpos

-- @node: positivePropensity_ae
/-- The global tail envelope rules out nonpositive propensity on a set of
positive covariate probability. -/
lemma positivePropensity_ae {d : ℕ} (P : Law d) (C γ : ℝ)
    [IsProbabilityMeasure P.full]
    (htail : GlobalTail P C γ) (hγ : 1 < γ) :
    ∀ᵐ x ∂P.xLaw, 0 < P.e x := by
  have : IsProbabilityMeasure P.xLaw :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable (fun u : Full d => u.1)).aemeasurable
  let B : Set (Fin d → ℝ) := {x | P.e x ≤ 0}
  have hbound (n : ℕ) : (P.xLaw).real B ≤
      C * (1 / ((n : ℝ) + 1)) ^ tailExponent γ := by
    have ht : (1 / ((n : ℝ) + 1)) ∈ Set.Ioc (0 : ℝ) 1 := by
      constructor
      · positivity
      · apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith
    calc
      (P.xLaw).real B ≤ (P.xLaw).real {x | P.e x ≤ 1 / ((n : ℝ) + 1)} :=
        measureReal_mono (by intro x hx; exact le_trans hx ht.1.le)
      _ ≤ _ := htail _ ht
  have hlim : Filter.Tendsto (fun n : ℕ =>
      C * (1 / ((n : ℝ) + 1)) ^ tailExponent γ) Filter.atTop (nhds 0) := by
    have hq : 0 < tailExponent γ := by dsimp [tailExponent]; linarith
    have hr := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).rpow_const
      (Or.inr hq.le)
    convert hr.const_mul C using 1
    simp [Real.zero_rpow (ne_of_gt hq)]
  have hreal : (P.xLaw).real B = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
    · exact measureReal_nonneg
  have hB : P.xLaw B = 0 := by
    have hfin : P.xLaw B ≠ ⊤ := measure_ne_top _ _
    exact (ENNReal.toReal_eq_zero_iff _).mp hreal |>.resolve_right hfin
  exact (measure_eq_zero_iff_ae_notMem.mp hB).mono (by
    intro x hx
    exact lt_of_not_ge (by simpa [B] using hx))

-- @node: lem:causal-identification
/-- Under consistency, exchangeability, and the global lower tail, the
observed treated regression equals the conditional potential-outcome mean
almost everywhere. The probability-law fact is part of the core type of `P`. -/
lemma causal_identification {d : ℕ} (P : Law d) (C γ M : ℝ)
    [IsProbabilityMeasure P.full]
    (hsem : LawSemantics P M)
    (hmeasE : AEMeasurable P.e P.xLaw)
    (hmeasMu : AEMeasurable P.mu1 P.xLaw)
    (hsupport : ∀ᵐ u ∂P.full, u.1 ∈ cube d)
    (hbounded : BoundedOutcomes P M)
    (hcons : Consistency P) (hexch : Exchangeability P)
    (htail : GlobalTail P C γ) (hγ : 1 < γ) :
    (∀ᵐ x ∂P.xLaw, 0 < P.e x) ∧
    (∀ᵐ x ∂P.xLaw,
      (∫ y, y ∂condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full (x, true)) = P.mu1 x) := by
  constructor
  · exact positivePropensity_ae P C γ htail hγ
  · let Xv : Full d → (Fin d → ℝ) := fun u => u.1
    let Av : Full d → Bool := fun u => u.2.1
    let Y₁ : Full d → ℝ := fun u => u.2.2.2
    let Yv : Full d → ℝ := fun u => if u.2.1 then u.2.2.2 else u.2.2.1
    let T : Full d → (Fin d → ℝ) × Bool := fun u => (Xv u, Av u)
    have hX : Measurable Xv := by fun_prop
    have hA : Measurable Av := by fun_prop
    have hY₁ : Measurable Y₁ := by fun_prop
    have hY : Measurable Yv := by
      dsimp [Yv]
      exact Measurable.ite (hA (measurableSet_singleton true))
        (by fun_prop) (by fun_prop)
    have hfiber :=
      Causalean.Mathlib.Probability.Kernel.CondDistribFiber.condDistrib_congr_on_conditioning_fiber
        P.full Xv Av Yv Y₁ hX hA hY hY₁ true (by
          filter_upwards with u
          cases h : u.2.1 <;> simp [Av, Yv, Y₁, h])
    have hci : CondIndepFun (MeasurableSpace.comap Xv inferInstance)
        (Measurable.comap_le hX) Av Y₁ P.full := by
      have hc := (hexch : Exchangeability P).comp
        (by fun_prop : Measurable (fun z : ℝ × ℝ => z.2))
        (by fun_prop : Measurable (fun a : Bool => a))
      simpa [Xv, Av, Y₁, Function.comp_def] using hc.symm
    have hexch' :
        (condDistrib Y₁ T P.full : (Fin d → ℝ) × Bool → Measure ℝ) =ᵐ[P.full.map T]
          (Kernel.prodMkRight Bool (condDistrib Y₁ Xv P.full) :
            (Fin d → ℝ) × Bool → Measure ℝ) := by
      exact (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY₁ hA hX).mp hci
    have hpos : ∀ᵐ x ∂P.xLaw, 0 < (condDistrib Av Xv P.full) x {true} := by
      have hident :
          P.full⟦Av ⁻¹' {true} | MeasurableSpace.comap Xv inferInstance⟧ =
            P.full[(fun u => if Av u then (1 : ℝ) else 0) |
              MeasurableSpace.comap Xv inferInstance] := by
        congr 1
        funext u
        cases h : Av u <;> simp [Set.indicator, h]
      have heq : (fun u => ((condDistrib Av Xv P.full) (Xv u)).real {true}) =ᵐ[P.full]
          fun u => P.e (Xv u) := by
        have hsemE : P.full[(fun u => if Av u then (1 : ℝ) else 0) |
            MeasurableSpace.comap Xv inferInstance] =ᵐ[P.full] fun u => P.e (Xv u) := by
          simpa [Xv, Av] using hsem.1
        rw [← hident] at hsemE
        exact (condDistrib_ae_eq_condExp hX hA (measurableSet_singleton true)).trans hsemE
      have heq' : (fun x => ((condDistrib Av Xv P.full) x).real {true}) =ᵐ[P.xLaw]
          P.e := by
        have heqm : (fun x => ((condDistrib Av Xv P.full) x).real {true}) =ᵐ[P.xLaw]
            hmeasE.mk P.e := by
          apply (ae_map_iff hX.aemeasurable
            (measurableSet_eq_fun
              ((Kernel.measurable_coe _ (measurableSet_singleton true)).ennreal_toReal)
              hmeasE.measurable_mk)).2
          exact heq.trans (ae_eq_comp hX.aemeasurable hmeasE.ae_eq_mk)
        exact heqm.trans hmeasE.ae_eq_mk.symm
      filter_upwards [heq', positivePropensity_ae P C γ htail hγ] with x hx hp
      have hr : 0 < ((condDistrib Av Xv P.full) x).real {true} := by rw [hx]; exact hp
      exact (ENNReal.toReal_pos_iff.mp hr).1
    have hjoint : P.xLaw ⊗ₘ condDistrib Av Xv P.full = P.full.map T := by
      simpa [T, Law.xLaw, Xv] using
        (compProd_map_condDistrib (μ := P.full) (X := Xv) hA.aemeasurable)
    letI : IsProbabilityMeasure P.xLaw :=
      Measure.isProbabilityMeasure_map hX.aemeasurable
    have hslice : ∀ᵐ x ∂P.xLaw,
        condDistrib Yv T P.full (x, true) = condDistrib Y₁ Xv P.full x := by
      have hfiber' : ∀ᵐ xa ∂P.xLaw ⊗ₘ condDistrib Av Xv P.full,
          xa.2 = true → condDistrib Yv T P.full xa = condDistrib Y₁ T P.full xa := by
        rw [hjoint]
        exact hfiber
      have hexch'' : ∀ᵐ xa ∂P.xLaw ⊗ₘ condDistrib Av Xv P.full,
          condDistrib Y₁ T P.full xa =
            (Kernel.prodMkRight Bool (condDistrib Y₁ Xv P.full)) xa := by
        rw [hjoint]
        exact hexch'
      have hs := ae_slice_of_ae_compProd_of_pos P.xLaw
        (condDistrib Av Xv P.full) true
        (fun xa => (xa.2 = true → condDistrib Yv T P.full xa = condDistrib Y₁ T P.full xa) ∧
          condDistrib Y₁ T P.full xa =
            (Kernel.prodMkRight Bool (condDistrib Y₁ Xv P.full)) xa)
        (by filter_upwards [hfiber', hexch''] with xa hf he; exact ⟨hf, he⟩) hpos
      filter_upwards [hs] with x hx
      exact (hx.1 rfl).trans (hx.2.trans (by simp))
    have hY₁int : Integrable Y₁ P.full := by
      apply Integrable.of_mem_Icc (-M) M (by fun_prop)
      filter_upwards [hbounded] with u hu
      dsimp [Y₁]
      exact abs_le.mp hu.2
    let k : (Fin d → ℝ) → ℝ := fun x =>
      ∫ y : ℝ, y ∂condDistrib Y₁ Xv P.full x
    have hkmeas : StronglyMeasurable k := by
      dsimp [k]
      exact (measurable_snd : Measurable (fun p : (Fin d → ℝ) × ℝ => p.2)).stronglyMeasurable
        |>.integral_condDistrib
    have hce : P.full[Y₁ | MeasurableSpace.comap Xv inferInstance] =ᵐ[P.full]
        fun u => k (Xv u) := by
      simpa [k] using condExp_ae_eq_integral_condDistrib' hX hY₁int
    have hcomp : (fun u => P.mu1 (Xv u)) =ᵐ[P.full] fun u => k (Xv u) :=
      hsem.2.1.symm.trans hce
    have hbase : P.mu1 =ᵐ[P.xLaw] k := by
      have hbaseMk : hmeasMu.mk P.mu1 =ᵐ[P.xLaw] k := by
        apply (ae_map_iff hX.aemeasurable
          (measurableSet_eq_fun hmeasMu.measurable_mk hkmeas.measurable)).2
        exact (ae_eq_comp hX.aemeasurable hmeasMu.ae_eq_mk).symm.trans hcomp
      exact hmeasMu.ae_eq_mk.trans hbaseMk
    filter_upwards [hbase, hslice] with x hb hs
    exact (congrArg (fun ν : Measure ℝ => ∫ y : ℝ, y ∂ν) hs).trans hb.symm

end CausalSmith.Stat.GlobalTailDesignRobustCate
