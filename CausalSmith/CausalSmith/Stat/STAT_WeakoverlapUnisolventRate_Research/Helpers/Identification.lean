module
public import Causalean.Mathlib.Probability.Kernel.CondDistribFiber
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Model
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Identification of the Hölder treated response -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
set_option linter.style.haveILetI false

/-- A global lower-tail bound excludes a zero propensity set. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hγ,hmodel), [the asserted conclusion holds](goal). -/
lemma zeroPropensity_null {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hγ : 1 < γ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e) :
    (covariateLaw (Pc.map observed)) {x | e x = 0} = 0 := by
  have htail := hmodel.tail.2 0 (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
  have hzero : C * (0 : ℝ) ^ (γ - 1) = 0 := by
    rw [Real.zero_rpow (ne_of_gt (sub_pos.mpr hγ)), mul_zero]
  rw [hzero] at htail
  have hnonneg : 0 ≤ (covariateLaw (Pc.map observed)).real {x | e x ≤ 0} :=
    ENNReal.toReal_nonneg
  have heq : (covariateLaw (Pc.map observed)).real {x | e x ≤ 0} = 0 :=
    le_antisymm htail hnonneg
  apply le_antisymm _ (zero_le)
  calc
    (covariateLaw (Pc.map observed)) {x | e x = 0} ≤
        (covariateLaw (Pc.map observed)) {x | e x ≤ 0} :=
      measure_mono (by intro x hx; exact le_of_eq hx)
    _ = 0 := by
      letI : IsProbabilityMeasure (Pc.map observed) :=
        Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
      letI : IsProbabilityMeasure (covariateLaw (Pc.map observed)) := by
        unfold covariateLaw
        exact Measure.isProbabilityMeasure_map (by fun_prop)
      have hfin : (covariateLaw (Pc.map observed)) {x | e x ≤ 0} ≠ ⊤ :=
        measure_ne_top _ _
      exact (ENNReal.toReal_eq_zero_iff _).mp heq |>.resolve_right hfin

/-- The global tail condition makes the propensity strictly positive almost
everywhere under the covariate law. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hγ,hmodel), [the asserted conclusion holds](goal). -/
lemma positivePropensity_ae {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hγ : 1 < γ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e) :
    ∀ᵐ x ∂covariateLaw (Pc.map observed), 0 < e x := by
  have hzero := zeroPropensity_null β B L C c_f γ Pc μ₁ e hγ hmodel
  have hne : ∀ᵐ x ∂covariateLaw (Pc.map observed), e x ≠ 0 :=
    (measure_eq_zero_iff_ae_notMem.mp hzero)
  filter_upwards [hne, hmodel.tail.1] with x hx he
  have hnonneg : 0 ≤ e x := by rw [he]; exact ENNReal.toReal_nonneg
  exact lt_of_le_of_ne hnonneg (Ne.symm hx)

/-- A positive density lower bound gives the reverse absolute continuity needed
to transfer almost-everywhere identification to volume on the cube. [For the stated inputs and conditions](hyp:d,P,c_f,hc,hdensity,hAC), [the asserted conclusion holds](goal). -/
lemma cubeVolume_ac_covariateLaw {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (c_f : ℝ) (hc : 0 < c_f)
    (hdensity : CovariateDensityLowerBound P c_f)
    (hAC : covariateLaw P ≪ volume.restrict (cube d)) :
    volume.restrict (cube d) ≪ covariateLaw P := by
  let ν := volume.restrict (cube d)
  let μ := covariateLaw P
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, covariateLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hvol : volume (cube d) = 1 := by
    have hcube : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp
  haveI : IsFiniteMeasure ν := by
    rw [isFiniteMeasure_restrict]
    simp [hvol]
  have hpos : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ 0 := by
    filter_upwards [hdensity] with x hx
    have hxpos : 0 < (μ.rnDeriv ν x).toReal := lt_of_lt_of_le hc hx
    exact ne_of_gt (ENNReal.toReal_pos_iff.mp hxpos).1
  have hwith : ν ≪ ν.withDensity (μ.rnDeriv ν) :=
    withDensity_absolutelyContinuous' (μ.measurable_rnDeriv ν).aemeasurable hpos
  have heq : ν.withDensity (μ.rnDeriv ν) = μ :=
    Measure.withDensity_rnDeriv_eq μ ν hAC
  simpa only [heq, ν, μ] using hwith

/-- Observing a causal completion preserves its covariate marginal. [For the stated inputs and conditions](hyp:d,Pc), [the asserted conclusion holds](goal). -/
lemma covariateLaw_observed {d : ℕ} (Pc : Measure (Completion d)) :
    covariateLaw (Pc.map observed) = Pc.map Prod.fst := by
  rw [covariateLaw, Measure.map_map (by fun_prop) (by unfold observed; fun_prop)]
  rfl

/-- An almost-everywhere property under a composition product holds at a fixed
fiber value whenever that value has positive conditional mass almost everywhere. [For the stated inputs and conditions](hyp:X,A,PX,KA,a,p,hp,hpos), [the asserted conclusion holds](goal). -/
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

-- @node: lem:causal-identification
/-- Consistency, exchangeability, and global positivity identify the treated
conditional regression almost everywhere; continuity and the density lower
bound fix its representative at all cube points. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ₁,e,hparams,hγ,hmodel), [the asserted conclusion holds](goal). -/
lemma mu1_eq_treatedRegression {d : ℕ} (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hparams : ModelParameterDomain d β B L C c_f) (hγ : 1 < γ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e) :
    (covariateLaw (Pc.map observed)) {x | e x = 0} = 0 ∧
    (∀ᵐ x ∂covariateLaw (Pc.map observed),
      μ₁ x = treatedRegression (Pc.map observed) x) ∧
    (∀ g : (Fin d → ℝ) → ℝ, ContinuousOn g (cube d) →
      (∀ᵐ x ∂covariateLaw (Pc.map observed),
        g x = treatedRegression (Pc.map observed) x) →
      ∀ x ∈ cube d, g x = μ₁ x) := by
  have hident : ∀ᵐ x ∂covariateLaw (Pc.map observed),
      μ₁ x = treatedRegression (Pc.map observed) x := by
    let Xv : Completion d → (Fin d → ℝ) := fun ω => ω.1
    let Av : Completion d → Bool := fun ω => ω.2.1
    let Y₁ : Completion d → ℝ := fun ω => ω.2.2.2.1
    let Yv : Completion d → ℝ := fun ω => ω.2.2.2.2
    let T : Completion d → (Fin d → ℝ) × Bool := fun ω => (Xv ω, Av ω)
    have hX : Measurable Xv := by fun_prop
    have hA : Measurable Av := by fun_prop
    have hY₁ : Measurable Y₁ := by fun_prop
    have hY : Measurable Yv := by fun_prop
    have hcons : ∀ᵐ ω ∂Pc, Av ω = true → Yv ω = Y₁ ω := by
      filter_upwards [hmodel.consistency] with ω hω hAt
      simpa [Av, Yv, Y₁, hAt] using hω
    have hfiber :=
      Causalean.Mathlib.Probability.Kernel.CondDistribFiber.condDistrib_congr_on_conditioning_fiber
        Pc Xv Av Yv Y₁ hX hA hY hY₁ true hcons
    have hci : ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Xv inferInstance)
        (Measurable.comap_le hX) Av Y₁ Pc := by
      have hc := hmodel.exchangeability.comp
        (by fun_prop : Measurable (fun z : ℝ × ℝ => z.2))
        (by fun_prop : Measurable (fun a : Bool => a))
      simpa [Xv, Av, Y₁, Function.comp_def] using hc.symm
    have hexch :
        (ProbabilityTheory.condDistrib Y₁ T Pc : (Fin d → ℝ) × Bool → Measure ℝ) =ᵐ[Pc.map T]
          (Kernel.prodMkRight Bool (ProbabilityTheory.condDistrib Y₁ Xv Pc) :
            (Fin d → ℝ) × Bool → Measure ℝ) := by
      exact (ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
        hY₁ hA hX).mp hci
    have hpos : ∀ᵐ x ∂Pc.map Xv,
        0 < ProbabilityTheory.condDistrib Av Xv Pc x {true} := by
      have hepos := positivePropensity_ae β B L C c_f γ Pc μ₁ e hγ hmodel
      have heprop := hmodel.tail.1
      have hkmap := ProbabilityTheory.condDistrib_map
        (ν := Pc) (f := observed)
        (X := fun z : Obs d => z.1) (Y := fun z : Obs d => z.2.1)
        (by fun_prop) (by fun_prop) (by unfold observed; fun_prop)
      have hPX : Pc.map Xv = covariateLaw (Pc.map observed) := by
        simpa [Xv] using (covariateLaw_observed Pc).symm
      have hkmap' :
          (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.1) (fun z => z.1)
            (Pc.map observed) : (Fin d → ℝ) → Measure Bool)
              =ᵐ[covariateLaw (Pc.map observed)]
          (ProbabilityTheory.condDistrib Av Xv Pc : (Fin d → ℝ) → Measure Bool) := by
        rw [covariateLaw_observed Pc]
        simpa [Xv, Av, observed, Function.comp_def] using hkmap
      rw [hPX]
      filter_upwards [hepos, heprop, hkmap'] with x heposx hepropx hkx
      have hp : 0 < propensity (Pc.map observed) x := by
        rw [← hepropx]
        exact heposx
      have hreal : 0 < ((ProbabilityTheory.condDistrib Av Xv Pc) x {true}).toReal := by
        rw [← hkx]
        simpa [propensity] using hp
      exact (ENNReal.toReal_pos_iff.mp hreal).1
    have hjoint : Pc.map Xv ⊗ₘ ProbabilityTheory.condDistrib Av Xv Pc = Pc.map T := by
      simpa [T] using ProbabilityTheory.compProd_map_condDistrib
        (μ := Pc) (X := Xv) hA.aemeasurable
    have hfiber' : ∀ᵐ xa ∂Pc.map Xv ⊗ₘ ProbabilityTheory.condDistrib Av Xv Pc,
        xa.2 = true → ProbabilityTheory.condDistrib Yv T Pc xa =
          ProbabilityTheory.condDistrib Y₁ T Pc xa := by
      rw [hjoint]
      exact hfiber
    have hexch' : ∀ᵐ xa ∂Pc.map Xv ⊗ₘ ProbabilityTheory.condDistrib Av Xv Pc,
        ProbabilityTheory.condDistrib Y₁ T Pc xa =
          (Kernel.prodMkRight Bool (ProbabilityTheory.condDistrib Y₁ Xv Pc)) xa := by
      rw [hjoint]
      exact hexch
    have hslice : ∀ᵐ x ∂Pc.map Xv,
        ProbabilityTheory.condDistrib Yv T Pc (x, true) =
          ProbabilityTheory.condDistrib Y₁ Xv Pc x := by
      have hboth := ae_slice_of_ae_compProd_of_pos
        (Pc.map Xv) (ProbabilityTheory.condDistrib Av Xv Pc) true
        (fun xa => (xa.2 = true → ProbabilityTheory.condDistrib Yv T Pc xa =
            ProbabilityTheory.condDistrib Y₁ T Pc xa) ∧
          ProbabilityTheory.condDistrib Y₁ T Pc xa =
            (Kernel.prodMkRight Bool (ProbabilityTheory.condDistrib Y₁ Xv Pc)) xa)
        (by
          filter_upwards [hfiber', hexch'] with xa hf he
          exact ⟨hf, he⟩) hpos
      filter_upwards [hboth] with x hx
      exact (hx.1 rfl).trans (hx.2.trans (by simp))
    have hobmap := ProbabilityTheory.condDistrib_map
      (ν := Pc) (f := observed)
      (X := fun z : Obs d => (z.1, z.2.1)) (Y := fun z : Obs d => z.2.2)
      (by fun_prop) (by fun_prop) (by unfold observed; fun_prop)
    have hobmap' :
        (ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
          (fun z => (z.1, z.2.1)) (Pc.map observed) :
            (Fin d → ℝ) × Bool → Measure ℝ) =ᵐ[Pc.map T]
        (ProbabilityTheory.condDistrib Yv T Pc : (Fin d → ℝ) × Bool → Measure ℝ) := by
      simpa [T, Yv, observed, Function.comp_def] using hobmap
    have hobmapComp : ∀ᵐ xa ∂Pc.map Xv ⊗ₘ ProbabilityTheory.condDistrib Av Xv Pc,
        ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
            (fun z => (z.1, z.2.1)) (Pc.map observed) xa =
          ProbabilityTheory.condDistrib Yv T Pc xa := by
      rw [hjoint]
      exact hobmap'
    have hobSlice : ∀ᵐ x ∂Pc.map Xv,
        treatedKernel (Pc.map observed) x = ProbabilityTheory.condDistrib Yv T Pc (x, true) := by
      have hs := ae_slice_of_ae_compProd_of_pos
        (Pc.map Xv) (ProbabilityTheory.condDistrib Av Xv Pc) true
        (fun xa => ProbabilityTheory.condDistrib (fun z : Obs d => z.2.2)
            (fun z => (z.1, z.2.1)) (Pc.map observed) xa =
          ProbabilityTheory.condDistrib Yv T Pc xa) hobmapComp hpos
      simpa [treatedKernel] using hs
    have hkernel : ∀ᵐ x ∂Pc.map Xv,
        treatedKernel (Pc.map observed) x = ProbabilityTheory.condDistrib Y₁ Xv Pc x := by
      filter_upwards [hobSlice, hslice] with x ho hs
      exact ho.trans hs
    have hPX : Pc.map Xv = covariateLaw (Pc.map observed) := by
      simpa [Xv] using (covariateLaw_observed Pc).symm
    have houtcome : ∀ᵐ x ∂Pc.map Xv,
        |treatedRegression (Pc.map observed) x| ≤ B ∧
        ∀ t : ℝ,
          Integrable (fun y : ℝ => Real.exp
              (t * (y - treatedRegression (Pc.map observed) x)))
              (ProbabilityTheory.condDistrib Y₁ Xv Pc x) ∧
          ProbabilityTheory.mgf (fun y : ℝ => y - treatedRegression (Pc.map observed) x)
              (ProbabilityTheory.condDistrib Y₁ Xv Pc x) t ≤
            Real.exp (B ^ 2 * t ^ 2 / 2) := by
      have ho' : ∀ᵐ x ∂Pc.map Xv,
          |treatedRegression (Pc.map observed) x| ≤ B ∧
          ∀ t : ℝ,
            Integrable (fun y : ℝ => Real.exp
                (t * (y - treatedRegression (Pc.map observed) x)))
                (treatedKernel (Pc.map observed) x) ∧
            ProbabilityTheory.mgf
                (fun y : ℝ => y - treatedRegression (Pc.map observed) x)
                (treatedKernel (Pc.map observed) x) t ≤
              Real.exp (B ^ 2 * t ^ 2 / 2) := by
        rw [hPX]
        exact hmodel.outcome
      filter_upwards [ho', hkernel] with x ho hk
      exact ⟨ho.1, fun t => by simpa [← hk] using ho.2 t⟩
    have hY₁fiber : ∀ᵐ x ∂Pc.map Xv,
        Integrable (fun y : ℝ => y) (ProbabilityTheory.condDistrib Y₁ Xv Pc x) := by
      filter_upwards [houtcome] with x ho
      let m := treatedRegression (Pc.map observed) x
      have hp : Integrable (fun y : ℝ => Real.exp (y - m))
          (ProbabilityTheory.condDistrib Y₁ Xv Pc x) := by
        simpa [m] using (ho.2 1).1
      have hn : Integrable (fun y : ℝ => Real.exp (-(y - m)))
          (ProbabilityTheory.condDistrib Y₁ Xv Pc x) := by
        simpa [m] using (ho.2 (-1)).1
      have hright : Integrable
          (fun y : ℝ => Real.exp (y - m) + Real.exp (-(y - m)) + |m|)
          (ProbabilityTheory.condDistrib Y₁ Xv Pc x) :=
        (hp.add hn).add (integrable_const |m|)
      apply Integrable.mono' hright (by fun_prop)
      filter_upwards [] with y
      rw [Real.norm_eq_abs]
      calc
        |y| = |(y - m) + m| := by ring_nf
        _ ≤ |y - m| + |m| := abs_add_le _ _
        _ ≤ (Real.exp (y - m) + Real.exp (-(y - m))) + |m| := by
          gcongr
          exact (le_add_of_nonneg_right zero_le_one).trans
            ((Real.add_one_le_exp _).trans (Real.exp_abs_le _))
    have hY₁norm_bound : ∀ᵐ x ∂Pc.map Xv,
        (∫ y : ℝ, ‖y‖ ∂ProbabilityTheory.condDistrib Y₁ Xv Pc x) ≤
          2 * Real.exp (B ^ 2 / 2) + B := by
      filter_upwards [houtcome] with x ho
      let m := treatedRegression (Pc.map observed) x
      let K := ProbabilityTheory.condDistrib Y₁ Xv Pc x
      have hp : Integrable (fun y : ℝ => Real.exp (y - m)) K := by
        simpa [m, K] using (ho.2 1).1
      have hn : Integrable (fun y : ℝ => Real.exp (-(y - m))) K := by
        simpa [m, K] using (ho.2 (-1)).1
      have hdom : ∀ y : ℝ, ‖y‖ ≤
          Real.exp (y - m) + Real.exp (-(y - m)) + |m| := by
        intro y
        rw [Real.norm_eq_abs]
        calc
          |y| = |(y - m) + m| := by ring_nf
          _ ≤ |y - m| + |m| := abs_add_le _ _
          _ ≤ (Real.exp (y - m) + Real.exp (-(y - m))) + |m| := by
            gcongr
            exact (le_add_of_nonneg_right zero_le_one).trans
              ((Real.add_one_le_exp _).trans (Real.exp_abs_le _))
      have hright : Integrable
          (fun y : ℝ => Real.exp (y - m) + Real.exp (-(y - m)) + |m|) K :=
        (hp.add hn).add (integrable_const |m|)
      have hleft : Integrable (fun y : ℝ => ‖y‖) K := by
        apply Integrable.mono' hright (by fun_prop)
        filter_upwards [] with y
        simpa using hdom y
      have hi := integral_mono hleft hright hdom
      calc
        (∫ y : ℝ, ‖y‖ ∂K) ≤
            ∫ y : ℝ, (Real.exp (y - m) + Real.exp (-(y - m)) + |m|) ∂K := hi
        _ = ProbabilityTheory.mgf (fun y : ℝ => y - m) K 1 +
            ProbabilityTheory.mgf (fun y : ℝ => y - m) K (-1) + |m| := by
          calc
            (∫ y : ℝ, Real.exp (y - m) + Real.exp (-(y - m)) + |m| ∂K) =
                (∫ y : ℝ, Real.exp (y - m) + Real.exp (-(y - m)) ∂K) +
                  ∫ _ : ℝ, |m| ∂K :=
              integral_add (hp.add hn) (integrable_const |m|)
            _ = ((∫ y : ℝ, Real.exp (y - m) ∂K) +
                  ∫ y : ℝ, Real.exp (-(y - m)) ∂K) + ∫ _ : ℝ, |m| ∂K := by
              rw [integral_add hp hn]
            _ = ProbabilityTheory.mgf (fun y : ℝ => y - m) K 1 +
                  ProbabilityTheory.mgf (fun y : ℝ => y - m) K (-1) + |m| := by
              simp [ProbabilityTheory.mgf, m, K]
        _ ≤ Real.exp (B ^ 2 * (1 : ℝ) ^ 2 / 2) +
            Real.exp (B ^ 2 * (-1 : ℝ) ^ 2 / 2) + B := by
          gcongr
          · exact (ho.2 1).2
          · exact (ho.2 (-1)).2
          · exact ho.1
        _ = 2 * Real.exp (B ^ 2 / 2) + B := by ring_nf
    have hnorm_meas : StronglyMeasurable
        (fun x => ∫ y : ℝ, ‖y‖ ∂ProbabilityTheory.condDistrib Y₁ Xv Pc x) := by
      fun_prop
    have hnorm_int : Integrable
        (fun x => ∫ y : ℝ, ‖y‖ ∂ProbabilityTheory.condDistrib Y₁ Xv Pc x)
        (Pc.map Xv) := by
      apply Integrable.mono' (integrable_const (2 * Real.exp (B ^ 2 / 2) + B))
        hnorm_meas.aestronglyMeasurable
      filter_upwards [hY₁norm_bound] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hx
      · exact integral_nonneg (fun _ => norm_nonneg _)
    have hcomp_int : Integrable (fun y : ℝ => y)
        ((ProbabilityTheory.condDistrib Y₁ Xv Pc) ∘ₘ (Pc.map Xv)) := by
      rw [Measure.integrable_comp_iff (by fun_prop)]
      exact ⟨hY₁fiber, hnorm_int⟩
    have hY₁int : Integrable Y₁ Pc := by
      have hmap : (ProbabilityTheory.condDistrib Y₁ Xv Pc) ∘ₘ (Pc.map Xv) = Pc.map Y₁ :=
        ProbabilityTheory.condDistrib_comp_map hX.aemeasurable hY₁.aemeasurable
      rw [hmap] at hcomp_int
      exact (integrable_map_measure (by fun_prop) hY₁.aemeasurable).mp hcomp_int
    let k : (Fin d → ℝ) → ℝ := fun x =>
      ∫ y : ℝ, y ∂ProbabilityTheory.condDistrib Y₁ Xv Pc x
    have hkmeas : StronglyMeasurable k := by
      dsimp [k]
      exact (measurable_snd : Measurable (fun p : (Fin d → ℝ) × ℝ => p.2)).stronglyMeasurable
        |>.integral_condDistrib
    have hμae : AEStronglyMeasurable μ₁ (Pc.map Xv) := by
      have hac : Pc.map Xv ≪ volume.restrict (cube d) := by
        rw [hPX]
        exact hmodel.covariateAC
      have hcube : MeasurableSet (cube d) := by
        unfold cube
        exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
      exact AEStronglyMeasurable.mono_ac hac
        (hmodel.smooth.1.regularity.continuousOn.aestronglyMeasurable hcube)
    let μ₁m := hμae.mk μ₁
    have hμmk : μ₁ =ᵐ[Pc.map Xv] μ₁m := hμae.ae_eq_mk
    have hce : Pc[Y₁ | MeasurableSpace.comap Xv inferInstance] =ᵐ[Pc]
        fun ω => k (Xv ω) := by
      simpa [k] using ProbabilityTheory.condExp_ae_eq_integral_condDistrib' hX hY₁int
    have hcomp : (fun ω => μ₁ (Xv ω)) =ᵐ[Pc] fun ω => k (Xv ω) :=
      hmodel.smooth.2.trans hce
    have hcompm : (fun ω => μ₁m (Xv ω)) =ᵐ[Pc] fun ω => k (Xv ω) :=
      (ae_eq_comp hX.aemeasurable hμmk.symm).trans hcomp
    have hmkeq : μ₁m =ᵐ[Pc.map Xv] k := by
      apply (ae_map_iff hX.aemeasurable
        (measurableSet_eq_fun hμae.measurable_mk hkmeas.measurable)).2
      exact hcompm
    have hbase : μ₁ =ᵐ[Pc.map Xv] k := hμmk.trans hmkeq
    rw [hPX] at hbase hkernel
    filter_upwards [hbase, hkernel] with x hb hk
    simpa [k, treatedRegression, hk] using hb
  refine ⟨zeroPropensity_null β B L C c_f γ Pc μ₁ e hγ hmodel, hident, ?_⟩
  intro g hg hgreg x hx
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  have hreverse : volume.restrict (cube d) ≪ covariateLaw (Pc.map observed) :=
    cubeVolume_ac_covariateLaw (Pc.map observed) c_f hparams.2.2.2.2.2.1
      hmodel.density hmodel.covariateAC
  have hAE : g =ᵐ[covariateLaw (Pc.map observed)] μ₁ := by
    filter_upwards [hgreg, hident] with y hgy hμy
    exact hgy.trans hμy.symm
  have hAEvol : g =ᵐ[volume.restrict (cube d)] μ₁ := hreverse.ae_eq hAE
  have hcube_reg : cube d ⊆ closure (interior (cube d)) := by
    intro y hy
    change y ∈ closure (interior (Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) 1)))
    rw [interior_pi_set Set.finite_univ, closure_pi_set]
    intro i hi
    rw [closure_interior_Icc (by norm_num : (0 : ℝ) ≠ 1)]
    exact (show y ∈ Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) 1) from hy) i hi
  exact Measure.eqOn_of_ae_eq hAEvol hg
    hmodel.smooth.1.regularity.continuousOn hcube_reg hx
end CausalSmith.Stat.WeakOverlap
