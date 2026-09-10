import Mathlib.Probability.Independence.Conditional

/-!
# Conditional independence from a three-block product density

This module isolates the measure-theoretic bridge needed by finite-DAG local Markov proofs.
It turns a density whose two random blocks interact only through a third, conditioning block
into `CondIndepFun` for the two coordinate maps given the third coordinate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean

universe uY uZ uC

variable {Y : Type uY} {Z : Type uZ} {C : Type uC}
variable [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace C]
variable [StandardBorelSpace Y] [StandardBorelSpace Z] [StandardBorelSpace C]

/-- For [three coordinate reference measures](hyp:muY,muZ,muC), [a measurable finite joint
density](hyp:hd), [first and second block factors](hyp:a,b), [measurability of those factors](hyp:ha,hb),
and [their almost-everywhere product representation](hyp:hfactor), [the first and second coordinate
maps are conditionally independent given the third coordinate](goal). -/
theorem condIndepFun_threeBlock_of_density_factors
    (muY : Measure Y) (muZ : Measure Z) (muC : Measure C)
    [SigmaFinite muY] [SigmaFinite muZ] [SigmaFinite muC]
    {d : Y × (Z × C) → ℝ≥0∞} (hd : Measurable d)
    [IsFiniteMeasure ((muY.prod (muZ.prod muC)).withDensity d)]
    (a : Y × C → ℝ≥0∞) (b : Z × C → ℝ≥0∞)
    (ha : Measurable a) (hb : Measurable b)
    (hfactor : d =ᵐ[muY.prod (muZ.prod muC)]
      (fun q ↦ a (q.1, q.2.2) * b (q.2.1, q.2.2))) :
    CondIndepFun
      (MeasurableSpace.comap (fun q : Y × (Z × C) ↦ q.2.2) inferInstance)
      ((measurable_snd.comp measurable_snd :
        Measurable (fun q : Y × (Z × C) ↦ q.2.2)).comap_le)
      (fun q : Y × (Z × C) ↦ q.1)
      (fun q : Y × (Z × C) ↦ q.2.1)
      ((muY.prod (muZ.prod muC)).withDensity d) := by
  /-
  This is the lowest analytic obligation in the ordered local-Markov proof.  A direct route is
  to compute the conditioning marginal and the two random-block-with-conditioning marginals by
  Tonelli, prove the cross-multiplied density identity, and use Mathlib's conditional-expectation
  characterization of `CondIndepFun`.  The empty `Y` and empty `Z` cases must be discharged
  separately; no positivity or nonemptiness assumption is valid here.
  -/
  classical
  cases isEmpty_or_nonempty Y with
  | inl hY =>
      letI := hY
      rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
        (show Measurable (fun q : Y × (Z × C) ↦ q.1) from measurable_fst)
        (show Measurable (fun q : Y × (Z × C) ↦ q.2.1) from
          measurable_fst.comp measurable_snd)]
      intro s t hs ht
      exact ae_of_all _ fun q ↦ isEmptyElim q.1
  | inr hY =>
      letI := hY
      cases isEmpty_or_nonempty Z with
      | inl hZ =>
          letI := hZ
          rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
            (show Measurable (fun q : Y × (Z × C) ↦ q.1) from measurable_fst)
            (show Measurable (fun q : Y × (Z × C) ↦ q.2.1) from
              measurable_fst.comp measurable_snd)]
          intro s t hs ht
          exact ae_of_all _ fun q ↦ isEmptyElim q.2.1
      | inr hZ =>
          letI := hZ
          let ref : Measure (Y × (Z × C)) := muY.prod (muZ.prod muC)
          let fact : Y × (Z × C) → ℝ≥0∞ :=
            fun q ↦ a (q.1, q.2.2) * b (q.2.1, q.2.2)
          let P : Measure (Y × (Z × C)) := ref.withDensity fact
          have hP : (muY.prod (muZ.prod muC)).withDensity d = P := by
            exact withDensity_congr_ae hfactor
          letI : IsFiniteMeasure P := hP ▸ inferInstance
          let massY : C → ℝ≥0∞ := fun c ↦ ∫⁻ y, a (y, c) ∂muY
          let massZ : C → ℝ≥0∞ := fun c ↦ ∫⁻ z, b (z, c) ∂muZ
          let mass : C → ℝ≥0∞ := fun c ↦ massY c * massZ c
          have hmassY : Measurable massY := by
            unfold massY
            fun_prop
          have hmassZ : Measurable massZ := by
            unfold massZ
            fun_prop
          have hmass : Measurable mass := hmassY.mul hmassZ
          let ccoord : Y × (Z × C) → C := fun q ↦ q.2.2
          let yzcoord : Y × (Z × C) → Y × Z := fun q ↦ (q.1, q.2.1)
          have hccoord : Measurable ccoord := measurable_snd.comp measurable_snd
          have hyzcoord : Measurable yzcoord := measurable_fst.prodMk
            (measurable_fst.comp measurable_snd)
          have hPmapC : P.map ccoord = muC.withDensity mass := by
            refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
            rw [lintegral_map hf hccoord,
              lintegral_withDensity_eq_lintegral_mul _ (by
                unfold fact
                fun_prop) (by fun_prop),
              lintegral_withDensity_eq_lintegral_mul _ hmass hf]
            change (∫⁻ q : Y × (Z × C),
                a (q.1, q.2.2) * b (q.2.1, q.2.2) * f q.2.2
                  ∂muY.prod (muZ.prod muC)) =
              ∫⁻ c, (∫⁻ y, a (y, c) ∂muY) * (∫⁻ z, b (z, c) ∂muZ) * f c ∂muC
            rw [lintegral_prod _ (by fun_prop)]
            calc
              _ = ∫⁻ y, ∫⁻ z, ∫⁻ c,
                    a (y, c) * b (z, c) * f c ∂muC ∂muZ ∂muY := by
                apply lintegral_congr
                intro y
                rw [lintegral_prod _ (by fun_prop)]
              _ = ∫⁻ y, ∫⁻ c, ∫⁻ z,
                    a (y, c) * b (z, c) * f c ∂muZ ∂muC ∂muY := by
                apply lintegral_congr
                intro y
                exact lintegral_lintegral_swap (by fun_prop)
              _ = ∫⁻ c, ∫⁻ y, ∫⁻ z,
                    a (y, c) * b (z, c) * f c ∂muZ ∂muY ∂muC := by
                exact lintegral_lintegral_swap (by fun_prop)
              _ = _ := by
                apply lintegral_congr
                intro c
                calc
                  _ = ∫⁻ y, a (y, c) * (massZ c * f c) ∂muY := by
                    apply lintegral_congr
                    intro y
                    calc
                      _ = ∫⁻ z, a (y, c) * (b (z, c) * f c) ∂muZ := by
                        apply lintegral_congr
                        intro z
                        ac_rfl
                      _ = a (y, c) * (∫⁻ z, b (z, c) * f c ∂muZ) := by
                        rw [lintegral_const_mul]
                        fun_prop
                      _ = _ := by
                        rw [lintegral_mul_const]
                        fun_prop
                  _ = massY c * (massZ c * f c) := by
                    rw [lintegral_mul_const]
                    fun_prop
                  _ = massY c * massZ c * f c := by ac_rfl
          let ν : Measure C := muC.withDensity mass
          haveI : IsFiniteMeasure ν := by
            change IsFiniteMeasure (muC.withDensity mass)
            rw [← hPmapC]
            infer_instance
          have hmassInt : ∫⁻ c, mass c ∂muC ≠ ∞ := by
            have h := measure_ne_top ν Set.univ
            simpa [ν, withDensity_apply] using h
          have hmassFinite : ∀ᵐ c ∂muC, mass c ≠ ∞ :=
            (ae_lt_top hmass hmassInt).mono fun _ h ↦ h.ne
          let goodY : Set C := {c | massY c ≠ 0 ∧ massY c ≠ ∞}
          let goodZ : Set C := {c | massZ c ≠ 0 ∧ massZ c ≠ ∞}
          have hgoodY : MeasurableSet goodY :=
            ((hmassY (measurableSet_singleton 0)).compl.inter
              (hmassY (measurableSet_singleton ∞)).compl)
          have hgoodZ : MeasurableSet goodZ :=
            ((hmassZ (measurableSet_singleton 0)).compl.inter
              (hmassZ (measurableSet_singleton ∞)).compl)
          have hgoodY_ae : ∀ᵐ c ∂ν, c ∈ goodY := by
            change ∀ᵐ c ∂muC.withDensity mass, c ∈ goodY
            rw [ae_withDensity_iff hmass]
            filter_upwards [hmassFinite] with c hcTop hc0
            have hy0 : massY c ≠ 0 := by
              intro hy
              apply hc0
              simp [mass, hy]
            have hyTop : massY c ≠ ∞ := by
              intro hy
              have hz0 : massZ c ≠ 0 := by
                intro hz
                apply hc0
                simp [mass, hz]
              apply hcTop
              simp [mass, hy, hz0]
            exact ⟨hy0, hyTop⟩
          have hgoodZ_ae : ∀ᵐ c ∂ν, c ∈ goodZ := by
            change ∀ᵐ c ∂muC.withDensity mass, c ∈ goodZ
            rw [ae_withDensity_iff hmass]
            filter_upwards [hmassFinite] with c hcTop hc0
            have hz0 : massZ c ≠ 0 := by
              intro hz
              apply hc0
              simp [mass, hz]
            have hzTop : massZ c ≠ ∞ := by
              intro hz
              have hy0 : massY c ≠ 0 := by
                intro hy
                apply hc0
                simp [mass, hy]
              apply hcTop
              simp [mass, hz, hy0]
            exact ⟨hz0, hzTop⟩
          let fallbackY : Kernel C Y :=
            Kernel.const C (Measure.dirac (Classical.choice hY))
          let fallbackZ : Kernel C Z :=
            Kernel.const C (Measure.dirac (Classical.choice hZ))
          have hrawY : Measurable
              (fun c ↦ muY.withDensity (fun y ↦ a (y, c) / massY c)) := by
            apply Measure.measurable_of_measurable_coe
            intro s hs
            simp_rw [withDensity_apply _ hs]
            fun_prop
          have hrawZ : Measurable
              (fun c ↦ muZ.withDensity (fun z ↦ b (z, c) / massZ c)) := by
            apply Measure.measurable_of_measurable_coe
            intro s hs
            simp_rw [withDensity_apply _ hs]
            fun_prop
          let κY : Kernel C Y :=
            ⟨fun c ↦ if c ∈ goodY then
                muY.withDensity (fun y ↦ a (y, c) / massY c) else fallbackY c,
              hrawY.piecewise hgoodY fallbackY.measurable⟩
          let κZ : Kernel C Z :=
            ⟨fun c ↦ if c ∈ goodZ then
                muZ.withDensity (fun z ↦ b (z, c) / massZ c) else fallbackZ c,
              hrawZ.piecewise hgoodZ fallbackZ.measurable⟩
          have hκYmarkov : IsMarkovKernel κY := by
            refine ⟨fun c ↦ ⟨?_⟩⟩
            change (if c ∈ goodY then
              muY.withDensity (fun y ↦ a (y, c) / massY c) else fallbackY c) Set.univ = 1
            split_ifs with hc
            · rw [withDensity_apply' _ Set.univ, Measure.restrict_univ]
              simp only [ENNReal.div_eq_inv_mul]
              rw [lintegral_const_mul]
              · exact ENNReal.inv_mul_cancel hc.1 hc.2
              · fun_prop
            · simp [fallbackY]
          have hκZmarkov : IsMarkovKernel κZ := by
            refine ⟨fun c ↦ ⟨?_⟩⟩
            change (if c ∈ goodZ then
              muZ.withDensity (fun z ↦ b (z, c) / massZ c) else fallbackZ c) Set.univ = 1
            split_ifs with hc
            · rw [withDensity_apply' _ Set.univ, Measure.restrict_univ]
              simp only [ENNReal.div_eq_inv_mul]
              rw [lintegral_const_mul]
              · exact ENNReal.inv_mul_cancel hc.1 hc.2
              · fun_prop
            · simp [fallbackZ]
          letI : IsMarkovKernel κY := hκYmarkov
          letI : IsMarkovKernel κZ := hκZmarkov
          have hgoodY_imp : ∀ᵐ c ∂muC, mass c ≠ 0 → c ∈ goodY :=
            (ae_withDensity_iff hmass).1 hgoodY_ae
          have hgoodZ_imp : ∀ᵐ c ∂muC, mass c ≠ 0 → c ∈ goodZ :=
            (ae_withDensity_iff hmass).1 hgoodZ_ae
          let jointcoord : Y × (Z × C) → C × (Y × Z) :=
            fun q ↦ (ccoord q, yzcoord q)
          have hjointcoord : Measurable jointcoord := hccoord.prodMk hyzcoord
          have hjoint : P.map jointcoord = ν ⊗ₘ (κY ×ₖ κZ) := by
            refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
            rw [lintegral_map hg hjointcoord,
              lintegral_withDensity_eq_lintegral_mul _ (by
                unfold fact
                fun_prop) (by fun_prop), Measure.lintegral_compProd hg]
            change (∫⁻ q : Y × (Z × C),
                a (q.1, q.2.2) * b (q.2.1, q.2.2) * g (q.2.2, (q.1, q.2.1))
                  ∂muY.prod (muZ.prod muC)) =
              ∫⁻ c, ∫⁻ yz, g (c, yz) ∂(κY ×ₖ κZ) c ∂ν
            rw [lintegral_prod _ (by fun_prop)]
            calc
              _ = ∫⁻ y, ∫⁻ z, ∫⁻ c,
                    a (y, c) * b (z, c) * g (c, (y, z)) ∂muC ∂muZ ∂muY := by
                apply lintegral_congr
                intro y
                rw [lintegral_prod _ (by fun_prop)]
              _ = ∫⁻ y, ∫⁻ c, ∫⁻ z,
                    a (y, c) * b (z, c) * g (c, (y, z)) ∂muZ ∂muC ∂muY := by
                apply lintegral_congr
                intro y
                exact lintegral_lintegral_swap (by fun_prop)
              _ = ∫⁻ c, ∫⁻ y, ∫⁻ z,
                    a (y, c) * b (z, c) * g (c, (y, z)) ∂muZ ∂muY ∂muC := by
                exact lintegral_lintegral_swap (by fun_prop)
              _ = ∫⁻ c, mass c *
                    (∫⁻ yz, g (c, yz) ∂(κY ×ₖ κZ) c) ∂muC := by
                apply lintegral_congr_ae
                filter_upwards [hmassFinite, hgoodY_imp, hgoodZ_imp] with
                  c hcTop hcY hcZ
                by_cases hc0 : mass c = 0
                · have hor : massY c = 0 ∨ massZ c = 0 := by
                    simpa [mass] using hc0
                  rcases hor with hy0 | hz0
                  · have hay : (fun y ↦ a (y, c)) =ᵐ[muY] 0 := by
                      apply (lintegral_eq_zero_iff (by fun_prop)).1
                      simpa [massY] using hy0
                    rw [hc0, zero_mul]
                    apply (lintegral_eq_zero_iff (by fun_prop)).2
                    filter_upwards [hay] with y hy
                    simp [hy]
                  · have hbz : (fun z ↦ b (z, c)) =ᵐ[muZ] 0 := by
                      apply (lintegral_eq_zero_iff (by fun_prop)).1
                      simpa [massZ] using hz0
                    rw [hc0, zero_mul]
                    apply (lintegral_eq_zero_iff (by fun_prop)).2
                    apply ae_of_all
                    intro y
                    apply (lintegral_eq_zero_iff (by fun_prop)).2
                    filter_upwards [hbz] with z hz
                    simp [hz]
                · have hcY' := hcY hc0
                  have hcZ' := hcZ hc0
                  change (∫⁻ y, ∫⁻ z,
                      a (y, c) * b (z, c) * g (c, (y, z)) ∂muZ ∂muY) =
                    mass c * (∫⁻ yz, g (c, yz) ∂(κY ×ₖ κZ) c)
                  rw [Kernel.prod_apply]
                  change _ = mass c * (∫⁻ yz, g (c, yz) ∂
                    ((if c ∈ goodY then
                        muY.withDensity (fun y ↦ a (y, c) / massY c) else fallbackY c).prod
                      (if c ∈ goodZ then
                        muZ.withDensity (fun z ↦ b (z, c) / massZ c) else fallbackZ c)))
                  rw [if_pos hcY', if_pos hcZ', prod_withDensity]
                  swap
                  · fun_prop
                  swap
                  · fun_prop
                  rw [lintegral_withDensity_eq_lintegral_mul]
                  swap
                  · fun_prop
                  swap
                  · fun_prop
                  rw [← lintegral_const_mul]
                  swap
                  · fun_prop
                  rw [← lintegral_prod
                    (fun yz : Y × Z ↦ a (yz.1, c) * b (yz.2, c) * g (c, yz)) (by fun_prop)]
                  apply lintegral_congr_ae
                  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
                  apply ae_of_all
                  intro y
                  apply ae_of_all
                  intro z
                  change a (y, c) * b (z, c) * g (c, (y, z)) =
                    mass c * ((a (y, c) / massY c * (b (z, c) / massZ c)) *
                      g (c, (y, z)))
                  simp only [mass, ENNReal.div_eq_inv_mul]
                  calc
                    _ = (massY c * ((massY c)⁻¹ * a (y, c))) *
                        (massZ c * ((massZ c)⁻¹ * b (z, c))) * g (c, (y, z)) := by
                      rw [ENNReal.mul_inv_cancel_left hcY'.1 hcY'.2,
                        ENNReal.mul_inv_cancel_left hcZ'.1 hcZ'.2]
                    _ = _ := by ac_rfl
              _ = _ := by
                change _ = ∫⁻ c,
                  (∫⁻ yz, g (c, yz) ∂(κY ×ₖ κZ) c) ∂muC.withDensity mass
                rw [lintegral_withDensity_eq_lintegral_mul]
                · rfl
                · exact hmass
                · fun_prop
          have hPmapCν : P.map ccoord = ν := by
            simpa [ν] using hPmapC
          have hjointCD : condDistrib yzcoord ccoord P =ᵐ[ν] κY ×ₖ κZ := by
            have h := condDistrib_ae_eq_of_measure_eq_compProd (Y := yzcoord)
              (μ := P) ccoord hyzcoord.aemeasurable (by
                change P.map jointcoord = P.map ccoord ⊗ₘ (κY ×ₖ κZ)
                rw [hPmapCν]
                exact hjoint)
            rwa [hPmapCν] at h
          let ycoord : Y × (Z × C) → Y := fun q ↦ q.1
          let zcoord : Y × (Z × C) → Z := fun q ↦ q.2.1
          have hycoord : Measurable ycoord := measurable_fst
          have hzcoord : Measurable zcoord := measurable_fst.comp measurable_snd
          have hcdY : condDistrib ycoord ccoord P =ᵐ[ν] κY := by
            have hcomp := condDistrib_comp (Y := yzcoord) (μ := P)
              (mβ := inferInstance) ccoord hyzcoord.aemeasurable measurable_fst
            rw [hPmapCν] at hcomp
            filter_upwards [hcomp, hjointCD] with c hc hpair
            calc
              condDistrib ycoord ccoord P c =
                  (condDistrib yzcoord ccoord P).map Prod.fst c := by
                simpa [ycoord, yzcoord, Function.comp_def] using hc
              _ = (κY ×ₖ κZ).map Prod.fst c := by
                rw [Kernel.map_apply _ measurable_fst, Kernel.map_apply _ measurable_fst, hpair]
              _ = κY c := by
                rw [← Kernel.fst_eq, Kernel.fst_prod]
          have hcdZ : condDistrib zcoord ccoord P =ᵐ[ν] κZ := by
            have hcomp := condDistrib_comp (Y := yzcoord) (μ := P)
              (mβ := inferInstance) ccoord hyzcoord.aemeasurable measurable_snd
            rw [hPmapCν] at hcomp
            filter_upwards [hcomp, hjointCD] with c hc hpair
            calc
              condDistrib zcoord ccoord P c =
                  (condDistrib yzcoord ccoord P).map Prod.snd c := by
                simpa [zcoord, yzcoord, Function.comp_def] using hc
              _ = (κY ×ₖ κZ).map Prod.snd c := by
                rw [Kernel.map_apply _ measurable_snd, Kernel.map_apply _ measurable_snd, hpair]
              _ = κZ c := by
                rw [← Kernel.snd_eq, Kernel.snd_prod]
          have hciP : CondIndepFun (MeasurableSpace.comap ccoord inferInstance)
              hccoord.comap_le ycoord zcoord P := by
            rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
              hycoord hzcoord hccoord]
            rw [← Measure.compProd_eq_comp_prod, hPmapCν]
            calc
              P.map (fun q ↦ (ccoord q, ycoord q, zcoord q)) =
                  ν ⊗ₘ (κY ×ₖ κZ) := by
                simpa [jointcoord, yzcoord, ycoord, zcoord] using hjoint
              _ = ν ⊗ₘ
                  (condDistrib ycoord ccoord P ×ₖ condDistrib zcoord ccoord P) := by
                apply Measure.compProd_congr
                filter_upwards [hcdY, hcdZ] with c hcY hcZ
                rw [Kernel.prod_apply, Kernel.prod_apply, hcY, hcZ]
          have hciP' : CondIndepFun (MeasurableSpace.comap ccoord inferInstance)
              hccoord.comap_le ycoord zcoord
              ((muY.prod (muZ.prod muC)).withDensity d) := by
            simpa only [← hP] using hciP
          simpa only [ccoord, ycoord, zcoord] using hciP'

end Causalean
