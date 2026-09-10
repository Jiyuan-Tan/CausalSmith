/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Basic
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Approximation duality and symmetric moment-matched priors

This module packages the Hahn--Banach/Riesz extremal certificate for best
uniform approximation of absolute value and converts its positive and negative
parts into two symmetric probability measures.  The resulting structure is the
consumer-facing moment-matched-prior API.
-/

open MeasureTheory Set

namespace Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality

/-- For [a Borel measure on the real line](hyp:ν), [symmetry about zero](goal) means that reflecting every point through zero leaves the measure unchanged. -/
def IsSymmetric (ν : Measure ℝ) : Prop :=
  Measure.map (fun x : ℝ => -x) ν = ν

/-- For [a measure on the real line](hyp:ν), [support on the unit interval](goal) means that the complement of the closed interval from −1 to 1 has measure zero. -/
def IsSupportedOnUnitInterval (ν : Measure ℝ) : Prop :=
  ν (unitIntervalᶜ) = 0

private theorem exists_positive_half_split
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (L : C(X, ℝ) →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (hLone : L 1 = 0) :
    ∃ P N : C(X, ℝ) →ₚ[ℝ] ℝ,
      P 1 = 1 / 2 ∧ N 1 = 1 / 2 ∧
      ∀ f, P f - N f = L f := by
  let Φ : ℝ × ℝ →ₗ[ℝ] C(X, ℝ) × ℝ :=
    { toFun := fun z => (z.1 • (1 : C(X, ℝ)), z.2)
      map_add' := by intro a b; ext x <;> simp
      map_smul' := by intro c z; ext x <;> simp [mul_assoc] }
  have hΦ : Function.Injective Φ := by
    intro a b hab
    have hfirst : a.1 = b.1 := by
      have hx := congrArg (fun z : C(X, ℝ) × ℝ =>
        z.1 (Classical.choice inferInstance)) hab
      change a.1 * 1 = b.1 * 1 at hx
      simpa using hx
    have hsecond : a.2 = b.2 := congrArg (fun z : C(X, ℝ) × ℝ => z.2) hab
    exact Prod.ext hfirst hsecond
  let eΦ := LinearEquiv.ofInjective Φ hΦ
  let fdom : Φ.range →ₗ[ℝ] ℝ :=
    { toFun := fun z => (eΦ.symm z).1 / 2 + (eΦ.symm z).2
      map_add' := by intro a b; simp; ring
      map_smul' := by intro c z; simp; ring }
  let f : (C(X, ℝ) × ℝ) →ₗ.[ℝ] ℝ := LinearPMap.mk Φ.range fdom
  let S : PointedCone ℝ (C(X, ℝ) × ℝ) :=
    { carrier := {z | ∃ a b : C(X, ℝ), 0 ≤ a ∧ 0 ≤ b ∧ z = (a + b, -L b)}
      zero_mem' := ⟨0, 0, le_rfl, le_rfl, by ext <;> simp⟩
      add_mem' := by
        rintro z w ⟨a, b, ha, hb, rfl⟩ ⟨c, d, hc, hd, rfl⟩
        refine ⟨a + c, b + d, (fun x => add_nonneg (ha x) (hc x)),
          (fun x => add_nonneg (hb x) (hd x)), ?_⟩
        ext x <;> simp [map_add, add_comm, add_left_comm, add_assoc]
      smul_mem' := by
        rintro ⟨c, hc⟩ z ⟨a, b, ha, hb, rfl⟩
        refine ⟨c • a, c • b, (fun x => mul_nonneg hc (ha x)),
          (fun x => mul_nonneg hc (hb x)), ?_⟩
        ext x <;> simp [map_smul] }
  have hf_nonneg : ∀ z : f.domain, (z : C(X, ℝ) × ℝ) ∈ S → 0 ≤ f z := by
    intro z hz
    rcases hz with ⟨a, b, ha, hb, hzeq⟩
    obtain ⟨q, hq⟩ := z.property
    have heq : (eΦ.symm z : ℝ × ℝ) = q := by
      apply eΦ.injective
      apply Subtype.ext
      simpa [eΦ] using hq.symm
    have hcoord := congrArg Prod.fst (hq.trans hzeq)
    have hpoint (x : X) : a x + b x = q.1 := by
      have := congrArg (fun u : C(X, ℝ) => u x) hcoord
      simpa [Φ] using this.symm
    have hq0 : 0 ≤ q.1 := by
      have := add_nonneg (ha (Classical.choice inferInstance))
        (hb (Classical.choice inferInstance))
      simpa [hpoint] using this
    let u : C(X, ℝ) := (2 : ℝ) • b - q.1 • (1 : C(X, ℝ))
    have hunorm : ‖u‖ ≤ q.1 := by
      apply (ContinuousMap.norm_le_of_nonempty _).2
      intro x
      rw [Real.norm_eq_abs, abs_le]
      have hax : 0 ≤ a x := ha x
      have hbx : 0 ≤ b x := hb x
      have hx := hpoint x
      simp only [u, ContinuousMap.coe_sub, Pi.sub_apply, ContinuousMap.coe_smul,
        Pi.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
      change -q.1 ≤ 2 * b x - q.1 ∧ 2 * b x - q.1 ≤ q.1
      constructor <;> linarith
    have hLu : L u ≤ q.1 := by
      calc
        L u ≤ |L u| := le_abs_self _
        _ = ‖L u‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖L‖ * ‖u‖ := L.le_opNorm u
        _ ≤ 1 * q.1 := mul_le_mul hL hunorm (norm_nonneg _) zero_le_one
        _ = q.1 := one_mul _
    have hLb : L b ≤ q.1 / 2 := by
      have hLu' : L u = 2 * L b := by simp [u, hLone]
      rw [hLu'] at hLu
      linarith
    have hsecond := congrArg Prod.snd (hq.trans hzeq)
    have hsecond' : q.2 = -L b := by simpa [Φ] using hsecond
    change (eΦ.symm z).1 / 2 + (eΦ.symm z).2 ≥ 0
    rw [heq, hsecond']
    linarith
  have hf_dense : ∀ y : C(X, ℝ) × ℝ, ∃ z : f.domain,
      (z : C(X, ℝ) × ℝ) + y ∈ S := by
    rintro ⟨y, t⟩
    let q : ℝ × ℝ := (‖y‖, -t)
    have hqmem : Φ q ∈ Φ.range := ⟨q, rfl⟩
    refine ⟨⟨Φ q, hqmem⟩, ?_⟩
    refine ⟨‖y‖ • (1 : C(X, ℝ)) + y, 0, ?_, le_rfl, ?_⟩
    · intro x
      have := ContinuousMap.norm_coe_le_norm y x
      simpa [q, Φ, Real.norm_eq_abs, neg_le_iff_add_nonneg, add_comm] using
        (neg_le_of_abs_le this)
    · ext <;> simp [q, Φ]
  obtain ⟨G, hGdom, hGS⟩ := riesz_extension S f hf_nonneg hf_dense
  let Pmap : C(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => G (u, 0)
      map_add' := by intro a b; simpa using G.map_add (a, 0) (b, 0)
      map_smul' := by intro c a; simpa using G.map_smul c (a, 0) }
  let Nmap : C(X, ℝ) →ₗ[ℝ] ℝ := Pmap - L.toLinearMap
  have hPnonneg : ∀ u : C(X, ℝ), 0 ≤ u → 0 ≤ Pmap u := by
    intro u hu
    exact hGS (u, 0) ⟨u, 0, hu, le_rfl, by simp [Pmap]⟩
  have hNnonneg : ∀ u : C(X, ℝ), 0 ≤ u → 0 ≤ Nmap u := by
    intro u hu
    have h := hGS (u, -L u) ⟨0, u, le_rfl, hu, by simp⟩
    have hg : G (u, -L u) = G (u, 0) - L u := by
      rw [show (u, -L u) = (u, 0) + (0, -L u) by ext <;> simp, map_add]
      rw [show G (0, -L u) = -L u by
        calc G (0, -L u) = G ((-L u) • (0, 1)) := by simp
             _ = (-L u) * G (0, 1) := by rw [map_smul]; rfl
             _ = -L u := by
               have hv : G (0, 1) = 1 := by
                 let qv : ℝ × ℝ := (0, 1)
                 have hmem : Φ qv ∈ Φ.range := ⟨qv, rfl⟩
                 have he : eΦ.symm (⟨Φ qv, hmem⟩ : Φ.range) = qv := by
                   apply eΦ.injective
                   rw [eΦ.apply_symm_apply]
                   apply Subtype.ext
                   rfl
                 have hd := hGdom (⟨Φ qv, hmem⟩ : f.domain)
                 change G (Φ qv) =
                   (eΦ.symm (⟨Φ qv, hmem⟩ : Φ.range)).1 / 2 +
                     (eΦ.symm (⟨Φ qv, hmem⟩ : Φ.range)).2 at hd
                 rw [he] at hd
                 simpa [qv, Φ] using hd
               rw [hv, mul_one]]
      ring
    rw [hg] at h
    exact h
  let P : C(X, ℝ) →ₚ[ℝ] ℝ :=
    { toLinearMap := Pmap
      monotone' := by
        intro a b hab
        have h := hPnonneg (b - a) (fun x => sub_nonneg.mpr (hab x))
        simpa [map_sub] using h }
  let N : C(X, ℝ) →ₚ[ℝ] ℝ :=
    { toLinearMap := Nmap
      monotone' := by
        intro a b hab
        have h := hNnonneg (b - a) (fun x => sub_nonneg.mpr (hab x))
        simpa [map_sub] using h }
  have hone_mem : Φ (1, 0) ∈ Φ.range := ⟨(1, 0), rfl⟩
  have hPone : P 1 = 1 / 2 := by
    change G ((1 : C(X, ℝ)), 0) = 1 / 2
    have he : eΦ.symm (⟨Φ (1, 0), hone_mem⟩ : Φ.range) = (1, 0) := by
      apply eΦ.injective
      rw [eΦ.apply_symm_apply]
      apply Subtype.ext
      rfl
    have h := hGdom (⟨Φ (1, 0), hone_mem⟩ : f.domain)
    change G (Φ (1, 0)) =
      (eΦ.symm (⟨Φ (1, 0), hone_mem⟩ : Φ.range)).1 / 2 +
        (eΦ.symm (⟨Φ (1, 0), hone_mem⟩ : Φ.range)).2 at h
    rw [he] at h
    simpa [Φ] using h
  refine ⟨P, N, hPone, ?_, ?_⟩
  · change Pmap 1 - L 1 = 1 / 2
    change Pmap 1 = 1 / 2 at hPone
    rw [hPone, hLone]
    ring
  · intro u
    change Pmap u - (Pmap u - L u) = L u
    ring

private noncomputable def dualAbs : C(unitInterval, ℝ) :=
  ⟨fun x => |(x : ℝ)|, by fun_prop⟩

private noncomputable def dualPow (j : ℕ) : C(unitInterval, ℝ) :=
  ⟨fun x => (x : ℝ) ^ j, by fun_prop⟩

private noncomputable def dualPolynomials (K : ℕ) :
    Submodule ℝ C(unitInterval, ℝ) :=
  ((Polynomial.toContinuousMapOnAlgHom unitInterval).toLinearMap.domRestrict
    (Polynomial.degreeLT ℝ (K + 1))).range

private theorem uniformApproxErrorAbs_eq_dual_norm (p : Polynomial ℝ) :
    uniformApproxErrorAbs p = ‖dualAbs - p.toContinuousMapOn unitInterval‖ := by
  apply le_antisymm
  · apply uniformApproxErrorAbs_le_iff.mpr
    intro x hx
    have h := ContinuousMap.norm_coe_le_norm
      (dualAbs - p.toContinuousMapOn unitInterval) ⟨x, by simpa [unitInterval] using hx⟩
    change |(|x| - p.eval x)| ≤ _ at h
    exact h
  · apply (ContinuousMap.norm_le_of_nonempty _).mpr
    intro x
    change |(|(x : ℝ)| - p.eval (x : ℝ))| ≤ uniformApproxErrorAbs p
    exact ((uniformApproxErrorAbs_le_iff (p := p) (e := uniformApproxErrorAbs p)).mp
      (le_refl _)) (x : ℝ) (by simpa [unitInterval] using x.property)

private theorem exists_dual_abs_certificate (K : ℕ) :
    ∃ L : C(unitInterval, ℝ) →L[ℝ] ℝ,
      ‖L‖ ≤ 1 ∧ L 1 = 0 ∧
      (∀ j : ℕ, j ≤ K → L (dualPow j) = 0) ∧
      L dualAbs = bestUniformApproxErrorAbs K := by
  let V := dualPolynomials K
  let qabs : C(unitInterval, ℝ) ⧸ V := Submodule.Quotient.mk dualAbs
  have hnorm : ‖qabs‖ = bestUniformApproxErrorAbs K := by
    dsimp only [qabs]
    change ‖(QuotientAddGroup.mk dualAbs :
      C(unitInterval, ℝ) ⧸ V.toAddSubgroup)‖ =
      bestUniformApproxErrorAbs K
    rw [QuotientAddGroup.norm_mk]
    apply le_antisymm
    · obtain ⟨p, hp, herr⟩ := exists_bestPolynomialAbs K
      have hpLT : p ∈ Polynomial.degreeLT ℝ (K + 1) := by
        rw [Polynomial.degreeLT_succ_eq_degreeLE]
        exact Polynomial.mem_degreeLE.mpr (Polynomial.natDegree_le_iff_degree_le.mp hp)
      let y : C(unitInterval, ℝ) := p.toContinuousMapOn unitInterval
      have hy : y ∈ V := ⟨⟨p, hpLT⟩, rfl⟩
      calc
        Metric.infDist dualAbs (V : Set C(unitInterval, ℝ)) ≤ dist dualAbs y :=
          Metric.infDist_le_dist_of_mem hy
        _ = ‖dualAbs - y‖ := dist_eq_norm _ _
        _ = uniformApproxErrorAbs p := (uniformApproxErrorAbs_eq_dual_norm p).symm
        _ = bestUniformApproxErrorAbs K := herr
    · apply (Metric.le_infDist (show (V : Set C(unitInterval, ℝ)).Nonempty from
        ⟨0, V.zero_mem⟩)).mpr
      intro y hy
      obtain ⟨p, hp⟩ := hy
      have hpdeg : (p : Polynomial ℝ).natDegree ≤ K := by
        have hpLE : (p : Polynomial ℝ) ∈ Polynomial.degreeLE ℝ K := by
          rw [← Polynomial.degreeLT_succ_eq_degreeLE]
          exact p.property
        exact Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hpLE)
      have hbest : bestUniformApproxErrorAbs K ≤ uniformApproxErrorAbs p := by
        rw [bestUniformApproxErrorAbs_eq_sInf]
        apply csInf_le
        · refine ⟨0, ?_⟩
          rintro e ⟨r, -, rfl⟩
          have h := ((uniformApproxErrorAbs_le_iff
            (p := r) (e := uniformApproxErrorAbs r)).mp (le_refl _)) 0 (by norm_num)
          exact (abs_nonneg _).trans h
        · exact ⟨p, hpdeg, rfl⟩
      rw [uniformApproxErrorAbs_eq_dual_norm] at hbest
      have hp' : (p : Polynomial ℝ).toContinuousMapOn unitInterval = y := hp
      rw [hp'] at hbest
      simpa [dist_eq_norm] using hbest
  obtain ⟨g, hg, hgabs⟩ := exists_dual_vector'' ℝ qabs
  let L : C(unitInterval, ℝ) →L[ℝ] ℝ := g.comp V.mkQL
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro u
    calc
      ‖L u‖ = ‖g (V.mkQL u)‖ := rfl
      _ ≤ ‖g‖ * ‖V.mkQL u‖ := g.le_opNorm _
      _ ≤ 1 * ‖u‖ := mul_le_mul hg (Submodule.Quotient.norm_mk_le V u)
        (norm_nonneg (V.mkQL u)) zero_le_one
  have hVzero (u : C(unitInterval, ℝ)) (hu : u ∈ V) : L u = 0 := by
    change g (Submodule.Quotient.mk u) = 0
    have hq : Submodule.Quotient.mk u = (0 : C(unitInterval, ℝ) ⧸ V) :=
      (QuotientAddGroup.eq_zero_iff u).2 hu
    rw [hq]
    simp
  have hone : L 1 = 0 := by
    apply hVzero
    let p : Polynomial ℝ := 1
    have hp : p ∈ Polynomial.degreeLT ℝ (K + 1) := by
      rw [Polynomial.degreeLT_succ_eq_degreeLE]
      apply Polynomial.mem_degreeLE.mpr
      simp [p]
    exact ⟨⟨p, hp⟩, by ext x; simp [p]⟩
  have hpows : ∀ j : ℕ, j ≤ K → L (dualPow j) = 0 := by
    intro j hj
    apply hVzero
    let p : Polynomial ℝ := Polynomial.X ^ j
    have hpdeg : p.natDegree ≤ K := by simp [p, hj]
    have hp : p ∈ Polynomial.degreeLT ℝ (K + 1) := by
      rw [Polynomial.degreeLT_succ_eq_degreeLE]
      exact Polynomial.mem_degreeLE.mpr (Polynomial.natDegree_le_iff_degree_le.mp hpdeg)
    exact ⟨⟨p, hp⟩, by ext x; simp [p, dualPow]⟩
  refine ⟨L, hL, hone, hpows, ?_⟩
  change g qabs = bestUniformApproxErrorAbs K
  simpa [hnorm] using hgabs

private noncomputable def symmPush (μ : Measure unitInterval) : Measure ℝ :=
  (1 / 2 : ENNReal) •
    (Measure.map (Subtype.val : unitInterval → ℝ) μ +
      Measure.map ((fun x : ℝ => -x) ∘ (Subtype.val : unitInterval → ℝ)) μ)

private theorem symmPush_mass (μ : Measure unitInterval) [IsFiniteMeasure μ]
    (hμ : μ Set.univ = (1 / 2 : ENNReal)) :
    symmPush μ Set.univ = (1 / 2 : ENNReal) := by
  have hm₁ : Measure.map (Subtype.val : unitInterval → ℝ) μ Set.univ =
      (1 / 2 : ENNReal) := by
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
    exact hμ
  have hm₂ : Measure.map ((fun x : ℝ => -x) ∘
      (Subtype.val : unitInterval → ℝ)) μ Set.univ =
      (1 / 2 : ENNReal) := by
    rw [Measure.map_apply (measurable_neg.comp measurable_subtype_coe) MeasurableSet.univ]
    exact hμ
  simp only [symmPush, Measure.smul_apply, MeasurableSet.univ, Measure.add_apply, hm₁, hm₂]
  simp only [smul_eq_mul, div_eq_mul_inv, one_mul]
  change (2 : ENNReal)⁻¹ * ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹) = (2 : ENNReal)⁻¹
  rw [← two_mul, ENNReal.mul_inv_cancel (a := (2 : ENNReal)) (by norm_num) (by norm_num)]
  simp

private theorem symmPush_supported (μ : Measure unitInterval) [IsFiniteMeasure μ] :
    IsSupportedOnUnitInterval (symmPush μ) := by
  have hset : MeasurableSet unitIntervalᶜ := by
    simpa [unitInterval] using (measurableSet_Icc : MeasurableSet (Icc (-1 : ℝ) 1)).compl
  simp only [IsSupportedOnUnitInterval, symmPush, Measure.smul_apply,
    hset, Measure.add_apply]
  have hpos : Measure.map (Subtype.val : unitInterval → ℝ) μ unitIntervalᶜ = 0 := by
    rw [Measure.map_apply_of_aemeasurable measurable_subtype_coe.aemeasurable
      hset]
    have hpre : (Subtype.val : unitInterval → ℝ) ⁻¹' unitIntervalᶜ = ∅ := by
      ext x
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
      exact not_not.mpr x.property
    rw [hpre]
    exact μ.empty
  have hneg : Measure.map ((fun x : ℝ => -x) ∘
      (Subtype.val : unitInterval → ℝ)) μ unitIntervalᶜ = 0 := by
    rw [Measure.map_apply_of_aemeasurable
      (measurable_neg.comp measurable_subtype_coe).aemeasurable
      hset]
    have hpre : ((fun x : ℝ => -x) ∘ (Subtype.val : unitInterval → ℝ)) ⁻¹'
        unitIntervalᶜ = ∅ := by
      ext x
      simp only [mem_preimage, Function.comp_apply, mem_compl_iff, mem_empty_iff_false,
        iff_false]
      simpa [unitInterval] using
        (show -(x : ℝ) ∈ Icc (-1 : ℝ) 1 by
          rcases x.property with ⟨hx1, hx2⟩
          constructor <;> linarith)
    rw [hpre]
    exact μ.empty
  rw [hpos, hneg]
  simp

private theorem symmPush_symmetric (μ : Measure unitInterval) [IsFiniteMeasure μ] :
    IsSymmetric (symmPush μ) := by
  simp only [IsSymmetric, symmPush, Measure.map_smul]
  rw [Measure.map_add _ _ measurable_neg]
  have hm₁ : Measure.map (fun x : ℝ => -x)
      (Measure.map (Subtype.val : unitInterval → ℝ) μ) =
      Measure.map ((fun x : ℝ => -x) ∘ (Subtype.val : unitInterval → ℝ)) μ := by
    rw [Measure.map_map measurable_neg measurable_subtype_coe]
  have hm₂ : Measure.map (fun x : ℝ => -x)
      (Measure.map ((fun x : ℝ => -x) ∘ (Subtype.val : unitInterval → ℝ)) μ) =
      Measure.map (Subtype.val : unitInterval → ℝ) μ := by
    rw [Measure.map_map measurable_neg (measurable_neg.comp measurable_subtype_coe)]
    congr 1
    funext x
    simp
  rw [hm₁, hm₂, add_comm]

private theorem integrable_comp_unitInterval (μ : Measure unitInterval) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Continuous f) (sgn : ℝ → ℝ) (hsgn : Continuous sgn) :
    Integrable (fun x : unitInterval => f (sgn (x : ℝ))) μ := by
  let g : C(unitInterval, ℝ) := ⟨fun x => f (sgn (x : ℝ)), by fun_prop⟩
  apply Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖
  filter_upwards [] with x
  exact ContinuousMap.norm_coe_le_norm g x

private theorem integral_symmPush (μ : Measure unitInterval) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ x : ℝ, f x ∂symmPush μ =
      (1 / 2 : ℝ) *
        ((∫ x : unitInterval, f (x : ℝ) ∂μ) +
          ∫ x : unitInterval, f (-(x : ℝ)) ∂μ) := by
  have hi₁ : Integrable f (Measure.map (Subtype.val : unitInterval → ℝ) μ) := by
    apply (integrable_map_measure hf.aestronglyMeasurable
      measurable_subtype_coe.aemeasurable).mpr
    exact integrable_comp_unitInterval μ f hf id continuous_id
  have hi₂ : Integrable f (Measure.map ((fun x : ℝ => -x) ∘
      (Subtype.val : unitInterval → ℝ)) μ) := by
    apply (integrable_map_measure hf.aestronglyMeasurable
      (measurable_neg.comp measurable_subtype_coe).aemeasurable).mpr
    exact integrable_comp_unitInterval μ f hf (-·) continuous_neg
  rw [symmPush, integral_smul_measure, integral_add_measure hi₁ hi₂,
    integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable,
    integral_map (measurable_neg.comp measurable_subtype_coe).aemeasurable
      hf.aestronglyMeasurable]
  norm_num

/-- Extremal signed-measure data represented by its positive and negative
parts.  Each part has mass `1/2`, is symmetric and supported on `[-1,1]`; their
degree-`K` moments agree, while their absolute first moments differ by `E_K`.

This is the normalized Jordan-decomposition output of the norm-one separating
functional.  Multiplying each part by two gives probability measures and the
gap `2 E_K`.
-/
structure AbsExtremalDecomposition (K : ℕ) where
  positive : Measure ℝ
  negative : Measure ℝ
  finite_positive : IsFiniteMeasure positive
  finite_negative : IsFiniteMeasure negative
  positive_mass : positive Set.univ = (1 / 2 : ENNReal)
  negative_mass : negative Set.univ = (1 / 2 : ENNReal)
  positive_supported : IsSupportedOnUnitInterval positive
  negative_supported : IsSupportedOnUnitInterval negative
  positive_symmetric : IsSymmetric positive
  negative_symmetric : IsSymmetric negative
  moments_eq : ∀ j : ℕ, j ≤ K →
    ∫ x : ℝ, x ^ j ∂positive = ∫ x : ℝ, x ^ j ∂negative
  abs_gap :
    (∫ x : ℝ, |x| ∂positive) - (∫ x : ℝ, |x| ∂negative) =
      bestUniformApproxErrorAbs K

/-- For [a polynomial degree limit](hyp:K), [a normalized extremal signed-measure decomposition exists](goal).

 Hahn--Banach separation and Riesz representation produce normalized
extremal signed-measure data for every degree bound. -/
theorem exists_absExtremalDecomposition (K : ℕ) :
    Nonempty (AbsExtremalDecomposition K) := by
  obtain ⟨L, hL, hLone, hLpows, hLabs⟩ := exists_dual_abs_certificate K
  obtain ⟨P, N, hPone, hNone, hPN⟩ := exists_positive_half_split L hL hLone
  let forgetC : CompactlySupportedContinuousMap unitInterval ℝ →ₗ[ℝ]
      C(unitInterval, ℝ) :=
    { toFun := fun f => f.toContinuousMap
      map_add' := by intro f g; ext x; rfl
      map_smul' := by intro c f; ext x; rfl }
  let Pc : CompactlySupportedContinuousMap unitInterval ℝ →ₚ[ℝ] ℝ :=
    { toLinearMap := P.toLinearMap.comp forgetC
      monotone' := by
        intro f g hfg
        exact P.monotone' (fun x => hfg x) }
  let Nc : CompactlySupportedContinuousMap unitInterval ℝ →ₚ[ℝ] ℝ :=
    { toLinearMap := N.toLinearMap.comp forgetC
      monotone' := by
        intro f g hfg
        exact N.monotone' (fun x => hfg x) }
  let μP : Measure unitInterval := RealRMK.rieszMeasure Pc
  let μN : Measure unitInterval := RealRMK.rieszMeasure Nc
  haveI : IsFiniteMeasure μP := by dsimp [μP]; infer_instance
  haveI : IsFiniteMeasure μN := by dsimp [μN]; infer_instance
  have hμP (c : C(unitInterval, ℝ)) : ∫ x, c x ∂μP = P c := by
    let cc := CompactlySupportedContinuousMap.continuousMapEquiv c
    have h := RealRMK.integral_rieszMeasure Pc cc
    calc
      (∫ x, c x ∂μP) = ∫ x, cc x ∂RealRMK.rieszMeasure Pc := by
        simp [μP, cc]
      _ = Pc cc := h
      _ = P c := rfl
  have hμN (c : C(unitInterval, ℝ)) : ∫ x, c x ∂μN = N c := by
    let cc := CompactlySupportedContinuousMap.continuousMapEquiv c
    have h := RealRMK.integral_rieszMeasure Nc cc
    calc
      (∫ x, c x ∂μN) = ∫ x, cc x ∂RealRMK.rieszMeasure Nc := by
        simp [μN, cc]
      _ = Nc cc := h
      _ = N c := rfl
  have hmassP : μP Set.univ = (1 / 2 : ENNReal) := by
    have h := hμP (1 : C(unitInterval, ℝ))
    change (∫ _ : unitInterval, (1 : ℝ) ∂μP) = P 1 at h
    rw [integral_const] at h
    simp only [smul_eq_mul, mul_one, hPone] at h
    have htr : (μP Set.univ).toReal = ((1 / 2 : ENNReal)).toReal := by
      simpa [measureReal_def] using h
    rcases (ENNReal.toReal_eq_toReal_iff _ _).mp htr with h | h | h
    · exact h
    · exact False.elim (by simpa using h.2)
    · exact False.elim ((measure_ne_top μP Set.univ) h.1)
  have hmassN : μN Set.univ = (1 / 2 : ENNReal) := by
    have h := hμN (1 : C(unitInterval, ℝ))
    change (∫ _ : unitInterval, (1 : ℝ) ∂μN) = N 1 at h
    rw [integral_const] at h
    simp only [smul_eq_mul, mul_one, hNone] at h
    have htr : (μN Set.univ).toReal = ((1 / 2 : ENNReal)).toReal := by
      simpa [measureReal_def] using h
    rcases (ENNReal.toReal_eq_toReal_iff _ _).mp htr with h | h | h
    · exact h
    · exact False.elim (by simpa using h.2)
    · exact False.elim ((measure_ne_top μN Set.univ) h.1)
  let positive := symmPush μP
  let negative := symmPush μN
  refine ⟨{
    positive := positive
    negative := negative
    finite_positive := by
      constructor
      dsimp only [positive]
      rw [symmPush_mass μP hmassP]
      norm_num
    finite_negative := by
      constructor
      dsimp only [negative]
      rw [symmPush_mass μN hmassN]
      norm_num
    positive_mass := by exact symmPush_mass μP hmassP
    negative_mass := by exact symmPush_mass μN hmassN
    positive_supported := by exact symmPush_supported μP
    negative_supported := by exact symmPush_supported μN
    positive_symmetric := by exact symmPush_symmetric μP
    negative_symmetric := by exact symmPush_symmetric μN
    moments_eq := ?_
    abs_gap := ?_ }⟩
  · intro j hj
    let rpow : C(unitInterval, ℝ) :=
      ⟨fun x => (-(x : ℝ)) ^ j, by fun_prop⟩
    have hrpow : rpow = (-1 : ℝ) ^ j • dualPow j := by
      ext x
      change (-(x : ℝ)) ^ j = (-1 : ℝ) ^ j * (x : ℝ) ^ j
      rw [neg_pow]
    have hLrpow : L rpow = 0 := by
      rw [hrpow, map_smul, hLpows j hj, smul_zero]
    have h₁ := hPN (dualPow j)
    have h₂ := hPN rpow
    have hp₁ : (∫ x : unitInterval, (x : ℝ) ^ j ∂μP) = P (dualPow j) :=
      hμP (dualPow j)
    have hp₂ : (∫ x : unitInterval, (-(x : ℝ)) ^ j ∂μP) = P rpow :=
      hμP rpow
    have hn₁ : (∫ x : unitInterval, (x : ℝ) ^ j ∂μN) = N (dualPow j) :=
      hμN (dualPow j)
    have hn₂ : (∫ x : unitInterval, (-(x : ℝ)) ^ j ∂μN) = N rpow :=
      hμN rpow
    have hp := integral_symmPush μP (fun x : ℝ => x ^ j) (by fun_prop)
    have hn := integral_symmPush μN (fun x : ℝ => x ^ j) (by fun_prop)
    change ∫ x : ℝ, x ^ j ∂positive = ∫ x : ℝ, x ^ j ∂negative
    dsimp only [positive, negative]
    rw [hp, hn]
    rw [hp₁, hp₂, hn₁, hn₂]
    rw [hLpows j hj] at h₁
    rw [hLrpow] at h₂
    linarith
  · let rabs : C(unitInterval, ℝ) :=
      ⟨fun x => |-(x : ℝ)|, by fun_prop⟩
    have hrabs : rabs = dualAbs := by ext x; simp [rabs, dualAbs]
    have h₁ := hPN dualAbs
    have h₂ := hPN rabs
    have hp₁ : (∫ x : unitInterval, |(x : ℝ)| ∂μP) = P dualAbs := hμP dualAbs
    have hp₂ : (∫ x : unitInterval, |-(x : ℝ)| ∂μP) = P rabs := hμP rabs
    have hn₁ : (∫ x : unitInterval, |(x : ℝ)| ∂μN) = N dualAbs := hμN dualAbs
    have hn₂ : (∫ x : unitInterval, |-(x : ℝ)| ∂μN) = N rabs := hμN rabs
    have hp := integral_symmPush μP (fun x : ℝ => |x|) (by fun_prop)
    have hn := integral_symmPush μN (fun x : ℝ => |x|) (by fun_prop)
    change (∫ x : ℝ, |x| ∂positive) - (∫ x : ℝ, |x| ∂negative) =
      bestUniformApproxErrorAbs K
    dsimp only [positive, negative]
    rw [hp, hn]
    rw [hp₁, hp₂, hn₁, hn₂]
    rw [hrabs] at h₂
    rw [hLabs] at h₁ h₂
    rw [hrabs]
    linarith

/-- Two symmetric probability measures on `[-1,1]` whose moments match through
degree `K` and whose absolute first moments have the oriented gap `2 E_K`. -/
structure AbsMomentMatchedPriors (K : ℕ) where
  ν₀ : Measure ℝ
  ν₁ : Measure ℝ
  probability₀ : IsProbabilityMeasure ν₀
  probability₁ : IsProbabilityMeasure ν₁
  supported₀ : IsSupportedOnUnitInterval ν₀
  supported₁ : IsSupportedOnUnitInterval ν₁
  symmetric₀ : IsSymmetric ν₀
  symmetric₁ : IsSymmetric ν₁
  moments_eq : ∀ j : ℕ, j ≤ K →
    ∫ x : ℝ, x ^ j ∂ν₀ = ∫ x : ℝ, x ^ j ∂ν₁
  abs_gap :
    (∫ x : ℝ, |x| ∂ν₁) - (∫ x : ℝ, |x| ∂ν₀) =
      2 * bestUniformApproxErrorAbs K

/-- For [a nonnegative moment-degree limit](hyp:K) and [an absolute-value extremal decomposition at that limit](hyp:D), [the associated pair of moment-matched priors](goal) has [first prior equal to twice the decomposition's negative measure](step:1) and second prior equal to twice its positive measure.

Doubling the two already oriented Jordan parts of an extremal decomposition produces the symmetric probability-prior pair. -/
noncomputable def AbsExtremalDecomposition.toMomentMatchedPriors
    {K : ℕ} (D : AbsExtremalDecomposition K) : AbsMomentMatchedPriors K := by
  let ν₀ : Measure ℝ := (2 : ENNReal) • D.negative
  let ν₁ : Measure ℝ := (2 : ENNReal) • D.positive
  refine
    { ν₀ := ν₀
      ν₁ := ν₁
      probability₀ := ?_
      probability₁ := ?_
      supported₀ := ?_
      supported₁ := ?_
      symmetric₀ := ?_
      symmetric₁ := ?_
      moments_eq := ?_
      abs_gap := ?_ }
  · constructor
    simp only [ν₀, Measure.smul_apply, D.negative_mass]
    simpa [smul_eq_mul, div_eq_inv_mul] using
      (ENNReal.mul_inv_cancel (a := (2 : ENNReal)) (by norm_num) (by norm_num))
  · constructor
    simp only [ν₁, Measure.smul_apply, D.positive_mass]
    simpa [smul_eq_mul, div_eq_inv_mul] using
      (ENNReal.mul_inv_cancel (a := (2 : ENNReal)) (by norm_num) (by norm_num))
  · dsimp only [IsSupportedOnUnitInterval, ν₀]
    rw [Measure.smul_apply, D.negative_supported]
    simp
  · dsimp only [IsSupportedOnUnitInterval, ν₁]
    rw [Measure.smul_apply, D.positive_supported]
    simp
  · simpa [IsSymmetric, ν₀, Measure.map_smul] using
      congrArg ((2 : ENNReal) • ·) D.negative_symmetric
  · simpa [IsSymmetric, ν₁, Measure.map_smul] using
      congrArg ((2 : ENNReal) • ·) D.positive_symmetric
  · intro j hj
    simp only [ν₀, ν₁, integral_smul_measure, ENNReal.toReal_ofNat]
    rw [D.moments_eq j hj]
  · simp only [ν₀, ν₁, integral_smul_measure, ENNReal.toReal_ofNat, smul_eq_mul]
    linarith [D.abs_gap]

/-- For [a positive even degree](hyp:K,_hK,_hEven), [a symmetric moment-matched probability-prior pair with the exact absolute-moment gap exists](goal).

 For every positive even degree, there are symmetric Borel probability
measures supported on `[-1,1]`, matching all moments through that degree, whose
absolute first moments differ by exactly twice the best approximation error. -/
theorem exists_symmetric_momentMatched_absGap
    {K : ℕ} (_hK : 0 < K) (_hEven : Even K) :
    Nonempty (AbsMomentMatchedPriors K) := by
  obtain ⟨D⟩ := exists_absExtremalDecomposition K
  exact ⟨D.toMomentMatchedPriors⟩

/-- For [a packaged prior pair](hyp:K,P), [its first prior is a probability measure](goal).

 The first prior in a packaged pair is a probability measure. -/
theorem priorZero_isProbabilityMeasure {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsProbabilityMeasure P.ν₀ :=
  P.probability₀

/-- For [a packaged prior pair](hyp:K,P), [its second prior is a probability measure](goal).

 The second prior in a packaged pair is a probability measure. -/
theorem priorOne_isProbabilityMeasure {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsProbabilityMeasure P.ν₁ :=
  P.probability₁

/-- For [a packaged prior pair](hyp:K,P), [its first prior has total mass one](goal).

 The first prior has total mass one. -/
theorem priorZero_mass {K : ℕ} (P : AbsMomentMatchedPriors K) :
    P.ν₀ Set.univ = 1 := by
  exact P.probability₀.measure_univ

/-- For [a packaged prior pair](hyp:K,P), [its second prior has total mass one](goal).

 The second prior has total mass one. -/
theorem priorOne_mass {K : ℕ} (P : AbsMomentMatchedPriors K) :
    P.ν₁ Set.univ = 1 := by
  exact P.probability₁.measure_univ

/-- For [a packaged prior pair](hyp:K,P), [its first prior is supported on the unit interval](goal).

 The first prior is supported on `[-1,1]`. -/
theorem priorZero_supported {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsSupportedOnUnitInterval P.ν₀ :=
  P.supported₀

/-- For [a packaged prior pair](hyp:K,P), [its second prior is supported on the unit interval](goal).

 The second prior is supported on `[-1,1]`. -/
theorem priorOne_supported {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsSupportedOnUnitInterval P.ν₁ :=
  P.supported₁

/-- For [a packaged prior pair](hyp:K,P), [its first prior is symmetric about zero](goal).

 The first prior is symmetric about zero. -/
theorem priorZero_symmetric {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsSymmetric P.ν₀ :=
  P.symmetric₀

/-- For [a packaged prior pair](hyp:K,P), [its second prior is symmetric about zero](goal).

 The second prior is symmetric about zero. -/
theorem priorOne_symmetric {K : ℕ} (P : AbsMomentMatchedPriors K) :
    IsSymmetric P.ν₁ :=
  P.symmetric₁

/-- For [a packaged prior pair](hyp:K,P) and [a moment order no larger than the degree limit](hyp:j,hj), [the two priors have equal moments of that order](goal).

 The two priors have equal `j`-th moments for every `j ≤ K`. -/
theorem prior_moments_eq {K : ℕ} (P : AbsMomentMatchedPriors K)
    {j : ℕ} (hj : j ≤ K) :
    ∫ x : ℝ, x ^ j ∂P.ν₀ = ∫ x : ℝ, x ^ j ∂P.ν₁ :=
  P.moments_eq j hj

/-- For [a packaged prior pair](hyp:K,P), [the oriented difference in absolute first moments is twice the best approximation error](goal).

 The oriented difference of the priors' absolute first moments is exactly
`2 E_K`. -/
theorem prior_absMoment_gap {K : ℕ} (P : AbsMomentMatchedPriors K) :
    (∫ x : ℝ, |x| ∂P.ν₁) - (∫ x : ℝ, |x| ∂P.ν₀) =
      2 * bestUniformApproxErrorAbs K :=
  P.abs_gap

end Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality
