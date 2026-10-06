module
public import Causalean.PO.Bridge.FiniteCellOneDraw
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Two-draw finite-cell pair moments

Independent observations from the induced observed law admit pair-kernel
expectation formulas in terms of the covariate law, arm probabilities, and arm
regressions. A measurable integrable covariate-pair weight can localize either
formula. Centering functions may be unbounded when the displayed envelope is
integrable.
-/

public section

open MeasureTheory
open Causalean.PO.Bridge

namespace Causalean.PO.Bridge

variable {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (D : FiniteCellData Ω γ μ)

/-- A [finite-cell observed table](hyp:D) sends the covariates of two
independent observed-law draws to [two independent draws from the covariate
law](goal). -/
theorem pair_covariate_map :
    (D.observedLaw.prod D.observedLaw).map
        (fun z : (γ × Bool × Bool) × (γ × Bool × Bool) => (z.1.1, z.2.1)) =
      (μ.map D.X).prod (μ.map D.X) := by
  letI : IsProbabilityMeasure D.observedLaw := observedLaw_isProbability D
  have hY : Measurable (observedY D.A D.Y0 D.Y1) :=
    Measurable.ite
      (measurableSet_eq_fun D.measurable_A measurable_const)
      D.measurable_Y1 D.measurable_Y0
  have hobs : Measurable
      (fun ω => (D.X ω, D.A ω, observedY D.A D.Y0 D.Y1 ω)) :=
    D.measurable_X.prodMk (D.measurable_A.prodMk hY)
  have hmarg : D.observedLaw.map Prod.fst = μ.map D.X := by
    rw [D.observedLaw_eq_map, Measure.map_map measurable_fst hobs]
    rfl
  calc
    _ = (D.observedLaw.map Prod.fst).prod (D.observedLaw.map Prod.fst) := by
      have hfun : (fun z : (γ × Bool × Bool) × (γ × Bool × Bool) =>
          (z.1.1, z.2.1)) = Prod.map Prod.fst Prod.fst := by
        funext z
        rfl
      rw [hfun]
      exact (Measure.map_prod_map D.observedLaw D.observedLaw
        measurable_fst measurable_fst).symm
    _ = _ := by rw [hmarg]

/-- A [finite-cell observed table](hyp:D), [two treatment arms](hyp:d,e),
[covariate-pair weight](hyp:W), [measurability of that weight](hyp:hW), and
[its integrability under the independent covariate-pair law](hyp:hInt) give
[the independent two-draw treatment-arm kernel expectation through the two arm
probabilities](goal). -/
theorem integral_pair_arm (d e : Bool) (W : γ → γ → ℝ)
    (hW : Measurable fun p : γ × γ => W p.1 p.2)
    (hInt : Integrable (fun p : γ × γ => W p.1 p.2)
      ((μ.map D.X).prod (μ.map D.X))) :
    ∫ z : (γ × Bool × Bool) × (γ × Bool × Bool),
        W z.1.1 z.2.1 * armIndicator d z.1.2.1 *
          armIndicator e z.2.2.1 ∂(D.observedLaw.prod D.observedLaw) =
      ∫ p : γ × γ,
        W p.1 p.2 * D.armProb d p.1 * D.armProb e p.2
          ∂((μ.map D.X).prod (μ.map D.X)) := by
  letI : IsProbabilityMeasure D.observedLaw := observedLaw_isProbability D
  let ν : Measure γ := μ.map D.X
  let ρ : Measure (γ × Bool × Bool) := D.observedLaw
  let F : γ × γ → ℝ := fun p => W p.1 p.2
  have hν : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map D.measurable_X.aemeasurable
  letI : IsProbabilityMeasure ν := hν
  have hF : Integrable F (ν.prod ν) := hInt
  have hA (a : Bool) : Measurable (fun z : γ × Bool × Bool => armIndicator a z.2.1) := by
    unfold armIndicator
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
      measurable_const measurable_const
  have hAb (a : Bool) (z : γ × Bool × Bool) : ‖armIndicator a z.2.1‖ ≤ 1 := by
    simp only [armIndicator]
    split_ifs <;> simp
  have hPb (a : Bool) (x : γ) : ‖D.armProb a x‖ ≤ 1 := by
    have hx := D.armProb_mem_Icc a x
    simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hρF : Integrable (fun z : (γ × Bool × Bool) × (γ × Bool × Bool) =>
      W z.1.1 z.2.1) (ρ.prod ρ) := by
    rw [← pair_covariate_map D] at hF
    exact (integrable_map_measure hW.aestronglyMeasurable
      (measurable_fst.comp measurable_fst |>.prodMk
        (measurable_fst.comp measurable_snd)).aemeasurable).1 hF
  have hρFF : Integrable (fun z : (γ × Bool × Bool) × (γ × Bool × Bool) =>
      W z.1.1 z.2.1 * armIndicator d z.1.2.1 * armIndicator e z.2.2.1)
      (ρ.prod ρ) := by
    have h₁ := hρF.mul_bdd
      ((hA d).comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ fun z => hAb d z.1)
    exact h₁.mul_bdd
      ((hA e).comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ fun z => hAb e z.2)
  have hFP : Integrable (fun p : γ × γ => W p.1 p.2 * D.armProb e p.2)
      (ν.prod ν) :=
    hF.mul_bdd ((D.measurable_armProb e).comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ fun p => hPb e p.2)
  have hFPP : Integrable (fun p : γ × γ =>
      W p.1 p.2 * D.armProb d p.1 * D.armProb e p.2) (ν.prod ν) := by
    convert (hFP.mul_bdd
      ((D.measurable_armProb d).comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ fun p => hPb d p.1)) using 1 <;> funext p <;> dsimp <;> ring
  let g : γ → ℝ := fun x => ∫ y, W x y * D.armProb e y ∂ν
  have hg : Integrable g ν := hFP.integral_prod_left
  have hgm : Measurable g := by
    exact ((hW.mul ((D.measurable_armProb e).comp measurable_snd)).stronglyMeasurable
      |>.integral_prod_right').measurable
  have hslice : ∀ᵐ z ∂ρ, Integrable (fun y => W z.1 y) ν := by
    have hY : Measurable (observedY D.A D.Y0 D.Y1) :=
      Measurable.ite
        (measurableSet_eq_fun D.measurable_A measurable_const)
        D.measurable_Y1 D.measurable_Y0
    have hobs : Measurable
        (fun ω => (D.X ω, D.A ω, observedY D.A D.Y0 D.Y1 ω)) :=
      D.measurable_X.prodMk (D.measurable_A.prodMk hY)
    have hmarg : ρ.map Prod.fst = ν := by
      dsimp [ρ, ν]
      rw [D.observedLaw_eq_map, Measure.map_map measurable_fst hobs]
      rfl
    have h := hF.prod_right_ae
    change ∀ᵐ x ∂ν, Integrable (fun y => W x y) ν at h
    have h' : ∀ᵐ x ∂ρ.map Prod.fst, Integrable (fun y => W x y) ν := by
      rw [hmarg]
      exact h
    exact ae_of_ae_map measurable_fst.aemeasurable h'
  calc
    _ = ∫ z : γ × Bool × Bool,
        (∫ t : γ × Bool × Bool,
          W z.1 t.1 * armIndicator d z.2.1 * armIndicator e t.2.1 ∂ρ) ∂ρ :=
      integral_prod _ hρFF
    _ = ∫ z : γ × Bool × Bool, g z.1 * armIndicator d z.2.1 ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hslice] with z hz
      calc
        _ = (∫ t : γ × Bool × Bool,
            W z.1 t.1 * armIndicator e t.2.1 ∂ρ) * armIndicator d z.2.1 := by
          rw [← integral_mul_const]
          congr 1
          funext t
          ring
        _ = g z.1 * armIndicator d z.2.1 := by
          rw [integral_observedLaw_weighted_arm D e (W z.1)
            (hW.comp (measurable_const.prodMk measurable_id)) hz]
    _ = ∫ x, g x * D.armProb d x ∂ν :=
      integral_observedLaw_weighted_arm D d g hgm hg
    _ = ∫ p : γ × γ,
        W p.1 p.2 * D.armProb d p.1 * D.armProb e p.2 ∂(ν.prod ν) := by
      rw [integral_prod _ hFPP]
      apply integral_congr_ae
      filter_upwards with x
      rw [← integral_mul_const]
      congr 1
      funext y
      ring

/-- A [finite-cell observed table](hyp:D), [two treatment arms](hyp:d,e),
[covariate-pair weight](hyp:W), [two centering functions](hyp:c,k),
[measurability of the weight](hyp:hW), [measurability of both centers](hyp:hc,hk),
and [integrability of the displayed envelope under the independent covariate-pair
law](hyp:hInt) give [the centered observed-outcome product expectation through
arm probabilities and arm regressions](goal). The integrable envelope permits
unbounded centering functions. -/
theorem integral_pair_centered (d e : Bool) (W : γ → γ → ℝ)
    (c k : γ → ℝ)
    (hW : Measurable fun p : γ × γ => W p.1 p.2)
    (hc : Measurable c) (hk : Measurable k)
    (hInt : Integrable
      (fun p : γ × γ => |W p.1 p.2| * (1 + |c p.1|) * (1 + |k p.2|))
      ((μ.map D.X).prod (μ.map D.X))) :
    ∫ z : (γ × Bool × Bool) × (γ × Bool × Bool),
        W z.1.1 z.2.1 *
          (armIndicator d z.1.2.1 * (boolReal z.1.2.2 - c z.1.1)) *
          (armIndicator e z.2.2.1 * (boolReal z.2.2.2 - k z.2.1))
          ∂(D.observedLaw.prod D.observedLaw) =
      ∫ p : γ × γ,
        W p.1 p.2 *
          (D.armProb d p.1 * (D.mean d p.1 - c p.1)) *
          (D.armProb e p.2 * (D.mean e p.2 - k p.2))
          ∂((μ.map D.X).prod (μ.map D.X)) := by
  -- Put `ν := μ.map D.X` and `ρ := D.observedLaw`. The hypothesis controls
  -- `W`, `W * c`, `W * k`, and `W * c * k` on `ν.prod ν` by domination.
  -- Transport that envelope to `ρ.prod ρ` with `pair_covariate_map`; both
  -- centered factors are bounded by `1 + |center|` pointwise. Fubini then
  -- applies to the displayed left integrand. For almost every first draw,
  -- use `integral_observedLaw_weighted_centered D e` on the second draw,
  -- with slice weight `y ↦ W x y`; Fubini's `prod_right_ae` gives the weight
  -- and weight-times-k integrability. Integrate the resulting function of x
  -- using the same one-draw theorem for d. The outer weight is the integral
  -- in y of `W x y * (armProb e y * (mean e y - k y))`; its integrability and
  -- its product with c follow from the original envelope and Fubini.
  letI : IsProbabilityMeasure D.observedLaw := observedLaw_isProbability D
  let ν : Measure γ := μ.map D.X
  let ρ : Measure (γ × Bool × Bool) := D.observedLaw
  have hν : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map D.measurable_X.aemeasurable
  letI : IsProbabilityMeasure ν := hν
  let E : γ × γ → ℝ := fun p =>
    |W p.1 p.2| * (1 + |c p.1|) * (1 + |k p.2|)
  have hE : Integrable E (ν.prod ν) := hInt
  have hEm : Measurable E := by
    dsimp [E]
    fun_prop
  have hWint : Integrable (fun p : γ × γ => W p.1 p.2) (ν.prod ν) := by
    apply hE.mono' hW.aestronglyMeasurable
    filter_upwards with p
    dsimp [E]
    have hc0 : 0 ≤ |c p.1| := abs_nonneg _
    have hk0 : 0 ≤ |k p.2| := abs_nonneg _
    calc
      |W p.1 p.2| = |W p.1 p.2| * 1 * 1 := by ring
      _ ≤ |W p.1 p.2| * (1 + |c p.1|) * (1 + |k p.2|) := by
        gcongr <;> linarith
  have hWc : Integrable (fun p : γ × γ => W p.1 p.2 * c p.1) (ν.prod ν) := by
    apply hE.mono' (hW.mul (hc.comp measurable_fst)).aestronglyMeasurable
    filter_upwards with p
    dsimp [E]
    rw [abs_mul]
    have hc0 : 0 ≤ |c p.1| := abs_nonneg _
    have hk0 : 0 ≤ |k p.2| := abs_nonneg _
    calc
      |W p.1 p.2| * |c p.1| = |W p.1 p.2| * |c p.1| * 1 := by ring
      _ ≤ |W p.1 p.2| * (1 + |c p.1|) * (1 + |k p.2|) := by
        gcongr <;> linarith
  have hWk : Integrable (fun p : γ × γ => W p.1 p.2 * k p.2) (ν.prod ν) := by
    apply hE.mono' (hW.mul (hk.comp measurable_snd)).aestronglyMeasurable
    filter_upwards with p
    dsimp [E]
    rw [abs_mul]
    have hc0 : 0 ≤ |c p.1| := abs_nonneg _
    have hk0 : 0 ≤ |k p.2| := abs_nonneg _
    calc
      |W p.1 p.2| * |k p.2| = |W p.1 p.2| * 1 * |k p.2| := by ring
      _ ≤ |W p.1 p.2| * (1 + |c p.1|) * (1 + |k p.2|) := by
        gcongr <;> linarith
  have hWck : Integrable (fun p : γ × γ => W p.1 p.2 * c p.1 * k p.2)
      (ν.prod ν) := by
    apply hE.mono' ((hW.mul (hc.comp measurable_fst)).mul
      (hk.comp measurable_snd)).aestronglyMeasurable
    filter_upwards with p
    dsimp [E]
    rw [abs_mul, abs_mul]
    have hc0 : 0 ≤ |c p.1| := abs_nonneg _
    have hk0 : 0 ≤ |k p.2| := abs_nonneg _
    gcongr <;> linarith
  have hArm (a : Bool) : Measurable
      (fun z : γ × Bool × Bool => armIndicator a z.2.1) := by
    unfold armIndicator
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
      measurable_const measurable_const
  have hBool : Measurable
      (fun z : γ × Bool × Bool => boolReal z.2.2) := by
    unfold boolReal
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const)
      measurable_const measurable_const
  have hArmB (a b : Bool) : |armIndicator a b| ≤ (1 : ℝ) := by
    simp only [armIndicator]
    split_ifs <;> simp
  have hBoolB (b : Bool) : |boolReal b| ≤ (1 : ℝ) := by
    simp only [boolReal]
    split_ifs <;> simp
  have hCenteredB (b : Bool) (r : ℝ) : |boolReal b - r| ≤ 1 + |r| := by
    calc
      _ ≤ |boolReal b| + |r| := abs_sub _ _
      _ ≤ 1 + |r| := add_le_add_left (hBoolB b) _
  have hMeanB (a : Bool) (x : γ) : |D.mean a x| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg (D.mean_mem_Icc a x).1]
    exact (D.mean_mem_Icc a x).2
  have hProbB (a : Bool) (x : γ) : |D.armProb a x| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg (D.armProb_mem_Icc a x).1]
    exact (D.armProb_mem_Icc a x).2
  have hObsB (a : Bool) (z : γ × Bool × Bool) (r : ℝ) :
      |armIndicator a z.2.1 * (boolReal z.2.2 - r)| ≤ 1 + |r| := by
    rw [abs_mul]
    calc
      _ ≤ 1 * (1 + |r|) := by
        gcongr
        · exact hArmB a z.2.1
        · exact hCenteredB z.2.2 r
      _ = _ := by ring
  let pairX : ((γ × Bool × Bool) × (γ × Bool × Bool)) → γ × γ :=
    fun z => (z.1.1, z.2.1)
  have hpairX : Measurable pairX :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)
  have hρE : Integrable (fun z : (γ × Bool × Bool) × (γ × Bool × Bool) =>
      E (pairX z)) (ρ.prod ρ) := by
    rw [← pair_covariate_map D] at hE
    exact (integrable_map_measure hEm.aestronglyMeasurable hpairX.aemeasurable).1 hE
  have hL : Integrable (fun z : (γ × Bool × Bool) × (γ × Bool × Bool) =>
      W z.1.1 z.2.1 *
        (armIndicator d z.1.2.1 * (boolReal z.1.2.2 - c z.1.1)) *
        (armIndicator e z.2.2.1 * (boolReal z.2.2.2 - k z.2.1)))
      (ρ.prod ρ) := by
    apply hρE.mono' ?_ ?_
    · have hm : Measurable (fun z : (γ × Bool × Bool) × (γ × Bool × Bool) =>
          W z.1.1 z.2.1 *
            (armIndicator d z.1.2.1 * (boolReal z.1.2.2 - c z.1.1)) *
            (armIndicator e z.2.2.1 * (boolReal z.2.2.2 - k z.2.1))) := by
        fun_prop (disch := assumption)
      exact hm.aestronglyMeasurable
    · filter_upwards with z
      dsimp [E, pairX]
      simp only [Real.norm_eq_abs, abs_mul]
      gcongr
      · simpa only [abs_mul] using hObsB d z.1 (c z.1.1)
      · simpa only [abs_mul] using hObsB e z.2 (k z.2.1)
  let Q : γ → ℝ := fun y => D.armProb e y * (D.mean e y - k y)
  have hQm : Measurable Q := by
    exact (D.measurable_armProb e).mul ((D.measurable_mean e).sub hk)
  have hFQ : Integrable (fun p : γ × γ => W p.1 p.2 * Q p.2) (ν.prod ν) := by
    have h₁ := hWint.mul_bdd
      (((D.measurable_armProb e).comp measurable_snd).aestronglyMeasurable)
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hProbB e p.2)
    have h₂ := h₁.mul_bdd
      (((D.measurable_mean e).comp measurable_snd).aestronglyMeasurable)
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hMeanB e p.2)
    have h₃ := hWk.mul_bdd
      (((D.measurable_armProb e).comp measurable_snd).aestronglyMeasurable)
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hProbB e p.2)
    convert h₂.sub h₃ using 1 <;> funext p <;> dsimp [Q] <;> ring
  have hFcQ : Integrable
      (fun p : γ × γ => (W p.1 p.2 * Q p.2) * c p.1) (ν.prod ν) := by
    have h₁ := hWc.mul_bdd
      (((D.measurable_armProb e).comp measurable_snd).aestronglyMeasurable)
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hProbB e p.2)
    have h₂ := h₁.mul_bdd
      (((D.measurable_mean e).comp measurable_snd).aestronglyMeasurable)
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hMeanB e p.2)
    have h₃ := hWck.mul_bdd
      (((D.measurable_armProb e).comp measurable_snd).aestronglyMeasurable)
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hProbB e p.2)
    convert h₂.sub h₃ using 1 <;> funext p <;> dsimp [Q] <;> ring
  let g : γ → ℝ := fun x => ∫ y, W x y * Q y ∂ν
  have hg : Integrable g ν := hFQ.integral_prod_left
  have hgc : Integrable (fun x => g x * c x) ν := by
    convert hFcQ.integral_prod_left using 1
    funext x
    dsimp [g]
    rw [integral_mul_const]
  have hgm : Measurable g := by
    exact ((hW.mul (hQm.comp measurable_snd)).stronglyMeasurable
      |>.integral_prod_right').measurable
  have hslice : ∀ᵐ z ∂ρ,
      Integrable (fun y => W z.1 y) ν ∧
      Integrable (fun y => W z.1 y * k y) ν := by
    have hY : Measurable (observedY D.A D.Y0 D.Y1) :=
      Measurable.ite
        (measurableSet_eq_fun D.measurable_A measurable_const)
        D.measurable_Y1 D.measurable_Y0
    have hobs : Measurable
        (fun ω => (D.X ω, D.A ω, observedY D.A D.Y0 D.Y1 ω)) :=
      D.measurable_X.prodMk (D.measurable_A.prodMk hY)
    have hmarg : ρ.map Prod.fst = ν := by
      dsimp [ρ, ν]
      rw [D.observedLaw_eq_map, Measure.map_map measurable_fst hobs]
      rfl
    have hs : ∀ᵐ x ∂ν,
        Integrable (fun y => W x y) ν ∧
        Integrable (fun y => W x y * k y) ν := by
      filter_upwards [hWint.prod_right_ae, hWk.prod_right_ae] with x hx hy
      exact ⟨hx, hy⟩
    have hs' : ∀ᵐ x ∂ρ.map Prod.fst,
        Integrable (fun y => W x y) ν ∧
        Integrable (fun y => W x y * k y) ν := by
      rw [hmarg]
      exact hs
    exact ae_of_ae_map measurable_fst.aemeasurable hs'
  have hR : Integrable (fun p : γ × γ =>
      W p.1 p.2 *
        (D.armProb d p.1 * (D.mean d p.1 - c p.1)) * Q p.2)
      (ν.prod ν) := by
    have h₁ := hFQ.mul_bdd
      (((D.measurable_armProb d).comp measurable_fst).aestronglyMeasurable)
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hProbB d p.1)
    have h₂ := h₁.mul_bdd
      (((D.measurable_mean d).comp measurable_fst).aestronglyMeasurable)
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hMeanB d p.1)
    have h₃ := hFcQ.mul_bdd
      (((D.measurable_armProb d).comp measurable_fst).aestronglyMeasurable)
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hProbB d p.1)
    convert h₂.sub h₃ using 1 <;> funext p <;> dsimp [Q] <;> ring
  have hmarg : ρ.map Prod.fst = ν := by
    have hY : Measurable (observedY D.A D.Y0 D.Y1) :=
      Measurable.ite
        (measurableSet_eq_fun D.measurable_A measurable_const)
        D.measurable_Y1 D.measurable_Y0
    have hobs : Measurable
        (fun ω => (D.X ω, D.A ω, observedY D.A D.Y0 D.Y1 ω)) :=
      D.measurable_X.prodMk (D.measurable_A.prodMk hY)
    dsimp [ρ, ν]
    rw [D.observedLaw_eq_map, Measure.map_map measurable_fst hobs]
    rfl
  have hCentered (a : Bool) (w r : γ → ℝ)
      (hwmeas : Measurable w) (hrmeas : Measurable r)
      (hw : Integrable w ν) (hwr : Integrable (fun x => w x * r x) ν) :
      ∫ z : γ × Bool × Bool,
          w z.1 * (armIndicator a z.2.1 * (boolReal z.2.2 - r z.1)) ∂ρ =
        ∫ x, w x * (D.armProb a x * (D.mean a x - r x)) ∂ν := by
    have hbase : Integrable (fun z : γ × Bool × Bool => w z.1) ρ := by
      have hi : Integrable w (ρ.map Prod.fst) := by rwa [hmarg]
      exact (integrable_map_measure hwmeas.aestronglyMeasurable
        measurable_fst.aemeasurable).1 hi
    have hbaser : Integrable (fun z : γ × Bool × Bool => w z.1 * r z.1) ρ := by
      have hi : Integrable (fun x => w x * r x) (ρ.map Prod.fst) := by rwa [hmarg]
      exact (integrable_map_measure (hwmeas.mul hrmeas).aestronglyMeasurable
        measurable_fst.aemeasurable).1 hi
    have hLarm : Integrable
        (fun z : γ × Bool × Bool => w z.1 * armIndicator a z.2.1) ρ :=
      hbase.mul_bdd (hArm a).aestronglyMeasurable
        (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hArmB a z.2.1)
    have hLprod : Integrable (fun z : γ × Bool × Bool =>
        w z.1 * armIndicator a z.2.1 * boolReal z.2.2) ρ :=
      hLarm.mul_bdd hBool.aestronglyMeasurable
        (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hBoolB z.2.2)
    have hLcenter : Integrable (fun z : γ × Bool × Bool =>
        w z.1 * r z.1 * armIndicator a z.2.1) ρ :=
      hbaser.mul_bdd (hArm a).aestronglyMeasurable
        (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hArmB a z.2.1)
    have hRarm : Integrable (fun x => w x * D.armProb a x) ν :=
      hw.mul_bdd (D.measurable_armProb a).aestronglyMeasurable
        (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hProbB a x)
    have hRprod : Integrable (fun x => w x * D.armProb a x * D.mean a x) ν :=
      hRarm.mul_bdd (D.measurable_mean a).aestronglyMeasurable
        (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hMeanB a x)
    have hRcenter : Integrable (fun x => w x * r x * D.armProb a x) ν :=
      hwr.mul_bdd (D.measurable_armProb a).aestronglyMeasurable
        (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hProbB a x)
    calc
      _ = (∫ z : γ × Bool × Bool,
            w z.1 * armIndicator a z.2.1 * boolReal z.2.2 ∂ρ) -
          (∫ z : γ × Bool × Bool,
            (w z.1 * r z.1) * armIndicator a z.2.1 ∂ρ) := by
        rw [← integral_sub hLprod hLcenter]
        congr 1
        funext z
        ring
      _ = (∫ x, w x * D.armProb a x * D.mean a x ∂ν) -
          (∫ x, (w x * r x) * D.armProb a x ∂ν) := by
        exact congrArg₂ (· - ·)
          (integral_observedLaw_weighted_observedProduct D a w hwmeas hw)
          (integral_observedLaw_weighted_arm D a (fun x => w x * r x)
            (hwmeas.mul hrmeas) hwr)
      _ = _ := by
        rw [← integral_sub hRprod hRcenter]
        congr 1
        funext x
        ring
  calc
    _ = ∫ z : γ × Bool × Bool,
        (∫ t : γ × Bool × Bool,
          W z.1 t.1 *
            (armIndicator d z.2.1 * (boolReal z.2.2 - c z.1)) *
            (armIndicator e t.2.1 * (boolReal t.2.2 - k t.1)) ∂ρ) ∂ρ :=
      integral_prod _ hL
    _ = ∫ z : γ × Bool × Bool,
        g z.1 * (armIndicator d z.2.1 * (boolReal z.2.2 - c z.1)) ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hslice] with z hz
      calc
        _ = (∫ t : γ × Bool × Bool,
            W z.1 t.1 *
              (armIndicator e t.2.1 * (boolReal t.2.2 - k t.1)) ∂ρ) *
              (armIndicator d z.2.1 * (boolReal z.2.2 - c z.1)) := by
          rw [← integral_mul_const]
          congr 1
          funext t
          ring
        _ = g z.1 * (armIndicator d z.2.1 * (boolReal z.2.2 - c z.1)) := by
          rw [hCentered e (W z.1) k
            (hW.comp (measurable_const.prodMk measurable_id)) hk hz.1 hz.2]
    _ = ∫ x, g x * (D.armProb d x * (D.mean d x - c x)) ∂ν :=
      hCentered d g c hgm hc hg hgc
    _ = ∫ p : γ × γ,
        W p.1 p.2 *
          (D.armProb d p.1 * (D.mean d p.1 - c p.1)) *
          (D.armProb e p.2 * (D.mean e p.2 - k p.2)) ∂(ν.prod ν) := by
      rw [integral_prod _ hR]
      apply integral_congr_ae
      filter_upwards with x
      rw [← integral_mul_const]
      congr 1
      funext y
      dsimp [g, Q]
      ring

/-- A [finite-cell observed table](hyp:D), [two treatment arms](hyp:d,e),
[pair-eligibility weight](hyp:W), [measurability of that weight](hyp:hW), and
[its integrability under the independent covariate-pair law](hyp:hInt) give
[an arm-regression-centered outcome product with zero two-draw mean](goal). -/
theorem integral_pair_regressionResidual (d e : Bool) (W : γ → γ → ℝ)
    (hW : Measurable fun p : γ × γ => W p.1 p.2)
    (hInt : Integrable (fun p : γ × γ => W p.1 p.2)
      ((μ.map D.X).prod (μ.map D.X))) :
    ∫ z : (γ × Bool × Bool) × (γ × Bool × Bool),
        W z.1.1 z.2.1 *
          (armIndicator d z.1.2.1 * (boolReal z.1.2.2 - D.mean d z.1.1)) *
          (armIndicator e z.2.2.1 * (boolReal z.2.2.2 - D.mean e z.2.1))
          ∂(D.observedLaw.prod D.observedLaw) = 0 := by
  -- The means lie in [0,1], so the envelope in `integral_pair_centered`
  -- is bounded by four times |W|. First derive integrability of that envelope
  -- from `hInt` using `Integrable.mono'`, `D.mean_mem_Icc`, and measurability
  -- of both regressions. Apply `integral_pair_centered` with
  -- `c = D.mean d`, `k = D.mean e`; the right integrand vanishes pointwise.
  have hEnv : Integrable
      (fun p : γ × γ => |W p.1 p.2| * (1 + |D.mean d p.1|) *
        (1 + |D.mean e p.2|)) ((μ.map D.X).prod (μ.map D.X)) := by
    apply Integrable.mono' (hInt.norm.const_mul 4)
    · exact ((hW.norm.mul
        (measurable_const.add ((D.measurable_mean d).comp measurable_fst).norm)).mul
        (measurable_const.add
          ((D.measurable_mean e).comp measurable_snd).norm)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs]
      have hd : |D.mean d p.1| ≤ (1 : ℝ) := by
        rw [abs_of_nonneg (D.mean_mem_Icc d p.1).1]
        exact (D.mean_mem_Icc d p.1).2
      have he : |D.mean e p.2| ≤ (1 : ℝ) := by
        rw [abs_of_nonneg (D.mean_mem_Icc e p.2).1]
        exact (D.mean_mem_Icc e p.2).2
      have hnonneg : 0 ≤ |W p.1 p.2| * (1 + |D.mean d p.1|) *
          (1 + |D.mean e p.2|) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hprod : (1 + |D.mean d p.1|) * (1 + |D.mean e p.2|) ≤
          (4 : ℝ) := by nlinarith [abs_nonneg (D.mean d p.1), abs_nonneg (D.mean e p.2)]
      calc
        _ ≤ |W p.1 p.2| * 4 := by
          simpa only [Pi.mul_apply, Real.norm_eq_abs, mul_assoc] using
            (mul_le_mul_of_nonneg_left hprod (abs_nonneg (W p.1 p.2)))
        _ = 4 * |W p.1 p.2| := by ring
  rw [integral_pair_centered D d e W (D.mean d) (D.mean e) hW
    (D.measurable_mean d) (D.measurable_mean e) hEnv]
  simp

end Causalean.PO.Bridge
