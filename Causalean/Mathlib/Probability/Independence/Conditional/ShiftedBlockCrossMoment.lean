module
public import Causalean.Mathlib.Probability.Independence.Conditional.ShiftedBlockMoments
public import Mathlib.Probability.Moments.Covariance

/-!
# Conditional cross moment of one training-shifted held-out block

The cross moment of two held-out scores shifted by training-measurable
functions is their unconditional covariance plus the product of their shifted
means. This is the local calculation used by the three-block factorization.
-/

public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence

namespace Causalean.Mathlib.Probability.Independence.Conditional

variable {ι : Type*} [Fintype ι]
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  [∀ i, StandardBorelSpace (Ω i)]

/-- [A finite product probability law](hyp:μ), [disjoint training and held-out
blocks](hyp:B0,B1,hdisj), [two held-out scores](hyp:f,g), [two training shifts](hyp:a,b),
[measurability](hyp:hfmeas,hgmeas,hameas,hbmeas), [integrability of the scores and
shifts](hyp:hf,hg,ha,hb), [an integrable held-out cross product](hyp:hfg), and
[square-integrable shifted scores](hyp:hflp,hglp) imply that [their conditional cross
moment equals unconditional covariance plus the product of shifted means](goal). -/
theorem condExp_shiftedBlockCross_eq_covariance_add
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (B0 B1 : Finset ι) (hdisj : Disjoint B0 B1)
    (f g : ((i : {i // i ∈ B1}) → Ω i.val) → ℝ)
    (a b : ((i : {i // i ∈ B0}) → Ω i.val) → ℝ)
    (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hameas : Measurable a) (hbmeas : Measurable b)
    (hf : Integrable (fun x : ∀ i, Ω i => f (finsetCoordProj B1 x))
      (Measure.pi μ))
    (hg : Integrable (fun x : ∀ i, Ω i => g (finsetCoordProj B1 x))
      (Measure.pi μ))
    (ha : Integrable (fun x : ∀ i, Ω i => a (finsetCoordProj B0 x))
      (Measure.pi μ))
    (hb : Integrable (fun x : ∀ i, Ω i => b (finsetCoordProj B0 x))
      (Measure.pi μ))
    (hfg : Integrable (fun x : ∀ i, Ω i =>
      f (finsetCoordProj B1 x) * g (finsetCoordProj B1 x)) (Measure.pi μ))
    (hflp : MemLp (fun x : ∀ i, Ω i =>
      f (finsetCoordProj B1 x) - a (finsetCoordProj B0 x)) 2 (Measure.pi μ))
    (hglp : MemLp (fun x : ∀ i, Ω i =>
      g (finsetCoordProj B1 x) - b (finsetCoordProj B0 x)) 2 (Measure.pi μ)) :
    condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ)
      (fun x : ∀ i, Ω i =>
        (f (finsetCoordProj B1 x) - a (finsetCoordProj B0 x)) *
        (g (finsetCoordProj B1 x) - b (finsetCoordProj B0 x))) =ᵐ[Measure.pi μ]
    (fun x => covariance
      (fun y : ∀ i, Ω i => f (finsetCoordProj B1 y))
      (fun y : ∀ i, Ω i => g (finsetCoordProj B1 y))
      (Measure.pi μ) +
      ((∫ y : (∀ i, Ω i), f (finsetCoordProj B1 y) ∂Measure.pi μ) -
        a (finsetCoordProj B0 x)) *
      ((∫ y : (∀ i, Ω i), g (finsetCoordProj B1 y) ∂Measure.pi μ) -
        b (finsetCoordProj B0 x))) := by
  let P : Measure (∀ i, Ω i) := Measure.pi μ
  let m : MeasurableSpace (∀ i, Ω i) :=
    MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) MeasurableSpace.pi
  let F : (∀ i, Ω i) → ℝ := fun x => f (finsetCoordProj B1 x)
  let G : (∀ i, Ω i) → ℝ := fun x => g (finsetCoordProj B1 x)
  let A : (∀ i, Ω i) → ℝ := fun x => a (finsetCoordProj B0 x)
  let B : (∀ i, Ω i) → ℝ := fun x => b (finsetCoordProj B0 x)
  have hle : m ≤ MeasurableSpace.pi := by
    exact (measurable_finsetCoordProj (Ω := Ω) B0).comap_le
  haveI : IsFiniteMeasure P := inferInstance
  haveI : IsFiniteMeasure (P.trim hle) := isFiniteMeasure_trim hle
  have hA : StronglyMeasurable[m] A := by
    have hp : Measurable[m] (finsetCoordProj (Ω := Ω) B0) :=
      measurable_iff_comap_le.mpr le_rfl
    exact (hameas.comp hp).stronglyMeasurable
  have hB : StronglyMeasurable[m] B := by
    have hp : Measurable[m] (finsetCoordProj (Ω := Ω) B0) :=
      measurable_iff_comap_le.mpr le_rfl
    exact (hbmeas.comp hp).stronglyMeasurable
  have hfg' : Integrable (F * G) P := hfg
  have hFint : (Fintype.ofFinite ι) = (inferInstance : Fintype ι) :=
    Subsingleton.elim _ _
  have hpi : @Measure.pi ι Ω (Fintype.ofFinite ι) _ μ = P :=
    congrArg (fun fi : Fintype ι => @Measure.pi ι Ω fi _ μ) hFint
  have hfb : Integrable (F * B) P := by
    have hi := (indepFun_pi_of_disjoint (Ω := Ω) μ hdisj.symm).comp hfmeas hbmeas
    have hi' : IndepFun F B P := by
      change IndepFun (fun x : ∀ i, Ω i => f (fun i => x i.val))
        (fun x : ∀ i, Ω i => b (fun i => x i.val)) P
      simpa only [hpi, Function.comp_def] using hi
    exact hi'.integrable_mul hf hb
  have hag : Integrable (A * G) P := by
    have hi := (indepFun_pi_of_disjoint (Ω := Ω) μ hdisj).comp hameas hgmeas
    have hi' : IndepFun A G P := by
      change IndepFun (fun x : ∀ i, Ω i => a (fun i => x i.val))
        (fun x : ∀ i, Ω i => g (fun i => x i.val)) P
      simpa only [hpi, Function.comp_def] using hi
    exact hi'.integrable_mul ha hg
  have hshift : Integrable ((F - A) * (G - B)) P := hflp.integrable_mul hglp
  have hab : Integrable (A * B) P := by
    have heq : A * B = ((F - A) * (G - B)) - (F * G) + (F * B) + (A * G) := by
      funext x
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
      ring
    rw [heq]
    exact ((hshift.sub hfg').add hfb).add hag
  have hcov : covariance F G P = (∫ x, F x * G x ∂P) - (∫ x, F x ∂P) * (∫ x, G x ∂P) := by
    simp_rw [covariance, sub_mul, mul_sub]
    repeat rw [integral_sub]
    · simp_rw [integral_mul_const, integral_const_mul, integral_const,
        probReal_univ, one_smul]
      ring
    · exact hg.const_mul _
    · exact integrable_const _
    · exact hfg'
    · exact hf.mul_const _
    · exact (hfg'.sub (hf.mul_const _))
    · exact (hg.const_mul _).sub (integrable_const _)
  have hcross := condExp_heldoutBlock_eq_integral μ B0 B1 hdisj
    (fun z => f z * g z) (hfmeas.mul hgmeas) hfg
  have hF := condExp_heldoutBlock_eq_integral μ B0 B1 hdisj f hfmeas hf
  have hG := condExp_heldoutBlock_eq_integral μ B0 B1 hdisj g hgmeas hg
  have hAB : condExp m P (A * B) =ᵐ[P] A * B := by
    rw [condExp_of_stronglyMeasurable hle (hA.mul hB) hab]
  have hFB : condExp m P (F * B) =ᵐ[P] (fun x => (∫ y, F y ∂P) * B x) := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_right hB hfb hf, hF]
      with x hx hy
    simpa only [Pi.mul_apply] using hx.trans (congrArg (fun z : ℝ => z * B x) hy)
  have hAG : condExp m P (A * G) =ᵐ[P] (fun x => A x * (∫ y, G y ∂P)) := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hA hag hg, hG]
      with x hx hy
    simpa only [Pi.mul_apply] using hx.trans (congrArg (fun z : ℝ => A x * z) hy)
  have hexpand : (F - A) * (G - B) = F * G - F * B - A * G + A * B := by
    funext x
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
    ring
  change condExp m P ((F - A) * (G - B)) =ᵐ[P]
    (fun x => covariance F G P + ((∫ y, F y ∂P) - A x) * ((∫ y, G y ∂P) - B x))
  rw [hexpand]
  have hlin : condExp m P (F * G - F * B - A * G + A * B) =ᵐ[P]
      condExp m P (F * G) - condExp m P (F * B) -
        condExp m P (A * G) + condExp m P (A * B) := by
    have h1 := condExp_sub hfg' hfb m
    have h2 := condExp_sub (hfg'.sub hfb) hag m
    have h3 := condExp_add ((hfg'.sub hfb).sub hag) hab m
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    simp only [Pi.add_apply, Pi.sub_apply] at *
    rw [hx3, hx2, hx1]
  filter_upwards [hlin, hcross, hFB, hAG, hAB] with x hx hc hfbx hagx habx
  simp only [Pi.sub_apply, Pi.add_apply] at hx
  have hc' : condExp m P (F * G) x = ∫ y, F y * G y ∂P := hc
  rw [hx, hc', hfbx, hagx, habx, hcov]
  simp only [Pi.mul_apply]
  ring

end Causalean.Mathlib.Probability.Independence.Conditional
