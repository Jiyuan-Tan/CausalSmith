module
public import Causalean.Mathlib.Probability.Independence.Conditional.JoinedBlockProduct
public import Causalean.Mathlib.Probability.Independence.Conditional.ShiftedBlockCrossMoment
public import Causalean.Mathlib.Probability.Independence.Conditional.ShiftedBlockMoments
public import Causalean.Mathlib.Probability.Independence.Conditional.ShiftedJoinedScore
public import Mathlib.Probability.Moments.Covariance

/-!
# Shifted three-block moments and covariance

Held-out scores are shifted by measurable training-block functions. The results
give their conditional first moments, cross moment, and covariance under a finite
product probability law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence

namespace Causalean.Mathlib.Probability.Independence.Conditional

variable {ι : Type*} [Fintype ι]
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  [∀ i, StandardBorelSpace (Ω i)]

/-- [The training block](hyp:B0), [three evaluation blocks](hyp:B), [one held-out
score for each block](hyp:f), and [one training-block shift for each score](hyp:a)
define [the shifted three-block product](goal), [by multiplying the three held-out
scores after subtracting their respective shifts](step:1). -/
noncomputable def shiftedThreeBlockProduct (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (f : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ)
    (a : (t : Fin 3) → ((i : {i // i ∈ B0}) → Ω i.val) → ℝ) :
    (∀ i, Ω i) → ℝ :=
  fun x => ∏ t : Fin 3,
    (f t (finsetCoordProj (B t) x) - a t (finsetCoordProj B0 x))

/-- [A finite product probability law](hyp:μ), [a training block and three evaluation
blocks](hyp:B0,B) with [training/evaluation disjointness](hyp:htrain) and [pairwise
evaluation disjointness](hyp:heval), [held-out scores and training shifts](hyp:f,a)
with [measurability](hyp:hfmeas,hameas) and [integrability](hyp:hf,ha), [an integrable
first shifted pair](hyp:hshift01), and [an integrable shifted three-block product](hyp:hshiftprod)
imply that [its conditional mean is the product of held-out means minus the corresponding
training shifts](goal). -/
theorem condExp_shiftedThreeBlockProduct
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (htrain : ∀ t, Disjoint B0 (B t))
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)))
    (f : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ)
    (a : (t : Fin 3) → ((i : {i // i ∈ B0}) → Ω i.val) → ℝ)
    (hfmeas : ∀ t, Measurable (f t)) (hameas : ∀ t, Measurable (a t))
    (hf : ∀ t, Integrable
      (fun x : ∀ i, Ω i => f t (finsetCoordProj (B t) x)) (Measure.pi μ))
    (ha : ∀ t, Integrable
      (fun x : ∀ i, Ω i => a t (finsetCoordProj B0 x)) (Measure.pi μ))
    (hshift01 : Integrable (fun x : ∀ i, Ω i =>
      (f 0 (finsetCoordProj (B 0) x) - a 0 (finsetCoordProj B0 x)) *
      (f 1 (finsetCoordProj (B 1) x) - a 1 (finsetCoordProj B0 x)))
      (Measure.pi μ))
    (hshiftprod : Integrable (shiftedThreeBlockProduct B0 B f a) (Measure.pi μ)) :
    condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ) (shiftedThreeBlockProduct B0 B f a) =ᵐ[Measure.pi μ]
    (fun x => ∏ t : Fin 3,
      ((∫ y : (∀ i, Ω i), f t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
      a t (finsetCoordProj B0 x))) := by
  classical
  let η : (t : Fin 3) → ((i : {i // i ∈ B0 ∪ B t}) → Ω i.val) → ℝ :=
    fun t => shiftedJoinedScore B0 (B t) (f t) (a t)
  have hηmeas : ∀ t, Measurable (η t) := by
    intro t
    exact measurable_shiftedJoinedScore B0 (B t) (f t) (a t) (hfmeas t) (hameas t)
  have hη : ∀ t, Integrable
      (fun x : ∀ i, Ω i => η t (finsetCoordProj (B0 ∪ B t) x))
      (Measure.pi μ) := by
    intro t
    change Integrable (fun x : ∀ i, Ω i =>
      f t (finsetCoordProj (B t) x) - a t (finsetCoordProj B0 x)) (Measure.pi μ)
    exact (hf t).sub (ha t)
  have hη01 : Integrable (fun x : ∀ i, Ω i =>
      η 0 (finsetCoordProj (B0 ∪ B 0) x) *
      η 1 (finsetCoordProj (B0 ∪ B 1) x)) (Measure.pi μ) := by
    simpa only [η, shiftedJoinedScore_comp_proj] using hshift01
  have hfun : joinedBlockProduct B0 B η = shiftedThreeBlockProduct B0 B f a := by
    funext x
    simp only [joinedBlockProduct, shiftedThreeBlockProduct, η,
      shiftedJoinedScore_comp_proj]
  have hηprod : Integrable (joinedBlockProduct B0 B η) (Measure.pi μ) := by
    simpa only [hfun] using hshiftprod
  have hfactor := condExp_joinedBlockProduct_of_integrable μ B0 B htrain heval
    η hηmeas hη hη01 hηprod
  have hmean : ∀ t, condExp
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ)
      (fun y : ∀ i, Ω i => η t (finsetCoordProj (B0 ∪ B t) y)) =ᵐ[Measure.pi μ]
      (fun x => (∫ y : (∀ i, Ω i), f t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
        a t (finsetCoordProj B0 x)) := by
    intro t
    simpa only [η, shiftedJoinedScore_comp_proj] using
      (condExp_shiftedBlock_eq_integral_sub μ B0 (B t) (htrain t)
        (f t) (a t) (hfmeas t) (hameas t) (hf t) (ha t))
  have hprod : (fun x => ∏ t : Fin 3,
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ)
        (fun y : ∀ i, Ω i => η t (finsetCoordProj (B0 ∪ B t) y)) x) =ᵐ[Measure.pi μ]
      (fun x => ∏ t : Fin 3,
        ((∫ y : (∀ i, Ω i), f t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
          a t (finsetCoordProj B0 x))) := by
    filter_upwards [hmean 0, hmean 1, hmean 2] with x h0 h1 h2
    simp only [Fin.prod_univ_three, h0, h1, h2]
  rw [← hfun]
  exact hfactor.trans hprod

/-- [A finite product probability law](hyp:μ), [a training block and three evaluation
blocks](hyp:B0,B) with [training/evaluation disjointness](hyp:htrain) and [pairwise
evaluation disjointness](hyp:heval), [two held-out-score families](hyp:f,g), [two
training-shift families](hyp:a,b), [measurability](hyp:hfmeas,hgmeas,hameas,hbmeas),
[integrability of all base scores and shifts](hyp:hf,hg,ha,hb), [integrable local cross
products](hyp:hfg), [square-integrable shifted scores](hyp:hflp,hglp), [an integrable
first shifted cross pair](hyp:hcross01), and [square-integrable shifted three-block
products](hyp:hflpProd,hglpProd) imply that [the conditional cross moment factors into
the three shifted blockwise cross moments](goal). -/
theorem condExp_shiftedThreeBlockCross
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (htrain : ∀ t, Disjoint B0 (B t))
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)))
    (f g : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ)
    (a b : (t : Fin 3) → ((i : {i // i ∈ B0}) → Ω i.val) → ℝ)
    (hfmeas : ∀ t, Measurable (f t)) (hgmeas : ∀ t, Measurable (g t))
    (hameas : ∀ t, Measurable (a t)) (hbmeas : ∀ t, Measurable (b t))
    (hf : ∀ t, Integrable
      (fun x : ∀ i, Ω i => f t (finsetCoordProj (B t) x)) (Measure.pi μ))
    (hg : ∀ t, Integrable
      (fun x : ∀ i, Ω i => g t (finsetCoordProj (B t) x)) (Measure.pi μ))
    (ha : ∀ t, Integrable
      (fun x : ∀ i, Ω i => a t (finsetCoordProj B0 x)) (Measure.pi μ))
    (hb : ∀ t, Integrable
      (fun x : ∀ i, Ω i => b t (finsetCoordProj B0 x)) (Measure.pi μ))
    (hfg : ∀ t, Integrable (fun x : ∀ i, Ω i =>
      f t (finsetCoordProj (B t) x) * g t (finsetCoordProj (B t) x))
      (Measure.pi μ))
    (hflp : ∀ t, MemLp
      (fun x : ∀ i, Ω i => f t (finsetCoordProj (B t) x) - a t (finsetCoordProj B0 x))
      2 (Measure.pi μ))
    (hglp : ∀ t, MemLp
      (fun x : ∀ i, Ω i => g t (finsetCoordProj (B t) x) - b t (finsetCoordProj B0 x))
      2 (Measure.pi μ))
    (hcross01 : Integrable (fun x : ∀ i, Ω i =>
      ((f 0 (finsetCoordProj (B 0) x) - a 0 (finsetCoordProj B0 x)) *
       (g 0 (finsetCoordProj (B 0) x) - b 0 (finsetCoordProj B0 x))) *
      ((f 1 (finsetCoordProj (B 1) x) - a 1 (finsetCoordProj B0 x)) *
       (g 1 (finsetCoordProj (B 1) x) - b 1 (finsetCoordProj B0 x))))
      (Measure.pi μ))
    (hflpProd : MemLp (shiftedThreeBlockProduct B0 B f a) 2 (Measure.pi μ))
    (hglpProd : MemLp (shiftedThreeBlockProduct B0 B g b) 2 (Measure.pi μ)) :
    condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ)
      (fun x => shiftedThreeBlockProduct B0 B f a x *
        shiftedThreeBlockProduct B0 B g b x) =ᵐ[Measure.pi μ]
    (fun x => ∏ t : Fin 3,
      (covariance
        (fun y : ∀ i, Ω i => f t (finsetCoordProj (B t) y))
        (fun y : ∀ i, Ω i => g t (finsetCoordProj (B t) y))
        (Measure.pi μ) +
       ((∫ y : (∀ i, Ω i), f t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
         a t (finsetCoordProj B0 x)) *
       ((∫ y : (∀ i, Ω i), g t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
         b t (finsetCoordProj B0 x)))) := by
  classical
  let η : (t : Fin 3) → ((i : {i // i ∈ B0 ∪ B t}) → Ω i.val) → ℝ :=
    fun t y => shiftedJoinedScore B0 (B t) (f t) (a t) y *
      shiftedJoinedScore B0 (B t) (g t) (b t) y
  have hηmeas : ∀ t, Measurable (η t) := by
    intro t
    exact (measurable_shiftedJoinedScore B0 (B t) (f t) (a t)
      (hfmeas t) (hameas t)).mul
      (measurable_shiftedJoinedScore B0 (B t) (g t) (b t)
        (hgmeas t) (hbmeas t))
  have hη : ∀ t, Integrable
      (fun x : ∀ i, Ω i => η t (finsetCoordProj (B0 ∪ B t) x))
      (Measure.pi μ) := by
    intro t
    change Integrable (fun x : ∀ i, Ω i =>
      (f t (finsetCoordProj (B t) x) - a t (finsetCoordProj B0 x)) *
      (g t (finsetCoordProj (B t) x) - b t (finsetCoordProj B0 x)))
      (Measure.pi μ)
    exact (hflp t).integrable_mul (hglp t)
  have hη01 : Integrable (fun x : ∀ i, Ω i =>
      η 0 (finsetCoordProj (B0 ∪ B 0) x) *
      η 1 (finsetCoordProj (B0 ∪ B 1) x)) (Measure.pi μ) := by
    simpa only [η, shiftedJoinedScore_comp_proj] using hcross01
  have hfun : joinedBlockProduct B0 B η =
      (fun x => shiftedThreeBlockProduct B0 B f a x *
        shiftedThreeBlockProduct B0 B g b x) := by
    funext x
    simp only [joinedBlockProduct, shiftedThreeBlockProduct, η,
      shiftedJoinedScore_comp_proj, Fin.prod_univ_three]
    ring
  have hηprod : Integrable (joinedBlockProduct B0 B η) (Measure.pi μ) := by
    rw [hfun]
    exact hflpProd.integrable_mul hglpProd
  have hfactor := condExp_joinedBlockProduct_of_integrable μ B0 B htrain heval
    η hηmeas hη hη01 hηprod
  have hmean : ∀ t, condExp
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ)
      (fun y : ∀ i, Ω i => η t (finsetCoordProj (B0 ∪ B t) y)) =ᵐ[Measure.pi μ]
      (fun x => covariance
        (fun y : ∀ i, Ω i => f t (finsetCoordProj (B t) y))
        (fun y : ∀ i, Ω i => g t (finsetCoordProj (B t) y))
        (Measure.pi μ) +
        ((∫ y : (∀ i, Ω i), f t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
          a t (finsetCoordProj B0 x)) *
        ((∫ y : (∀ i, Ω i), g t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
          b t (finsetCoordProj B0 x))) := by
    intro t
    simpa only [η, shiftedJoinedScore_comp_proj] using
      (condExp_shiftedBlockCross_eq_covariance_add μ B0 (B t) (htrain t)
        (f t) (g t) (a t) (b t) (hfmeas t) (hgmeas t)
        (hameas t) (hbmeas t) (hf t) (hg t) (ha t) (hb t)
        (hfg t) (hflp t) (hglp t))
  have hprod : (fun x => ∏ t : Fin 3,
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ)
        (fun y : ∀ i, Ω i => η t (finsetCoordProj (B0 ∪ B t) y)) x) =ᵐ[Measure.pi μ]
      (fun x => ∏ t : Fin 3,
        (covariance
          (fun y : ∀ i, Ω i => f t (finsetCoordProj (B t) y))
          (fun y : ∀ i, Ω i => g t (finsetCoordProj (B t) y))
          (Measure.pi μ) +
          ((∫ y : (∀ i, Ω i), f t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
            a t (finsetCoordProj B0 x)) *
          ((∫ y : (∀ i, Ω i), g t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
            b t (finsetCoordProj B0 x)))) := by
    filter_upwards [hmean 0, hmean 1, hmean 2] with x h0 h1 h2
    simp only [Fin.prod_univ_three, h0, h1, h2]
  rw [← hfun]
  exact hfactor.trans hprod

/-- [A finite product probability law](hyp:μ), [a training block and three evaluation
blocks](hyp:B0,B) with [training/evaluation disjointness](hyp:htrain) and [pairwise
evaluation disjointness](hyp:heval), [two held-out-score families](hyp:f,g), [two
training-shift families](hyp:a,b), [measurability](hyp:hfmeas,hgmeas,hameas,hbmeas),
[integrability of base scores and shifts](hyp:hf,hg,ha,hb), [integrable local cross
products](hyp:hfg), [square-integrable shifted scores](hyp:hflp,hglp), [integrable
first shifted pairs](hyp:hf01,hg01), [an integrable first shifted cross pair](hyp:hcross01),
and [square-integrable shifted three-block products](hyp:hflpProd,hglpProd) imply that
[their conditional covariance equals the product of shifted blockwise cross moments minus
the product of shifted conditional means](goal). -/
theorem condCov_shiftedThreeBlockProduct
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (htrain : ∀ t, Disjoint B0 (B t))
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)))
    (f g : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ)
    (a b : (t : Fin 3) → ((i : {i // i ∈ B0}) → Ω i.val) → ℝ)
    (hfmeas : ∀ t, Measurable (f t)) (hgmeas : ∀ t, Measurable (g t))
    (hameas : ∀ t, Measurable (a t)) (hbmeas : ∀ t, Measurable (b t))
    (hf : ∀ t, Integrable
      (fun x : ∀ i, Ω i => f t (finsetCoordProj (B t) x)) (Measure.pi μ))
    (hg : ∀ t, Integrable
      (fun x : ∀ i, Ω i => g t (finsetCoordProj (B t) x)) (Measure.pi μ))
    (ha : ∀ t, Integrable
      (fun x : ∀ i, Ω i => a t (finsetCoordProj B0 x)) (Measure.pi μ))
    (hb : ∀ t, Integrable
      (fun x : ∀ i, Ω i => b t (finsetCoordProj B0 x)) (Measure.pi μ))
    (hfg : ∀ t, Integrable (fun x : ∀ i, Ω i =>
      f t (finsetCoordProj (B t) x) * g t (finsetCoordProj (B t) x))
      (Measure.pi μ))
    (hflp : ∀ t, MemLp
      (fun x : ∀ i, Ω i => f t (finsetCoordProj (B t) x) - a t (finsetCoordProj B0 x))
      2 (Measure.pi μ))
    (hglp : ∀ t, MemLp
      (fun x : ∀ i, Ω i => g t (finsetCoordProj (B t) x) - b t (finsetCoordProj B0 x))
      2 (Measure.pi μ))
    (hf01 : Integrable (fun x : ∀ i, Ω i =>
      (f 0 (finsetCoordProj (B 0) x) - a 0 (finsetCoordProj B0 x)) *
      (f 1 (finsetCoordProj (B 1) x) - a 1 (finsetCoordProj B0 x)))
      (Measure.pi μ))
    (hg01 : Integrable (fun x : ∀ i, Ω i =>
      (g 0 (finsetCoordProj (B 0) x) - b 0 (finsetCoordProj B0 x)) *
      (g 1 (finsetCoordProj (B 1) x) - b 1 (finsetCoordProj B0 x)))
      (Measure.pi μ))
    (hcross01 : Integrable (fun x : ∀ i, Ω i =>
      ((f 0 (finsetCoordProj (B 0) x) - a 0 (finsetCoordProj B0 x)) *
       (g 0 (finsetCoordProj (B 0) x) - b 0 (finsetCoordProj B0 x))) *
      ((f 1 (finsetCoordProj (B 1) x) - a 1 (finsetCoordProj B0 x)) *
       (g 1 (finsetCoordProj (B 1) x) - b 1 (finsetCoordProj B0 x))))
      (Measure.pi μ))
    (hflpProd : MemLp (shiftedThreeBlockProduct B0 B f a) 2 (Measure.pi μ))
    (hglpProd : MemLp (shiftedThreeBlockProduct B0 B g b) 2 (Measure.pi μ)) :
    (fun x =>
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ)
        (fun y => shiftedThreeBlockProduct B0 B f a y *
          shiftedThreeBlockProduct B0 B g b y) x -
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ) (shiftedThreeBlockProduct B0 B f a) x *
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ) (shiftedThreeBlockProduct B0 B g b) x) =ᵐ[Measure.pi μ]
    (fun x =>
      (∏ t : Fin 3,
        (covariance
          (fun y : ∀ i, Ω i => f t (finsetCoordProj (B t) y))
          (fun y : ∀ i, Ω i => g t (finsetCoordProj (B t) y))
          (Measure.pi μ) +
         ((∫ y : (∀ i, Ω i), f t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
           a t (finsetCoordProj B0 x)) *
         ((∫ y : (∀ i, Ω i), g t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
           b t (finsetCoordProj B0 x)))) -
      (∏ t : Fin 3,
        ((∫ y : (∀ i, Ω i), f t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
          a t (finsetCoordProj B0 x))) *
      (∏ t : Fin 3,
        ((∫ y : (∀ i, Ω i), g t (finsetCoordProj (B t) y) ∂Measure.pi μ) -
          b t (finsetCoordProj B0 x)))) := by
  have hcross := condExp_shiftedThreeBlockCross μ B0 B htrain heval f g a b
    hfmeas hgmeas hameas hbmeas hf hg ha hb hfg hflp hglp hcross01
    hflpProd hglpProd
  have hleft := condExp_shiftedThreeBlockProduct μ B0 B htrain heval f a
    hfmeas hameas hf ha hf01 (hflpProd.integrable (by norm_num))
  have hright := condExp_shiftedThreeBlockProduct μ B0 B htrain heval g b
    hgmeas hbmeas hg hb hg01 (hglpProd.integrable (by norm_num))
  filter_upwards [hcross, hleft, hright] with x hx hy hz
  simp only [hx, hy, hz]

end Causalean.Mathlib.Probability.Independence.Conditional
