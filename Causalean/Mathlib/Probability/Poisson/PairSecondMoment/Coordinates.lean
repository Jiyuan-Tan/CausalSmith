module
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Algebra
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Basic

/-!
# Coordinate integrals for two independent iid arrays

The four coincidence patterns in a bilinear square have different coordinate
laws. These lemmas keep the left and right observations independent, and use
two fresh coordinates within a stream whenever its indices differ.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Mathlib.Probability.Poisson.PairSecondMoment

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private lemma measurePreserving_fixedCount_pair
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (m n : ℕ) (i : Fin m) (j : Fin n) :
    MeasurePreserving
      (fun p : (Fin m → X) × (Fin n → Y) => (p.1 i, p.2 j))
      ((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q))
      (P.prod Q) := by
  convert (measurePreserving_eval (fun _ : Fin m => P) i).prod
      (measurePreserving_eval (fun _ : Fin n => Q) j) using 1
  rfl

private lemma measurePreserving_fixedCount_two
    {Z : Type*} [MeasurableSpace Z]
    (R : Measure Z) [IsProbabilityMeasure R]
    (t : ℕ) (a b : Fin t) (hab : a ≠ b) :
    MeasurePreserving (fun s : Fin t → Z => (s a, s b))
      (Measure.pi fun _ : Fin t => R) (R.prod R) := by
  let μ := Measure.pi fun _ : Fin t => R
  have hcoord : iIndepFun (fun c : Fin t => fun s : Fin t → Z => s c) μ := by
    simpa [μ] using (iIndepFun_pi (μ := fun _ : Fin t => R)
      (X := fun _ : Fin t => id) (fun _ => aemeasurable_id))
  have hmap : μ.map (fun s : Fin t → Z => (s a, s b)) = R.prod R := by
    have hind := hcoord.indepFun hab
    simpa only [μ, (measurePreserving_eval (fun _ : Fin t => R) a).map_eq,
      (measurePreserving_eval (fun _ : Fin t => R) b).map_eq] using
      (hind.map_prod_eq_prod_map_map (measurable_pi_apply a).aemeasurable
        (measurable_pi_apply b).aemeasurable)
  exact ⟨(measurable_pi_apply a).prodMk (measurable_pi_apply b), hmap⟩

/-- Given [two probability laws](hyp:P,Q), [a real kernel](hyp:K), [two fixed
array lengths](hyp:m,n), [a measurable kernel](hyp:hK), [an integrable kernel
square](hyp:hK2), and [two selected positions in each array](hyp:i,k,j,l),
[the product of the two kernel evaluations is integrable](goal). -/
theorem integrable_fixedCount_kernelProduct
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (K : X → Y → ℝ) (m n : ℕ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q))
    (i k : Fin m) (j l : Fin n) :
    Integrable
      (fun p : (Fin m → X) × (Fin n → Y) =>
        K (p.1 i) (p.2 j) * K (p.1 k) (p.2 l))
      ((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q)) := by
  let μ := (Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q)
  let f := fun p : (Fin m → X) × (Fin n → Y) => K (p.1 i) (p.2 j)
  let g := fun p : (Fin m → X) × (Fin n → Y) => K (p.1 k) (p.2 l)
  have hfmeas : Measurable f := by
    change Measurable ((Function.uncurry K) ∘
      fun p : (Fin m → X) × (Fin n → Y) => (p.1 i, p.2 j))
    exact hK.comp (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd))
  have hgmeas : Measurable g := by
    change Measurable ((Function.uncurry K) ∘
      fun p : (Fin m → X) × (Fin n → Y) => (p.1 k, p.2 l))
    exact hK.comp (((measurable_pi_apply k).comp measurable_fst).prodMk
      ((measurable_pi_apply l).comp measurable_snd))
  have hfsq : Integrable (fun p => f p ^ 2) μ := by
    simpa only [f, Function.comp_def] using
      (measurePreserving_fixedCount_pair P Q m n i j).integrable_comp_of_integrable hK2
  have hgsq : Integrable (fun p => g p ^ 2) μ := by
    simpa only [g, Function.comp_def] using
      (measurePreserving_fixedCount_pair P Q m n k l).integrable_comp_of_integrable hK2
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfmeas.aestronglyMeasurable).2 hfsq
  have hg : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgmeas.aestronglyMeasurable).2 hgsq
  change Integrable (f * g) μ
  exact hf.integrable_mul hg

/-- Given [two probability laws](hyp:P,Q), [a measurable real kernel](hyp:K,hK),
[an integrable kernel square](hyp:hK2), [two fixed array lengths](hyp:m,n), and
[one selected position in each array](hyp:i,j), [coincident evaluations
integrate as one independent point-pair kernel square](goal). -/
theorem integral_fixedCount_both_equal
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (K : X → Y → ℝ) (m n : ℕ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q))
    (i : Fin m) (j : Fin n) :
    (∫ p : (Fin m → X) × (Fin n → Y),
      K (p.1 i) (p.2 j) * K (p.1 i) (p.2 j)
      ∂((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q))) =
      ∫ x, ∫ y, K x y * K x y ∂Q ∂P := by
  let φ : ((Fin m → X) × (Fin n → Y)) → X × Y := fun p => (p.1 i, p.2 j)
  have hφ := measurePreserving_fixedCount_pair P Q m n i j
  have hprod : Integrable (fun z : X × Y => K z.1 z.2 * K z.1 z.2) (P.prod Q) := by
    simpa only [← pow_two] using hK2
  calc
    _ = ∫ z : X × Y, K z.1 z.2 * K z.1 z.2 ∂(P.prod Q) := by
      have e := integral_map
        (μ := (Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q))
        (φ := φ) hφ.measurable.aemeasurable
        (f := fun z : X × Y => K z.1 z.2 * K z.1 z.2)
        (hK.mul hK).aestronglyMeasurable
      rw [hφ.map_eq] at e
      exact e.symm
    _ = _ := integral_prod _ hprod

/-- Given [two probability laws](hyp:P,Q), [a measurable real kernel](hyp:K,hK),
[an integrable kernel square](hyp:hK2), [two fixed array lengths](hyp:m,n),
[one left position and distinct right positions](hyp:i,j,l,hjl), [the product
integrates with a shared left coordinate and independent right coordinates](goal). -/
theorem integral_fixedCount_shared_left
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (K : X → Y → ℝ) (m n : ℕ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q))
    (i : Fin m) (j l : Fin n) (hjl : j ≠ l) :
    (∫ p : (Fin m → X) × (Fin n → Y),
      K (p.1 i) (p.2 j) * K (p.1 i) (p.2 l)
      ∂((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q))) =
      ∫ x, ∫ y, ∫ y', K x y * K x y' ∂Q ∂Q ∂P := by
  let μ := (Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q)
  let φ : ((Fin m → X) × (Fin n → Y)) → X × (Y × Y) :=
    fun p => (p.1 i, (p.2 j, p.2 l))
  let F : X × (Y × Y) → ℝ := fun z => K z.1 z.2.1 * K z.1 z.2.2
  have hφ : MeasurePreserving φ μ (P.prod (Q.prod Q)) := by
    convert (measurePreserving_eval (fun _ : Fin m => P) i).prod
      (measurePreserving_fixedCount_two Q n j l hjl) using 1
    rfl
  have hFmeas : Measurable F := by
    have h₁ : Measurable (fun z : X × (Y × Y) => (z.1, z.2.1)) := by fun_prop
    have h₂ : Measurable (fun z : X × (Y × Y) => (z.1, z.2.2)) := by fun_prop
    exact (hK.comp h₁).mul (hK.comp h₂)
  have hI := integrable_fixedCount_kernelProduct P Q K m n hK hK2 i i j l
  have hF : Integrable F (P.prod (Q.prod Q)) := by
    apply (hφ.integrable_comp hFmeas.aestronglyMeasurable).mp
    exact hI
  have houter : (∫ p, F (φ p) ∂μ) = ∫ z, F z ∂(P.prod (Q.prod Q)) := by
    have e := integral_map (μ := μ) (φ := φ) hφ.measurable.aemeasurable
      (f := F) hFmeas.aestronglyMeasurable
    rw [hφ.map_eq] at e
    exact e.symm
  change (∫ p, F (φ p) ∂μ) = _
  rw [houter, integral_prod _ hF]
  apply integral_congr_ae
  filter_upwards [hF.prod_right_ae] with x hx
  exact integral_prod _ hx

/-- Given [two probability laws](hyp:P,Q), [a measurable real kernel](hyp:K,hK),
[an integrable kernel square](hyp:hK2), [two fixed array lengths](hyp:m,n),
[distinct left positions and one right position](hyp:i,k,j,hik), [the product
integrates with independent left coordinates and a shared right coordinate](goal). -/
theorem integral_fixedCount_shared_right
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (K : X → Y → ℝ) (m n : ℕ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q))
    (i k : Fin m) (j : Fin n) (hik : i ≠ k) :
    (∫ p : (Fin m → X) × (Fin n → Y),
      K (p.1 i) (p.2 j) * K (p.1 k) (p.2 j)
      ∂((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q))) =
      ∫ x, ∫ x', ∫ y, K x y * K x' y ∂Q ∂P ∂P := by
  let μ := (Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q)
  let φ : ((Fin m → X) × (Fin n → Y)) → (X × X) × Y :=
    fun p => ((p.1 i, p.1 k), p.2 j)
  let F : (X × X) × Y → ℝ := fun z => K z.1.1 z.2 * K z.1.2 z.2
  have hφ : MeasurePreserving φ μ ((P.prod P).prod Q) := by
    convert (measurePreserving_fixedCount_two P m i k hik).prod
      (measurePreserving_eval (fun _ : Fin n => Q) j) using 1
    rfl
  have hFmeas : Measurable F := by
    have h₁ : Measurable (fun z : (X × X) × Y => (z.1.1, z.2)) := by fun_prop
    have h₂ : Measurable (fun z : (X × X) × Y => (z.1.2, z.2)) := by fun_prop
    exact (hK.comp h₁).mul (hK.comp h₂)
  have hI := integrable_fixedCount_kernelProduct P Q K m n hK hK2 i k j j
  have hF : Integrable F ((P.prod P).prod Q) := by
    apply (hφ.integrable_comp hFmeas.aestronglyMeasurable).mp
    exact hI
  have houter : (∫ p, F (φ p) ∂μ) = ∫ z, F z ∂((P.prod P).prod Q) := by
    have e := integral_map (μ := μ) (φ := φ) hφ.measurable.aemeasurable
      (f := F) hFmeas.aestronglyMeasurable
    rw [hφ.map_eq] at e
    exact e.symm
  change (∫ p, F (φ p) ∂μ) = _
  rw [houter, integral_prod _ hF]
  exact integral_prod _ hF.integral_prod_left

/-- Given [two probability laws](hyp:P,Q), [a measurable real kernel](hyp:K,hK),
[an integrable kernel square](hyp:hK2), [two fixed array lengths](hyp:m,n), and
[distinct selected positions in each array](hyp:i,k,j,l,hik,hjl), [the product
of the two kernel evaluations has the four-independent-coordinate integral](goal). -/
theorem integral_fixedCount_both_distinct
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (K : X → Y → ℝ) (m n : ℕ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q))
    (i k : Fin m) (j l : Fin n) (hik : i ≠ k) (hjl : j ≠ l) :
    (∫ p : (Fin m → X) × (Fin n → Y),
      K (p.1 i) (p.2 j) * K (p.1 k) (p.2 l)
      ∂((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q))) =
      ∫ x, ∫ x', ∫ y, ∫ y', K x y * K x' y' ∂Q ∂Q ∂P ∂P := by
  let μ := (Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q)
  let φ : ((Fin m → X) × (Fin n → Y)) → (X × X) × (Y × Y) :=
    fun p => ((p.1 i, p.1 k), (p.2 j, p.2 l))
  let F : (X × X) × (Y × Y) → ℝ :=
    fun z => K z.1.1 z.2.1 * K z.1.2 z.2.2
  have hφ : MeasurePreserving φ μ ((P.prod P).prod (Q.prod Q)) := by
    convert (measurePreserving_fixedCount_two P m i k hik).prod
      (measurePreserving_fixedCount_two Q n j l hjl) using 1
    rfl
  have hFmeas : Measurable F := by
    have h₁ : Measurable (fun z : (X × X) × (Y × Y) => (z.1.1, z.2.1)) := by
      fun_prop
    have h₂ : Measurable (fun z : (X × X) × (Y × Y) => (z.1.2, z.2.2)) := by
      fun_prop
    exact (hK.comp h₁).mul (hK.comp h₂)
  have hI := integrable_fixedCount_kernelProduct P Q K m n hK hK2 i k j l
  have hF : Integrable F ((P.prod P).prod (Q.prod Q)) := by
    apply (hφ.integrable_comp hFmeas.aestronglyMeasurable).mp
    exact hI
  have houter : (∫ p, F (φ p) ∂μ) =
      ∫ z, F z ∂((P.prod P).prod (Q.prod Q)) := by
    have e := integral_map (μ := μ) (φ := φ) hφ.measurable.aemeasurable
      (f := F) hFmeas.aestronglyMeasurable
    rw [hφ.map_eq] at e
    exact e.symm
  have hinner : ∀ᵐ p : X × X ∂(P.prod P),
      (∫ q : Y × Y, F (p, q) ∂(Q.prod Q)) =
        ∫ y, ∫ y', K p.1 y * K p.2 y' ∂Q ∂Q := by
    filter_upwards [hF.prod_right_ae] with p hp
    exact integral_prod _ hp
  have hG : Integrable
      (fun p : X × X => ∫ y, ∫ y', K p.1 y * K p.2 y' ∂Q ∂Q)
      (P.prod P) := hF.integral_prod_left.congr hinner
  change (∫ p, F (φ p) ∂μ) = _
  calc
    (∫ p, F (φ p) ∂μ) =
        ∫ p : X × X, ∫ q : Y × Y, F (p, q) ∂(Q.prod Q) ∂(P.prod P) := by
      rw [houter, integral_prod _ hF]
    _ = ∫ p : X × X, ∫ y, ∫ y', K p.1 y * K p.2 y' ∂Q ∂Q ∂(P.prod P) :=
      integral_congr_ae hinner
    _ = _ := integral_prod _ hG

end Causalean.Mathlib.Probability.Poisson.PairSecondMoment
