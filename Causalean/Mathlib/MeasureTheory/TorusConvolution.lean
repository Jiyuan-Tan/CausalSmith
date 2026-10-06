module
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic

/-!
# Fourier uniqueness and marked convolution on the torus

Finite measures on a torus are determined by their integer Fourier coefficients, and a
channel with no vanishing coefficient is injective under convolution.  The same result
holds when convolution changes only a torus coordinate of a marked measure.  The module
also supplies product-law factorizations after conditioning an independent channel on a
record-based event.
-/

@[expose] public section

namespace Causalean.Mathlib.MeasureTheory

open _root_.MeasureTheory AddCircle BoundedContinuousFunction

variable {T : ℝ}
variable {Ω L β : Type*} [MeasurableSpace Ω] [MeasurableSpace L] [MeasurableSpace β]

/-- [Two finite torus measures](hyp:μ,ν) whose [integer-character integrals agree](hyp:h)
are [the same measure](goal). -/
theorem torus_measure_ext_of_fourier_eq [Fact (0 < T)]
    (μ ν : Measure (AddCircle T)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℤ, (∫ x, fourier n x ∂μ) = ∫ x, fourier n x ∂ν) : μ = ν := by
  let A : StarSubalgebra ℂ (AddCircle T →ᵇ ℂ) :=
    (fourierSubalgebra (T := T)).comap (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)
  have hA : A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ) =
      fourierSubalgebra (T := T) := by
    apply le_antisymm
    · rintro f ⟨g, hg, rfl⟩
      exact hg
    · intro f hf
      exact ⟨BoundedContinuousFunction.mkOfCompact f, hf, rfl⟩
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish
    (A := A) (by simpa [hA] using (fourierSubalgebra_separatesPoints (T := T)))
  intro g hg
  have hg' : (g.toContinuousMap : C(AddCircle T, ℂ)) ∈
      Submodule.span ℂ (Set.range (fourier (T := T))) := by
    rw [← fourierSubalgebra_coe]
    exact hg
  have hspan : ∀ f : C(AddCircle T, ℂ),
      f ∈ Submodule.span ℂ (Set.range (fourier (T := T))) →
      (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨n, rfl⟩ := hf
        exact h n
    | zero => simp
    | add f g hf hg ihf ihg =>
        have hfμ : Integrable (fun x => f x) μ :=
          (BoundedContinuousFunction.mkOfCompact f).integrable μ
        have hgμ : Integrable (fun x => g x) μ :=
          (BoundedContinuousFunction.mkOfCompact g).integrable μ
        have hfν : Integrable (fun x => f x) ν :=
          (BoundedContinuousFunction.mkOfCompact f).integrable ν
        have hgν : Integrable (fun x => g x) ν :=
          (BoundedContinuousFunction.mkOfCompact g).integrable ν
        simp only [ContinuousMap.add_apply, integral_add hfμ hgμ,
          integral_add hfν hgν, ihf, ihg]
    | smul c f hf ih =>
        simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul, ih]
  exact hspan g.toContinuousMap hg'

/-- The [integer index](hyp:n) Fourier coefficient of the convolution of [two finite torus
measures](hyp:μ,ν) [is the product of their coefficients](goal). -/
theorem torus_integral_fourier_conv [Fact (0 < T)]
    (μ ν : Measure (AddCircle T)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℤ) :
    (∫ x, fourier n x ∂(μ ∗ ν)) =
      (∫ x, fourier n x ∂μ) * (∫ x, fourier n x ∂ν) := by
  have hf : Integrable (fun x : AddCircle T => fourier n x) (μ ∗ ν) := by
    exact (BoundedContinuousFunction.mkOfCompact (fourier n)).integrable _
  rw [integral_conv hf]
  simp_rw [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]
  simp only [integral_const_mul, integral_mul_const]

/-- A [finite torus channel](hyp:κ) with [no zero integer Fourier coefficient](hyp:hκ)
maps [two finite torus measures](hyp:μ,ν) with [equal convolution outputs](hyp:hconv) to
[the same input measure](goal). -/
theorem torus_conv_injective_right [Fact (0 < T)]
    (κ μ ν : Measure (AddCircle T)) [IsFiniteMeasure κ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hκ : ∀ n : ℤ, (∫ x, fourier n x ∂κ) ≠ 0)
    (hconv : μ ∗ κ = ν ∗ κ) : μ = ν := by
  apply torus_measure_ext_of_fourier_eq μ ν
  intro n
  have heq := congrArg (fun ρ : Measure (AddCircle T) => ∫ x, fourier n x ∂ρ) hconv
  rw [torus_integral_fourier_conv, torus_integral_fourier_conv] at heq
  exact mul_right_cancel₀ (hκ n) heq

/-- The [marked convolution](goal) of a [marked torus measure](hyp:ρ) and a [torus
channel](hyp:κ) is [the pushforward that adds the channel only to the torus coordinate](step:1). -/
noncomputable def markedConv (ρ : Measure (AddCircle T × β))
    (κ : Measure (AddCircle T)) : Measure (AddCircle T × β) :=
  Measure.map (fun p : (AddCircle T × β) × AddCircle T => (p.1.1 + p.2, p.1.2))
    (ρ.prod κ)

/-- Restricting [a marked torus measure](hyp:ρ) convolved with [a torus channel](hyp:κ)
to [a measurable mark set](hyp:B,hB) [commutes with marked convolution](goal). -/
theorem markedConv_restrict_mark
    (ρ : Measure (AddCircle T × β)) (κ : Measure (AddCircle T))
    [SFinite ρ] [SFinite κ]
    (B : Set β) (hB : MeasurableSet B) :
    (markedConv ρ κ).restrict (Prod.snd ⁻¹' B) =
      markedConv (ρ.restrict (Prod.snd ⁻¹' B)) κ := by
  have hmarked : Measurable
      (fun p : (AddCircle T × β) × AddCircle T => (p.1.1 + p.2, p.1.2)) := by
    fun_prop
  have hmark : MeasurableSet (Prod.snd ⁻¹' B : Set (AddCircle T × β)) :=
    measurable_snd hB
  have hpre :
      (fun p : (AddCircle T × β) × AddCircle T => (p.1.1 + p.2, p.1.2)) ⁻¹'
          (Prod.snd ⁻¹' B) = (Prod.snd ⁻¹' B) ×ˢ Set.univ := by
    ext p
    simp
  rw [markedConv, Measure.restrict_map hmarked hmark, hpre,
    ← Measure.restrict_prod_eq_prod_univ]
  rfl

/-- The torus marginal of [a marked torus measure](hyp:ρ) after convolution with [a torus
channel](hyp:κ) [is the convolution of its original marginal and that channel](goal). -/
theorem markedConv_map_fst
    (ρ : Measure (AddCircle T × β)) (κ : Measure (AddCircle T))
    [SFinite ρ] [SFinite κ] :
    Measure.map Prod.fst (markedConv ρ κ) =
      (Measure.map Prod.fst ρ) ∗ κ := by
  have hmarked : Measurable
      (fun p : (AddCircle T × β) × AddCircle T => (p.1.1 + p.2, p.1.2)) := by
    fun_prop
  have hsum : Measurable (fun p : AddCircle T × AddCircle T => p.1 + p.2) := by
    fun_prop
  have hpair : Measurable
      (Prod.map Prod.fst id : (AddCircle T × β) × AddCircle T →
        AddCircle T × AddCircle T) := measurable_fst.prodMap measurable_id
  have hprod : (Measure.map Prod.fst ρ).prod κ =
      Measure.map (Prod.map Prod.fst id) (ρ.prod κ) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map ρ κ measurable_fst measurable_id)
  calc
    Measure.map Prod.fst (markedConv ρ κ) =
        Measure.map (fun p : (AddCircle T × β) × AddCircle T => p.1.1 + p.2)
          (ρ.prod κ) := by
      rw [markedConv, Measure.map_map measurable_fst hmarked]
      rfl
    _ = Measure.map (fun p : AddCircle T × AddCircle T => p.1 + p.2)
          ((Measure.map Prod.fst ρ).prod κ) := by
      rw [hprod, Measure.map_map hsum hpair]
      rfl
    _ = (Measure.map Prod.fst ρ) ∗ κ := rfl

/-- A [finite torus channel](hyp:κ) with [no zero integer Fourier coefficient](hyp:hκ)
maps [two finite marked torus measures](hyp:ρ,σ) with [equal marked convolutions](hyp:hconv)
to [the same marked measure](goal). -/
theorem markedConv_injective_right [Fact (0 < T)]
    (κ : Measure (AddCircle T)) (ρ σ : Measure (AddCircle T × β))
    [IsFiniteMeasure κ] [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hκ : ∀ n : ℤ, (∫ x, fourier n x ∂κ) ≠ 0)
    (hconv : markedConv ρ κ = markedConv σ κ) : ρ = σ := by
  apply Measure.ext_prod
  intro A B hA hB
  have hmark : MeasurableSet (Prod.snd ⁻¹' B : Set (AddCircle T × β)) :=
    measurable_snd hB
  have hrestricted :
      (markedConv (ρ.restrict (Prod.snd ⁻¹' B)) κ) =
        markedConv (σ.restrict (Prod.snd ⁻¹' B)) κ := by
    rw [← markedConv_restrict_mark ρ κ B hB,
      ← markedConv_restrict_mark σ κ B hB, hconv]
  have hmarg :
      Measure.map Prod.fst (ρ.restrict (Prod.snd ⁻¹' B)) =
        Measure.map Prod.fst (σ.restrict (Prod.snd ⁻¹' B)) := by
    apply torus_conv_injective_right κ _ _ hκ
    rw [← markedConv_map_fst, ← markedConv_map_fst, hrestricted]
  have hAρ := congrArg (fun μ : Measure (AddCircle T) => μ A) hmarg
  rw [Measure.map_apply measurable_fst hA,
    Measure.map_apply measurable_fst hA,
    Measure.restrict_apply' hmark,
    Measure.restrict_apply' hmark] at hAρ
  simpa only [Set.preimage, Set.prod_eq] using hAρ

/-- Under [a probability law](hyp:P), a [measurable torus channel](hyp:U,hU) and a
[measurable record](hyp:R,hR) that are [independent](hyp:hind), conditioning on [a measurable
record event](hyp:A,hA) with [positive probability](hyp:hpos) leaves [the channel marginal
unchanged](goal). -/
theorem independent_channel_map_cond
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → AddCircle T) (R : Ω → L)
    (hU : Measurable U) (hR : Measurable R)
    (hind : ProbabilityTheory.IndepFun U R P)
    (A : Set L) (hA : MeasurableSet A) (hpos : P (R ⁻¹' A) ≠ 0) :
    (ProbabilityTheory.cond P (R ⁻¹' A)).map U = P.map U := by
  have hEA : MeasurableSet (R ⁻¹' A) := hR hA
  have htop : P (R ⁻¹' A) ≠ (⊤ : ENNReal) := measure_ne_top P _
  ext S hS
  rw [Measure.map_apply hU hS, ProbabilityTheory.cond_apply hEA,
    Measure.map_apply hU hS]
  rw [Set.inter_comm, hind.measure_inter_preimage_eq_mul S A hS hA]
  rw [mul_comm (P (U ⁻¹' S)) (P (R ⁻¹' A)), ← mul_assoc,
    ENNReal.inv_mul_cancel hpos htop, one_mul]

/-- Under [a probability law](hyp:P), a [measurable torus channel](hyp:U,hU) and a
[measurable record](hyp:R,hR) that are [independent](hyp:hind), conditioning on [a measurable
record event](hyp:A,hA) with [positive probability](hyp:hpos) makes [the joint law the product
of the unchanged channel law and the conditioned record law](goal). -/
theorem independent_channel_record_map_cond
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → AddCircle T) (R : Ω → L)
    (hU : Measurable U) (hR : Measurable R)
    (hind : ProbabilityTheory.IndepFun U R P)
    (A : Set L) (hA : MeasurableSet A) (hpos : P (R ⁻¹' A) ≠ 0) :
    (ProbabilityTheory.cond P (R ⁻¹' A)).map (fun ω => (U ω, R ω)) =
      (P.map U).prod ((ProbabilityTheory.cond P (R ⁻¹' A)).map R) := by
  have _hpos : P (R ⁻¹' A) ≠ 0 := hpos
  let F : Ω → AddCircle T × L := fun ω => (U ω, R ω)
  have hF : Measurable F := hU.prodMk hR
  have hEA : MeasurableSet (R ⁻¹' A) := hR hA
  have hbase : P.map F = (P.map U).prod (P.map R) :=
    hind.map_prod_eq_prod_map_map hU.aemeasurable hR.aemeasurable
  have hpre : F ⁻¹' (Set.univ ×ˢ A) = R ⁻¹' A := by ext ω; simp [F]
  have hrest : (P.restrict (R ⁻¹' A)).map F =
      (P.map U).prod ((P.restrict (R ⁻¹' A)).map R) := by
    calc
      (P.restrict (R ⁻¹' A)).map F = (P.map F).restrict (Set.univ ×ˢ A) := by
        rw [Measure.restrict_map hF (MeasurableSet.univ.prod hA), hpre]
      _ = (P.map U).prod ((P.restrict (R ⁻¹' A)).map R) := by
        rw [hbase, ← Measure.prod_restrict, Measure.restrict_univ,
          Measure.restrict_map hR hA]
  simp only [ProbabilityTheory.cond, Measure.map_smul]
  rw [hrest, Measure.prod_smul_right]

/-- Under [a probability law](hyp:P), a [measurable torus channel](hyp:U,hU) and a
[measurable record](hyp:R,hR) with [a measurable mark map](hyp:M,hM) that are
[independent](hyp:hind), conditioning on [a measurable record event](hyp:A,hA) with
[positive probability](hyp:hpos) and then restricting to [a measurable mark set](hyp:B,hB)
[preserves the channel-product factorization](goal). -/
theorem independent_channel_mark_restrict_cond
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → AddCircle T) (R : Ω → L) (M : L → β)
    (hU : Measurable U) (hR : Measurable R) (hM : Measurable M)
    (hind : ProbabilityTheory.IndepFun U R P)
    (A : Set L) (hA : MeasurableSet A) (hpos : P (R ⁻¹' A) ≠ 0)
    (B : Set β) (hB : MeasurableSet B) :
    ((ProbabilityTheory.cond P (R ⁻¹' A)).map
      (fun ω => (U ω, M (R ω)))).restrict (Prod.snd ⁻¹' B) =
      (P.map U).prod
        (((ProbabilityTheory.cond P (R ⁻¹' A)).map (M ∘ R)).restrict B) := by
  have _hB : MeasurableSet B := hB
  have hpair : Measurable (fun ω : Ω => (U ω, R ω)) := hU.prodMk hR
  have hmap : Measurable (Prod.map id M : AddCircle T × L → AddCircle T × β) :=
    measurable_id.prodMap hM
  have hcomp :
      (fun ω : Ω => (U ω, M (R ω))) =
        (Prod.map id M) ∘ (fun ω : Ω => (U ω, R ω)) := rfl
  rw [hcomp, ← Measure.map_map hmap hpair,
    independent_channel_record_map_cond P U R hU hR hind A hA hpos,
    ← Measure.map_prod_map (P.map U)
      ((ProbabilityTheory.cond P (R ⁻¹' A)).map R) measurable_id hM]
  simp only [Measure.map_id]
  have hBprod : Prod.snd ⁻¹' B = (Set.univ ×ˢ B : Set (AddCircle T × β)) := by
    ext p; simp
  rw [hBprod, ← Measure.prod_restrict, Measure.restrict_univ]
  congr 1
  rw [Measure.map_map hM hR]

end Causalean.Mathlib.MeasureTheory
