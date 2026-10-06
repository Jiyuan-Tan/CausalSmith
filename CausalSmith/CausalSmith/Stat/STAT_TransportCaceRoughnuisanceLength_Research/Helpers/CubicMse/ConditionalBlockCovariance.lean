module
public import Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockProduct

/-! # Conditional moments of centered held-out block scores

These adapters derive centering and cross-moment factorization from disjoint
blocks of a finite product experiment.
-/

public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence
open Causalean.Mathlib.Probability.Independence.Conditional

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
variable {ι : Type*} [Fintype ι]
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  [∀ i, StandardBorelSpace (Ω i)]
variable (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]

-- @node: condExp_blockScore_eq_integral
/-- Given [the supplied inputs](hyp:S,T,hST,f,hf), [the stated result about cond exp block score eq integral holds](goal). -/
lemma condExp_blockScore_eq_integral (S T : Finset ι) (hST : Disjoint S T)
    (f : ((i : {i // i ∈ T}) → Ω i.val) → ℝ) (hf : Measurable f) :
    condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) S) MeasurableSpace.pi)
      (Measure.pi μ) (fun x => f (finsetCoordProj T x)) =ᵐ[Measure.pi μ]
      (fun _ => ∫ x, f (finsetCoordProj T x) ∂Measure.pi μ) := by
  let F := fun x : (∀ i, Ω i) => f (finsetCoordProj T x)
  have hF : StronglyMeasurable[MeasurableSpace.comap F inferInstance] F :=
    (show Measurable[MeasurableSpace.comap F inferInstance] F from comap_measurable F).stronglyMeasurable
  have hi := indepFun_pi_of_disjoint (Ω := Ω) μ hST
  have hft : (Fintype.ofFinite ι) = (inferInstance : Fintype ι) := Subsingleton.elim _ _
  have hpi : @Measure.pi ι Ω (Fintype.ofFinite ι) _ μ = Measure.pi μ :=
    congrArg (fun fi : Fintype ι => @Measure.pi ι Ω fi _ μ) hft
  have hindProj : Indep
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) T) MeasurableSpace.pi)
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) S) MeasurableSpace.pi)
      (Measure.pi μ) := by
    apply (IndepFun_iff_Indep _ _ _).mp
    change (fun x : ∀ i, Ω i => fun i : {i // i ∈ T} => x i.val) ⟂ᵢ[Measure.pi μ]
      (fun x : ∀ i, Ω i => fun i : {i // i ∈ S} => x i.val)
    simpa only [hpi] using hi.symm
  have hind : Indep
      (MeasurableSpace.comap F inferInstance)
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) S) MeasurableSpace.pi)
      (Measure.pi μ) := by
    apply indep_of_indep_of_le_left hindProj
    rw [show F = f ∘ finsetCoordProj T by rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hf.comap_le
  exact condExp_indep_eq
    (hf.comp (measurable_finsetCoordProj T)).comap_le
    (measurable_finsetCoordProj S).comap_le hF hind


-- @node: condExp_centeredBlockScore_zero
/-- Given [the supplied inputs](hyp:S,T,hST,f,hf,hfLp), [the stated result about cond exp centered block score zero holds](goal). -/
lemma condExp_centeredBlockScore_zero (S T : Finset ι) (hST : Disjoint S T)
    (f : ((i : {i // i ∈ T}) → Ω i.val) → ℝ) (hf : Measurable f)
    (hfLp : MemLp (fun x : ∀ i, Ω i => f (finsetCoordProj T x)) 2 (Measure.pi μ)) :
    condExp (MeasurableSpace.comap
        (finsetCoordProj (Ω := Ω) S) MeasurableSpace.pi)
      (Measure.pi μ)
      (fun x => f (finsetCoordProj T x) -
        ∫ y, f (finsetCoordProj T y) ∂Measure.pi μ) =ᵐ[Measure.pi μ]
      (0 : (∀ i, Ω i) → ℝ) := by
  let m := ∫ y, f (finsetCoordProj T y) ∂Measure.pi μ
  have hmain := condExp_blockScore_eq_integral μ S T hST
    (fun z => f z - m) (hf.sub measurable_const)
  have hfint := hfLp.integrable (by norm_num)
  have hconst : Integrable (fun _ : (∀ i, Ω i) => m) (Measure.pi μ) :=
    integrable_const m
  have hint : (∫ x, f (finsetCoordProj T x) - m ∂Measure.pi μ) = 0 := by
    rw [integral_sub hfint hconst, integral_const, probReal_univ, one_smul]
    simp [m]
  rw [hint] at hmain
  filter_upwards [hmain] with x hx
  change _ = (0 : ℝ)
  simpa only [m] using hx

-- @node: condExp_centeredBlockCross_eq_covariance
/-- Given [the supplied inputs](hyp:S,T,hST,f,g,hf,hg), [the stated result about cond exp centered block cross eq covariance holds](goal). -/
lemma condExp_centeredBlockCross_eq_covariance (S T : Finset ι)
    (hST : Disjoint S T)
    (f g : ((i : {i // i ∈ T}) → Ω i.val) → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    condExp (MeasurableSpace.comap
        (finsetCoordProj (Ω := Ω) S) MeasurableSpace.pi)
      (Measure.pi μ)
      (fun x =>
        (f (finsetCoordProj T x) - ∫ y, f (finsetCoordProj T y) ∂Measure.pi μ) *
        (g (finsetCoordProj T x) - ∫ y, g (finsetCoordProj T y) ∂Measure.pi μ))
      =ᵐ[Measure.pi μ]
      (fun _ => cov[(fun x => f (finsetCoordProj T x)),
        (fun x => g (finsetCoordProj T x)); Measure.pi μ]) := by
  have hmain := condExp_blockScore_eq_integral μ S T hST
    (fun z =>
      (f z - ∫ y, f (finsetCoordProj T y) ∂Measure.pi μ) *
      (g z - ∫ y, g (finsetCoordProj T y) ∂Measure.pi μ))
    ((hf.sub measurable_const).mul (hg.sub measurable_const))
  simpa only [covariance] using hmain


-- @node: condCov_centeredThreeBlock_eq_prod_covariance
/-- Given [the supplied inputs](hyp:B0,B,htrain,heval,f,g,hf,hg,hfLp,hgLp), [the stated result about cond cov centered three block eq prod covariance holds](goal). -/
lemma condCov_centeredThreeBlock_eq_prod_covariance
    (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (htrain : ∀ t, Disjoint B0 (B t))
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)))
    (f g : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ)
    (hf : ∀ t, Measurable (f t)) (hg : ∀ t, Measurable (g t))
    (hfLp : ∀ t, MemLp
      (fun x : ∀ i, Ω i => f t (finsetCoordProj (B t) x)) 2 (Measure.pi μ))
    (hgLp : ∀ t, MemLp
      (fun x : ∀ i, Ω i => g t (finsetCoordProj (B t) x)) 2 (Measure.pi μ)) :
    let fc : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ :=
      fun t z => f t z - ∫ x, f t (finsetCoordProj (B t) x) ∂Measure.pi μ
    let gc : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ :=
      fun t z => g t z - ∫ x, g t (finsetCoordProj (B t) x) ∂Measure.pi μ
    (fun x =>
      condExp (MeasurableSpace.comap
          (finsetCoordProj (Ω := Ω) B0) MeasurableSpace.pi)
        (Measure.pi μ)
        (fun y => threeBlockProduct B fc y * threeBlockProduct B gc y) x -
      condExp (MeasurableSpace.comap
          (finsetCoordProj (Ω := Ω) B0) MeasurableSpace.pi)
        (Measure.pi μ) (threeBlockProduct B fc) x *
      condExp (MeasurableSpace.comap
          (finsetCoordProj (Ω := Ω) B0) MeasurableSpace.pi)
        (Measure.pi μ) (threeBlockProduct B gc) x)
      =ᵐ[Measure.pi μ]
    (fun _ => ∏ t : Fin 3,
      cov[(fun x => f t (finsetCoordProj (B t) x)),
        (fun x => g t (finsetCoordProj (B t) x)); Measure.pi μ]) := by
  dsimp only
  let fc : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ :=
    fun t z => f t z - ∫ x, f t (finsetCoordProj (B t) x) ∂Measure.pi μ
  let gc : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ :=
    fun t z => g t z - ∫ x, g t (finsetCoordProj (B t) x) ∂Measure.pi μ
  have hfcmeas (t : Fin 3) : Measurable (fc t) := (hf t).sub measurable_const
  have hgcmeas (t : Fin 3) : Measurable (gc t) := (hg t).sub measurable_const
  have hfcLp (t : Fin 3) : MemLp
      (fun x : ∀ i, Ω i => fc t (finsetCoordProj (B t) x)) 2 (Measure.pi μ) :=
    (hfLp t).sub (memLp_const _)
  have hgcLp (t : Fin 3) : MemLp
      (fun x : ∀ i, Ω i => gc t (finsetCoordProj (B t) x)) 2 (Measure.pi μ) :=
    (hgLp t).sub (memLp_const _)
  have hfc0 (t : Fin 3) := condExp_centeredBlockScore_zero μ B0 (B t)
    (htrain t) (f t) (hf t) (hfLp t)
  have hgc0 (t : Fin 3) := condExp_centeredBlockScore_zero μ B0 (B t)
    (htrain t) (g t) (hg t) (hgLp t)
  have hmain := condCov_threeBlockProduct μ B0 B htrain heval fc gc
    hfcmeas hgcmeas hfcLp hgcLp hfc0 hgc0
  have hcross (t : Fin 3) := condExp_centeredBlockCross_eq_covariance μ B0 (B t)
    (htrain t) (f t) (g t) (hf t) (hg t)
  filter_upwards [hmain, hcross 0, hcross 1, hcross 2] with x hx h0 h1 h2
  simpa only [fc, gc, Fin.prod_univ_three, h0, h1, h2] using hx

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
