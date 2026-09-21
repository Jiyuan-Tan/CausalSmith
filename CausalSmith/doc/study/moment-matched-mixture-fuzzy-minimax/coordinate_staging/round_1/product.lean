import Causalean.Stat.Minimax.MomentMatchedMixture.Analytic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite products of prior-predictive mixtures

This module tensorizes one-coordinate total-variation bounds and packages the independent
coordinate prior-predictive law used by high-dimensional applications.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.Minimax.MomentMatchedMixture

variable {X : Type*} [MeasurableSpace X]

/-- Given [a dimension](hyp:d) and [a scalar prior](hyp:π), the [independent coordinate prior](goal)
is the finite product of that prior across all coordinates. -/
noncomputable def productPrior (d : ℕ) (π : Measure ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => π

/-- Given [a dimension](hyp:d), [a scalar prior](hyp:π), and [a one-coordinate experiment
kernel](hyp:K), the [independent coordinate prior-predictive law](goal) is the finite product of
the one-coordinate mixture law. -/
noncomputable def productPriorPredictive (d : ℕ) (π : Measure ℝ) (K : Kernel ℝ X) :
    Measure (Fin d → X) :=
  Measure.pi fun _ : Fin d => priorPredictive π K

/-- Given [a dimension](hyp:d), [a probability prior](hyp:π), and [an experiment kernel](hyp:K)
whose [component laws are probability laws](hyp:hK), [the independent coordinate
prior-predictive law is a probability law](goal). -/
theorem productPriorPredictive_isProbability (d : ℕ) (π : Measure ℝ) (K : Kernel ℝ X)
    [IsProbabilityMeasure π] (hK : ∀ θ, IsProbabilityMeasure (K θ)) :
    IsProbabilityMeasure (productPriorPredictive d π K) := by
  change IsProbabilityMeasure (Measure.pi fun _ : Fin d => priorPredictive π K)
  exact @Measure.pi.instIsProbabilityMeasure (Fin d) (fun _ => X) inferInstance
    (fun _ => inferInstance) _ (fun _ => priorPredictive_isProbability π K hK)

/-- Given [a dimension](hyp:d), [a probability prior](hyp:π), [a one-coordinate experiment
kernel](hyp:K) with [probability component laws](hyp:hK), and [a product experiment
kernel](hyp:productKernel) whose [fibres are the coordinatewise product laws](hyp:hfiber), the
[mixture mass of a coordinate rectangle](hyp:s,hs) [factors into the product of the
one-coordinate predictive masses](goal). -/
theorem priorPredictive_productPrior_apply_pi
    (d : ℕ) (π : Measure ℝ) (K : Kernel ℝ X)
    (productKernel : Kernel (Fin d → ℝ) (Fin d → X))
    [IsProbabilityMeasure π] (hK : ∀ θ, IsProbabilityMeasure (K θ))
    (hfiber : ∀ θ, productKernel θ = Measure.pi fun i : Fin d => K (θ i))
    (s : Fin d → Set X) (hs : ∀ i, MeasurableSet (s i)) :
    priorPredictive (productPrior d π) productKernel (Set.pi Set.univ s) =
      ∏ i, priorPredictive π K (s i) := by
  rw [priorPredictive_apply _ _ (by
    exact MeasurableSet.pi Set.countable_univ fun i _ => hs i)]
  simp_rw [hfiber, Measure.pi_pi]
  letI : IsProbabilityMeasure (priorPredictive π K) :=
    priorPredictive_isProbability π K hK
  have hprodPrior : IsProbabilityMeasure (productPrior d π) := by
    unfold productPrior
    exact @Measure.pi.instIsProbabilityMeasure (Fin d) (fun _ => ℝ) inferInstance
      (fun _ => inferInstance) _ (fun _ => inferInstance)
  letI : IsProbabilityMeasure (productPrior d π) := hprodPrior
  have hcoord_le (i : Fin d) (x : ℝ) : K x (s i) ≤ 1 := by
    letI : IsProbabilityMeasure (K x) := hK x
    exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have hfun_meas (i : Fin d) : Measurable fun x => K x (s i) :=
    K.measurable_coe (hs i)
  have hfun_top (i : Fin d) : ∀ x, K x (s i) < ⊤ := fun x => by
    letI : IsProbabilityMeasure (K x) := hK x
    exact measure_lt_top _ _
  have hprod_meas : Measurable (fun θ : Fin d → ℝ => ∏ i, K (θ i) (s i)) := by
    exact Finset.univ.measurable_prod fun i _ =>
      (hfun_meas i).comp (measurable_pi_apply i)
  have hprod_top : ∀ θ : Fin d → ℝ, (∏ i, K (θ i) (s i)) < ⊤ := fun θ =>
    ENNReal.prod_lt_top fun i _ => hfun_top i (θ i)
  have hlhs_ne :
      (∫⁻ (θ : Fin d → ℝ), ∏ i, K (θ i) (s i) ∂productPrior d π) ≠ ⊤ := by
    apply ne_of_lt
    refine (lintegral_le_const (c := 1) ?_).trans_lt ENNReal.one_lt_top
    exact Filter.Eventually.of_forall fun θ =>
      Finset.prod_le_one' fun i _ => hcoord_le i (θ i)
  have hrhs_ne : (∏ i, priorPredictive π K (s i)) ≠ ⊤ :=
    (ENNReal.prod_lt_top fun i _ => measure_lt_top _ _).ne
  have hfactor :
      (∫ θ : Fin d → ℝ, ∏ i, (K (θ i) (s i)).toReal ∂productPrior d π) =
        ∏ i, ∫ x, (K x (s i)).toReal ∂π := by
    unfold productPrior
    exact integral_fintype_prod_eq_prod (fun i x => (K x (s i)).toReal)
  have hcoord_int (i : Fin d) :
      (∫ x, (K x (s i)).toReal ∂π) = (priorPredictive π K (s i)).toReal := by
    rw [priorPredictive_apply _ _ (hs i)]
    exact integral_toReal (hfun_meas i).aemeasurable
      (Filter.Eventually.of_forall (hfun_top i))
  apply (ENNReal.toReal_eq_toReal_iff' hlhs_ne hrhs_ne).mp
  rw [← integral_toReal hprod_meas.aemeasurable
    (Filter.Eventually.of_forall hprod_top)]
  simp_rw [ENNReal.toReal_prod]
  rw [hfactor]
  exact Finset.prod_congr rfl fun i _ => hcoord_int i

/-- Given [a dimension](hyp:d), [a probability prior](hyp:π), [a one-coordinate experiment
kernel](hyp:K) with [probability component laws](hyp:hK), and [a product experiment
kernel](hyp:productKernel) whose [fibres are the coordinatewise product laws](hyp:hfiber),
[mixing the product experiment against the product prior equals the product of the
one-coordinate prior-predictive mixtures](goal). -/
theorem priorPredictive_productPrior_eq_productPriorPredictive
    (d : ℕ) (π : Measure ℝ) (K : Kernel ℝ X)
    (productKernel : Kernel (Fin d → ℝ) (Fin d → X))
    [IsProbabilityMeasure π] (hK : ∀ θ, IsProbabilityMeasure (K θ))
    (hfiber : ∀ θ, productKernel θ = Measure.pi fun i : Fin d => K (θ i)) :
    priorPredictive (productPrior d π) productKernel = productPriorPredictive d π K := by
  -- Extensionality on measurable rectangles reduces both sides via `Measure.pi_pi`.
  -- On the left use `priorPredictive_apply` and `hfiber`; the remaining integral of
  -- the finite product of coordinate functions factors under `productPrior`.
  -- Treat `d = 0` explicitly if the finite-product integration API does so.
  letI : IsProbabilityMeasure (priorPredictive π K) :=
    priorPredictive_isProbability π K hK
  unfold productPriorPredictive
  refine (Measure.pi_eq fun s hs => ?_).symm
  exact priorPredictive_productPrior_apply_pi d π K productKernel hK hfiber s hs

/-- Given [two probability laws on one coordinate](hyp:μ0,μ1) and [two probability laws on a
second coordinate](hyp:ν0,ν1), [the total variation distance between the binary product laws is
at most the sum of the two coordinatewise distances](goal). -/
theorem tvDist_prod_le_add {Y : Type*} [MeasurableSpace Y]
    (μ0 μ1 : Measure X) (ν0 ν1 : Measure Y)
    [IsProbabilityMeasure μ0] [IsProbabilityMeasure μ1]
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1] :
    Causalean.Stat.tvDist (μ0.prod ν0) (μ1.prod ν1) ≤
      Causalean.Stat.tvDist μ0 μ1 + Causalean.Stat.tvDist ν0 ν1 := by
  unfold Causalean.Stat.tvDist
  refine ciSup_le fun A => ?_
  have hprodReal (μ : Measure X) (ν : Measure Y)
      [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
      (μ.prod ν).real A.1 = ∫ x, ν.real (Prod.mk x ⁻¹' A.1) ∂μ := by
    rw [measureReal_def, Measure.prod_apply A.2]
    symm
    exact integral_toReal
      (measurable_measure_prodMk_left A.2).aemeasurable
      (Filter.Eventually.of_forall fun x => measure_lt_top ν _)
  have hmeas0 : Measurable fun x => ν0.real (Prod.mk x ⁻¹' A.1) :=
    (measurable_measure_prodMk_left A.2).ennreal_toReal
  have houter :
      |(∫ x, ν0.real (Prod.mk x ⁻¹' A.1) ∂μ0) -
        ∫ x, ν0.real (Prod.mk x ⁻¹' A.1) ∂μ1| ≤
          Causalean.Stat.tvDist μ0 μ1 := by
    simpa using Causalean.Stat.tvDist_integral_range μ0 μ1
      (fun x => ν0.real (Prod.mk x ⁻¹' A.1)) hmeas0 0 1 zero_le_one
      (fun x => ⟨measureReal_nonneg, by simpa only [zero_add] using
        (measureReal_le_one : ν0.real (Prod.mk x ⁻¹' A.1) ≤ 1)⟩)
  have hf0int : Integrable (fun x => ν0.real (Prod.mk x ⁻¹' A.1)) μ1 :=
    Measure.integrable_measure_prodMk_left A.2 (measure_ne_top _ _)
  have hf1int : Integrable (fun x => ν1.real (Prod.mk x ⁻¹' A.1)) μ1 :=
    Measure.integrable_measure_prodMk_left A.2 (measure_ne_top _ _)
  have hinner :
      |(∫ x, ν0.real (Prod.mk x ⁻¹' A.1) ∂μ1) -
        ∫ x, ν1.real (Prod.mk x ⁻¹' A.1) ∂μ1| ≤
          Causalean.Stat.tvDist ν0 ν1 := by
    rw [← integral_sub hf0int hf1int]
    have hnorm := norm_setIntegral_le_of_norm_le_const_ae
      (μ := μ1) (s := Set.univ) (C := Causalean.Stat.tvDist ν0 ν1)
      (measure_lt_top μ1 Set.univ)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact Causalean.Stat.abs_measureReal_sub_le_tvDist
          (μ := ν0) (ν := ν1) (A := Prod.mk x ⁻¹' A.1)
          (A.2.preimage (measurable_prodMk_left (x := x))))
    simpa [Real.norm_eq_abs, probReal_univ] using hnorm
  rw [hprodReal μ0 ν0, hprodReal μ1 ν1]
  calc
    |(∫ x, ν0.real (Prod.mk x ⁻¹' A.1) ∂μ0) -
        ∫ x, ν1.real (Prod.mk x ⁻¹' A.1) ∂μ1| =
      |((∫ x, ν0.real (Prod.mk x ⁻¹' A.1) ∂μ0) -
         ∫ x, ν0.real (Prod.mk x ⁻¹' A.1) ∂μ1) +
        ((∫ x, ν0.real (Prod.mk x ⁻¹' A.1) ∂μ1) -
         ∫ x, ν1.real (Prod.mk x ⁻¹' A.1) ∂μ1)| := by
           congr 1
           ring
    _ ≤ |(∫ x, ν0.real (Prod.mk x ⁻¹' A.1) ∂μ0) -
            ∫ x, ν0.real (Prod.mk x ⁻¹' A.1) ∂μ1| +
          |(∫ x, ν0.real (Prod.mk x ⁻¹' A.1) ∂μ1) -
            ∫ x, ν1.real (Prod.mk x ⁻¹' A.1) ∂μ1| := abs_add_le _ _
    _ ≤ Causalean.Stat.tvDist μ0 μ1 + Causalean.Stat.tvDist ν0 ν1 :=
      add_le_add houter hinner

/-- Given [a number of coordinates](hyp:d) and [two one-coordinate probability laws](hyp:μ,ν),
[the total variation distance between their finite independent product laws is at most the
number of coordinates times their one-coordinate distance](goal). -/
theorem tvDist_pi_iid_le (d : ℕ) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Causalean.Stat.tvDist (Measure.pi fun _ : Fin d => μ) (Measure.pi fun _ : Fin d => ν) ≤
      d * Causalean.Stat.tvDist μ ν := by
  induction d with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
      simp [Causalean.Stat.tvDist]
  | succ n ih =>
      let e : ((i : Fin (n + 1)) → X) ≃ᵐ X × ((j : Fin n) → X) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let ρ := Measure.pi (fun _ : Fin (n + 1) => μ)
      let σ := Measure.pi (fun _ : Fin (n + 1) => ν)
      have hmap_eq :
          Causalean.Stat.tvDist (ρ.map e) (σ.map e) =
            Causalean.Stat.tvDist ρ σ := by
        letI : IsProbabilityMeasure (ρ.map e) :=
          Measure.isProbabilityMeasure_map e.measurable.aemeasurable
        letI : IsProbabilityMeasure (σ.map e) :=
          Measure.isProbabilityMeasure_map e.measurable.aemeasurable
        apply le_antisymm
        · unfold Causalean.Stat.tvDist
          refine ciSup_le fun A => ?_
          rw [Measure.real, Measure.real, Measure.map_apply e.measurable A.2,
            Measure.map_apply e.measurable A.2]
          exact Causalean.Stat.abs_measureReal_sub_le_tvDist
            (A.2.preimage e.measurable)
        · unfold Causalean.Stat.tvDist
          refine ciSup_le fun A => ?_
          have hB : MeasurableSet (e.symm ⁻¹' A.1) :=
            A.2.preimage e.symm.measurable
          have hle := Causalean.Stat.abs_measureReal_sub_le_tvDist
            (μ := ρ.map e) (ν := σ.map e) hB
          rw [Measure.real, Measure.real, Measure.map_apply e.measurable hB,
            Measure.map_apply e.measurable hB] at hle
          have hpre : e ⁻¹' (e.symm ⁻¹' A.1) = A.1 := by
            ext x
            simp
          rw [hpre] at hle
          exact hle
      have hμ :
          Measure.map e (Measure.pi (fun _ : Fin (n + 1) => μ)) =
            μ.prod (Measure.pi (fun _ : Fin n => μ)) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove
            (μ := fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1))).map_eq
      have hν :
          Measure.map e (Measure.pi (fun _ : Fin (n + 1) => ν)) =
            ν.prod (Measure.pi (fun _ : Fin n => ν)) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove
            (μ := fun _ : Fin (n + 1) => ν) (0 : Fin (n + 1))).map_eq
      calc
        Causalean.Stat.tvDist (Measure.pi fun _ : Fin (n + 1) => μ)
            (Measure.pi fun _ : Fin (n + 1) => ν) =
            Causalean.Stat.tvDist
              (Measure.map e (Measure.pi fun _ : Fin (n + 1) => μ))
              (Measure.map e (Measure.pi fun _ : Fin (n + 1) => ν)) := by
          simpa [ρ, σ] using hmap_eq.symm
        _ = Causalean.Stat.tvDist
              (μ.prod (Measure.pi fun _ : Fin n => μ))
              (ν.prod (Measure.pi fun _ : Fin n => ν)) := by rw [hμ, hν]
        _ ≤ Causalean.Stat.tvDist μ ν +
              Causalean.Stat.tvDist (Measure.pi fun _ : Fin n => μ)
                (Measure.pi fun _ : Fin n => ν) :=
          tvDist_prod_le_add _ _ _ _
        _ ≤ Causalean.Stat.tvDist μ ν + n * Causalean.Stat.tvDist μ ν :=
          add_le_add (le_refl _) ih
        _ = ((n + 1 : ℕ) : ℝ) * Causalean.Stat.tvDist μ ν := by
          rw [Nat.cast_add, Nat.cast_one]
          ring

/-- Given [a dimension](hyp:d), [two probability priors](hyp:π0,π1), [a probability experiment
kernel](hyp:K,hK), [a probability dominating law](hyp:Q), [a jointly measurable nonnegative
likelihood family](hyp:likelihood,hmeas,hnonneg), [a nonnegative interaction
scale](hyp:lambda,hlambda), [a nonnegative support radius](hyp:a,ha), and [a matching
degree](hyp:degree), if [each experiment law has the stated density](hyp:hdensity), [likelihood
inner products have the exponential product form](hyp:hinner), [both priors are supported within
the radius](hyp:hsupp0,hsupp1), and [their moments agree through that degree](hyp:hmom), then
[the product prior-predictive mixtures are within the dimension times the square root of the
explicit unmatched series tail in total variation](goal). -/
theorem momentMatchedProductMixture_tv_le
    (d : ℕ) (π0 π1 : Measure ℝ) (K : Kernel ℝ X) (Q : Measure X)
    (likelihood : ℝ → X → ℝ) [IsProbabilityMeasure π0] [IsProbabilityMeasure π1]
    [IsProbabilityMeasure Q] (hK : ∀ θ, IsProbabilityMeasure (K θ))
    (lambda a : ℝ) (degree : ℕ)
    (hlambda : 0 ≤ lambda) (ha : 0 ≤ a)
    (hmeas : Measurable fun p : ℝ × X => likelihood p.1 p.2)
    (hnonneg : ∀ θ x, 0 ≤ likelihood θ x)
    (hdensity : ∀ θ, K θ = Q.withDensity fun x => ENNReal.ofReal (likelihood θ x))
    (hinner : ∀ θ θ',
      ∫ x, likelihood θ x * likelihood θ' x ∂Q = Real.exp (lambda * θ * θ'))
    (hsupp0 : π0 {θ | |θ| ≤ a} = 1) (hsupp1 : π1 {θ | |θ| ≤ a} = 1)
    (hmom : ∀ n ≤ degree, ∫ θ, θ ^ n ∂π0 = ∫ θ, θ ^ n ∂π1) :
    Causalean.Stat.tvDist (productPriorPredictive d π0 K) (productPriorPredictive d π1 K) ≤
      d * Real.sqrt (exponentialSeriesTail degree (lambda * a ^ 2)) := by
  -- This is the direct composition of `tvDist_pi_iid_le` and
  -- `momentMatchedMixture_tv_le_sqrt_tail`, after unfolding
  -- `productPriorPredictive` and multiplying by the nonnegative cast of `d`.
  letI : IsProbabilityMeasure (priorPredictive π0 K) :=
    priorPredictive_isProbability π0 K hK
  letI : IsProbabilityMeasure (priorPredictive π1 K) :=
    priorPredictive_isProbability π1 K hK
  unfold productPriorPredictive
  calc
    Causalean.Stat.tvDist (Measure.pi fun _ : Fin d => priorPredictive π0 K)
        (Measure.pi fun _ : Fin d => priorPredictive π1 K) ≤
        d * Causalean.Stat.tvDist (priorPredictive π0 K) (priorPredictive π1 K) :=
      tvDist_pi_iid_le d _ _
    _ ≤ d * Real.sqrt (exponentialSeriesTail degree (lambda * a ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (momentMatchedMixture_tv_le_sqrt_tail π0 π1 K Q likelihood hK lambda a degree
          hlambda ha hmeas hnonneg hdensity hinner hsupp0 hsupp1 hmom)
        (Nat.cast_nonneg d)

end Causalean.Stat.Minimax.MomentMatchedMixture
