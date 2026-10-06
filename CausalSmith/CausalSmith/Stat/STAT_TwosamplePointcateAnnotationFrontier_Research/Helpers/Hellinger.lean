module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Basic
public import Causalean.Stat.Minimax.HellingerAffinity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Helpers/Hellinger

Two-channel point-CATE annotation frontier: Helpers/Hellinger
constructions and obligations.
-/

@[expose] public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


-- @node: def:hellinger
/-- Given [the specified input B](hyp:B), [the specified input C](hyp:C), [hellinger sq](goal) is the corresponding construction. -/
def hellingerSq {Ω : Type*} [MeasurableSpace Ω] (B C : Measure Ω) : ℝ :=
  Causalean.Stat.hellingerSqDensity (B+C)
    (fun w => (B.rnDeriv (B+C) w).toReal) (fun w => (C.rnDeriv (B+C) w).toReal) -- @realizes Htwo(unhalved squared Hellinger)
/-- A common s-finite reference kernel with jointly measurable conditional densities.  Given [the specified input Z](hyp:Z), [the specified input B](hyp:B), [the specified input C](hyp:C), [has conditional densities](goal) is the corresponding construction. -/
def HasConditionalDensities {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (B C : Kernel Z Ω) : Prop :=
  ∃ ξ : Kernel Z Ω, IsSFiniteKernel ξ ∧
    ∃ f g : Z × Ω → ℝ≥0∞, Measurable f ∧ Measurable g ∧
      (∀ z, B z = (ξ z).withDensity (fun w => f (z,w))) ∧
      (∀ z, C z = (ξ z).withDensity (fun w => g (z,w)))
/-- Square-root differences are homogeneous of degree one in their densities.  Given [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input c](hyp:c), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the specified input hc](hyp:hc), [the sqrt difference square mul conclusion](goal) holds. -/
lemma sqrt_difference_square_mul (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    c * (Real.sqrt a - Real.sqrt b)^2 =
      (Real.sqrt (a*c) - Real.sqrt (b*c))^2 := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul hb]
  nlinarith [Real.sq_sqrt hc]

/-- The sum-of-laws definition agrees with any finite dominating reference measure.  Given [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input hB](hyp:hB), [the specified input hC](hyp:hC), [the hellinger sq eq density conclusion](goal) holds. -/
lemma hellingerSq_eq_density {Ω : Type*} [MeasurableSpace Ω]
    (B C ξ : Measure Ω) [IsFiniteMeasure B] [IsFiniteMeasure C] [IsFiniteMeasure ξ]
    (hB : B ≪ ξ) (hC : C ≪ ξ) :
    hellingerSq B C = Causalean.Stat.hellingerSqDensity ξ
      (fun x => (B.rnDeriv ξ x).toReal) (fun x => (C.rnDeriv ξ x).toReal) := by
  have hsum : B+C ≪ ξ := hB.add_left hC
  have hBsum : B ≪ B+C := Measure.AbsolutelyContinuous.rfl.add_right C
  have hCsum : C ≪ B+C := Measure.AbsolutelyContinuous.rfl.add_right' B
  have hb := Measure.rnDeriv_mul_rnDeriv (κ := ξ) hBsum
  have hc := Measure.rnDeriv_mul_rnDeriv (κ := ξ) hCsum
  unfold hellingerSq Causalean.Stat.hellingerSqDensity
  rw [← integral_toReal_rnDeriv_mul hsum]
  apply integral_congr_ae
  filter_upwards [hb, hc] with x hxB hxC
  have hrB : (B.rnDeriv ξ x).toReal =
      (B.rnDeriv (B+C) x).toReal * ((B+C).rnDeriv ξ x).toReal := by
    rw [← hxB, Pi.mul_apply, ENNReal.toReal_mul]
  have hrC : (C.rnDeriv ξ x).toReal =
      (C.rnDeriv (B+C) x).toReal * ((B+C).rnDeriv ξ x).toReal := by
    rw [← hxC, Pi.mul_apply, ENNReal.toReal_mul]
  rw [hrB, hrC]
  exact sqrt_difference_square_mul _ _ _ ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- Products of integrable nonnegative densities represent products of their laws.  Given [the specified input E](hyp:E), [the specified input B](hyp:B), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input hf0](hyp:hf0), [the specified input hB](hyp:hB), [the pi real density conclusion](goal) holds. -/
lemma pi_real_density {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (μ B : ∀ i, Measure (E i))
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsProbabilityMeasure (B i)]
    (f : ∀ i, E i → ℝ) (hf : ∀ i, Integrable (f i) (μ i))
    (hf0 : ∀ i x, 0 ≤ f i x)
    (hB : ∀ i, B i = (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) :
    Measure.pi B = (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (show Integrable (fun x => ∏ i, f i (x i)) ((Measure.pi μ).restrict (Set.pi univ s)) from by
      rw [Measure.restrict_pi_pi]
      exact Integrable.fintype_prod_dep (fun i => (hf i).integrableOn))
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hf0 i (x i))))]
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hf0 i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [hB i, withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).integrableOn
    (Filter.Eventually.of_forall (hf0 i))

/-- A finite absolutely continuous law has its real Radon--Nikodym density.  Given [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the real rn deriv density conclusion](goal) holds. -/
lemma real_rnDeriv_density {Ω : Type*} [MeasurableSpace Ω]
    (B μ : Measure Ω) [IsFiniteMeasure B] [IsFiniteMeasure μ] (hB : B ≪ μ) :
    B = μ.withDensity (fun x => ENNReal.ofReal (B.rnDeriv μ x).toReal) := by
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq B μ hB]
  apply withDensity_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top B μ] with x hx
  exact (ENNReal.ofReal_toReal hx.ne).symm

/-- Explicit densities can be used in the sum-of-laws Hellinger definition.  Given [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input hf0](hyp:hf0), [the specified input hg0](hyp:hg0), [the specified input hB](hyp:hB), [the specified input hC](hyp:hC), [the hellinger sq real density conclusion](goal) holds. -/
lemma hellingerSq_real_density {Ω : Type*} [MeasurableSpace Ω]
    (B C μ : Measure Ω) [IsFiniteMeasure B] [IsFiniteMeasure C] [IsFiniteMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hB : B = μ.withDensity (fun x => ENNReal.ofReal (f x)))
    (hC : C = μ.withDensity (fun x => ENNReal.ofReal (g x))) :
    hellingerSq B C = Causalean.Stat.hellingerSqDensity μ f g := by
  rw [hellingerSq_eq_density B C μ
    (hB ▸ withDensity_absolutelyContinuous μ _)
    (hC ▸ withDensity_absolutelyContinuous μ _)]
  have hb : B.rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (f x) := by
    rw [hB]; exact Measure.rnDeriv_withDensity μ (by fun_prop)
  have hc : C.rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (g x) := by
    rw [hC]; exact Measure.rnDeriv_withDensity μ (by fun_prop)
  apply integral_congr_ae
  filter_upwards [hb, hc] with x hxB hxC
  simp only [hxB, hxC, ENNReal.toReal_ofReal (hf0 x), ENNReal.toReal_ofReal (hg0 x)]

/-- Affinity of two normalized nonnegative densities lies in the unit interval.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input hf0](hyp:hf0), [the specified input hg0](hyp:hg0), [the specified input hf1](hyp:hf1), [the specified input hg1](hyp:hg1), [the density affinity mem unit conclusion](goal) holds. -/
lemma densityAffinity_mem_unit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : ∫ x, f x ∂μ = 1) (hg1 : ∫ x, g x ∂μ = 1) :
    0 ≤ Causalean.Stat.densityAffinity μ f g ∧
      Causalean.Stat.densityAffinity μ f g ≤ 1 := by
  refine ⟨integral_nonneg (fun x => Real.sqrt_nonneg _), ?_⟩
  have hid := Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity
    μ f g hf hg hf0 hg0 hf1 hg1
  have hn : 0 ≤ Causalean.Stat.hellingerSqDensity μ f g :=
    integral_nonneg (fun x => sq_nonneg _)
  linarith

/-- Squared Hellinger distance subadditivity for finite products of probability laws.  Given [the specified input E](hyp:E), [the specified input B](hyp:B), [the specified input C](hyp:C), [the hellinger sq pi le sum conclusion](goal) holds. -/
lemma hellingerSq_pi_le_sum {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (B C : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (B i)] [∀ i, IsProbabilityMeasure (C i)] :
    hellingerSq (Measure.pi B) (Measure.pi C) ≤ ∑ i, hellingerSq (B i) (C i) := by
  classical
  let μ := fun i => B i + C i
  let f := fun i x => (B i |>.rnDeriv (μ i) x).toReal
  let g := fun i x => (C i |>.rnDeriv (μ i) x).toReal
  have hBa (i : ι) : B i ≪ μ i := Measure.AbsolutelyContinuous.rfl.add_right _
  have hCa (i : ι) : C i ≪ μ i := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hf (i : ι) : Integrable (f i) (μ i) := by fun_prop
  have hg (i : ι) : Integrable (g i) (μ i) := by fun_prop
  have hfm (i : ι) : Measurable (f i) := by fun_prop
  have hgm (i : ι) : Measurable (g i) := by fun_prop
  have hf0 (i : ι) (x : E i) : 0 ≤ f i x := ENNReal.toReal_nonneg
  have hg0 (i : ι) (x : E i) : 0 ≤ g i x := ENNReal.toReal_nonneg
  have hf1 (i : ι) : ∫ x, f i x ∂μ i = 1 := by
    dsimp [f]; rw [Measure.integral_toReal_rnDeriv (hBa i)]; simp
  have hg1 (i : ι) : ∫ x, g i x ∂μ i = 1 := by
    dsimp [g]; rw [Measure.integral_toReal_rnDeriv (hCa i)]; simp
  have hBd (i : ι) : B i = (μ i).withDensity (fun x => ENNReal.ofReal (f i x)) :=
    real_rnDeriv_density _ _ (hBa i)
  have hCd (i : ι) : C i = (μ i).withDensity (fun x => ENNReal.ofReal (g i x)) :=
    real_rnDeriv_density _ _ (hCa i)
  have hid (i : ι) : hellingerSq (B i) (C i) =
      2 * (1 - Causalean.Stat.densityAffinity (μ i) (f i) (g i)) := by
    rw [hellingerSq_real_density _ _ _ _ _ (hfm i) (hgm i) (hf0 i) (hg0 i) (hBd i) (hCd i)]
    exact Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity
      _ _ _ (hf i) (hg i) (hf0 i) (hg0 i) (hf1 i) (hg1 i)
  rw [hellingerSq_real_density _ _ (Measure.pi μ)
    (fun x => ∏ i, f i (x i)) (fun x => ∏ i, g i (x i))
    (by fun_prop) (by fun_prop)
    (fun x => Finset.prod_nonneg (fun i _ => hf0 i (x i)))
    (fun x => Finset.prod_nonneg (fun i _ => hg0 i (x i)))
    (pi_real_density μ B f hf hf0 hBd) (pi_real_density μ C g hg hg0 hCd)]
  rw [Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity _ _ _
    (Integrable.fintype_prod_dep hf) (Integrable.fintype_prod_dep hg)
    (fun x => Finset.prod_nonneg (fun i _ => hf0 i (x i)))
    (fun x => Finset.prod_nonneg (fun i _ => hg0 i (x i)))
    (by rw [integral_fintype_prod_eq_prod]; simp [hf1])
    (by rw [integral_fintype_prod_eq_prod]; simp [hg1])]
  rw [Causalean.Stat.densityAffinity_pi μ f g hf0 hg0]
  simp_rw [hid]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  exact Causalean.Stat.one_sub_prod_le_sum _
    (fun i => (densityAffinity_mem_unit _ _ _ (hf i) (hg i) (hf0 i) (hg0 i) (hf1 i) (hg1 i)).1)
    (fun i => (densityAffinity_mem_unit _ _ _ (hf i) (hg i) (hf0 i) (hg0 i) (hf1 i) (hg1 i)).2)

/-- Normalizing two measurable densities against their sum gives a bounded density.  Given [the specified input a](hyp:a), [the specified input b](hyp:b), [the density ratio le one conclusion](goal) holds. -/
lemma density_ratio_le_one (a b : ℝ≥0∞) : a / (a+b) ≤ 1 :=
  (ENNReal.div_le_div_right (le_add_right le_rfl) _).trans ENNReal.div_self_le_one

/-- A law's density against the sum of two laws is the normalized original density.  Given [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input hB](hyp:hB), [the specified input hC](hyp:hC), [the with density density ratio conclusion](goal) holds. -/
lemma withDensity_density_ratio {Ω : Type*} [MeasurableSpace Ω]
    (B C ξ : Measure Ω) [IsFiniteMeasure B] [IsFiniteMeasure C]
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hB : B = ξ.withDensity f) (hC : C = ξ.withDensity g) :
    (B+C).withDensity (fun x => f x / (f x+g x)) = B := by
  have hsum : B+C = ξ.withDensity (fun x => f x+g x) := by
    rw [hB, hC, ← withDensity_add_left hf]
    rfl
  have hfin : ∫⁻ x, f x+g x ∂ξ ≠ ⊤ := by
    have ht : (B+C) univ ≠ ⊤ := measure_ne_top _ _
    rwa [hsum, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at ht
  rw [hsum, ← withDensity_mul ξ
    (f := fun x => f x+g x) (g := fun x => f x/(f x+g x))
    (by fun_prop) (by fun_prop), hB]
  apply withDensity_congr_ae
  filter_upwards [ae_lt_top (hf.add hg) hfin] with x hx
  exact ENNReal.mul_div_cancel' (fun hzero => by
    have h : f x ≤ f x+g x := le_add_right le_rfl
    change f x+g x = 0 at hzero
    rw [hzero] at h
    exact le_antisymm h bot_le) (fun htop => False.elim (hx.ne htop))

/-- Measurable densities bounded by one have integrable squared square-root differences.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input hf0](hyp:hf0), [the specified input hg0](hyp:hg0), [the specified input hf1](hyp:hf1), [the specified input hg1](hyp:hg1), [the integrable sqrt difference bounded conclusion](goal) holds. -/
lemma integrable_sqrt_difference_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1) :
    Integrable (fun x => (Real.sqrt (f x) - Real.sqrt (g x))^2) μ := by
  apply (integrable_const (4:ℝ)).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsf : Real.sqrt (f x) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (hf1 x)
  have hsg : Real.sqrt (g x) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (hg1 x)
  nlinarith [Real.sqrt_nonneg (f x), Real.sqrt_nonneg (g x)]

/-- Joint laws with a common marginal have the average conditional squared Hellinger distance.  Given [the specified input Z](hyp:Z), [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input hBC](hyp:hBC), [the hellinger sq comp prod common conclusion](goal) holds. -/
lemma hellingerSq_compProd_common {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (ν : Measure Z) [IsProbabilityMeasure ν] (B C : Kernel Z Ω)
    [IsMarkovKernel B] [IsMarkovKernel C] (hBC : HasConditionalDensities B C) :
    hellingerSq (ν ⊗ₘ B) (ν ⊗ₘ C) = ∫ z, hellingerSq (B z) (C z) ∂ν := by
  obtain ⟨ξ, hξ, f, g, hf, hg, hB, hC⟩ := hBC
  let K := B+C
  let r : Z × Ω → ℝ≥0∞ := fun p => f p / (f p+g p)
  let s : Z × Ω → ℝ≥0∞ := fun p => g p / (f p+g p)
  have hr : Measurable r := by fun_prop
  have hs : Measurable s := by fun_prop
  have hr1 (p : Z × Ω) : r p ≤ 1 := density_ratio_le_one _ _
  have hs1 (p : Z × Ω) : s p ≤ 1 := by
    simpa only [add_comm] using density_ratio_le_one (g p) (f p)
  have hrfin (p : Z × Ω) : r p ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (hr1 p) (by simp))
  have hsfin (p : Z × Ω) : s p ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (hs1 p) (by simp))
  have hBr (z : Z) : B z = (K z).withDensity (fun w => ENNReal.ofReal (r (z,w)).toReal) := by
    rw [show (fun w => ENNReal.ofReal (r (z,w)).toReal) = (fun w => r (z,w)) from
      funext (fun w => ENNReal.ofReal_toReal (hrfin (z,w)))]
    exact (withDensity_density_ratio (B z) (C z) (ξ z) _ _
      (hf.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left) (hB z) (hC z)).symm
  have hCs (z : Z) : C z = (K z).withDensity (fun w => ENNReal.ofReal (s (z,w)).toReal) := by
    rw [show (fun w => ENNReal.ofReal (s (z,w)).toReal) = (fun w => s (z,w)) from
      funext (fun w => ENNReal.ofReal_toReal (hsfin (z,w)))]
    simpa only [K, add_apply, Function.comp_def, add_comm, s] using
      (withDensity_density_ratio (C z) (B z) (ξ z) _ _
        (hg.comp measurable_prodMk_left) (hf.comp measurable_prodMk_left) (hC z) (hB z)).symm
  have hKr : K.withDensity (fun z w => r (z,w)) = B := by
    ext z : 1
    rw [Kernel.withDensity_apply _ hr]
    simpa only [ENNReal.ofReal_toReal (hrfin _)] using (hBr z).symm
  have hKs : K.withDensity (fun z w => s (z,w)) = C := by
    ext z : 1
    rw [Kernel.withDensity_apply _ hs]
    simpa only [ENNReal.ofReal_toReal (hsfin _)] using (hCs z).symm
  have : IsFiniteKernel (K.withDensity (fun z w => r (z,w))) := by
    rw [hKr]; infer_instance
  have : IsFiniteKernel (K.withDensity (fun z w => s (z,w))) := by
    rw [hKs]; infer_instance
  have hjointB : ν ⊗ₘ B = (ν ⊗ₘ K).withDensity (fun p => ENNReal.ofReal (r p).toReal) := by
    rw [← hKr, Measure.compProd_withDensity hr]
    congr 1
    funext p
    exact (ENNReal.ofReal_toReal (hrfin p)).symm
  have hjointC : ν ⊗ₘ C = (ν ⊗ₘ K).withDensity (fun p => ENNReal.ofReal (s p).toReal) := by
    rw [← hKs, Measure.compProd_withDensity hs]
    congr 1
    funext p
    exact (ENNReal.ofReal_toReal (hsfin p)).symm
  have hrr1 (p : Z × Ω) : (r p).toReal ≤ 1 := by
    exact_mod_cast ENNReal.toReal_mono (by simp : (1:ℝ≥0∞) ≠ ⊤) (hr1 p)
  have hss1 (p : Z × Ω) : (s p).toReal ≤ 1 := by
    exact_mod_cast ENNReal.toReal_mono (by simp : (1:ℝ≥0∞) ≠ ⊤) (hs1 p)
  rw [hellingerSq_real_density _ _ (ν ⊗ₘ K) _ _ (by fun_prop) (by fun_prop)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg) hjointB hjointC]
  unfold Causalean.Stat.hellingerSqDensity
  rw [Measure.integral_compProd (integrable_sqrt_difference_bounded (ν ⊗ₘ K)
    (fun p => (r p).toReal) (fun p => (s p).toReal) (by fun_prop) (by fun_prop)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg) hrr1 hss1)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  exact (hellingerSq_real_density (B z) (C z) (K z) _ _
    (by fun_prop) (by fun_prop) (fun _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg) (hBr z) (hCs z)).symm

/-- Appending a common finite measure multiplies squared Hellinger distance by its mass.  Given [the specified input Z](hyp:Z), [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input G](hyp:G), [the hellinger sq prod common conclusion](goal) holds. -/
lemma hellingerSq_prod_common {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (B C : Measure Ω) (G : Measure Z) [IsFiniteMeasure B]
    [IsFiniteMeasure C] [IsFiniteMeasure G] :
    hellingerSq (B.prod G) (C.prod G) = G.real univ * hellingerSq B C := by
  have hB := rnDeriv_measure_compProd_left B (B+C) (Kernel.const Ω G)
  have hC := rnDeriv_measure_compProd_left C (B+C) (Kernel.const Ω G)
  simp only [Measure.compProd_const] at hB hC
  unfold hellingerSq Causalean.Stat.hellingerSqDensity
  rw [← Measure.add_prod]
  calc
    _ = ∫ p : Ω × Z,
        (Real.sqrt ((B.rnDeriv (B+C) p.1).toReal) -
          Real.sqrt ((C.rnDeriv (B+C) p.1).toReal))^2 ∂(B+C).prod G := by
      apply integral_congr_ae
      filter_upwards [hB, hC] with p hpB hpC
      rw [hpB, hpC]
    _ = _ := integral_fun_fst
      (fun x => (Real.sqrt ((B.rnDeriv (B+C) x).toReal) -
        Real.sqrt ((C.rnDeriv (B+C) x).toReal))^2)

/-- A common independent probability factor preserves squared Hellinger distance.  Given [the specified input Z](hyp:Z), [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input G](hyp:G), [the hellinger sq prod probability conclusion](goal) holds. -/
lemma hellingerSq_prod_probability {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (B C : Measure Ω) (G : Measure Z) [IsProbabilityMeasure B]
    [IsProbabilityMeasure C] [IsProbabilityMeasure G] :
    hellingerSq (B.prod G) (C.prod G) = hellingerSq B C := by
  rw [hellingerSq_prod_common]
  simp

-- @node: lem:hellinger-block-calculus
/-- [the hellinger block calculus conclusion](goal) holds. -/
lemma hellinger_block_calculus :
    (∀ (ι : Type) [Fintype ι] (E : ι → Type) [∀ i, MeasurableSpace (E i)]
      (B C : ∀ i, Measure (E i)), (∀ i, IsProbabilityMeasure (B i)) →
      (∀ i, IsProbabilityMeasure (C i)) →
      hellingerSq (Measure.pi B) (Measure.pi C) ≤ ∑ i, hellingerSq (B i) (C i)) ∧
    (∀ (Z Ω : Type) [MeasurableSpace Z] [MeasurableSpace Ω]
      (ν : Measure Z) [IsProbabilityMeasure ν] (B C : Kernel Z Ω)
      [IsMarkovKernel B] [IsMarkovKernel C], HasConditionalDensities B C →
      hellingerSq (ν ⊗ₘ B) (ν ⊗ₘ C) = ∫ z, hellingerSq (B z) (C z) ∂ν) ∧
    (∀ (Ω Z : Type) [MeasurableSpace Ω] [MeasurableSpace Z]
      (B C : Measure Ω) (G : Measure Z) [IsProbabilityMeasure B]
      [IsProbabilityMeasure C] [IsProbabilityMeasure G],
      hellingerSq (B.prod G) (C.prod G) = hellingerSq B C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ι _ E _ B C hB hC
    have := hB
    have := hC
    exact hellingerSq_pi_le_sum B C
  · intro Z Ω _ _ ν _ B C _ _ hBC
    exact hellingerSq_compProd_common ν B C hBC
  · intro Ω Z _ _ B C G _ _ _
    exact hellingerSq_prod_probability B C G

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
