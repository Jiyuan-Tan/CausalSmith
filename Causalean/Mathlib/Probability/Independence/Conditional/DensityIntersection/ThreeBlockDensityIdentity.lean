module
public import Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection.ThreeBlockMarginals

/-!
# Three-block density factorization versus the marginal-density identity

For a measurable finite density on a three-block product, a measurable factorization through
the conditioning block is equivalent to the cross-multiplied identity between the joint density,
its conditioning marginal, and its two block-with-conditioning marginals. This is the purely
density-theoretic half of the three-block conditional-independence criterion.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection

universe uA uB uC

section DensityFactorization

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
variable (muA : Measure A) (muB : Measure B) (muC : Measure C)
variable [SigmaFinite muA] [SigmaFinite muB] [SigmaFinite muC]
variable {d : ThreeBlock A B C → ℝ≥0∞}
variable [IsFiniteMeasure ((threeBlockReference muA muB muC).withDensity d)]

/-- A measurable conditional product factorization of a finite three-block density implies the
cross-multiplied conditional-density identity. -/
theorem threeBlockDensityIdentity_of_factors (hd : Measurable d)
    (hfac : ThreeBlockFactors muA muB muC d) :
    ThreeBlockDensityIdentity muA muB muC d := by
  /- Expand all three marginal densities and use Tonelli to integrate the product factorization.
  Finiteness rules out the `0 * ∞` exceptional cases almost everywhere, after which the target
  is commutativity and associativity of multiplication in `ℝ≥0∞`. -/
  rcases hfac with ⟨a, b, ha, hb, hab⟩
  have hfirstMeas : Measurable (densityFirstConditioning muB d) := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (A × C) × B ↦ d (q.1.1, (q.2, q.1.2)))
    fun_prop
  have hsecondMeas : Measurable (densitySecondConditioning muA d) := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (B × C) × A ↦ d (q.2, (q.1.1, q.1.2)))
    fun_prop
  have hcondMeas : Measurable (densityConditioning muA muB d) := by
    apply Measurable.lintegral_prod_right
    change Measurable
      (fun q : C × A ↦ ∫⁻ b, d (q.2, (b, q.1)) ∂muB)
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (C × A) × B ↦ d (q.1.2, (q.2, q.1.1)))
    fun_prop
  have habABC : ∀ᵐ x ∂muA, ∀ᵐ y ∂muB, ∀ᵐ z ∂muC,
      d (x, (y, z)) = a (x, z) * b (y, z) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hab] with x hx
    exact Measure.ae_ae_of_ae_prod hx
  have habACB : ∀ᵐ x ∂muA, ∀ᵐ z ∂muC, ∀ᵐ y ∂muB,
      d (x, (y, z)) = a (x, z) * b (y, z) := by
    filter_upwards [habABC] with x hx
    exact (Measure.ae_ae_comm (by measurability)).1 hx
  have habBCA : ∀ᵐ y ∂muB, ∀ᵐ z ∂muC, ∀ᵐ x ∂muA,
      d (x, (y, z)) = a (x, z) * b (y, z) := by
    have hswap : ∀ᵐ yz ∂muB.prod muC, ∀ᵐ x ∂muA,
        d (x, yz) = a (x, yz.2) * b yz := by
      apply (Measure.ae_ae_comm (by measurability)).1
      exact Measure.ae_ae_of_ae_prod hab
    exact Measure.ae_ae_of_ae_prod hswap
  have hfirst : ∀ᵐ x ∂muA, ∀ᵐ z ∂muC,
      densityFirstConditioning muB d (x, z) =
        a (x, z) * ∫⁻ y, b (y, z) ∂muB := by
    filter_upwards [habACB] with x hx
    filter_upwards [hx] with z hz
    change (∫⁻ y, d (x, (y, z)) ∂muB) = _
    rw [lintegral_congr_ae hz, lintegral_const_mul]
    fun_prop
  have hsecond : ∀ᵐ y ∂muB, ∀ᵐ z ∂muC,
      densitySecondConditioning muA d (y, z) =
        (∫⁻ x, a (x, z) ∂muA) * b (y, z) := by
    filter_upwards [habBCA] with y hy
    filter_upwards [hy] with z hz
    change (∫⁻ x, d (x, (y, z)) ∂muA) = _
    rw [lintegral_congr_ae hz, lintegral_mul_const]
    fun_prop
  have hfirstCA : ∀ᵐ z ∂muC, ∀ᵐ x ∂muA,
      densityFirstConditioning muB d (x, z) =
        a (x, z) * ∫⁻ y, b (y, z) ∂muB := by
    apply (Measure.ae_ae_comm (by measurability)).1
    exact hfirst
  have hcond : ∀ᵐ z ∂muC,
      densityConditioning muA muB d z =
        (∫⁻ x, a (x, z) ∂muA) * (∫⁻ y, b (y, z) ∂muB) := by
    filter_upwards [hfirstCA] with z hz
    have hz' : (fun x ↦ ∫⁻ y, d (x, (y, z)) ∂muB) =ᵐ[muA]
        (fun x ↦ a (x, z) * ∫⁻ y, b (y, z) ∂muB) := by
      filter_upwards [hz] with x hx
      exact hx
    change (∫⁻ x, ∫⁻ y, d (x, (y, z)) ∂muB ∂muA) = _
    rw [lintegral_congr_ae hz', lintegral_mul_const]
    fun_prop
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [habABC, hfirst] with x hxy hxfirst
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [hxy, hsecond] with y hyz hysecond
  filter_upwards [hyz, hxfirst, hysecond, hcond] with z hdab hfirstz hsecondz hcondz
  rw [hdab, hfirstz, hsecondz, hcondz]
  ac_rfl

/-- For a measurable finite three-block density, the cross-multiplied conditional-density
identity yields a measurable product factorization given the third block. -/
theorem threeBlockFactors_of_densityIdentity (hd : Measurable d)
    (hid : ThreeBlockDensityIdentity muA muB muC d) :
    ThreeBlockFactors muA muB muC d := by
  /- Use `densityFirstConditioning muB d` as the first factor and the ratio of
  `densitySecondConditioning muA d` to `densityConditioning muA muB d` as the second.  On fibres
  where the conditioning marginal vanishes, Tonelli implies that `d` vanishes almost everywhere;
  on the remaining fibres, finiteness permits cancellation in the density identity. -/
  let dAC := densityFirstConditioning muB d
  let dBC := densitySecondConditioning muA d
  let dC := densityConditioning muA muB d
  have hdAC : Measurable dAC := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (A × C) × B ↦ d (q.1.1, (q.2, q.1.2)))
    fun_prop
  have hdBC : Measurable dBC := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (B × C) × A ↦ d (q.2, (q.1.1, q.1.2)))
    fun_prop
  have hdC : Measurable dC := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : C × A ↦ ∫⁻ b, d (q.2, (b, q.1)) ∂muB)
    apply Measurable.lintegral_prod_right
    change Measurable (fun q : (C × A) × B ↦ d (q.1.2, (q.2, q.1.1)))
    fun_prop
  have hdInt : ∫⁻ q, d q ∂threeBlockReference muA muB muC ≠ ∞ := by
    have h := measure_ne_top
      ((threeBlockReference muA muB muC).withDensity d) Set.univ
    simpa [withDensity_apply] using h
  have htotal : (∫⁻ c, dC c ∂muC) =
      ∫⁻ q, d q ∂threeBlockReference muA muB muC := by
    change (∫⁻ c, ∫⁻ a, ∫⁻ b, d (a, (b, c)) ∂muB ∂muA ∂muC) = _
    rw [← lintegral_prod
      (fun q : C × A ↦ ∫⁻ b, d (q.2, (b, q.1)) ∂muB) (by fun_prop)]
    rw [lintegral_prod_symm
      (fun q : C × A ↦ ∫⁻ b, d (q.2, (b, q.1)) ∂muB) (by fun_prop)]
    change _ = ∫⁻ q, d q ∂muA.prod (muB.prod muC)
    rw [lintegral_prod d hd.aemeasurable]
    apply lintegral_congr
    intro a
    rw [← lintegral_prod (fun q : C × B ↦ d (a, (q.2, q.1))) (by fun_prop)]
    rw [lintegral_prod_symm (fun q : C × B ↦ d (a, (q.2, q.1))) (by fun_prop)]
    rw [← lintegral_prod (fun q : B × C ↦ d (a, q)) (by fun_prop)]
  have hdCInt : ∫⁻ c, dC c ∂muC ≠ ∞ := by
    rwa [htotal]
  have hdCFinite : ∀ᵐ c ∂muC, dC c < ∞ := ae_lt_top hdC hdCInt
  have hzeroC : ∀ᵐ c ∂muC, ∀ᵐ a ∂muA, ∀ᵐ b ∂muB,
      dC c = 0 → dAC (a, c) = 0 ∧ d (a, (b, c)) = 0 := by
    refine ae_of_all muC fun c ↦ ?_
    by_cases hc : dC c = 0
    · have hACzero : (fun a ↦ dAC (a, c)) =ᵐ[muA] 0 := by
        apply (lintegral_eq_zero_iff (by fun_prop)).1
        simpa only [dC, dAC, densityConditioning, densityFirstConditioning] using hc
      filter_upwards [hACzero] with a ha0
      change dAC (a, c) = 0 at ha0
      have hdzero : (fun b ↦ d (a, (b, c))) =ᵐ[muB] 0 := by
        apply (lintegral_eq_zero_iff (by fun_prop)).1
        simpa only [dAC, densityFirstConditioning] using ha0
      filter_upwards [hdzero] with b hb0
      exact fun _ ↦ ⟨ha0, hb0⟩
    · exact ae_of_all muA fun _ ↦ ae_of_all muB fun _ h ↦ (hc h).elim
  have hzeroFlat : ∀ᵐ q ∂muC.prod (muA.prod muB),
      dC q.1 = 0 → dAC (q.2.1, q.1) = 0 ∧ d (q.2.1, (q.2.2, q.1)) = 0 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hzeroC] with c hc
    exact (Measure.ae_prod_iff_ae_ae (by measurability)).2 hc
  have hzeroSwap : ∀ᵐ ab ∂muA.prod muB, ∀ᵐ c ∂muC,
      dC c = 0 → dAC (ab.1, c) = 0 ∧ d (ab.1, (ab.2, c)) = 0 := by
    apply (Measure.ae_ae_comm (by measurability)).1
    exact Measure.ae_ae_of_ae_prod hzeroFlat
  have hzeroABC : ∀ᵐ a ∂muA, ∀ᵐ b ∂muB, ∀ᵐ c ∂muC,
      dC c = 0 → dAC (a, c) = 0 ∧ d (a, (b, c)) = 0 := by
    exact Measure.ae_ae_of_ae_prod hzeroSwap
  have hidABC : ∀ᵐ a ∂muA, ∀ᵐ b ∂muB, ∀ᵐ c ∂muC,
      d (a, (b, c)) * dC c = dAC (a, c) * dBC (b, c) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hid] with a ha
    exact Measure.ae_ae_of_ae_prod ha
  refine ⟨dAC, fun bc ↦ dBC bc / dC bc.2, hdAC, hdBC.div (hdC.comp measurable_snd), ?_⟩
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [hidABC, hzeroABC] with a ha hza
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ha, hza] with b hb hzb
  filter_upwards [hb, hzb, hdCFinite] with c hidc hzc hfin
  by_cases hc0 : dC c = 0
  · rw [(hzc hc0).2, (hzc hc0).1]
    simp
  · symm
    calc
      dAC (a, c) * (dBC (b, c) / dC c) =
          (dAC (a, c) * dBC (b, c)) / dC c := by
            simp only [div_eq_mul_inv]
            ac_rfl
      _ = (d (a, (b, c)) * dC c) / dC c := by rw [hidc]
      _ = d (a, (b, c)) := ENNReal.mul_div_cancel_right hc0 hfin.ne

/-- For [a measurable](hyp:hd) three-block density against a product of three σ-finite reference
measures, with finite total mass, [almost-everywhere factorization into a measurable term of the
first and conditioning blocks times a measurable term of the second and conditioning blocks is
equivalent to the almost-everywhere identity that the joint density times its conditioning marginal
equals the product of its two block-with-conditioning marginals](goal). -/
theorem threeBlockFactors_iff_densityIdentity (hd : Measurable d) :
    ThreeBlockFactors muA muB muC d ↔ ThreeBlockDensityIdentity muA muB muC d :=
  ⟨threeBlockDensityIdentity_of_factors muA muB muC hd,
    threeBlockFactors_of_densityIdentity muA muB muC hd⟩

end DensityFactorization

end Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection
