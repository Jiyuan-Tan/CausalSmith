module
public import Causalean.Stat.Concentration.Hilbert.CrossInnerProduct
public import Mathlib.Probability.Moments.Variance

/-! Orthogonality of the linear and quadratic terms from independent centered blocks. -/
public section
set_option linter.style.whitespace false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Independence and zero means remove all mixed terms in the quadratic block expansion. [the parameters and conditions in the statement](hyp:J,hX,hY,hXL,hYL,hind), [the asserted mathematical result holds](goal). This statement assumes [the hXm condition](hyp:hXm), [the hYm condition](hyp:hYm), [the hXmom condition](hyp:hXmom), [the hYmom condition](hyp:hYmom). -/
-- @node: centered_block_quadratic_second_moment_le
lemma centered_block_quadratic_second_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {J : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin J))] [BorelSpace (EuclideanSpace ℝ (Fin J))]
    (X Y : Ω → EuclideanSpace ℝ (Fin J)) (m : EuclideanSpace ℝ (Fin J)) (Λ : ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXL : MemLp X ∞ ν) (hYL : MemLp Y ∞ ν) (hind : IndepFun X Y ν)
    (hXm : (∫ ω, X ω ∂ν) = 0) (hYm : (∫ ω, Y ω ∂ν) = 0)
    (hXmom : ∀ u, (∫ ω, inner ℝ u (X ω)^2 ∂ν) ≤ Λ*‖u‖^2)
    (hYmom : ∀ u, (∫ ω, inner ℝ u (Y ω)^2 ∂ν) ≤ Λ*‖u‖^2) :
    (∫ ω, (inner ℝ m (X ω)+inner ℝ m (Y ω)+inner ℝ (X ω) (Y ω))^2 ∂ν) ≤
      2*Λ*‖m‖^2+J*Λ^2 := by
  let a := fun ω => inner ℝ m (X ω)
  let b := fun ω => inner ℝ m (Y ω)
  let c := fun ω => inner ℝ (X ω) (Y ω)
  have hXi : Integrable X ν := (hXL.mono_exponent (show 1 ≤ ∞ from le_top)).integrable le_rfl
  have hYi : Integrable Y ν := (hYL.mono_exponent (show 1 ≤ ∞ from le_top)).integrable le_rfl
  have haL : MemLp a ∞ ν := hXL.const_inner m
  have hbL : MemLp b ∞ ν := hYL.const_inner m
  have hab : (∫ ω, a ω*b ω ∂ν) = 0 := by
    have hi : IndepFun a b ν := hind.comp (by fun_prop) (by fun_prop)
    have h := hi.integral_fun_mul_eq_mul_integral haL.aestronglyMeasurable hbL.aestronglyMeasurable
    dsimp [a, b] at h ⊢
    rw [h, integral_inner hXi, integral_inner hYi, hXm, hYm]
    simp
  have hac : (∫ ω, a ω*c ω ∂ν) = 0 := by
    have hi : Integrable (fun ω => a ω • X ω) ν :=
      ((hXL.smul haL).mono_exponent (show 1 ≤ ∞ from le_top)).integrable le_rfl
    have h := (hind.comp (by fun_prop : Measurable (fun x => inner ℝ m x • x))
      measurable_id).integral_bilin hi hYi (innerSL ℝ)
    change (∫ ω, inner ℝ (a ω • X ω) (Y ω) ∂ν) =
      inner ℝ (∫ ω, a ω • X ω ∂ν) (∫ ω, Y ω ∂ν) at h
    simpa [inner_smul_left, hYm, c] using h
  have hbc : (∫ ω, b ω*c ω ∂ν) = 0 := by
    have hi : Integrable (fun ω => b ω • Y ω) ν :=
      ((hYL.smul hbL).mono_exponent (show 1 ≤ ∞ from le_top)).integrable le_rfl
    have h := (hind.comp measurable_id
      (by fun_prop : Measurable (fun y => inner ℝ m y • y))).integral_bilin hXi hi (innerSL ℝ)
    change (∫ ω, inner ℝ (X ω) (b ω • Y ω) ∂ν) =
      inner ℝ (∫ ω, X ω ∂ν) (∫ ω, b ω • Y ω ∂ν) at h
    simpa [inner_smul_right, hXm, c] using h
  have hcL : MemLp c 2 ν := by
    apply (memLp_two_iff_integrable_sq (by dsimp [c]; fun_prop)).mpr
    exact Causalean.Stat.Concentration.integrable_indep_inner_sq ν X Y hX hY
      (hXL.mono_exponent le_top) (hYL.mono_exponent le_top) hind
  have ha2 : MemLp a 2 ν := haL.mono_exponent le_top
  have hb2 : MemLp b 2 ν := hbL.mono_exponent le_top
  have he : (∫ ω, (a ω+b ω+c ω)^2 ∂ν) =
      (∫ ω, a ω^2 ∂ν)+(∫ ω, b ω^2 ∂ν)+(∫ ω, c ω^2 ∂ν) := by
    have hp : (fun ω => (a ω+b ω+c ω)^2) = fun ω =>
        (a ω^2+b ω^2+c ω^2)+2*(a ω*b ω)+2*(a ω*c ω)+2*(b ω*c ω) := by
      funext ω; ring
    have hs := (ha2.integrable_sq.add hb2.integrable_sq).add hcL.integrable_sq
    have hiab := (ha2.integrable_mul hb2).const_mul 2
    have hiac := (ha2.integrable_mul hcL).const_mul 2
    have hibc := (hb2.integrable_mul hcL).const_mul 2
    simp only [Pi.add_apply, Pi.mul_apply] at hs hiab hiac hibc
    rw [hp]
    rw [integral_add, integral_add, integral_add, integral_add, integral_add]
    · simp only [integral_const_mul, hab, hac, hbc]; ring
    all_goals first
      | exact ha2.integrable_sq
      | exact hb2.integrable_sq
      | exact hcL.integrable_sq
      | exact hs
      | exact hiab
      | exact hiac
      | exact hibc
      | exact ha2.integrable_sq.add hb2.integrable_sq
      | exact hs.add hiab
      | exact (hs.add hiab).add hiac
  change (∫ ω, (a ω+b ω+c ω)^2 ∂ν) ≤ _
  rw [he]
  have hc := Causalean.Stat.Concentration.indep_inner_sq_integral_le ν X Y Λ hX hY
    (hXL.mono_exponent le_top) (hYL.mono_exponent le_top) hind hXmom hYmom
  have ha := hXmom m
  have hb := hYmom m
  dsimp [a, b, c] at *
  linarith

end CausalSmith.Stat.FinitepHomogeneityDensegamma
