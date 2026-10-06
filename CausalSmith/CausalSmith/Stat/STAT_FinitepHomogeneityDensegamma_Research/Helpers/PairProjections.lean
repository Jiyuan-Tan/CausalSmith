module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Scores
public import Causalean.Stat.UStatistic.LocalizedVariance.Coordinates
public import Causalean.Stat.UStatistic.LocalizedVariance.Mean
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! Finite-moment homogeneity testing: Helpers/PairVariance. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


variable {Ω : Type*} [MeasurableSpace Ω]
/-- Integrate the pair kernel under two independent draws. This statement assumes [the P parameter](hyp:P), [the g parameter](hyp:g). [This is the stated defined object](goal). -/
def pairMean (P : Measure Ω) (g : Ω → Ω → ℝ) : ℝ := ∫ z : Ω × Ω, g z.1 z.2 ∂P.prod P
/-- Subtract the pair mean from the kernel average over its second draw. This statement assumes [the P parameter](hyp:P), [the g parameter](hyp:g), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def singletonProjection (P : Measure Ω) (g : Ω → Ω → ℝ) (x : Ω) : ℝ := (∫ y, g x y ∂P)-pairMean P g
/-- Remove the mean and both singleton projections from the pair kernel. This statement assumes [the P parameter](hyp:P), [the g parameter](hyp:g), [the x parameter](hyp:x), [the y parameter](hyp:y). [This is the stated defined object](goal). -/
def canonicalProjection (P : Measure Ω) (g : Ω → Ω → ℝ) (x y : Ω) : ℝ :=
  g x y-pairMean P g-singletonProjection P g x-singletonProjection P g y
/-- Average the kernel over every ordered distinct pair in a finite sample. This statement assumes [the s parameter](hyp:s), [the g parameter](hyp:g), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def orderedPairAverage (s : ℕ) (g : Ω → Ω → ℝ) (data : Fin s → Ω) : ℝ :=
  ((s:ℝ)*((s:ℝ)-1))⁻¹*∑ i : Fin s, ∑ j ∈ Finset.univ.erase i, g (data i) (data j)
/-- The conditional kernel mean is square integrable by the nonnegativity of slice variances. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
-- @node: pair_conditional_mean_memLp
lemma pair_conditional_mean_memLp (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P)) :
    MemLp (fun x => ∫ y, g x y ∂P) 2 P := by
  have hm : StronglyMeasurable (fun x => ∫ y, g x y ∂P) :=
    hg.stronglyMeasurable.integral_prod_right
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply hL2.integrable_sq.integral_prod_left.mono' (hm.pow 2).aestronglyMeasurable
  filter_upwards [hL2.integrable_sq.prod_right_ae] with x hx
  have hmx : MemLp (fun y => g x y) 2 P :=
    (memLp_two_iff_integrable_sq
      (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hx
  have hv := variance_nonneg (fun y => g x y) P
  rw [variance_eq_sub hmx] at hv
  simp only [Pi.pow_apply] at hv
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.pow_apply]
  linarith

/-- The centered singleton projection inherits the conditional mean's second moment. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
-- @node: singletonProjection_memLp
lemma singletonProjection_memLp (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P)) :
    MemLp (singletonProjection P g) 2 P :=
  (pair_conditional_mean_memLp P g hg hL2).sub (memLp_const _)

/-- The singleton projection has zero mean under the original record law. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
-- @node: singletonProjection_integral_zero
lemma singletonProjection_integral_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P)) :
    (∫ x, singletonProjection P g x ∂P) = 0 := by
  unfold singletonProjection
  rw [integral_sub
    (hL2.integrable (by norm_num)).integral_prod_left (integrable_const _)]
  rw [← integral_prod _ (hL2.integrable (by norm_num))]
  simp [pairMean]

/-- Removing the two singleton projections preserves square integrability of the kernel. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
-- @node: canonicalProjection_memLp
lemma canonicalProjection_memLp (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P)) :
    MemLp (fun z : Ω × Ω => canonicalProjection P g z.1 z.2) 2 (P.prod P) := by
  have h1 := singletonProjection_memLp P g hg hL2
  exact ((hL2.sub (memLp_const _)).sub (h1.comp_fst P)).sub (h1.comp_snd P)

/-- Conditional integration of the canonical projection vanishes almost everywhere. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
-- @node: canonicalProjection_integral_zero
lemma canonicalProjection_integral_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P)) :
    ∀ᵐ x ∂P, (∫ y, canonicalProjection P g x y ∂P) = 0 := by
  have h1 := (singletonProjection_memLp P g hg hL2).integrable (by norm_num)
  filter_upwards [(hL2.integrable (by norm_num)).prod_right_ae] with x hx
  unfold canonicalProjection
  integral_linearity
  rw [singletonProjection_integral_zero P g hg hL2]
  simp [singletonProjection]

/-- A symmetric kernel has a symmetric canonical residual. This statement assumes [the hsym condition](hyp:hsym). [This is the stated conclusion](goal). -/
-- @node: canonicalProjection_symmetric
lemma canonicalProjection_symmetric (P : Measure Ω) (g : Ω → Ω → ℝ)
    (hsym : ∀ x y, g x y = g y x) (x y : Ω) :
    canonicalProjection P g x y = canonicalProjection P g y x := by
  simp only [canonicalProjection, hsym x y]
  ring

/-- The canonical residual is orthogonal to every square-integrable function of its first record. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: canonicalProjection_orthogonal_first
lemma canonicalProjection_orthogonal_first (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    (f : Ω → ℝ) (hf : MemLp f 2 P) :
    (∫ z : Ω × Ω, f z.1*canonicalProjection P g z.1 z.2 ∂P.prod P) = 0 := by
  have hi : Integrable (fun z : Ω × Ω => f z.1*canonicalProjection P g z.1 z.2)
      (P.prod P) := (hf.comp_fst P).integrable_mul (canonicalProjection_memLp P g hg hL2)
  rw [integral_prod _ hi]
  calc
    _ = ∫ x, f x*0 ∂P := by
      apply integral_congr_ae
      filter_upwards [canonicalProjection_integral_zero P g hg hL2] with x hx
      rw [integral_const_mul, hx]
    _ = 0 := by simp

/-- Symmetry also makes the canonical residual orthogonal to functions of the second record. This statement assumes [the hg condition](hyp:hg), [the hsym condition](hyp:hsym), [the hL2 condition](hyp:hL2), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: canonicalProjection_orthogonal_second
lemma canonicalProjection_orthogonal_second (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hsym : ∀ x y, g x y = g y x)
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P))
    (f : Ω → ℝ) (hf : MemLp f 2 P) :
    (∫ z : Ω × Ω, f z.2*canonicalProjection P g z.1 z.2 ∂P.prod P) = 0 := by
  rw [← integral_prod_swap]
  change (∫ z : Ω × Ω, f z.1*canonicalProjection P g z.2 z.1 ∂P.prod P) = 0
  have he : (fun z : Ω × Ω => f z.1*canonicalProjection P g z.2 z.1) =
      (fun z : Ω × Ω => f z.1*canonicalProjection P g z.1 z.2) := by
    funext z
    rw [canonicalProjection_symmetric P g hsym z.2 z.1]
  rw [he]
  exact canonicalProjection_orthogonal_first P g hg hL2 f hf

/-- The pair kernel's energy splits into its mean, two singleton energies, and canonical energy. This statement assumes [the hg condition](hyp:hg), [the hsym condition](hyp:hsym), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
-- @node: hoeffding_pair_energy
lemma hoeffding_pair_energy (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hsym : ∀ x y, g x y = g y x)
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P)) :
    (∫ z : Ω × Ω, g z.1 z.2^2 ∂P.prod P) = pairMean P g^2+
      2*(∫ x, singletonProjection P g x^2 ∂P)+
      (∫ z : Ω × Ω, canonicalProjection P g z.1 z.2^2 ∂P.prod P) := by
  let m := pairMean P g
  let p := singletonProjection P g
  let k := fun z : Ω × Ω => canonicalProjection P g z.1 z.2
  have hp : MemLp p 2 P := singletonProjection_memLp P g hg hL2
  have hk : MemLp k 2 (P.prod P) := canonicalProjection_memLp P g hg hL2
  have hpx : MemLp (fun z : Ω × Ω => p z.1) 2 (P.prod P) := hp.comp_fst P
  have hpy : MemLp (fun z : Ω × Ω => p z.2) 2 (P.prod P) := hp.comp_snd P
  have hpi : Integrable p P := hp.integrable (by norm_num)
  have hpxi : Integrable (fun z : Ω × Ω => p z.1) (P.prod P) := hpx.integrable (by norm_num)
  have hpyi : Integrable (fun z : Ω × Ω => p z.2) (P.prod P) := hpy.integrable (by norm_num)
  have hki : Integrable k (P.prod P) := hk.integrable (by norm_num)
  have hpxsq : Integrable (fun z : Ω × Ω => p z.1^2) (P.prod P) := hpx.integrable_sq
  have hpysq : Integrable (fun z : Ω × Ω => p z.2^2) (P.prod P) := hpy.integrable_sq
  have hksq : Integrable (fun z => k z^2) (P.prod P) := hk.integrable_sq
  have hxy : Integrable (fun z : Ω × Ω => p z.1*p z.2) (P.prod P) := hpx.integrable_mul hpy
  have hxk : Integrable (fun z : Ω × Ω => p z.1*k z) (P.prod P) := hpx.integrable_mul hk
  have hyk : Integrable (fun z : Ω × Ω => p z.2*k z) (P.prod P) := hpy.integrable_mul hk
  have hz : (∫ x, p x ∂P) = 0 := singletonProjection_integral_zero P g hg hL2
  have hzk : (∫ z, k z ∂P.prod P) = 0 := by
    simpa only [one_mul] using canonicalProjection_orthogonal_first P g hg hL2
      (fun _ => 1) (memLp_const 1)
  have hzxy : (∫ z : Ω × Ω, p z.1*p z.2 ∂P.prod P) = 0 := by
    rw [integral_prod_mul, hz, zero_mul]
  have hzxk : (∫ z : Ω × Ω, p z.1*k z ∂P.prod P) = 0 :=
    canonicalProjection_orthogonal_first P g hg hL2 p hp
  have hzyk : (∫ z : Ω × Ω, p z.2*k z ∂P.prod P) = 0 :=
    canonicalProjection_orthogonal_second P g hg hsym hL2 p hp
  have he (z : Ω × Ω) : g z.1 z.2^2 =
      m^2+p z.1^2+p z.2^2+k z^2+
      2*m*p z.1+2*m*p z.2+2*m*k z+
      2*(p z.1*p z.2)+2*(p z.1*k z)+2*(p z.2*k z) := by
    dsimp [m, p, k, canonicalProjection]
    ring
  have hmx := hpxi.const_mul (2*m)
  have hmy := hpyi.const_mul (2*m)
  have hmk := hki.const_mul (2*m)
  have hxy2 := hxy.const_mul 2
  have hxk2 := hxk.const_mul 2
  have hyk2 := hyk.const_mul 2
  have h0 := (integrable_const (μ := P.prod P) (m^2)).add hpxsq
  have h1 := h0.add hpysq
  have h2 := h1.add hksq
  have h3 := h2.add hmx
  have h4 := h3.add hmy
  have h5 := h4.add hmk
  have h6 := h5.add hxy2
  have h7 := h6.add hxk2
  simp_rw [he]
  integral_linearity
  rw [hzk, hzxy, hzxk, hzyk]
  simp only [integral_const, probReal_univ, one_smul, mul_zero, add_zero]
  rw [integral_prod _ hpxsq, integral_prod_symm _ hpysq,
    integral_prod _ hpxi, integral_prod_symm _ hpyi]
  simp only [integral_const, probReal_univ, one_smul, hz, mul_zero, add_zero]
  dsimp [m, p, k]
  ring

/-- Canonical projection cannot increase the pair kernel's second-moment energy. This statement assumes [the hg condition](hyp:hg), [the hsym condition](hyp:hsym), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
-- @node: canonicalProjection_energy_le
lemma canonicalProjection_energy_le (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → Ω → ℝ) (hg : Measurable (fun z : Ω × Ω => g z.1 z.2))
    (hsym : ∀ x y, g x y = g y x)
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P)) :
    (∫ z : Ω × Ω, canonicalProjection P g z.1 z.2^2 ∂P.prod P) ≤
      ∫ z : Ω × Ω, g z.1 z.2^2 ∂P.prod P := by
  rw [hoeffding_pair_energy P g hg hsym hL2]
  have hsingle : 0 ≤ ∫ x, singletonProjection P g x^2 ∂P :=
    integral_nonneg (fun _ => sq_nonneg _)
  nlinarith [sq_nonneg (pairMean P g)]

end CausalSmith.Stat.FinitepHomogeneityDensegamma
