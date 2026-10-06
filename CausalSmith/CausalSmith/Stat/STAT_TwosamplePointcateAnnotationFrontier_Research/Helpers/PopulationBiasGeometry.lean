module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationCausalEntries
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationGram
public import Causalean.Mathlib.Probability.SteinMethod.DependencyCLT

/-! # Population bias projection geometry
Finite orthonormal expansions give the bilinear projection identity and the
orthogonality cancellation used in the population-bias roadmap. The causal
response and Gram action give the exact bias identity; projection contraction
and Cauchy–Schwarz give its coordinate and Euclidean bounds.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- A finite orthonormal projection preserves square integrability.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the population projection mem lp conclusion](goal) holds. -/
lemma population_projection_memLp (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (f : Cov d → ℝ) (hf : MemLp f 2 (locLaw d h)) :
    MemLp (projOp d h J f) 2 (locLaw d h) := by
  have he : projOp d h J f = fun x => ∑ z : FineIdx d J, fineBasis h J x z *
      (∫ y, fineBasis h J y z*f y ∂locLaw d h) :=
    funext (projection_finite_expansion d h J hh hh' hJ f hf)
  rw [he]
  exact memLp_finsetSum _ (fun z _ => (fineBasis_memLp d h J hh hh' hJ z).mul_const _)

/-- Orthogonal projection preserves each fine-basis coefficient.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input z](hyp:z), [the population projection coefficient conclusion](goal) holds. -/
lemma population_projection_coefficient (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (f : Cov d → ℝ) (hf : MemLp f 2 (locLaw d h)) (z : FineIdx d J) :
    (∫ x, fineBasis h J x z * projOp d h J f x ∂locLaw d h) =
      ∫ x, fineBasis h J x z*f x ∂locLaw d h := by
  classical
  simp_rw [projection_finite_expansion d h J hh hh' hJ f hf, Finset.mul_sum,
    ← mul_assoc]
  rw [integral_finsetSum (f := fun w x =>
    (fineBasis h J x z*fineBasis h J x w)*(∫ y, fineBasis h J y w*f y ∂locLaw d h))
    Finset.univ (fun w _ =>
      ((fineBasis_memLp d h J hh hh' hJ z).integrable_mul
        (fineBasis_memLp d h J hh hh' hJ w)).mul_const _)]
  simp_rw [integral_mul_const, fine_orthonormal d h J hh hh' hJ]
  simp

/-- Pairing a projected function with any square-integrable function is the finite coefficient inner product.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the population projection inner conclusion](goal) holds. -/
lemma population_projection_inner (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (f g : Cov d → ℝ) (hf : MemLp f 2 (locLaw d h)) (hg : MemLp g 2 (locLaw d h)) :
    (∫ x, projOp d h J f x*g x ∂locLaw d h) =
      ∑ z : FineIdx d J,
        (∫ x, fineBasis h J x z*f x ∂locLaw d h)*
        (∫ x, fineBasis h J x z*g x ∂locLaw d h) := by
  simp_rw [projection_finite_expansion d h J hh hh' hJ f hf, Finset.sum_mul]
  simp_rw [show ∀ (z : FineIdx d J) x,
    fineBasis h J x z*(∫ y, fineBasis h J y z*f y ∂locLaw d h)*g x =
      (fineBasis h J x z*g x)*(∫ y, fineBasis h J y z*f y ∂locLaw d h) by intros; ring]
  rw [integral_finsetSum (f := fun z x =>
    (fineBasis h J x z*g x)*(∫ y, fineBasis h J y z*f y ∂locLaw d h))
    Finset.univ (fun z _ =>
      ((fineBasis_memLp d h J hh hh' hJ z).integrable_mul hg).mul_const _)]
  simp_rw [integral_mul_const]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- A control-mean residual pairs only with the residual of the propensity feature.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the population residual inner identity conclusion](goal) holds. -/
lemma population_residual_inner_identity (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (f g : Cov d → ℝ) (hf : MemLp f 2 (locLaw d h)) (hg : MemLp g 2 (locLaw d h)) :
    (∫ x, f x*(g x-projOp d h J g x) ∂locLaw d h) =
      ∫ x, (f x-projOp d h J f x)*(g x-projOp d h J g x) ∂locLaw d h := by
  have hpf := population_projection_memLp d h J hh hh' hJ f hf
  have hpg := population_projection_memLp d h J hh hh' hJ g hg
  have hc : (∫ x, projOp d h J f x*(g x-projOp d h J g x) ∂locLaw d h) = 0 := by
    simp_rw [mul_sub]
    rw [integral_sub
      (show Integrable (fun x => projOp d h J f x*g x) (locLaw d h) from hpf.integrable_mul hg)
      (show Integrable (fun x => projOp d h J f x*projOp d h J g x) (locLaw d h) from hpf.integrable_mul hpg),
      population_projection_inner d h J hh hh' hJ f g hf hg,
      population_projection_inner d h J hh hh' hJ f _ hf hpg]
    simp_rw [population_projection_coefficient d h J hh hh' hJ g hg]
    exact sub_self _
  simp_rw [sub_mul]
  rw [integral_sub
    (show Integrable (fun x => f x*(g x-projOp d h J g x)) (locLaw d h) from hf.integrable_mul (hg.sub hpg))
    (show Integrable (fun x => projOp d h J f x*(g x-projOp d h J g x)) (locLaw d h) from hpf.integrable_mul (hg.sub hpg)), hc,
    sub_zero]

/-- Applying the population Gram matrix to polynomial coefficients gives the
localized bilinear projection formula.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input theta](hyp:theta), [the specified input u](hyp:u), [the population gram action conclusion](goal) holds. -/
lemma population_gram_action {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (n m : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (J : ℕ) (hJ : 1 ≤ J) (theta : PolyIdx d → ℝ) (u : PolyIdx d) :
    ((qPop P n m h J).mulVec theta) u =
      (∫ x, coarseBasis h x u * (designatedPropensity P hP x * pv h theta x) ∂locLaw d h) -
      ∑ z : FineIdx d J,
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x u) ∂locLaw d h) *
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * pv h theta x) ∂locLaw d h) := by
  classical
  have hfirst : (∫ x, coarseBasis h x u * (designatedPropensity P hP x * pv h theta x) ∂locLaw d h) =
      ∑ v, (∫ x, coarseBasis h x u * (designatedPropensity P hP x * coarseBasis h x v) ∂locLaw d h) * theta v := by
    simp only [pv, Finset.mul_sum]
    simp_rw [← mul_assoc]
    rw [integral_finsetSum (f := fun v x =>
      coarseBasis h x u * designatedPropensity P hP x * coarseBasis h x v * theta v)
      Finset.univ (fun v _ => (show Integrable (fun x =>
        coarseBasis h x u * designatedPropensity P hP x * coarseBasis h x v) (locLaw d h) by
          convert (coarseBasis_memLp d h hh hh' u).integrable_mul
            (designatedPropensity_mul_memLp P hP h hh' _ (coarseBasis_memLp d h hh hh' v)) using 1
          ext x; simp only [Pi.mul_apply]; ring).mul_const _)]
    simp_rw [integral_mul_const]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [population_gram_entries P hP n m hn h hh hh' J hJ,
    sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hfirst, Finset.sum_comm]
  simp_rw [weighted_pv_projection_coefficient P hP h hh hh' J hJ theta, Finset.mul_sum, mul_assoc]

/-- For [a primitive law P](hyp:P) [in the model class](hyp:hP) at [overlap level eps](hyp:eps), [the designated treated mean is Borel](goal). -/
@[fun_prop] lemma measurable_designatedTreated {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) :
    Measurable (designatedTreated P hP) := by
  unfold designatedTreated
  have hc : MeasurableSet (cube d) := by
    unfold cube
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_Icc.preimage (by fun_prop)
  exact Measurable.ite hc (canonicalLaw P hP).measurable_mu1 measurable_const

/-- For [a primitive law P](hyp:P) [in the model class](hyp:hP) at [overlap level eps](hyp:eps), [the canonical treatment contrast is Borel](goal). -/
@[fun_prop] lemma measurable_tau {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) :
    Measurable (tau P hP) := by
  unfold tau
  fun_prop

/-- Interior arm means give square-integrable designated means and contrast.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the population causal mem lp conclusion](goal) holds. -/
lemma population_causal_memLp {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2) :
    MemLp (designatedControl P hP) 2 (locLaw d h) ∧
      MemLp (designatedTreated P hP) 2 (locLaw d h) ∧
      MemLp (tau P hP) 2 (locLaw d h) := by
  letI := localization_probability d h hh hh'
  have hae : ∀ᵐ x ∂locLaw d h, x ∈ locCube d h := by
    unfold locLaw
    apply Measure.ae_smul_measure
    exact ae_restrict_mem (isClosed_locCube d h).measurableSet
  have hs := canonicalLaw_spec P hP
  have hmu : MemLp (designatedControl P hP) 2 (locLaw d h) := by
    apply (memLp_top_of_bound (by fun_prop) 1 ?_).mono_exponent (by simp)
    filter_upwards [hae] with x hx
    have hc := locCube_subset_cube d h hh' hx
    have hi := hs.2.2.2.2.2.2.2.1 x hc
    simp only [designatedControl, if_pos hc, Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩)
  have ht : MemLp (designatedTreated P hP) 2 (locLaw d h) := by
    apply (memLp_top_of_bound (by fun_prop) 1 ?_).mono_exponent (by simp)
    filter_upwards [hae] with x hx
    have hc := locCube_subset_cube d h hh' hx
    have hi := hs.2.2.2.2.2.2.2.2 x hc
    simp only [designatedTreated, if_pos hc, Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩)
  exact ⟨hmu, ht, ht.sub hmu⟩

/-- Subtracting the population Gram action cancels the control mean except
for its orthogonal projection residual.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input theta](hyp:theta), [the specified input u](hyp:u), [the population bias coordinate identity conclusion](goal) holds. -/
lemma population_bias_coordinate_identity {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (n m : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (J : ℕ) (hJ : 1 ≤ J) (theta : PolyIdx d → ℝ) (u : PolyIdx d) :
    rBar P n m h J u - ((qPop P n m h J).mulVec theta) u =
      (∫ x, (designatedPropensity P hP x * coarseBasis h x u -
        projOp d h J (fun y => designatedPropensity P hP y * coarseBasis h y u) x) *
        (designatedControl P hP x - projOp d h J (designatedControl P hP) x) ∂locLaw d h) +
      (∫ x, coarseBasis h x u * (designatedPropensity P hP x * (tau P hP x - pv h theta x)) ∂locLaw d h) -
      (∫ x, projOp d h J (fun y => designatedPropensity P hP y * coarseBasis h y u) x *
        (designatedPropensity P hP x * (tau P hP x - pv h theta x)) ∂locLaw d h) := by
  classical
  let e := designatedPropensity P hP
  let mu := designatedControl P hP
  let g := fun x => tau P hP x - pv h theta x
  let f := fun x => e x * coarseBasis h x u
  have hmu := (population_causal_memLp P hP h hh hh').1
  have htreated := (population_causal_memLp P hP h hh hh').2.1
  have htau := (population_causal_memLp P hP h hh hh').2.2
  have hp := pv_memLp d h hh hh' theta
  have heg := designatedPropensity_mul_memLp P hP h hh' g (htau.sub hp)
  have hep := designatedPropensity_mul_memLp P hP h hh' _ hp
  have hf := designatedPropensity_mul_memLp P hP h hh' _ (coarseBasis_memLp d h hh hh' u)
  have hr := coarseBasis_memLp d h hh hh' u
  have hfst :
      (∫ x, coarseBasis h x u * e x * designatedTreated P hP x ∂locLaw d h) -
      (∫ x, coarseBasis h x u * (e x * pv h theta x) ∂locLaw d h) =
      (∫ x, f x * mu x ∂locLaw d h) +
      (∫ x, coarseBasis h x u * (e x * g x) ∂locLaw d h) := by
    rw [← integral_sub (by convert hf.integrable_mul htreated using 1; ext x; simp only [f, e, Pi.mul_apply]; ring)
      (show Integrable (fun x => coarseBasis h x u * (e x * pv h theta x)) (locLaw d h) from hr.integrable_mul hep),
      ← integral_add (show Integrable (fun x => f x * mu x) (locLaw d h) from hf.integrable_mul hmu)
        (show Integrable (fun x => coarseBasis h x u * (e x * g x)) (locLaw d h) from hr.integrable_mul heg)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [f, g, e, tau]
    ring
  have hcoef (z : FineIdx d J) :
      (∫ x, fineBasis h J x z * (mu x + e x * tau P hP x) ∂locLaw d h) -
      (∫ x, fineBasis h J x z * (e x * pv h theta x) ∂locLaw d h) =
      (∫ x, fineBasis h J x z * mu x ∂locLaw d h) +
      (∫ x, fineBasis h J x z * (e x * g x) ∂locLaw d h) := by
    have hb := fineBasis_memLp d h J hh hh' hJ z
    have het := designatedPropensity_mul_memLp P hP h hh' _ htau
    rw [← integral_sub (show Integrable (fun x => fineBasis h J x z * (mu x + e x * tau P hP x)) (locLaw d h) from hb.integrable_mul (hmu.add het))
      (show Integrable (fun x => fineBasis h J x z * (e x * pv h theta x)) (locLaw d h) from hb.integrable_mul hep),
      ← integral_add (show Integrable (fun x => fineBasis h J x z * mu x) (locLaw d h) from hb.integrable_mul hmu)
        (show Integrable (fun x => fineBasis h J x z * (e x * g x)) (locLaw d h) from hb.integrable_mul heg)]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [g]
    ring
  rw [population_response_causal_entries P hP n m hn h hh hh' J hJ u,
    population_gram_action P hP n m hn h hh hh' J hJ theta u]
  change (_ - ∑ z, _ * (∫ x, fineBasis h J x z * (mu x + e x * tau P hP x) ∂locLaw d h)) -
    (_ - ∑ z, _ * (∫ x, fineBasis h J x z * (e x * pv h theta x) ∂locLaw d h)) = _
  rw [show ∀ (a b c D : ℝ), (a-b)-(c-D) = (a-c)-(b-D) by intros; ring,
    hfst, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, hcoef, mul_add, Finset.sum_add_distrib]
  rw [← population_projection_inner d h J hh hh' hJ f mu hf hmu,
    ← population_projection_inner d h J hh hh' hJ f (fun x => e x * g x) hf heg]
  have hres := population_residual_inner_identity d h J hh hh' hJ f mu hf hmu
  have hpg := population_projection_memLp d h J hh hh' hJ mu hmu
  have hself : (∫ x, projOp d h J f x * mu x ∂locLaw d h) =
      ∫ x, f x * projOp d h J mu x ∂locLaw d h := by
    rw [population_projection_inner d h J hh hh' hJ f mu hf hmu]
    simp_rw [mul_comm (f _) (projOp d h J mu _)]
    rw [population_projection_inner d h J hh hh' hJ mu f hmu hf]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have hres' : (∫ x, f x * mu x ∂locLaw d h) -
      (∫ x, projOp d h J f x * mu x ∂locLaw d h) =
      ∫ x, (f x - projOp d h J f x) * (mu x - projOp d h J mu x) ∂locLaw d h := by
    rw [hself, ← integral_sub (show Integrable (fun x => f x * mu x) (locLaw d h) from hf.integrable_mul hmu)
      (show Integrable (fun x => f x * projOp d h J mu x) (locLaw d h) from hf.integrable_mul hpg)]
    simp_rw [← mul_sub]
    exact hres
  dsimp only [f, g, e, mu] at hres' ⊢
  linarith [hres']

/-- Projection contraction and overlap control the two Taylor-error pairings;
Cauchy–Schwarz controls the product of the two nuisance residuals.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input theta](hyp:theta), [the specified input C](hyp:C), [the specified input hC](hyp:hC), [the specified input herr](hyp:herr), [the specified input he](hyp:he), [the specified input hmu](hyp:hmu), [the specified input u](hyp:u), [the population bias coordinate bound conclusion](goal) holds. -/
lemma population_bias_coordinate_bound {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (n m : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (J : ℕ) (hJ : 1 ≤ J) (theta : PolyIdx d → ℝ) (C : ℝ) (hC : 0 < C)
    (herr : ∀ x ∈ locCube d h, |tau P hP x - pv h theta x| ≤ C*h^gamma)
    (he : ∀ u : PolyIdx d, Real.sqrt (∫ x,
      (designatedPropensity P hP x * coarseBasis h x u -
        projOp d h J (fun y => designatedPropensity P hP y * coarseBasis h y u) x)^2 ∂locLaw d h) ≤ C*(h/J)^alpha)
    (hmu : Real.sqrt (∫ x,
      (designatedControl P hP x - projOp d h J (designatedControl P hP) x)^2 ∂locLaw d h) ≤ C*(h/J)^beta)
    (u : PolyIdx d) :
    |rBar P n m h J u - ((qPop P n m h J).mulVec theta) u| ≤
      (C^2+2*C)*(h^gamma+(h/J)^(alpha+beta)) := by
  letI := localization_probability d h hh hh'
  let e := designatedPropensity P hP
  let mu := designatedControl P hP
  let g := fun x => tau P hP x - pv h theta x
  let f := fun x => e x * coarseBasis h x u
  have hr := coarseBasis_memLp d h hh hh' u
  have hf := designatedPropensity_mul_memLp P hP h hh' _ hr
  have hm := (population_causal_memLp P hP h hh hh').1
  have hg := (population_causal_memLp P hP h hh hh').2.2.sub (pv_memLp d h hh hh' theta)
  have heg := designatedPropensity_mul_memLp P hP h hh' _ hg
  have hpf := population_projection_memLp d h J hh hh' hJ f hf
  have hpm := population_projection_memLp d h J hh hh' hJ mu hm
  have hae : ∀ᵐ x ∂locLaw d h, x ∈ locCube d h := by
    unfold locLaw
    apply Measure.ae_smul_measure
    exact ae_restrict_mem (isClosed_locCube d h).measurableSet
  have hover := designatedPropensity_overlap_locLaw P hP h hh'
  have hepsP := hP.eps_pos
  have hrootr : Real.sqrt (∫ x, (coarseBasis h x u)^2 ∂locLaw d h) = 1 := by
    have ho := coarse_orthonormal d h hh hh' u u
    simpa only [← pow_two, ite_true, ho, Real.sqrt_one] using congrArg Real.sqrt ho
  have hfsq : (∫ x, (f x)^2 ∂locLaw d h) ≤ 1 := by
    have ho : (∫ x, (coarseBasis h x u)^2 ∂locLaw d h) = 1 := by
      simpa only [← pow_two, ite_true] using coarse_orthonormal d h hh hh' u u
    rw [← ho]
    apply integral_mono_ae hf.integrable_sq hr.integrable_sq
    filter_upwards [hover] with x hx
    change (designatedPropensity P hP x * coarseBasis h x u)^2 ≤ (coarseBasis h x u)^2
    have heabs : |designatedPropensity P hP x| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hle : |designatedPropensity P hP x * coarseBasis h x u| ≤ |coarseBasis h x u| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) heabs
    nlinarith [sq_abs (designatedPropensity P hP x * coarseBasis h x u), sq_abs (coarseBasis h x u), abs_nonneg (coarseBasis h x u), abs_nonneg (designatedPropensity P hP x * coarseBasis h x u)]
  have hpfroot : Real.sqrt (∫ x, (projOp d h J f x)^2 ∂locLaw d h) ≤ 1 := by
    have hpy := projection_pythagoras d h J hh hh' hJ f hf
    have hres : 0 ≤ ∫ x, (f x - projOp d h J f x)^2 ∂locLaw d h := integral_nonneg (fun _ => sq_nonneg _)
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith
  have hnonneg : 0 ≤ C*h^gamma := mul_nonneg hC.le (Real.rpow_nonneg hh.le _)
  have hegsq : (∫ x, (e x * g x)^2 ∂locLaw d h) ≤ (C*h^gamma)^2 := by
    calc
      _ ≤ ∫ _x : Cov d, (C*h^gamma)^2 ∂locLaw d h := by
        apply integral_mono_ae heg.integrable_sq (integrable_const _)
        filter_upwards [hae, hover] with x hx hov
        have heabs : |e x| ≤ 1 := abs_le.mpr ⟨by dsimp [e]; linarith [hov.1], by dsimp [e]; linarith [hov.2]⟩
        have hle : |e x * g x| ≤ C*h^gamma := by
          rw [abs_mul]
          exact (mul_le_of_le_one_left (abs_nonneg _) heabs).trans (herr x hx)
        change (e x * g x)^2 ≤ (C*h^gamma)^2
        nlinarith [sq_abs (e x * g x), abs_nonneg (e x * g x)]
      _ = (C*h^gamma)^2 := by simp
  have hegroot : Real.sqrt (∫ x, (e x * g x)^2 ∂locLaw d h) ≤ C*h^gamma :=
    (Real.sqrt_le_iff).2 ⟨hnonneg, hegsq⟩
  have hbias : |∫ x, (f x-projOp d h J f x)*(mu x-projOp d h J mu x) ∂locLaw d h| ≤
      C^2*(h/J)^(alpha+beta) := by
    calc
      _ ≤ Real.sqrt (∫ x, (f x-projOp d h J f x)^2 ∂locLaw d h) *
        Real.sqrt (∫ x, (mu x-projOp d h J mu x)^2 ∂locLaw d h) :=
        Causalean.Mathlib.Probability.SteinMethod.abs_integral_mul_le_sqrt _ _ (hf.sub hpf) (hm.sub hpm)
      _ ≤ (C*(h/J)^alpha)*(C*(h/J)^beta) :=
        mul_le_mul (he u) hmu (Real.sqrt_nonneg _) (by positivity)
      _ = C^2*(h/J)^(alpha+beta) := by
        rw [Real.rpow_add (div_pos hh (by exact_mod_cast hJ))]
        ring
  have hterm1 : |∫ x, coarseBasis h x u*(e x*g x) ∂locLaw d h| ≤ C*h^gamma := by
    have hc := Causalean.Mathlib.Probability.SteinMethod.abs_integral_mul_le_sqrt _ _ hr heg
    rw [hrootr, one_mul] at hc
    exact hc.trans hegroot
  have hterm2 : |∫ x, projOp d h J f x*(e x*g x) ∂locLaw d h| ≤ C*h^gamma := by
    calc
      _ ≤ Real.sqrt (∫ x, (projOp d h J f x)^2 ∂locLaw d h) *
        Real.sqrt (∫ x, (e x*g x)^2 ∂locLaw d h) :=
        Causalean.Mathlib.Probability.SteinMethod.abs_integral_mul_le_sqrt _ _ hpf heg
      _ ≤ 1*(C*h^gamma) := mul_le_mul hpfroot hegroot (Real.sqrt_nonneg _) zero_le_one
      _ = _ := one_mul _
  rw [population_bias_coordinate_identity P hP n m hn h hh hh' J hJ theta u]
  calc
    _ ≤ |∫ x, (f x-projOp d h J f x)*(mu x-projOp d h J mu x) ∂locLaw d h| +
        |∫ x, coarseBasis h x u*(e x*g x) ∂locLaw d h| +
        |∫ x, projOp d h J f x*(e x*g x) ∂locLaw d h| := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C^2*(h/J)^(alpha+beta) + C*h^gamma + C*h^gamma :=
      add_le_add (add_le_add hbias hterm1) hterm2
    _ ≤ (C^2+2*C)*(h^gamma+(h/J)^(alpha+beta)) := by
      have ha : 0 ≤ h^gamma := Real.rpow_nonneg hh.le _
      have hb : 0 ≤ (h/(J:ℝ))^(alpha+beta) := Real.rpow_nonneg (by positivity) _
      nlinarith [sq_nonneg C, mul_nonneg (sq_nonneg C) ha, mul_nonneg hC.le hb]

/-- Coordinatewise absolute bounds imply the Euclidean bound in fixed dimension.  Given [the specified input v](hyp:v), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hv](hyp:hv), [the population finite norm bound conclusion](goal) holds. -/
lemma population_finite_norm_bound {ι : Type*} [Fintype ι] (v : ι → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hv : ∀ i, |v i| ≤ B) :
    Real.sqrt (∑ i, (v i)^2) ≤ Real.sqrt (Fintype.card ι)*B := by
  have hs : (∑ i, (v i)^2) ≤ (Fintype.card ι : ℝ)*B^2 := by
    calc
      _ ≤ ∑ _i : ι, B^2 := Finset.sum_le_sum (fun i _ => by
        nlinarith [hv i, sq_abs (v i), abs_nonneg (v i)])
      _ = _ := by simp
  calc
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ)*B^2) := Real.sqrt_le_sqrt hs
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB]

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
