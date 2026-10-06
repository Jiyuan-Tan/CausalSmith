module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CoordinateRegularity
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CoordinateVariance

/-! # Hölder approximation bounds for the coordinate biases

Cauchy–Schwarz for the uniform design converts the verified constant-five
projection approximation into residual-product bounds. Native-logit regularity
supplies the off-diagonal Hölder radii, giving the exact denominator constant.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [For continuous functions, the extended norm has the ordinary integral representation.](goal) Under [the stated assumptions](hyp:f,hf). -/
-- @node: uniformL2Norm_toReal
lemma uniformL2Norm_toReal (f : Covariate → ℝ) (hf : Continuous f) :
    (uniformL2Norm f).toReal = (∫ x, f x^2 ∂uniformLaw)^(1/2 : ℝ) := by
  have hi : Integrable (fun x => f x^2) uniformLaw :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [uniformL2Norm, ← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))]
  change ((ENNReal.ofReal (∫ x, f x^2 ∂uniformLaw)) ^ (1/2 : ℝ)).toReal = _
  rw [← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg (f x)))]

/-- [The real inner product is bounded by the product of the two finite L2 norms.](goal) Under [the stated assumptions](hyp:f,g,hf,hg). -/
-- @node: uniformInner_abs_le_L2
lemma uniformInner_abs_le_L2 (f g : Covariate → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    |uniformInner f g| ≤ (uniformL2Norm f).toReal*(uniformL2Norm g).toReal := by
  have hfm : MemLp f (ENNReal.ofReal 2) uniformLaw :=
    hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgm : MemLp g (ENNReal.ofReal 2) uniformLaw :=
    hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcs := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) (by constructor <;> norm_num) hfm hgm
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs] at hcs
  rw [uniformL2Norm_toReal f hf, uniformL2Norm_toReal g hg]
  exact (show |uniformInner f g| ≤ ∫ x, |f x| *|g x| ∂uniformLaw by
    simpa only [uniformInner, Real.norm_eq_abs, abs_mul] using
      norm_integral_le_integral_norm (fun x => f x*g x)).trans hcs

/-- [The finite projection of any function is continuous.](goal) Under [the stated assumptions](hyp:f). -/
-- @node: continuous_cosineProjection_function
lemma continuous_cosineProjection_function (k : ℕ) (f : Covariate → ℝ) :
    Continuous (cosineProjection k f) := by
  have hb (j : ℕ) : Continuous (cosineBasis j) := by
    unfold cosineBasis
    split_ifs <;> fun_prop
  unfold cosineProjection
  fun_prop

/-- [A real Hölder radius bounds the real L2 approximation error.](goal) Under [the stated assumptions](hyp:f,hγ,hf,hL,hH,hk). -/
-- @node: cosineProjection_error_real_bound
lemma cosineProjection_error_real_bound (γ L : ℝ) (f : Covariate → ℝ)
    (hγ : HolderExponentDomain γ) (hf : Continuous f) (hL : 0 ≤ L)
    (hH : holderSeminorm γ f ≤ ENNReal.ofReal L) (k : ℕ) (hk : 1 ≤ k) :
    (uniformL2Norm (fun x => f x-cosineProjection k f x)).toReal ≤
      5*L*(k : ℝ)^(-γ) := by
  have hb := cosineProjection_error_le_holderSeminorm γ f hγ hf k hk
  have hm : uniformL2Norm (fun x => f x-cosineProjection k f x) ≤
      5*ENNReal.ofReal L*ENNReal.ofReal ((k : ℝ)^(-γ)) :=
    hb.trans (by gcongr)
  have ht : 5*ENNReal.ofReal L*ENNReal.ofReal ((k : ℝ)^(-γ)) ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono ht hm
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hL, ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg k) _)] using hr

/-- [Two real Hölder radii give the product approximation bound with constant twenty-five.](goal) Under [the stated assumptions](hyp:f,g,hγ,hτ,hf,hg,hL,hM,hF,hG,hk). -/
-- @node: cosineProjection_residual_holder_bound
lemma cosineProjection_residual_holder_bound (γ τ L M : ℝ) (f g : Covariate → ℝ)
    (hγ : HolderExponentDomain γ) (hτ : HolderExponentDomain τ)
    (hf : Continuous f) (hg : Continuous g) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hF : holderSeminorm γ f ≤ ENNReal.ofReal L)
    (hG : holderSeminorm τ g ≤ ENNReal.ofReal M) (k : ℕ) (hk : 1 ≤ k) :
    |uniformInner (fun x => f x-cosineProjection k f x)
      (fun x => g x-cosineProjection k g x)| ≤ 25*L*M*(k : ℝ)^(-(γ+τ)) := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcs := uniformInner_abs_le_L2 _ _
    (hf.sub (continuous_cosineProjection_function k f))
    (hg.sub (continuous_cosineProjection_function k g))
  have hprod := mul_le_mul
    (cosineProjection_error_real_bound γ L f hγ hf hL hF k hk)
    (cosineProjection_error_real_bound τ M g hτ hg hM hG k hk)
    ENNReal.toReal_nonneg (by positivity : 0 ≤ 5*L*(k : ℝ)^(-γ))
  have he : (5*L*(k : ℝ)^(-γ))*(5*M*(k : ℝ)^(-τ)) =
      25*L*M*(k : ℝ)^(-(γ+τ)) := by
    rw [neg_add, Real.rpow_add hkp]
    ring
  exact hcs.trans (he ▸ hprod)

/-- [The off-diagonal residual has precisely the paper's constant twenty-five bound.](goal) Under [the stated assumptions](hyp:hab,hP,hk). -/
-- @node: denominator_projection_bias_bound
lemma denominator_projection_bias_bound (P : ObservedLaw) (α β : ℝ)
    (hab : ExponentDomain α β) (hP : Model α β P) (k : ℕ) (hk : 1 ≤ k) :
    |uniformInner
      (fun x => cellProbability P true false x-cosineProjection k (cellProbability P true false) x)
      (fun x => cellProbability P false true x-cosineProjection k (cellProbability P false true) x)| ≤
      25*(k : ℝ)^(-2*β) := by
  obtain ⟨hF, hG⟩ := offDiagonal_holder_bounds P α β hab hP
  have hcont (a y : Bool) : Continuous (cellProbability P a y) := by
    have he : cellProbability P a y = P.cells a y := funext (cellProbability_eq_cells P a y)
    rw [he]
    exact P.continuous_cells a y
  have hβ : HolderExponentDomain β := ⟨hab.1, by linarith [hab.2.1]⟩
  have h := cosineProjection_residual_holder_bound β β 1 1 _ _ hβ hβ
    (hcont true false) (hcont false true) (by norm_num) (by norm_num)
    (by simpa using hF) (by simpa using hG) k hk
  convert h using 1 <;> ring

/-- [The sharper marginal radius gives a numerator residual constant below eight.](goal) Under [the stated assumptions](hyp:hab,hP,hk). -/
-- @node: numerator_projection_bias_bound
lemma numerator_projection_bias_bound (P : ObservedLaw) (α β : ℝ)
    (hab : ExponentDomain α β) (hP : Model α β P) (k : ℕ) (hk : 1 ≤ k) :
    |uniformInner (fun x => propensity P x-cosineProjection k (propensity P) x)
      (fun x => marginalMean P x-cosineProjection k (marginalMean P) x)| ≤
      8*(k : ℝ)^(-(α+β)) := by
  have he : holderSeminorm α (propensity P) ≤ ENNReal.ofReal (1/2 : ℝ) :=
    holderSeminorm_le_of_pointwise α (1/2) _ (propensity_holder_modulus P α hP.propensity_holder)
  have hc : Continuous (propensity P) :=
    (P.continuous_cells true false).add (P.continuous_cells true true)
  have hm : Continuous (marginalMean P) := by
    have heq : marginalMean P = fun x => P.cells false true x+P.cells true true x :=
      funext (marginalMean_eq_cells P)
    rw [heq]
    exact (P.continuous_cells false true).add (P.continuous_cells true true)
  have hα : HolderExponentDomain α := ⟨hab.1.trans hab.2.2.1, hab.2.2.2⟩
  have hβ : HolderExponentDomain β := ⟨hab.1, by linarith [hab.2.1]⟩
  have h := cosineProjection_residual_holder_bound α β (1/2) (9/16) _ _ hα hβ
    hc hm (by norm_num) (by norm_num) he (marginalMean_holder_bound P α β hab hP) k hk
  exact h.trans (by gcongr; norm_num)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
