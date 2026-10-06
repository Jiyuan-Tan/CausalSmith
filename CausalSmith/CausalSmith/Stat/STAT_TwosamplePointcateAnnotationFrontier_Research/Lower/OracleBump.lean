module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.MarkedMembership
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.MixtureDensity

/-! # Constant-propensity bump alternatives
The oracle lower-bound roadmap uses a fixed smooth compact profile, with a
constant control mean and independent Bernoulli potential outcomes.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The unsquared macro bump has the exact scaled Hölder bound on windows up to side one.  Given [the specified input d](hyp:d), [the specified input s](hyp:s), [the specified input hs](hyp:hs), [the oracle macro holder conclusion](goal) holds. -/
lemma oracle_macro_holder (d : ℕ) (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ h, 0 < h → h ≤ 1 →
      holderNorm (macroBump (d:=d) h) s ≤ ENNReal.ofReal (C*h^(-s)) := by
  let f : Cov d → ℝ := fun z => macroBump 1 (z+x0 d)
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    dsimp [f]
    fun_prop
  have hsupp : HasCompactSupport f :=
    (macroBump_compactSupport d).comp_homeomorph (Homeomorph.addRight (x0 d))
  obtain ⟨C, hC, hb⟩ := compact_profile_scaled_holder f hf hsupp s hs
  refine ⟨C, hC, ?_⟩
  intro h hh hh1
  simpa only [f, macroBump_dilation] using hb h hh hh1

/-- The two oracle alternatives use treatment probability and control mean one half.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [oracle bump primitive](goal) is the corresponding construction. -/
def oracleBumpPrimitive (d : ℕ) (h b : ℝ) (theta : Bool) : PrimitiveLaw d :=
  independentPrimitive (fun _ => 1/2) (fun _ => 1/2)
    (fun x => 1/2+thetaSign theta*b*macroBump h x)
    measurable_const measurable_const (by fun_prop)

/-- Small bump amplitudes keep all three raw margins in their prescribed probability bands.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input hb](hyp:hb), [the specified input hbsmall](hyp:hbsmall), [the oracle bump primitive margins conclusion](goal) holds. -/
lemma oracleBumpPrimitive_margins (d : ℕ) (h b : ℝ) (theta : Bool)
    (hb : 0 ≤ b) (hbsmall : b ≤ 1/8) :
    (oracleBumpPrimitive d h b theta).e = (fun _ => 1/2) ∧
    (oracleBumpPrimitive d h b theta).mu0 = (fun _ => 1/2) ∧
    (oracleBumpPrimitive d h b theta).mu1 =
      (fun x => 1/2+thetaSign theta*b*macroBump h x) ∧
    (∀ x, 1/8 ≤ (oracleBumpPrimitive d h b theta).mu1 x ∧
      (oracleBumpPrimitive d h b theta).mu1 x ≤ 7/8) := by
  have hband (x : Cov d) : 1/8 ≤ 1/2+thetaSign theta*b*macroBump h x ∧
      1/2+thetaSign theta*b*macroBump h x ≤ 7/8 := by
    have hm := macroBump_mem h x
    cases theta <;> norm_num [thetaSign] <;> constructor <;> nlinarith [hm.1, hm.2]
  have he : (oracleBumpPrimitive d h b theta).e = (fun _ => 1/2) := by
    funext x
    exact probabilityClip_eq_of_mem _ (by norm_num)
  have h0 : (oracleBumpPrimitive d h b theta).mu0 = (fun _ => 1/2) := by
    funext x
    exact probabilityClip_eq_of_mem _ (by norm_num)
  have h1 : (oracleBumpPrimitive d h b theta).mu1 =
      (fun x => 1/2+thetaSign theta*b*macroBump h x) := by
    funext x
    apply probabilityClip_eq_of_mem
    constructor <;> linarith [(hband x).1, (hband x).2]
  exact ⟨he, h0, h1, fun x => h1 ▸ hband x⟩

/-- Canonical representatives coincide with admissible raw propensity and arm means.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hu](hyp:hu), [the specified input he](hyp:he), [the specified input h0](hyp:h0), [the specified input ht](hyp:ht), [the specified input hov](hyp:hov), [the specified input hi0](hyp:hi0), [the specified input hi1](hyp:hi1), [the oracle admissible raw versions conclusion](goal) holds. -/
lemma oracle_admissible_raw_versions {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (hu : UniformDesign P) (he : PropensityHolder alpha L P)
    (h0 : ControlHolder beta L P) (ht : EffectHolder gamma L P)
    (hov : Overlap eps P) (hi0 : ControlInterior P) (hi1 : TreatedInterior P) :
    ∀ x ∈ cube d, designatedPropensity P hP x = P.e x ∧
      designatedControl P hP x = P.mu0 x ∧ tau P hP x = rawContrast P x := by
  let W := canonicalLaw P hP
  have hW := canonicalLaw_spec P hP
  have hWu : W.law.map Prod.fst = uniformLaw d := hW.2.1
  letI : IsFiniteMeasure (uniformLaw d) := by rw [← hWu]; infer_instance
  letI := bernKernel_sfinite_of_margin W (fun w => w.2.1) (by fun_prop)
    W.e W.measurable_e W.margin_e
  letI := bernKernel_sfinite_of_margin P (fun w => w.2.1) (by fun_prop)
    P.e P.measurable_e P.margin_e
  letI := bernKernel_sfinite_of_margin W (fun w => w.2.2.1) (by fun_prop)
    W.mu0 W.measurable_mu0 W.margin_mu0
  letI := bernKernel_sfinite_of_margin P (fun w => w.2.2.1) (by fun_prop)
    P.mu0 P.measurable_mu0 P.margin_mu0
  have heq : EqOn W.e P.e (cube d) := by
    apply bern_margin_versions_unique _ _ W.measurable_e P.measurable_e
      (holderNorm_continuousOn _ _ _ hW.2.2.2.2.1)
      (holderNorm_continuousOn _ _ _ he)
    · exact hW.2.2.2.1.unit
    · exact hov.unit
    · rw [← hWu, ← W.margin_e, hW.1, P.margin_e, hu]
  have h0eq : EqOn W.mu0 P.mu0 (cube d) := by
    apply bern_margin_versions_unique _ _ W.measurable_mu0 P.measurable_mu0
      (holderNorm_continuousOn _ _ _ hW.2.2.2.2.2.1)
      (holderNorm_continuousOn _ _ _ h0)
    · intro x hx; have hb := hW.2.2.2.2.2.2.2.1 x hx; constructor <;> linarith [hb.1, hb.2]
    · intro x hx; have hb := hi0 x hx; constructor <;> linarith [hb.1, hb.2]
    · rw [← hWu, ← W.margin_mu0, hW.1, P.margin_mu0, hu]
  intro x hx
  refine ⟨?_, ?_, tau_eq_rawContrast_of_admissible P hP hu h0 ht hi0 hi1 x hx⟩
  · simpa only [designatedPropensity, if_pos hx] using heq hx
  · simpa only [designatedControl, if_pos hx] using h0eq hx

/-- Smoothness and small amplitude make each explicit oracle alternative a member of the exact class.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input h](hyp:h), [the specified input b](hyp:b), [the specified input hL](hyp:hL), [the specified input hb](hyp:hb), [the specified input hbsmall](hyp:hbsmall), [the specified input hsmooth](hyp:hsmooth), [the specified input theta](hyp:theta), [the oracle bump primitive membership conclusion](goal) holds. -/
lemma oracleBumpPrimitive_membership (d : ℕ) (alpha beta gamma L eps h b : ℝ)
    (hL : 1/2 ≤ L) (heps : 0 < eps) (heps' : eps ≤ 1/2) (hb : 0 ≤ b) (hbsmall : b ≤ 1/8)
    (hsmooth : holderNorm (fun x : Cov d => b*macroBump h x) gamma ≤ ENNReal.ofReal L)
    (theta : Bool) :
    ∃ hP : PrimitiveClass alpha beta gamma L eps (oracleBumpPrimitive d h b theta),
      ∀ x ∈ cube d,
        designatedPropensity _ hP x = 1/2 ∧ designatedControl _ hP x = 1/2 ∧
        tau _ hP x = thetaSign theta*b*macroBump h x := by
  let P := oracleBumpPrimitive d h b theta
  obtain ⟨heq, h0eq, h1eq, hband⟩ := oracleBumpPrimitive_margins d h b theta hb hbsmall
  have hu : UniformDesign P := independentFullLaw_covariates d _ _ _ measurable_const measurable_const (by fun_prop)
  have hex : ConditionalExchangeability P := independentPrimitive_exchangeability _ _ _ measurable_const measurable_const (by fun_prop)
  have hov : Overlap eps P := by
    refine ⟨heps, fun x hx => ?_⟩
    rw [show P.e = _ from heq]
    constructor <;> linarith
  have hi0 : ControlInterior P := by intro x hx; rw [show P.mu0 = _ from h0eq]; norm_num
  have hi1 : TreatedInterior P := fun x _ =>
    ⟨by linarith [(hband x).1], by linarith [(hband x).2]⟩
  have he : PropensityHolder alpha L P := by
    change holderNorm P.e alpha ≤ _
    rw [show P.e = _ from heq]
    exact (holderNorm_const_bound (d:=d) (1/2) alpha).trans
      (ENNReal.ofReal_le_ofReal (by norm_num; linarith))
  have h0 : ControlHolder beta L P := by
    change holderNorm P.mu0 beta ≤ _
    rw [show P.mu0 = _ from h0eq]
    exact (holderNorm_const_bound (d:=d) (1/2) beta).trans
      (ENNReal.ofReal_le_ofReal (by norm_num; linarith))
  have hcontrast : rawContrast P = (fun x => thetaSign theta*b*macroBump h x) := by
    funext x
    simp only [rawContrast, show P.mu1 = _ from h1eq, show P.mu0 = _ from h0eq]
    ring
  have ht : EffectHolder gamma L P := by
    change holderNorm (rawContrast P) gamma ≤ _
    rw [hcontrast]
    cases theta
    · have ht := holderNorm_const_mul_bound (fun x : Cov d => b*macroBump h x)
        gamma L (-1) (by linarith) hsmooth
      simpa [thetaSign, mul_assoc] using ht
    · simpa [thetaSign] using hsmooth
  have hP : PrimitiveClass alpha beta gamma L eps P :=
    ⟨P, rfl, hu, hex, hov, he, h0, ht, hi0, hi1⟩
  refine ⟨hP, ?_⟩
  intro x hx
  obtain ⟨hpe, hp0, hpt⟩ := oracle_admissible_raw_versions P hP hu he h0 ht hov hi0 hi1 x hx
  exact ⟨hpe.trans (congrFun heq x), hp0.trans (congrFun h0eq x),
    hpt.trans (congrFun hcontrast x)⟩

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
