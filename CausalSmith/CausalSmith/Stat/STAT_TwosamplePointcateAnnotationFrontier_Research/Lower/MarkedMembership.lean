module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.HolderAlgebra
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.IndependentExchangeability

/-! Membership of the finite marked priors and identification of their canonical contrasts. -/

public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- An admissible raw witness has the same contrast as the canonical continuous versions.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hu](hyp:hu), [the specified input h0](hyp:h0), [the specified input ht](hyp:ht), [the specified input hi0](hyp:hi0), [the specified input hi1](hyp:hi1), [the tau eq raw contrast of admissible conclusion](goal) holds. -/
lemma tau_eq_rawContrast_of_admissible {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (hu : UniformDesign P) (h0 : ControlHolder beta L P)
    (ht : EffectHolder gamma L P) (hi0 : ControlInterior P) (hi1 : TreatedInterior P) :
    ∀ x ∈ cube d, tau P hP x = rawContrast P x := by
  let W := canonicalLaw P hP
  have hW := canonicalLaw_spec P hP
  have hWu : W.law.map Prod.fst = uniformLaw d := hW.2.1
  letI : IsFiniteMeasure (uniformLaw d) := by rw [← hWu]; infer_instance
  letI := bernKernel_sfinite_of_margin W (fun w => w.2.2.1) (by fun_prop)
    W.mu0 W.measurable_mu0 W.margin_mu0
  letI := bernKernel_sfinite_of_margin W (fun w => w.2.2.2) (by fun_prop)
    W.mu1 W.measurable_mu1 W.margin_mu1
  letI := bernKernel_sfinite_of_margin P (fun w => w.2.2.1) (by fun_prop)
    P.mu0 P.measurable_mu0 P.margin_mu0
  letI := bernKernel_sfinite_of_margin P (fun w => w.2.2.2) (by fun_prop)
    P.mu1 P.measurable_mu1 P.margin_mu1
  have hW0 := holderNorm_continuousOn _ _ _ hW.2.2.2.2.2.1
  have hP0 := holderNorm_continuousOn _ _ _ h0
  have hW1 : ContinuousOn W.mu1 (cube d) := by
    have hc := (holderNorm_continuousOn _ _ _ hW.2.2.2.2.2.2.1).add hW0
    change ContinuousOn (fun x => (W.mu1 x - W.mu0 x) + W.mu0 x) (cube d) at hc
    simpa only [sub_add_cancel] using hc
  have hP1 : ContinuousOn P.mu1 (cube d) := by
    have hc := (holderNorm_continuousOn _ _ _ ht).add hP0
    change ContinuousOn (fun x => (P.mu1 x - P.mu0 x) + P.mu0 x) (cube d) at hc
    simpa only [sub_add_cancel] using hc
  have hzero : EqOn W.mu0 P.mu0 (cube d) := by
    apply bern_margin_versions_unique _ _ W.measurable_mu0 P.measurable_mu0 hW0 hP0
    · intro x hx; have hb := hW.2.2.2.2.2.2.2.1 x hx; constructor <;> linarith [hb.1, hb.2]
    · intro x hx; have hb := hi0 x hx; constructor <;> linarith [hb.1, hb.2]
    · rw [← hWu, ← W.margin_mu0, hW.1, P.margin_mu0, hu]
  have hone : EqOn W.mu1 P.mu1 (cube d) := by
    apply bern_margin_versions_unique _ _ W.measurable_mu1 P.measurable_mu1 hW1 hP1
    · intro x hx; have hb := hW.2.2.2.2.2.2.2.2 x hx; constructor <;> linarith [hb.1, hb.2]
    · intro x hx; have hb := hi1 x hx; constructor <;> linarith [hb.1, hb.2]
    · rw [← hWu, ← W.margin_mu1, hW.1, P.margin_mu1, hu]
  intro x hx
  simp only [tau, designatedTreated, designatedControl, if_pos hx, rawContrast]
  exact congrArg₂ (fun a b : ℝ => a - b) (hone hx) (hzero hx)

/-- Amplitude restrictions cancel the inverse Hölder scale.  Given [the specified input x](hyp:x), [the specified input s](hyp:s), [the specified input a](hyp:a), [the specified input c](hyp:c), [the specified input hx](hyp:hx), [the specified input ha](hyp:ha), [the amplitude inverse scale bound conclusion](goal) holds. -/
lemma amplitude_inverse_scale_bound (x s a c : ℝ) (hx : 0 < x)
    (ha : a ≤ c * x ^ s) : a * x ^ (-s) ≤ c := by
  calc
    _ ≤ (c * x ^ s) * x ^ (-s) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_pos_of_pos hx _).le
    _ = c := by rw [mul_assoc, ← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero, mul_one]

/-- Every prescribed marked law belongs to the exact primitive class at uniformly small amplitudes.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the marked membership conclusion](goal) holds. -/
lemma marked_membership (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c : ℝ, 0 < c ∧ -- @realizes c(positive claim-local constant)
       c ≤ 1 ∧ ∀ h delta a b,
      0 < delta → delta ≤ h → h ≤ 1/2 → 0 < a → a ≤ c*delta^alpha →
      0 < b → b ≤ c*delta^beta → a*b ≤ c*h^gamma →
      ∀ theta (sigma : SignArray d h delta),
        ∃ hP : PrimitiveClass alpha beta gamma L eps (markedLaw h delta a b theta sigma),
        (∀ x ∈ cube d, tau (markedLaw h delta a b theta sigma) hP x = markedContrast h a b theta x) ∧
        markedContrast (d:=d) h a b theta (x0 d) = -2*thetaSign theta*a*b := by
  rcases hdom with ⟨hdim, hα, hα1, hβ, hβ1, hγ1, hγ3, hL, heps, heps2⟩
  have hγ : 0 < gamma := lt_of_lt_of_le (by norm_num) hγ1
  obtain ⟨Ca, hCa, hFa⟩ := signField_holder d alpha hα hα1
  obtain ⟨Cb, hCb, hFb⟩ := signField_holder d beta hβ hβ1
  obtain ⟨Cg, hCg, hBg⟩ := macro_square_holder d gamma hγ hγ3
  obtain ⟨Ct, hCt, hBt⟩ := macro_square_holder d beta hβ (hβ1.trans (by norm_num))
  let K := (2:ℝ)^d + Ca + Cb + Cg + Ct + 1
  have hK : 0 < K := by dsimp [K]; nlinarith only [hCa, hCb, hCg, hCt, pow_pos (by norm_num : (0:ℝ) < 2) d]
  -- the amplitude room left by the radius `L` and the overlap level `eps`
  let ρ := min 1 (min (L - 1/2) (1/2 - eps))
  have hρ : 0 < ρ := lt_min one_pos (lt_min (by linarith) (by linarith))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρL : ρ ≤ L - 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρe : ρ ≤ 1/2 - eps := (min_le_right _ _).trans (min_le_right _ _)
  let c := ρ*(32*K)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hcK : c*K = ρ/32 := by dsimp [c]; field_simp
  have hKa : Ca ≤ K := by dsimp [K]; nlinarith only [hCa, hCb, hCg, hCt, pow_pos (by norm_num : (0:ℝ) < 2) d]
  have hKb : Cb ≤ K := by dsimp [K]; nlinarith only [hCa, hCb, hCg, hCt, pow_pos (by norm_num : (0:ℝ) < 2) d]
  have hKg : Cg ≤ K := by dsimp [K]; nlinarith only [hCa, hCb, hCg, hCt, pow_pos (by norm_num : (0:ℝ) < 2) d]
  have hKt : Ct ≤ K := by dsimp [K]; nlinarith only [hCa, hCb, hCg, hCt, pow_pos (by norm_num : (0:ℝ) < 2) d]
  have hKd : (2:ℝ)^d ≤ K := by dsimp [K]; nlinarith only [hCa, hCb, hCg, hCt, pow_pos (by norm_num : (0:ℝ) < 2) d]
  have hK1 : 1 ≤ K := by dsimp [K]; nlinarith only [hCa, hCb, hCg, hCt, pow_pos (by norm_num : (0:ℝ) < 2) d]
  have hsmall (D : ℝ) (hD : D ≤ K) : c*D ≤ ρ/32 := by
    exact (mul_le_mul_of_nonneg_left hD hc.le).trans_eq hcK
  have hcsmall : c ≤ 1/32 := by
    have := hsmall 1 hK1
    rw [mul_one] at this
    linarith
  have hc1 : c ≤ 1 := hcsmall.trans (by norm_num)
  refine ⟨c, hc, hc1, ?_⟩
  intro h delta a b hd hdh hh ha hac hb hbc hab theta sigma
  have hh0 : 0 < h := hd.trans_le hdh
  have hd1 : delta ≤ 1 := hdh.trans (hh.trans (by norm_num))
  have hh1 : h ≤ 1 := hh.trans (by norm_num)
  have ha' : a ≤ c := hac.trans (by
    simpa using mul_le_mul_of_nonneg_left (Real.rpow_le_one hd.le hd1 hα.le) hc.le)
  have hb' : b ≤ c := hbc.trans (by
    simpa using mul_le_mul_of_nonneg_left (Real.rpow_le_one hd.le hd1 hβ.le) hc.le)
  have hab' : a*b ≤ c := hab.trans (by
    simpa using mul_le_mul_of_nonneg_left (Real.rpow_le_one hh0.le hh1 hγ.le) hc.le)
  have heSmall : a*(2:ℝ)^d ≤ 1/4 := by
    have ht := (mul_le_mul_of_nonneg_right ha' (by positivity : 0 ≤ (2:ℝ)^d)).trans
      (hsmall _ hKd)
    linarith only [ht, hρ1]
  have hovSmall : a*(2:ℝ)^d ≤ 1/2 - eps := by
    have ht := (mul_le_mul_of_nonneg_right ha' (by positivity : 0 ≤ (2:ℝ)^d)).trans
      (hsmall _ hKd)
    linarith only [ht, hρe, hρ]
  have hmSmall : b*(2:ℝ)^d + a*b ≤ 3/8 := by
    have ht := (mul_le_mul_of_nonneg_right hb' (by positivity : 0 ≤ (2:ℝ)^d)).trans
      (hsmall _ hKd)
    linarith only [ht, hab', hcsmall, hρ1]
  have hsA := amplitude_inverse_scale_bound delta alpha a c hd hac
  have hsB := amplitude_inverse_scale_bound delta beta b c hd hbc
  have hsG := amplitude_inverse_scale_bound h gamma (a*b) c hh0 hab
  have hβγ : beta ≤ gamma := hβ1.trans hγ1
  have hsT : a*b*h^(-beta) ≤ c := by
    have ht : a*b ≤ c*h^beta := hab.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hh0 hh1 hβγ) hc.le)
    exact amplitude_inverse_scale_bound h beta (a*b) c hh0 ht
  have hfieldA : holderNorm (fun x => a*signField h delta sigma false x) alpha ≤
      ENNReal.ofReal (Ca*c) := by
    have ht := holderNorm_const_mul_bound _ alpha (Ca*delta^(-alpha)) a
      (by positivity) (hFa h delta hd hdh hh sigma false)
    rw [abs_of_pos ha] at ht
    apply ht.trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [mul_le_mul_of_nonneg_left hsA hCa.le]
  have hfieldB : holderNorm (fun x => b*signField h delta sigma true x) beta ≤
      ENNReal.ofReal (Cb*c) := by
    have ht := holderNorm_const_mul_bound _ beta (Cb*delta^(-beta)) b
      (by positivity) (hFb h delta hd hdh hh sigma true)
    rw [abs_of_pos hb] at ht
    apply ht.trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [mul_le_mul_of_nonneg_left hsB hCb.le]
  have htheta : |thetaSign theta| = 1 := by cases theta <;> norm_num [thetaSign]
  have hcontrast : holderNorm (markedContrast (d:=d) h a b theta) gamma ≤
      ENNReal.ofReal (2*Cg*c) := by
    have ht := holderNorm_const_mul_bound (fun x : Cov d => (macroBump h x)^2)
      gamma (Cg*h^(-gamma)) (-2*thetaSign theta*a*b) (by positivity) (hBg h hh0 hh)
    have hcoef : |-2*thetaSign theta*a*b| = 2*a*b := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb, htheta]
      norm_num
    rw [hcoef] at ht
    apply ht.trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [mul_le_mul_of_nonneg_left hsG hCg.le]
  have hterm : holderNorm (fun x : Cov d => thetaSign theta*a*b*(macroBump h x)^2) beta ≤
      ENNReal.ofReal (Ct*c) := by
    have ht := holderNorm_const_mul_bound (fun x : Cov d => (macroBump h x)^2)
      beta (Ct*h^(-beta)) (thetaSign theta*a*b) (by positivity) (hBt h hh0 hh)
    rw [abs_mul, abs_mul, htheta, abs_of_pos ha, abs_of_pos hb, one_mul] at ht
    apply ht.trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [mul_le_mul_of_nonneg_left hsT hCt.le]
  have hprop : holderNorm (markedPropensity h delta a sigma) alpha ≤ ENNReal.ofReal L := by
    have ht := holderNorm_add_bound (fun _ : Cov d => (1/2:ℝ)) _ alpha (1/2) (Ca*c)
      (by norm_num) (by positivity) (by simpa using holderNorm_const_bound (d:=d) (1/2) alpha) hfieldA
    exact ht.trans (ENNReal.ofReal_le_ofReal (by linarith only [hρL, hρ, hsmall Ca hKa]))
  have hcontrol : holderNorm (markedMean h delta a b theta false sigma) beta ≤ ENNReal.ofReal L := by
    have ht := holderNorm_add_bound (fun _ : Cov d => (1/2:ℝ)) _ beta (1/2) (Cb*c)
      (by norm_num) (by positivity) (by simpa using holderNorm_const_bound (d:=d) (1/2) beta) hfieldB
    have ht' := holderNorm_add_bound _ _ beta (1/2+Cb*c) (Ct*c)
      (by positivity) (by positivity) ht hterm
    have heq : markedMean h delta a b theta false sigma =
        (fun x => (1/2+b*signField h delta sigma true x) + thetaSign theta*a*b*(macroBump h x)^2) := by
      funext x
      simp only [markedMean, markedContrast, thetaSign, Bool.false_eq_true, if_false]
      ring
    rw [heq]
    exact ht'.trans (ENNReal.ofReal_le_ofReal (by linarith only [hρL, hρ, hsmall Cb hKb, hsmall Ct hKt]))
  let P := markedLaw h delta a b theta sigma
  have hu : UniformDesign P := independentFullLaw_covariates d _ _ _
    (measurable_markedPropensity h delta a sigma)
    (measurable_markedMean h delta a b theta false sigma)
    (measurable_markedMean h delta a b theta true sigma)
  have hex : ConditionalExchangeability P := independentPrimitive_exchangeability _ _ _ _ _ _
  have hbands := markedLaw_probability_bands h delta a b theta sigma ha.le hb.le heSmall hmSmall
    eps heps hovSmall
  have he : PropensityHolder alpha L P := by
    change holderNorm _ alpha ≤ _
    have hpEq : P.e = markedPropensity h delta a sigma :=
      funext (markedLaw_propensity_eq h delta a b theta sigma ha.le heSmall)
    rw [hpEq]
    exact hprop
  have h0 : ControlHolder beta L P := by
    change holderNorm _ beta ≤ _
    have hpEq : P.mu0 = markedMean h delta a b theta false sigma :=
      funext (fun x => (markedLaw_means_eq h delta a b theta sigma ha.le hb.le hmSmall x).1)
    rw [hpEq]
    exact hcontrol
  have ht : EffectHolder gamma L P := by
    change holderNorm (rawContrast P) gamma ≤ _
    rw [markedLaw_rawContrast_eq h delta a b theta sigma ha.le hb.le hmSmall]
    exact hcontrast.trans (ENNReal.ofReal_le_ofReal (by linarith only [hρL, hρ, hsmall Cg hKg]))
  have hP : PrimitiveClass alpha beta gamma L eps P :=
    ⟨P, rfl, hu, hex, hbands.1, he, h0, ht, hbands.2.1, hbands.2.2⟩
  refine ⟨hP, ?_, markedContrast_at_x0 h a b theta⟩
  intro x hx
  rw [tau_eq_rawContrast_of_admissible P hP hu h0 ht hbands.2.1 hbands.2.2 x hx,
    markedLaw_rawContrast_eq h delta a b theta sigma ha.le hb.le hmSmall]

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
