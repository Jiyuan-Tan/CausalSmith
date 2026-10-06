module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.ComponentInformation

/-!
# Component Hellinger estimate

Positive record likelihoods give the component density floor (MC23).
The square-root identity converts the two-amplitude density difference into
the squared Hellinger estimate (MC30–MC31).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- A common positive density floor controls squared square-root differences.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input t](hyp:t), [the specified input ht](hyp:ht), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the sqrt difference sq le of floor conclusion](goal) holds. -/
lemma sqrt_difference_sq_le_of_floor (f g t : ℝ) (ht : 0 < t)
    (hf : t ≤ f) (hg : t ≤ g) :
    (Real.sqrt f - Real.sqrt g)^2 ≤ (f-g)^2 / (4*t) := by
  have hf0 : 0 ≤ f := ht.le.trans hf
  have hg0 : 0 ≤ g := ht.le.trans hg
  have hs := Real.sqrt_le_sqrt hf
  have hr := Real.sqrt_le_sqrt hg
  have hden : 4*t ≤ (Real.sqrt f + Real.sqrt g)^2 := by
    nlinarith [Real.sq_sqrt ht.le, Real.sqrt_nonneg t,
      Real.sqrt_nonneg f, Real.sqrt_nonneg g]
  have hid : (f-g)^2 = (Real.sqrt f-Real.sqrt g)^2 *
      (Real.sqrt f+Real.sqrt g)^2 := by
    nlinarith [Real.sq_sqrt hf0, Real.sq_sqrt hg0]
  apply (le_div_iff₀ (by positivity : 0 < 4*t)).2
  nlinarith [mul_le_mul_of_nonneg_left hden
    (sq_nonneg (Real.sqrt f-Real.sqrt g))]

/-- Small marked amplitudes give every record likelihood a uniform positive floor.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input sigma](hyp:sigma), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the specified input he](hyp:he), [the specified input hm](hyp:hm), [the specified input x](hyp:x), [the specified input s](hyp:s), [the specified input i](hyp:i), [the marked record likelihood lower conclusion](goal) holds. -/
lemma marked_recordLikelihood_lower {d n m : ℕ} (h delta a b : ℝ)
    (theta : Bool) (sigma : SignArray d h delta) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : a*(2:ℝ)^d ≤ 1/16) (hm : b*(2:ℝ)^d+a*b ≤ 1/16)
    (x : Fin (n+m) → Cov d) (s : RecordSpins n m) (i : Fin (n+m)) :
    (1/2:ℝ) ≤ recordLikelihood (markedLaw h delta a b theta sigma) x s i := by
  have hsign (v : Bool) : |thetaSign v| = 1 := by cases v <;> norm_num [thetaSign]
  have hpert (v : Bool) (amp : ℝ) (hamp : 0 ≤ amp) (control : Bool) (y : Cov d) :
      |2*thetaSign v*amp*signField h delta sigma control y| ≤ 2*amp*(2:ℝ)^d := by
    rw [abs_mul, abs_mul, abs_mul, hsign, abs_of_nonneg hamp]
    norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), mul_one]
    exact mul_le_mul_of_nonneg_left (abs_signField_le h delta sigma control y)
      (by positivity)
  induction i using Fin.addCases with
  | left j =>
    let y := x (Fin.castAdd m j)
    have hp := markedPropensity_overlap h delta a sigma ha (by linarith) y
    have hmean := fun arm => markedMean_interior h delta a b theta arm sigma ha hb
      (by linarith : b*(2:ℝ)^d+a*b ≤ 3/8) y
    have hlik := marked_labelLikelihood_spin d h delta a b theta sigma y
      ⟨by linarith [hp.1], by linarith [hp.2]⟩
      (fun arm => ⟨by linarith [(hmean arm).1], by linarith [(hmean arm).2]⟩) (s.1 j)
    have ht : |thetaSign (s.1 j).1*thetaSign (s.1 j).2*markedContrast h a b theta y| ≤ 2*a*b := by
      simpa only [abs_mul, hsign, one_mul] using abs_markedContrast_le h a b theta y ha hb
    have h1 := (abs_le.mp (hpert (s.1 j).1 a ha false y)).1
    have h2 := (abs_le.mp (hpert (s.1 j).2 b hb true y)).1
    have h3 := (abs_le.mp ht).1
    have hfirst : 7/8 ≤ 1+2*thetaSign (s.1 j).1*a*signField h delta sigma false y := by linarith
    have hsecond : 7/8 ≤ 1+2*thetaSign (s.1 j).2*b*signField h delta sigma true y+
        thetaSign (s.1 j).1*thetaSign (s.1 j).2*markedContrast h a b theta y := by linarith
    simp only [recordLikelihood, Fin.addCases_left]
    change 1/2 ≤ labelLikelihood _ y _
    rw [hlik]
    have hmul := mul_le_mul hfirst hsecond (by norm_num : (0:ℝ) ≤ 7/8)
      (by linarith : 0 ≤ 1+2*thetaSign (s.1 j).1*a*signField h delta sigma false y)
    linarith
  | right j =>
    let y := x (Fin.natAdd n j)
    have hp := markedPropensity_overlap h delta a sigma ha (by linarith) y
    simp only [recordLikelihood, Fin.addCases_right, auxiliaryLikelihood]
    rw [markedLaw_propensity_eq h delta a b theta sigma ha (by linarith) y,
      bern_singleton_toReal_spin _ ⟨by linarith [hp.1], by linarith [hp.2]⟩]
    have h1 := (abs_le.mp (hpert (s.2 j) a ha false y)).1
    dsimp [y, markedPropensity] at *
    linarith

/-- Averaging positive record products preserves the component density floor.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the specified input he](hyp:he), [the specified input hm](hyp:hm), [the specified input x](hyp:x), [the specified input V](hyp:V), [the specified input s](hyp:s), [the marked component density lower conclusion](goal) holds. -/
lemma marked_componentDensity_lower {d n m : ℕ} (h delta a b : ℝ)
    (theta : Bool) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : a*(2:ℝ)^d ≤ 1/16) (hm : b*(2:ℝ)^d+a*b ≤ 1/16)
    (x : Fin (n+m) → Cov d) (V : Finset (Fin (n+m))) (s : RecordSpins n m) :
    (1/2:ℝ)^V.card ≤ componentDensity (markedHandle d h delta a b) theta x V s := by
  have hp (sigma : SignArray d h delta) :
      (1/2:ℝ)^V.card ≤ ∏ i ∈ V, recordLikelihood (markedLaw h delta a b theta sigma) x s i := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by norm_num)
      (fun i _ => marked_recordLikelihood_lower h delta a b theta sigma ha hb he hm x s i)
  calc
    _ = ∑ sigma : SignArray d h delta, markedWeight h delta theta sigma * (1/2:ℝ)^V.card := by
      rw [← Finset.sum_mul, (marked_prior_mass d h delta theta).2, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun sigma _ =>
      mul_le_mul_of_nonneg_left (hp sigma) ((marked_prior_mass d h delta theta).1 sigma))

/-- A bounded density difference and a positive floor imply the integrated Hellinger bound.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input t](hyp:t), [the specified input D](hyp:D), [the specified input ht](hyp:ht), [the specified input hD](hyp:hD), [the specified input hfloor](hyp:hfloor), [the specified input hdiff](hyp:hdiff), [the density hellinger le of floor conclusion](goal) holds. -/
lemma density_hellinger_le_of_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (t D : ℝ) (ht : 0 < t) (hD : 0 ≤ D)
    (hfloor : ∀ x, t ≤ f x ∧ t ≤ g x) (hdiff : ∀ x, |f x-g x| ≤ D) :
    Causalean.Stat.hellingerSqDensity μ f g ≤ D^2/(4*t) := by
  have hbound (x : Ω) : (Real.sqrt (f x)-Real.sqrt (g x))^2 ≤ D^2/(4*t) := by
    apply (sqrt_difference_sq_le_of_floor _ _ _ ht (hfloor x).1 (hfloor x).2).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_abs (f x-g x), sq_nonneg (D-|f x-g x|), hdiff x, abs_nonneg (f x-g x)]
  have hi : Integrable (fun x => (Real.sqrt (f x)-Real.sqrt (g x))^2) μ := by
    apply (integrable_const (D^2/(4*t))).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.sqrt (f x)-Real.sqrt (g x)))] using hbound x)
  unfold Causalean.Stat.hellingerSqDensity
  simpa using integral_mono hi (integrable_const (D^2/(4*t))) hbound

/-- The component squared Hellinger estimate retains both nuisance amplitudes,
uniformly in the two channel sizes and in the common probability reference.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the marked component hellinger bound conclusion](goal) holds. -/
lemma marked_component_hellinger_bound (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < K ∧ ∀ h delta a b,
      0 < delta → delta ≤ h → h ≤ 1/2 → 0 < a → a ≤ c*delta^alpha →
      0 < b → b ≤ c*delta^beta → a*b ≤ c*h^gamma →
      ∀ n m (x : Fin (n+m) → Cov d), (∀ i, x i ∈ cube d) →
      ∀ V : Finset (Fin (n+m)), ∀ μ : Measure (RecordSpins n m),
      IsProbabilityMeasure μ →
      Causalean.Stat.hellingerSqDensity μ
        (componentDensity (markedHandle d h delta a b) true x V)
        (componentDensity (markedHandle d h delta a b) false x V) ≤
        K*(9/2:ℝ)^V.card*(V.card:ℝ)^4*a^2*b^2 := by
  obtain ⟨cI, C, hcI, hcI1, hC, hdiff⟩ := component_information_bound d alpha beta gamma L eps hdom
  let B : ℝ := (2:ℝ)^d
  let c := min cI (1/(64*B))
  have hB : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hBp : 0 < B := by positivity
  have hc : 0 < c := lt_min hcI (by positivity)
  have hcI' : c ≤ cI := min_le_left _ _
  have hcB : c*B ≤ 1/64 := by
    have hm := mul_le_mul_of_nonneg_right (min_le_right cI (1/(64*B))) hBp.le
    have hid : (1/(64*B))*B = 1/64 := by field_simp
    simpa only [c, hid] using hm
  have hcsmall : c ≤ 1/64 := by nlinarith
  refine ⟨c, C^2, hc, hcI'.trans hcI1, sq_pos_of_pos hC, ?_⟩
  intro h delta a b hd hdh hh ha hac hb hbc hab n m x hx V μ hμ
  letI := hμ
  have hd1 : delta ≤ 1 := by linarith
  have haC : a ≤ c := hac.trans (by
    simpa using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one hd.le hd1 hdom.2.1.le) hc.le)
  have hbC : b ≤ c := hbc.trans (by
    simpa using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one hd.le hd1 hdom.2.2.2.1.le) hc.le)
  have he : a*(2:ℝ)^d ≤ 1/16 := by change a*B ≤ _; nlinarith
  have hm : b*(2:ℝ)^d+a*b ≤ 1/16 := by
    have hab' := mul_le_mul haC hbC hb.le hc.le
    change b*B+a*b ≤ _
    nlinarith
  have hscale (s : ℝ) (hs : 0 < s) (e : ℝ) : c*s^e ≤ cI*s^e :=
    mul_le_mul_of_nonneg_right hcI' (Real.rpow_pos_of_pos hs e).le
  have hh0 : 0 < h := hd.trans_le hdh
  have hdif := hdiff h delta a b hd hdh hh ha (hac.trans (hscale delta hd alpha))
    hb (hbc.trans (hscale delta hd beta)) (hab.trans (hscale h hh0 gamma)) n m x hx V
  have hbnd := density_hellinger_le_of_floor μ
    (componentDensity (markedHandle d h delta a b) true x V)
    (componentDensity (markedHandle d h delta a b) false x V)
    (measurable_of_countable _) (measurable_of_countable _)
    ((1/2:ℝ)^V.card) (C*(3/2:ℝ)^V.card*(V.card:ℝ)^2*a*b)
    (by positivity) (by positivity)
    (fun s => ⟨marked_componentDensity_lower h delta a b true ha.le hb.le he hm x V s,
      marked_componentDensity_lower h delta a b false ha.le hb.le he hm x V s⟩) hdif
  refine hbnd.trans ?_
  have hid : (C*(3/2:ℝ)^V.card*(V.card:ℝ)^2*a*b)^2 / (4*(1/2:ℝ)^V.card) =
      C^2/4*(9/2:ℝ)^V.card*(V.card:ℝ)^4*a^2*b^2 := by
    rw [show (9/2:ℝ)^V.card = ((3/2:ℝ)^V.card)^2 / (1/2:ℝ)^V.card by
      rw [← pow_mul, mul_comm V.card 2, pow_mul, ← div_pow]; norm_num]
    field_simp
    <;> ring
  rw [hid]
  gcongr
  nlinarith [sq_nonneg C]

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
