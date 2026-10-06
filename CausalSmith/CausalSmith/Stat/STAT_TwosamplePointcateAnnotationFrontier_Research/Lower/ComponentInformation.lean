module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.Components

/-!
# Component likelihood information bound

Contrast deletion and cancellation of the common one-channel sign marginals
retain both nuisance amplitudes in the component density difference (MC24–MC29).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Both sign-array marginals agree between hypotheses, for arbitrary functions of one array.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input control](hyp:control), [the specified input F](hyp:F), [the marked channel marginal expectation conclusion](goal) holds. -/
lemma marked_channel_marginal_expectation (d : ℕ) (h delta : ℝ) (control : Bool)
    (F : ({z // z ∈ frameIdx d h delta} → Bool) → ℝ) :
    (∑ sigma : SignArray d h delta, markedWeight h delta true sigma *
      F (fun z => if control then (sigma z).2 else (sigma z).1)) =
    ∑ sigma : SignArray d h delta, markedWeight h delta false sigma *
      F (fun z => if control then (sigma z).2 else (sigma z).1) := by
  let e : SignArray d h delta ≃ SignArray d h delta :=
    { toFun := fun sigma z => if control then (!(sigma z).1, (sigma z).2)
        else ((sigma z).1, !(sigma z).2)
      invFun := fun sigma z => if control then (!(sigma z).1, (sigma z).2)
        else ((sigma z).1, !(sigma z).2)
      left_inv := by intro sigma; funext z; cases control <;> simp
      right_inv := by intro sigma; funext z; cases control <;> simp }
  apply Fintype.sum_equiv e
  intro sigma
  have hw : markedWeight h delta true sigma = markedWeight h delta false (e sigma) := by
    unfold markedWeight
    apply Finset.prod_congr rfl
    intro z _
    rcases hs : sigma z with ⟨l,v⟩
    cases control <;> cases l <;> cases v <;> norm_num [e, thetaSign, hs]
  rw [hw]
  congr 2
  funext z
  cases control <;> rfl

/-- Squared channel-product growth is bounded by the full-record growth factor.  Given [the specified input p](hyp:p), [the component channel power bound conclusion](goal) holds. -/
lemma component_channel_power_bound (p : ℕ) :
    (9/8:ℝ)^p * (9/8:ℝ)^p ≤ (3/2:ℝ)^p := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) p

set_option maxHeartbeats 800000 in
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the component information bound conclusion](goal) holds. -/
lemma component_information_bound (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < C ∧ ∀ h delta a b,
      0 < delta → delta ≤ h → h ≤ 1/2 → 0 < a → a ≤ c*delta^alpha →
      0 < b → b ≤ c*delta^beta → a*b ≤ c*h^gamma →
      ∀ n m (x : Fin (n+m) → Cov d), (∀ i, x i ∈ cube d) →
      ∀ V : Finset (Fin (n+m)), ∀ s : RecordSpins n m,
        |componentDensity (markedHandle d h delta a b) true x V s -
          componentDensity (markedHandle d h delta a b) false x V s| ≤
          C*(3/2:ℝ)^V.card*(V.card:ℝ)^2*a*b := by
  classical
  let B : ℝ := (2:ℝ)^d
  let c : ℝ := 1/(64*B)
  have hB : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hBp : 0 < B := by positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hcB : c*B = 1/64 := by dsimp [c]; field_simp
  have hc1 : c ≤ 1/64 := by nlinarith
  refine ⟨c, 8*B^2+6, hc, by linarith, by positivity, ?_⟩
  intro h delta a b hd hdh hh ha hac hb hbc hab n m x hx V s
  have hδ1 : delta ≤ 1 := by linarith
  have haC : a ≤ c := hac.trans (by
    simpa using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one hd.le hδ1 hdom.2.1.le) hc.le)
  have hbC : b ≤ c := hbc.trans (by
    simpa using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one hd.le hδ1 hdom.2.2.2.1.le) hc.le)
  have haB : a*B ≤ 1/64 := by nlinarith
  have hbB : b*B ≤ 1/64 := by nlinarith
  have habsmall : a*b ≤ 1/4096 := by nlinarith [mul_le_mul haC hbC hb.le hc.le]
  let f : SignArray d h delta → Fin (n+m) → ℝ := fun sigma =>
    Fin.addCases
      (fun i => 1+2*thetaSign (s.1 i).1*a*signField h delta sigma false (x (Fin.castAdd m i)))
      (fun j => 1+2*thetaSign (s.2 j)*a*signField h delta sigma false (x (Fin.natAdd n j)))
  let g : SignArray d h delta → Fin (n+m) → ℝ := fun sigma =>
    Fin.addCases
      (fun i => 1+2*thetaSign (s.1 i).2*b*signField h delta sigma true (x (Fin.castAdd m i)))
      (fun _ => 1)
  have hsign (v : Bool) : |thetaSign v| = 1 := by cases v <;> norm_num [thetaSign]
  have hpert (v : Bool) (amp : ℝ) (hamp : 0 ≤ amp) (sigma : SignArray d h delta)
      (control : Bool) (y : Cov d) :
      |2*thetaSign v*amp*signField h delta sigma control y| ≤ 2*amp*B := by
    rw [abs_mul, abs_mul, abs_mul, hsign, abs_of_nonneg hamp]
    norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), mul_one]
    exact mul_le_mul_of_nonneg_left (abs_signField_le h delta sigma control y) (by positivity)
  have hfd : ∀ sigma i, |f sigma i-1| ≤ 2*a*B := by
    intro sigma i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simpa [f] using hpert _ a ha.le sigma false _
  have hgd : ∀ sigma i, |g sigma i-1| ≤ 2*b*B := by
    intro sigma i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [g] using hpert _ b hb.le sigma true _
    · simp [g]; positivity
  have hfactor {v D : ℝ} (hv : |v-1| ≤ D) (hD : D ≤ 1/8) :
      |v| ≤ 9/8 ∧ 7/8 ≤ v := by
    have ht := abs_le.mp hv
    have hn := (abs_add_le (v-1) 1)
    rw [sub_add_cancel, abs_one] at hn
    constructor <;> linarith
  have hf : ∀ sigma i, |f sigma i| ≤ 9/8 := fun sigma i =>
    (hfactor (hfd sigma i) (by linarith)).1
  have hg : ∀ sigma i, |g sigma i| ≤ 9/8 := fun sigma i =>
    (hfactor (hgd sigma i) (by linarith)).1
  have he : a*B ≤ 1/4 := by linarith
  have hm : b*B+a*b ≤ 3/8 := by linarith
  have hrec (theta : Bool) (sigma : SignArray d h delta) (i : Fin (n+m)) :
      |recordLikelihood (markedLaw h delta a b theta sigma) x s i| ≤ 3/2 ∧
      |recordLikelihood (markedLaw h delta a b theta sigma) x s i - f sigma i*g sigma i| ≤ 3*a*b := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hp := markedPropensity_overlap h delta a sigma ha.le he (x (Fin.castAdd m j))
      have hmean := fun arm => markedMean_interior h delta a b theta arm sigma ha.le hb.le hm (x (Fin.castAdd m j))
      have hlik := marked_labelLikelihood_spin d h delta a b theta sigma _
        ⟨by linarith [hp.1], by linarith [hp.2]⟩
        (fun arm => ⟨by linarith [(hmean arm).1], by linarith [(hmean arm).2]⟩) (s.1 j)
      have ht : |thetaSign (s.1 j).1*thetaSign (s.1 j).2 * markedContrast h a b theta (x (Fin.castAdd m j))| ≤ 2*a*b := by
        simpa only [abs_mul, hsign, one_mul] using abs_markedContrast_le h a b theta _ ha.le hb.le
      simp only [recordLikelihood, Fin.addCases_left]
      change |labelLikelihood _ _ _| ≤ _ ∧ |labelLikelihood _ _ _ - _| ≤ _
      rw [hlik]
      have hfj : f sigma (Fin.castAdd m j) = 1+2*thetaSign (s.1 j).1*a*signField h delta sigma false (x (Fin.castAdd m j)) := by simp only [f, Fin.addCases_left]
      have hgj : g sigma (Fin.castAdd m j) = 1+2*thetaSign (s.1 j).2*b*signField h delta sigma true (x (Fin.castAdd m j)) := by simp only [g, Fin.addCases_left]
      rw [← hfj, ← hgj]
      change |f sigma (Fin.castAdd m j) * (g sigma (Fin.castAdd m j) + _)| ≤ _ ∧
        |f sigma (Fin.castAdd m j) * (g sigma (Fin.castAdd m j) + _) -
          f sigma (Fin.castAdd m j)*g sigma (Fin.castAdd m j)| ≤ _
      constructor
      · rw [abs_mul]
        have hu := abs_add_le (g sigma (Fin.castAdd m j))
          (thetaSign (s.1 j).1*thetaSign (s.1 j).2*markedContrast h a b theta (x (Fin.castAdd m j)))
        have hm := mul_le_mul (hf sigma (Fin.castAdd m j)) (hu.trans (add_le_add (hg sigma _) ht))
          (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 9/8)
        nlinarith only [hm, habsmall]
      · rw [mul_add, add_sub_cancel_left, abs_mul]
        have hm := mul_le_mul (hf sigma (Fin.castAdd m j)) ht (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 9/8)
        nlinarith only [hm, ha, hb]
    · have hp := markedPropensity_overlap h delta a sigma ha.le he (x (Fin.natAdd n j))
      have hlik : auxiliaryLikelihood (markedLaw h delta a b theta sigma) (x (Fin.natAdd n j)) (s.2 j) = f sigma (Fin.natAdd n j) := by
        unfold auxiliaryLikelihood
        rw [markedLaw_propensity_eq h delta a b theta sigma ha.le he]
        rw [bern_singleton_toReal_spin _ ⟨by linarith [hp.1], by linarith [hp.2]⟩]
        simp [f, markedPropensity]; ring
      simpa [recordLikelihood, hlik, g] using And.intro ((hf sigma (Fin.natAdd n j)).trans (by norm_num : (9/8:ℝ) ≤ 3/2)) (by positivity : (0:ℝ) ≤ 3*a*b)
  let A := fun sigma => ∏ i ∈ V, f sigma i
  let G := fun sigma => ∏ i ∈ V, g sigma i
  have hcommon (control : Bool) (F : SignArray d h delta → ℝ)
      (hF : ∀ sigma sigma', (∀ z, (if control then (sigma z).2 else (sigma z).1) =
        (if control then (sigma' z).2 else (sigma' z).1)) → F sigma = F sigma') :
      (∑ sigma, markedWeight h delta true sigma*F sigma) =
      ∑ sigma, markedWeight h delta false sigma*F sigma := by
    let lift : ({z // z ∈ frameIdx d h delta} → Bool) → SignArray d h delta := fun l z => if control then (false,l z) else (l z,false)
    have ht (sigma) : F sigma = F (lift (fun z => if control then (sigma z).2 else (sigma z).1)) := by
      apply hF; intro z; cases control <;> rfl
    calc
      _ = ∑ sigma, markedWeight h delta true sigma * F (lift (fun z => if control then (sigma z).2 else (sigma z).1)) :=
        Finset.sum_congr rfl (fun sigma _ => congrArg (fun v => markedWeight h delta true sigma*v) (ht sigma))
      _ = ∑ sigma, markedWeight h delta false sigma * F (lift (fun z => if control then (sigma z).2 else (sigma z).1)) :=
        marked_channel_marginal_expectation d h delta control (fun l => F (lift l))
      _ = _ := Finset.sum_congr rfl (fun sigma _ => congrArg (fun v => markedWeight h delta false sigma*v) (ht sigma).symm)
  have hA := hcommon false A (by
    intro sigma sigma' hs
    simp only [Bool.false_eq_true, if_false, if_true] at hs
    apply Finset.prod_congr rfl; intro i _
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [f, Fin.addCases_left, Fin.addCases_right, signField, Bool.false_eq_true, if_false, hs])
  have hG := hcommon true G (by
    intro sigma sigma' hs
    simp only [Bool.false_eq_true, if_false, if_true] at hs
    apply Finset.prod_congr rfl; intro i _
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [g, Fin.addCases_left, Fin.addCases_right, signField, if_true, hs])
  let U := (V.card:ℝ)* (2*a*B) * (9/8:ℝ)^V.card
  let W := (V.card:ℝ)* (2*b*B) * (9/8:ℝ)^V.card
  let D := (V.card:ℝ)* (3*a*b) * (3/2:ℝ)^V.card
  have hdel (theta : Bool) (sigma : SignArray d h delta) :
      |(∏ i ∈ V, recordLikelihood (markedLaw h delta a b theta sigma) x s i) - A sigma*G sigma| ≤ D := by
    rw [← Finset.prod_mul_distrib]
    have hp := finite_product_perturbation_bound V
      (recordLikelihood (markedLaw h delta a b theta sigma) x s) (fun i => f sigma i*g sigma i)
      (3/2) (by norm_num) (fun i _ => (hrec theta sigma i).1)
      (fun i _ => by rw [abs_mul]; nlinarith [mul_le_mul (hf sigma i) (hg sigma i) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 9/8)])
    calc
      _ ≤ (3/2:ℝ)^V.card * ∑ i ∈ V, |recordLikelihood _ x s i-f sigma i*g sigma i| := hp
      _ ≤ (3/2:ℝ)^V.card * ∑ _i ∈ V, 3*a*b := by
        gcongr; exact (hrec theta sigma _).2
      _ = D := by simp [D, Finset.sum_const]; ring
  have hbound := finite_prior_contrast_deletion_bound
    (markedWeight h delta true) (markedWeight h delta false) A G _ _
    (marked_prior_mass d h delta true).1 (marked_prior_mass d h delta false).1
    (marked_prior_mass d h delta true).2 (marked_prior_mass d h delta false).2
    hA hG U W D D (by dsimp [U]; positivity) (by dsimp [W]; positivity)
    (fun sigma => finite_product_deviation_bound V (f sigma) (9/8) (2*a*B)
      (by norm_num) (fun i _ => hf sigma i) (fun i _ => hfd sigma i))
    (fun sigma => finite_product_deviation_bound V (g sigma) (9/8) (2*b*B)
      (by norm_num) (fun i _ => hg sigma i) (fun i _ => hgd sigma i))
    (hdel true) (hdel false)
  change |(∑ sigma, markedWeight h delta true sigma * ∏ i ∈ V, recordLikelihood _ x s i) -
    (∑ sigma, markedWeight h delta false sigma * ∏ i ∈ V, recordLikelihood _ x s i)| ≤ _
  refine hbound.trans ?_
  have hp := component_channel_power_bound V.card
  have hcard : (V.card:ℝ) ≤ (V.card:ℝ)^2 := by
    have hn : V.card = 0 ∨ 1 ≤ V.card := by omega
    rcases hn with hn | hn
    · simp [hn]
    · have hn' : (1:ℝ) ≤ V.card := by exact_mod_cast hn
      nlinarith
  have hab0 : 0 ≤ a*b := by positivity
  dsimp [D, U, W]
  clear hbound hrec hA hG hcommon hdel hf hg hfd hgd hfactor hpert
  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 8*B^2*(V.card:ℝ)^2*a*b by positivity),
    mul_le_mul_of_nonneg_right hcard (show 0 ≤ 6*a*b*(3/2:ℝ)^V.card by positivity)]

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
