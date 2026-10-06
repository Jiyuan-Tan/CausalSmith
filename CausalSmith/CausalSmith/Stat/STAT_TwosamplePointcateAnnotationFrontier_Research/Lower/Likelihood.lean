module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.MarkedHandle

/-!
# Lower/Likelihood

Two-channel point-CATE annotation frontier: Lower/Likelihood
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


variable {d n m : ℕ}
/-- Given [the specified input P](hyp:P), [the specified input x](hyp:x), [conditional observed](goal) is the corresponding construction. -/
def conditionalObserved (P : PrimitiveLaw d) (x : Cov d) : Measure (Bool × Bool) :=
  (bern (P.e x)).bind (fun A => (Measure.dirac A).prod (bern (if A then P.mu1 x else P.mu0 x)))
/-- Given [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [singleton mixture](goal) is the corresponding construction. -/
def singletonMixture (H : MarkedPriors d) (theta : Bool) (x : Cov d) : Measure (Bool × Bool) :=
  ∑ sigma, ENNReal.ofReal (H.weight theta sigma) • conditionalObserved (H.law theta sigma) x
/-- Given [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input k](hyp:k), [auxiliary mixture](goal) is the corresponding construction. -/
def auxiliaryMixture (H : MarkedPriors d) (theta : Bool) (k : ℕ) : Measure (Fin k → Cov d × Bool) :=
  ∑ sigma, ENNReal.ofReal (H.weight theta sigma) •
    Measure.pi (fun _ : Fin k => xaLaw (H.law theta sigma))
/-- Given [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input k](hyp:k), [the specified input x](hyp:x), [conditional auxiliary mixture](goal) is the corresponding construction. -/
def conditionalAuxiliaryMixture (H : MarkedPriors d) (theta : Bool) (k : ℕ)
    (x : Fin k → Cov d) : Measure (Fin k → Bool) :=
  ∑ sigma, ENNReal.ofReal (H.weight theta sigma) •
    Measure.pi (fun i : Fin k => bern ((H.law theta sigma).e (x i)))
/-- [fair observed](goal) is the corresponding construction. -/
def fairObserved : Measure (Bool × Bool) := (bern (1/2)).prod (bern (1/2))
/-- Given [the specified input P](hyp:P), [the specified input x](hyp:x), [the specified input s](hyp:s), [label likelihood](goal) is the corresponding construction. -/
def labelLikelihood (P : PrimitiveLaw d) (x : Cov d) (s : Bool × Bool) : ℝ :=
  4 * ((bern (P.e x)) {s.1}).toReal *
    ((bern (if s.1 then P.mu1 x else P.mu0 x)) {s.2}).toReal
/-- Given [the specified input P](hyp:P), [the specified input x](hyp:x), [the specified input s](hyp:s), [auxiliary likelihood](goal) is the corresponding construction. -/
def auxiliaryLikelihood (P : PrimitiveLaw d) (x : Cov d) (s : Bool) : ℝ :=
  2 * ((bern (P.e x)) {s}).toReal
/-- Given [the specified input n](hyp:n), [the specified input m](hyp:m), [record spins](goal) is the corresponding construction. -/
abbrev RecordSpins (n m : ℕ) := (Fin n → Bool × Bool) × (Fin m → Bool)
/-- Given [the specified input x](hyp:x), [the specified input xt](hyp:xt), [record covariates](goal) is the corresponding construction. -/
def recordCovariates (x : Fin n → Cov d) (xt : Fin m → Cov d) : Fin (n+m) → Cov d := Fin.addCases x xt
/-- Given [the specified input P](hyp:P), [the specified input x](hyp:x), [the specified input s](hyp:s), [record likelihood](goal) is the corresponding construction. -/
def recordLikelihood (P : PrimitiveLaw d) (x : Fin (n+m) → Cov d) (s : RecordSpins n m) : Fin (n+m) → ℝ :=
  Fin.addCases (fun i => labelLikelihood P (x (Fin.castAdd m i)) (s.1 i))
    (fun j => auxiliaryLikelihood P (x (Fin.natAdd n j)) (s.2 j))
/-- Given [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [the specified input s](hyp:s), [mixed density](goal) is the corresponding construction. -/
def mixedDensity (H : MarkedPriors d) (theta : Bool) (x : Fin (n+m) → Cov d) (s : RecordSpins n m) : ℝ :=
  ∑ sigma, H.weight theta sigma * ∏ i, recordLikelihood (H.law theta sigma) x s i
/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input theta](hyp:theta), [the marked prior mass conclusion](goal) holds. -/
lemma marked_prior_mass (d : ℕ) (h delta : ℝ) (theta : Bool) :
    (∀ sigma : SignArray d h delta, 0 ≤ markedWeight h delta theta sigma) ∧
    (∑ sigma : SignArray d h delta, markedWeight h delta theta sigma) = 1 := by
  constructor
  · intro sigma
    apply Finset.prod_nonneg
    intro z _
    rcases hs : sigma z with ⟨l, v⟩
    cases theta <;> cases l <;> cases v <;>
      norm_num [thetaSign, hs]
  · unfold markedWeight
    rw [← Fintype.prod_sum (fun (_ : {z // z ∈ frameIdx d h delta}) (s : Bool × Bool) =>
      (1 + thetaSign theta * thetaSign s.1 * thetaSign s.2 / 2) / 4)]
    have hpair : ∑ s : Bool × Bool,
        (1 + thetaSign theta * thetaSign s.1 * thetaSign s.2 / 2) / 4 = 1 := by
      cases theta <;> norm_num [Fintype.sum_prod_type, thetaSign]
    simp only [hpair, Finset.prod_const_one]
/-- Flip every outcome sign while retaining every propensity sign.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [flip outcome signs](goal) is the corresponding construction. -/
def flipOutcomeSigns (d : ℕ) (h delta : ℝ) : SignArray d h delta ≃ SignArray d h delta where
  toFun sigma z := ((sigma z).1, !(sigma z).2)
  invFun sigma z := ((sigma z).1, !(sigma z).2)
  left_inv sigma := by funext z; simp
  right_inv sigma := by funext z; simp

/-- The sign flip transports the positive prior weights to the negative weights.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input sigma](hyp:sigma), [the marked weight flip outcome signs conclusion](goal) holds. -/
lemma markedWeight_flipOutcomeSigns (d : ℕ) (h delta : ℝ)
    (sigma : SignArray d h delta) :
    markedWeight h delta true sigma =
      markedWeight h delta false (flipOutcomeSigns d h delta sigma) := by
  unfold markedWeight
  apply Finset.prod_congr rfl
  intro z _
  rcases hs : sigma z with ⟨l, v⟩
  cases l <;> cases v <;> norm_num [flipOutcomeSigns, thetaSign, hs]

/-- The designated propensity ignores outcome signs and the hypothesis index.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input sigma](hyp:sigma), [the marked propensity flip outcome signs conclusion](goal) holds. -/
lemma markedPropensity_flipOutcomeSigns (d : ℕ) (h delta a b : ℝ)
    (sigma : SignArray d h delta) :
    (markedLaw h delta a b true sigma).e =
      (markedLaw h delta a b false (flipOutcomeSigns d h delta sigma)).e := by
  rfl

/-- The treatment-record law depends only on the propensity, with the same uniform design.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input sigma](hyp:sigma), [the marked xa law flip outcome signs conclusion](goal) holds. -/
lemma marked_xaLaw_flipOutcomeSigns (d : ℕ) (h delta a b : ℝ)
    (sigma : SignArray d h delta) :
    xaLaw (markedLaw h delta a b true sigma) =
      xaLaw (markedLaw h delta a b false (flipOutcomeSigns d h delta sigma)) := by
  have hm (theta : Bool) (sigma : SignArray d h delta) :
      xaLaw (markedLaw h delta a b theta sigma) =
        (uniformLaw d) ⊗ₘ bernKernel (markedLaw h delta a b theta sigma).e
          (markedLaw h delta a b theta sigma).measurable_e := by
    rw [xaLaw, (markedLaw h delta a b theta sigma).margin_e]
    rw [show (markedLaw h delta a b theta sigma).law.map Prod.fst = uniformLaw d from
      independentFullLaw_covariates d _ _ _ (measurable_markedPropensity h delta a sigma)
        (measurable_markedMean h delta a b theta false sigma)
        (measurable_markedMean h delta a b theta true sigma)]
  rw [hm, hm]
  rfl

/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input k](hyp:k), [the auxiliary only equality conclusion](goal) holds. -/
lemma auxiliary_only_equality (d : ℕ) (h delta a b : ℝ) (k : ℕ) :
    let H := markedHandle d h delta a b
    auxiliaryMixture H true k = auxiliaryMixture H false k ∧
    ∀ x : Fin k → Cov d, conditionalAuxiliaryMixture H true k x = conditionalAuxiliaryMixture H false k x := by
  dsimp only
  constructor
  · unfold auxiliaryMixture
    apply Fintype.sum_equiv (flipOutcomeSigns d h delta)
    intro sigma
    change ENNReal.ofReal (markedWeight h delta true sigma) •
        Measure.pi (fun _ : Fin k => xaLaw (markedLaw h delta a b true sigma)) =
      ENNReal.ofReal (markedWeight h delta false (flipOutcomeSigns d h delta sigma)) •
        Measure.pi (fun _ : Fin k =>
          xaLaw (markedLaw h delta a b false (flipOutcomeSigns d h delta sigma)))
    rw [markedWeight_flipOutcomeSigns, marked_xaLaw_flipOutcomeSigns]
  · intro x
    unfold conditionalAuxiliaryMixture
    apply Fintype.sum_equiv (flipOutcomeSigns d h delta)
    intro sigma
    change ENNReal.ofReal (markedWeight h delta true sigma) •
        Measure.pi (fun i : Fin k => bern ((markedLaw h delta a b true sigma).e (x i))) =
      ENNReal.ofReal (markedWeight h delta false (flipOutcomeSigns d h delta sigma)) •
        Measure.pi (fun i : Fin k =>
          bern ((markedLaw h delta a b false (flipOutcomeSigns d h delta sigma)).e (x i)))
    rw [markedWeight_flipOutcomeSigns, markedPropensity_flipOutcomeSigns]
/-- Finite product weights turn expectations of coordinate products into products of scalar sums.  Given [the specified input S](hyp:S), [the specified input w](hyp:w), [the specified input f](hyp:f), [the finite product weighted sum conclusion](goal) holds. -/
lemma finite_product_weighted_sum {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S]
    (w f : ι → S → ℝ) :
    (∑ sigma : ι → S, (∏ i, w i (sigma i)) * ∏ i, f i (sigma i)) =
      ∏ i, ∑ s, w i s * f i s := by
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i s => w i s * f i s)).symm
/-- A normalized finite product prior has the prescribed scalar marginal at a coordinate.  Given [the specified input S](hyp:S), [the specified input w](hyp:w), [the specified input hw](hyp:hw), [the specified input z](hyp:z), [the specified input f](hyp:f), [the finite product coordinate sum conclusion](goal) holds. -/
lemma finite_product_coordinate_sum {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S]
    (w : ι → S → ℝ) (hw : ∀ i, ∑ s, w i s = 1) (z : ι) (f : S → ℝ) :
    (∑ sigma : ι → S, (∏ i, w i (sigma i)) * f (sigma z)) = ∑ s, w z s * f s := by
  classical
  have h := finite_product_weighted_sum w (fun i s => if i = z then f s else 1)
  simpa [hw] using h
/-- Each propensity or outcome sign has mean zero under the prescribed sign-pair prior.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input theta](hyp:theta), [the specified input control](hyp:control), [the specified input z](hyp:z), [the marked sign mean zero conclusion](goal) holds. -/
lemma marked_sign_mean_zero (d : ℕ) (h delta : ℝ) (theta control : Bool)
    (z : {z // z ∈ frameIdx d h delta}) :
    (∑ sigma : SignArray d h delta, markedWeight h delta theta sigma *
      thetaSign (if control then (sigma z).2 else (sigma z).1)) = 0 := by
  have hw (i : {z // z ∈ frameIdx d h delta}) :
      (∑ s : Bool × Bool, (1 + thetaSign theta * thetaSign s.1 * thetaSign s.2 / 2) / 4) = 1 := by
    cases theta <;> norm_num [Fintype.sum_prod_type, thetaSign]
  unfold markedWeight
  rw [finite_product_coordinate_sum _ hw z (fun s : Bool × Bool => thetaSign (if control then s.2 else s.1))]
  cases theta <;> cases control <;> norm_num [Fintype.sum_prod_type, thetaSign]
/-- Sign-pair correlation is one half the hypothesis sign at matching indices and zero otherwise.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input theta](hyp:theta), [the specified input z](hyp:z), [the specified input w](hyp:w), [the marked sign cross moment conclusion](goal) holds. -/
lemma marked_sign_cross_moment (d : ℕ) (h delta : ℝ) (theta : Bool)
    (z w : {z // z ∈ frameIdx d h delta}) :
    (∑ sigma : SignArray d h delta, markedWeight h delta theta sigma *
      (thetaSign (sigma z).1 * thetaSign (sigma w).2)) =
        if z = w then thetaSign theta / 2 else 0 := by
  classical
  let p := fun s : Bool × Bool =>
    (1 + thetaSign theta * thetaSign s.1 * thetaSign s.2 / 2) / 4
  have hfactor := finite_product_weighted_sum (fun _ : {z // z ∈ frameIdx d h delta} => p)
    (fun i s => (if i = z then thetaSign s.1 else 1) *
      (if i = w then thetaSign s.2 else 1))
  simp only [Finset.prod_mul_distrib] at hfactor
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true] at hfactor
  change (∑ sigma : SignArray d h delta, markedWeight h delta theta sigma *
    (thetaSign (sigma z).1 * thetaSign (sigma w).2)) = _ at hfactor
  rw [hfactor]
  have hs (i : {z // z ∈ frameIdx d h delta}) :
      (∑ s : Bool × Bool, p s * ((if i = z then thetaSign s.1 else 1) *
        (if i = w then thetaSign s.2 else 1))) =
      if i = z then (if z = w then thetaSign theta / 2 else 0)
      else if i = w then 0 else 1 := by
    by_cases hz : i = z
    · subst i
      by_cases hw : z = w <;> cases theta <;>
        norm_num [p, hw, Fintype.sum_prod_type, thetaSign]
    · by_cases hw : i = w
      · subst i
        cases theta <;> norm_num [p, hz, Fintype.sum_prod_type, thetaSign]
      · cases theta <;> norm_num [p, hz, hw, Fintype.sum_prod_type, thetaSign]
  simp_rw [hs]
  by_cases hzw : z = w
  · subst w
    simp only [ite_true]
    have heq (i : {z // z ∈ frameIdx d h delta}) :
        (if i = z then thetaSign theta / 2 else if i = z then 0 else 1) =
          (if i = z then thetaSign theta / 2 else 1) := by split_ifs <;> rfl
    simp_rw [heq]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  · rw [if_neg hzw]
    exact Finset.prod_eq_zero (Finset.mem_univ z) (by simp only [ite_true, if_neg hzw])
/-- Both signed frame fields have zero prior mean.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input theta](hyp:theta), [the specified input control](hyp:control), [the specified input x](hyp:x), [the marked field mean zero conclusion](goal) holds. -/
lemma marked_field_mean_zero (d : ℕ) (h delta : ℝ) (theta control : Bool) (x : Cov d) :
    (∑ sigma : SignArray d h delta, markedWeight h delta theta sigma *
      signField h delta sigma control x) = 0 := by
  unfold signField
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, marked_sign_mean_zero]
  simp only [zero_mul, Finset.sum_const_zero]
/-- The frame partition identifies the prior cross moment of the two signed fields.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input hd](hyp:hd), [the specified input hdh](hyp:hdh), [the specified input hh](hyp:hh), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [the marked field cross moment conclusion](goal) holds. -/
lemma marked_field_cross_moment (d : ℕ) (h delta : ℝ) (hd : 0 < delta) (hdh : delta ≤ h)
    (hh : h ≤ 1/2) (theta : Bool) (x : Cov d) :
    (∑ sigma : SignArray d h delta, markedWeight h delta theta sigma *
      (signField h delta sigma false x * signField h delta sigma true x)) =
        thetaSign theta / 2 * (macroBump h x)^2 := by
  classical
  simp only [signField, Bool.false_eq_true, if_false, if_true, Finset.sum_mul, Finset.mul_sum]
  have rearrange (sigma : SignArray d h delta) (z w : {z // z ∈ frameIdx d h delta}) :
      markedWeight h delta theta sigma *
        (thetaSign (sigma z).1 * frame h delta z.1 x *
          (thetaSign (sigma w).2 * frame h delta w.1 x)) =
      (markedWeight h delta theta sigma * (thetaSign (sigma z).1 * thetaSign (sigma w).2)) *
        (frame h delta z.1 x * frame h delta w.1 x) := by ring
  simp_rw [rearrange]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (f := fun sigma z =>
    (markedWeight h delta theta sigma * (thetaSign (sigma z).1 * thetaSign (sigma _).2)) *
      (frame h delta z.1 x * frame h delta _ x))]
  simp_rw [← Finset.sum_mul, marked_sign_cross_moment]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← pow_two]
  rw [← Finset.mul_sum, frame_square_partition h delta (lt_of_lt_of_le hd hdh) hh hd hdh]
/-- Compensation cancels the cross moment in the raw singleton likelihood, including its cubic term.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input hd](hyp:hd), [the specified input hdh](hyp:hdh), [the specified input hh](hyp:hh), [the specified input theta](hyp:theta), [the specified input u](hyp:u), [the specified input v](hyp:v), [the specified input x](hyp:x), [the marked raw singleton cancellation conclusion](goal) holds. -/
lemma marked_raw_singleton_cancellation (d : ℕ) (h delta a b : ℝ) (hd : 0 < delta) (hdh : delta ≤ h)
    (hh : h ≤ 1/2) (theta : Bool) (u v : ℝ) (x : Cov d) :
    (∑ sigma : SignArray d h delta, markedWeight h delta theta sigma *
      ((1 + 2*u*a*signField h delta sigma false x) *
        (1 + 2*v*b*signField h delta sigma true x + u*v*markedContrast h a b theta x))) = 1 := by
  have hp (sigma : SignArray d h delta) :
      markedWeight h delta theta sigma *
        ((1 + 2*u*a*signField h delta sigma false x) *
          (1 + 2*v*b*signField h delta sigma true x + u*v*markedContrast h a b theta x)) =
      markedWeight h delta theta sigma * (1 + u*v*markedContrast h a b theta x) +
        (2*u*a + 2*u^2*v*a*markedContrast h a b theta x) *
          (markedWeight h delta theta sigma * signField h delta sigma false x) +
        (2*v*b) * (markedWeight h delta theta sigma * signField h delta sigma true x) +
        (4*u*v*a*b) * (markedWeight h delta theta sigma *
          (signField h delta sigma false x * signField h delta sigma true x)) := by ring
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [(marked_prior_mass d h delta theta).2, marked_field_mean_zero, marked_field_mean_zero,
    marked_field_cross_moment d h delta hd hdh hh]
  unfold markedContrast
  ring
/-- The zero-order partial in the Hölder norm bounds the function on the design cube.  Given [the specified input d](hyp:d), [the specified input f](hyp:f), [the specified input s](hyp:s), [the specified input K](hyp:K), [the specified input hK](hyp:hK), [the specified input hf](hyp:hf), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the holder norm sup bound conclusion](goal) holds. -/
lemma holderNorm_sup_bound {d : ℕ} (f : Cov d → ℝ) (s K : ℝ) (hK : 0 ≤ K)
    (hf : holderNorm f s ≤ ENNReal.ofReal K) (x : Cov d) (hx : x ∈ cube d) : |f x| ≤ K := by
  have hb := ((holderNorm_le_iff f s K hK).mp hf).2.1 (fun _ => 0)
    (by simp [multiOrder]) x hx
  have hz : multiOrder (fun _ : Fin d => 0) = 0 := by simp [multiOrder]
  have hc : coordinatePartial f (fun _ => 0) x = f x := by
    unfold coordinatePartial
    generalize coordinateDirections (fun _ : Fin d => 0) = v
    revert v
    rw [hz]
    intro v
    exact iteratedFDerivWithin_zero_apply v
  rwa [hc] at hb
/-- A scale-controlled amplitude cancels the inverse scale in a Hölder supremum bound.  Given [the specified input r](hyp:r), [the specified input s](hyp:s), [the specified input c](hyp:c), [the specified input K](hyp:K), [the specified input a](hyp:a), [the specified input f](hyp:f), [the specified input hr](hyp:hr), [the specified input hc](hyp:hc), [the specified input hK](hyp:hK), [the specified input ha0](hyp:ha0), [the specified input ha](hyp:ha), [the specified input hf](hyp:hf), [the holder scaled amplitude bound conclusion](goal) holds. -/
lemma holder_scaled_amplitude_bound (r s c K a f : ℝ) (hr : 0 < r) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (ha0 : 0 ≤ a) (ha : a ≤ c*r^s) (hf : |f| ≤ K*r^(-s)) : |a*f| ≤ c*K := by
  rw [abs_mul, abs_of_nonneg ha0]
  calc
    a * |f| ≤ (c*r^s)*(K*r^(-s)) := mul_le_mul ha hf (abs_nonneg _) (by positivity)
    _ = c*K := by
      have hrpow : r^s*r^(-s) = 1 := by rw [← Real.rpow_add hr]; simp
      calc
        _ = c*K*(r^s*r^(-s)) := by ring
        _ = c*K := by rw [hrpow, mul_one]
/-- The frame field vanishes outside the design cube for an admissible localization window.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input hh0](hyp:hh0), [the specified input hh](hyp:hh), [the specified input sigma](hyp:sigma), [the specified input control](hyp:control), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the sign field zero outside cube conclusion](goal) holds. -/
lemma signField_zero_outside_cube (h delta : ℝ) (hh0 : 0 < h) (hh : h ≤ 1/2) (sigma : SignArray d h delta)
    (control : Bool) (x : Cov d) (hx : x ∉ cube d) : signField h delta sigma control x = 0 := by
  have hl : x ∉ locCube d h := by
    intro hl
    apply hx
    intro i
    have hi := hl i
    constructor <;> linarith [hi.1, hi.2]
  simp only [signField, frame, macroBump_zero_outside h hh0 x hl, zero_mul, mul_zero,
    Finset.sum_const_zero]
/-- The macro bump vanishes outside the design cube for an admissible localization window.  Given [the specified input h](hyp:h), [the specified input hh0](hyp:hh0), [the specified input hh](hyp:hh), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the macro bump zero outside cube conclusion](goal) holds. -/
lemma macroBump_zero_outside_cube (h : ℝ) (hh0 : 0 < h) (hh : h ≤ 1/2) (x : Cov d) (hx : x ∉ cube d) : macroBump h x = 0 := by
  apply macroBump_zero_outside h hh0
  intro hl
  apply hx
  intro i
  have hi := hl i
  constructor <;> linarith [hi.1, hi.2]
/-- A public positive amplitude constant keeps the raw propensity and arm means in the unit interval.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the marked raw probability bounds conclusion](goal) holds. -/
lemma marked_raw_probability_bounds (d : ℕ) (alpha beta gamma L eps : ℝ) (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ h delta a b,
      0 < delta → delta ≤ h → h ≤ 1/2 → 0 < a → a ≤ c*delta^alpha →
      0 < b → b ≤ c*delta^beta → a*b ≤ c*h^gamma →
      ∀ theta (sigma : SignArray d h delta) (x : Cov d), markedPropensity h delta a sigma x ∈ Set.Icc (0:ℝ) 1 ∧
        ∀ arm, markedMean h delta a b theta arm sigma x ∈ Set.Icc (0:ℝ) 1 := by
  let B : ℝ := (2:ℝ)^d
  let c : ℝ := 1/(64*B)
  have hB : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hBp : 0 < B := by positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hcB : c*B = 1/64 := by dsimp [c]; field_simp
  have hcsmall : c ≤ 1/64 := by nlinarith
  refine ⟨c, hc, by linarith, ?_⟩
  intro h delta a b hd hdh hh ha hac hb hbc hab theta sigma x
  have hd1 : delta ≤ 1 := by linarith
  have haC : a ≤ c := hac.trans (by
    simpa using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one hd.le hd1 hdom.2.1.le) hc.le)
  have hbC : b ≤ c := hbc.trans (by
    simpa using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one hd.le hd1 hdom.2.2.2.1.le) hc.le)
  have he : a*(2:ℝ)^d ≤ 1/4 := by change a*B ≤ _; nlinarith
  have hm : b*(2:ℝ)^d+a*b ≤ 3/8 := by
    have habsmall := mul_le_mul haC hbC hb.le hc.le
    change b*B+a*b ≤ _
    nlinarith
  have hp := markedPropensity_overlap h delta a sigma ha.le he x
  refine ⟨⟨by linarith [hp.1], by linarith [hp.2]⟩, ?_⟩
  intro arm
  have hmean := markedMean_interior h delta a b theta arm sigma ha.le hb.le hm x
  exact ⟨by linarith [hmean.1], by linarith [hmean.2]⟩
/-- A valid Bernoulli atom equals its affine fair-spin likelihood divided by two.  Given [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the specified input s](hyp:s), [the bern singleton to real spin conclusion](goal) holds. -/
lemma bern_singleton_toReal_spin (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Bool) :
    (bern p {s}).toReal = (1 + thetaSign s*(2*p-1))/2 := by
  cases s <;> simp [bern, thetaSign, ENNReal.toReal_ofReal hp.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)] <;> ring
/-- For valid raw probabilities the marked label likelihood is the compensated two-spin product.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input sigma](hyp:sigma), [the specified input x](hyp:x), [the specified input hp](hyp:hp), [the specified input hm](hyp:hm), [the specified input s](hyp:s), [the marked label likelihood spin conclusion](goal) holds. -/
lemma marked_labelLikelihood_spin (d : ℕ) (h delta a b : ℝ) (theta : Bool) (sigma : SignArray d h delta)
    (x : Cov d) (hp : markedPropensity h delta a sigma x ∈ Set.Icc (0:ℝ) 1)
    (hm : ∀ arm, markedMean h delta a b theta arm sigma x ∈ Set.Icc (0:ℝ) 1)
    (s : Bool × Bool) :
    labelLikelihood (markedLaw h delta a b theta sigma) x s =
      (1+2*thetaSign s.1*a*signField h delta sigma false x) *
        (1+2*thetaSign s.2*b*signField h delta sigma true x +
          thetaSign s.1*thetaSign s.2*markedContrast h a b theta x) := by
  unfold labelLikelihood
  change 4*(bern (probabilityClip (markedPropensity h delta a sigma x)) {s.1}).toReal *
    (bern (if s.1 then probabilityClip (markedMean h delta a b theta true sigma x)
      else probabilityClip (markedMean h delta a b theta false sigma x)) {s.2}).toReal = _
  rw [probabilityClip_eq_of_mem _ hp, probabilityClip_eq_of_mem _ (hm true), probabilityClip_eq_of_mem _ (hm false)]
  rw [bern_singleton_toReal_spin _ hp, bern_singleton_toReal_spin _ (by cases s.1 <;> simpa using hm _)]
  rcases s with ⟨A,Y⟩
  cases A <;> cases Y <;> simp [thetaSign, markedPropensity, markedMean] <;> ring

/-- The conditional observed atom factors into its treatment and selected outcome atoms.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input x](hyp:x), [the specified input s](hyp:s), [the conditional observed singleton conclusion](goal) holds. -/
lemma conditionalObserved_singleton {d : ℕ} (P : PrimitiveLaw d) (x : Cov d) (s : Bool × Bool) :
    conditionalObserved P x {s} =
      bern (P.e x) {s.1} * bern (if s.1 then P.mu1 x else P.mu0 x) {s.2} := by
  rw [conditionalObserved, Measure.bind_apply (measurableSet_singleton s)
    (measurable_of_countable _).aemeasurable]
  rcases s with ⟨A,Y⟩
  cases A <;> cases Y <;>
    simp [bern, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
      ← singleton_prod_singleton, Measure.prod_prod]
/-- Each Bernoulli atom has finite mass, including for total raw inputs.  Given [the specified input p](hyp:p), [the specified input s](hyp:s), [the bern singleton ne top conclusion](goal) holds. -/
lemma bern_singleton_ne_top (p : ℝ) (s : Bool) : bern p {s} ≠ ⊤ := by
  cases s <;> simp [bern]

/-- The fair-spin density of a singleton mixture is its prior-weighted label likelihood.  Given [the specified input d](hyp:d), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input hw](hyp:hw), [the specified input x](hyp:x), [the specified input s](hyp:s), [the singleton mixture density conclusion](goal) holds. -/
lemma singletonMixture_density {d : ℕ} (H : MarkedPriors d) (theta : Bool)
    (hw : ∀ sigma, 0 ≤ H.weight theta sigma) (x : Cov d) (s : Bool × Bool) :
    4 * (singletonMixture H theta x {s}).toReal =
      ∑ sigma, H.weight theta sigma * labelLikelihood (H.law theta sigma) x s := by
  unfold singletonMixture
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  have hfinite (sigma : PriorSign H) :
      ENNReal.ofReal (H.weight theta sigma) * conditionalObserved (H.law theta sigma) x {s} ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    rw [conditionalObserved_singleton]
    exact ENNReal.mul_ne_top (bern_singleton_ne_top _ _) (bern_singleton_ne_top _ _)
  rw [ENNReal.toReal_sum (fun sigma _ => hfinite sigma), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw sigma),
    conditionalObserved_singleton, ENNReal.toReal_mul]
  unfold labelLikelihood
  ring

/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the singleton cancellation conclusion](goal) holds. -/
lemma singleton_cancellation (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c : ℝ, 0 < c ∧ -- @realizes c(positive claim-local constant)
       c ≤ 1 ∧ ∀ h delta a b,
      0 < delta → delta ≤ h → h ≤ 1/2 → 0 < a → a ≤ c*delta^alpha →
      0 < b → b ≤ c*delta^beta → a*b ≤ c*h^gamma →
      ∀ theta x, singletonMixture (markedHandle d h delta a b) theta x = fairObserved := by
  obtain ⟨c, hc, hc1, hraw⟩ := marked_raw_probability_bounds d alpha beta gamma L eps hdom
  refine ⟨c, hc, hc1, ?_⟩
  intro h delta a b hd hdh hh ha hac hb hbc hab theta x
  apply Measure.ext_iff_singleton.mpr
  intro s
  have hw := (marked_prior_mass d h delta theta).1
  have hdensity := singletonMixture_density (markedHandle d h delta a b) theta hw x s
  have hl (sigma : SignArray d h delta) := marked_labelLikelihood_spin d h delta a b theta sigma x
    (hraw h delta a b hd hdh hh ha hac hb hbc hab theta sigma x).1
    (hraw h delta a b hd hdh hh ha hac hb hbc hab theta sigma x).2 s
  change 4*(singletonMixture (markedHandle d h delta a b) theta x {s}).toReal =
    ∑ sigma : SignArray d h delta, markedWeight h delta theta sigma *
      labelLikelihood (markedLaw h delta a b theta sigma) x s at hdensity
  simp_rw [hl] at hdensity
  rw [marked_raw_singleton_cancellation d h delta a b hd hdh hh] at hdensity
  have hfin : singletonMixture (markedHandle d h delta a b) theta x {s} ≠ ⊤ := by
    unfold singletonMixture
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    apply ENNReal.sum_ne_top.mpr
    intro sigma _
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    rw [conditionalObserved_singleton]
    exact ENNReal.mul_ne_top (bern_singleton_ne_top _ _) (bern_singleton_ne_top _ _)
  have hfair : fairObserved {s} = ENNReal.ofReal (1/4 : ℝ) := by
    rcases s with ⟨A,Y⟩
    cases A <;> cases Y <;>
      norm_num [fairObserved, ← singleton_prod_singleton, Measure.prod_prod, bern,
        ← ENNReal.ofReal_mul]
  rw [hfair]
  apply (ENNReal.toReal_eq_toReal_iff' hfin ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1/4:ℝ))]
  linarith

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
