module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Kernel
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Rate
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Witness

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


/-- The initial segment of odd weights has square total mass. Given [the displayed inputs and assumptions](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma oddWeight_sum_range (n : ℕ) :
    (∑ j ∈ Finset.range n, (2 * (j : ℝ) + 1)) = (n : ℝ)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The Legendre block normalizer is its total positive weight. Given [the displayed inputs and assumptions](hyp:m), [the stated mathematical conclusion holds](goal). -/
lemma blockNorm_sum (m : ℕ) :
    (∑ j ∈ Finset.Icc m (2*m), (2 * (j : ℝ) + 1)) = blockNorm m := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (by omega),
    oddWeight_sum_range, oddWeight_sum_range]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  norm_num [blockNorm]

/-- Endpoint signs cancel in the normalized Legendre block. Given [the displayed inputs and assumptions](hyp:legendre_of_gate,m), [the stated mathematical conclusion holds](goal). -/
lemma block_zero (legendre_of_gate : ClassicalLegendreFacts) (m : ℕ) : block m 0 = 1 := by
  have hs : (∑ j ∈ Finset.Icc m (2*m),
      (2 * (j : ℝ) + 1) * (-1 : ℝ)^j * legendreP j (-1)) = blockNorm m := by
    calc
      _ = ∑ j ∈ Finset.Icc m (2*m), (2 * (j : ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [(legendre_of_gate j 0).2.2.2, mul_assoc, ← mul_pow]
        simp
      _ = blockNorm m := blockNorm_sum m
  simpa [block, hs, (blockNorm_pos m).ne'] using
    (inv_mul_cancel₀ (blockNorm_pos m).ne')

/-- The taper vanishes at the right endpoint. Given [the displayed inputs and assumptions](hyp:m), [the stated mathematical conclusion holds](goal). -/
lemma block_one (m : ℕ) : block m 1 = 0 := by
  simp [block]

/-- The cited Legendre unit bound controls the tapered block on the whole unit interval. Given [the displayed inputs and assumptions](hyp:legendre_of_gate,m,t,ht), [the stated mathematical conclusion holds](goal). -/
lemma block_abs_le_one (legendre_of_gate : ClassicalLegendreFacts) (m : ℕ)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |block m t| ≤ 1 := by
  have hleg (j : ℕ) : |legendreP j (2*t-1)| ≤ 1 :=
    (legendre_of_gate j 0).2.2.1 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsum : |∑ j ∈ Finset.Icc m (2*m),
      (2 * (j : ℝ) + 1) * (-1 : ℝ)^j * legendreP j (2*t-1)| ≤ blockNorm m := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc m (2*m),
          |(2 * (j : ℝ) + 1) * (-1 : ℝ)^j * legendreP j (2*t-1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Icc m (2*m), (2 * (j : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hw : 0 ≤ 2 * (j : ℝ) + 1 := by positivity
        simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
          abs_of_nonneg hw]
        exact mul_le_of_le_one_right hw (hleg j)
      _ = blockNorm m := blockNorm_sum m
  have hn := blockNorm_pos m
  have htaper : |1-t| ≤ 1 := by rw [abs_of_nonneg (by linarith [ht.2])]; linarith [ht.1]
  unfold block
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ 1 * (blockNorm m)⁻¹ * blockNorm m :=
      mul_le_mul (mul_le_mul_of_nonneg_right htaper (le_of_lt (inv_pos.mpr hn))) hsum
        (abs_nonneg _) (by positivity)
    _ = 1 := by simp [hn.ne']

/-- The legal continuation retains the normalized cutoff value. Given [the displayed inputs and assumptions](hyp:legendre_of_gate,b,m,hb), [the stated mathematical conclusion holds](goal). -/
lemma legalExtension_zero (legendre_of_gate : ClassicalLegendreFacts)
    (b : ℝ) (m : ℕ) (hb : 0 ≤ b) : legalExtension b m 0 = 1 := by
  simp [legalExtension, hb, block_zero legendre_of_gate m]

/-- The explicitly constructed alternative has the displayed cutoff effect. Given [the displayed inputs and assumptions](hyp:legendre_of_gate,β,b,m,s,hβ,hb,hm), [the stated mathematical conclusion holds](goal). -/
lemma theta_altLaw (legendre_of_gate : ClassicalLegendreFacts)
    (β b : ℝ) (m : ℕ) (s : Bool) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    theta (altLaw legendre_of_gate β b m s hβ hb hm) = witnessSign s * kappa * (b/(m : ℝ)^2)^β := by
  simp [theta, altLaw, bernoulliWitness, witnessMu, altProbability,
    legalExtension_zero legendre_of_gate b m hb.1.le]

/-- Opposite Bernoulli perturbations have twice the positive cutoff amplitude. Given [the displayed inputs and assumptions](hyp:legendre_of_gate,β,b,m,hβ,hb,hm), [the stated mathematical conclusion holds](goal). -/
lemma altLaw_separation (legendre_of_gate : ClassicalLegendreFacts)
    (β b : ℝ) (m : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    |theta (altLaw legendre_of_gate β b m true hβ hb hm) - theta (altLaw legendre_of_gate β b m false hβ hb hm)| =
      2 * kappa * (b/(m : ℝ)^2)^β := by
  rw [theta_altLaw legendre_of_gate, theta_altLaw legendre_of_gate]
  simp only [witnessSign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
  have ha : 0 ≤ kappa * (b/(m : ℝ)^2)^β := by
    apply mul_nonneg (by norm_num [kappa])
    exact Real.rpow_nonneg (div_nonneg hb.1.le (sq_nonneg _)) _
  rw [abs_of_nonneg (by linarith)]
  ring

/-- The unnormalized Legendre block before the endpoint taper. Given [the displayed inputs and assumptions](hyp:m,t), [this definition specifies the stated object](goal). -/
def legendreBlockSum (m : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc m (2*m), (2*(j : ℝ)+1) * (-1 : ℝ)^j * legendreP j (2*t-1)
/-- Given the [polynomial degree](hyp:m), the finite Legendre block is [continuous on the real line](goal). -/
@[fun_prop] lemma legendreBlockSum_continuous (m : ℕ) : Continuous (legendreBlockSum m) := by
  unfold legendreBlockSum
  fun_prop
/-- Orthogonality leaves precisely the sum of odd weights in the squared block integral. Given [the displayed inputs and assumptions](hyp:hleg,m), [the stated mathematical conclusion holds](goal). -/
lemma legendreBlockSum_sq_integral (hleg : ClassicalLegendreFacts) (m : ℕ) :
    (∫ t in (0 : ℝ)..1, (legendreBlockSum m t)^2) = blockNorm m := by
  have hint (j k : ℕ) : IntervalIntegrable (fun t : ℝ =>
      ((2*(j : ℝ)+1) * (-1 : ℝ)^j * legendreP j (2*t-1)) *
      ((2*(k : ℝ)+1) * (-1 : ℝ)^k * legendreP k (2*t-1))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpair (j k : ℕ) : (∫ t in (0 : ℝ)..1,
      ((2*(j : ℝ)+1) * (-1 : ℝ)^j * legendreP j (2*t-1)) *
      ((2*(k : ℝ)+1) * (-1 : ℝ)^k * legendreP k (2*t-1))) =
      if j = k then 2*(j : ℝ)+1 else 0 := by
    calc
      _ = ((2*(j : ℝ)+1) * (-1 : ℝ)^j * ((2*(k : ℝ)+1) * (-1 : ℝ)^k)) *
          (∫ t in (0 : ℝ)..1, legendreP j (2*t-1) * legendreP k (2*t-1)) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        ext t
        ring
      _ = _ := by
        rw [shiftedLegendre_orthogonal hleg]
        split_ifs with h
        · subst k
          have hw : 2*(j : ℝ)+1 ≠ 0 := by positivity
          have hsign : (-1 : ℝ)^j * (-1 : ℝ)^j = 1 := by rw [← mul_pow]; norm_num
          field_simp
          nlinarith
        · ring
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ j ∈ Finset.Icc m (2*m), ∑ k ∈ Finset.Icc m (2*m),
        ((2*(j : ℝ)+1) * (-1 : ℝ)^j * legendreP j (2*t-1)) *
        ((2*(k : ℝ)+1) * (-1 : ℝ)^k * legendreP k (2*t-1)) := by
      congr 1
      ext t
      simp only [legendreBlockSum, pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.Icc m (2*m), ∑ k ∈ Finset.Icc m (2*m),
        if j = k then 2*(j : ℝ)+1 else 0 := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [intervalIntegral.integral_finsetSum (fun k hk => hint j k)]
        exact Finset.sum_congr rfl (fun k hk => hpair j k)
      · intro j hj
        apply Continuous.intervalIntegrable
        fun_prop
    _ = blockNorm m := by
      simp only [Finset.sum_ite_eq, Finset.mem_Icc]
      have : (∑ j ∈ Finset.Icc m (2*m),
          if m ≤ j ∧ j ≤ 2*m then 2*(j : ℝ)+1 else 0) =
          ∑ j ∈ Finset.Icc m (2*m), (2*(j : ℝ)+1) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [Finset.mem_Icc.mp hj]
      rw [this, blockNorm_sum]
/-- The normalized untapered block has squared mass equal to its inverse normalizer. Given [the displayed inputs and assumptions](hyp:hleg,m), [the stated mathematical conclusion holds](goal). -/
lemma normalizedBlock_sq_integral (hleg : ClassicalLegendreFacts) (m : ℕ) :
    (∫ t in (0 : ℝ)..1, ((blockNorm m)⁻¹ * legendreBlockSum m t)^2) =
      1 / blockNorm m := by
  calc
    _ = (blockNorm m)⁻¹^2 * (∫ t in (0 : ℝ)..1, (legendreBlockSum m t)^2) := by
      simp_rw [mul_pow]
      rw [intervalIntegral.integral_const_mul]
    _ = 1 / blockNorm m := by
      rw [legendreBlockSum_sq_integral hleg]
      field_simp [(blockNorm_pos m).ne']
/-- Tapering the normalized block cannot increase its squared mass on the unit interval. Given [the displayed inputs and assumptions](hyp:hleg,m), [the stated mathematical conclusion holds](goal). -/
lemma block_sq_integral_le (hleg : ClassicalLegendreFacts) (m : ℕ) :
    (∫ t in (0 : ℝ)..1, (block m t)^2) ≤ 1 / blockNorm m := by
  rw [← normalizedBlock_sq_integral hleg m]
  have hc : Continuous (block m) := by
    unfold block
    fun_prop
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((hc.pow 2).intervalIntegrable _ _) (by
      apply Continuous.intervalIntegrable
      fun_prop)
  intro t ht
  have htaper : (1-t)^2 ≤ 1 := by nlinarith [ht.1, ht.2]
  change ((1-t) * (blockNorm m)⁻¹ * legendreBlockSum m t)^2 ≤ _
  calc
    _ = (1-t)^2 * ((blockNorm m)⁻¹ * legendreBlockSum m t)^2 := by ring
    _ ≤ 1 * ((blockNorm m)⁻¹ * legendreBlockSum m t)^2 :=
      mul_le_mul_of_nonneg_right htaper (sq_nonneg _)
    _ = _ := one_mul _

/-- Given the [polynomial degree](hyp:m), the untapered finite Legendre block is [differentiable on the real line](goal). -/
@[fun_prop] lemma legendreBlockSum_differentiable (m : ℕ) :
    Differentiable ℝ (legendreBlockSum m) := by
  change Differentiable ℝ (fun t => ∑ j ∈ Finset.Icc m (2*m),
    (2*(j : ℝ)+1) * (-1 : ℝ)^j * shiftedLegendre j t)
  fun_prop

/-- The untapered normalized block has absolute value at most one. Given [the displayed inputs and assumptions](hyp:hleg,m,t,ht), [the stated mathematical conclusion holds](goal). -/
lemma normalizedBlock_abs_le_one (hleg : ClassicalLegendreFacts) (m : ℕ)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |(blockNorm m)⁻¹ * legendreBlockSum m t| ≤ 1 := by
  have hsum : |legendreBlockSum m t| ≤ blockNorm m := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc m (2*m),
          |(2*(j : ℝ)+1) * (-1 : ℝ)^j * legendreP j (2*t-1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Icc m (2*m), (2*(j : ℝ)+1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hw : 0 ≤ 2*(j : ℝ)+1 := by positivity
        simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
          abs_of_nonneg hw]
        exact mul_le_of_le_one_right hw ((hleg j 0).2.2.1 _
          ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      _ = blockNorm m := blockNorm_sum m
  rw [abs_mul, abs_of_pos (inv_pos.mpr (blockNorm_pos m))]
  calc
    _ ≤ (blockNorm m)⁻¹ * blockNorm m :=
      mul_le_mul_of_nonneg_left hsum (inv_pos.mpr (blockNorm_pos m)).le
    _ = 1 := inv_mul_cancel₀ (blockNorm_pos m).ne'

/-- The derivative of the untapered block is bounded by its total weight times
    the largest shifted Legendre derivative in the block. Given [the displayed inputs and assumptions](hyp:hleg,m,hm,t,ht), [the stated mathematical conclusion holds](goal). -/
lemma legendreBlockSum_deriv_bound (hleg : ClassicalLegendreFacts) (m : ℕ)
    (hm : 2 ≤ m) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |deriv (legendreBlockSum m) t| ≤ blockNorm m * ((2*(m : ℝ))*(2*m+1)) := by
  have hd : deriv (legendreBlockSum m) t = ∑ j ∈ Finset.Icc m (2*m),
      ((2*(j : ℝ)+1) * (-1 : ℝ)^j) * deriv (shiftedLegendre j) t := by
    change deriv (fun t => ∑ j ∈ Finset.Icc m (2*m),
      ((2*(j : ℝ)+1) * (-1 : ℝ)^j) * shiftedLegendre j t) t = _
    rw [deriv_fun_sum (fun j hj =>
      (shiftedLegendre_differentiable j t).const_mul _)]
    simp only [deriv_const_mul_field]
  rw [hd]
  calc
    _ ≤ ∑ j ∈ Finset.Icc m (2*m),
        |((2*(j : ℝ)+1) * (-1 : ℝ)^j) * deriv (shiftedLegendre j) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc m (2*m),
        (2*(j : ℝ)+1) * ((2*(m : ℝ))*(2*m+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjm := Finset.mem_Icc.mp hj
      have hjpos : 1 ≤ j := by omega
      have hjle : (j : ℝ) ≤ 2*(m : ℝ) := by exact_mod_cast hjm.2
      have hbound := (shifted_legendre_derivative j hjpos).2 t ht
      have hw : 0 ≤ 2*(j : ℝ)+1 := by positivity
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
        abs_of_nonneg hw]
      apply mul_le_mul_of_nonneg_left (hbound.trans ?_) hw
      exact mul_le_mul hjle (by linarith) (by positivity) (by positivity)
    _ = blockNorm m * ((2*(m : ℝ))*(2*m+1)) := by
      rw [← Finset.sum_mul, blockNorm_sum]

/-- Differentiating the endpoint taper gives the paper's uniform derivative bound. Given [the displayed inputs and assumptions](hyp:hleg,m,hm,t,ht), [the stated mathematical conclusion holds](goal). -/
lemma block_deriv_bound (hleg : ClassicalLegendreFacts) (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |deriv (block m) t| ≤ 7*(m : ℝ)^2 := by
  have hd : deriv (block m) t =
      -((blockNorm m)⁻¹ * legendreBlockSum m t) +
      (1-t) * ((blockNorm m)⁻¹ * deriv (legendreBlockSum m) t) := by
    change deriv (fun t => (1-t) * (blockNorm m)⁻¹ * legendreBlockSum m t) t = _
    have ha : HasDerivAt (fun t : ℝ => (1-t) * (blockNorm m)⁻¹)
        (-(blockNorm m)⁻¹) t := by
      simpa using ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const
        ((blockNorm m)⁻¹)
    calc
      _ = -((blockNorm m)⁻¹) * legendreBlockSum m t +
          ((1-t) * (blockNorm m)⁻¹) * deriv (legendreBlockSum m) t :=
        (ha.fun_mul (legendreBlockSum_differentiable m t).hasDerivAt).deriv
      _ = _ := by ring
  have hn : 0 < blockNorm m := blockNorm_pos m
  have hnorm : |(blockNorm m)⁻¹ * deriv (legendreBlockSum m) t| ≤
      (2*(m : ℝ))*(2*m+1) := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hn)]
    calc
      _ ≤ (blockNorm m)⁻¹ * (blockNorm m * ((2*(m : ℝ))*(2*m+1))) :=
        mul_le_mul_of_nonneg_left (legendreBlockSum_deriv_bound hleg m hm t ht)
          (by positivity)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
  have htaper : |1-t| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [ht.2])]
    linarith [ht.1]
  rw [hd]
  calc
    _ ≤ |(blockNorm m)⁻¹ * legendreBlockSum m t| +
        |(1-t) * ((blockNorm m)⁻¹ * deriv (legendreBlockSum m) t)| := by
      simpa only [abs_neg] using abs_add_le
        (-((blockNorm m)⁻¹ * legendreBlockSum m t))
        ((1-t) * ((blockNorm m)⁻¹ * deriv (legendreBlockSum m) t))
    _ ≤ 1 + (2*(m : ℝ))*(2*m+1) := by
      apply add_le_add (normalizedBlock_abs_le_one hleg m t ht)
      rw [abs_mul]
      calc
        _ ≤ 1 * |(blockNorm m)⁻¹ * deriv (legendreBlockSum m) t| :=
          mul_le_mul_of_nonneg_right htaper (abs_nonneg _)
        _ ≤ _ := by simpa using hnorm
    _ ≤ 7*(m : ℝ)^2 := by
      have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith [sq_nonneg ((m : ℝ)-1)]

/-- The endpoint taper increases degree by at most one, so all prescribed monomials
remain orthogonal to every Legendre mode in the block. Given [the displayed inputs and assumptions](hyp:hleg,m,k,hm,hk), [the stated mathematical conclusion holds](goal). -/
lemma block_moment_zero (hleg : ClassicalLegendreFacts) (m k : ℕ)
    (hm : 2 ≤ m) (hk : k ≤ m-2) :
    (∫ t in (0 : ℝ)..1, t^k * block m t) = 0 := by
  let p : Polynomial ℝ := Polynomial.X ^ k * (1 - Polynomial.X)
  have hp : p.natDegree ≤ k+1 := by
    calc
      _ ≤ (Polynomial.X ^ k : Polynomial ℝ).natDegree +
          (1 - Polynomial.X : Polynomial ℝ).natDegree := Polynomial.natDegree_mul_le
      _ ≤ k+1 := by
        simp only [Polynomial.natDegree_X_pow]
        have h := Polynomial.natDegree_sub_le (1 : Polynomial ℝ) Polynomial.X
        simp only [Polynomial.natDegree_one, Polynomial.natDegree_X, max_eq_right (by omega : 0 ≤ 1)] at h
        omega
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc m (2*m)) :
      (∫ t in (0 : ℝ)..1, t^k * (1-t) * legendreP j (2*t-1)) = 0 := by
    have hkj : k+1 < j := by have := Finset.mem_Icc.mp hj; omega
    have hdeg : p.degree < j := lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast (lt_of_le_of_lt hp hkj))
    simpa [p] using polynomial_shiftedLegendre_orthogonal hleg p j hdeg
  calc
    _ = (blockNorm m)⁻¹ * ∑ j ∈ Finset.Icc m (2*m),
        ((2*(j : ℝ)+1) * (-1 : ℝ)^j) *
        (∫ t in (0 : ℝ)..1, t^k * (1-t) * legendreP j (2*t-1)) := by
      unfold block
      simp_rw [Finset.mul_sum]
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
        congr 1
        ext t
        ring
      · intro j hj
        apply Continuous.intervalIntegrable
        fun_prop
    _ = 0 := by
      rw [Finset.sum_eq_zero (fun j hj => by rw [hterm j hj, mul_zero]), mul_zero]

end CausalSmith.Stat.RdTruesideNoiseFrontier
