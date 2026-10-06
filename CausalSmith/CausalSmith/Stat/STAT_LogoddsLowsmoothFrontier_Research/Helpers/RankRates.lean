module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_FixedBudgetRealization

/-! # Deterministic rank and radius rates

The represented rank bounds imply uniform bias and noise rates. These estimates
use only the rank-budget contract, independently of endpoint realization.
-/
public section
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Rank selection obeys the exact target and its threefold upper bound.](goal) Under [the stated assumptions](hyp:hE,hN,hn,hab). -/
-- @node: resolutions_target_bounds
lemma resolutions_target_bounds (E : ArithmeticEngine) (hE : E.Admissible)
    (N : NamingPolicy) (hN : N.Admissible) (n : ℕ) (hn : 2 ≤ n)
    (α β : ℝ) (hab : ExponentDomain α β) :
    let k := resolutions E N n α β
    (n : ℝ)^(2/(2*α+2*β+1)) ≤ k.1 ∧
    (k.1 : ℝ) ≤ 3*(n : ℝ)^(2/(2*α+2*β+1)) ∧
    (n : ℝ)^(2/(4*β+1)) ≤ k.2 ∧
    (k.2 : ℝ) ≤ 3*(n : ℝ)^(2/(4*β+1)) := by
  obtain ⟨c, s, hr, hc, hs, hwc, hws⟩ :=
    rankBoxes_rank_budget_contract E hE N hN n (by omega) α β hab
  obtain ⟨hco, hso⟩ := rank_targets_one_le n hn α β hab
  obtain ⟨hcl, hcu, hct⟩ := enclosure_ceiling_rank_bounds c _ hco hc hwc
  obtain ⟨hsl, hsu, hst⟩ := enclosure_ceiling_rank_bounds s _ hso hs hws
  simpa only [resolutions, hr] using
    And.intro hcl (And.intro (hcu.le.trans hct) (And.intro hsl (hsu.le.trans hst)))

/-- [The ordered-pair denominator is at least half the squared sample size.](goal) Under [the stated assumptions](hyp:hn). -/
-- @node: sample_pair_denominator_lower
lemma sample_pair_denominator_lower (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ)^2/2 ≤ (n : ℝ)*((n : ℝ)-1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- [Bias at a rank above its target has exactly the balanced power rate.](goal) Under [the stated assumptions](hyp:x,hx,hs). Under [the stated assumptions](hyp:hk). -/
-- @node: rank_bias_power_bound
lemma rank_bias_power_bound (x k s : ℝ) (hx : 1 ≤ x) (hs : 0 < s)
    (hk : x^(2/(2*s+1)) ≤ k) :
    k^(-s) ≤ x^(-(2*s/(2*s+1))) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx0 _) hk (by linarith : -s ≤ 0)
  rw [← Real.rpow_mul hx0.le] at h
  convert h using 1 <;> congr 1 <;> ring

/-- [A selected rank at most three times its target gives a uniform noise rate.](goal) Under [the stated assumptions](hyp:hn,hs). Under [the stated assumptions](hyp:hk). -/
-- @node: rank_noise_power_bound
lemma rank_noise_power_bound (n k : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s)
    (hk : (k : ℝ) ≤ 3*(n : ℝ)^(2/(2*s+1))) :
    Real.sqrt (20*varianceRadius n k) ≤
      40*((n : ℝ)^(-(1/2 : ℝ))+(n : ℝ)^(-(2*s/(2*s+1)))) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos hn0
  have hden := sample_pair_denominator_lower n hn
  have hden0 : 0 < (n : ℝ)*((n : ℝ)-1) := by nlinarith
  have hv : 20*varianceRadius n k ≤
      200/(n : ℝ)+480*((n : ℝ)^(2/(2*s+1))/(n : ℝ)^2) := by
    have hd : 4*(k : ℝ)/((n : ℝ)*((n : ℝ)-1)) ≤
        24*((n : ℝ)^(2/(2*s+1))/(n : ℝ)^2) := by
      apply (div_le_iff₀ hden0).mpr
      have ht : (k : ℝ)*(n : ℝ)^2 ≤
          6*(n : ℝ)^(2/(2*s+1))*((n : ℝ)*((n : ℝ)-1)) := by
        have hp := Real.rpow_nonneg hn0.le (2/(2*s+1))
        nlinarith [mul_le_mul_of_nonneg_right hk hn2.le,
          mul_le_mul_of_nonneg_left hden hp]
      have he : 24*((n : ℝ)^(2/(2*s+1))/(n : ℝ)^2)*((n : ℝ)*((n : ℝ)-1)) =
          (24*(n : ℝ)^(2/(2*s+1))*((n : ℝ)*((n : ℝ)-1)))/(n : ℝ)^2 := by ring
      rw [he]
      apply (le_div_iff₀ hn2).mpr
      convert (show 4*(k : ℝ)*(n : ℝ)^2 ≤
        24*(n : ℝ)^(2/(2*s+1))*((n : ℝ)*((n : ℝ)-1)) by nlinarith) using 1 <;> ring
    dsimp only [varianceRadius]
    calc
      20*(10/(n : ℝ)+4*(k : ℝ)/((n : ℝ)*((n : ℝ)-1))) =
          200/(n : ℝ)+20*(4*(k : ℝ)/((n : ℝ)*((n : ℝ)-1))) := by ring
      _ ≤ _ := by linarith
  have ht : ((n : ℝ)^(-(1/2 : ℝ)))^2 = 1/(n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
    simp [Real.rpow_neg_one, one_div]
  have hu : ((n : ℝ)^(-(2*s/(2*s+1))))^2 =
      (n : ℝ)^(2/(2*s+1))/(n : ℝ)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
      ← Real.rpow_natCast, ← Real.rpow_sub hn0]
    congr 1
    field_simp
    ring
  have ht0 := Real.rpow_nonneg hn0.le (-(1/2 : ℝ))
  have hu0 := Real.rpow_nonneg hn0.le (-(2*s/(2*s+1)))
  have hv0 : 0 ≤ 20*varianceRadius n k := by dsimp [varianceRadius]; positivity
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  have htn : 200/(n : ℝ) = 200*((n : ℝ)^(-(1/2 : ℝ)))^2 := by rw [ht]; ring
  rw [htn, ← hu] at hv
  nlinarith [mul_nonneg ht0 hu0]

/-- [Both bias and noise are bounded by the slower of the balanced and parametric rates.](goal) Under [the stated assumptions](hyp:hn,hs,hB). Under [the stated assumptions](hyp:hkl,hku). -/
-- @node: rank_radius_power_bound
lemma rank_radius_power_bound (n k : ℕ) (hn : 2 ≤ n) (s B : ℝ)
    (hs : 0 < s) (hB : 0 ≤ B)
    (hkl : (n : ℝ)^(2/(2*s+1)) ≤ k)
    (hku : (k : ℝ) ≤ 3*(n : ℝ)^(2/(2*s+1))) :
    B*(k : ℝ)^(-s)+Real.sqrt (20*varianceRadius n k) ≤
      (B+80)*(n : ℝ)^(-min (1/2) (2*s/(2*s+1))) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hb := rank_bias_power_bound (n : ℝ) k s hn1 hs hkl
  have hv := rank_noise_power_bound n k hn s hs hku
  have ht := Real.rpow_le_rpow_of_exponent_le hn1
    (neg_le_neg (min_le_left (1/2 : ℝ) (2*s/(2*s+1))))
  have hu := Real.rpow_le_rpow_of_exponent_le hn1
    (neg_le_neg (min_le_right (1/2 : ℝ) (2*s/(2*s+1))))
  nlinarith [mul_le_mul_of_nonneg_left hb hB, mul_le_mul_of_nonneg_left hu hB]

/-- [The two prescribed coordinate radii have absolute uniform power bounds.](goal) Under [the stated assumptions](hyp:hE,hN,hn,hab). -/
-- @node: coordinate_radii_power_bounds
lemma coordinate_radii_power_bounds (E : ArithmeticEngine) (hE : E.Admissible)
    (N : NamingPolicy) (hN : N.Admissible) (n : ℕ) (hn : 2 ≤ n)
    (α β : ℝ) (hab : ExponentDomain α β) :
    let k := resolutions E N n α β
    (8*(k.1 : ℝ)^(-(α+β))+Real.sqrt (20*varianceRadius n k.1) ≤
      128*(n : ℝ)^(-exponentA α β)) ∧
    (25*(k.2 : ℝ)^(-2*β)+Real.sqrt (20*varianceRadius n k.2) ≤
      128*(n : ℝ)^(-exponentB β)) := by
  obtain ⟨hcl, hcu, hsl, hsu⟩ := resolutions_target_bounds E hE N hN n hn α β hab
  have hα : 0 < α := hab.1.trans hab.2.2.1
  have hc := rank_radius_power_bound n (resolutions E N n α β).1 hn (α+β) 8
    (by linarith [hab.1]) (by norm_num) (by convert hcl using 1 <;> congr 1 <;> ring)
    (by convert hcu using 1 <;> congr 1 <;> ring)
  have hs := rank_radius_power_bound n (resolutions E N n α β).2 hn (2*β) 25
    (by linarith [hab.1]) (by norm_num) (by convert hsl using 1 <;> congr 1 <;> ring)
    (by convert hsu using 1 <;> congr 1 <;> ring)
  have hmin : min (1/2 : ℝ) (2*(2*β)/(2*(2*β)+1)) = exponentB β := by
    dsimp [exponentB]
    rw [min_eq_right]
    · congr 1 <;> ring
    · apply (div_le_iff₀ (by linarith [hab.1] : 0 < 2*(2*β)+1)).mpr
      linarith [hab.2.1]
  have hca : min (1/2 : ℝ) (2*(α+β)/(2*(α+β)+1)) = exponentA α β := by
    dsimp [exponentA]
    congr 2 <;> ring
  rw [hca] at hc
  rw [hmin] at hs
  dsimp only
  constructor
  · exact hc.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · convert hs.trans (mul_le_mul_of_nonneg_right (show (25 : ℝ)+80 ≤ 128 by norm_num)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) using 1 <;> congr 2 <;> ring

/-- [The diagnostic powers are at most one, and the numerator absorbs inverse sample size.](goal) Under [the stated assumptions](hyp:hn,hab). -/
-- @node: diagnostic_power_bounds
lemma diagnostic_power_bounds (n : ℕ) (hn : 2 ≤ n) (α β : ℝ)
    (hab : ExponentDomain α β) :
    (n : ℝ)^(-exponentA α β) ≤ 1 ∧
    (n : ℝ)^(-exponentB β) ≤ 1 ∧
    1/(n : ℝ) ≤ (n : ℝ)^(-exponentA α β) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hα : 0 < α := hab.1.trans hab.2.2.1
  have hβ : 0 < β := hab.1
  have ha0 : 0 ≤ exponentA α β := by dsimp [exponentA]; positivity
  have hb0 : 0 ≤ exponentB β := by dsimp [exponentB]; positivity
  have ha1 : exponentA α β ≤ 1 :=
    (min_le_left (1/2 : ℝ) _).trans (by norm_num)
  refine ⟨Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith),
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith), ?_⟩
  simpa [Real.rpow_neg_one, one_div] using
    Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg ha1)

/-- [The sensitivity formula assembles into the diagnostic profile without a remainder.](goal) Under [the stated assumptions](hyp:x,hx,hA,hB,hB1,hc0,hs0,hc,hs,hInv,hL,hH,hT,hr). -/
-- @node: radius_sensitivity_rate_assembly
lemma radius_sensitivity_rate_assembly (x A B bC bS L H T r : ℝ)
    (hx : 0 < x) (hA : 0 ≤ A) (hB : 0 ≤ B) (hB1 : B ≤ 1)
    (hc0 : 0 ≤ bC) (hs0 : 0 ≤ bS) (hc : bC ≤ 128*A) (hs : bS ≤ 128*B)
    (hInv : 1/x ≤ A) (hL : 0 ≤ L) (hH : 0 ≤ H) (hT : 0 ≤ T) (hr : 0 ≤ r) :
    L*bC+H*bS*(T*r+2*bC)+2/x ≤
      (128*L+32768*H+128*H*T+2)*(A+r*B) := by
  have hcross : H*B*A ≤ H*A := by
    have h := mul_le_mul_of_nonneg_right hB1 hA
    have h' := mul_le_mul_of_nonneg_left h hH
    simpa [mul_assoc] using h'
  calc
    L*bC+H*bS*(T*r+2*bC)+2/x ≤
        L*(128*A)+H*(128*B)*(T*r+2*(128*A))+2*A := by
      have hi : 2/x ≤ 2*A := by
        calc
          2/x = 2*(1/x) := by ring
          _ ≤ 2*A := mul_le_mul_of_nonneg_left hInv (by norm_num)
      gcongr
    _ ≤ (128*L+32768*H+2)*A+(128*H*T)*(r*B) := by
      nlinarith only [hcross]
    _ ≤ _ := by
      have h1 : 0 ≤ (128*H*T)*A := by positivity
      have h2 : 0 ≤ (128*L+32768*H+2)*(r*B) := by positivity
      nlinarith only [h1, h2]

/-- A single absolute constant bounds the full rank-dependent sensitivity expression. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: upper_radii_uniform_rate
lemma upper_radii_uniform_rate : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (E : ArithmeticEngine), E.Admissible →
    ∀ (N : NamingPolicy) (hN : N.Admissible) (α β : ℝ), ExponentDomain α β →
    ∀ n : ℕ, 2 ≤ n → ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) (1/2) →
      let k := resolutions E N n α β
      let bC := 8*(k.1 : ℝ)^(-(α+β))+Real.sqrt (20*varianceRadius n k.1)
      let bS := 25*(k.2 : ℝ)^(-2*β)+Real.sqrt (20*varianceRadius n k.2)
      2*Real.exp (1/2)/denominatorFloor*bC+
        2*Real.exp (1/2)/denominatorFloor^2*bS*(Real.exp (1/2)*r+2*bC)+2/(n : ℝ) ≤
          K*diagnosticEnvelope n α β r := by
  let L := 2*Real.exp (1/2)/denominatorFloor
  let H := 2*Real.exp (1/2)/denominatorFloor^2
  let T := Real.exp (1/2 : ℝ)
  have hL : 0 ≤ L := by dsimp [L, denominatorFloor]; positivity
  have hH : 0 ≤ H := by dsimp [H, denominatorFloor]; positivity
  have hT : 0 ≤ T := (Real.exp_pos _).le
  refine ⟨128*L+32768*H+128*H*T+2, by nlinarith [mul_nonneg hH hT], ?_⟩
  intro E hE N hN α β hab n hn r hr
  obtain ⟨hc, hs⟩ := coordinate_radii_power_bounds E hE N hN n hn α β hab
  obtain ⟨_, hB, hInv⟩ := diagnostic_power_bounds n hn α β hab
  exact radius_sensitivity_rate_assembly (n : ℝ) _ _ _ _ L H T r
    (by exact_mod_cast (show 0 < n by omega)) (by positivity) (by positivity) hB
    (by positivity) (by positivity) hc hs hInv hL hH hT hr.1

end CausalSmith.Stat.LogoddsLowsmoothFrontier
