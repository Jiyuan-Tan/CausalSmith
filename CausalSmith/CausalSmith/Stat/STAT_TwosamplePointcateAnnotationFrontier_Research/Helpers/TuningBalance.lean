module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Estimator

/-! # Public bandwidth and grid balance
Algebraic bounds for the two sampling terms under the prescribed public tuning.
-/

public section

noncomputable section
set_option linter.style.whitespace false
set_option linter.style.longLine false
open scoped BigOperators
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- A bandwidth above the sample power balances a sampling monomial against its bias.  Given [the specified input x](hyp:x), [the specified input H](hyp:H), [the specified input D](hyp:D), [the specified input p](hyp:p), [the specified input g](hyp:g), [the specified input hx](hyp:hx), [the specified input hH](hyp:hH), [the specified input hD](hyp:hD), [the specified input heq](hyp:heq), [the specified input hb](hyp:hb), [the bandwidth monomial balance conclusion](goal) holds. -/
lemma bandwidth_monomial_balance (x H D p g : ℝ) (hx : 0 < x) (hH : 0 < H)
    (hD : 0 < D) (heq : D = 2*g+p) (hb : x^(-(1/D)) ≤ 2*H) :
    (x*H^p)^(-(1/2:ℝ)) ≤ (2:ℝ)^(D/2)*H^g := by
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hx _) hb
  rw [Real.log_rpow hx, Real.log_mul (by norm_num) hH.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl hD.le
  have hc : D * (-(1/D) * Real.log x) = -Real.log x := by
    field_simp
  rw [hc] at hm
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_rpow (by positivity), Real.log_mul hx.ne' (by positivity),
    Real.log_rpow hH, Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num), Real.log_rpow hH]
  rw [heq] at hm ⊢
  nlinarith

/-- Rounding the grid power changes its cell side by at most a factor two.  Given [the specified input H](hyp:H), [the specified input t](hyp:t), [the specified input hH](hyp:hH), [the specified input hH1](hyp:hH1), [the specified input ht](hyp:ht), [the ceil grid side bounds conclusion](goal) holds. -/
lemma ceil_grid_side_bounds (H t : ℝ) (hH : 0 < H) (hH1 : H ≤ 1) (ht : 1 ≤ t) :
    let J := Nat.ceil (H^(-(t-1)))
    1 ≤ J ∧ 0 < H/J ∧ H^t/2 ≤ H/J ∧ H/J ≤ H^t := by
  let z := H^(-(t-1))
  have hz : 0 < z := Real.rpow_pos_of_pos hH _
  have hz1 : 1 ≤ z := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hH hH1 (show -(t-1) ≤ 0 by linarith)
  have hJ : 1 ≤ Nat.ceil z := Nat.one_le_ceil_iff.mpr hz
  have hJpos : (0:ℝ) < Nat.ceil z := by exact_mod_cast hJ
  have hlow : z ≤ (Nat.ceil z:ℝ) := Nat.le_ceil z
  have hupp : (Nat.ceil z:ℝ) ≤ 2*z := by
    have hc := Nat.ceil_lt_add_one hz.le
    linarith
  have heq : H/z = H^t := by
    dsimp [z]
    rw [div_eq_mul_inv, ← Real.rpow_neg hH.le]
    conv_lhs => lhs; rw [← Real.rpow_one H]
    rw [← Real.rpow_add hH]
    congr 1
    ring
  refine ⟨hJ, div_pos hH hJpos, ?_, ?_⟩
  · rw [← heq]
    calc
      H/z/2 = H/(2*z) := by ring
      _ ≤ H/(Nat.ceil z:ℝ) := div_le_div_of_nonneg_left hH.le hJpos hupp
  · rw [← heq]
    exact div_le_div_of_nonneg_left hH.le hz hlow

/-- A factor-two cell-side bound gives the corresponding pair-sampling bound.  Given [the specified input x](hyp:x), [the specified input H](hyp:H), [the specified input delta](hyp:delta), [the specified input t](hyp:t), [the specified input d](hyp:d), [the specified input hx](hyp:hx), [the specified input hH](hyp:hH), [the specified input hd](hyp:hd), [the specified input hgrid](hyp:hgrid), [the grid pair sampling le conclusion](goal) holds. -/
lemma grid_pair_sampling_le (x H delta t : ℝ) (d : ℕ)
    (hx : 0 < x) (hH : 0 < H) (hd : 0 < delta) (hgrid : H^t/2 ≤ delta) :
    (x*H^d*delta^d)^(-(1/2:ℝ)) ≤
      (2:ℝ)^((d:ℝ)/2)*(x*H^((d:ℝ)+(d:ℝ)*t))^(-(1/2:ℝ)) := by
  have hl := Real.log_le_log (by positivity : 0 < H^t/2) hgrid
  rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hH] at hl
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp only [← Real.rpow_natCast]
  rw [Real.log_rpow (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul hx.ne' (by positivity), Real.log_rpow hH, Real.log_rpow hd,
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
    Real.log_rpow (by positivity), Real.log_mul hx.ne' (by positivity), Real.log_rpow hH]
  nlinarith

/-- The prescribed tuning balances approximation and both sampling channels.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the tuning balance conclusion](goal) holds. -/
lemma tuning_balance (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n →
      let h := hStar d alpha beta gamma n m
      let J := jStar d alpha beta gamma n m
      0 < h ∧ h ≤ 1/2 ∧ 1 ≤ J ∧
      h^gamma+(h/J)^(alpha+beta)+((n:ℝ)*h^d)^(-(1/2:ℝ))+
        ((n:ℝ)*((n:ℝ)+m)*h^d*(h/J)^d)^(-(1/2:ℝ)) ≤
        C*upperRate d alpha beta gamma n m := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hS : 0 < alpha+beta := add_pos hdom.2.1 hdom.2.2.2.1
  let A : ℝ := 2*gamma+d
  let D := bigDelta d alpha beta gamma
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D, bigDelta]; positivity
  let c1 : ℝ := (2:ℝ)^(A/2)
  let c2 : ℝ := (2:ℝ)^((d:ℝ)/2)*(2:ℝ)^(D/2)+(2:ℝ)^A
  refine ⟨2+c1+c2, by dsimp [c1, c2]; positivity, ?_⟩
  intro n m hn
  let H := hStar d alpha beta gamma n m
  let J := jStar d alpha beta gamma n m
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hN : (n:ℝ) ≤ (n:ℝ)+m := le_add_of_nonneg_right (Nat.cast_nonneg m)
  have hNpos : (0:ℝ) < (n:ℝ)+m := hnpos.trans_le hN
  have hx : (0:ℝ) < (n:ℝ)*((n:ℝ)+m) := mul_pos hnpos hNpos
  let u : ℝ := (n:ℝ)^(-(1/A))
  let w : ℝ := ((n:ℝ)*((n:ℝ)+m))^(-(1/D))
  have hu : 0 < u := Real.rpow_pos_of_pos hnpos _
  have hw : 0 < w := Real.rpow_pos_of_pos hx _
  have hu1 : u ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hn1 (show -(1/A) ≤ 0 by exact neg_nonpos.mpr (one_div_nonneg.mpr hA.le))
  have hx1 : (1:ℝ) ≤ (n:ℝ)*((n:ℝ)+m) := by nlinarith
  have hw1 : w ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hx1 (show -(1/D) ≤ 0 by exact neg_nonpos.mpr (one_div_nonneg.mpr hD.le))
  have hHdef : H = (1/2:ℝ)*max u w := rfl
  have hH : 0 < H := by rw [hHdef]; positivity
  have hHhalf : H ≤ 1/2 := by rw [hHdef]; nlinarith [max_le hu1 hw1]
  have hH1 : H ≤ 1 := by linarith
  have hbu : u ≤ 2*H := by rw [hHdef]; nlinarith [le_max_left u w]
  have hbw : w ≤ 2*H := by rw [hHdef]; nlinarith [le_max_right u w]
  have hrate : H^gamma ≤ upperRate d alpha beta gamma n m := by
    have hHm : H ≤ max u w := by rw [hHdef]; nlinarith [le_max_left u w]
    have hp := Real.rpow_le_rpow hH.le hHm hg.le
    rw [Real.rpow_max hu.le hw.le hg.le] at hp
    have he1 : u^gamma = oracleRate d gamma n := by
      dsimp [u, oracleRate, A]
      rw [← Real.rpow_mul hnpos.le]
      congr 1
      ring
    have he2 : w^gamma = ((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma)) := by
      dsimp [w, D]
      rw [← Real.rpow_mul hx.le]
      congr 1
      ring
    simpa only [he1, he2, upperRate] using hp
  have hsamp : ((n:ℝ)*H^d)^(-(1/2:ℝ)) ≤ c1*H^gamma := by
    rw [← Real.rpow_natCast]
    exact bandwidth_monomial_balance _ _ A _ _ hnpos hH hA rfl hbu
  have hgrid : 1 ≤ J ∧ 0 < H/J ∧ (H/J)^(alpha+beta) ≤ H^gamma ∧
      ((n:ℝ)*((n:ℝ)+m)*H^d*(H/J)^d)^(-(1/2:ℝ)) ≤ c2*H^gamma := by
    by_cases hSG : alpha+beta < gamma
    · have ht : 1 ≤ gamma/(alpha+beta) := (le_div_iff₀ hS).mpr (by linarith)
      have hJdef : J = Nat.ceil (H^(-(gamma/(alpha+beta)-1))) := by
        dsimp [J, jStar]
        rw [max_eq_right (by linarith : 0 ≤ gamma/(alpha+beta)-1)]
      obtain ⟨hJ, hd, hlo, hhi⟩ := ceil_grid_side_bounds H (gamma/(alpha+beta)) hH hH1 ht
      rw [← hJdef] at hJ hd hlo hhi
      have hbias := Real.rpow_le_rpow hd.le hhi hS.le
      rw [← Real.rpow_mul hH.le, div_mul_cancel₀ _ hS.ne'] at hbias
      have hp := grid_pair_sampling_le _ H (H/J) (gamma/(alpha+beta)) d hx hH hd hlo
      have hbal := bandwidth_monomial_balance _ H D ((d:ℝ)+(d:ℝ)*(gamma/(alpha+beta))) gamma hx hH hD
        (by dsimp [D, bigDelta]; ring) hbw
      have hc : (2:ℝ)^((d:ℝ)/2)*(2:ℝ)^(D/2) ≤ c2 := by dsimp [c2]; exact le_add_of_nonneg_right (by positivity)
      refine ⟨hJ, hd, hbias, ?_⟩
      calc
        _ ≤ (2:ℝ)^((d:ℝ)/2)*((2:ℝ)^(D/2)*H^gamma) :=
          hp.trans (mul_le_mul_of_nonneg_left hbal (by positivity))
        _ ≤ c2*H^gamma := by nlinarith [Real.rpow_pos_of_pos hH gamma]
    · have ht : gamma/(alpha+beta) ≤ 1 := (div_le_iff₀ hS).mpr (by linarith)
      have hJdef : J = 1 := by
        dsimp [J, jStar]
        rw [max_eq_left (by linarith : gamma/(alpha+beta)-1 ≤ 0)]
        norm_num
      rw [hJdef]
      simp only [Nat.cast_one, div_one]
      have hbias := Real.rpow_le_rpow_of_exponent_ge hH hH1 (le_of_not_gt hSG)
      have hb2 : ((n:ℝ)^2)^(-(1/(2*A))) ≤ 2*H := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
        norm_num only [Nat.cast_ofNat]
        have he : (2:ℝ)*(-(1/(2*A))) = -(1/A) := by field_simp
        rw [he]
        exact hbu
      have hbal := bandwidth_monomial_balance ((n:ℝ)^2) H (2*A) (2*(d:ℝ)) (2*gamma)
        (by positivity) hH (by positivity) (by dsimp [A]; ring) hb2
      have hcompare : ((n:ℝ)*((n:ℝ)+m)*H^d*H^d)^(-(1/2:ℝ)) ≤
          ((n:ℝ)^2*H^(2*(d:ℝ)))^(-(1/2:ℝ)) := by
        apply Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
        rw [show 2*(d:ℝ) = (d:ℝ)+(d:ℝ) by ring, Real.rpow_add hH, Real.rpow_natCast]
        nlinarith [sq_nonneg (H^d), mul_nonneg (by positivity : (0:ℝ) ≤ n) (Nat.cast_nonneg m : (0:ℝ) ≤ m)]
      have hpow : H^(2*gamma) ≤ H^gamma :=
        Real.rpow_le_rpow_of_exponent_ge hH hH1 (by linarith)
      have hc : (2:ℝ)^A ≤ c2 := by dsimp [c2]; exact le_add_of_nonneg_left (by positivity)
      refine ⟨by omega, hH, hbias, ?_⟩
      calc
        _ ≤ (2:ℝ)^A*H^(2*gamma) := by
          convert hcompare.trans hbal using 1 <;> congr 2 <;> ring
        _ ≤ c2*H^gamma := mul_le_mul hc hpow (by positivity) (by positivity)
  rcases hgrid with ⟨hJ, hd, hbias, hpair⟩
  refine ⟨hH, hHhalf, hJ, ?_⟩
  calc
    _ ≤ (2+c1+c2)*H^gamma := by change H^gamma+(H/J)^(alpha+beta)+((n:ℝ)*H^d)^(-(1/2:ℝ))+((n:ℝ)*((n:ℝ)+m)*H^d*(H/J)^d)^(-(1/2:ℝ)) ≤ _; nlinarith
    _ ≤ (2+c1+c2)*upperRate d alpha beta gamma n m :=
      mul_le_mul_of_nonneg_left hrate (by dsimp [c1, c2]; positivity)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
