module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Basic

/-!
# Helpers/RateAlgebra

Two-channel point-CATE annotation frontier: Helpers/RateAlgebra
constructions and obligations.
-/

public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the rate exponent identities conclusion](goal) holds. -/
lemma rate_exponent_identities (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    qStar d alpha beta gamma = sCrit d gamma/(alpha+beta) ∧
    bigDelta d alpha beta gamma = (2*gamma+d)*(1+qStar d alpha beta gamma) := by
  have hS : 0 < alpha + beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hD : 0 < 2 * gamma + (d : ℝ) := by positivity
  constructor
  · dsimp [qStar, sCrit]
    field_simp
  · dsimp [bigDelta, qStar]
    field_simp
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the rate branches conclusion](goal) holds. -/
lemma rate_branches (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (n m : ℕ) (hn : 2 ≤ n) :
    (sCrit d gamma ≤ alpha+beta → sharpRate d alpha beta gamma n m = oracleRate d gamma n) ∧
    (alpha+beta < sCrit d gamma → (n:ℝ)+m ≤ (n:ℝ)^qStar d alpha beta gamma →
      sharpRate d alpha beta gamma n m = ((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma))) ∧
    (alpha+beta < sCrit d gamma → (n:ℝ)^qStar d alpha beta gamma ≤ (n:ℝ)+m →
      sharpRate d alpha beta gamma n m = oracleRate d gamma n) ∧
    ((n:ℝ)+m = (n:ℝ)^qStar d alpha beta gamma →
      ((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma)) = oracleRate d gamma n) := by
  have hS : 0 < alpha + beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hD : 0 < 2 * gamma + (d : ℝ) := by positivity
  have hDelta : 0 < bigDelta d alpha beta gamma := by
    dsimp [bigDelta]
    positivity
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hN : (n : ℝ) ≤ (n : ℝ) + m := le_add_of_nonneg_right (Nat.cast_nonneg m)
  have hexp : -(gamma / bigDelta d alpha beta gamma) ≤ 0 := by
    exact neg_nonpos.mpr (le_of_lt (div_pos hg hDelta))
  have hid := (rate_exponent_identities d alpha beta gamma L eps hdom).2
  have hboundary : ((n : ℝ) * (n : ℝ) ^ qStar d alpha beta gamma) ^
      (-(gamma / bigDelta d alpha beta gamma)) = oracleRate d gamma n := by
    rw [show (n : ℝ) * (n : ℝ) ^ qStar d alpha beta gamma =
      (n : ℝ) ^ (1 + qStar d alpha beta gamma) by
        rw [Real.rpow_add hnpos, Real.rpow_one]]
    rw [← Real.rpow_mul hnpos.le]
    dsimp [oracleRate]
    congr 1
    rw [hid]
    have hq : 0 ≤ qStar d alpha beta gamma := by
      dsimp [qStar]
      positivity
    field_simp
  have hlarge : ∀ N : ℝ, (n : ℝ) ^ qStar d alpha beta gamma ≤ N →
      ((n : ℝ) * N) ^ (-(gamma / bigDelta d alpha beta gamma)) ≤ oracleRate d gamma n := by
    intro N h
    rw [← hboundary]
    exact Real.rpow_le_rpow_of_nonpos
      (mul_pos hnpos (Real.rpow_pos_of_pos hnpos _))
      (mul_le_mul_of_nonneg_left h hnpos.le) hexp
  have hsmall : ∀ N : ℝ, 0 < N → N ≤ (n : ℝ) ^ qStar d alpha beta gamma →
      oracleRate d gamma n ≤ ((n : ℝ) * N) ^ (-(gamma / bigDelta d alpha beta gamma)) := by
    intro N hNpos h
    rw [← hboundary]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hnpos hNpos)
      (mul_le_mul_of_nonneg_left h hnpos.le) hexp
  change
    (sCrit d gamma ≤ alpha + beta →
      max (oracleRate d gamma n) _ = oracleRate d gamma n) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hs
    apply max_eq_left
    apply hlarge
    have hq : qStar d alpha beta gamma ≤ 1 := by
      rw [(rate_exponent_identities d alpha beta gamma L eps hdom).1]
      exact (div_le_one hS).mpr hs
    calc
      (n : ℝ) ^ qStar d alpha beta gamma ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 hq
      _ = (n : ℝ) := Real.rpow_one _
      _ ≤ (n : ℝ) + m := hN
  · intro hs h
    exact max_eq_right (hsmall _ (lt_of_lt_of_le hnpos hN) h)
  · intro hs h
    exact max_eq_left (hlarge _ h)
  · intro h
    rw [h]
    exact hboundary

/-- Below the smoothness cutoff, the total-count boundary exponent exceeds one.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input hs](hyp:hs), [the q star gt one conclusion](goal) holds. -/
lemma qStar_gt_one (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps)
    (hs : alpha + beta < sCrit d gamma) : 1 < qStar d alpha beta gamma := by
  rw [(rate_exponent_identities d alpha beta gamma L eps hdom).1]
  exact (one_lt_div (add_pos hdom.2.1 hdom.2.2.2.1)).mpr hs

/-- With no auxiliary records, the pair branch is the stated supervised power.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input n](hyp:n), [the specified input hn](hyp:hn), [the supervised rate branches conclusion](goal) holds. -/
lemma supervised_rate_branches (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (n : ℕ) (hn : 2 ≤ n) :
    (alpha + beta < sCrit d gamma →
      sharpRate d alpha beta gamma n 0 = (n:ℝ)^(-(2*gamma/bigDelta d alpha beta gamma))) ∧
    (sCrit d gamma ≤ alpha + beta → sharpRate d alpha beta gamma n 0 = oracleRate d gamma n) := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hb := rate_branches d alpha beta gamma L eps hdom n 0 hn
  refine ⟨?_, hb.1⟩
  intro hs
  have hN : (n:ℝ) + (0:ℕ) ≤ (n:ℝ)^qStar d alpha beta gamma := by
    simpa only [Nat.cast_zero, add_zero, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn1 (qStar_gt_one d alpha beta gamma L eps hdom hs).le
  rw [hb.2.1 hs hN]
  simp only [Nat.cast_zero, add_zero]
  rw [← pow_two, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
  congr 1
  norm_num
  ring

/-- Inverting a decreasing positive power gives its exact sample threshold.  Given [the specified input x](hyp:x), [the specified input epsilon](hyp:epsilon), [the specified input D](hyp:D), [the specified input g](hyp:g), [the specified input hx](hyp:hx), [the specified input he](hyp:he), [the specified input hD](hyp:hD), [the specified input hg](hyp:hg), [the decreasing power threshold conclusion](goal) holds. -/
lemma decreasing_power_threshold (x epsilon D g : ℝ)
    (hx : 0 < x) (he : 0 < epsilon) (hD : 0 < D) (hg : 0 < g) :
    x^(-(g/D)) ≤ epsilon ↔ epsilon^(-(D/g)) ≤ x := by
  have hz : -(D/g) < 0 := neg_neg_of_pos (div_pos hD hg)
  have hi : (-(D/g))⁻¹ = -(g/D) := by field_simp
  simpa only [hi] using (Real.rpow_inv_le_iff_of_neg hx he hz)

/-- The maximum of the two frontier branches gives both exact acquisition requirements.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input epsilon](hyp:epsilon), [the specified input he](hyp:he), [the sharp rate acquisition iff conclusion](goal) holds. -/
lemma sharpRate_acquisition_iff (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (n m : ℕ) (hn : 2 ≤ n)
    (epsilon : ℝ) (he : 0 < epsilon) :
    sharpRate d alpha beta gamma n m ≤ epsilon ↔
      epsilon^(-(2+(d:ℝ)/gamma)) ≤ (n:ℝ) ∧
      epsilon^(-(2+(d:ℝ)/gamma+(d:ℝ)/(alpha+beta))) ≤ (n:ℝ)*((n:ℝ)+m) := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hS : 0 < alpha+beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hA : 0 < 2*gamma+(d:ℝ) := by positivity
  have hD : 0 < bigDelta d alpha beta gamma := by dsimp [bigDelta]; positivity
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hNpos : 0 < (n:ℝ)+(m:ℝ) := by positivity
  change max ((n:ℝ)^(-(gamma/(2*gamma+(d:ℝ)))))
    (((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma))) ≤ epsilon ↔ _
  rw [max_le_iff, decreasing_power_threshold _ _ _ _ hnpos he hA hg,
    decreasing_power_threshold _ _ _ _ (mul_pos hnpos hNpos) he hD hg]
  have h0 : (2*gamma+(d:ℝ))/gamma = 2+(d:ℝ)/gamma := by field_simp
  have h1 : bigDelta d alpha beta gamma/gamma =
      2+(d:ℝ)/gamma+(d:ℝ)/(alpha+beta) := by dsimp [bigDelta]; field_simp
  rw [h0, h1]

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
