module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RateAlgebra
public import Mathlib.Order.LiminfLimsup

/-!
# Oracle attainment and positive liminf

The exact annotation threshold converts eventual oracle-order attainment into
an eventual positive lower bound on the normalized total sample count.
-/

public section

open Filter
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- A positive extended-real liminf is equivalent to an eventual positive real lower bound.  Given [the specified input f](hyp:f), [the of real liminf pos iff conclusion](goal) holds. -/
lemma ofReal_liminf_pos_iff (f : ℕ → ℝ) :
    0 < liminf (fun n => ENNReal.ofReal (f n)) atTop ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ f n := by
  constructor
  · intro h
    obtain ⟨c, hc, hcl⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp h
    have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
    have hcl' : ENNReal.ofReal (c : ℝ) < liminf (fun n => ENNReal.ofReal (f n)) atTop := by
      simpa using hcl
    refine ⟨c, hcR, ?_⟩
    filter_upwards [eventually_lt_of_lt_liminf hcl'] with n hn
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hcR.le).mp hn |>.le
  · rintro ⟨c, hc, h⟩
    exact (ENNReal.ofReal_pos.mpr hc).trans_le
      (le_liminf_of_le (h := h.mono fun n hn => ENNReal.ofReal_le_ofReal hn))

/-- The annotation region is exactly a lower threshold on the normalized total count.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input zeta](hyp:zeta), [the specified input hz](hyp:hz), [the annotation region count iff conclusion](goal) holds. -/
lemma annotationRegion_count_iff (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (n m : ℕ) (hn : 2 ≤ n)
    (zeta : ℝ) (hz : 1 ≤ zeta) :
    (n,m) ∈ annotationRegion d alpha beta gamma zeta ↔
      zeta^(-(bigDelta d alpha beta gamma/gamma)) ≤
        ((n:ℝ)+m)/(n:ℝ)^qStar d alpha beta gamma := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hS : 0 < alpha+beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hA : 0 < 2*gamma+(d:ℝ) := by positivity
  have hD : 0 < bigDelta d alpha beta gamma := by unfold bigDelta; positivity
  have hnp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < (n:ℝ)+(m:ℝ) := by positivity
  have hzp : 0 < zeta := zero_lt_one.trans_le hz
  have ho : 0 < oracleRate d gamma n := Real.rpow_pos_of_pos hnp _
  have hboundary : (oracleRate d gamma n)^(-(bigDelta d alpha beta gamma/gamma)) =
      (n:ℝ)*(n:ℝ)^qStar d alpha beta gamma := by
    unfold oracleRate
    rw [← Real.rpow_mul hnp.le]
    have he : -(gamma/(2*gamma+(d:ℝ)))*(-(bigDelta d alpha beta gamma/gamma)) =
        1+qStar d alpha beta gamma := by
      rw [(rate_exponent_identities d alpha beta gamma L eps hdom).2]
      field_simp
    rw [he, Real.rpow_add hnp, Real.rpow_one]
  change (2 ≤ n ∧ max (oracleRate d gamma n)
    (((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma))) ≤
      zeta*oracleRate d gamma n) ↔ _
  rw [and_iff_right hn, max_le_iff, and_iff_right (le_mul_of_one_le_left ho.le hz)]
  rw [decreasing_power_threshold _ _ _ _ (mul_pos hnp hN) (mul_pos hzp ho) hD hg,
    Real.mul_rpow hzp.le ho.le, hboundary, le_div_iff₀ (Real.rpow_pos_of_pos hnp _)]
  constructor <;> intro h
  · nlinarith
  · nlinarith

/-- Some finite oracle tolerance is equivalent to a positive normalized-count liminf.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input mseq](hyp:mseq), [the annotation region liminf iff conclusion](goal) holds. -/
lemma annotationRegion_liminf_iff (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (mseq : ℕ → ℕ) :
    (∃ zeta : ℝ, 1 ≤ zeta ∧ ∀ᶠ n in atTop,
      (n,mseq n) ∈ annotationRegion d alpha beta gamma zeta) ↔
    0 < liminf (fun n : ℕ => ENNReal.ofReal
      (((n:ℝ)+mseq n)/(n:ℝ)^qStar d alpha beta gamma)) atTop := by
  rw [ofReal_liminf_pos_iff]
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hS : 0 < alpha+beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hD : 0 < bigDelta d alpha beta gamma := by unfold bigDelta; positivity
  constructor
  · rintro ⟨zeta, hz, hevent⟩
    refine ⟨zeta^(-(bigDelta d alpha beta gamma/gamma)),
      Real.rpow_pos_of_pos (zero_lt_one.trans_le hz) _, ?_⟩
    filter_upwards [hevent] with n hn
    exact (annotationRegion_count_iff d alpha beta gamma L eps hdom n (mseq n) hn.1 zeta hz).mp hn
  · rintro ⟨c, hc, hevent⟩
    let zeta : ℝ := max 1 (c^(-(gamma/bigDelta d alpha beta gamma)))
    have hz : 1 ≤ zeta := le_max_left _ _
    have hzc : zeta^(-(bigDelta d alpha beta gamma/gamma)) ≤ c :=
      (decreasing_power_threshold zeta c gamma (bigDelta d alpha beta gamma)
        (zero_lt_one.trans_le hz) hc hg hD).mpr (le_max_right _ _)
    refine ⟨zeta, hz, ?_⟩
    filter_upwards [hevent, eventually_ge_atTop (2 : ℕ)] with n hn hn2
    exact (annotationRegion_count_iff d alpha beta gamma L eps hdom n (mseq n) hn2 zeta hz).mpr
      (hzc.trans hn)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
