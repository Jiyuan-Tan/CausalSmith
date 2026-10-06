module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.OracleBumpInformation
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.Hellinger
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.MarkedHandle

/-!
# Lower/TwoPoint

Two-channel point-CATE annotation frontier: Lower/TwoPoint
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


/-- Constant-propensity bump alternatives remain members of the exact primitive class.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the oracle bump pair conclusion](goal) holds. -/
lemma oracle_bump_pair (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧ ∀ (n : ℕ), 2 ≤ n →
      let H := (n:ℝ)^(-(1/(2*gamma+d)))
      let bn := eta*oracleRate d gamma n
      ∃ P0 P1 : PrimitiveLaw d,
        ∃ (hP0 : PrimitiveClass alpha beta gamma L eps P0) (hP1 : PrimitiveClass alpha beta gamma L eps P1),
        (∀ x ∈ cube d, (designatedPropensity P0 hP0) x = 1/2 ∧ (designatedPropensity P1 hP1) x = 1/2 ∧ (designatedControl P0 hP0) x = 1/2 ∧ (designatedControl P1 hP1) x = 1/2) ∧
        (∀ x ∈ cube d, tau P0 hP0 x = -bn*macroBump H x ∧ tau P1 hP1 x = bn*macroBump H x) ∧
        hellingerSq (obsLaw P0) (obsLaw P1) ≤ C*bn^2*H^d  := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hL : 1/2 ≤ L := hdom.2.2.2.2.2.2.2.1.le
  have heps : 0 < eps := hdom.2.2.2.2.2.2.2.2.1
  have heps' : eps ≤ 1/2 := hdom.2.2.2.2.2.2.2.2.2.le
  obtain ⟨D, hD, hprofile⟩ := oracle_macro_holder d gamma hg
  let eta := (8*(D+1))⁻¹
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaD : eta*(D+1) = 1/8 := by dsimp [eta]; field_simp
  have hetasmall : eta ≤ 1/8 := by nlinarith
  have hDeta : eta*D ≤ L := by nlinarith
  refine ⟨eta, 16, heta, by norm_num, ?_⟩
  intro n hn
  dsimp only
  let H : ℝ := (n:ℝ)^(-(1/(2*gamma+d)))
  let bn : ℝ := eta*oracleRate d gamma n
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hden : 0 < 2*gamma+(d:ℝ) := by positivity
  have hH : 0 < H := Real.rpow_pos_of_pos hn0 _
  have hH1 : H ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (one_div_nonneg.mpr hden.le))
  have hrate : H^gamma = oracleRate d gamma n := by
    dsimp only [H, oracleRate]
    rw [← Real.rpow_mul hn0.le]
    congr 1
    ring
  have hbn : 0 < bn := by dsimp [bn, oracleRate]; positivity
  have hbsmall : bn ≤ 1/8 := by
    dsimp only [bn]
    rw [← hrate]
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_one hH.le hH1 hg.le) heta.le).trans
      (by simpa using hetasmall)
  have hsmooth : holderNorm (fun x : Cov d => bn*macroBump H x) gamma ≤ ENNReal.ofReal L := by
    have hs := holderNorm_const_mul_bound (macroBump (d:=d) H) gamma (D*H^(-gamma)) bn
      (by positivity) (hprofile H hH hH1)
    rw [abs_of_pos hbn] at hs
    have hid : bn*(D*H^(-gamma)) = eta*D := by
      dsimp only [bn]
      rw [← hrate]
      calc
        eta*H^gamma*(D*H^(-gamma)) = eta*D*(H^gamma*H^(-gamma)) := by ring
        _ = eta*D := by rw [← Real.rpow_add hH, add_neg_cancel, Real.rpow_zero, mul_one]
    rw [hid] at hs
    exact hs.trans (ENNReal.ofReal_le_ofReal hDeta)
  obtain ⟨hP0, hp0⟩ := oracleBumpPrimitive_membership d alpha beta gamma L eps H bn
    hL heps heps' hbn.le hbsmall hsmooth false
  obtain ⟨hP1, hp1⟩ := oracleBumpPrimitive_membership d alpha beta gamma L eps H bn
    hL heps heps' hbn.le hbsmall hsmooth true
  refine ⟨oracleBumpPrimitive d H bn false, oracleBumpPrimitive d H bn true,
    hP0, hP1, ?_, ?_, oracle_bump_hellinger_bound d H bn hH hH1 hbn.le hbsmall⟩
  · intro x hx
    exact ⟨(hp0 x hx).1, (hp1 x hx).1, (hp0 x hx).2.1, (hp1 x hx).2.1⟩
  · intro x hx
    constructor
    · simpa [thetaSign, H, bn] using (hp0 x hx).2.2
    · simpa [thetaSign, H, bn] using (hp1 x hx).2.2


end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
