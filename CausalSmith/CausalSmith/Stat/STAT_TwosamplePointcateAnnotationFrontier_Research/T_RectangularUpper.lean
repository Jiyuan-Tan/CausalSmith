module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.UpperRiskMoments

/-!
# T_RectangularUpper

Two-channel point-CATE annotation frontier: T_RectangularUpper
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


-- @node: thm:rectangular-upper
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the rectangular upper conclusion](goal) holds. -/
theorem rectangular_upper (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive claim-local constant)
      
      (∀ (n m : ℕ) (h : ℝ) (J : ℕ), 2 ≤ n → 0 < h → h ≤ 1/2 → 1 ≤ J →
        ∃ hMeas : Measurable (fun w : Sample d n m => tHat eps h J w.1),
          ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
            risk ⟨fun w => tHat eps h J w.1, hMeas⟩ P hP ≤
              ENNReal.ofReal (C*min 1 (h^gamma+(h/J)^(alpha+beta)+
                ((n:ℝ)*h^d)^(-(1/2:ℝ))+
                ((n:ℝ)*((n:ℝ)+m)*h^d*(h/J)^d)^(-(1/2:ℝ))))) ∧
      (∀ (n m : ℕ), 2 ≤ n → ∃ hMeas : Measurable (fun w : Sample d n m => tUp d alpha beta gamma eps n m w.1),
        ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
          risk ⟨fun w => tUp d alpha beta gamma eps n m w.1, hMeas⟩ P hP ≤
            ENNReal.ofReal (C*upperRate d alpha beta gamma n m)) := by
  obtain ⟨A, hA, hfixed⟩ := rectangular_fixed_tuning_risk d alpha beta gamma L eps hdom
  obtain ⟨B, hB, htuning⟩ := tuning_balance d alpha beta gamma L eps hdom
  refine ⟨A*(B+1), by positivity, ?_, ?_⟩
  · intro n m h J hn hh hh' hJ
    obtain ⟨hMeas, hrisk⟩ := hfixed n m h J hn hh hh' hJ
    refine ⟨hMeas, ?_⟩
    intro P hP
    refine (hrisk P hP).trans (ENNReal.ofReal_le_ofReal ?_)
    have hnonneg : 0 ≤ min 1 (h^gamma+(h/J)^(alpha+beta)+
        ((n:ℝ)*h^d)^(-(1/2:ℝ))+
        ((n:ℝ)*((n:ℝ)+m)*h^d*(h/J)^d)^(-(1/2:ℝ))) := by positivity
    exact mul_le_mul_of_nonneg_right (by nlinarith) hnonneg
  · intro n m hn
    obtain ⟨hh, hh', hJ, hbalance⟩ := htuning n m hn
    obtain ⟨hMeas, hrisk⟩ := hfixed n m (hStar d alpha beta gamma n m)
      (jStar d alpha beta gamma n m) hn hh hh' hJ
    refine ⟨hMeas, ?_⟩
    intro P hP
    change risk ⟨fun w => tHat eps (hStar d alpha beta gamma n m)
      (jStar d alpha beta gamma n m) w.1, hMeas⟩ P hP ≤ _
    refine (hrisk P hP).trans (ENNReal.ofReal_le_ofReal ?_)
    have hrate : 0 ≤ upperRate d alpha beta gamma n m := by
      unfold upperRate oracleRate
      positivity
    have hm := mul_le_mul_of_nonneg_left
      ((min_le_right (1:ℝ) _).trans hbalance) hA.le
    nlinarith


end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
