module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.OracleRisk
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.UpperAssembly
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.FuzzyBlockTesting
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.OracleBlockInformation

/-!
# T_SuppliedPropensity

Two-channel point-CATE annotation frontier: T_SuppliedPropensity
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
set_option linter.style.haveILetI false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


variable {d : ℕ}
/-- Given [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [constant nuisance](goal) is the corresponding construction. -/
def ConstantNuisance {alpha beta gamma L eps : ℝ} (P : PrimitiveLaw d)
    (hP : PrimitiveClass alpha beta gamma L eps P) : Prop :=
  ∀ x ∈ cube d, designatedPropensity P hP x = 1/2 ∧ designatedControl P hP x = 1/2
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input n](hyp:n), [the specified input m](hyp:m), [oracle subfamily risk](goal) is the corresponding construction. -/
def oracleSubfamilyRisk (d : ℕ) (alpha beta gamma L eps : ℝ) (n m : ℕ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (T : OracleDecision d n m)
      (P : {P : PrimitiveLaw d // ∃ hP : PrimitiveClass alpha beta gamma L eps P, ConstantNuisance P hP}) =>
        ∫⁻ w, ENNReal.ofReal |T.1 w (designatedPropensity P.1 P.2.choose)-tau P.1 P.2.choose (x0 d)| ∂experiment P.1 n m)
/-- Restricting to the constant-nuisance subfamily can only decrease oracle minimax risk.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input n](hyp:n), [the specified input m](hyp:m), [the oracle subfamily risk le oracle risk conclusion](goal) holds. -/
lemma oracleSubfamilyRisk_le_oracleRisk (d : ℕ) (alpha beta gamma L eps : ℝ) (n m : ℕ) :
    oracleSubfamilyRisk d alpha beta gamma L eps n m ≤ oracleRisk d alpha beta gamma L eps n m := by
  unfold oracleSubfamilyRisk oracleRisk
  apply Causalean.Stat.minimaxValueENNReal_mono_class
    (fun P => ⟨P.1, P.2.choose⟩)
  intro T P
  exact le_rfl

/-- The supplied function is identical on the whole covariate space for every
member of the constant-nuisance subfamily, including its zero extension.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hconst](hyp:hconst), [the constant nuisance propensity eq conclusion](goal) holds. -/
lemma constantNuisance_propensity_eq {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (hconst : ConstantNuisance P hP) :
    designatedPropensity P hP = (fun x => if x ∈ cube d then 1/2 else 0) := by
  funext x
  by_cases hx : x ∈ cube d
  · rw [if_pos hx]
    exact (hconst x hx).1
  · simp only [designatedPropensity, if_neg hx]

/-- Singleton priors at the two explicit bump laws give an oracle-subfamily
lower bound: their supplied input is common, so the cited block test applies.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input h](hyp:h), [the specified input b](hyp:b), [the specified input hb](hyp:hb), [the specified input hn](hyp:hn), [the specified input hMembers](hyp:hMembers), [the specified input hconst](hyp:hconst), [the specified input htarget](hyp:htarget), [the specified input hhell](hyp:hhell), [the oracle bump testing lower conclusion](goal) holds. -/
lemma oracle_bump_testing_lower
    {d n m : ℕ} {alpha beta gamma L eps h b : ℝ}
    (hb : 0 < b) (hn : 0 < n)
    (hMembers : ∀ theta, PrimitiveClass alpha beta gamma L eps (oracleBumpPrimitive d h b theta))
    (hconst : ∀ theta, ConstantNuisance _ (hMembers theta))
    (htarget : ∀ theta, tau _ (hMembers theta) (x0 d) = thetaSign theta*b)
    (hhell : hellingerSq (experiment (oracleBumpPrimitive d h b true) n m)
      (experiment (oracleBumpPrimitive d h b false) n m) ≤ 1/16) :
    ENNReal.ofReal ((3/8:ℝ)*b) ≤ oracleSubfamilyRisk d alpha beta gamma L eps n m := by
  obtain ⟨Ψ, hΨ⟩ := oracle_bump_experiment_target_exists hn hMembers
  let E := fun theta => experiment (oracleBumpPrimitive d h b theta) n m
  let omega : Measure Unit := Measure.dirac ()
  let B : Kernel Unit (Sample d n m) := Kernel.const Unit (E true)
  let C : Kernel Unit (Sample d n m) := Kernel.const Unit (E false)
  letI := population_experiment_probability (oracleBumpPrimitive d h b true) n m
  letI := population_experiment_probability (oracleBumpPrimitive d h b false) n m
  have hsep : ∀ z z', 2*b ≤ Ψ (B z) - Ψ (C z') := by
    intro z z'
    change 2*b ≤ Ψ (E true) - Ψ (E false)
    rw [hΨ, hΨ, htarget, htarget]
    simp only [thetaSign, if_true, Bool.false_eq_true, if_false]
    linarith
  have hh : hellingerSq (omega.bind (fun z => B z))
      (omega.bind (fun z => C z)) ≤ 1/16 := by
    simpa [omega, B, C, E, Measure.dirac_bind, Kernel.measurable] using hhell
  unfold oracleSubfamilyRisk
  apply Causalean.Stat.le_minimaxValueENNReal
  intro T
  let e : Cov d → ℝ := fun x => if x ∈ cube d then 1/2 else 0
  let Model : Set (Measure (Sample d n m)) := Set.range E
  have htest := published_fuzzy_testing_block omega B C Model
    (fun _ => ⟨true, rfl⟩) (fun _ => ⟨false, rfl⟩)
    Ψ (2*b) (1/16) (by positivity) (by norm_num) (by norm_num)
    hsep hh (fun w => T.1 w e) (T.2 e)
  have hconstant : (3/8:ℝ)*b ≤
      (2*b/4)*(1-Real.sqrt ((1/16:ℝ)*(1-(1/16:ℝ)/4))) := by
    have ho := mul_le_mul_of_nonneg_left fuzzy_testing_overlap_sixteenth hb.le
    nlinarith
  apply (ENNReal.ofReal_le_ofReal hconstant).trans (htest.trans ?_)
  apply iSup_le
  intro P
  apply iSup_le
  rintro ⟨theta, rfl⟩
  rw [hΨ]
  have hprop := constantNuisance_propensity_eq _ (hMembers theta) (hconst theta)
  rw [show e = designatedPropensity _ (hMembers theta) from hprop.symm]
  exact Causalean.Stat.le_worstCaseRiskENNReal T
    (⟨oracleBumpPrimitive d h b theta, ⟨hMembers theta, hconst theta⟩⟩ :
      {P : PrimitiveLaw d // ∃ hP : PrimitiveClass alpha beta gamma L eps P, ConstantNuisance P hP})

/-- The same-class constant-nuisance subfamily has the irreducible oracle
outcome rate, uniformly over every auxiliary sample size.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the oracle subfamily lower rate conclusion](goal) holds. -/
lemma oracle_subfamily_lower_rate
    (d : ℕ) (alpha beta gamma L eps : ℝ) (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), 2 ≤ n →
      ENNReal.ofReal (c*oracleRate d gamma n) ≤ oracleSubfamilyRisk d alpha beta gamma L eps n m := by
  obtain ⟨eta, heta, hetas, hfamily⟩ := oracle_bump_testing_family d alpha beta gamma L eps hdom
  refine ⟨(3/8:ℝ)*eta, by positivity, ?_⟩
  intro n m hn
  obtain ⟨hmem, hinfo⟩ := hfamily n hn
  let H := (n:ℝ)^(-(1/(2*gamma+d)))
  let b := eta*oracleRate d gamma n
  let hMembers := fun theta => (hmem theta).choose
  have hversions (theta : Bool) := (hmem theta).choose_spec
  have hc : ∀ theta, ConstantNuisance _ (hMembers theta) := by
    intro theta x hx
    exact ⟨(hversions theta x hx).1, (hversions theta x hx).2.1⟩
  have ht : ∀ theta, tau _ (hMembers theta) (x0 d) = thetaSign theta*b := by
    intro theta
    have hx : x0 d ∈ cube d := by intro i; norm_num [x0, cube]
    simpa only [macroBump_at_x0, mul_one] using (hversions theta (x0 d) hx).2.2
  have hb : 0 < b := by dsimp [b, oracleRate]; positivity
  have hh : hellingerSq (experiment (oracleBumpPrimitive d H b true) n m)
      (experiment (oracleBumpPrimitive d H b false) n m) ≤ 1/16 := by
    have hsym : hellingerSq (experiment (oracleBumpPrimitive d H b true) n m)
        (experiment (oracleBumpPrimitive d H b false) n m) =
        hellingerSq (experiment (oracleBumpPrimitive d H b false) n m)
          (experiment (oracleBumpPrimitive d H b true) n m) := by
      unfold hellingerSq Causalean.Stat.hellingerSqDensity
      simp only [add_comm]
      apply integral_congr_ae
      filter_upwards [] with w
      ring
    rw [hsym]
    exact hinfo m
  have htest := oracle_bump_testing_lower hb (by omega : 0 < n) hMembers hc ht hh
  simpa only [b, mul_assoc] using htest

-- @node: thm:supplied-propensity
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the supplied propensity conclusion](goal) holds. -/
theorem supplied_propensity
    (d : ℕ) (alpha beta gamma L eps : ℝ) (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ -- @realizes c(positive claim-local constant) @realizes C(finite claim-local upper constant)
       ∀ (n m : ℕ), 2 ≤ n →
      ENNReal.ofReal (c*oracleRate d gamma n) ≤ oracleRisk d alpha beta gamma L eps n m ∧
      oracleRisk d alpha beta gamma L eps n m ≤ ENNReal.ofReal (C*oracleRate d gamma n) ∧
      (∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
        Measurable (fun w => oracleSmoother d gamma n m w (designatedPropensity P hP)) ∧
        (∀ w, |oracleSmoother d gamma n m w (designatedPropensity P hP)| ≤ 1) ∧
        (∫⁻ w, ENNReal.ofReal |oracleSmoother d gamma n m w (designatedPropensity P hP)-tau P hP (x0 d)| ∂experiment P n m) ≤
          ENNReal.ofReal (C*oracleRate d gamma n)) ∧
      ENNReal.ofReal (c*oracleRate d gamma n) ≤ oracleSubfamilyRisk d alpha beta gamma L eps n m := by
  suffices hcontent : ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ (n m : ℕ), 2 ≤ n →
        (∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
          (∫⁻ w, ENNReal.ofReal
            |oracleSmoother d gamma n m w (designatedPropensity P hP) - tau P hP (x0 d)|
            ∂experiment P n m) ≤ ENNReal.ofReal (C*oracleRate d gamma n)) ∧
        ENNReal.ofReal (c*oracleRate d gamma n) ≤ oracleSubfamilyRisk d alpha beta gamma L eps n m by
    obtain ⟨c, C, hc, hcC, hcontent⟩ := hcontent
    refine ⟨c, C, hc, hcC, ?_⟩
    intro n m hn
    obtain ⟨hupper, hlower⟩ := hcontent n m hn
    refine ⟨hlower.trans (oracleSubfamilyRisk_le_oracleRisk d alpha beta gamma L eps n m),
      oracleRisk_le_of_oracleSmoother d alpha beta gamma L eps n m _ hupper, ?_, hlower⟩
    intro P hP
    exact ⟨measurable_oracleSmoother_designated P hP n m,
      fun w => oracleSmoother_bounded d gamma n m w _, hupper P hP⟩
  obtain ⟨c, hc, hlower⟩ := oracle_subfamily_lower_rate d alpha beta gamma L eps hdom
  suffices hupper : ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n →
      ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
        (∫⁻ w, ENNReal.ofReal
          |oracleSmoother d gamma n m w (designatedPropensity P hP) - tau P hP (x0 d)|
          ∂experiment P n m) ≤ ENNReal.ofReal (C*oracleRate d gamma n) by
    obtain ⟨C, hC, hupper⟩ := hupper
    refine ⟨c, max c C, hc, le_max_left _ _, ?_⟩
    intro n m hn
    refine ⟨?_, hlower n m hn⟩
    intro P hP
    apply (hupper n m hn P hP).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_max_right c C)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact oracle_smoother_upper_rate d alpha beta gamma L eps hdom

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
