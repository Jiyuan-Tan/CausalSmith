module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.AnnotationImprovement
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.AnnotationLiminf
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.T_SharpAnnotationFrontier
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Order.LiminfLimsup

/-!
# T_AnnotationThreshold

Two-channel point-CATE annotation frontier: T_AnnotationThreshold
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
set_option linter.unnecessarySeqFocus false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


/-- Kennedy, Balakrishnan, Robins and Wasserman (2024), Section 3, Theorem 1,
has exactly the same numerical supervised exponents and cutoff after substituting
the nuisance-average smoothness. This is only a descriptive formula comparison.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input n](hyp:n), [the published benchmark eq supervised rate conclusion](goal) holds. -/
lemma published_benchmark_eq_supervised_rate (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (n : ℕ) :
    kbrwBenchmarkRate d alpha beta gamma n = sharpRate d alpha beta gamma n 0 := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hS : 0 < alpha+beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hA : 0 < 2*gamma+(d:ℝ) := by positivity
  have hD : 0 < bigDelta d alpha beta gamma := by dsimp [bigDelta]; positivity
  have hden : 0 < 1+(d:ℝ)/(2*gamma) := by positivity
  have hcut : ((d:ℝ)/4)/(1+(d:ℝ)/(2*gamma)) = sCrit d gamma/2 := by
    dsimp [sCrit]
    field_simp
    <;> ring
  have hpair : 1/(1+(d:ℝ)/(2*gamma)+(d:ℝ)/(4*((alpha+beta)/2))) =
      2*gamma/bigDelta d alpha beta gamma := by
    dsimp [bigDelta]
    field_simp
    <;> ring
  have horacle : 1/(2+(d:ℝ)/gamma) = gamma/(2*gamma+(d:ℝ)) := by
    field_simp
  have hcond : (alpha+beta)/2 < ((d:ℝ)/4)/(1+(d:ℝ)/(2*gamma)) ↔
      alpha+beta < sCrit d gamma := by rw [hcut]; constructor <;> intro h <;> linarith
  unfold kbrwBenchmarkRate
  simp only [hcond, hpair, horacle]
  by_cases hn : 2 ≤ n
  · obtain ⟨hsmall, hlarge⟩ := supervised_rate_branches d alpha beta gamma L eps hdom n hn
    by_cases hs : alpha+beta < sCrit d gamma
    · rw [if_pos hs, hsmall hs]
    · rw [if_neg hs, hlarge (le_of_not_gt hs)]
      rfl
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · have ho : -(gamma/(2*gamma+(d:ℝ))) ≠ 0 := ne_of_lt (neg_neg_of_pos (div_pos hg hA))
      have hp : -(gamma/bigDelta d alpha beta gamma) ≠ 0 := ne_of_lt (neg_neg_of_pos (div_pos hg hD))
      have hp2 : -(2*gamma/bigDelta d alpha beta gamma) ≠ 0 :=
        ne_of_lt (neg_neg_of_pos (div_pos (mul_pos (by norm_num) hg) hD))
      simp only [sharpRate, Nat.cast_zero, add_zero, zero_mul]
      change (if alpha+beta < sCrit d gamma then _ else _) =
        max ((0:ℝ)^(-(gamma/(2*gamma+(d:ℝ)))))
          ((0:ℝ)^(-(gamma/bigDelta d alpha beta gamma)))
      split_ifs <;> simp [Real.zero_rpow, ho, hp, hp2]
    · split_ifs <;> simp [sharpRate]

-- @node: lem:published-cate-benchmark
/-- For [positive dimension](hyp:d), [positive first nuisance smoothness](hyp:alpha),
[positive second nuisance smoothness](hyp:beta), and [effect smoothness at least one](hyp:gamma),
the published point-CATE benchmark's [two exponent identities, cutoff equivalence, and
piecewise maximum formula all hold](goal). -/
lemma published_cate_benchmark (d : ℕ) (alpha beta gamma : ℝ) :
    PublishedCateBenchmark d alpha beta gamma := by
  intro hd ha hb hg
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hg0 : 0 < gamma := lt_of_lt_of_le zero_lt_one hg
  have hS : 0 < alpha + beta := add_pos ha hb
  have hA : 0 < 2 * gamma + (d : ℝ) := by positivity
  have hD : 0 < 2 * gamma + (d : ℝ) + gamma * (d : ℝ) / (alpha + beta) := by
    positivity
  have hpair :
      1 / (1 + (d : ℝ) / (2 * gamma) + (d : ℝ) / (4 * ((alpha + beta) / 2))) =
        2 * gamma / (2 * gamma + (d : ℝ) + gamma * (d : ℝ) / (alpha + beta)) := by
    field_simp
    <;> ring
  have horacle :
      1 / (2 + (d : ℝ) / gamma) = gamma / (2 * gamma + (d : ℝ)) := by
    field_simp
  have hcutEq :
      ((d : ℝ) / 4) / (1 + (d : ℝ) / (2 * gamma)) =
        (gamma * (d : ℝ) / (2 * gamma + (d : ℝ))) / 2 := by
    field_simp
    <;> ring
  have hcut :
      (alpha + beta) / 2 < ((d : ℝ) / 4) / (1 + (d : ℝ) / (2 * gamma)) ↔
        alpha + beta < gamma * (d : ℝ) / (2 * gamma + (d : ℝ)) := by
    rw [hcutEq]
    constructor <;> intro h <;> linarith
  refine ⟨hpair, horacle, hcut, ?_⟩
  intro n hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  unfold kbrwBenchmarkRate
  rw [hpair, horacle]
  by_cases hs : alpha + beta < gamma * (d : ℝ) / (2 * gamma + (d : ℝ))
  · rw [if_pos (hcut.mpr hs)]
    symm
    apply max_eq_right
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have hSA : (alpha + beta) * (2 * gamma + (d : ℝ)) < gamma * (d : ℝ) :=
      (lt_div_iff₀ hA).mp hs
    have hAS : 2 * gamma + (d : ℝ) < gamma * (d : ℝ) / (alpha + beta) := by
      apply (lt_div_iff₀ hS).mpr
      nlinarith
    have htwice :
        2 * (2 * gamma + (d : ℝ)) ≤
          2 * gamma + (d : ℝ) + gamma * (d : ℝ) / (alpha + beta) := by
      linarith
    have hexp :
        2 * gamma / (2 * gamma + (d : ℝ) + gamma * (d : ℝ) / (alpha + beta)) ≤
          gamma / (2 * gamma + (d : ℝ)) := by
      apply (div_le_div_iff₀ hD hA).mpr
      nlinarith [mul_le_mul_of_nonneg_left htwice hg0.le]
    linarith
  · rw [if_neg (mt hcut.mp hs)]
    symm
    apply max_eq_left
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have hs' : gamma * (d : ℝ) / (2 * gamma + (d : ℝ)) ≤ alpha + beta :=
      le_of_not_gt hs
    have hgd : gamma * (d : ℝ) ≤ (alpha + beta) * (2 * gamma + (d : ℝ)) :=
      (div_le_iff₀ hA).mp hs'
    have hquot : gamma * (d : ℝ) / (alpha + beta) ≤ 2 * gamma + (d : ℝ) := by
      apply (div_le_iff₀ hS).mpr
      nlinarith
    have htwice :
        2 * gamma + (d : ℝ) + gamma * (d : ℝ) / (alpha + beta) ≤
          2 * (2 * gamma + (d : ℝ)) := by
      linarith
    have hexp :
        gamma / (2 * gamma + (d : ℝ)) ≤
          2 * gamma / (2 * gamma + (d : ℝ) + gamma * (d : ℝ) / (alpha + beta)) := by
      apply (div_le_div_iff₀ hA hD).mpr
      nlinarith [mul_le_mul_of_nonneg_left htwice hg0.le]
    linarith

/-- The frontier lower bound and its explicit decision give both sample-growth directions.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the annotation acquisition conclusion](goal) holds. -/
lemma annotation_acquisition
    (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    let r := sharpRate d alpha beta gamma
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ -- @realizes c(positive necessity constant) @realizes C(finite positive sufficiency constant)
       ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 → -- @realizes epsilon(target absolute-error scale)
      ∀ (n m : ℕ), 2 ≤ n →
      ((∃ T : Decision d n m, ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
        risk T P hP ≤ ENNReal.ofReal epsilon) →
        c*epsilon^(-(2+(d:ℝ)/gamma)) ≤ (n:ℝ) ∧
        c*epsilon^(-(2+(d:ℝ)/gamma+(d:ℝ)/(alpha+beta))) ≤ (n:ℝ)*((n:ℝ)+m)) ∧
      (C*epsilon^(-(2+(d:ℝ)/gamma)) ≤ (n:ℝ) →
        C*epsilon^(-(2+(d:ℝ)/gamma+(d:ℝ)/(alpha+beta))) ≤ (n:ℝ)*((n:ℝ)+m) →
        ∃ hMeas : Measurable (sharpDecision d alpha beta gamma eps n m),
          ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
            risk ⟨sharpDecision d alpha beta gamma eps n m,hMeas⟩ P hP ≤ ENNReal.ofReal epsilon) ∧
      (r n m ≤ epsilon ↔
        epsilon^(-(2+(d:ℝ)/gamma)) ≤ (n:ℝ) ∧
        epsilon^(-(2+(d:ℝ)/gamma+(d:ℝ)/(alpha+beta))) ≤ (n:ℝ)*((n:ℝ)+m)) ∧
      (n:ℝ) ≤ (n:ℝ)+m := by
  obtain ⟨cF, CF, hcF, hcFC, hfrontier⟩ :=
    sharp_annotation_frontier d alpha beta gamma L eps hdom
  have hCF : 0 < CF := hcF.trans_le hcFC
  let p0 : ℝ := 2+(d:ℝ)/gamma
  let p1 : ℝ := 2+(d:ℝ)/gamma+(d:ℝ)/(alpha+beta)
  have hscale (e c p : ℝ) (he : 0 < e) (hc : 0 < c) :
      (e/c)^(-p) = c^p * e^(-p) := by
    rw [Real.div_rpow he.le hc.le, Real.rpow_neg hc.le, div_eq_mul_inv, inv_inv]
    ring
  refine ⟨min (cF^p0) (cF^p1), max (CF^p0) (CF^p1),
    lt_min (by positivity) (by positivity),
    lt_of_lt_of_le (by positivity : 0 < CF^p0) (le_max_left _ _), ?_⟩
  intro epsilon he he1 n m hn
  obtain ⟨hMeas, hlower, hmin, hupper, hall, hbranches⟩ := hfrontier n m hn
  refine ⟨?_, ?_, sharpRate_acquisition_iff d alpha beta gamma L eps hdom n m hn epsilon he,
    le_add_of_nonneg_right (Nat.cast_nonneg m)⟩
  · rintro ⟨T, hT⟩
    have hminT : minimaxRisk d alpha beta gamma L eps n m ≤ ENNReal.ofReal epsilon :=
      (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk T).trans
        (Causalean.Stat.worstCaseRiskENNReal_le (fun P => hT P.1 P.2))
    have hreal : cF*sharpRate d alpha beta gamma n m ≤ epsilon :=
      (ENNReal.ofReal_le_ofReal_iff he.le).mp (hlower.trans hminT)
    have hr : sharpRate d alpha beta gamma n m ≤ epsilon/cF :=
      (le_div_iff₀ hcF).mpr (by nlinarith [hreal])
    obtain ⟨h0, h1⟩ := (sharpRate_acquisition_iff d alpha beta gamma L eps hdom n m hn
      (epsilon/cF) (div_pos he hcF)).mp hr
    change (epsilon/cF)^(-p0) ≤ (n:ℝ) at h0
    change (epsilon/cF)^(-p1) ≤ (n:ℝ)*((n:ℝ)+m) at h1
    rw [hscale epsilon cF p0 he hcF] at h0
    rw [hscale epsilon cF p1 he hcF] at h1
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans h0,
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans h1⟩
  · intro h0 h1
    have hr : sharpRate d alpha beta gamma n m ≤ epsilon/CF := by
      apply (sharpRate_acquisition_iff d alpha beta gamma L eps hdom n m hn
        (epsilon/CF) (div_pos he hCF)).mpr
      change (epsilon/CF)^(-p0) ≤ (n:ℝ) ∧
        (epsilon/CF)^(-p1) ≤ (n:ℝ)*((n:ℝ)+m)
      rw [hscale epsilon CF p0 he hCF, hscale epsilon CF p1 he hCF]
      exact ⟨(mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans h0,
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans h1⟩
    refine ⟨hMeas, ?_⟩
    intro P hP
    have hpoint : risk ⟨sharpDecision d alpha beta gamma eps n m,hMeas⟩ P hP ≤
        ENNReal.ofReal (CF*sharpRate d alpha beta gamma n m) :=
      (Causalean.Stat.le_worstCaseRiskENNReal
        (risk := classRisk d alpha beta gamma L eps n m)
        ⟨sharpDecision d alpha beta gamma eps n m,hMeas⟩
        (⟨P, hP⟩ : {P : PrimitiveLaw d // PrimitiveClass alpha beta gamma L eps P})).trans hupper
    apply hpoint.trans
    apply ENNReal.ofReal_le_ofReal
    have hh := (le_div_iff₀ hCF).mp hr
    nlinarith

/-- Finite extended-real bounds retain both inequalities after taking real values.  Given [the specified input R](hyp:R), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the specified input hl](hyp:hl), [the specified input hu](hyp:hu), [the risk to real sandwich conclusion](goal) holds. -/
lemma risk_toReal_sandwich (R : ℝ≥0∞) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl : ENNReal.ofReal a ≤ R) (hu : R ≤ ENNReal.ofReal b) :
    a ≤ R.toReal ∧ R.toReal ≤ b := by
  have hfinite : R ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  refine ⟨?_, ENNReal.toReal_le_of_le_ofReal hb hu⟩
  simpa only [ENNReal.toReal_ofReal ha] using ENNReal.toReal_mono hfinite hl

/-- In the smooth regime the frontier upper bound divided by the oracle floor is uniform.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input hs](hyp:hs), [the smooth oracle risk ratio conclusion](goal) holds. -/
lemma smooth_oracle_risk_ratio
    (d : ℕ) (alpha beta gamma L eps : ℝ) (hdom : PublicDomain d alpha beta gamma L eps)
    (hs : sCrit d gamma ≤ alpha+beta) :
    ∃ K : ℝ, 0 < K ∧ ∀ n m, 2 ≤ n →
      (minimaxRisk d alpha beta gamma L eps n m).toReal /
        (oracleRisk d alpha beta gamma L eps n m).toReal ≤ K := by
  obtain ⟨cF, CF, hcF, hcFC, hfrontier⟩ :=
    sharp_annotation_frontier d alpha beta gamma L eps hdom
  obtain ⟨cO, CO, hcO, hcOC, horacle⟩ :=
    supplied_propensity d alpha beta gamma L eps hdom
  have hCF : 0 < CF := hcF.trans_le hcFC
  have hCO : 0 < CO := hcO.trans_le hcOC
  refine ⟨CF/cO, div_pos hCF hcO, ?_⟩
  intro n m hn
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hro : 0 < oracleRate d gamma n := Real.rpow_pos_of_pos hnpos _
  obtain ⟨hMeas, hl, hm, hu, hall, hbranches⟩ := hfrontier n m hn
  rw [hbranches.1 hs] at hl
  have hupper := hm.trans hu
  rw [hbranches.1 hs] at hupper
  have hrealF := risk_toReal_sandwich _ _ _ (mul_pos hcF hro).le
    (mul_pos hCF hro).le hl hupper
  have hrealO := risk_toReal_sandwich _ _ _ (mul_pos hcO hro).le
    (mul_pos hCO hro).le (horacle n m hn).1 (horacle n m hn).2.1
  have hden : 0 < (oracleRisk d alpha beta gamma L eps n m).toReal :=
    (mul_pos hcO hro).trans_le hrealO.1
  apply (div_le_iff₀ hden).mpr
  calc
    (minimaxRisk d alpha beta gamma L eps n m).toReal ≤ CF * oracleRate d gamma n := hrealF.2
    _ = (CF/cO) * (cO * oracleRate d gamma n) := by field_simp
    _ ≤ (CF/cO) * (oracleRisk d alpha beta gamma L eps n m).toReal :=
      mul_le_mul_of_nonneg_left hrealO.1 (div_pos hCF hcO).le

/-- Bounded auxiliary counts change either branch of the maximum rate by only a fixed factor.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input K](hyp:K), [the specified input hK](hyp:hK), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input hm](hyp:hm), [the sharp rate bounded auxiliary comparison conclusion](goal) holds. -/
lemma sharpRate_bounded_auxiliary_comparison (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (K : ℝ) (hK : 0 ≤ K)
    (n m : ℕ) (hn : 2 ≤ n) (hm : (m:ℝ) ≤ K*(n:ℝ)) :
    sharpRate d alpha beta gamma n m ≤ sharpRate d alpha beta gamma n 0 ∧
    sharpRate d alpha beta gamma n 0 ≤
      (1+K)^(gamma/bigDelta d alpha beta gamma) * sharpRate d alpha beta gamma n m := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hS : 0 < alpha+beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hD : 0 < bigDelta d alpha beta gamma := by dsimp [bigDelta]; positivity
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  let p : ℝ := gamma/bigDelta d alpha beta gamma
  let M : ℝ := (1+K)^p
  have hp : 0 < p := div_pos hg hD
  have hM : 0 < M := Real.rpow_pos_of_pos (by linarith) _
  have hM1 : 1 ≤ M := Real.one_le_rpow (by linarith) hp.le
  have hbase : (n:ℝ)*(n:ℝ) ≤ (n:ℝ)*((n:ℝ)+m) := by nlinarith [show (0:ℝ) ≤ m from Nat.cast_nonneg m]
  have hbase' : (n:ℝ)*((n:ℝ)+m) ≤ (1+K)*((n:ℝ)*(n:ℝ)) := by nlinarith
  have hpair := Real.rpow_le_rpow_of_nonpos (mul_pos hnpos hnpos) hbase (neg_nonpos.mpr hp.le)
  have hpair' := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (n:ℝ)*((n:ℝ)+m))
    hbase' (neg_nonpos.mpr hp.le)
  rw [Real.mul_rpow (by linarith : 0 ≤ 1+K) (mul_self_nonneg (n:ℝ)),
    Real.rpow_neg (by linarith : 0 ≤ 1+K)] at hpair'
  have hscaled : ((n:ℝ)*(n:ℝ))^(-p) ≤ M*((n:ℝ)*((n:ℝ)+m))^(-p) := by
    have ht := mul_le_mul_of_nonneg_left hpair' hM.le
    change M * (M⁻¹ * ((n:ℝ)*(n:ℝ))^(-p)) ≤ _ at ht
    simpa only [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul] using ht
  change max (oracleRate d gamma n) (((n:ℝ)*((n:ℝ)+m))^(-p)) ≤
      max (oracleRate d gamma n) (((n:ℝ)*((n:ℝ)+(0:ℕ)))^(-p)) ∧
    max (oracleRate d gamma n) (((n:ℝ)*((n:ℝ)+(0:ℕ)))^(-p)) ≤
      M * max (oracleRate d gamma n) (((n:ℝ)*((n:ℝ)+m))^(-p))
  simp only [Nat.cast_zero, add_zero]
  refine ⟨max_le_max le_rfl hpair, max_le ?_ ?_⟩
  · calc
      oracleRate d gamma n ≤ M * oracleRate d gamma n :=
        le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) hM1
      _ ≤ M * max (oracleRate d gamma n) (((n:ℝ)*((n:ℝ)+m))^(-p)) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hM.le
  · exact hscaled.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hM.le)

/-- A bounded auxiliary-to-labeled ratio preserves the supervised minimax order in both directions.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input mseq](hyp:mseq), [the specified input hseq](hyp:hseq), [the bounded auxiliary risk order conclusion](goal) holds. -/
lemma bounded_auxiliary_risk_order
    (d : ℕ) (alpha beta gamma L eps : ℝ) (hdom : PublicDomain d alpha beta gamma L eps)
    (mseq : ℕ → ℕ)
    (hseq : Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (mseq n:ℝ)/(n:ℝ))
      (fun _ : ℕ => (1:ℝ))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (minimaxRisk d alpha beta gamma L eps n (mseq n)).toReal)
      (fun n => (minimaxRisk d alpha beta gamma L eps n 0).toReal) ∧
    Asymptotics.IsBigO Filter.atTop
      (fun n => (minimaxRisk d alpha beta gamma L eps n 0).toReal)
      (fun n => (minimaxRisk d alpha beta gamma L eps n (mseq n)).toReal) := by
  obtain ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp hseq
  obtain ⟨c, C, hc, hcC, hfrontier⟩ :=
    sharp_annotation_frontier d alpha beta gamma L eps hdom
  have hC : 0 < C := hc.trans_le hcC
  let M : ℝ := (1+max K 0)^(gamma/bigDelta d alpha beta gamma)
  have hM : 0 < M := Real.rpow_pos_of_pos (by positivity) _
  have hreal (n m : ℕ) (hn : 2 ≤ n) :
      c*sharpRate d alpha beta gamma n m ≤ (minimaxRisk d alpha beta gamma L eps n m).toReal ∧
      (minimaxRisk d alpha beta gamma L eps n m).toReal ≤ C*sharpRate d alpha beta gamma n m := by
    obtain ⟨hMeas, hl, hm, hu, hall, hb⟩ := hfrontier n m hn
    have hr : 0 ≤ sharpRate d alpha beta gamma n m :=
      (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans (le_max_left _ _)
    exact risk_toReal_sandwich _ _ _ (mul_nonneg hc.le hr) (mul_nonneg hC.le hr) hl (hm.trans hu)
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      (minimaxRisk d alpha beta gamma L eps n (mseq n)).toReal ≤
        (C/c)*(minimaxRisk d alpha beta gamma L eps n 0).toReal ∧
      (minimaxRisk d alpha beta gamma L eps n 0).toReal ≤
        (C*M/c)*(minimaxRisk d alpha beta gamma L eps n (mseq n)).toReal := by
    filter_upwards [hK, Filter.eventually_ge_atTop (2 : ℕ)] with n hkn hn
    have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    simp only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (mseq n:ℝ)/(n:ℝ) from div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      abs_one, mul_one] at hkn
    have hm : (mseq n:ℝ) ≤ max K 0 * (n:ℝ) :=
      (div_le_iff₀ hnpos).mp (hkn.trans (le_max_left _ _))
    have hrates := sharpRate_bounded_auxiliary_comparison d alpha beta gamma L eps hdom
      (max K 0) (le_max_right _ _) n (mseq n) hn hm
    obtain ⟨hl0, hu0⟩ := hreal n 0 hn
    obtain ⟨hlm, hum⟩ := hreal n (mseq n) hn
    constructor
    · calc
        _ ≤ C*sharpRate d alpha beta gamma n (mseq n) := hum
        _ ≤ C*sharpRate d alpha beta gamma n 0 := mul_le_mul_of_nonneg_left hrates.1 hC.le
        _ = (C/c)*(c*sharpRate d alpha beta gamma n 0) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hl0 (div_pos hC hc).le
    · calc
        _ ≤ C*sharpRate d alpha beta gamma n 0 := hu0
        _ ≤ C*(M*sharpRate d alpha beta gamma n (mseq n)) := mul_le_mul_of_nonneg_left hrates.2 hC.le
        _ = (C*M/c)*(c*sharpRate d alpha beta gamma n (mseq n)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlm (by positivity)
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨C/c, ?_⟩
    filter_upwards [hevent] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hn.1
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨C*M/c, ?_⟩
    filter_upwards [hevent] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hn.2

/-- Uniform positive sandwiches compare ratios in both directions.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input r](hyp:r), [the specified input s](hyp:s), [the specified input cF](hyp:cF), [the specified input CF](hyp:CF), [the specified input cG](hyp:cG), [the specified input CG](hyp:CG), [the specified input hcF](hyp:hcF), [the specified input hCF](hyp:hCF), [the specified input hcG](hyp:hcG), [the specified input hCG](hyp:hCG), [the specified input hr](hyp:hr), [the specified input hs](hyp:hs), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the positive sandwich ratio bounds conclusion](goal) holds. -/
lemma positive_sandwich_ratio_bounds (f g r s cF CF cG CG : ℝ)
    (hcF : 0 < cF) (hCF : 0 < CF) (hcG : 0 < cG) (hCG : 0 < CG)
    (hr : 0 < r) (hs : 0 < s)
    (hf : cF*r ≤ f ∧ f ≤ CF*r) (hg : cG*s ≤ g ∧ g ≤ CG*s) :
    0 ≤ f/g ∧ f/g ≤ (CF/cG)*(r/s) ∧ r/s ≤ (CG/cF)*(f/g) := by
  have hfpos := (mul_pos hcF hr).trans_le hf.1
  have hgpos := (mul_pos hcG hs).trans_le hg.1
  refine ⟨(div_pos hfpos hgpos).le, ?_, ?_⟩
  · calc
      f/g ≤ (CF*r)/(cG*s) := div_le_div₀ (mul_pos hCF hr).le hf.2
        (mul_pos hcG hs) hg.1
      _ = (CF/cG)*(r/s) := by ring
  · have ht : (cF*r)/(CG*s) ≤ f/g :=
      div_le_div₀ hfpos.le hf.1 hgpos hg.2
    have ht' := mul_le_mul_of_nonneg_left ht (div_pos hCG hcF).le
    have heq : (CG/cF)*((cF*r)/(CG*s)) = r/s := by field_simp
    rwa [heq] at ht'

/-- Comparable nonnegative sequences have the same boundedness and zero-limit behavior.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input A](hyp:A), [the specified input B](hyp:B), [the specified input hA](hyp:hA), [the specified input hB](hyp:hB), [the specified input h](hyp:h), [the comparable nonnegative sequences conclusion](goal) holds. -/
lemma comparable_nonnegative_sequences (f g : ℕ → ℝ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ᶠ n in Filter.atTop, 0 ≤ f n ∧ 0 ≤ g n ∧ f n ≤ A*g n ∧ g n ≤ B*f n) :
    (Asymptotics.IsBigO Filter.atTop f (fun _ => (1:ℝ)) ↔
      Asymptotics.IsBigO Filter.atTop g (fun _ => (1:ℝ))) ∧
    (Filter.Tendsto f Filter.atTop (nhds 0) ↔ Filter.Tendsto g Filter.atTop (nhds 0)) := by
  constructor
  · constructor
    · intro hf
      obtain ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp hf
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨B*K, ?_⟩
      filter_upwards [h, hK] with n hn hkn
      simp only [Real.norm_eq_abs, abs_of_nonneg hn.1, abs_one, mul_one] at hkn
      simpa only [Real.norm_eq_abs, abs_of_nonneg hn.2.1, abs_one, mul_one] using
        hn.2.2.2.trans (mul_le_mul_of_nonneg_left hkn hB)
    · intro hg
      obtain ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp hg
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨A*K, ?_⟩
      filter_upwards [h, hK] with n hn hkn
      simp only [Real.norm_eq_abs, abs_of_nonneg hn.2.1, abs_one, mul_one] at hkn
      simpa only [Real.norm_eq_abs, abs_of_nonneg hn.1, abs_one, mul_one] using
        hn.2.2.1.trans (mul_le_mul_of_nonneg_left hkn hA)
  · constructor
    · intro hf
      apply squeeze_zero' (h.mono fun n hn => hn.2.1) (h.mono fun n hn => hn.2.2.2)
      simpa only [mul_zero] using hf.const_mul B
    · intro hg
      apply squeeze_zero' (h.mono fun n hn => hn.1) (h.mono fun n hn => hn.2.2.1)
      simpa only [mul_zero] using hg.const_mul A

/-- Dividing by a positive rate converts a big-O comparison into boundedness.  Given [the specified input r](hyp:r), [the specified input s](hyp:s), [the specified input h](hyp:h), [the nonnegative rate big o div iff conclusion](goal) holds. -/
lemma nonnegative_rate_bigO_div_iff (r s : ℕ → ℝ)
    (h : ∀ᶠ n in Filter.atTop, 0 ≤ r n ∧ 0 < s n) :
    Asymptotics.IsBigO Filter.atTop (fun n => r n/s n) (fun _ => (1:ℝ)) ↔
      Asymptotics.IsBigO Filter.atTop r s := by
  constructor <;> intro hh
  · obtain ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp hh
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨K, ?_⟩
    filter_upwards [h, hK] with n hn hkn
    simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn.1 hn.2.le),
      abs_one, mul_one] at hkn
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn.1, abs_of_pos hn.2] using
      (div_le_iff₀ hn.2).mp hkn
  · obtain ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp hh
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨K, ?_⟩
    filter_upwards [h, hK] with n hn hkn
    simp only [Real.norm_eq_abs, abs_of_nonneg hn.1, abs_of_pos hn.2] at hkn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn.1 hn.2.le),
      abs_one, mul_one] using (div_le_iff₀ hn.2).mpr hkn

/-- The frontier and supplied-propensity bounds give real-valued uniform sandwiches.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the annotation risk sandwiches conclusion](goal) holds. -/
lemma annotation_risk_sandwiches
    (d : ℕ) (alpha beta gamma L eps : ℝ) (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ cF CF cO CO : ℝ, 0 < cF ∧ 0 < CF ∧ 0 < cO ∧ 0 < CO ∧
      ∀ n m, 2 ≤ n →
        (cF*sharpRate d alpha beta gamma n m ≤ (minimaxRisk d alpha beta gamma L eps n m).toReal ∧
          (minimaxRisk d alpha beta gamma L eps n m).toReal ≤ CF*sharpRate d alpha beta gamma n m) ∧
        (cO*oracleRate d gamma n ≤ (oracleRisk d alpha beta gamma L eps n m).toReal ∧
          (oracleRisk d alpha beta gamma L eps n m).toReal ≤ CO*oracleRate d gamma n) := by
  obtain ⟨cF, CF, hcF, hcFC, hfrontier⟩ :=
    sharp_annotation_frontier d alpha beta gamma L eps hdom
  obtain ⟨cO, CO, hcO, hcOC, horacle⟩ :=
    supplied_propensity d alpha beta gamma L eps hdom
  have hCF := hcF.trans_le hcFC
  have hCO := hcO.trans_le hcOC
  refine ⟨cF, CF, cO, CO, hcF, hCF, hcO, hCO, ?_⟩
  intro n m hn
  have hro : 0 ≤ oracleRate d gamma n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hr : 0 ≤ sharpRate d alpha beta gamma n m := hro.trans (le_max_left _ _)
  obtain ⟨hMeas, hl, hm, hu, hall, hb⟩ := hfrontier n m hn
  exact ⟨risk_toReal_sandwich _ _ _ (mul_nonneg hcF.le hr) (mul_nonneg hCF.le hr) hl (hm.trans hu),
    risk_toReal_sandwich _ _ _ (mul_nonneg hcO.le hro) (mul_nonneg hCO.le hro)
      (horacle n m hn).1 (horacle n m hn).2.1⟩

/-- Risk and numerical rate comparisons coincide along every auxiliary-size sequence.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input mseq](hyp:mseq), [the annotation risk rate equivalences conclusion](goal) holds. -/
lemma annotation_risk_rate_equivalences
    (d : ℕ) (alpha beta gamma L eps : ℝ) (hdom : PublicDomain d alpha beta gamma L eps)
    (mseq : ℕ → ℕ) :
    let R := fun n m => (minimaxRisk d alpha beta gamma L eps n m).toReal
    let Re := fun n m => (oracleRisk d alpha beta gamma L eps n m).toReal
    let r := sharpRate d alpha beta gamma
    let ro := oracleRate d gamma
    (Asymptotics.IsBigO Filter.atTop (fun n => R n (mseq n)/Re n (mseq n)) (fun _ => (1:ℝ)) ↔
      Asymptotics.IsBigO Filter.atTop (fun n => r n (mseq n)) ro) ∧
    (Filter.Tendsto (fun n => R n (mseq n)/R n 0) Filter.atTop (nhds 0) ↔
      Filter.Tendsto (fun n => r n (mseq n)/r n 0) Filter.atTop (nhds 0)) ∧
    (Asymptotics.IsBigO Filter.atTop (fun n => R n (mseq n)/Re n (mseq n)) (fun _ => (1:ℝ)) ↔
      ∃ zeta : ℝ, 1 ≤ zeta ∧ ∀ᶠ n in Filter.atTop,
        (n,mseq n) ∈ annotationRegion d alpha beta gamma zeta) := by
  obtain ⟨cF, CF, cO, CO, hcF, hCF, hcO, hCO, hb⟩ :=
    annotation_risk_sandwiches d alpha beta gamma L eps hdom
  have hpos (n : ℕ) (hn : 2 ≤ n) : 0 < oracleRate d gamma n ∧
      ∀ m, 0 < sharpRate d alpha beta gamma n m := by
    have hnp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    have ho : 0 < oracleRate d gamma n := Real.rpow_pos_of_pos hnp _
    exact ⟨ho, fun m => ho.trans_le (le_max_left _ _)⟩
  have hratios : ∀ᶠ n : ℕ in Filter.atTop,
      0 ≤ (minimaxRisk d alpha beta gamma L eps n (mseq n)).toReal /
        (oracleRisk d alpha beta gamma L eps n (mseq n)).toReal ∧
      0 ≤ sharpRate d alpha beta gamma n (mseq n)/oracleRate d gamma n ∧
      (minimaxRisk d alpha beta gamma L eps n (mseq n)).toReal /
        (oracleRisk d alpha beta gamma L eps n (mseq n)).toReal ≤
        (CF/cO)*(sharpRate d alpha beta gamma n (mseq n)/oracleRate d gamma n) ∧
      sharpRate d alpha beta gamma n (mseq n)/oracleRate d gamma n ≤
        (CO/cF)*((minimaxRisk d alpha beta gamma L eps n (mseq n)).toReal /
          (oracleRisk d alpha beta gamma L eps n (mseq n)).toReal) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hh := positive_sandwich_ratio_bounds _ _ _ _ _ _ _ _ hcF hCF hcO hCO
      ((hpos n hn).2 _) (hpos n hn).1 (hb n (mseq n) hn).1 (hb n (mseq n) hn).2
    exact ⟨hh.1, (div_pos ((hpos n hn).2 _) (hpos n hn).1).le, hh.2⟩
  have hbig := (comparable_nonnegative_sequences _ _ (CF/cO) (CO/cF)
    (div_pos hCF hcO).le (div_pos hCO hcF).le hratios).1
  have hrate := nonnegative_rate_bigO_div_iff
    (fun n => sharpRate d alpha beta gamma n (mseq n)) (oracleRate d gamma)
    (by
      filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
      exact ⟨((hpos n hn).2 _).le, (hpos n hn).1⟩)
  refine ⟨hbig.trans hrate, ?_, ?_⟩
  · apply (comparable_nonnegative_sequences _ _ (CF/cF) (CF/cF)
      (div_pos hCF hcF).le (div_pos hCF hcF).le ?_).2
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hh := positive_sandwich_ratio_bounds _ _ _ _ _ _ _ _ hcF hCF hcF hCF
      ((hpos n hn).2 _) ((hpos n hn).2 0)
      (hb n (mseq n) hn).1 (hb n 0 hn).1
    exact ⟨hh.1, (div_pos ((hpos n hn).2 _) ((hpos n hn).2 0)).le, hh.2⟩
  · rw [hbig.trans hrate]
    constructor
    · intro h
      obtain ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp h
      refine ⟨max K 1, le_max_right _ _, ?_⟩
      filter_upwards [hK, Filter.eventually_ge_atTop (2 : ℕ)] with n hkn hn
      have hp := hpos n hn
      simp only [Real.norm_eq_abs, abs_of_pos (hp.2 _), abs_of_pos hp.1] at hkn
      exact ⟨hn, hkn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.1.le)⟩
    · rintro ⟨zeta, hzeta, hregion⟩
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨zeta, ?_⟩
      filter_upwards [hregion] with n hn
      have hp := hpos n hn.1
      simpa only [Real.norm_eq_abs, abs_of_pos (hp.2 _), abs_of_pos hp.1] using hn.2

open Filter
-- @node: prop:annotation-threshold
/-- Oracle attainment, strict benefit, all rate branches, supervised comparison,
and necessary and sufficient acquisition requirements for the established frontier.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the annotation threshold conclusion](goal) holds. -/
theorem annotation_threshold
    (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    let R := fun n m => (minimaxRisk d alpha beta gamma L eps n m).toReal
    let Re := fun n m => (oracleRisk d alpha beta gamma L eps n m).toReal
    let r := sharpRate d alpha beta gamma
    let ro := oracleRate d gamma
    (∀ mseq : ℕ → ℕ, -- @realizes mn(auxiliary-size sequence)
      (Asymptotics.IsBigO atTop (fun n : ℕ => R n (mseq n)/Re n (mseq n)) (fun _ : ℕ => (1:ℝ)) ↔
        Asymptotics.IsBigO atTop (fun n : ℕ => r n (mseq n)) ro) ∧
      (Tendsto (fun n : ℕ => R n (mseq n)/R n 0) atTop (nhds 0) ↔
        Tendsto (fun n : ℕ => r n (mseq n)/r n 0) atTop (nhds 0)) ∧
      (Asymptotics.IsBigO atTop (fun n : ℕ => R n (mseq n)/Re n (mseq n)) (fun _ : ℕ => (1:ℝ)) ↔
        ∃ zeta : ℝ, 1 ≤ zeta ∧ ∀ᶠ n in atTop, (n,mseq n) ∈ annotationRegion d alpha beta gamma zeta) ∧ -- @realizes zeta(finite oracle-order tolerance)
      (Asymptotics.IsBigO atTop (fun n : ℕ => R n (mseq n)/Re n (mseq n)) (fun _ : ℕ => (1:ℝ)) ↔
        0 < Filter.liminf (fun n : ℕ => ENNReal.ofReal (((n:ℝ)+mseq n)/(n:ℝ)^qStar d alpha beta gamma)) atTop) ∧
      (Tendsto (fun n : ℕ => R n (mseq n)/R n 0) atTop (nhds 0) ↔
        alpha+beta < sCrit d gamma ∧ Tendsto (fun n : ℕ => (mseq n:ℝ)/(n:ℝ)) atTop atTop)) ∧
    (alpha+beta < sCrit d gamma → 1 < qStar d alpha beta gamma) ∧
    (∀ mseq : ℕ → ℕ, Asymptotics.IsBigO atTop (fun n : ℕ => (mseq n:ℝ)/(n:ℝ)) (fun _ : ℕ => (1:ℝ)) →
      Asymptotics.IsBigO atTop (fun n : ℕ => R n (mseq n)) (fun n : ℕ => R n 0) ∧
      Asymptotics.IsBigO atTop (fun n : ℕ => R n 0) (fun n : ℕ => R n (mseq n))) ∧
    (sCrit d gamma ≤ alpha+beta → ∀ mseq : ℕ → ℕ,
      Asymptotics.IsBigO atTop (fun n : ℕ => R n (mseq n)/Re n (mseq n)) (fun _ : ℕ => (1:ℝ))) ∧
    (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ -- @realizes c(positive claim-local constant) @realizes C(finite claim-local upper constant)
       ∀ (n m : ℕ), 2 ≤ n →
      ENNReal.ofReal (c*r n m) ≤ minimaxRisk d alpha beta gamma L eps n m ∧
      minimaxRisk d alpha beta gamma L eps n m ≤ ENNReal.ofReal (C*r n m) ∧
      (sCrit d gamma ≤ alpha+beta → r n m = ro n) ∧
      (alpha+beta < sCrit d gamma → (n:ℝ)+m ≤ (n:ℝ)^qStar d alpha beta gamma →
        r n m = ((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma))) ∧
      (alpha+beta < sCrit d gamma → (n:ℝ)^qStar d alpha beta gamma ≤ (n:ℝ)+m → r n m = ro n) ∧
      ((n:ℝ)+m = (n:ℝ)^qStar d alpha beta gamma →
        ((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma)) = ro n)) ∧
    (∀ n, 2 ≤ n →
      (alpha+beta < sCrit d gamma → r n 0 = (n:ℝ)^(-(2*gamma/bigDelta d alpha beta gamma))) ∧
      (sCrit d gamma ≤ alpha+beta → r n 0 = ro n)) ∧
    (∀ n, kbrwBenchmarkRate d alpha beta gamma n = r n 0) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ -- @realizes c(positive necessity constant) @realizes C(finite positive sufficiency constant)
       ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 → -- @realizes epsilon(target absolute-error scale)
      ∀ (n m : ℕ), 2 ≤ n →
      ((∃ T : Decision d n m, ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
        risk T P hP ≤ ENNReal.ofReal epsilon) →
        c*epsilon^(-(2+(d:ℝ)/gamma)) ≤ (n:ℝ) ∧
        c*epsilon^(-(2+(d:ℝ)/gamma+(d:ℝ)/(alpha+beta))) ≤ (n:ℝ)*((n:ℝ)+m)) ∧
      (C*epsilon^(-(2+(d:ℝ)/gamma)) ≤ (n:ℝ) →
        C*epsilon^(-(2+(d:ℝ)/gamma+(d:ℝ)/(alpha+beta))) ≤ (n:ℝ)*((n:ℝ)+m) →
        ∃ hMeas : Measurable (sharpDecision d alpha beta gamma eps n m),
          ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
            risk ⟨sharpDecision d alpha beta gamma eps n m,hMeas⟩ P hP ≤ ENNReal.ofReal epsilon) ∧
      (r n m ≤ epsilon ↔
        epsilon^(-(2+(d:ℝ)/gamma)) ≤ (n:ℝ) ∧
        epsilon^(-(2+(d:ℝ)/gamma+(d:ℝ)/(alpha+beta))) ≤ (n:ℝ)*((n:ℝ)+m)) ∧
      (n:ℝ) ≤ (n:ℝ)+m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro mseq
    obtain ⟨hbig, hzero, hregion⟩ :=
      annotation_risk_rate_equivalences d alpha beta gamma L eps hdom mseq
    refine ⟨hbig, hzero, hregion, ?_, ?_⟩
    · exact hregion.trans (annotationRegion_liminf_iff d alpha beta gamma L eps hdom mseq)
    · exact hzero.trans (annotation_rate_improvement_iff d alpha beta gamma L eps hdom mseq)
  · exact qStar_gt_one d alpha beta gamma L eps hdom
  · exact bounded_auxiliary_risk_order d alpha beta gamma L eps hdom
  · intro hs mseq
    obtain ⟨K, hK, hbound⟩ := smooth_oracle_risk_ratio d alpha beta gamma L eps hdom hs
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨K, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg), abs_one, mul_one]
    exact hbound n (mseq n) hn
  · obtain ⟨c, C, hc, hcC, hfrontier⟩ :=
      sharp_annotation_frontier d alpha beta gamma L eps hdom
    refine ⟨c, C, hc, hcC, ?_⟩
    intro n m hn
    obtain ⟨hMeas, hlower, hmin, hupper, hall, hbranches⟩ := hfrontier n m hn
    exact ⟨hlower, hmin.trans hupper, hbranches⟩
  · exact fun n hn => supervised_rate_branches d alpha beta gamma L eps hdom n hn
  · exact published_benchmark_eq_supervised_rate d alpha beta gamma L eps hdom
  · exact annotation_acquisition d alpha beta gamma L eps hdom

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
