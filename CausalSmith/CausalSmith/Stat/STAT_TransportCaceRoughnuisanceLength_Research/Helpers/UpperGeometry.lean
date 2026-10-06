module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Identification
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Deterministic steps of the honest upper bound

These lemmas implement the coverage event, the zero-volume fallback, the
good-slope length bound (1), and the final two-regime calculation in the
honest-upper roadmap. The probabilistic moment and tail steps remain separate.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The calibrated radius is nonnegative for every sample size.  Under [the displayed assumptions and inputs](hyp:α,c_f,C_f,L,n), [the stated conclusion holds](goal). -/
-- @node: scoreRadius_nonneg
lemma scoreRadius_nonneg (α c_f C_f L : ℝ) (n : ℕ) :
    0 ≤ scoreRadius α c_f C_f L n := by
  unfold scoreRadius
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Identification turns simultaneous reduced-form error bounds into inclusion
of the true parameter in the exact interval, including the finite-size rule.  Under [the displayed assumptions and inputs](hyp:α,c_f,C_f,L,P,n,hf,hF,hL,hP,hY,hD), [the stated conclusion holds](goal). -/
-- @node: targetCACE_mem_scoreInterval_of_errors
lemma targetCACE_mem_scoreInterval_of_errors (α c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hf : 0 < c_f ∧ c_f < 1)
    (hF : 1 < C_f) (hL : 1 < L) (hP : ModelClass c_f C_f L P n)
    (ω : TwoSample n n)
    (hY : |cubicEstimator c_f C_f ω true - transportedForm P true| ≤
      scoreRadius α c_f C_f L n)
    (hD : |cubicEstimator c_f C_f ω false - firstStage P| ≤
      scoreRadius α c_f C_f L n) :
    targetCACE P ∈ scoreInterval α c_f C_f L ω := by
  classical
  have hid := transported_cace_identification c_f C_f L P n hf hF hL hP
  have hθ := hid.2.2.2.2.2.2
  have hratio := hid.2.2.2.2.2.1
  have hμ : firstStage P ≠ 0 := ne_of_gt hP.strength
  have hform : transportedForm P true = targetCACE P * firstStage P := by
    rw [hratio]
    exact (div_mul_cancel₀ _ hμ).symm
  have habsθ : |targetCACE P| ≤ 1 := abs_le.mpr hθ
  have hscore : |cubicEstimator c_f C_f ω true -
      targetCACE P * cubicEstimator c_f C_f ω false| ≤
      2 * scoreRadius α c_f C_f L n := by
    calc
      _ = |(cubicEstimator c_f C_f ω true - transportedForm P true) +
          targetCACE P * (firstStage P - cubicEstimator c_f C_f ω false)| := by
        rw [hform]
        congr 1
        ring
      _ ≤ |cubicEstimator c_f C_f ω true - transportedForm P true| +
          |targetCACE P * (firstStage P - cubicEstimator c_f C_f ω false)| :=
        abs_add_le _ _
      _ ≤ scoreRadius α c_f C_f L n + scoreRadius α c_f C_f L n := by
        apply add_le_add hY
        rw [abs_mul, abs_sub_comm]
        exact (mul_le_mul_of_nonneg_right habsθ (abs_nonneg _)).trans
          (by simpa using hD)
      _ = _ := by ring
  have hinv : targetCACE P ∈ scoreInversion α c_f C_f L ω := ⟨hθ, hscore⟩
  unfold scoreInterval
  split_ifs with hn hne
  · exact hθ
  · exact hinv
  · exact (hne ⟨targetCACE P, hinv⟩).elim

/-- Replacing an empty acceptance set by the singleton zero preserves its
restricted length exactly.  Under [the displayed assumptions and inputs](hyp:α,c_f,C_f,L,n,hn), [the stated conclusion holds](goal). -/
-- @node: restrictedLength_scoreInterval_eq_inversion
lemma restrictedLength_scoreInterval_eq_inversion (α c_f C_f L : ℝ)
    (n : ℕ) (hn : threshold ≤ n) (ω : TwoSample n n) :
    restrictedLength (scoreInterval α c_f C_f L ω) =
      restrictedLength (scoreInversion α c_f C_f L ω) := by
  classical
  unfold scoreInterval
  rw [if_neg (not_lt.mpr hn)]
  split_ifs with hne
  · rfl
  · have hempty := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hempty, restrictedLength, Causalean.Stat.restrictedSetVolume,
      parameterSpace]

/-- On the good first-stage event, the exact fallback interval obeys roadmap
equation (1), with the displayed constant eight. Under [the displayed assumptions and inputs](hyp:α,c_f,C_f,L,P,n,hn,hgood,hμ), [the stated conclusion holds](goal). -/
-- @node: restrictedLength_scoreInterval_le_on_good_slope
lemma restrictedLength_scoreInterval_le_on_good_slope (α c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hμ : 0 < firstStage P) (ω : TwoSample n n)
    (hgood : |cubicEstimator c_f C_f ω false - firstStage P| ≤ firstStage P / 2) :
    restrictedLength (scoreInterval α c_f C_f L ω) ≤
      min 2 (8 * scoreRadius α c_f C_f L n / firstStage P) := by
  have hslope : firstStage P / 2 ≤ |cubicEstimator c_f C_f ω false| := by
    have hrev := abs_sub_abs_le_abs_sub (firstStage P)
      (cubicEstimator c_f C_f ω false)
    rw [abs_of_pos hμ, abs_sub_comm] at hrev
    linarith
  have hpos : 0 < |cubicEstimator c_f C_f ω false| :=
    (half_pos hμ).trans_le hslope
  rw [restrictedLength_scoreInterval_eq_inversion α c_f C_f L n hn ω]
  have hlen := Causalean.Stat.affineInversionSet_restrictedVolume_le
    parameterSpace (by simp [parameterSpace, Real.volume_Icc])
    (cubicEstimator c_f C_f ω true) (cubicEstimator c_f C_f ω false)
    (2 * scoreRadius α c_f C_f L n) (abs_pos.mp hpos)
    (mul_nonneg (by norm_num) (scoreRadius_nonneg α c_f C_f L n))
  have hcap : (volume parameterSpace).toReal = 2 := by
    norm_num [parameterSpace, Real.volume_Icc]
  change Causalean.Stat.restrictedSetVolume parameterSpace
    (scoreInversion α c_f C_f L ω) ≤ _
  apply hlen.trans
  rw [hcap]
  apply min_le_min_left
  calc
    2 * (2 * scoreRadius α c_f C_f L n) /
        |cubicEstimator c_f C_f ω false| ≤
      2 * (2 * scoreRadius α c_f C_f L n) / (firstStage P / 2) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num)
            (mul_nonneg (by norm_num) (scoreRadius_nonneg α c_f C_f L n)))
          (half_pos hμ) hslope
    _ = _ := by field_simp; ring

/-- The two expectation bounds in the roadmap give its exact constant
`max 2 (8 c_r + 8 C_mse)` after separating the regimes at one.  Under [the displayed assumptions and inputs](hyp:ell,x,cr,C,hx,hC,hcap,hmean), [the stated conclusion holds](goal). -/
-- @node: upper_length_two_regime_bound
lemma upper_length_two_regime_bound (ell x cr C : ℝ)
    (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hcap : ell ≤ 2) (hmean : ell ≤ 8 * cr * x + 8 * C * x ^ 2) :
    ell ≤ max 2 (8 * cr + 8 * C) * min 1 x := by
  by_cases hsmall : x ≤ 1
  · rw [min_eq_right hsmall]
    calc
      ell ≤ (8 * cr + 8 * C) * x := by
        have hsq : x ^ 2 ≤ x := by nlinarith
        nlinarith
      _ ≤ max 2 (8 * cr + 8 * C) * x :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hx
  · rw [min_eq_left (le_of_lt (lt_of_not_ge hsmall)), mul_one]
    exact hcap.trans (le_max_left _ _)

/-- Each outcome of the prescribed affine inversion is a connected subset
of the parameter interval, including both fallback rules.  Under [the displayed assumptions and inputs](hyp:α,c_f,C_f,L,n), [the stated conclusion holds](goal). -/
-- @node: scoreInterval_subset_ordConnected
lemma scoreInterval_subset_ordConnected (α c_f C_f L : ℝ) (n : ℕ)
    (ω : TwoSample n n) :
    scoreInterval α c_f C_f L ω ⊆ parameterSpace ∧
      OrdConnected (scoreInterval α c_f C_f L ω) := by
  classical
  have hInv : scoreInversion α c_f C_f L ω ⊆ parameterSpace ∧
      OrdConnected (scoreInversion α c_f C_f L ω) := by
    refine ⟨fun _ ht => ht.1, ?_⟩
    rw [ordConnected_def]
    intro x hx y hy z hz
    refine ⟨⟨hx.1.1.trans hz.1, hz.2.trans hy.1.2⟩, ?_⟩
    have hx' := abs_le.mp hx.2
    have hy' := abs_le.mp hy.2
    apply abs_le.mpr
    by_cases hb : 0 ≤ cubicEstimator c_f C_f ω false
    · have hzx := mul_le_mul_of_nonneg_right hz.1 hb
      have hzy := mul_le_mul_of_nonneg_right hz.2 hb
      constructor <;> linarith
    · have hzx := mul_le_mul_of_nonpos_right hz.1 (le_of_not_ge hb)
      have hzy := mul_le_mul_of_nonpos_right hz.2 (le_of_not_ge hb)
      constructor <;> linarith
  unfold scoreInterval
  split_ifs
  · exact ⟨Subset.rfl, ordConnected_Icc⟩
  · exact hInv
  · refine ⟨?_, ordConnected_singleton⟩
    intro t ht
    simp only [mem_singleton_iff] at ht
    subst t
    norm_num [parameterSpace]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
