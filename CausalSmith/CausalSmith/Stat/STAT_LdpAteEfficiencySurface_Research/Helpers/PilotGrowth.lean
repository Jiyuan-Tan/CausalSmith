module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotMoments
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotPrefix

/-! # Uniform growth bounds for the pilot saddle score -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Under the supplied quantities and conditions, the pattern ray le exp assertion holds. Under [the stated assumptions](hyp:hε), [the pattern Ray le exp](goal).

Under the stated assumptions, the pattern Ray le exp. -/
lemma patternRay_le_exp (ε : ℝ) (hε : 0 ≤ ε) (s : Fin 14) (j : Fin 4) :
    patternRay ε s j ≤ Real.exp ε := by
  unfold patternRay privacyIncrement privacyRatio
  split_ifs <;> simp_all [Real.one_le_exp_iff]

/-- Under the supplied quantities and conditions, the pattern mass one le assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the pattern Mass one le](goal).

Under the stated assumptions, the pattern Mass one le. -/
lemma patternMass_one_le (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε)
    (s : Fin 14) :
    1 ≤ patternMass θ p ε s := by
  rw [← piTheta_sum_eq_one θ p]
  unfold patternMass
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_one (piTheta θ p j)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (patternRay_one_le_interior ε hε s j)
      (piTheta_pos_interior θ p hp hθ j).le

/-- Under the supplied quantities and conditions, the pattern mass le exp assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the pattern Mass le exp](goal).

Under the stated assumptions, the pattern Mass le exp. -/
lemma patternMass_le_exp (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε)
    (s : Fin 14) :
    patternMass θ p ε s ≤ Real.exp ε := by
  rw [← one_mul (Real.exp ε), ← piTheta_sum_eq_one θ p,
    Finset.sum_mul]
  unfold patternMass
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (patternRay_le_exp ε hε s j)
    (piTheta_pos_interior θ p hp hθ j).le

/-- the pilot reference weight is the mathematical object specified below. [The pilot Reference Weight](goal) is determined by [the displayed parameters](hyp:ε). -/
def pilotReferenceWeight (ε : ℝ) : StaircaseWeight := fun s =>
  if s ∈ ({0, 1, 3, 7} : Finset (Fin 14)) then
    1 / (Real.exp ε + 3) else 0

/-- [the pilot reference weight feasible assertion](goal) holds. -/
lemma pilotReferenceWeight_feasible (ε : ℝ) :
    staircaseFeasible ε (pilotReferenceWeight ε) := by
  exact staircaseFeasible_singleton_design ε

/-- For the supplied quantities and conditions, the pilot lower a is the mathematical object specified below. [The pilot Lower A](goal) is determined by [the displayed parameters](hyp:p,ε). -/
def pilotLowerA (p ε : ℝ) : ℝ :=
  (1 / (Real.exp ε + 3)) *
    (privacyIncrement ε * controlProb p) ^ 2 / Real.exp ε

/-- For the supplied quantities and conditions, the pilot lower b is the mathematical object specified below. [The pilot Lower B](goal) is determined by [the displayed parameters](hyp:p,ε). -/
def pilotLowerB (p ε : ℝ) : ℝ :=
  (1 / (Real.exp ε + 3)) *
    (privacyIncrement ε * p) ^ 2 / Real.exp ε

/-- Under the supplied quantities and conditions, the pilot lower a pos assertion holds. Under [the stated assumptions](hyp:hp,hε), [the pilot Lower A pos](goal).

Under the stated assumptions, the pilot Lower A pos. -/
lemma pilotLowerA_pos (p ε : ℝ) (hp : InteriorAssignment p) (hε : 0 < ε) :
    0 < pilotLowerA p ε := by
  have hq : 0 < controlProb p := by dsimp [controlProb]; linarith [hp.2]
  have hd := privacyIncrement_pos hε
  dsimp [pilotLowerA]
  positivity

/-- Under the supplied quantities and conditions, the pilot lower b pos assertion holds. Under [the stated assumptions](hyp:hp,hε), [the pilot Lower B pos](goal).

Under the stated assumptions, the pilot Lower B pos. -/
lemma pilotLowerB_pos (p ε : ℝ) (hp : InteriorAssignment p) (hε : 0 < ε) :
    0 < pilotLowerB p ε := by
  have hd := privacyIncrement_pos hε
  have hp0 := hp.1
  dsimp [pilotLowerB]
  positivity

/-- Under [the supplied quantities and conditions](hyp:p,t), [the seventh pattern information quadratic assertion](goal) holds. -/
lemma seventh_pattern_information_quadratic
    (θ : TrialParameter) (p ε t : ℝ) :
    patternInformation θ p ε 7 t =
      ((privacyIncrement ε * p) ^ 2 / patternMass θ p ε 7) * (t + 1) ^ 2 := by
  simp +decide [patternInformation, projectedGradient, patternGradient,
    direction, Fin.sum_univ_succ]
  ring

/-- Under the supplied quantities and conditions, the pilot reference objective lower assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the pilot Reference Objective lower](goal).

Under the stated assumptions, the pilot Reference Objective lower. -/
lemma pilotReferenceObjective_lower (θ : TrialParameter) (p ε t : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    pilotLowerA p ε * t ^ 2 + pilotLowerB p ε * (t + 1) ^ 2 ≤
      informationObjective θ p ε (pilotReferenceWeight ε) t := by
  have hm0pos := patternMass_pos_interior θ p ε hp hθ hε.le 0
  have hm7pos := patternMass_pos_interior θ p ε hp hθ hε.le 7
  have hm0le := patternMass_le_exp θ p ε hp hθ hε.le 0
  have hm7le := patternMass_le_exp θ p ε hp hθ hε.le 7
  have hterm0 : pilotLowerA p ε * t ^ 2 ≤
      pilotReferenceWeight ε 0 * patternInformation θ p ε 0 t := by
    rw [first_pattern_information_quadratic]
    simp only [pilotReferenceWeight, Finset.mem_insert, Finset.mem_singleton,
      true_or, if_true]
    dsimp [pilotLowerA]
    have hn : 0 ≤ (privacyIncrement ε * controlProb p) ^ 2 := sq_nonneg _
    have hd := (div_le_div_iff₀ (Real.exp_pos ε) hm0pos).2
      (mul_le_mul_of_nonneg_left hm0le hn)
    have hc : 0 ≤ 1 / (Real.exp ε + 3) := by positivity
    calc
      1 / (Real.exp ε + 3) * (privacyIncrement ε * controlProb p) ^ 2 /
          Real.exp ε * t ^ 2 =
          1 / (Real.exp ε + 3) *
            ((privacyIncrement ε * controlProb p) ^ 2 / Real.exp ε * t ^ 2) := by ring
      _ ≤ 1 / (Real.exp ε + 3) *
          ((privacyIncrement ε * controlProb p) ^ 2 /
            patternMass θ p ε 0 * t ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hd (sq_nonneg t)) hc
  have hterm7 : pilotLowerB p ε * (t + 1) ^ 2 ≤
      pilotReferenceWeight ε 7 * patternInformation θ p ε 7 t := by
    rw [seventh_pattern_information_quadratic]
    simp only [pilotReferenceWeight, Finset.mem_insert, Finset.mem_singleton,
      OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, or_false, true_or, if_true]
    dsimp [pilotLowerB]
    have hn : 0 ≤ (privacyIncrement ε * p) ^ 2 := sq_nonneg _
    have hd := (div_le_div_iff₀ (Real.exp_pos ε) hm7pos).2
      (mul_le_mul_of_nonneg_left hm7le hn)
    have hc : 0 ≤ 1 / (Real.exp ε + 3) := by positivity
    calc
      1 / (Real.exp ε + 3) * (privacyIncrement ε * p) ^ 2 /
          Real.exp ε * (t + 1) ^ 2 =
          1 / (Real.exp ε + 3) *
            ((privacyIncrement ε * p) ^ 2 / Real.exp ε * (t + 1) ^ 2) := by ring
      _ ≤ 1 / (Real.exp ε + 3) *
          ((privacyIncrement ε * p) ^ 2 /
            patternMass θ p ε 7 * (t + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hd (sq_nonneg (t + 1))) hc
  calc
    pilotLowerA p ε * t ^ 2 + pilotLowerB p ε * (t + 1) ^ 2 ≤
        pilotReferenceWeight ε 0 * patternInformation θ p ε 0 t +
          pilotReferenceWeight ε 7 * patternInformation θ p ε 7 t :=
      add_le_add hterm0 hterm7
    _ = ∑ s ∈ ({0, 7} : Finset (Fin 14)),
        pilotReferenceWeight ε s * patternInformation θ p ε s t := by
      simp
    _ ≤ informationObjective θ p ε (pilotReferenceWeight ε) t := by
      unfold informationObjective
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro s hs hnot
      exact mul_nonneg ((pilotReferenceWeight_feasible ε).1 s)
        (div_nonneg (sq_nonneg _)
          (patternMass_pos_interior θ p ε hp hθ hε.le s).le)

/-- For the supplied quantities and conditions, the pilot j lower is the mathematical object specified below. [The pilot JLower](goal) is determined by [the displayed parameters](hyp:p,ε). -/
def pilotJLower (p ε : ℝ) : ℝ :=
  pilotLowerA p ε * pilotLowerB p ε /
    (pilotLowerA p ε + pilotLowerB p ε)

/-- Under the supplied quantities and conditions, the pilot j lower pos assertion holds. Under [the stated assumptions](hyp:hp,hε), [the pilot JLower pos](goal).

Under the stated assumptions, the pilot JLower pos. -/
lemma pilotJLower_pos (p ε : ℝ) (hp : InteriorAssignment p) (hε : 0 < ε) :
    0 < pilotJLower p ε := by
  exact div_pos (mul_pos (pilotLowerA_pos p ε hp hε)
    (pilotLowerB_pos p ε hp hε))
    (add_pos (pilotLowerA_pos p ε hp hε) (pilotLowerB_pos p ε hp hε))

/-- Under the supplied quantities and conditions, the pilot j lower le quadratic assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hε), [the pilot JLower le quadratic](goal).

Under the stated assumptions, the pilot JLower le quadratic. -/
lemma pilotJLower_le_quadratic (p ε t : ℝ)
    (hp : InteriorAssignment p) (hε : 0 < ε) :
    pilotJLower p ε ≤
      pilotLowerA p ε * t ^ 2 + pilotLowerB p ε * (t + 1) ^ 2 := by
  let A := pilotLowerA p ε
  let B := pilotLowerB p ε
  have hA : 0 < A := pilotLowerA_pos p ε hp hε
  have hB : 0 < B := pilotLowerB_pos p ε hp hε
  have hsq : 0 ≤ (A * t + B * (t + 1)) ^ 2 := sq_nonneg _
  dsimp [pilotJLower, A, B]
  apply (div_le_iff₀ (add_pos hA hB)).2
  nlinarith

/-- Under the supplied quantities and conditions, the staircase weight le one assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hα), [the staircase Weight le one](goal).

Under the stated assumptions, the staircase Weight le one. -/
lemma staircaseWeight_le_one (ε : ℝ) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) (s : Fin 14) :
    α s ≤ 1 := by
  have hterm : α s * patternRay ε s 0 ≤
      ∑ u : Fin 14, α u * patternRay ε u 0 := by
    apply Finset.single_le_sum (s := Finset.univ) (a := s)
    · intro u hu
      exact mul_nonneg (hα.1 u)
        (le_trans (by norm_num) (patternRay_one_le_interior ε hε u 0))
    · exact Finset.mem_univ s
  calc
    α s = α s * 1 := by ring
    _ ≤ α s * patternRay ε s 0 :=
      mul_le_mul_of_nonneg_left (patternRay_one_le_interior ε hε s 0) (hα.1 s)
    _ ≤ _ := hterm
    _ = 1 := hα.2 0

/-- For the supplied quantities and conditions, the pilot objective zero upper is the mathematical object specified below. [The pilot Objective Zero Upper](goal) is determined by [the displayed parameters](hyp:p,ε). -/
def pilotObjectiveZeroUpper (p ε : ℝ) : ℝ :=
  ∑ s : Fin 14, projectedGradient p ε s 0 ^ 2

/-- Under the supplied quantities and conditions, the information objective zero le upper assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hα), [the information Objective zero le upper](goal).

Under the stated assumptions, the information Objective zero le upper. -/
lemma informationObjective_zero_le_upper (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) :
    informationObjective θ p ε α 0 ≤ pilotObjectiveZeroUpper p ε := by
  unfold informationObjective patternInformation pilotObjectiveZeroUpper
  apply Finset.sum_le_sum
  intro s hs
  have hm := patternMass_one_le θ p ε hp hθ hε s
  have ha := staircaseWeight_le_one ε hε α hα s
  have hdiv : projectedGradient p ε s 0 ^ 2 / patternMass θ p ε s ≤
      projectedGradient p ε s 0 ^ 2 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hm)).2
    nlinarith [sq_nonneg (projectedGradient p ε s 0)]
  calc
    α s * (projectedGradient p ε s 0 ^ 2 / patternMass θ p ε s) ≤
        1 * (projectedGradient p ε s 0 ^ 2 / patternMass θ p ε s) := by
      exact mul_le_mul_of_nonneg_right ha
        (div_nonneg (sq_nonneg _) (le_trans (by norm_num) hm))
    _ ≤ projectedGradient p ε s 0 ^ 2 := by simpa using hdiv

/-- Under the supplied quantities and conditions, the strong selector j bounds assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hθ), [the strong Selector J bounds](goal).

Under the stated assumptions, the strong Selector J bounds. -/
lemma strongSelector_J_bounds (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (θ : TrialParameter) (hθ : InteriorMeans θ) :
    pilotJLower p ε ≤ (select θ).2.2 ∧
      (select θ).2.2 ≤ pilotObjectiveZeroUpper p ε := by
  have hs := hselect.1.2 θ hθ
  have hmax := hselect.2 θ hθ
  have href := pilotReferenceObjective_lower θ p ε (select θ).2.1 hp hθ hε
  have hquad := pilotJLower_le_quadratic p ε (select θ).2.1 hp hε
  constructor
  · calc
      pilotJLower p ε ≤ pilotLowerA p ε * (select θ).2.1 ^ 2 +
          pilotLowerB p ε * ((select θ).2.1 + 1) ^ 2 := hquad
      _ ≤ informationObjective θ p ε (pilotReferenceWeight ε) (select θ).2.1 := href
      _ ≤ informationObjective θ p ε (select θ).1 (select θ).2.1 :=
        hmax (pilotReferenceWeight ε) (pilotReferenceWeight_feasible ε)
      _ = (select θ).2.2 := hs.2.2.2.symm
  · calc
      (select θ).2.2 =
          informationObjective θ p ε (select θ).1 (select θ).2.1 := hs.2.2.2
      _ ≤ informationObjective θ p ε (select θ).1 0 := hs.2.1 0
      _ ≤ pilotObjectiveZeroUpper p ε :=
        informationObjective_zero_le_upper θ p ε hp hθ hε.le _ hs.1

/-- For the supplied quantities and conditions, the pilot t upper is the mathematical object specified below. [The pilot TUpper](goal) is determined by [the displayed parameters](hyp:p,ε). -/
def pilotTUpper (p ε : ℝ) : ℝ :=
  Real.sqrt (pilotObjectiveZeroUpper p ε / pilotLowerA p ε)

/-- Under the supplied quantities and conditions, the strong selector t bound assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hθ), [the strong Selector t bound](goal).

Under the stated assumptions, the strong Selector t bound. -/
lemma strongSelector_t_bound (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (θ : TrialParameter) (hθ : InteriorMeans θ) :
    |(select θ).2.1| ≤ pilotTUpper p ε := by
  have hs := hselect.1.2 θ hθ
  have hmax := hselect.2 θ hθ
  have href := pilotReferenceObjective_lower θ p ε (select θ).2.1 hp hθ hε
  have hJupper := (strongSelector_J_bounds select hselect hp hε θ hθ).2
  have hAt : pilotLowerA p ε * (select θ).2.1 ^ 2 ≤
      pilotObjectiveZeroUpper p ε := by
    calc
      pilotLowerA p ε * (select θ).2.1 ^ 2 ≤
          pilotLowerA p ε * (select θ).2.1 ^ 2 +
            pilotLowerB p ε * ((select θ).2.1 + 1) ^ 2 := by
        exact le_add_of_nonneg_right (mul_nonneg
          (pilotLowerB_pos p ε hp hε).le (sq_nonneg _))
      _ ≤ informationObjective θ p ε (pilotReferenceWeight ε) (select θ).2.1 := href
      _ ≤ informationObjective θ p ε (select θ).1 (select θ).2.1 :=
        hmax (pilotReferenceWeight ε) (pilotReferenceWeight_feasible ε)
      _ = (select θ).2.2 := hs.2.2.2.symm
      _ ≤ pilotObjectiveZeroUpper p ε := hJupper
  have hratio : (select θ).2.1 ^ 2 ≤
      pilotObjectiveZeroUpper p ε / pilotLowerA p ε := by
    exact (le_div_iff₀ (pilotLowerA_pos p ε hp hε)).2 (by simpa [mul_comm] using hAt)
  rw [pilotTUpper, Real.le_sqrt (abs_nonneg _)
    (div_nonneg (by unfold pilotObjectiveZeroUpper; positivity)
      (pilotLowerA_pos p ε hp hε).le)]
  simpa [sq_abs] using hratio

/-- For the supplied quantities and conditions, the pilot score growth upper is the mathematical object specified below. [The pilot Score Growth Upper](goal) is determined by [the displayed parameters](hyp:p,ε). -/
def pilotScoreGrowthUpper (p ε : ℝ) : ℝ :=
  (1 + pilotTUpper p ε) / pilotJLower p ε

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the strong selector score growth bound assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hθ), [the strong Selector score Growth bound](goal).

Under the stated assumptions, the strong Selector score Growth bound. -/
lemma strongSelector_scoreGrowth_bound (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (θ : TrialParameter) (hθ : InteriorMeans θ) :
    (1 + |(select θ).2.1|) / (select θ).2.2 ≤
      pilotScoreGrowthUpper p ε := by
  have hJ := strongSelector_J_bounds select hselect hp hε θ hθ
  have ht := strongSelector_t_bound select hselect hp hε θ hθ
  have hT : 0 ≤ pilotTUpper p ε := by
    unfold pilotTUpper
    exact Real.sqrt_nonneg _
  apply div_le_div₀
  · exact add_nonneg (by norm_num) hT
  · linarith
  · exact pilotJLower_pos p ε hp hε
  · exact hJ.1

/-- For the supplied quantities and conditions, the pilot gradient upper is the mathematical object specified below. [The pilot Gradient Upper](goal) is determined by [the displayed parameters](hyp:p,ε). -/
def pilotGradientUpper (p ε : ℝ) : ℝ :=
  ∑ s : Fin 14,
    (|patternGradient p ε s 0| + |patternGradient p ε s 1|)

/-- Under [the supplied quantities and conditions](hyp:p), [the pilot gradient upper nonneg assertion](goal) holds. -/
lemma pilotGradientUpper_nonneg (p ε : ℝ) : 0 ≤ pilotGradientUpper p ε := by
  unfold pilotGradientUpper
  positivity

/-- Under [the supplied quantities and conditions](hyp:p,t,s), [the projected gradient abs le assertion](goal) holds. -/
lemma projectedGradient_abs_le (p ε t : ℝ) (s : Fin 14) :
    |projectedGradient p ε s t| ≤
      pilotGradientUpper p ε * (|t| + 1) := by
  have hlocal :
      |patternGradient p ε s 0| + |patternGradient p ε s 1| ≤
        pilotGradientUpper p ε := by
    unfold pilotGradientUpper
    apply Finset.single_le_sum (s := Finset.univ) (a := s)
    · intro u hu
      positivity
    · exact Finset.mem_univ s
  have ht1 : |t + 1| ≤ |t| + 1 := by
    calc
      |t + 1| ≤ |t| + |(1 : ℝ)| := abs_add_le _ _
      _ = |t| + 1 := by norm_num
  unfold projectedGradient
  simp only [Fin.sum_univ_two, direction, ↓reduceIte, Fin.isValue]
  calc
    |patternGradient p ε s 0 * t + patternGradient p ε s 1 * (t + 1)| ≤
        |patternGradient p ε s 0 * t| +
          |patternGradient p ε s 1 * (t + 1)| := abs_add_le _ _
    _ = |patternGradient p ε s 0| * |t| +
        |patternGradient p ε s 1| * |t + 1| := by rw [abs_mul, abs_mul]
    _ ≤ |patternGradient p ε s 0| * (|t| + 1) +
        |patternGradient p ε s 1| * (|t| + 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num)) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left ht1 (abs_nonneg _))
    _ = (|patternGradient p ε s 0| + |patternGradient p ε s 1|) *
        (|t| + 1) := by ring
    _ ≤ pilotGradientUpper p ε * (|t| + 1) := by
      exact mul_le_mul_of_nonneg_right hlocal (by positivity)

/-- For the supplied quantities and conditions, the pilot phi upper is the mathematical object specified below. [The pilot Phi Upper](goal) is determined by [the displayed parameters](hyp:p,ε). -/
def pilotPhiUpper (p ε : ℝ) : ℝ :=
  pilotGradientUpper p ε * (pilotTUpper p ε + 1) / pilotJLower p ε

/-- Under the supplied quantities and conditions, the strong selector phi tilde bound assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hθ), [the strong Selector phi Tilde bound](goal).

Under the stated assumptions, the strong Selector phi Tilde bound. -/
lemma strongSelector_phiTilde_bound (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (θ : TrialParameter) (hθ : InteriorMeans θ) (s : Fin 14) :
    |phiTilde θ p ε (select) s| ≤ pilotPhiUpper p ε := by
  have hJ := strongSelector_J_bounds select hselect hp hε θ hθ
  have ht := strongSelector_t_bound select hselect hp hε θ hθ
  have hT : 0 ≤ pilotTUpper p ε := by
    unfold pilotTUpper
    exact Real.sqrt_nonneg _
  have hm := patternMass_one_le θ p ε hp hθ hε.le s
  have hJpos : 0 < (select θ).2.2 :=
    lt_of_lt_of_le (pilotJLower_pos p ε hp hε) hJ.1
  have hden : pilotJLower p ε ≤
      (select θ).2.2 * patternMass θ p ε s := by
    calc
      pilotJLower p ε ≤ (select θ).2.2 := hJ.1
      _ = (select θ).2.2 * 1 := by ring
      _ ≤ (select θ).2.2 * patternMass θ p ε s :=
        mul_le_mul_of_nonneg_left hm hJpos.le
  rw [phiTilde, abs_div, abs_of_pos
    (mul_pos hJpos (lt_of_lt_of_le (by norm_num) hm))]
  apply div_le_div₀
  · exact mul_nonneg (pilotGradientUpper_nonneg p ε)
      (add_nonneg hT (by norm_num))
  · calc
      |projectedGradient p ε s (select θ).2.1| ≤
          pilotGradientUpper p ε * (|(select θ).2.1| + 1) :=
        projectedGradient_abs_le p ε _ s
      _ ≤ pilotGradientUpper p ε * (pilotTUpper p ε + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith)
          (pilotGradientUpper_nonneg p ε)
  · exact pilotJLower_pos p ε hp hε
  · exact hden

/-- Under the supplied quantities and conditions, the pilot phi upper nonneg assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hε), [the pilot Phi Upper nonneg](goal).

Under the stated assumptions, the pilot Phi Upper nonneg. -/
lemma pilotPhiUpper_nonneg (p ε : ℝ)
    (hp : InteriorAssignment p) (hε : 0 < ε) :
    0 ≤ pilotPhiUpper p ε := by
  unfold pilotPhiUpper
  exact div_nonneg
    (mul_nonneg (pilotGradientUpper_nonneg p ε)
      (add_nonneg (by unfold pilotTUpper; exact Real.sqrt_nonneg _) (by norm_num)))
    (pilotJLower_pos p ε hp hε).le

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the strong selector phi output bound assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hθ), [the strong Selector phi Output bound](goal).

Under the stated assumptions, the strong Selector phi Output bound. -/
lemma strongSelector_phiOutput_bound (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (θ : TrialParameter) (hθ : InteriorMeans θ) (z : PilotOutput) :
    |phiOutput θ p ε (select) z| ≤ pilotPhiUpper p ε := by
  cases z with
  | inl k =>
      simp [phiOutput, pilotPhiUpper_nonneg p ε hp hε]
  | inr s =>
      simpa [phiOutput] using
        strongSelector_phiTilde_bound select p ε hselect hp hε θ hθ s

end CausalSmith.Stat.LdpAteEfficiencySurface
