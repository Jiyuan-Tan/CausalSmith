module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotMoments
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotGrowth
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotLocalization

/-! # Finite adaptive main-release inputs -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open scoped BigOperators

/-- For the supplied quantities and conditions, the adaptive main mass is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Main Mass](goal) is determined by [the displayed parameters](hyp:select,θ,η,p,ε,s). -/
def adaptiveMainMass (θ η : TrialParameter) (p ε : ℝ)
    (s : Fin 14) : ℝ :=
  (select η).1 s * patternMass θ p ε s

/-- For the supplied quantities and conditions, the adaptive selected score is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Selected Score](goal) is determined by [the displayed parameters](hyp:select,η,p,ε,s). -/
def adaptiveSelectedScore (η : TrialParameter) (p ε : ℝ)
    (s : Fin 14) : ℝ :=
  phiTilde η p ε (select) s

/-- Under the supplied quantities and conditions, the adaptive main mass nonneg assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε), [the adaptive Main Mass nonneg](goal).

Under the stated assumptions, the adaptive Main Mass nonneg. -/
lemma adaptiveMainMass_nonneg (θ η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hη : InteriorMeans η)
    (hε : 0 < ε) (s : Fin 14) :
    0 ≤ adaptiveMainMass select θ η p ε s := by
  exact mul_nonneg (((hselect.1).2 η hη).1.1 s)
    (patternMass_pos_interior θ p ε hp hθ hε.le s).le

/-- Under the supplied quantities and conditions, the staircase weighted mass sum assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hα), [the staircase Weighted Mass sum](goal).

Under the stated assumptions, the staircase Weighted Mass sum. -/
lemma staircaseWeightedMass_sum (θ : TrialParameter) (p ε : ℝ)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) :
    ∑ s : Fin 14, α s * patternMass θ p ε s = 1 := by
  unfold patternMass
  simp_rw [Finset.mul_sum]
  calc
    (∑ s : Fin 14, ∑ j : Fin 4,
        α s * (piTheta θ p j * patternRay ε s j)) =
        ∑ j : Fin 4, piTheta θ p j *
          ∑ s : Fin 14, α s * patternRay ε s j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = ∑ j : Fin 4, piTheta θ p j * 1 := by
      apply Finset.sum_congr rfl
      intro j _
      have hj := hα.2 j
      unfold staircaseMatrix at hj
      rw [hj]
    _ = 1 := by simp [piTheta_sum_eq_one]

/-- Under the supplied quantities and conditions, the adaptive main mass sum assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hη,hε), [the adaptive Main Mass sum](goal).

Under the stated assumptions, the adaptive Main Mass sum. -/
lemma adaptiveMainMass_sum (θ η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hη : InteriorMeans η) (hε : 0 < ε) :
    ∑ s : Fin 14, adaptiveMainMass select θ η p ε s = 1 := by
  exact staircaseWeightedMass_sum θ p ε _
    (((hselect.1).2 η hη).1)

/-- Under the supplied quantities and conditions, the adaptive selected score mean assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hη,hε), [the adaptive Selected Score mean](goal).

Under the stated assumptions, the adaptive Selected Score mean. -/
lemma adaptiveSelectedScore_mean (θ η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hη : InteriorMeans η) (hε : 0 < ε) :
    ∑ s : Fin 14, adaptiveMainMass select θ η p ε s *
      adaptiveSelectedScore select η p ε s = contrast θ - contrast η := by
  exact phiTilde_mean_identity θ η p ε _ hp hη hε
    (hselect.1)

/-- Under the supplied quantities and conditions, the adaptive selected score second moment diag assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hη,hε), [the adaptive Selected Score second Moment diag](goal).

Under the stated assumptions, the adaptive Selected Score second Moment diag. -/
lemma adaptiveSelectedScore_secondMoment_diag (η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hη : InteriorMeans η) (hε : 0 < ε) :
    ∑ s : Fin 14, adaptiveMainMass select η η p ε s *
      (adaptiveSelectedScore select η p ε s) ^ 2 = Vstar η p ε := by
  exact phiTilde_secondMoment_identity η p ε _ hp hη hε
    (hselect.1)

/-- For the supplied quantities and conditions, the adaptive score variance is the mathematical object specified below. [The adaptive Score Variance](goal) is determined by [the displayed parameters](hyp:select,θ,η,p,ε). -/
def adaptiveScoreVariance (θ η : TrialParameter) (p ε : ℝ)
    : ℝ :=
  ∑ s : Fin 14, adaptiveMainMass select θ η p ε s *
      (adaptiveSelectedScore select η p ε s) ^ 2 -
    (contrast θ - contrast η) ^ 2

/-- For the supplied quantities and conditions, the adaptive score moment is the mathematical object specified below. [The adaptive Score Moment](goal) is determined by [the displayed parameters](hyp:select,r,θ,η,p,ε). -/
def adaptiveScoreMoment (r : ℝ) (θ η : TrialParameter) (p ε : ℝ)
    : ℝ :=
  ∑ s : Fin 14, adaptiveMainMass select θ η p ε s *
    |adaptiveSelectedScore select η p ε s| ^ r

/-- Under the supplied quantities and conditions, the adaptive score moment nonneg assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε), [the adaptive Score Moment nonneg](goal).

Under the stated assumptions, the adaptive Score Moment nonneg. -/
lemma adaptiveScoreMoment_nonneg (r : ℝ) (θ η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hη : InteriorMeans η)
    (hε : 0 < ε) : 0 ≤ adaptiveScoreMoment select r θ η p ε := by
  unfold adaptiveScoreMoment
  exact Finset.sum_nonneg fun s _ => mul_nonneg
    (adaptiveMainMass_nonneg select θ η p ε hselect hp hθ hη hε s)
    (Real.rpow_nonneg (abs_nonneg _) _)

/-- Under the supplied quantities and conditions, the adaptive score variance eq centered sum assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hη,hε), [the adaptive Score Variance eq centered sum](goal).

Under the stated assumptions, the adaptive Score Variance eq centered sum. -/
lemma adaptiveScoreVariance_eq_centered_sum (θ η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hη : InteriorMeans η) (hε : 0 < ε) :
    adaptiveScoreVariance select θ η p ε =
      ∑ s : Fin 14, adaptiveMainMass select θ η p ε s *
        (adaptiveSelectedScore select η p ε s -
          (contrast θ - contrast η)) ^ 2 := by
  rw [adaptiveScoreVariance]
  have hm := adaptiveSelectedScore_mean select θ η p ε hselect hp hη hε
  have hmass := adaptiveMainMass_sum select θ η p ε hselect hp hη hε
  have hpoint (s : Fin 14) :
      adaptiveMainMass select θ η p ε s *
          (adaptiveSelectedScore select η p ε s -
            (contrast θ - contrast η)) ^ 2 =
        adaptiveMainMass select θ η p ε s *
            (adaptiveSelectedScore select η p ε s) ^ 2 -
          2 * (contrast θ - contrast η) *
            (adaptiveMainMass select θ η p ε s *
              adaptiveSelectedScore select η p ε s) +
          (contrast θ - contrast η) ^ 2 *
            adaptiveMainMass select θ η p ε s := by
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hm, hmass]
  ring

/-- Under the supplied quantities and conditions, the adaptive score variance nonneg assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε), [the adaptive Score Variance nonneg](goal).

Under the stated assumptions, the adaptive Score Variance nonneg. -/
lemma adaptiveScoreVariance_nonneg (θ η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hη : InteriorMeans η)
    (hε : 0 < ε) : 0 ≤ adaptiveScoreVariance select θ η p ε := by
  rw [adaptiveScoreVariance_eq_centered_sum select θ η p ε hselect hp hη hε]
  exact Finset.sum_nonneg fun s _ => mul_nonneg
    (adaptiveMainMass_nonneg select θ η p ε hselect hp hθ hη hε s) (sq_nonneg _)

/-- Under the supplied quantities and conditions, the adaptive score variance diag assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hη,hε), [the adaptive Score Variance diag](goal).

Under the stated assumptions, the adaptive Score Variance diag. -/
lemma adaptiveScoreVariance_diag (η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hη : InteriorMeans η) (hε : 0 < ε) :
    adaptiveScoreVariance select η η p ε = Vstar η p ε := by
  rw [adaptiveScoreVariance, adaptiveSelectedScore_secondMoment_diag select η p ε hselect hp hη hε]
  simp

/-- Under the supplied quantities and conditions, the adaptive selected score abs le assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hη,hε), [the adaptive Selected Score abs le](goal).

Under the stated assumptions, the adaptive Selected Score abs le. -/
lemma adaptiveSelectedScore_abs_le (η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hη : InteriorMeans η) (hε : 0 < ε)
    (s : Fin 14) :
    |adaptiveSelectedScore select η p ε s| ≤ pilotPhiUpper p ε :=
  strongSelector_phiTilde_bound select p ε hselect hp hε η hη s

/-- Under the supplied quantities and conditions, the adaptive selected score second moment le assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε), [the adaptive Selected Score second Moment le](goal).

Under the stated assumptions, the adaptive Selected Score second Moment le. -/
lemma adaptiveSelectedScore_secondMoment_le (θ η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hη : InteriorMeans η)
    (hε : 0 < ε) :
    ∑ s : Fin 14, adaptiveMainMass select θ η p ε s *
        (adaptiveSelectedScore select η p ε s) ^ 2 ≤
      (pilotPhiUpper p ε) ^ 2 := by
  calc
    _ ≤ ∑ s : Fin 14, adaptiveMainMass select θ η p ε s *
        (pilotPhiUpper p ε) ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      have hab := adaptiveSelectedScore_abs_le select η p ε hselect hp hη hε s
      have hB : 0 ≤ pilotPhiUpper p ε := (abs_nonneg _).trans hab
      apply mul_le_mul_of_nonneg_left
      · simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 hab
      · exact adaptiveMainMass_nonneg select θ η p ε hselect hp hθ hη hε s
    _ = _ := by rw [← Finset.sum_mul, adaptiveMainMass_sum select θ η p ε hselect hp hη hε, one_mul]

/-- Under the supplied quantities and conditions, the adaptive selected score abs moment le assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε,hr), [the adaptive Selected Score abs Moment le](goal).

Under the stated assumptions, the adaptive Selected Score abs Moment le. -/
lemma adaptiveSelectedScore_absMoment_le (θ η : TrialParameter) (p ε r : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hη : InteriorMeans η)
    (hε : 0 < ε) (hr : 0 < r) :
    ∑ s : Fin 14, adaptiveMainMass select θ η p ε s *
        |adaptiveSelectedScore select η p ε s| ^ r ≤
      (pilotPhiUpper p ε) ^ r := by
  calc
    _ ≤ ∑ s : Fin 14, adaptiveMainMass select θ η p ε s *
        (pilotPhiUpper p ε) ^ r := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow (abs_nonneg _)
          (adaptiveSelectedScore_abs_le select η p ε hselect hp hη hε s) hr.le
      · exact adaptiveMainMass_nonneg select θ η p ε hselect hp hθ hη hε s
    _ = _ := by
      rw [← Finset.sum_mul, adaptiveMainMass_sum select θ η p ε hselect hp hη hε, one_mul]

/-- Under the supplied quantities and conditions, the adaptive score moment le assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε,hr), [the adaptive Score Moment le](goal).

Under the stated assumptions, the adaptive Score Moment le. -/
lemma adaptiveScoreMoment_le (θ η : TrialParameter) (p ε r : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hη : InteriorMeans η)
    (hε : 0 < ε) (hr : 0 < r) :
    adaptiveScoreMoment select r θ η p ε ≤ (pilotPhiUpper p ε) ^ r := by
  exact adaptiveSelectedScore_absMoment_le select θ η p ε r hselect hp hθ hη hε hr

/-- Under the supplied quantities and conditions, the adaptive score variance le assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε), [the adaptive Score Variance le](goal).

Under the stated assumptions, the adaptive Score Variance le. -/
lemma adaptiveScoreVariance_le (θ η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hη : InteriorMeans η)
    (hε : 0 < ε) :
    adaptiveScoreVariance select θ η p ε ≤ (pilotPhiUpper p ε) ^ 2 := by
  unfold adaptiveScoreVariance
  nlinarith [adaptiveSelectedScore_secondMoment_le select θ η p ε hselect hp hθ hη hε,
    sq_nonneg (contrast θ - contrast η)]

/-- Under the supplied quantities and conditions, the adaptive rare event integrand bounds assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hη,hε,hr), [the adaptive Rare Event Integrand bounds](goal).

Under the stated assumptions, the adaptive Rare Event Integrand bounds. -/
lemma adaptiveRareEventIntegrand_bounds (θ η : TrialParameter) (p ε r : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hη : InteriorMeans η)
    (hε : 0 < ε) (hr : 0 < r) :
    1 ≤ 1 + adaptiveScoreVariance select θ η p ε +
        adaptiveScoreMoment select r θ η p ε ∧
      1 + adaptiveScoreVariance select θ η p ε +
          adaptiveScoreMoment select r θ η p ε ≤
        1 + (pilotPhiUpper p ε) ^ 2 + (pilotPhiUpper p ε) ^ r := by
  constructor
  · nlinarith [adaptiveScoreVariance_nonneg select θ η p ε hselect hp hθ hη hε,
      adaptiveScoreMoment_nonneg select r θ η p ε hselect hp hθ hη hε]
  · linarith [adaptiveScoreVariance_le select θ η p ε hselect hp hθ hη hε,
      adaptiveScoreMoment_le select θ η p ε r hselect hp hθ hη hε hr]

end CausalSmith.Stat.LdpAteEfficiencySurface
