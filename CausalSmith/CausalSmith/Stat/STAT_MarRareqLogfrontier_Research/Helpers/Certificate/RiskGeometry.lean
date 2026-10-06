module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.IdealEstimator
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Identification

/-! Bounded-target and clipping geometry used by the risk certificate. -/

public section

open MeasureTheory ProbabilityTheory Set Finset

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma ate_mem_Icc_of_fullLaw {d : ℕ} (P : FullLaw d) :
    ate P ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ate_eq_potentialOutcomeMass]
  letI : IsProbabilityMeasure P.1 := P.2
  have h0 : (0 : ℝ) ≤ P.1.real {r | r.Y0 = true} := measureReal_nonneg
  have h1 : (0 : ℝ) ≤ P.1.real {r | r.Y1 = true} := measureReal_nonneg
  have h0' : P.1.real {r | r.Y0 = true} ≤ 1 := measureReal_le_one
  have h1' : P.1.real {r | r.Y1 = true} ≤ 1 := measureReal_le_one
  constructor <;> linarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma cellFunctional_mem_Icc {n d : ℕ} {q : ℝ} (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) :
    cellFunctional P ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [← unrestricted_cell_identification P hP]
  exact ate_mem_Icc_of_fullLaw P

/-- Given [the specified inputs and assumptions](hyp:u,theta,htheta), [the stated mathematical conclusion holds](goal). -/
lemma clip_sq_sub_le (u theta : ℝ) (htheta : theta ∈ Set.Icc (-1 : ℝ) 1) :
    (clip u - theta) ^ 2 ≤ (u - theta) ^ 2 := by
  rcases htheta with ⟨htheta0, htheta1⟩
  unfold clip
  by_cases hu0 : u < -1
  · have hmax : max (-1) (min 1 u) = -1 := by
      rw [max_eq_left]
      exact (min_le_right 1 u).trans (le_of_lt hu0)
    rw [hmax]
    nlinarith [sq_nonneg (u - theta), sq_nonneg (-1 - theta)]
  · have hu0' : -1 ≤ u := le_of_not_gt hu0
    by_cases hu1 : 1 < u
    · have hmax : max (-1) (min 1 u) = 1 := by
        rw [min_eq_left (le_of_lt hu1), max_eq_right]
        norm_num
      rw [hmax]
      nlinarith [sq_nonneg (u - theta), sq_nonneg (1 - theta)]
    · have hu1' : u ≤ 1 := le_of_not_gt hu1
      rw [min_eq_right hu1', max_eq_right hu0']

/-- Given [the specified inputs and assumptions](hyp:u,theta,hu,htheta), [the stated mathematical conclusion holds](goal). -/
lemma sq_sub_le_four_of_mem_Icc {u theta : ℝ}
    (hu : u ∈ Set.Icc (-1 : ℝ) 1)
    (htheta : theta ∈ Set.Icc (-1 : ℝ) 1) :
    (u - theta) ^ 2 ≤ 4 := by
  rcases hu with ⟨hu0, hu1⟩
  rcases htheta with ⟨htheta0, htheta1⟩
  nlinarith [sq_nonneg (u - theta + 2), sq_nonneg (2 - (u - theta))]

end CausalSmith.Stat.MarRareqLogfrontier
