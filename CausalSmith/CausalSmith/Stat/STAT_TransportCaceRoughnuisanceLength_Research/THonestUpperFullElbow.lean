module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.ScoreMeasurability
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.UpperGeometry
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.UpperProbability

/-! # Finite-sample honest affine interval and its upper length frontier

The proof follows the calibrated MSE tails, identification, good-slope length
bound, and minimax assembly. Graph measurability and square integrability of the
exact construction are derived by internal helper statements from the
construction and model membership.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @node: thm:honest-upper-full-elbow
/-- Given [the supplied inputs](hyp:α,c_f,C_f,L,hα,hf,hF,hL), [the stated result about honest upper full elbow holds](goal). -/
theorem honest_upper_full_elbow (α c_f C_f L : ℝ)
    (hα : 0 < α ∧ α < 1) (hf : 0 < c_f ∧ c_f < 1)
    (hF : 1 < C_f) (hL : 1 < L) :
    (∀ n : ℕ, 0 < n →
      scoreInterval α c_f C_f L ∈ HonestIntervals α c_f C_f L n) ∧
    ∃ C0 : ℝ, 0 < C0 ∧ -- @realizes C_0(positive upper constant)
      (∀ n : ℕ, threshold ≤ n →
        ∀ P : TransportLaw, ModelClass c_f C_f L P n →
          expectedLength P n n (scoreInterval α c_f C_f L) ≤
            C0 * min 1
              ((n : ℝ) ^ (-(1 / 3 : ℝ)) / firstStage P)) ∧
      (∀ n : ℕ, threshold ≤ n →
        ∀ a : ℝ, 0 < a → a ≤ 1 / 4 →
          lengthFrontier α c_f C_f L a n ≤
            C0 * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a)) := by
  classical
  have hgraph (n : ℕ) := scoreInterval_measurableSet_graph α c_f C_f L n hα hf hF hL
  have hsquare (n : ℕ) (P : TransportLaw) (hP : ModelClass c_f C_f L P n) (A : Bool) :=
    cubicEstimator_error_sq_integrable c_f C_f L P n hP A
  have hhonest (n : ℕ) : scoreInterval α c_f C_f L ∈
      HonestIntervals α c_f C_f L n := by
    refine ⟨hα.1, hα.2, scoreInterval_subset_ordConnected α c_f C_f L n,
      hgraph n, ?_⟩
    intro P hP
    exact scoreInterval_coverage_of_square_integrable α c_f C_f L P n
      hα hf hF hL hP (hsquare n P hP)
  let C0 := max 2 (8 * Real.sqrt (2 * mseEnvelope c_f C_f L / α) +
    8 * mseEnvelope c_f C_f L)
  have hC0 : 0 < C0 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlength (n : ℕ) (hn : threshold ≤ n) (P : TransportLaw)
      (hP : ModelClass c_f C_f L P n) :
      expectedLength P n n (scoreInterval α c_f C_f L) ≤
        C0 * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / firstStage P) :=
    scoreInterval_expectedLength_le_of_square_integrable α c_f C_f L P n
      hf hF hL hn hP (hsquare n P hP false)
  refine ⟨fun n _ => hhonest n, C0, hC0, hlength, ?_⟩
  intro n hn a ha ha1
  let Slice := {P : TransportLaw // P ∈ StrengthSlice c_f C_f L a n}
  have hbound0 : 0 ≤ C0 * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) := by
    apply mul_nonneg hC0.le
    exact le_min (by norm_num) (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) ha.le)
  have hpoint (P : Slice) : expectedLength P.1 n n
      (scoreInterval α c_f C_f L) ≤
        C0 * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) := by
    have hP := P.2.2.2.1
    apply (hlength n hn P.1 hP).trans
    apply mul_le_mul_of_nonneg_left _ hC0.le
    apply min_le_min_left
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      ha P.2.2.2.2.1
  have hsup : (⨆ P : Slice, expectedLength P.1 n n
      (scoreInterval α c_f C_f L)) ≤
        C0 * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) := by
    cases isEmpty_or_nonempty Slice with
    | inl he =>
      letI := he
      simpa using hbound0
    | inr he =>
      letI := he
      exact ciSup_le hpoint
  have hnonneg (C : {C // C ∈ HonestIntervals α c_f C_f L n}) :
      0 ≤ ⨆ P : Slice, expectedLength P.1 n n C.1 := by
    cases isEmpty_or_nonempty Slice with
    | inl he =>
      letI := he
      simp
    | inr he =>
      letI := he
      obtain ⟨P⟩ := he
      have hbdd : BddAbove (Set.range fun P : Slice => expectedLength P.1 n n C.1) := by
        refine ⟨2, ?_⟩
        rintro y ⟨Q, rfl⟩
        let := dataLaw_isProbabilityMeasure_of_model c_f C_f L Q.1 n Q.2.2.2.1
        exact expectedLength_le_two Q.1 n C.1
      exact (expectedLength_nonneg P.1 n C.1).trans (le_ciSup hbdd P)
  have hbdd : BddBelow (Set.range fun C : {C // C ∈ HonestIntervals α c_f C_f L n} =>
      ⨆ P : Slice, expectedLength P.1 n n C.1) := by
    refine ⟨0, ?_⟩
    rintro y ⟨C, rfl⟩
    exact hnonneg C
  exact (ciInf_le hbdd ⟨scoreInterval α c_f C_f L, hhonest n⟩).trans hsup

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
