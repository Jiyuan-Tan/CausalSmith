module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.R5Rigidity

/-! # Explicit centered five-ray certificate -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

/-- For [the supplied quantities and conditions](hyp:p), the [centered r5 scale](goal) is the mathematical object specified below. -/
def centeredR5Scale (p : ℝ) : ℝ :=
  Real.sqrt (8 * p ^ 2 / (5 * (1 + p)))

/-- For [the supplied quantities and conditions](hyp:p), the [centered r5 denom](goal) is the mathematical object specified below. -/
def centeredR5Denom (p : ℝ) : ℝ := 1 - 2 * p + centeredR5Scale p

/-- For [the supplied quantities and conditions](hyp:p), the [centered r5 direction](goal) is the mathematical object specified below. -/
def centeredR5Direction (p : ℝ) : ℝ :=
  (p - centeredR5Scale p) / centeredR5Denom p

/-- For [the supplied quantities and conditions](hyp:p), the [centered r5 mix](goal) is the mathematical object specified below. -/
def centeredR5Mix (p : ℝ) : ℝ := centeredR5Scale p / centeredR5Denom p

/-- For [the supplied quantities and conditions](hyp:p), the [centered r5 value](goal) is the mathematical object specified below. -/
def centeredR5Value (p : ℝ) : ℝ :=
  centeredR5Scale p ^ 2 * (1 - p) ^ 2 / centeredR5Denom p ^ 2

/-- For [the supplied quantities and conditions](hyp:p), the [centered r5 dual](goal) is the mathematical object specified below. -/
def centeredR5Dual (p : ℝ) : Fin 4 → ℝ := fun j =>
  if j.val < 2 then -centeredR5Value p / 4 else 3 * centeredR5Value p / 4

/-- For [the supplied quantities and conditions](hyp:p), the [centered r5 left score](goal) is the mathematical object specified below. -/
def centeredR5LeftScore (p : ℝ) : ℝ :=
  p - (1 - 2 * p) * centeredR5Direction p

/-- For [the supplied quantities and conditions](hyp:p), the [centered r5 right score](goal) is the mathematical object specified below. -/
def centeredR5RightScore (p : ℝ) : ℝ :=
  2 * p * (centeredR5Direction p + 1) / (1 + p)

/-- For [the supplied quantities and conditions](hyp:p,t,s), the [centered r5 information table](goal) is the mathematical object specified below. -/
def centeredR5InformationTable (p t : ℝ) (s : Fin 14) : ℝ :=
  match s.val with
  | 0 | 1 => 4 * (1 - p) ^ 2 * t ^ 2 / (2 - p)
  | 2 => 0
  | 3 | 7 => 4 * p ^ 2 * (t + 1) ^ 2 / (1 + p)
  | 4 | 9 => 2 * (p + t) ^ 2
  | 5 | 8 => 2 * (p - (1 - 2 * p) * t) ^ 2
  | 6 | 10 => 4 * p ^ 2 * (t + 1) ^ 2 / (3 - p)
  | 11 => 0
  | _ => 4 * (1 - p) ^ 2 * t ^ 2 / (2 + p)

/-- For [the supplied quantities and conditions](hyp:s), the [centered r5 dual coeff](goal) is the mathematical object specified below. -/
def centeredR5DualCoeff (s : Fin 14) : ℝ :=
  match s.val with
  | 0 | 1 => 1 / 2
  | 2 => 0
  | 3 | 7 => 5 / 2
  | 4 | 9 => 2
  | 5 | 8 => 2
  | 6 | 10 => 3 / 2
  | 11 => 4
  | _ => 7 / 2

/-- For [the supplied quantities and conditions](hyp:p), the [centered r5 weight](goal) is the mathematical object specified below. -/
def centeredR5Weight (p : ℝ) : StaircaseWeight := fun s =>
  if s = 5 ∨ s = 8 then centeredR5Mix p / 4
  else if s = 2 ∨ s = 3 ∨ s = 7 then (1 - centeredR5Mix p) / 5
  else 0

private lemma centered_piTheta_by_val (p : ℝ) (j : Fin 4) :
    piTheta (fun _ => (1 / 2 : ℝ)) p j =
      if j.val = 0 then controlProb p * (1 - (1 / 2 : ℝ))
      else if j.val = 1 then controlProb p * (1 / 2 : ℝ)
      else if j.val = 2 then p * (1 - (1 / 2 : ℝ))
      else p * (1 / 2 : ℝ) := by
  rcases j with ⟨j, hj⟩
  interval_cases j <;> rfl

/-- Under [the supplied quantities and conditions](hyp:p,j), [the centered pi theta assertion](goal) holds. -/
lemma centered_piTheta (p : ℝ) (j : Fin 4) :
    piTheta (fun _ => (1 / 2 : ℝ)) p j =
      if j.val < 2 then (1 - p) / 2 else p / 2 := by
  rw [centered_piTheta_by_val]
  rcases j with ⟨j, hj⟩
  interval_cases j <;> norm_num [controlProb] <;> ring

/-- Under [the supplied quantities and conditions](hyp:p,s), [the centered pattern mass assertion](goal) holds. -/
lemma centered_patternMass (p ε : ℝ) (s : Fin 14) :
    patternMass (fun _ => (1 / 2 : ℝ)) p ε s =
      ∑ j : Fin 4, (if j.val < 2 then (1 - p) / 2 else p / 2) *
        patternRay ε s j := by
  unfold patternMass
  simp_rw [centered_piTheta]

/-- Under [the supplied quantities and conditions](hyp:p,s), [the centered pattern mass inv assertion](goal) holds. -/
lemma centered_patternMass_inv (p ε : ℝ) (s : Fin 14) :
    patternMass (fun _ => (2 : ℝ)⁻¹) p ε s =
      ∑ j : Fin 4, (if j.val < 2 then (1 - p) / 2 else p / 2) *
        patternRay ε s j := by
  simpa only [one_div] using centered_patternMass p ε s

/-- Under [the supplied quantities and conditions](hyp:p,t,s), [the centered pattern information assertion](goal) holds. -/
lemma centered_patternInformation (p ε t : ℝ) (s : Fin 14) :
    patternInformation (fun _ => (2 : ℝ)⁻¹) p ε s t =
      projectedGradient p ε s t ^ 2 /
        (∑ j : Fin 4, (if j.val < 2 then (1 - p) / 2 else p / 2) *
          patternRay ε s j) := by
  rw [patternInformation, centered_patternMass_inv]

-- keep: reusable mechanism-geometry certificate or refinement API for neighboring extremal analyses
/-- Under [the supplied quantities and conditions](hyp:p,t,s), [the centered projected score assertion](goal) holds. -/
lemma centered_projectedScore (p ε t : ℝ) (s : Fin 14) :
    projectedScore (fun _ => (2 : ℝ)⁻¹) p ε s t =
      projectedGradient p ε s t /
        (∑ j : Fin 4, (if j.val < 2 then (1 - p) / 2 else p / 2) *
          patternRay ε s j) := by
  rw [projectedScore, centered_patternMass_inv]

set_option maxHeartbeats 800000 in
-- Expanding all fourteen centered pattern masses is a finite but sizable calculation.
/-- Under [the supplied quantities and conditions](hyp:p,t,s), [the centered r5 information table assertion](goal) holds. -/
lemma centeredR5_information_table (p t : ℝ) (s : Fin 14) :
    patternInformation (fun _ => (1 / 2 : ℝ)) p (Real.log 3) s t =
      centeredR5InformationTable p t s := by
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  simp only [one_div]
  rw [centered_patternInformation]
  rcases s with ⟨s, hs⟩
  interval_cases s <;>
    simp +decide [centeredR5InformationTable, projectedGradient,
      patternGradient, patternRay, patternContains, controlProb, direction,
      privacyIncrement, privacyRatio, he, Fin.sum_univ_succ] <;> try ring

/-- Under [the supplied quantities and conditions](hyp:p,s), [the centered r5 dual table assertion](goal) holds. -/
lemma centeredR5_dual_table (p : ℝ) (s : Fin 14) :
    dualRay (Real.log 3) (centeredR5Dual p) s =
      centeredR5DualCoeff s * centeredR5Value p := by
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  rcases s with ⟨s, hs⟩
  interval_cases s <;>
    simp +decide [centeredR5DualCoeff, dualRay, centeredR5Dual, patternRay,
      patternContains, privacyIncrement, privacyRatio, he,
      Fin.sum_univ_succ] <;> ring

/-- Under [the supplied quantities and conditions](hyp:p,hp0), [the centered r5 scale sq assertion](goal) holds. -/
lemma centeredR5Scale_sq (p : ℝ) (hp0 : 0 < p) :
    centeredR5Scale p ^ 2 = 8 * p ^ 2 / (5 * (1 + p)) := by
  unfold centeredR5Scale
  rw [Real.sq_sqrt]
  positivity

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 scale bounds assertion](goal) holds. -/
lemma centeredR5Scale_bounds (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    p < centeredR5Scale p ∧ centeredR5Scale p < 2 * p := by
  have hpden : 0 < 5 * (1 + p) := by positivity
  have hs0 : 0 ≤ centeredR5Scale p := Real.sqrt_nonneg _
  have hs2 := centeredR5Scale_sq p hp0
  field_simp [ne_of_gt hpden] at hs2
  constructor
  · nlinarith [sq_nonneg (centeredR5Scale p - p)]
  · nlinarith [sq_nonneg (2 * p - centeredR5Scale p)]

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 denom pos assertion](goal) holds. -/
lemma centeredR5Denom_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    0 < centeredR5Denom p := by
  have hs0 : 0 ≤ centeredR5Scale p := Real.sqrt_nonneg _
  unfold centeredR5Denom
  linarith

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 mix mem ioo assertion](goal) holds. -/
lemma centeredR5Mix_mem_Ioo (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    0 < centeredR5Mix p ∧ centeredR5Mix p < 1 := by
  have hd := centeredR5Denom_pos p hp0 hp1
  have hs := (centeredR5Scale_bounds p hp0 hp1).1
  unfold centeredR5Mix
  constructor
  · exact div_pos (hp0.trans hs) hd
  · rw [div_lt_one hd]
    unfold centeredR5Denom
    linarith

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 direction neg assertion](goal) holds. -/
lemma centeredR5Direction_neg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    centeredR5Direction p < 0 := by
  exact div_neg_of_neg_of_pos
    (sub_neg.mpr (centeredR5Scale_bounds p hp0 hp1).1)
    (centeredR5Denom_pos p hp0 hp1)

-- keep: reusable mechanism-geometry certificate or refinement API for neighboring extremal analyses
/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 left score pos assertion](goal) holds. -/
lemma centeredR5LeftScore_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    0 < centeredR5LeftScore p := by
  have ht := centeredR5Direction_neg p hp0 hp1
  unfold centeredR5LeftScore
  nlinarith

-- keep: reusable mechanism-geometry certificate or refinement API for neighboring extremal analyses
/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 right score pos assertion](goal) holds. -/
lemma centeredR5RightScore_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    0 < centeredR5RightScore p := by
  have hd := centeredR5Denom_pos p hp0 hp1
  have htp1 : 0 < centeredR5Direction p + 1 := by
    unfold centeredR5Direction centeredR5Denom
    have hd' : 1 - 2 * p + centeredR5Scale p ≠ 0 := by
      exact ne_of_gt hd
    have hd'' : 1 - p * 2 + centeredR5Scale p ≠ 0 := by
      intro h
      apply hd'
      nlinarith
    rw [show (p - centeredR5Scale p) /
          (1 - 2 * p + centeredR5Scale p) + 1 =
        (1 - p) / (1 - 2 * p + centeredR5Scale p) by
      field_simp [hd', hd'']
      ring]
    exact div_pos (by linarith) hd
  unfold centeredR5RightScore
  positivity

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 direction add one assertion](goal) holds. -/
lemma centeredR5Direction_add_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    centeredR5Direction p + 1 = (1 - p) / centeredR5Denom p := by
  have hd := ne_of_gt (centeredR5Denom_pos p hp0 hp1)
  unfold centeredR5Direction
  field_simp [hd]
  unfold centeredR5Denom
  ring

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 common score assertion](goal) holds. -/
lemma centeredR5_common_score (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    p - (1 - 2 * p) * centeredR5Direction p =
      centeredR5Scale p * (1 - p) / centeredR5Denom p := by
  have hd := ne_of_gt (centeredR5Denom_pos p hp0 hp1)
  unfold centeredR5Direction
  field_simp [hd]
  unfold centeredR5Denom
  ring

/-- Under [the supplied quantities and conditions](hyp:p,hp0), [the centered r5 value eq common score sq assertion](goal) holds. For [the displayed quantities and conditions](hyp:hp1), these specify the stated inputs. -/
lemma centeredR5Value_eq_common_score_sq (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) :
    centeredR5Value p =
      (p - (1 - 2 * p) * centeredR5Direction p) ^ 2 := by
  rw [centeredR5_common_score p hp0 hp1]
  unfold centeredR5Value
  ring

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 value pos assertion](goal) holds. -/
lemma centeredR5Value_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    0 < centeredR5Value p := by
  unfold centeredR5Value
  have hs : 0 < centeredR5Scale p :=
    hp0.trans (centeredR5Scale_bounds p hp0 hp1).1
  have hd := centeredR5Denom_pos p hp0 hp1
  exact div_pos (mul_pos (sq_pos_of_pos hs) (sq_pos_of_pos (by linarith)))
    (sq_pos_of_pos hd)

private lemma centeredR5_mask12_reduced (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) :
    8 * (p - centeredR5Scale p) ^ 2 <
      (2 - p) * centeredR5Scale p ^ 2 := by
  have hs2 := centeredR5Scale_sq p hp0
  have hsb := centeredR5Scale_bounds p hp0 hp1
  have hspos : 0 < centeredR5Scale p := hp0.trans hsb.1
  field_simp at hs2
  have hsSq : 5 * centeredR5Scale p ^ 2 < 8 * p ^ 2 := by
    nlinarith [mul_pos hp0 (sq_pos_of_pos hspos)]
  have hs43 : centeredR5Scale p < 4 * p / 3 := by
    nlinarith [sq_nonneg (centeredR5Scale p - 4 * p / 3)]
  nlinarith [sq_pos_of_pos hp0, sq_pos_of_pos (sub_pos.mpr hsb.1)]

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 slack mask12 assertion](goal) holds. -/
lemma centeredR5_slack_mask12 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    4 * (1 - p) ^ 2 * centeredR5Direction p ^ 2 / (2 - p) <
      centeredR5Value p / 2 := by
  have hd := centeredR5Denom_pos p hp0 hp1
  have hd' := ne_of_gt hd
  have hp2 : 0 < 2 - p := by linarith
  have hr := centeredR5_mask12_reduced p hp0 hp1
  have hq : 0 < (1 - p) ^ 2 := sq_pos_of_pos (by linarith)
  unfold centeredR5Direction centeredR5Value
  rw [div_lt_div_iff₀ hp2 (by positivity : (0 : ℝ) < 2)]
  field_simp [hd']
  nlinarith [mul_lt_mul_of_pos_left hr hq]

/-- Under [the supplied quantities and conditions](hyp:p,hp0), [the centered r5 slack mask5 10 assertion](goal) holds. For [the displayed quantities and conditions](hyp:hp1), these specify the stated inputs. -/
lemma centeredR5_slack_mask5_10 (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) :
    2 * (p + centeredR5Direction p) ^ 2 < 2 * centeredR5Value p := by
  have hd := centeredR5Denom_pos p hp0 hp1
  have hd' := ne_of_gt hd
  have hsb := centeredR5Scale_bounds p hp0 hp1
  have hq : 0 < 1 - p := by linarith
  have hpt : p + centeredR5Direction p =
      (1 - p) * (2 * p - centeredR5Scale p) / centeredR5Denom p := by
    unfold centeredR5Direction
    field_simp [hd']
    unfold centeredR5Denom
    ring
  have hl := centeredR5_common_score p hp0 hp1
  have hpt0 : 0 < p + centeredR5Direction p := by
    rw [hpt]
    exact div_pos (mul_pos hq (sub_pos.mpr hsb.2)) hd
  have hlt : p + centeredR5Direction p <
      p - (1 - 2 * p) * centeredR5Direction p := by
    rw [hpt, hl, div_lt_div_iff_of_pos_right hd]
    nlinarith [mul_pos hq (sub_pos.mpr hsb.1)]
  have hl0 : 0 < p - (1 - 2 * p) * centeredR5Direction p := by
    rw [hl]
    exact div_pos (mul_pos (hp0.trans hsb.1) hq) hd
  rw [centeredR5Value_eq_common_score_sq p hp0 hp1]
  nlinarith [mul_pos (add_pos hpt0 hl0) (sub_pos.mpr hlt)]

/-- Under [the supplied quantities and conditions](hyp:p,hp0), [the centered r5 slack mask7 11 assertion](goal) holds. For [the displayed quantities and conditions](hyp:hp1), these specify the stated inputs. -/
lemma centeredR5_slack_mask7_11 (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) :
    4 * p ^ 2 * (centeredR5Direction p + 1) ^ 2 / (3 - p) <
      (3 / 2 : ℝ) * centeredR5Value p := by
  have hp3 : 0 < 3 - p := by linarith
  have hd := centeredR5Denom_pos p hp0 hp1
  have hd' := ne_of_gt hd
  have hs2 := centeredR5Scale_sq p hp0
  rw [centeredR5Direction_add_one p hp0 hp1]
  unfold centeredR5Value
  rw [div_lt_iff₀ hp3]
  field_simp [hd']
  field_simp at hs2
  have hspos : 0 < centeredR5Scale p :=
    hp0.trans (centeredR5Scale_bounds p hp0 hp1).1
  have hc : 8 * p ^ 2 < 3 * centeredR5Scale p ^ 2 * (3 - p) := by
    nlinarith [sq_pos_of_pos hspos]
  have hq : 0 < (1 - p) ^ 2 := sq_pos_of_pos (by linarith)
  nlinarith [mul_lt_mul_of_pos_right hc hq]

/-- Under [the supplied quantities and conditions](hyp:p,hp0), [the centered r5 slack mask12 zero assertion](goal) holds. For [the displayed quantities and conditions](hyp:hp1), these specify the stated inputs. -/
lemma centeredR5_slack_mask12_zero (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) : (0 : ℝ) < 4 * centeredR5Value p := by
  exact mul_pos (by norm_num) (centeredR5Value_pos p hp0 hp1)

/-- Under [the supplied quantities and conditions](hyp:p,hp0), [the centered r5 slack mask13 14 assertion](goal) holds. For [the displayed quantities and conditions](hyp:hp1), these specify the stated inputs. -/
lemma centeredR5_slack_mask13_14 (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) :
    4 * (1 - p) ^ 2 * centeredR5Direction p ^ 2 / (2 + p) <
      (7 / 2 : ℝ) * centeredR5Value p := by
  have hd := centeredR5Denom_pos p hp0 hp1
  have hd' := ne_of_gt hd
  have hp2 : 0 < 2 + p := by linarith
  have hr := centeredR5_mask12_reduced p hp0 hp1
  have hq : 0 < (1 - p) ^ 2 := sq_pos_of_pos (by linarith)
  have hlarge : 8 * (p - centeredR5Scale p) ^ 2 <
      7 * (2 + p) * centeredR5Scale p ^ 2 := by
    have hspos : 0 < centeredR5Scale p :=
      hp0.trans (centeredR5Scale_bounds p hp0 hp1).1
    nlinarith [sq_pos_of_pos hspos]
  unfold centeredR5Direction centeredR5Value
  rw [div_lt_iff₀ hp2]
  field_simp [hd']
  nlinarith [mul_lt_mul_of_pos_left hlarge hq]

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 weight feasible assertion](goal) holds. -/
lemma centeredR5Weight_feasible (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    staircaseFeasible (Real.log 3) (centeredR5Weight p) := by
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  obtain ⟨hmix0, hmix1⟩ := centeredR5Mix_mem_Ioo p hp0 hp1
  constructor
  · intro s
    simp only [centeredR5Weight]
    split_ifs <;> positivity
  · intro j
    fin_cases j <;>
      simp +decide [staircaseMatrix, centeredR5Weight, patternRay,
        patternContains, privacyRatio, privacyIncrement, he,
        Fin.sum_univ_succ] <;> ring

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered r5 weight active assertion](goal) holds. -/
lemma centeredR5Weight_active (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    activeSupport (centeredR5Weight p) r5Active ∧
      ∀ s ∈ r5Active, 0 < centeredR5Weight p s := by
  obtain ⟨hm0, hm1⟩ := centeredR5Mix_mem_Ioo p hp0 hp1
  constructor
  · intro s
    rcases s with ⟨s, hs⟩
    interval_cases s <;> simp_all [centeredR5Weight, r5Active] <;> linarith
  · intro s hs
    rcases s with ⟨s, hslt⟩
    interval_cases s <;> simp_all [centeredR5Weight, r5Active] <;> positivity

/-- Under [the supplied quantities and conditions](hyp:p,hp0), [the centered r5 weight stationary assertion](goal) holds. For [the displayed quantities and conditions](hyp:hp1), these specify the stated inputs. -/
lemma centeredR5Weight_stationary (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) :
    (∑ s : Fin 14, centeredR5Weight p s *
      patternInformationSlope (fun _ => (1 / 2 : ℝ)) p (Real.log 3) s
        (centeredR5Direction p)) = 0 := by
  have he : Real.exp (Real.log (3 : ℝ)) = 3 :=
    Real.exp_log (by norm_num)
  have hd := centeredR5Denom_pos p hp0 hp1
  have hd' : 1 + centeredR5Scale p - p * 2 ≠ 0 := by
    intro hz
    unfold centeredR5Denom at hd
    nlinarith
  have hs2 := centeredR5Scale_sq p hp0
  unfold patternInformationSlope patternMass
  simp_rw [centered_piTheta]
  simp +decide [centeredR5Weight, centeredR5Direction, centeredR5Mix,
    centeredR5Denom, projectedGradient, patternGradient, patternRay,
    patternContains, controlProb, direction, privacyIncrement,
    privacyRatio, he, Fin.sum_univ_succ]
  ring_nf
  field_simp [hd']
  field_simp at hs2
  nlinarith

set_option maxHeartbeats 800000 in
-- The five active identities use the explicit centered information table.
/-- Under [the supplied quantities and conditions](hyp:p,hp0), [the centered r5 active dual equalities assertion](goal) holds. For [the displayed quantities and conditions](hyp:hp1), these specify the stated inputs. -/
lemma centeredR5_active_dual_equalities (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) :
    ∀ s ∈ r5Active,
      dualRay (Real.log 3) (centeredR5Dual p) s =
        patternInformation (fun _ => (1 / 2 : ℝ)) p (Real.log 3) s
          (centeredR5Direction p) := by
  intro s hs
  rw [centeredR5_dual_table, centeredR5_information_table]
  have hs2 := centeredR5Scale_sq p hp0
  have ht := centeredR5Direction_add_one p hp0 hp1
  have hv := centeredR5Value_eq_common_score_sq p hp0 hp1
  rcases s with ⟨s, hsl⟩
  interval_cases s <;>
    simp_all [r5Active, centeredR5DualCoeff, centeredR5InformationTable]
  all_goals
    have hp1' : p < 1 / 2 := by simpa only [one_div] using hp1
    rw [centeredR5_common_score p hp0 hp1']
    have hd := ne_of_gt (centeredR5Denom_pos p hp0 hp1')
    field_simp [hd]
    field_simp at hs2
    nlinarith

/-- Under [the supplied quantities and conditions](hyp:p,hp0), [the centered r5 inactive dual slacks assertion](goal) holds. For [the displayed quantities and conditions](hyp:hp1), these specify the stated inputs. -/
lemma centeredR5_inactive_dual_slacks (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) :
    ∀ s ∉ r5Active,
      patternInformation (fun _ => (1 / 2 : ℝ)) p (Real.log 3) s
          (centeredR5Direction p) <
        dualRay (Real.log 3) (centeredR5Dual p) s := by
  intro s hs
  rw [centeredR5_dual_table, centeredR5_information_table]
  have hA := centeredR5_slack_mask12 p hp0 hp1
  have hB := centeredR5_slack_mask5_10 p hp0 hp1
  have hC := centeredR5_slack_mask7_11 p hp0 hp1
  have hD := centeredR5_slack_mask12_zero p hp0 hp1
  have hE := centeredR5_slack_mask13_14 p hp0 hp1
  rcases s with ⟨s, hsl⟩
  interval_cases s <;>
    simp_all [r5Active, centeredR5DualCoeff, centeredR5InformationTable]
  all_goals
    convert hA using 1
    ring

set_option maxHeartbeats 800000 in
-- The explicit ten-pair finite score check requires repeated rational normalization.
/-- Under [the supplied quantities and conditions](hyp:p,hp0), [the centered r5 active scores pairwise ne assertion](goal) holds. For [the displayed quantities and conditions](hyp:hp1), these specify the stated inputs. -/
lemma centeredR5_active_scores_pairwise_ne (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) :
    ∀ s ∈ r5Active, ∀ u ∈ r5Active, s ≠ u →
      projectedScore (fun _ => (1 / 2 : ℝ)) p (Real.log 3) s
          (centeredR5Direction p) ≠
        projectedScore (fun _ => (1 / 2 : ℝ)) p (Real.log 3) u
          (centeredR5Direction p) := by
  intro s hs u hu hne
  wlog hlt : s.val < u.val generalizing s u
  · apply Ne.symm
    apply this u hu s hs (Ne.symm hne)
    omega
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  have hd := centeredR5Denom_pos p hp0 hp1
  have hd' : 1 + centeredR5Scale p - p * 2 ≠ 0 := by
    intro hz
    unfold centeredR5Denom at hd
    nlinarith
  have hd2 : 1 - p * 2 + centeredR5Scale p ≠ 0 := by
    intro hz
    apply hd'
    nlinarith
  have hsb := centeredR5Scale_bounds p hp0 hp1
  have hs2 := centeredR5Scale_sq p hp0
  rcases s with ⟨s, hslt⟩
  rcases u with ⟨u, hult⟩
  interval_cases s <;> interval_cases u <;> simp_all [r5Active]
  all_goals
    unfold projectedScore
    simp_rw [centered_patternMass_inv]
    simp +decide [centeredR5Direction, centeredR5Denom, projectedGradient,
      patternGradient, patternRay, patternContains, controlProb, direction,
      privacyIncrement, privacyRatio, he, Fin.sum_univ_succ]
    ring_nf
    field_simp [hd', hd2]
    ring_nf
    field_simp [hd', hd2]
    field_simp at hs2
    simp only [inv_eq_one_div] at *
    field_simp [hd', hd2] at *
    ring_nf at *
    nlinarith

/-- Under the supplied quantities and conditions, the centered r5 supported stationary eq assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp0,hp1,hβ,hout,hstat), [the centered R5 supported stationary eq](goal).

Under the stated assumptions, the centered R5 supported stationary eq. -/
lemma centeredR5_supported_stationary_eq (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2)
    (β : StaircaseWeight) (hβ : staircaseFeasible (Real.log 3) β)
    (hout : ∀ s ∉ r5Active, β s = 0)
    (hstat : ∑ s : Fin 14, β s *
      patternInformationSlope (fun _ => (1 / 2 : ℝ)) p (Real.log 3) s
        (centeredR5Direction p) = 0) :
    β = centeredR5Weight p := by
  obtain ⟨h23, h37, h58, hnorm⟩ :=
    r5_supported_feasible_coordinates (Real.log 3) (Real.log_pos (by norm_num)) β hβ hout
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  have hd := centeredR5Denom_pos p hp0 hp1
  have hd' : 1 + centeredR5Scale p - p * 2 ≠ 0 := by
    intro hz
    unfold centeredR5Denom at hd
    nlinarith
  have hd2 : 1 - p * 2 + centeredR5Scale p ≠ 0 := by
    intro hz
    apply hd'
    nlinarith
  have hs2 := centeredR5Scale_sq p hp0
  have hstat' := hstat
  rw [he] at hnorm
  unfold patternInformationSlope patternMass at hstat'
  simp_rw [centered_piTheta] at hstat'
  simp +decide [hout, r5Active, centeredR5Direction, centeredR5Denom,
    projectedGradient, patternGradient, patternRay, patternContains,
    controlProb, direction, privacyIncrement, privacyRatio, he,
    Fin.sum_univ_succ] at hstat'
  rw [← h37, ← h23, ← h58] at hstat'
  ring_nf at hstat'
  field_simp [hd', hd2] at hstat'
  ring_nf at hstat'
  field_simp at hs2
  let C := 10 * centeredR5Scale p * p ^ 2 +
    5 * centeredR5Scale p * p - 5 * centeredR5Scale p - 8 * p ^ 2
  have hfac : (-8 / 5 : ℝ) * (p - 1) * (C * β 5 + 2 * p ^ 2) = 0 := by
    rw [← hstat']
    dsimp [C]
    rw [show β 2 = (1 - 4 * β 5) / 5 by nlinarith [hnorm]]
    ring
  have hX : C * β 5 + 2 * p ^ 2 = 0 := by
    rcases mul_eq_zero.mp hfac with hleft | hX
    · rcases mul_eq_zero.mp hleft with hnum | hp
      · norm_num at hnum
      · linarith
    · exact hX
  have hCS : C * centeredR5Scale p =
      -8 * p ^ 2 * centeredR5Denom p := by
    dsimp [C, centeredR5Denom]
    nlinarith [hs2]
  have hspos : 0 < centeredR5Scale p :=
    hp0.trans (centeredR5Scale_bounds p hp0 hp1).1
  have hC : C ≠ 0 := by
    intro hC
    rw [hC, zero_mul] at hCS
    nlinarith [sq_pos_of_pos hp0]
  have htarget : 4 * centeredR5Denom p * β 5 = centeredR5Scale p := by
    apply (mul_left_cancel₀ hC)
    calc
      C * (4 * centeredR5Denom p * β 5) =
          4 * centeredR5Denom p * (C * β 5) := by ring
      _ = C * centeredR5Scale p := by rw [hCS]; nlinarith [hX]
  have hfive : β 5 = centeredR5Weight p 5 := by
    simp [centeredR5Weight, centeredR5Mix, centeredR5Denom]
    field_simp [hd', hd2]
    apply (eq_div_iff (by
      unfold centeredR5Denom at hd
      exact ne_of_gt hd)).2
    unfold centeredR5Denom at htarget
    nlinarith [htarget]
  exact r5_supported_feasible_eq_of_five_eq (Real.log 3)
    (Real.log_pos (by norm_num)) β (centeredR5Weight p) hβ
    (centeredR5Weight_feasible p hp0 hp1) hout
    (fun s hs => by
      by_contra hn
      exact hs (((centeredR5Weight_active p hp0 hp1).1 s).mp hn)) hfive

/-- Under [the supplied quantities and conditions](hyp:p,hp0,hp1), [the centered point mem r5 assertion](goal) holds. -/
lemma centeredPoint_mem_R5 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    (p, (1 / 2 : ℝ), (1 / 2 : ℝ), Real.log 3) ∈ R5 := by
  simp only [R5, certifiedRegion, Set.mem_ofPred_eq]
  refine ⟨hp0, by linarith, by norm_num, by norm_num, by norm_num,
    by norm_num, Real.log_pos (by norm_num), ?_⟩
  have hθ : (fun k : Fin 2 => if k = 0 then (1 / 2 : ℝ) else 1 / 2) =
      (fun _ => (1 / 2 : ℝ)) := by
    funext k
    split <;> rfl
  simp only [hθ]
  refine ⟨centeredR5Weight p, centeredR5Direction p, centeredR5Dual p,
    centeredR5Weight_feasible p hp0 hp1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (centeredR5Weight_active p hp0 hp1).1
  · exact (centeredR5Weight_active p hp0 hp1).2
  · simpa only [one_div] using centeredR5Weight_stationary p hp0 hp1
  · intro s hs
    simpa only [one_div] using centeredR5_active_dual_equalities p hp0 hp1 s hs
  · intro s hs
    simpa only [one_div] using centeredR5_inactive_dual_slacks p hp0 hp1 s hs
  · intro _ s hs u hu hne
    simpa only [one_div] using
      centeredR5_active_scores_pairwise_ne p hp0 hp1 s hs u hu hne

end CausalSmith.Stat.LdpAteEfficiencySurface
