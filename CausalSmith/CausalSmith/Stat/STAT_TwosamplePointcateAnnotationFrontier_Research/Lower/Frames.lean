module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Basic
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.ScaledHolder
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Projection
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Lower/Frames

Two-channel point-CATE annotation frontier: Lower/Frames
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
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


-- @env: S4
variable {d : ℕ} (h delta a b : ℝ)
/-- Given [the specified input theta](hyp:theta), [theta sign](goal) is the corresponding construction. -/
def thetaSign (theta : Bool) : ℝ := if theta then 1 else -1 -- @realizes theta(two hypotheses)
/-- Given [the specified input t](hyp:t), [flat exp](goal) is the corresponding construction. -/
def flatExp (t : ℝ) : ℝ := if 0 < t then Real.exp (-1/t) else 0
/-- Given [the specified input t](hyp:t), [frame angle](goal) is the corresponding construction. -/
def frameAngle (t : ℝ) : ℝ := (Real.pi/2) * Real.smoothTransition t
/-- Given [the specified input z](hyp:z), [the specified input t](hyp:t), [frame1d](goal) is the corresponding construction. -/
def frame1d (z : ℤ) (t : ℝ) : ℝ :=
  if (z:ℝ)-1 ≤ t ∧ t ≤ z then Real.sin (frameAngle (t-z+1))
  else if (z:ℝ) ≤ t ∧ t ≤ (z:ℝ)+1 then Real.cos (frameAngle (t-z)) else 0
/-- Given [the specified input h](hyp:h), [the specified input x](hyp:x), [macro bump](goal) is the corresponding construction. -/
def macroBump (h : ℝ) (x : Cov d) : ℝ :=
  ∏ i, flatExp (1-4*((x i-1/2)/h)^2)/flatExp 1
/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [grid radius](goal) is the corresponding construction. -/
def gridRadius (h delta : ℝ) : ℕ := Nat.ceil (|h/delta|/2)+2
/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [frame idx](goal) is the corresponding construction. -/
def frameIdx (d : ℕ) (h delta : ℝ) : Finset (Fin d → ℤ) :=
  (Finset.univ.image (fun z : Fin d → Fin (2*gridRadius h delta+1) =>
    fun i => (z i : ℤ) - (gridRadius h delta : ℤ))).filter
      (fun z => ∃ x ∈ locCube d h, ∀ i, |(x i-1/2)/delta - (z i:ℝ)| ≤ 1)
/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input z](hyp:z), [the specified input x](hyp:x), [frame](goal) is the corresponding construction. -/
def frame (h delta : ℝ) (z : Fin d → ℤ) (x : Cov d) : ℝ :=
  macroBump h x * ∏ i, frame1d (z i) ((x i-1/2)/delta)
/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [sign array](goal) is the corresponding construction. -/
abbrev SignArray (d : ℕ) (h delta : ℝ) := {z // z ∈ frameIdx d h delta} → Bool × Bool
/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input sigma](hyp:sigma), [the specified input control](hyp:control), [the specified input x](hyp:x), [sign field](goal) is the corresponding construction. -/
def signField (h delta : ℝ) (sigma : SignArray d h delta) (control : Bool) (x : Cov d) : ℝ :=
  ∑ z : {z // z ∈ frameIdx d h delta}, thetaSign (if control then (sigma z).2 else (sigma z).1) * frame h delta z.1 x
/-- [the measurable flat exp conclusion](goal) holds. -/
@[fun_prop] lemma measurable_flatExp : Measurable flatExp := by
  unfold flatExp
  apply Measurable.ite measurableSet_Ioi <;> fun_prop

/-- [the measurable frame angle conclusion](goal) holds. -/
@[fun_prop] lemma measurable_frameAngle : Measurable frameAngle := by
  unfold frameAngle
  fun_prop

/-- Given [the specified input z](hyp:z), [the measurable frame1d conclusion](goal) holds. -/
@[fun_prop] lemma measurable_frame1d (z : ℤ) : Measurable (frame1d z) := by
  unfold frame1d
  apply Measurable.ite measurableSet_Icc
  · fun_prop
  · apply Measurable.ite measurableSet_Icc <;> fun_prop

/-- Given [the specified input h](hyp:h), [the measurable macro bump conclusion](goal) holds. -/
@[fun_prop] lemma measurable_macroBump (h : ℝ) : Measurable (macroBump (d:=d) h) := by
  unfold macroBump
  fun_prop

/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input z](hyp:z), [the measurable frame conclusion](goal) holds. -/
@[fun_prop] lemma measurable_frame (h delta : ℝ) (z : Fin d → ℤ) :
    Measurable (frame h delta z) := by
  unfold frame
  fun_prop

/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input sigma](hyp:sigma), [the specified input control](hyp:control), [the measurable sign field conclusion](goal) holds. -/
@[fun_prop] lemma measurable_signField (h delta : ℝ) (sigma : SignArray d h delta) (control : Bool) :
    Measurable (signField h delta sigma control) := by
  unfold signField
  fun_prop
/-- The flat exponential is nonnegative, including on its zero branch.  Given [the specified input t](hyp:t), [the flat exp nonneg conclusion](goal) holds. -/
lemma flatExp_nonneg (t : ℝ) : 0 ≤ flatExp t := by
  unfold flatExp
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

/-- The normalizing value of the macro bump is strictly positive.  [the flat exp one pos conclusion](goal) holds. -/
lemma flatExp_one_pos : 0 < flatExp 1 := by
  simpa [flatExp] using Real.exp_pos (-1 : ℝ)

/-- Below one, the flat exponential is bounded by its normalizing value.  Given [the specified input t](hyp:t), [the specified input ht](hyp:ht), [the flat exp le one value conclusion](goal) holds. -/
lemma flatExp_le_one_value (t : ℝ) (ht : t ≤ 1) : flatExp t ≤ flatExp 1 := by
  by_cases hp : 0 < t
  · have hexp : -1 / t ≤ (-1 : ℝ) := (div_le_iff₀ hp).mpr (by linarith)
    simpa [flatExp, hp] using Real.exp_le_exp.mpr hexp
  · simpa [flatExp, hp] using flatExp_one_pos.le

/-- Every normalized coordinate factor lies in the unit interval.  Given [the specified input t](hyp:t), [the macro bump factor mem conclusion](goal) holds. -/
lemma macroBump_factor_mem (t : ℝ) :
    flatExp (1-4*t^2) / flatExp 1 ∈ Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (flatExp_nonneg _) flatExp_one_pos.le, ?_⟩
  apply (div_le_one flatExp_one_pos).mpr
  exact flatExp_le_one_value _ (by nlinarith [sq_nonneg t])

/-- The tensor macro bump has values between zero and one in every dimension.  Given [the specified input h](hyp:h), [the specified input x](hyp:x), [the macro bump mem conclusion](goal) holds. -/
lemma macroBump_mem (h : ℝ) (x : Cov d) : macroBump h x ∈ Icc (0 : ℝ) 1 := by
  unfold macroBump
  exact ⟨Finset.prod_nonneg (fun i _ => (macroBump_factor_mem _).1),
    Finset.prod_le_one (fun i _ => (macroBump_factor_mem _).1)
      (fun i _ => (macroBump_factor_mem _).2)⟩

/-- The macro bump is normalized to one at the interior target point.  Given [the specified input h](hyp:h), [the macro bump at x0 conclusion](goal) holds. -/
lemma macroBump_at_x0 (h : ℝ) : macroBump (d:=d) h (x0 d) = 1 := by
  simp [macroBump, x0, ne_of_gt flatExp_one_pos]

/-- A frame vanishes at and beyond the left end of its support.  Given [the specified input z](hyp:z), [the specified input t](hyp:t), [the specified input ht](hyp:ht), [the frame1d zero left conclusion](goal) holds. -/
lemma frame1d_zero_left (z : ℤ) (t : ℝ) (ht : t ≤ (z:ℝ)-1) :
    frame1d z t = 0 := by
  unfold frame1d
  split_ifs with h1 h2
  · rw [frameAngle, Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero,
      Real.sin_zero]
  · exfalso; linarith [h2.1]
  · rfl

/-- A frame vanishes at and beyond the right end of its support.  Given [the specified input z](hyp:z), [the specified input t](hyp:t), [the specified input ht](hyp:ht), [the frame1d zero right conclusion](goal) holds. -/
lemma frame1d_zero_right (z : ℤ) (t : ℝ) (ht : (z:ℝ)+1 ≤ t) :
    frame1d z t = 0 := by
  unfold frame1d
  split_ifs with h1 h2
  · exfalso; linarith [h1.2]
  · rw [frameAngle, Real.smoothTransition.one_of_one_le (by linarith), mul_one,
      Real.cos_pi_div_two]
  · rfl

/-- On one grid interval the two adjacent frames are the cosine and sine pair.  Given [the specified input j](hyp:j), [the specified input t](hyp:t), [the specified input hl](hyp:hl), [the specified input hu](hyp:hu), [the frame1d adjacent square conclusion](goal) holds. -/
lemma frame1d_adjacent_square (j : ℤ) (t : ℝ)
    (hl : (j:ℝ) ≤ t) (hu : t ≤ (j:ℝ)+1) :
    (frame1d j t)^2 + (frame1d (j+1) t)^2 = 1 := by
  have hj : frame1d j t = Real.cos (frameAngle (t-j)) := by
    unfold frame1d
    split_ifs with h1 h2
    · have he : t = (j:ℝ) := by linarith [h1.2]
      rw [he]
      norm_num [frameAngle, Real.smoothTransition.zero, Real.smoothTransition.one]
    · rfl
    · exact False.elim (h2 ⟨hl, hu⟩)
  have hj1 : frame1d (j+1) t = Real.sin (frameAngle (t-j)) := by
    unfold frame1d
    rw [if_pos (by push_cast; constructor <;> linarith)]
    congr 2
    push_cast
    ring
  rw [hj, hj1]
  exact Real.cos_sq_add_sin_sq _

/-- Only the two frames adjacent to the integer floor can contribute.  Given [the specified input t](hyp:t), [the specified input z](hyp:z), [the specified input hz](hyp:hz), [the frame1d zero of not adjacent conclusion](goal) holds. -/
lemma frame1d_zero_of_not_adjacent (t : ℝ) (z : ℤ)
    (hz : z ≠ ⌊t⌋ ∧ z ≠ ⌊t⌋+1) : frame1d z t = 0 := by
  have hl := Int.floor_le t
  have hu := Int.lt_floor_add_one t
  by_cases h : z < ⌊t⌋
  · apply frame1d_zero_right
    have hi : z+1 ≤ ⌊t⌋ := by omega
    have hir : (z:ℝ)+1 ≤ (⌊t⌋:ℝ) := by exact_mod_cast hi
    linarith
  · apply frame1d_zero_left
    have hi : ⌊t⌋+2 ≤ z := by omega
    have hir : (⌊t⌋:ℝ)+2 ≤ z := by exact_mod_cast hi
    linarith

/-- Each one-dimensional frame is bounded in absolute value by one.  Given [the specified input z](hyp:z), [the specified input t](hyp:t), [the abs frame1d le one conclusion](goal) holds. -/
lemma abs_frame1d_le_one (z : ℤ) (t : ℝ) : |frame1d z t| ≤ 1 := by
  unfold frame1d
  split_ifs
  · exact Real.abs_sin_le_one _
  · exact Real.abs_cos_le_one _
  · norm_num

/-- Tensor frames inherit the macro bump's unit bound.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input z](hyp:z), [the specified input x](hyp:x), [the abs frame le one conclusion](goal) holds. -/
lemma abs_frame_le_one (h delta : ℝ) (z : Fin d → ℤ) (x : Cov d) :
    |frame h delta z x| ≤ 1 := by
  rw [frame, abs_mul, Finset.abs_prod]
  have ht : (∏ i, |frame1d (z i) ((x i-1/2)/delta)|) ≤ 1 :=
    Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => abs_frame1d_le_one _ _)
  rw [abs_of_nonneg (macroBump_mem h x).1]
  exact (mul_le_mul_of_nonneg_left ht (macroBump_mem h x).1).trans
    (by simpa using (macroBump_mem h x).2)

/-- Only the two adjacent indices in each coordinate can support a tensor frame.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input z](hyp:z), [the specified input x](hyp:x), [the specified input hz](hyp:hz), [the frame zero of not coordinate adjacent conclusion](goal) holds. -/
lemma frame_zero_of_not_coordinate_adjacent (h delta : ℝ) (z : Fin d → ℤ) (x : Cov d)
    (hz : ¬ ∀ i, z i = ⌊(x i-1/2)/delta⌋ ∨ z i = ⌊(x i-1/2)/delta⌋+1) :
    frame h delta z x = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hz
  rw [frame, Finset.prod_eq_zero (Finset.mem_univ i)
    (frame1d_zero_of_not_adjacent _ _ (not_or.mp hi)), mul_zero]

/-- The signed tensor field is uniformly bounded by the number of adjacent tensor indices.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input sigma](hyp:sigma), [the specified input control](hyp:control), [the specified input x](hyp:x), [the abs sign field le conclusion](goal) holds. -/
lemma abs_signField_le (h delta : ℝ) (sigma : SignArray d h delta)
    (control : Bool) (x : Cov d) : |signField h delta sigma control x| ≤ (2:ℝ)^d := by
  classical
  let A : Finset (Fin d → ℤ) := Finset.univ.image (fun v : Fin d → Bool =>
    fun i => ⌊(x i-1/2)/delta⌋ + if v i then 1 else 0)
  have hzero (z : Fin d → ℤ) (hz : z ∉ A) : frame h delta z x = 0 := by
    apply frame_zero_of_not_coordinate_adjacent
    intro hadj
    apply hz
    apply Finset.mem_image.mpr
    refine ⟨fun i => decide (z i = ⌊(x i-1/2)/delta⌋+1), Finset.mem_univ _, ?_⟩
    funext i
    rcases hadj i with hi | hi <;> simp [hi]
  have hsum : (∑ z ∈ frameIdx d h delta, |frame h delta z x|) ≤ (A.card:ℝ) := by
    calc
      _ = ∑ z ∈ (frameIdx d h delta).filter (fun z => z ∈ A), |frame h delta z x| := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs with hz
        · rfl
        · simp [hzero z hz]
      _ ≤ ∑ z ∈ A, |frame h delta z x| :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun z hz => (Finset.mem_filter.mp hz).2) (fun z _ _ => abs_nonneg _)
      _ ≤ ∑ z ∈ A, (1:ℝ) := Finset.sum_le_sum (fun z _ => abs_frame_le_one _ _ _ _)
      _ = _ := by simp
  have hcard : A.card ≤ 2^d := by
    exact (Finset.card_image_le).trans (by simp)
  calc
    |signField h delta sigma control x| ≤
        ∑ z : {z // z ∈ frameIdx d h delta},
          |thetaSign (if control then (sigma z).2 else (sigma z).1) * frame h delta z.1 x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z ∈ frameIdx d h delta, |frame h delta z x| := by
      simp only [abs_mul, show ∀ theta, |thetaSign theta| = 1 from
        fun theta => by cases theta <;> norm_num [thetaSign], one_mul]
      exact Finset.sum_coe_sort (frameIdx d h delta) (fun z => |frame h delta z x|)
    _ ≤ (A.card:ℝ) := hsum
    _ ≤ (2:ℝ)^d := by exact_mod_cast hcard

/-- Any finite index set containing the adjacent pair has squared-frame sum one.  Given [the specified input s](hyp:s), [the specified input t](hyp:t), [the specified input h0](hyp:h0), [the specified input h1](hyp:h1), [the frame1d square sum conclusion](goal) holds. -/
lemma frame1d_square_sum (s : Finset ℤ) (t : ℝ)
    (h0 : ⌊t⌋ ∈ s) (h1 : ⌊t⌋+1 ∈ s) :
    (∑ z ∈ s, (frame1d z t)^2) = 1 := by
  classical
  have hsub : {⌊t⌋, ⌊t⌋+1} ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact h0
    · exact h1
  have he := Finset.sum_subset hsub (f := fun z => (frame1d z t)^2) (by
    intro z _ hz
    have hn : z ≠ ⌊t⌋ ∧ z ≠ ⌊t⌋+1 := by simpa using hz
    rw [frame1d_zero_of_not_adjacent t z hn, zero_pow (by decide : 2 ≠ 0)])
  rw [← he]
  rw [Finset.sum_pair (by omega : ⌊t⌋ ≠ ⌊t⌋+1)]
  exact frame1d_adjacent_square _ _ (Int.floor_le t) (Int.lt_floor_add_one t).le

/-- The finite grid contains both adjacent frames whenever the argument is in its interior.  Given [the specified input R](hyp:R), [the specified input t](hyp:t), [the specified input hl](hyp:hl), [the specified input hu](hyp:hu), [the frame1d grid square sum conclusion](goal) holds. -/
lemma frame1d_grid_square_sum (R : ℕ) (t : ℝ)
    (hl : -(R:ℝ)+1 ≤ t) (hu : t ≤ (R:ℝ)-1) :
    (∑ z : Fin (2*R+1), (frame1d ((z:ℤ)-(R:ℤ)) t)^2) = 1 := by
  let s : Finset ℤ := Finset.univ.image (fun z : Fin (2*R+1) => (z:ℤ)-(R:ℤ))
  have hmem (j : ℤ) (hjl : -(R:ℤ) ≤ j) (hju : j ≤ (R:ℤ)) : j ∈ s := by
    have hj0 : 0 ≤ j+(R:ℤ) := by omega
    have hjM : j+(R:ℤ) < (2*R+1:ℕ) := by omega
    let z : Fin (2*R+1) := ⟨(j+(R:ℤ)).toNat, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_univ _, ?_⟩
    dsimp [z]
    rw [Int.toNat_of_nonneg hj0]
    omega
  have hfloor : -(R:ℤ) ≤ ⌊t⌋ ∧ ⌊t⌋+1 ≤ (R:ℤ) := by
    have hf := Int.floor_le t
    have hf' := Int.lt_floor_add_one t
    constructor
    · have hr : -(R:ℝ) < (⌊t⌋:ℝ)+1 := by linarith
      have hi : -(R:ℤ) < ⌊t⌋+1 := by exact_mod_cast hr
      omega
    · have hr : (⌊t⌋:ℝ)+1 ≤ (R:ℝ) := by linarith
      exact_mod_cast hr
  have he := frame1d_square_sum s t
    (hmem _ hfloor.1 (by omega)) (hmem _ (by omega) hfloor.2)
  rw [Finset.sum_image] at he
  · exact he
  · intro z _ w _ hzw
    apply Fin.ext
    have hv : (z:ℤ) = (w:ℤ) := by
      change (z:ℤ)-(R:ℤ) = (w:ℤ)-(R:ℤ) at hzw
      omega
    exact_mod_cast hv

/-- Outside its localization cube the macro bump is identically zero.  Given [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the macro bump zero outside conclusion](goal) holds. -/
lemma macroBump_zero_outside (h : ℝ) (hh : 0 < h) (x : Cov d)
    (hx : x ∉ locCube d h) : macroBump h x = 0 := by
  have hex : ∃ i, ¬ (1/2-h/2 ≤ x i ∧ x i ≤ 1/2+h/2) := by
    simpa only [locCube, mem_ofPred_eq, mem_Icc, not_forall] using hx
  obtain ⟨i, hi⟩ := hex
  have ht : 1-4*((x i-1/2)/h)^2 ≤ 0 := by
    have hcases : x i < 1/2-h/2 ∨ 1/2+h/2 < x i := by
      by_cases hl : 1/2-h/2 ≤ x i
      · exact Or.inr (lt_of_not_ge (fun hu => hi ⟨hl, hu⟩))
      · exact Or.inl (lt_of_not_ge hl)
    rcases hcases with hi | hi
    · have hb : (x i-1/2)/h < -1/2 := (div_lt_iff₀ hh).mpr (by linarith)
      nlinarith [sq_nonneg ((x i-1/2)/h+1/2)]
    · have hb : 1/2 < (x i-1/2)/h := (lt_div_iff₀ hh).mpr (by linarith)
      nlinarith [sq_nonneg ((x i-1/2)/h-1/2)]
  unfold macroBump
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [flatExp, if_neg (not_lt.mpr ht), zero_div]

/-- An index failing the geometric support filter has a zero tensor frame at a cube point.  Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the specified input z](hyp:z), [the specified input hz](hyp:hz), [the frame tensor zero of filter conclusion](goal) holds. -/
lemma frame_tensor_zero_of_filter (h delta : ℝ) (x : Cov d) (hx : x ∈ locCube d h)
    (z : Fin d → ℤ)
    (hz : ¬ ∃ y ∈ locCube d h, ∀ i, |(y i-1/2)/delta-(z i:ℝ)| ≤ 1) :
    (∏ i, frame1d (z i) ((x i-1/2)/delta)) = 0 := by
  have hex : ∃ i, ¬ |(x i-1/2)/delta-(z i:ℝ)| ≤ 1 := by
    by_contra hn
    apply hz
    refine ⟨x, hx, ?_⟩
    simpa using hn
  obtain ⟨i, hi⟩ := hex
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hc : (x i-1/2)/delta-(z i:ℝ) < -1 ∨
      1 < (x i-1/2)/delta-(z i:ℝ) := by
    simpa only [abs_le, not_and_or, not_le] using hi
  rcases hc with hc | hc
  · exact frame1d_zero_left _ _ (by linarith)
  · exact frame1d_zero_right _ _ (by linarith)

/-- Given [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hd](hyp:hd), [the specified input hdh](hyp:hdh), [the specified input x](hyp:x), [the frame square partition conclusion](goal) holds. -/
lemma frame_square_partition (h delta : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (hd : 0 < delta) (hdh : delta ≤ h) (x : Cov d) :
    (∑ z : {z // z ∈ frameIdx d h delta}, (frame h delta z.1 x)^2) = (macroBump h x)^2 := by
  classical
  by_cases hx : x ∈ locCube d h
  · let R := gridRadius h delta
    let G : Finset (Fin d → ℤ) := Finset.univ.image
      (fun z : Fin d → Fin (2*R+1) => fun i => (z i:ℤ)-(R:ℤ))
    let f : (Fin d → ℤ) → ℝ := fun z => (∏ i, frame1d (z i) ((x i-1/2)/delta))^2
    have harg (i : Fin d) : -(R:ℝ)+1 ≤ (x i-1/2)/delta ∧
        (x i-1/2)/delta ≤ (R:ℝ)-1 := by
      have hc := hx i
      have habs : |h/delta| = h/delta := abs_of_pos (div_pos hh hd)
      have hr : h/delta/2 ≤ (Nat.ceil (|h/delta|/2):ℝ) := by
        simpa only [habs] using Nat.le_ceil (|h/delta|/2)
      have hR : h/delta/2+2 ≤ (R:ℝ) := by
        dsimp [R, gridRadius]
        push_cast
        linarith
      constructor
      · apply (le_div_iff₀ hd).mpr
        have hb : -h/2 ≤ x i-1/2 := by linarith [hc.1]
        have hr' := (div_le_iff₀ hd).mp (show h/2/delta ≤ (R:ℝ)-1 by
          convert (show h/delta/2 ≤ (R:ℝ)-1 by linarith) using 1; ring)
        nlinarith
      · apply (div_le_iff₀ hd).mpr
        have hb : x i-1/2 ≤ h/2 := by linarith [hc.2]
        have hr' := (div_le_iff₀ hd).mp (show h/2/delta ≤ (R:ℝ)-1 by
          convert (show h/delta/2 ≤ (R:ℝ)-1 by linarith) using 1; ring)
        linarith
    have hfull : (∑ z ∈ G, f z) = 1 := by
      rw [Finset.sum_image]
      · dsimp only [f]
        simp_rw [← Finset.prod_pow]
        rw [← Fintype.prod_sum (fun (i : Fin d) (j : Fin (2*R+1)) =>
          (frame1d ((j:ℤ)-(R:ℤ)) ((x i-1/2)/delta))^2)]
        simp only [frame1d_grid_square_sum R _ (harg _).1 (harg _).2,
          Finset.prod_const_one]
      · intro z _ w _ he
        funext i
        have hi := congrFun he i
        change (z i:ℤ)-(R:ℤ) = (w i:ℤ)-(R:ℤ) at hi
        apply Fin.ext
        have hv : (z i:ℤ) = (w i:ℤ) := by omega
        exact_mod_cast hv
    have hfiltered : (∑ z ∈ frameIdx d h delta, f z) = 1 := by
      change (∑ z ∈ G.filter
        (fun z => ∃ y ∈ locCube d h, ∀ i, |(y i-1/2)/delta-(z i:ℝ)| ≤ 1), f z) = 1
      rw [Finset.sum_filter]
      convert hfull using 1
      apply Finset.sum_congr rfl
      intro z hz
      split_ifs with hsupport
      · rfl
      · dsimp only [f]
        rw [frame_tensor_zero_of_filter h delta x hx z hsupport, zero_pow (by decide : 2 ≠ 0)]
    rw [show (∑ z : {z // z ∈ frameIdx d h delta}, (frame h delta z.1 x)^2) =
      (macroBump h x)^2 * (∑ z ∈ frameIdx d h delta, f z) by
        simp only [frame, mul_pow]
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_coe_sort (frameIdx d h delta) f]
    rw [hfiltered, mul_one]
  · simp only [frame, macroBump_zero_outside h hh x hx, zero_mul, zero_pow
      (by decide : 2 ≠ 0), Finset.sum_const_zero]

/-- The prescribed flat exponential is Mathlib's smooth glue function.  [the flat exp eq glue conclusion](goal) holds. -/
lemma flatExp_eq_glue : flatExp = expNegInvGlue := by
  funext t
  unfold flatExp expNegInvGlue
  by_cases ht : 0 < t
  · simp [ht, not_le.mpr ht, div_eq_mul_inv]
  · simp [ht, le_of_not_gt ht]

/-- For [bandwidth h](hyp:h), [the fixed macro bump is globally smooth, including its support boundary](goal). -/
@[fun_prop] lemma macroBump_contDiff (h : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (macroBump (d:=d) h) := by
  unfold macroBump
  apply contDiff_prod
  intro i _
  rw [flatExp_eq_glue]
  have hcoord : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Cov d => x i) :=
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).contDiff
  exact (expNegInvGlue.contDiff.comp (by fun_prop)).div_const _

/-- The fixed macro bump has compact support.  Given [the specified input d](hyp:d), [the macro bump compact support conclusion](goal) holds. -/
lemma macroBump_compactSupport (d : ℕ) : HasCompactSupport (macroBump (d:=d) 1) := by
  have hcompact : IsCompact (locCube d 1) := by
    have heq : locCube d 1 = ((PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
        Set.pi Set.univ (fun _ => Icc (1/2-1/2 : ℝ) (1/2+1/2))) := by
      ext x
      simp only [locCube, mem_setOf_eq, mem_preimage, mem_pi, mem_univ, forall_const]
      rfl
    rw [heq]
    exact (Homeomorph.isCompact_preimage _).2 (isCompact_univ_pi fun _ => isCompact_Icc)
  exact HasCompactSupport.intro hcompact (fun x hx => macroBump_zero_outside 1 (by norm_num) x hx)

/-- Dilation of the fixed centered macro profile is exactly the prescribed bump.  Given [the specified input h](hyp:h), [the specified input x](hyp:x), [the macro bump dilation conclusion](goal) holds. -/
lemma macroBump_dilation (h : ℝ) (x : Cov d) :
    macroBump 1 (h⁻¹ • (x-x0 d) + x0 d) = macroBump h x := by
  unfold macroBump
  apply Finset.prod_congr rfl
  intro i _
  congr 3
  simp [x0, div_eq_mul_inv, mul_comm]

/-- Given [the specified input d](hyp:d), [the specified input s](hyp:s), [the specified input hs](hyp:hs), [the specified input hs'](hyp:hs'), [the macro square holder conclusion](goal) holds. -/
lemma macro_square_holder (d : ℕ) (s : ℝ) (hs : 0 < s) (hs' : s ≤ 3) : -- @realizes s(Holder-order public domain)
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive claim-local constant)
       ∀ h, 0 < h → h ≤ 1/2 →
      holderNorm (fun x : Cov d => (macroBump h x)^2) s ≤ ENNReal.ofReal (C*h^(-s)) := by
  let f : Cov d → ℝ := fun z => (macroBump 1 (z+x0 d))^2
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    dsimp [f]
    fun_prop
  have hsupp : HasCompactSupport f := by
    have hc := (macroBump_compactSupport d).comp_homeomorph (Homeomorph.addRight (x0 d))
    change HasCompactSupport (fun z => macroBump 1 (z+x0 d)) at hc
    change HasCompactSupport (fun z => (macroBump 1 (z+x0 d))^2)
    apply HasCompactSupport.intro hc
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_pow (by decide : 2 ≠ 0)]
  obtain ⟨C, hC, hbound⟩ := compact_profile_scaled_holder f hf hsupp s hs
  refine ⟨C, hC, ?_⟩
  intro h hh hh'
  have hb := hbound h hh (by linarith)
  simpa only [f, macroBump_dilation] using hb

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
