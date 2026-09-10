import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.Sampling

/-! Elementary monotone interval propagation used by the finite-sample envelope. -/

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

/-- A closed real interval used for dependency-preserving arithmetic propagation. -/
structure IntervalBound where
  lower : ℝ
  upper : ℝ

def IntervalBound.point (x : ℝ) : IntervalBound := ⟨x, x⟩

def IntervalBound.add (x y : IntervalBound) : IntervalBound :=
  ⟨x.lower + y.lower, x.upper + y.upper⟩

def IntervalBound.neg (x : IntervalBound) : IntervalBound :=
  ⟨-x.upper, -x.lower⟩

def IntervalBound.sub (x y : IntervalBound) : IntervalBound := x.add y.neg

def min4 (a b c d : ℝ) : ℝ := min (min a b) (min c d)

def max4 (a b c d : ℝ) : ℝ := max (max a b) (max c d)

def IntervalBound.mul (x y : IntervalBound) : IntervalBound :=
  ⟨min4 (x.lower * y.lower) (x.lower * y.upper)
      (x.upper * y.lower) (x.upper * y.upper),
    max4 (x.lower * y.lower) (x.lower * y.upper)
      (x.upper * y.lower) (x.upper * y.upper)⟩

noncomputable def IntervalBound.div (x y : IntervalBound) : IntervalBound :=
  ⟨min4 (x.lower / y.lower) (x.lower / y.upper)
      (x.upper / y.lower) (x.upper / y.upper),
    max4 (x.lower / y.lower) (x.lower / y.upper)
      (x.upper / y.lower) (x.upper / y.upper)⟩

def IntervalBound.max (x y : IntervalBound) : IntervalBound :=
  ⟨Max.max x.lower y.lower, Max.max x.upper y.upper⟩

def IntervalBound.min (x y : IntervalBound) : IntervalBound :=
  ⟨Min.min x.lower y.lower, Min.min x.upper y.upper⟩

def IntervalBound.unitClamp (x : IntervalBound) : IntervalBound :=
  ⟨Max.max 0 x.lower, Min.min 1 x.upper⟩

lemma add_mem_Icc {x y lx ux ly uy : ℝ}
    (hx : x ∈ Set.Icc lx ux) (hy : y ∈ Set.Icc ly uy) :
    x + y ∈ Set.Icc (lx + ly) (ux + uy) := by
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma max_mem_Icc {x y lx ux ly uy : ℝ}
    (hx : x ∈ Set.Icc lx ux) (hy : y ∈ Set.Icc ly uy) :
    max x y ∈ Set.Icc (max lx ly) (max ux uy) := by
  constructor
  · exact max_le_max hx.1 hy.1
  · exact max_le_max hx.2 hy.2

lemma min_mem_Icc {x y lx ux ly uy : ℝ}
    (hx : x ∈ Set.Icc lx ux) (hy : y ∈ Set.Icc ly uy) :
    min x y ∈ Set.Icc (min lx ly) (min ux uy) := by
  constructor
  · exact min_le_min hx.1 hy.1
  · exact min_le_min hx.2 hy.2

lemma div_mem_Icc_of_pos {x y lx ux ly uy : ℝ}
    (hx : x ∈ Set.Icc lx ux) (hy : y ∈ Set.Icc ly uy) (hly : 0 < ly) :
    x / y ∈ Set.Icc (min (lx / ly) (lx / uy))
      (max (ux / ly) (ux / uy)) := by
  have hypos : 0 < y := lt_of_lt_of_le hly hy.1
  have huypos : 0 < uy := lt_of_lt_of_le hypos hy.2
  constructor
  · apply le_trans ?_ ((div_le_div_iff_of_pos_right hypos).2 hx.1)
    by_cases hlx : 0 ≤ lx
    · exact le_trans (min_le_right _ _)
        (div_le_div_of_nonneg_left hlx hypos hy.2)
    · apply le_trans (min_le_left _ _)
      have hneg : 0 ≤ -lx := by linarith
      have hdiv := div_le_div_of_nonneg_left hneg hly hy.1
      rw [neg_div, neg_div] at hdiv
      linarith
  · apply le_trans ((div_le_div_iff_of_pos_right hypos).2 hx.2)
    by_cases hux : 0 ≤ ux
    · exact le_trans (div_le_div_of_nonneg_left hux hly hy.1)
        (le_max_left _ _)
    · apply le_trans ?_ (le_max_right _ _)
      have hneg : 0 ≤ -ux := by linarith
      have hdiv := div_le_div_of_nonneg_left hneg hypos hy.2
      rw [neg_div, neg_div] at hdiv
      linarith

end CausalSmith.PartialID.ImperfectrefCutoffRegret
