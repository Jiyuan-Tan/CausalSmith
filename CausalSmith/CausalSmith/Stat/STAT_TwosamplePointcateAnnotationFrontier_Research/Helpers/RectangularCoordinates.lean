module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RectangularMomentBounds

/-! # Coordinate bounds for the rectangular vector and raw Gram matrix
Both types of coordinate are instances of the original-record marked moment
bound. Their constants depend only on dimension, and hence are uniform in the
law, sample counts, and localization grid.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- A common finite variance constant for vector and raw-matrix coordinates.  Given [the specified input d](hyp:d), [rectangular coordinate constant](goal) is the corresponding construction. -/
def rectangularCoordinateConstant (d : ℕ) : ℝ :=
  let M := ((4:ℝ)^d)^2
  6*M^2 + 12*(M*M)^2*(((Fintype.card (PolyIdx d):ℝ)*((4:ℝ)^d)^2)^2+1)

/-- Coarse basis coordinates times a binary mark share a dimension-only local bound.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the specified input u](hyp:u), [the specified input a](hyp:a), [the rectangular coarse mark bound conclusion](goal) holds. -/
lemma rectangular_coarse_mark_bound (d : ℕ) (h : ℝ) (hh : 0 < h)
    (x : Cov d) (hx : x ∈ locCube d h) (u : PolyIdx d) (a : Bool) :
    |coarseBasis h x u * bit a| ≤ ((4:ℝ)^d)^2 := by
  rw [abs_mul]
  have hb : 1 ≤ (4:ℝ)^d := one_le_pow₀ (by norm_num)
  calc
    _ ≤ (4:ℝ)^d * 1 := mul_le_mul (coarseBasis_abs_bound d h hh x hx u)
      (rectangular_bit_abs_le_one a) (abs_nonneg _) (by positivity)
    _ ≤ _ := by nlinarith

/-- A product of two coarse coordinates and a binary mark has the same common bound.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the specified input u](hyp:u), [the specified input v](hyp:v), [the specified input a](hyp:a), [the rectangular coarse pair mark bound conclusion](goal) holds. -/
lemma rectangular_coarse_pair_mark_bound (d : ℕ) (h : ℝ) (hh : 0 < h)
    (x : Cov d) (hx : x ∈ locCube d h) (u v : PolyIdx d) (a : Bool) :
    |coarseBasis h x u * coarseBasis h x v * bit a| ≤ ((4:ℝ)^d)^2 := by
  rw [abs_mul, abs_mul]
  calc
    _ ≤ ((4:ℝ)^d * (4:ℝ)^d) * 1 :=
      mul_le_mul (mul_le_mul (coarseBasis_abs_bound d h hh x hx u)
        (coarseBasis_abs_bound d h hh x hx v) (abs_nonneg _) (by positivity))
        (rectangular_bit_abs_le_one a) (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The vector coordinate's centered energy has the claimed rectangular sampling order.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the rectangular r coordinate bound conclusion](goal) holds. -/
lemma rectangular_r_coordinate_bound {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) (hn : 2 ≤ n)
    (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J) (u : PolyIdx d) :
    MemLp (fun w : Sample d n m => rHat w.1 h J u) 2 (experiment P n m) ∧
    (∫ w, (rHat w.1 h J u-rBar P n m h J u)^2 ∂experiment P n m) ≤
      rectangularCoordinateConstant d *
        (1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
          ((n:ℝ)*((n:ℝ)+m)*h^(2*d))) := by
  let f0 := fun z : Cov d × Bool × Bool => coarseBasis h z.1 u * bit z.2.1 * bit z.2.2
  let f := fun z : Cov d × Bool => coarseBasis h z.1 u * bit z.2
  let g := fun z : Cov d × Bool × Bool => bit z.2.2
  let H := fun p : (Cov d × Bool) × (Cov d × Bool × Bool) =>
    locWeight h p.1.1 * locWeight h p.2.1 * fineKernel d h J p.1.1 p.2.1 * f p.1 * g p.2
  have hf0 : Measurable f0 := by dsimp [f0]; fun_prop
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  have h0 (z : Cov d × Bool × Bool) (hz : z.1 ∈ locCube d h) : |f0 z| ≤ ((4:ℝ)^d)^2 := by
    dsimp [f0]
    rw [abs_mul]
    calc
      _ ≤ ((4:ℝ)^d)^2 * 1 := mul_le_mul (rectangular_coarse_mark_bound d h hh z.1 hz u z.2.1)
        (rectangular_bit_abs_le_one _) (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hfB (z : Cov d × Bool) (hz : z.1 ∈ locCube d h) : |f z| ≤ ((4:ℝ)^d)^2 :=
    rectangular_coarse_mark_bound d h hh z.1 hz u z.2
  have hgB (z : Cov d × Bool × Bool) (_ : z.1 ∈ locCube d h) : |g z| ≤ ((4:ℝ)^d)^2 := by
    have hb : 1 ≤ (4:ℝ)^d := one_le_pow₀ (by norm_num)
    exact (rectangular_bit_abs_le_one _).trans (by nlinarith)
  have hb := rectangular_marked_moment_bound (m := m) P hP hn h J hh hh' hJ f0 f g hf0 hf hg
    (((4:ℝ)^d)^2) (by positivity) h0 hfB hgB
  have he : (fun w : Sample d n m => rHat w.1 h J u) =
      (fun w => rectangularOutcomeAverage (fun z => locWeight h z.1*f0 z) w - rectangularAverage H w) := by
    funext w
    rw [rHat_rectangular]
    dsimp [rectangularOutcomeAverage, rectangularAverage, H, f0, f, g]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  change MemLp (fun w => rectangularOutcomeAverage (fun z => locWeight h z.1*f0 z) w-rectangularAverage H w) 2 _ ∧ _ at hb
  rw [← he] at hb
  exact hb

/-- Every raw Gram coordinate has the same dimension-only centered-energy bound.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the specified input v](hyp:v), [the rectangular q coordinate bound conclusion](goal) holds. -/
lemma rectangular_q_coordinate_bound {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) (hn : 2 ≤ n)
    (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J) (u v : PolyIdx d) :
    MemLp (fun w : Sample d n m => qRaw w.1 h J u v) 2 (experiment P n m) ∧
    (∫ w, (qRaw w.1 h J u v-∫ z, qRaw z.1 h J u v ∂experiment P n m)^2 ∂experiment P n m) ≤
      rectangularCoordinateConstant d *
        (1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
          ((n:ℝ)*((n:ℝ)+m)*h^(2*d))) := by
  let f0 := fun z : Cov d × Bool × Bool => coarseBasis h z.1 u * coarseBasis h z.1 v * bit z.2.1
  let f := fun z : Cov d × Bool => coarseBasis h z.1 u * bit z.2
  let g := fun z : Cov d × Bool × Bool => coarseBasis h z.1 v * bit z.2.1
  let H := fun p : (Cov d × Bool) × (Cov d × Bool × Bool) =>
    locWeight h p.1.1 * locWeight h p.2.1 * fineKernel d h J p.1.1 p.2.1 * f p.1 * g p.2
  have hf0 : Measurable f0 := by dsimp [f0]; fun_prop
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  have h0 (z : Cov d × Bool × Bool) (hz : z.1 ∈ locCube d h) : |f0 z| ≤ ((4:ℝ)^d)^2 :=
    rectangular_coarse_pair_mark_bound d h hh z.1 hz u v z.2.1
  have hfB (z : Cov d × Bool) (hz : z.1 ∈ locCube d h) : |f z| ≤ ((4:ℝ)^d)^2 :=
    rectangular_coarse_mark_bound d h hh z.1 hz u z.2
  have hgB (z : Cov d × Bool × Bool) (hz : z.1 ∈ locCube d h) : |g z| ≤ ((4:ℝ)^d)^2 :=
    rectangular_coarse_mark_bound d h hh z.1 hz v z.2.1
  have hb := rectangular_marked_moment_bound (m := m) P hP hn h J hh hh' hJ f0 f g hf0 hf hg
    (((4:ℝ)^d)^2) (by positivity) h0 hfB hgB
  have he : (fun w : Sample d n m => qRaw w.1 h J u v) =
      (fun w => rectangularOutcomeAverage (fun z => locWeight h z.1*f0 z) w - rectangularAverage H w) := by
    funext w
    dsimp [qRaw, rectangularOutcomeAverage, rectangularAverage, H, f0, f, g]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  change MemLp (fun w => rectangularOutcomeAverage (fun z => locWeight h z.1*f0 z) w-rectangularAverage H w) 2 _ ∧ _ at hb
  rw [← he] at hb
  exact hb

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
