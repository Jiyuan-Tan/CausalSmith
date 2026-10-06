module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Witnesses
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedGram
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Hostile thin-slab design and raw Gram degeneration -/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory Filter
open scoped BigOperators

/-- All raw linear features: intercept and the `d` coordinate slopes. -/
noncomputable def rawLinearFeature (d j : ℕ) (x : Fin d → ℝ) :
    Fin (d + 1) → ℝ :=
  fun a => if h : a.val = 0 then 1 else
    (x ⟨a.val - 1, by have := a.isLt; omega⟩ -
      (4 : ℝ) ^ (-(j : ℤ))) / ((4 : ℝ) ^ (-(j : ℤ)))

/-- Raw treated linear Gram, normalized by its treated cell mass. -/
noncomputable def rawHostileGram (d j : ℕ) (q : ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun a b =>
    (∫ x in hostileCube d j, hostilePropensity d q x *
      rawLinearFeature d j x a * rawLinearFeature d j x b ∂volume) /
    (∫ x in hostileCube d j, hostilePropensity d q x ∂volume)

-- @node: rawHostileGram_symmetric
/-- The raw treated Gram matrix is symmetric at every scale. -/
lemma rawHostileGram_symmetric (d j : ℕ) (q : ℝ)
    (a b : Fin (d + 1)) :
    rawHostileGram d j q a b = rawHostileGram d j q b a := by
  unfold rawHostileGram
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

-- @node: hostileCube_measurable
/-- Each hostile cube is measurable, so its treated mass is a valid set integral. -/
lemma hostileCube_measurable (d j : ℕ) :
    MeasurableSet (hostileCube d j) := by
  have hset : hostileCube d j =
      Set.Icc (fun _ : Fin d => (4 : ℝ) ^ (-(j : ℤ)))
        (fun _ : Fin d => 2 * (4 : ℝ) ^ (-(j : ℤ))) := by
    ext x
    simp only [hostileCube, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
    constructor
    · intro hx
      exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩
    · rintro ⟨hl, hu⟩ i
      exact ⟨hl i, hu i⟩
  rw [hset]
  exact measurableSet_Icc

-- @node: hostileSlab_measurable
/-- The raised-propensity slab is measurable. -/
lemma hostileSlab_measurable (d j : ℕ) (q : ℝ) :
    MeasurableSet (hostileSlab d j q) := by
  by_cases hd : 0 < d
  · have hset : hostileSlab d j q = hostileCube d j ∩
        {x : Fin d → ℝ |
          |(x ⟨0, hd⟩ - (4 : ℝ) ^ (-(j : ℤ))) /
            ((4 : ℝ) ^ (-(j : ℤ))) - 1 / 2| ≤
              ((4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / (3 * q)) / 2} := by
      ext x
      simp [hostileSlab, hd]
    rw [hset]
    apply (hostileCube_measurable d j).inter
    apply measurableSet_le
    · fun_prop
    · fun_prop
  · have hset : hostileSlab d j q = ∅ := by
      ext x
      simp [hostileSlab, hd]
    rw [hset]
    exact MeasurableSet.empty

/-- The least Rayleigh value of the full raw linear Gram matrix. -/
noncomputable def rawHostileMinEigenvalue (d j : ℕ) (q : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ a : Fin (d + 1) → ℝ,
    (∑ i, (a i) ^ 2) = 1 ∧ quadraticForm (rawHostileGram d j q) a = r}

/-- A proof direction supported on the intercept and first slope. -/
noncomputable def hostileDirection (d : ℕ) : Fin (d + 1) → ℝ :=
  fun a => if a.val = 0 then -1 / 2 else if a.val = 1 then 1 else 0

-- @node: hostileDirection_norm_sq
/-- The explicit intercept and first-slope direction has squared norm `5/4`. -/
lemma hostileDirection_norm_sq (d : ℕ) (hd : 1 ≤ d) :
    (∑ a : Fin (d + 1), hostileDirection d a ^ 2) = (5 : ℝ) / 4 := by
  letI : NeZero d := ⟨by omega⟩
  rw [Fin.sum_univ_succ]
  have h0 : hostileDirection d (0 : Fin (d + 1)) = -(1 : ℝ) / 2 := by
    simp [hostileDirection]
  rw [h0]
  have htail : (∑ a : Fin d, hostileDirection d a.succ ^ 2) = 1 := by
    let f : Fin d → ℝ := fun a => hostileDirection d a.succ ^ 2
    have hf : ∀ a : Fin d, a ≠ 0 → f a = 0 := by
      intro a ha
      simpa [f, hostileDirection] using ha
    rw [Fintype.sum_eq_single (0 : Fin d) (fun a ha => hf a ha)]
    simp [f, hostileDirection]
  rw [htail]
  norm_num

-- @node: unitHostileDirection
/-- Normalize the intercept-slope witness to a unit Euclidean vector. -/
noncomputable def unitHostileDirection (d : ℕ) : Fin (d + 1) → ℝ :=
  fun a => Real.sqrt ((4 : ℝ) / 5) * hostileDirection d a

-- @node: unitHostileDirection_norm_sq
/-- The hostile Rayleigh witness has exactly unit squared norm. -/
lemma unitHostileDirection_norm_sq (d : ℕ) (hd : 1 ≤ d) :
    (∑ a : Fin (d + 1), unitHostileDirection d a ^ 2) = 1 := by
  have hs : Real.sqrt ((4 : ℝ) / 5) ^ 2 = (4 : ℝ) / 5 := by
    rw [Real.sq_sqrt (by norm_num)]
  simp only [unitHostileDirection, mul_pow, ← Finset.mul_sum]
  rw [hs, hostileDirection_norm_sq d hd]
  norm_num

-- @node: hostileDirection_feature
/-- The Rayleigh witness reads the centered first normalized coordinate. -/
lemma hostileDirection_feature (d j : ℕ) (hd : 1 ≤ d) (x : Fin d → ℝ) :
    (∑ a : Fin (d + 1), hostileDirection d a * rawLinearFeature d j x a) =
      (x ⟨0, hd⟩ - (4 : ℝ) ^ (-(j : ℤ))) /
        ((4 : ℝ) ^ (-(j : ℤ))) - 1 / 2 := by
  letI : NeZero d := ⟨by omega⟩
  rw [Fin.sum_univ_succ]
  have h0 : hostileDirection d (0 : Fin (d + 1)) *
      rawLinearFeature d j x (0 : Fin (d + 1)) = -(1 : ℝ) / 2 := by
    simp [hostileDirection, rawLinearFeature]
  rw [h0]
  have htail : (∑ a : Fin d,
      hostileDirection d a.succ * rawLinearFeature d j x a.succ) =
      (x ⟨0, hd⟩ - (4 : ℝ) ^ (-(j : ℤ))) /
        ((4 : ℝ) ^ (-(j : ℤ))) := by
    rw [Fintype.sum_eq_single (0 : Fin d)]
    · have hs : (Fin.succ (0 : Fin d) : Fin (d + 1)) = ⟨1, by omega⟩ := by
        ext
        simp
        omega
      rw [hs]
      simp [hostileDirection, rawLinearFeature]
    · intro a ha
      have hzero : hostileDirection d a.succ = 0 := by
        simpa [hostileDirection] using ha
      simp [hzero]
  rw [htail]
  ring

-- @node: unitHostileDirection_feature
/-- The unit Rayleigh witness is the rescaled centered first coordinate. -/
lemma unitHostileDirection_feature (d j : ℕ) (hd : 1 ≤ d)
    (x : Fin d → ℝ) :
    (∑ a : Fin (d + 1), unitHostileDirection d a * rawLinearFeature d j x a) =
      Real.sqrt ((4 : ℝ) / 5) *
        ((x ⟨0, hd⟩ - (4 : ℝ) ^ (-(j : ℤ))) /
          ((4 : ℝ) ^ (-(j : ℤ))) - 1 / 2) := by
  simp only [unitHostileDirection, mul_assoc, ← Finset.mul_sum]
  rw [hostileDirection_feature d j hd x]

-- @node: hostileDirection_slab_bound
/-- On the raised-propensity slab, the Rayleigh witness is bounded by half
the shrinking slab width. -/
lemma hostileDirection_slab_bound (d j : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (x : Fin d → ℝ) (hx : x ∈ hostileSlab d j q) :
    |∑ a : Fin (d + 1), hostileDirection d a * rawLinearFeature d j x a| ≤
      ((4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / (3 * q)) / 2 := by
  rw [hostileDirection_feature d j hd x]
  simpa [hostileSlab, show 0 < d by omega] using hx.2

-- @node: unitHostileDirection_slab_bound
/-- The unit Rayleigh witness is small on the high-propensity slab. -/
lemma unitHostileDirection_slab_bound (d j : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (x : Fin d → ℝ) (hx : x ∈ hostileSlab d j q) :
    |∑ a : Fin (d + 1), unitHostileDirection d a * rawLinearFeature d j x a| ≤
      Real.sqrt ((4 : ℝ) / 5) *
        (((4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / (3 * q)) / 2) := by
  have hscale : 0 ≤ Real.sqrt ((4 : ℝ) / 5) := Real.sqrt_nonneg _
  rw [unitHostileDirection_feature d j hd x, abs_mul,
    abs_of_nonneg hscale]
  exact mul_le_mul_of_nonneg_left (by
    simpa only [hostileDirection_feature d j hd x] using
      hostileDirection_slab_bound d j q hd x hx) hscale

-- @node: unitHostileDirection_slab_sq_bound
/-- The slab contribution to the normalized Rayleigh numerator is quadratic
in its shrinking width. -/
lemma unitHostileDirection_slab_sq_bound (d j : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (x : Fin d → ℝ) (hx : x ∈ hostileSlab d j q) :
    (∑ a : Fin (d + 1), unitHostileDirection d a * rawLinearFeature d j x a) ^ 2 ≤
      (((4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / (3 * q))) ^ 2 / 5 := by
  let η : ℝ := ((4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / (3 * q))
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hb := unitHostileDirection_slab_bound d j q hd x hx
  have hs : Real.sqrt ((4 : ℝ) / 5) ^ 2 = (4 : ℝ) / 5 := by
    rw [Real.sq_sqrt (by norm_num)]
  have hbound : 0 ≤ Real.sqrt ((4 : ℝ) / 5) * (η / 2) := by positivity
  have hsq :
      (∑ a : Fin (d + 1), unitHostileDirection d a * rawLinearFeature d j x a) ^ 2 ≤
        (Real.sqrt ((4 : ℝ) / 5) * (η / 2)) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hbound).2 (by simpa only [η] using hb)
  rw [mul_pow, hs] at hsq
  dsimp [η] at *
  nlinarith

-- @node: hostileDirection_cube_bound
/-- The centered slope witness is uniformly bounded throughout its cube. -/
lemma hostileDirection_cube_bound (d j : ℕ) (hd : 1 ≤ d)
    (x : Fin d → ℝ) (hx : x ∈ hostileCube d j) :
    |∑ a : Fin (d + 1), hostileDirection d a * rawLinearFeature d j x a| ≤
      (1 : ℝ) / 2 := by
  rw [hostileDirection_feature d j hd x]
  have hh : 0 < (4 : ℝ) ^ (-(j : ℤ)) := by positivity
  have hfirst := hx ⟨0, hd⟩
  have hu : 0 ≤ (x ⟨0, hd⟩ - (4 : ℝ) ^ (-(j : ℤ))) /
      (4 : ℝ) ^ (-(j : ℤ)) ∧
      (x ⟨0, hd⟩ - (4 : ℝ) ^ (-(j : ℤ))) /
        (4 : ℝ) ^ (-(j : ℤ)) ≤ 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hfirst.1) hh.le
    · apply (div_le_iff₀ hh).2
      nlinarith [hfirst.2]
  rw [abs_le]
  constructor <;> linarith [hu.1, hu.2]

-- @node: unitHostileDirection_cube_sq_bound
/-- The normalized witness is uniformly bounded on the whole hostile cube. -/
lemma unitHostileDirection_cube_sq_bound (d j : ℕ) (hd : 1 ≤ d)
    (x : Fin d → ℝ) (hx : x ∈ hostileCube d j) :
    (∑ a : Fin (d + 1), unitHostileDirection d a * rawLinearFeature d j x a) ^ 2 ≤
      (1 : ℝ) / 5 := by
  have hb := hostileDirection_cube_bound d j hd x hx
  have hscale : 0 ≤ Real.sqrt ((4 : ℝ) / 5) := Real.sqrt_nonneg _
  have hunit :
      |∑ a : Fin (d + 1), unitHostileDirection d a * rawLinearFeature d j x a| ≤
        Real.sqrt ((4 : ℝ) / 5) / 2 := by
    rw [unitHostileDirection_feature d j hd x, abs_mul, abs_of_nonneg hscale]
    simpa [hostileDirection_feature d j hd x, div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hb hscale
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity :
      0 ≤ Real.sqrt ((4 : ℝ) / 5) / 2)).2 hunit
  rw [sq_abs] at hsq
  have hs : Real.sqrt ((4 : ℝ) / 5) ^ 2 = (4 : ℝ) / 5 := by
    rw [Real.sq_sqrt (by norm_num)]
  nlinarith [hs]

-- @node: hostileCube_disjoint
/-- Hostile cubes at distinct scales have disjoint supports. -/
lemma hostileCube_disjoint (d j k : ℕ) (hd : 1 ≤ d)
    (hjk : j ≠ k) :
    Disjoint (hostileCube d j) (hostileCube d k) := by
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  have hpow (a b : ℕ) (hab : a < b) :
      2 * (4 : ℝ) ^ (-(b : ℤ)) < (4 : ℝ) ^ (-(a : ℤ)) := by
    have hgap : a + 1 ≤ b := hab
    have hp : (4 : ℝ) ^ (a + 1) ≤ (4 : ℝ) ^ b :=
      pow_le_pow_right₀ (by norm_num) hgap
    have ha : 0 < (4 : ℝ) ^ a := by positivity
    have hb : 0 < (4 : ℝ) ^ b := by positivity
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
    rw [pow_succ] at hp
    calc
      2 * ((4 : ℝ) ^ b)⁻¹ = 2 / (4 : ℝ) ^ b := by ring
      _ < 1 / (4 : ℝ) ^ a :=
        (div_lt_div_iff₀ hb ha).2 (by nlinarith)
      _ = ((4 : ℝ) ^ a)⁻¹ := by ring
  rcases lt_or_gt_of_ne hjk with h | h
  · have hsep := hpow j k h
    have hjx := hxj ⟨0, hd⟩
    have hkx := hxk ⟨0, hd⟩
    linarith
  · have hsep := hpow k j h
    have hjx := hxj ⟨0, hd⟩
    have hkx := hxk ⟨0, hd⟩
    linarith

-- @node: hostileCube_subset_cube
/-- Every hostile cube at a positive scale lies inside the design cube. -/
lemma hostileCube_subset_cube (d j : ℕ) (hj : 1 ≤ j) :
    hostileCube d j ⊆ cube d := by
  intro x hx i _
  have hjpow : (4 : ℝ) ≤ (4 : ℝ) ^ j := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj :
      (4 : ℝ) ^ 1 ≤ (4 : ℝ) ^ j)
  have hpowpos : 0 < (4 : ℝ) ^ j := by positivity
  have hwidth : 2 * (4 : ℝ) ^ (-(j : ℤ)) ≤ 1 := by
    rw [zpow_neg, zpow_natCast]
    apply (div_le_iff₀ hpowpos).2
    nlinarith
  exact ⟨(by exact (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _).trans (hx i).1),
    (hx i).2.trans hwidth⟩

-- @node: hostilePropensity_eq_one_on_slab
/-- The raised part of the design has propensity one. -/
lemma hostilePropensity_eq_one_on_slab (d j : ℕ) (q : ℝ)
    (hj : 1 ≤ j) (x : Fin d → ℝ) (hx : x ∈ hostileSlab d j q) :
    hostilePropensity d q x = 1 := by
  have h : ∃ k : ℕ, 1 ≤ k ∧ x ∈ hostileSlab d k q := ⟨j, hj, hx⟩
  simp [hostilePropensity, h]

-- @node: hostilePropensity_eq_baseline_off_slab
/-- Within one hostile cube, its own slab is the only possible raised part. -/
lemma hostilePropensity_eq_baseline_off_slab (d j : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (x : Fin d → ℝ)
    (hx : x ∈ hostileCube d j) (hnot : x ∉ hostileSlab d j q) :
    hostilePropensity d q x = baselinePropensity d q x := by
  have hnone : ¬ ∃ k : ℕ, 1 ≤ k ∧ x ∈ hostileSlab d k q := by
    rintro ⟨k, -, hslab⟩
    by_cases hkj : k = j
    · exact hnot (hkj ▸ hslab)
    · exact (Set.disjoint_left.mp
        (hostileCube_disjoint d k j hd hkj)) hslab.1 hx
  simp [hostilePropensity, hnone]

-- @node: baselinePropensity_upper_on_hostileCube
/-- The untreated background contribution is small on the hostile cube. -/
lemma baselinePropensity_upper_on_hostileCube (d j : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (x : Fin d → ℝ)
    (hx : x ∈ hostileCube d j) :
    baselinePropensity d q x ≤
      (2 * (4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / q) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hh : 0 < (4 : ℝ) ^ (-(j : ℤ)) := by positivity
  have hmax : maxCoordinate x ≤ 2 * (4 : ℝ) ^ (-(j : ℤ)) := by
    unfold maxCoordinate
    apply csSup_le
    · exact Set.range_nonempty x
    · rintro y ⟨i, rfl⟩
      exact (hx i).2
  have hmax_nonneg : 0 ≤ maxCoordinate x := by
    have hle : x ⟨0, hd⟩ ≤ maxCoordinate x := by
      unfold maxCoordinate
      exact le_csSup ⟨2 * (4 : ℝ) ^ (-(j : ℤ)), by
        rintro y ⟨i, rfl⟩; exact (hx i).2⟩ ⟨⟨0, hd⟩, rfl⟩
    exact hh.le.trans ((hx ⟨0, hd⟩).1.trans hle)
  unfold baselinePropensity
  exact Real.rpow_le_rpow hmax_nonneg hmax (by positivity)

-- @node: hostilePropensity_ge_baseline_on_cube
/-- Raising the propensity to one on a slab preserves the baseline lower bound. -/
lemma hostilePropensity_ge_baseline_on_cube (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    baselinePropensity d q x ≤ hostilePropensity d q x := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmax : maxCoordinate x ≤ 1 := by
    unfold maxCoordinate
    apply csSup_le
    · exact Set.range_nonempty x
    · rintro y ⟨i, rfl⟩
      exact (hx i (Set.mem_univ i)).2
  have hmax_nonneg : 0 ≤ maxCoordinate x := by
    have hle : x ⟨0, hd⟩ ≤ maxCoordinate x := by
      unfold maxCoordinate
      exact le_csSup ⟨1, by rintro y ⟨i, rfl⟩; exact (hx i (Set.mem_univ i)).2⟩
        ⟨⟨0, hd⟩, rfl⟩
    exact (hx ⟨0, hd⟩ (Set.mem_univ _)).1.trans hle
  have hpow : baselinePropensity d q x ≤ 1 := by
    unfold baselinePropensity
    exact Real.rpow_le_one hmax_nonneg hmax (by positivity)
  unfold hostilePropensity
  split_ifs with h
  · exact hpow
  · exact le_rfl

-- @node: hostilePropensity_nonneg_on_cube
/-- The hostile treatment weight is nonnegative on the design cube. -/
lemma hostilePropensity_nonneg_on_cube (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    0 ≤ hostilePropensity d q x := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmax : 0 ≤ maxCoordinate x := by
    have hle : x ⟨0, hd⟩ ≤ maxCoordinate x := by
      unfold maxCoordinate
      exact le_csSup ⟨1, by
        rintro y ⟨i, rfl⟩
        exact (hx i (Set.mem_univ i)).2⟩ ⟨⟨0, hd⟩, rfl⟩
    exact (hx ⟨0, hd⟩ (Set.mem_univ _)).1.trans hle
  exact (Real.rpow_nonneg hmax _).trans
    (hostilePropensity_ge_baseline_on_cube d q hd hq x hx)

-- @node: hostilePropensity_le_one_on_cube
/-- Raising the baseline weight on a slab never exceeds one on the cube. -/
lemma hostilePropensity_le_one_on_cube (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    hostilePropensity d q x ≤ 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmax : maxCoordinate x ≤ 1 := by
    unfold maxCoordinate
    apply csSup_le
    · exact Set.range_nonempty x
    · rintro y ⟨i, rfl⟩
      exact (hx i (Set.mem_univ i)).2
  have hmax_nonneg : 0 ≤ maxCoordinate x := by
    have hle : x ⟨0, hd⟩ ≤ maxCoordinate x := by
      unfold maxCoordinate
      exact le_csSup ⟨1, by
        rintro y ⟨i, rfl⟩
        exact (hx i (Set.mem_univ i)).2⟩ ⟨⟨0, hd⟩, rfl⟩
    exact (hx ⟨0, hd⟩ (Set.mem_univ _)).1.trans hle
  unfold hostilePropensity
  split_ifs
  · exact le_rfl
  · exact Real.rpow_le_one hmax_nonneg hmax (by positivity)

-- @node: hostilePropensity_pos_on_hostileCube
/-- Treated mass has positive pointwise density throughout a hostile cube. -/
lemma hostilePropensity_pos_on_hostileCube (d j : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hj : 1 ≤ j)
    (x : Fin d → ℝ) (hx : x ∈ hostileCube d j) :
    0 < hostilePropensity d q x := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmax : 0 < maxCoordinate x := by
    have hle : x ⟨0, hd⟩ ≤ maxCoordinate x := by
      unfold maxCoordinate
      exact le_csSup ⟨1, by
        rintro y ⟨i, rfl⟩
        exact ((hostileCube_subset_cube d j hj hx) i (Set.mem_univ i)).2⟩
        ⟨⟨0, hd⟩, rfl⟩
    exact lt_of_lt_of_le (lt_of_lt_of_le (by positivity) (hx ⟨0, hd⟩).1) hle
  have hbase : 0 < baselinePropensity d q x := by
    unfold baselinePropensity
    exact Real.rpow_pos_of_pos hmax _
  exact hbase.trans_le (hostilePropensity_ge_baseline_on_cube d q hd hq x
    (hostileCube_subset_cube d j hj hx))

-- @node: baselinePropensity_sublevel_volume
/-- The uniform cube mass below the baseline propensity is exactly controlled
by its power-law envelope. -/
lemma baselinePropensity_sublevel_volume (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    (volume.restrict (cube d)).real
      {x | baselinePropensity d q x ≤ t} ≤ t ^ q := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  let r : ℝ := t ^ (q / d)
  have hr0 : 0 ≤ r := by dsimp [r]; exact Real.rpow_nonneg (le_of_lt ht.1) _
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact Real.rpow_le_one (le_of_lt ht.1) ht.2 (le_of_lt (div_pos hq hdpos))
  let B : Set (Fin d → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) r)
  have hBcube : B ⊆ cube d := by
    intro x hx i hi
    exact ⟨(hx i hi).1, (hx i hi).2.trans hr1⟩
  have hsub : {x | baselinePropensity d q x ≤ t} ∩ cube d ⊆ B := by
    rintro x ⟨hxt, hx⟩ i hi
    have hmax0 : 0 ≤ maxCoordinate x := by
      letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      have hle : x ⟨0, hd⟩ ≤ maxCoordinate x := by
        unfold maxCoordinate
        exact le_csSup ⟨1, by rintro y ⟨k, rfl⟩; exact (hx k (Set.mem_univ k)).2⟩
          ⟨⟨0, hd⟩, rfl⟩
      exact (hx ⟨0, hd⟩ (Set.mem_univ _)).1.trans hle
    have hmaxle : maxCoordinate x ≤ r := by
      have hp := Real.rpow_le_rpow (Real.rpow_nonneg hmax0 _)
        (show (maxCoordinate x) ^ ((d : ℝ) / q) ≤ t by
          simpa [baselinePropensity] using hxt) (le_of_lt (div_pos hq hdpos))
      have heq : ((maxCoordinate x) ^ ((d : ℝ) / q)) ^ (q / d) = maxCoordinate x := by
        rw [← Real.rpow_mul hmax0]
        have : (d : ℝ) / q * (q / d) = 1 := by field_simp
        simp [this]
      simpa only [r, heq] using hp
    have hile : x i ≤ maxCoordinate x := by
      unfold maxCoordinate
      exact le_csSup ⟨1, by rintro y ⟨k, rfl⟩; exact (hx k (Set.mem_univ k)).2⟩
        ⟨i, rfl⟩
    exact ⟨(hx i hi).1, hile.trans hmaxle⟩
  have hfinite : volume (cube d) ≠ ⊤ := by simp [cube, Real.volume_Icc_pi]
  have hmeasure : (volume.restrict (cube d)).real
      {x | baselinePropensity d q x ≤ t} ≤ volume.real B := by
    have hmono : {x | baselinePropensity d q x ≤ t} ∩ cube d ⊆ B := hsub
    rw [measureReal_restrict_apply' (by simp [cube] : MeasurableSet (cube d))]
    exact measureReal_mono hmono (by
      have hBfinite : volume B ≤ volume (cube d) := measure_mono hBcube
      exact ne_top_of_le_ne_top hfinite hBfinite)
  have hvol : volume.real B = r ^ d := by
    dsimp [B]
    rw [show Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) r) =
      Set.Icc (fun _ => (0 : ℝ)) (fun _ => r) by ext x; simp]
    change (volume (Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => r))).toReal = r ^ d
    rw [Real.volume_Icc_pi_toReal (fun _ => hr0)]
    simp
  calc
    (volume.restrict (cube d)).real {x | baselinePropensity d q x ≤ t}
        ≤ volume.real B := hmeasure
    _ = r ^ d := hvol
    _ = t ^ q := by
      dsimp [r]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt ht.1)]
      congr 1
      field_simp

-- @node: hostileScale_power_tendsto_zero
/-- The power of the hostile cube width occurring in the Rayleigh bound vanishes. -/
lemma hostileScale_power_tendsto_zero (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) :
    Tendsto (fun j : ℕ =>
      ((4 : ℝ) ^ (-(j : ℤ))) ^ ((2 * (d : ℝ)) / (3 * q))) atTop (nhds 0) := by
  have hbase : Tendsto (fun j : ℕ => ((4 : ℝ)⁻¹) ^ j) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hexp : 0 ≤ (2 * (d : ℝ)) / (3 * q) := by positivity
  have h := hbase.rpow_const (Or.inr hexp)
  simpa only [zpow_neg, zpow_natCast, inv_pow, Real.zero_rpow (ne_of_gt (by positivity :
    0 < (2 * (d : ℝ)) / (3 * q)))] using h

-- @node: hostileRayleighUpper_tendsto_zero
/-- The explicit upper bound in the thin-slab Rayleigh estimate tends to zero. -/
lemma hostileRayleighUpper_tendsto_zero (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) :
    Tendsto (fun j : ℕ =>
      ((4 : ℝ) / 5) *
        (1 / 4 + (2 : ℝ) ^ ((d : ℝ) / q - 2)) *
        ((4 : ℝ) ^ (-(j : ℤ))) ^ ((2 * (d : ℝ)) / (3 * q)))
      atTop (nhds 0) := by
  have h := (hostileScale_power_tendsto_zero d q hd hq).const_mul
    ((4 : ℝ) / 5 * (1 / 4 + (2 : ℝ) ^ ((d : ℝ) / q - 2)))
  simpa only [mul_zero, mul_assoc] using h


end CausalSmith.Stat.GlobalTailDesignRobustCate
