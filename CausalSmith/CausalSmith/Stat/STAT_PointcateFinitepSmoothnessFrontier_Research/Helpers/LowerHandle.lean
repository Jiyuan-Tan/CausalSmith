module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LawConstruction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Finite-moment point-CATE frontier: Helpers/LowerHandle. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


-- @env: S5
variable (κ : Params) (n : ℕ)
/-- Fixed baseline assignment probability. -/
def lowerP0 : ℝ := 3/8
/-- Public interaction denominator. -/
def lowerDenom : ℝ := 1+sumReg κ/κ.γ+2*κ.α+κ.β/qExp κ
/-- Public small grid multiplier. -/
def lowerC : ℝ := min (1/1000) ((4 : ℝ)^(-κ.γ/sumReg κ))
/-- Optimized grid spacing. -/
def lowerEll : ℝ := lowerC κ * (n : ℝ)^(-2/lowerDenom κ)
/-- Macro localization radius. -/
def lowerH : ℝ := lowerEll κ n ^ (sumReg κ/κ.γ)
/-- Propensity perturbation amplitude. -/
def lowerA : ℝ := lowerEll κ n ^ κ.α / 1024
/-- Baseline perturbation amplitude. -/
def lowerB : ℝ := lowerEll κ n ^ κ.β / 1024
/-- Rare outcome amplitude. -/
def lowerAmplitude : ℝ := lowerB κ n ^ (-1/(κ.p-1))
/-- Rare mark probability. -/
def lowerRare : ℝ := 4 * lowerAmplitude κ n ^ (-κ.p)
/-- Number of squared-frame coordinates. -/
def signCount : ℕ := ⌈1/lowerEll κ n⌉₊+1
/-- Sign vectors have a finite, uniform, independent fair-sign distribution. -/
abbrev Signs := Fin (signCount κ n) → Bool
/-- A boolean sign is encoded as plus or minus one. -/
def sign (v : Bool) : ℝ := if v then 1 else -1
/-- Continuous sine-cosine squared partition of unity on the spacing grid. -/
def frame (j : Fin (signCount κ n)) (x : unitInterval) : ℝ :=
  let u := (x : ℝ)/lowerEll κ n - (j.val : ℝ)
  if 0 ≤ u ∧ u ≤ 1 then Real.cos (Real.pi*u/2)
  else if -1 ≤ u ∧ u < 0 then Real.sin (Real.pi*(u+1)/2) else 0
/-- Triangular macro cutoff. -/
def lowerCutoff (x : unitInterval) : ℝ := max 0 (1-|(x : ℝ)-1/2|/lowerH κ n)
/-- Shared-sign localized field. -/
def lowerField (v : Signs κ n) (x : unitInterval) : ℝ :=
  lowerCutoff κ n x * ∑ j, sign (v j) * frame κ n j x
/-- Deterministic squared localization field. -/
def lowerSquare (x : unitInterval) : ℝ := (lowerCutoff κ n x)^2
/-- Perturbed propensity. -/
def lowerPropensity (v : Signs κ n) (x : unitInterval) : ℝ := lowerP0 + lowerA κ n * lowerField κ n v x
/-- The arm means share the localized signs. -/
def lowerMean (ε : Bool) (v : Signs κ n) (z : Bool) (x : unitInterval) : ℝ :=
  sign ε * lowerB κ n * lowerField κ n v x +
  (if z then -(sign ε * lowerA κ n * lowerB κ n * lowerSquare κ n x)/lowerP0
   else (sign ε * lowerA κ n * lowerB κ n * lowerSquare κ n x)/(1-lowerP0))
/-- Effect is deterministic across each sign-prior support. -/
def lowerEffect (ε : Bool) (x : unitInterval) : ℝ :=
  -(sign ε * lowerA κ n * lowerB κ n * lowerSquare κ n x)/(lowerP0*(1-lowerP0))
/-- Subtracting the two constructed arm means cancels all shared signs. -/
-- @node: lowerMean_effect_identity
lemma lowerMean_effect_identity (ε : Bool) (v : Signs κ n) (x : unitInterval) :
    lowerMean κ n ε v true x - lowerMean κ n ε v false x = lowerEffect κ n ε x := by
  simp only [lowerMean, lowerEffect, lowerP0, Bool.false_eq_true, ↓reduceIte]
  ring

/-- The three outcome atoms retain the rare-mark weights. -/
def lowerOutcomeMeasure (ε : Bool) (v : Signs κ n) (z : Bool) (x : unitInterval) : Measure ℝ :=
  ENNReal.ofReal (lowerRare κ n / 2 + lowerMean κ n ε v z x/(2*lowerAmplitude κ n)) • Measure.dirac (lowerAmplitude κ n) +
  ENNReal.ofReal (lowerRare κ n / 2 - lowerMean κ n ε v z x/(2*lowerAmplitude κ n)) • Measure.dirac (-lowerAmplitude κ n) +
  ENNReal.ofReal (1-lowerRare κ n) • Measure.dirac 0
/-- Each piece of the explicit trigonometric frame is Borel. -/
-- @node: measurable_frame
@[fun_prop] lemma measurable_frame (j : Fin (signCount κ n)) : Measurable (frame κ n j) := by
  unfold frame
  dsimp only
  have hu : Measurable (fun x : unitInterval => (x : ℝ)/lowerEll κ n - (j.val : ℝ)) := by
    fun_prop
  apply Measurable.ite
    ((measurableSet_le measurable_const hu).inter (measurableSet_le hu measurable_const))
  · fun_prop
  · apply Measurable.ite
      ((measurableSet_le measurable_const hu).inter (measurableSet_lt hu measurable_const))
    · fun_prop
    · fun_prop

/-- The two trigonometric pieces are one cosine clipped at the support boundary. -/
-- @node: frame_eq_clipped_cos
lemma frame_eq_clipped_cos (j : Fin (signCount κ n)) (x : unitInterval) :
    frame κ n j x =
      Real.cos (Real.pi * min |(x : ℝ)/lowerEll κ n - (j.val : ℝ)| 1 / 2) := by
  let u := (x : ℝ)/lowerEll κ n - (j.val : ℝ)
  change (if 0 ≤ u ∧ u ≤ 1 then Real.cos (Real.pi*u/2)
    else if -1 ≤ u ∧ u < 0 then Real.sin (Real.pi*(u+1)/2) else 0) =
      Real.cos (Real.pi * min |u| 1 / 2)
  by_cases hp : 0 ≤ u ∧ u ≤ 1
  · simp [hp, abs_of_nonneg hp.1, min_eq_left hp.2]
  · by_cases hn : -1 ≤ u ∧ u < 0
    · rw [if_neg hp, if_pos hn, abs_of_neg hn.2,
        min_eq_left (by linarith : -u ≤ 1)]
      rw [show Real.pi*(u+1)/2 = Real.pi*u/2 + Real.pi/2 by ring,
        Real.sin_add_pi_div_two]
      rw [show Real.pi * -u / 2 = -(Real.pi*u/2) by ring, Real.cos_neg]
    · have hu : 1 ≤ |u| := by
        by_cases hzero : 0 ≤ u
        · rw [abs_of_nonneg hzero]
          have hgt : ¬ u ≤ 1 := fun h => hp ⟨hzero, h⟩
          linarith
        · rw [abs_of_neg (lt_of_not_ge hzero)]
          have hlt : ¬ -1 ≤ u := fun h => hn ⟨h, lt_of_not_ge hzero⟩
          linarith
      simp [hp, hn, min_eq_right hu, Real.cos_pi_div_two]

/-- Each frame coordinate is continuous, including at the three gluing points. -/
-- @node: continuous_frame
@[fun_prop] lemma continuous_frame (j : Fin (signCount κ n)) :
    Continuous (frame κ n j) := by
  have he : frame κ n j = fun x : unitInterval =>
      Real.cos (Real.pi * min |(x : ℝ)/lowerEll κ n - (j.val : ℝ)| 1 / 2) := by
    funext x
    exact frame_eq_clipped_cos κ n j x
  rw [he]
  fun_prop

/-- A nonzero coordinate lies strictly inside its two-cell support. -/
-- @node: frame_active_distance
lemma frame_active_distance (j : Fin (signCount κ n)) (x : unitInterval)
    (hj : frame κ n j x ≠ 0) :
    |(x : ℝ)/lowerEll κ n - (j.val : ℝ)| < 1 := by
  by_contra h
  have hz : frame κ n j x = 0 := by
    rw [frame_eq_clipped_cos, min_eq_right (le_of_not_gt h)]
    simp only [mul_one, Real.cos_pi_div_two]
  exact hj hz

/-- Only the floor of the grid location and its successor can be active. -/
-- @node: frame_active_indices
lemma frame_active_indices (j : Fin (signCount κ n)) (x : unitInterval)
    (hj : frame κ n j x ≠ 0) :
    (j.val : ℤ) = ⌊(x : ℝ)/lowerEll κ n⌋ ∨
      (j.val : ℤ) = ⌊(x : ℝ)/lowerEll κ n⌋ + 1 := by
  obtain ⟨hl, hu⟩ := abs_lt.mp (frame_active_distance κ n j x hj)
  have hf := Int.floor_le ((x : ℝ)/lowerEll κ n)
  have hg := Int.lt_floor_add_one ((x : ℝ)/lowerEll κ n)
  have ha : (⌊(x : ℝ)/lowerEll κ n⌋ : ℝ) - 1 < (j.val : ℝ) := by linarith
  have hb : (j.val : ℝ) < (⌊(x : ℝ)/lowerEll κ n⌋ : ℝ) + 2 := by linarith
  have hai : ⌊(x : ℝ)/lowerEll κ n⌋ - 1 < (j.val : ℤ) := by exact_mod_cast ha
  have hbi : (j.val : ℤ) < ⌊(x : ℝ)/lowerEll κ n⌋ + 2 := by exact_mod_cast hb
  omega

/-- Mapping active coordinates injectively to the two possible grid integers bounds their count. -/
-- @node: frame_active_card
lemma frame_active_card (x : unitInterval) :
    (Finset.univ.filter (fun j => frame κ n j x ≠ 0)).card ≤ 2 := by
  let S := Finset.univ.filter (fun j => frame κ n j x ≠ 0)
  have hinj : Function.Injective (fun j : Fin (signCount κ n) => (j.val : ℤ)) := by
    intro i j hij
    apply Fin.ext
    dsimp only at hij
    exact_mod_cast hij
  have hsub : S.image (fun j => (j.val : ℤ)) ⊆
      {⌊(x : ℝ)/lowerEll κ n⌋, ⌊(x : ℝ)/lowerEll κ n⌋ + 1} := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hj' := (Finset.mem_filter.mp hj).2
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      frame_active_indices κ n j x hj'
  calc
    S.card = (S.image (fun j => (j.val : ℤ))).card :=
      (Finset.card_image_of_injective S hinj).symm
    _ ≤ ({⌊(x : ℝ)/lowerEll κ n⌋, ⌊(x : ℝ)/lowerEll κ n⌋ + 1} : Finset ℤ).card :=
      Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

/-- Positive sample size makes the public grid spacing strictly positive. -/
-- @node: lowerEll_pos
lemma lowerEll_pos (hn : 0 < n) : 0 < lowerEll κ n := by
  unfold lowerEll lowerC
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  positivity

/-- The two active grid indices also have a natural-number description on the design interval. -/
-- @node: frame_active_indices_nat
lemma frame_active_indices_nat (hn : 0 < n) (j : Fin (signCount κ n)) (x : unitInterval)
    (hj : frame κ n j x ≠ 0) :
    j.val = ⌊(x : ℝ)/lowerEll κ n⌋₊ ∨ j.val = ⌊(x : ℝ)/lowerEll κ n⌋₊ + 1 := by
  have ht : 0 ≤ (x : ℝ)/lowerEll κ n := div_nonneg x.2.1 (lowerEll_pos κ n hn).le
  obtain ⟨hl, hu⟩ := abs_lt.mp (frame_active_distance κ n j x hj)
  have hf := Nat.floor_le ht
  have hg := Nat.lt_floor_add_one ((x : ℝ)/lowerEll κ n)
  have ha : (⌊(x : ℝ)/lowerEll κ n⌋₊ : ℝ) < (j.val : ℝ) + 1 := by linarith
  have hb : (j.val : ℝ) < (⌊(x : ℝ)/lowerEll κ n⌋₊ : ℝ) + 2 := by linarith
  have hai : ⌊(x : ℝ)/lowerEll κ n⌋₊ < j.val + 1 := by exact_mod_cast ha
  have hbi : j.val < ⌊(x : ℝ)/lowerEll κ n⌋₊ + 2 := by exact_mod_cast hb
  omega

/-- On each grid interval, the two nonzero frame squares are cosine squared and sine squared. -/
-- @node: frame_square_partition
lemma frame_square_partition (hn : 0 < n) (x : unitInterval) :
    (∑ j, (frame κ n j x)^2) = 1 := by
  let t : ℝ := (x : ℝ)/lowerEll κ n
  let k : ℕ := ⌊t⌋₊
  have he := lowerEll_pos κ n hn
  have ht : 0 ≤ t := div_nonneg x.2.1 he.le
  have hklo : (k : ℝ) ≤ t := Nat.floor_le ht
  have hkhi : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
  have htx : t ≤ 1/lowerEll κ n := (div_le_div_iff_of_pos_right he).mpr x.2.2
  have hkbound : k ≤ ⌈1/lowerEll κ n⌉₊ := by
    have h := hklo.trans (htx.trans (Nat.le_ceil _))
    exact_mod_cast h
  let i : Fin (signCount κ n) := ⟨k, by unfold signCount; omega⟩
  have hi : frame κ n i x = Real.cos (Real.pi*(t-(k : ℝ))/2) := by
    unfold frame
    dsimp only
    rw [if_pos (show 0 ≤ t - (k : ℝ) ∧ t - (k : ℝ) ≤ 1 by constructor <;> linarith)]
  by_cases htk : t = (k : ℝ)
  · rw [Finset.sum_eq_single i]
    · rw [hi, htk]
      norm_num
    · intro j _ hji
      have hz : frame κ n j x = 0 := by
        by_contra hj
        obtain hjk | hjk := frame_active_indices_nat κ n hn j x hj
        · exact hji (Fin.ext hjk)
        · have hu : (x : ℝ)/lowerEll κ n - (j.val : ℝ) = -1 := by
            change t - (j.val : ℝ) = -1
            rw [hjk, Nat.cast_add, Nat.cast_one, htk]
            ring
          apply hj
          rw [frame_eq_clipped_cos, hu]
          norm_num
      simp only [hz, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    · simp
  · have hkt : (k : ℝ) < t := lt_of_le_of_ne hklo (Ne.symm htk)
    have hkb : k < ⌈1/lowerEll κ n⌉₊ := Nat.lt_ceil.mpr (hkt.trans_le htx)
    let i' : Fin (signCount κ n) := ⟨k+1, by unfold signCount; omega⟩
    have hii : i ≠ i' := by intro h; have hv := congrArg Fin.val h; dsimp [i, i'] at hv; omega
    have hi' : frame κ n i' x = Real.sin (Real.pi*(t-(k : ℝ))/2) := by
      have hu : (x : ℝ)/lowerEll κ n - (i'.val : ℝ) = t - (k : ℝ) - 1 := by
        dsimp [i', t]
        push_cast
        ring
      unfold frame
      dsimp only
      rw [hu, if_neg (by intro h; linarith : ¬ (0 ≤ t-(k : ℝ)-1 ∧ t-(k : ℝ)-1 ≤ 1)),
        if_pos (show -1 ≤ t-(k : ℝ)-1 ∧ t-(k : ℝ)-1 < 0 by constructor <;> linarith)]
      congr 2
      ring
    have hsum : (∑ j, (frame κ n j x)^2) = ∑ j ∈ ({i, i'} : Finset _), (frame κ n j x)^2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hz : frame κ n j x = 0 := by
        by_contra hne
        obtain hk | hk := frame_active_indices_nat κ n hn j x hne
        · exact hj (Finset.mem_insert.mpr (Or.inl (Fin.ext hk)))
        · exact hj (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Fin.ext hk))))
      simp [hz]
    rw [hsum]
    simp only [Finset.sum_pair hii, hi, hi']
    simpa only [add_comm] using Real.sin_sq_add_cos_sq (Real.pi*(t-(k : ℝ))/2)

/-- A frame sign shared by two locations has support diameter at most two grid spacings. -/
-- @node: frame_support_diameter
lemma frame_support_diameter (hn : 0 < n) (j : Fin (signCount κ n))
    (x z : unitInterval) (hx : frame κ n j x ≠ 0) (hz : frame κ n j z ≠ 0) :
    |(x : ℝ) - (z : ℝ)| ≤ 2 * lowerEll κ n := by
  have he := lowerEll_pos κ n hn
  obtain ⟨hxlo, hxhi⟩ := abs_lt.mp (frame_active_distance κ n j x hx)
  obtain ⟨hzlo, hzhi⟩ := abs_lt.mp (frame_active_distance κ n j z hz)
  have hlo : -2 < (x : ℝ)/lowerEll κ n - (z : ℝ)/lowerEll κ n := by linarith
  have hhi : (x : ℝ)/lowerEll κ n - (z : ℝ)/lowerEll κ n < 2 := by linarith
  rw [← sub_div] at hlo hhi
  have hlo' := (lt_div_iff₀ he).mp hlo
  have hhi' := (div_lt_iff₀ he).mp hhi
  apply abs_le.mpr
  constructor <;> linarith

/-- The three-atom conditional measure family is Borel. -/
-- @node: measurable_lowerOutcomeMeasure
@[fun_prop] lemma measurable_lowerOutcomeMeasure (ε : Bool) (v : Signs κ n) (z : Bool) :
  Measurable (lowerOutcomeMeasure κ n ε v z) := by
  have hc : Measurable (lowerCutoff κ n) := by
    apply Continuous.measurable
    unfold lowerCutoff
    fun_prop
  unfold lowerOutcomeMeasure lowerMean lowerField lowerSquare
  cases z <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
/-- The explicit three-atom Borel outcome kernel. -/
def lowerOutcomeKernel (ε : Bool) (v : Signs κ n) (z : Bool) : Kernel unitInterval ℝ :=
  ⟨lowerOutcomeMeasure κ n ε v z, measurable_lowerOutcomeMeasure κ n ε v z⟩
/-- The concrete lower construction has a Borel propensity. -/
-- @node: measurable_lowerPropensity
@[fun_prop] lemma measurable_lowerPropensity (v : Signs κ n) : Measurable (lowerPropensity κ n v) := by
  unfold lowerPropensity lowerField lowerCutoff
  fun_prop
/-- The public spacing and perturbations are positive and uniformly small. -/
-- @node: lower_scale_small
lemma lower_scale_small (hκ : κ.Valid) (hn : 2 ≤ n) :
    (0 < lowerEll κ n ∧ lowerEll κ n ≤ 1) ∧
    (0 < lowerA κ n ∧ lowerA κ n ≤ 1/1024) ∧
    (0 < lowerB κ n ∧ lowerB κ n ≤ 1/1024) := by
  have hp : 0 < κ.p := by linarith [hκ.1.1]
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hκ.1.1) hp
  have ha := hκ.2.1.1
  have hb := hκ.2.2.1.1
  have hg := hκ.2.2.2.1
  have hd : 0 < lowerDenom κ := by unfold lowerDenom sumReg; positivity
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have he := lowerEll_pos κ n (by omega)
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hn1
    (show -2/lowerDenom κ ≤ 0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) hd.le)
  have hc : lowerC κ ≤ 1/1000 := min_le_left _ _
  have hcpos : 0 ≤ lowerC κ := by unfold lowerC; positivity
  have hel : lowerEll κ n ≤ 1 := by
    unfold lowerEll
    have h := mul_le_mul_of_nonneg_left hpow hcpos
    nlinarith
  have hpa := Real.rpow_le_one he.le hel ha.le
  have hpb := Real.rpow_le_one he.le hel hb.le
  refine ⟨⟨he, hel⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · unfold lowerA; positivity
  · unfold lowerA; linarith
  · unfold lowerB; positivity
  · unfold lowerB; linarith

/-- The localized shared-sign field is bounded using its two active coordinates. -/
-- @node: lower_field_abs_le_two
lemma lower_field_abs_le_two (v : Signs κ n) (x : unitInterval) :
    |lowerField κ n v x| ≤ 2 := by
  have hk : |lowerCutoff κ n x| ≤ 1 := by
    have hh : 0 ≤ lowerH κ n := by unfold lowerH lowerEll lowerC; positivity
    have hz : 0 ≤ |(x : ℝ)-1/2|/lowerH κ n := div_nonneg (abs_nonneg _) hh
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le (by norm_num) (by linarith)
  let S := Finset.univ.filter (fun j => frame κ n j x ≠ 0)
  have hsum : (∑ j, sign (v j)*frame κ n j x) = ∑ j ∈ S, sign (v j)*frame κ n j x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hz : frame κ n j x = 0 := by simpa [S] using hj
    simp [hz]
  have hterm (j : Fin (signCount κ n)) : |sign (v j)*frame κ n j x| ≤ 1 := by
    rw [abs_mul, frame_eq_clipped_cos]
    have hs : |sign (v j)| = 1 := by cases v j <;> norm_num [sign]
    rw [hs, one_mul]
    exact Real.abs_cos_le_one _
  have hcard : (S.card : ℝ) ≤ 2 := by exact_mod_cast frame_active_card κ n x
  have hbound : |∑ j, sign (v j)*frame κ n j x| ≤ 2 := by
    rw [hsum]
    calc
      _ ≤ ∑ j ∈ S, |sign (v j)*frame κ n j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = (S.card : ℝ) := by simp
      _ ≤ 2 := hcard
  rw [lowerField, abs_mul]
  exact (mul_le_mul hk hbound (abs_nonneg _) (by norm_num)).trans (by norm_num)

/-- Rare-mark probability is at most one and its first absolute moment is four times b. -/
-- @node: lower_rare_scale
lemma lower_rare_scale (hκ : κ.Valid) (hn : 2 ≤ n) :
    0 < lowerAmplitude κ n ∧ lowerRare κ n ≤ 1 ∧
    lowerRare κ n * lowerAmplitude κ n = 4*lowerB κ n := by
  have hb := (lower_scale_small κ n hκ hn).2.2
  have hp1 : 0 < κ.p-1 := sub_pos.mpr hκ.1.1
  have hexp : -1/(κ.p-1) ≤ (-1 : ℝ) := by
    apply (div_le_iff₀ hp1).mpr
    linarith [hκ.1.2]
  have hbp := hb.1
  have hBpos : 0 < lowerAmplitude κ n := by unfold lowerAmplitude; positivity
  have hBge : 1024 ≤ lowerAmplitude κ n := by
    have h := Real.rpow_le_rpow_of_exponent_ge hb.1 (by linarith : lowerB κ n ≤ 1) hexp
    rw [Real.rpow_neg_one] at h
    have hinv : (1024 : ℝ) ≤ (lowerB κ n)⁻¹ := by
      have hi := one_div_le_one_div_of_le hb.1 hb.2
      norm_num at hi
      simpa [one_div] using hi
    exact hinv.trans h
  have hrle : lowerRare κ n ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ lowerAmplitude κ n by linarith)
      (show -κ.p ≤ (-1 : ℝ) by linarith [hκ.1.1])
    rw [Real.rpow_neg_one] at h
    have hi : (lowerAmplitude κ n)⁻¹ ≤ 1/1024 := by
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1024) hBge
    unfold lowerRare
    linarith
  refine ⟨hBpos, hrle, ?_⟩
  unfold lowerRare
  conv_lhs => arg 2; rw [← Real.rpow_one (lowerAmplitude κ n)]
  rw [mul_assoc, ← Real.rpow_add hBpos]
  unfold lowerAmplitude
  rw [← Real.rpow_mul hb.1.le]
  have hid : -1/(κ.p-1)*(-κ.p+1) = 1 := by field_simp; ring
  rw [hid, Real.rpow_one]

/-- The three atom weights are nonnegative throughout the lower construction. -/
-- @node: lower_atom_weights_nonneg
lemma lower_atom_weights_nonneg (hκ : κ.Valid) (hn : 2 ≤ n)
    (ε : Bool) (v : Signs κ n) (z : Bool) (x : unitInterval) :
    0 ≤ lowerRare κ n/2 + lowerMean κ n ε v z x/(2*lowerAmplitude κ n) ∧
    0 ≤ lowerRare κ n/2 - lowerMean κ n ε v z x/(2*lowerAmplitude κ n) ∧
    0 ≤ 1-lowerRare κ n := by
  have hs := lower_scale_small κ n hκ hn
  obtain ⟨hB, hr, hid⟩ := lower_rare_scale κ n hκ hn
  have hf := lower_field_abs_le_two κ n v x
  have hk : 0 ≤ lowerCutoff κ n x ∧ lowerCutoff κ n x ≤ 1 := by
    have hh : 0 ≤ lowerH κ n := by unfold lowerH lowerEll lowerC; positivity
    have hz := div_nonneg (abs_nonneg ((x : ℝ)-1/2)) hh
    exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith)⟩
  have hk2 : |lowerSquare κ n x| ≤ 1 := by
    unfold lowerSquare
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have he : |sign ε| = 1 := by cases ε <;> norm_num [sign]
  have hm : |lowerMean κ n ε v z x| ≤ 4*lowerB κ n := by
    have ht : |sign ε*lowerB κ n*lowerField κ n v x| ≤ 2*lowerB κ n := by
      simpa [abs_mul, he, abs_of_pos hs.2.2.1, mul_comm] using
        mul_le_mul_of_nonneg_left hf hs.2.2.1.le
    have hu : |sign ε*lowerA κ n*lowerB κ n*lowerSquare κ n x| ≤ lowerA κ n*lowerB κ n := by
      simpa [abs_mul, he, abs_of_pos hs.2.1.1, abs_of_pos hs.2.2.1] using
        mul_le_mul_of_nonneg_left hk2 (mul_nonneg hs.2.1.1.le hs.2.2.1.le)
    have hab : lowerA κ n*lowerB κ n ≤ lowerB κ n/1024 := by
      nlinarith [mul_le_mul_of_nonneg_right hs.2.1.2 hs.2.2.1.le]
    unfold lowerMean
    cases z <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · have h := abs_add_le (sign ε*lowerB κ n*lowerField κ n v x)
        (sign ε*lowerA κ n*lowerB κ n*lowerSquare κ n x/(1-lowerP0))
      rw [abs_div] at h
      simp only [lowerP0, abs_of_pos (by norm_num : (0 : ℝ) < 3/8),
        show (1 : ℝ)-3/8 = 5/8 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 5/8)] at h ⊢
      nlinarith
    · have h := abs_add_le (sign ε*lowerB κ n*lowerField κ n v x)
        (-(sign ε*lowerA κ n*lowerB κ n*lowerSquare κ n x)/lowerP0)
      rw [abs_div, abs_neg] at h
      simp only [lowerP0, abs_of_pos (by norm_num : (0 : ℝ) < 3/8),
        show (1 : ℝ)-3/8 = 5/8 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 5/8)] at h ⊢
      nlinarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hm
  have hden : 0 < 2*lowerAmplitude κ n := by positivity
  have hlow : -(lowerRare κ n/2) ≤ lowerMean κ n ε v z x/(2*lowerAmplitude κ n) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [hid]
  have hhigh : lowerMean κ n ε v z x/(2*lowerAmplitude κ n) ≤ lowerRare κ n/2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [hid]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- On the lower-bound domain the original-law construction is normalized and has the stated means. -/
-- @node: lower_law_versions
lemma lower_law_versions (hd : κ.Valid ∧ boundary κ ≤ 1 ∧ 2 ≤ n) (ε : Bool) (v : Signs κ n) :
  (∀ x, 0 ≤ lowerPropensity κ n v x ∧ lowerPropensity κ n v x ≤ 1) ∧
  (∀ z, IsMarkovKernel (lowerOutcomeKernel κ n ε v z)) ∧
  (∀ᵐ x ∂design, lowerMean κ n ε v false x = ∫ y, y ∂lowerOutcomeKernel κ n ε v false x) ∧
  (∀ᵐ x ∂design, lowerMean κ n ε v false x + lowerEffect κ n ε x = ∫ y, y ∂lowerOutcomeKernel κ n ε v true x) := by
  have hs := lower_scale_small κ n hd.1 hd.2.2
  have hB := (lower_rare_scale κ n hd.1 hd.2.2).1
  have hmean (z : Bool) (x : unitInterval) :
      lowerMean κ n ε v z x = ∫ y, y ∂lowerOutcomeKernel κ n ε v z x := by
    obtain ⟨hw1, hw2, hw3⟩ := lower_atom_weights_nonneg κ n hd.1 hd.2.2 ε v z x
    have hi (a w : ℝ) : Integrable (fun y : ℝ => y) (ENNReal.ofReal w • Measure.dirac a) := by
      first | fun_prop | exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    change lowerMean κ n ε v z x = ∫ y, y ∂lowerOutcomeMeasure κ n ε v z x
    unfold lowerOutcomeMeasure
    rw [integral_add_measure ((hi _ _).add_measure (hi _ _)) (hi _ _),
      integral_add_measure (hi _ _) (hi _ _)]
    simp only [integral_smul_measure, integral_dirac, smul_eq_mul, mul_zero, add_zero,
      ENNReal.toReal_ofReal hw1, ENNReal.toReal_ofReal hw2]
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    have hf := lower_field_abs_le_two κ n v x
    obtain ⟨hlo, hhi⟩ := abs_le.mp hf
    unfold lowerPropensity lowerP0
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hhi hs.2.1.1.le,
      mul_le_mul_of_nonneg_left hlo hs.2.1.1.le]
  · intro z
    constructor
    intro x
    constructor
    obtain ⟨hw1, hw2, hw3⟩ := lower_atom_weights_nonneg κ n hd.1 hd.2.2 ε v z x
    change lowerOutcomeMeasure κ n ε v z x univ = 1
    simp only [lowerOutcomeMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hw1 hw2,
      ← ENNReal.ofReal_add (add_nonneg hw1 hw2) hw3]
    convert ENNReal.ofReal_one using 1 <;> congr 1 <;> ring
  · exact Filter.Eventually.of_forall (hmean false)
  · filter_upwards [] with x
    rw [← hmean true, ← lowerMean_effect_identity κ n ε v x]
    ring
/-- The exact-uniform original-law rare-mark construction, extended by a fixed law off-domain. -/
def lowerPriorLaw (ε : Bool) (v : Signs κ n) : ObservedLaw :=
  if hd : κ.Valid ∧ boundary κ ≤ 1 ∧ 2 ≤ n then
    lawFromUniform (lowerPropensity κ n v) (measurable_lowerPropensity κ n v)
      (lower_law_versions κ n hd ε v).1 (lowerOutcomeKernel κ n ε v)
      (lower_law_versions κ n hd ε v).2.1 (lowerMean κ n ε v false) (lowerEffect κ n ε)
      (lower_law_versions κ n hd ε v).2.2.1 (lower_law_versions κ n hd ε v).2.2.2
  else referenceLaw
/-- Finite uniform mixture of the n-record original experiment laws. -/
def lowerMixture (ε : Bool) : Measure (Dataset n) :=
  (Fintype.card (Signs κ n) : ℝ≥0∞)⁻¹ •
    ∑ v : Signs κ n, Measure.pi (fun _ : Fin n => (lowerPriorLaw κ n ε v).P)
/-- Computable interaction lower constant. -/
def cInter : ℝ := (3/16) * 2 * lowerC κ ^ sumReg κ / ((1024 : ℝ)^2 * lowerP0 * (1-lowerP0))
/-- The squared partition has exactly two or fewer active coordinates at every point. -/
-- @node: lower_frame_geometry
lemma lower_frame_geometry (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n) :
  (∀ x, (∑ j, (frame κ n j x)^2) = 1) ∧
  (∀ x, (Finset.univ.filter (fun j => frame κ n j x ≠ 0)).card ≤ 2) ∧
  (∀ j, Continuous (frame κ n j)) := by
  exact ⟨frame_square_partition κ n (by omega), frame_active_card κ n, continuous_frame κ n⟩
/-- A spacing, macro radius, perturbation scales, rare-mark amplitude and probability, base
propensity, finite continuous frame, localization profile and shared-sign original laws. -/
abbrev LowerProgram := Σ m : ℕ, ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ×
  (Fin m → unitInterval → ℝ) × (unitInterval → ℝ) × (Bool → (Fin m → Bool) → ObservedLaw)
/-- A finite uniform prior's original-record mixture. -/
def signProgramMixture {m : ℕ} (laws : (Fin m → Bool) → ObservedLaw) (n : ℕ) : Measure (Dataset n) :=
  (Fintype.card (Fin m → Bool) : ℝ≥0∞)⁻¹ • ∑ v, Measure.pi (fun _ : Fin n => (laws v).P)
/-- The programme certificate retains the continuous squared frame, shared signs,
three rare-mark atoms and exact means, singleton cancellation, deterministic smooth effects,
original-law membership, optimized separation and original-record testing bound. -/
def LowerProgramCertificate (c : ℝ) (program : LowerProgram) : Prop :=
  κ.Valid ∧ boundary κ ≤ 1 ∧ 2 ≤ n →
  let ⟨m, ell, h, a, b, B, r, p0, ψ, k, laws⟩ := program
  let F := fun (v : Fin m → Bool) x => k x * ∑ j, sign (v j)*ψ j x
  let effect := fun ε x => -(sign ε*a*b*(k x)^2)/(p0*(1-p0))
  0 < ell ∧ ell ≤ 1 ∧ h = ell^(sumReg κ/κ.γ) ∧ 0 < a ∧ 0 < b ∧ 1 ≤ B ∧
  p0 = 3/8 ∧ 0 < p0 ∧ p0 < 1 ∧ r = 4*B^(-κ.p) ∧ r ≤ 1 ∧
  (∀ j, Continuous (ψ j)) ∧ (∀ x, (∑ j, (ψ j x)^2) = 1) ∧
  (∀ x, (Finset.univ.filter (fun j => ψ j x ≠ 0)).card ≤ 2) ∧
  (∀ j x z, ψ j x ≠ 0 → ψ j z ≠ 0 → |(x : ℝ)-(z : ℝ)| ≤ 2*ell) ∧
  (∀ x, k x = max 0 (1-|(x : ℝ)-1/2|/h)) ∧
  (∀ ε v, InModel κ (laws ε v) ∧ UniformDesign (laws ε v) ∧
    (laws ε v).e = (fun x => p0+a*F v x) ∧
    (laws ε v).m0 = (fun x => sign ε*b*F v x+(sign ε*a*b*(k x)^2)/(1-p0)) ∧
    (laws ε v).tau = effect ε ∧ holderBall κ.γ (effect ε) ∧
    ∀ z x, (laws ε v).Q z x =
      ENNReal.ofReal (r/2+(if z then (laws ε v).m1 x else (laws ε v).m0 x)/(2*B)) • Measure.dirac B +
      ENNReal.ofReal (r/2-(if z then (laws ε v).m1 x else (laws ε v).m0 x)/(2*B)) • Measure.dirac (-B) +
      ENNReal.ofReal (1-r) • Measure.dirac 0) ∧
  ((Fintype.card (Fin m → Bool) : ℝ≥0∞)⁻¹ • ∑ v, (laws true v).P =
    (Fintype.card (Fin m → Bool) : ℝ≥0∞)⁻¹ • ∑ v, (laws false v).P) ∧
  c*(n : ℝ)^(-rInter κ) ≤ |effect true xstar-effect false xstar| ∧
  Causalean.Stat.tvDist (signProgramMixture (laws true) n) (signProgramMixture (laws false) n) ≤ 1/4

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
