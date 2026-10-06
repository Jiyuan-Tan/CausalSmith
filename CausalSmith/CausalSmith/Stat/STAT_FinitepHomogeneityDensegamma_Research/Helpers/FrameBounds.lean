module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CopulaPriors
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Finite-moment homogeneity testing: Helpers/FrameBounds. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- The triangular bump takes values between zero and one. [This is the stated conclusion](goal). -/
-- @node: tentBase_range
lemma tentBase_range (t : ℝ) : 0 ≤ tentBase t ∧ tentBase t ≤ 1 := by
  unfold tentBase
  split
  · rename_i ht
    constructor
    · exact mul_nonneg (by norm_num) (le_min ht.1 (by linarith [ht.2]))
    · have h1 := min_le_left t (1-t)
      have h2 := min_le_right t (1-t)
      linarith
  · norm_num

/-- A nonzero triangular bump lies strictly inside its support. This statement assumes [the ht condition](hyp:ht). [This is the stated conclusion](goal). -/
-- @node: tentBase_ne_zero_support
lemma tentBase_ne_zero_support (t : ℝ) (ht : tentBase t ≠ 0) : 0 < t ∧ t < 1 := by
  unfold tentBase at ht
  split at ht
  · rename_i h
    constructor
    · by_contra hn
      have : t = 0 := by linarith [h.1]
      simp [this] at ht
    · by_contra hn
      have : t = 1 := by linarith [h.2]
      simp [this] at ht
  · exact (ht rfl).elim

/-- At most one paired coarse bump is nonzero at any position. This statement assumes [the hj condition](hyp:hj). [This is the stated conclusion](goal). -/
-- @node: coarseTent_pair_support
lemma coarseTent_pair_support (M : ℕ) (x : ℝ) (j : Fin (M/2))
    (hj : tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*x-(2*j.val+1)) ≠ 0) :
    2*(j.val:ℝ) < (M:ℝ)*x ∧ (M:ℝ)*x < 2*(j.val:ℝ)+2 := by
  by_cases h0 : tentBase ((M:ℝ)*x-2*j.val) = 0
  · have h1 : tentBase ((M:ℝ)*x-(2*j.val+1)) ≠ 0 := by
      intro h1; simp [h0, h1] at hj
    have hs := tentBase_ne_zero_support _ h1
    constructor <;> linarith
  · have hs := tentBase_ne_zero_support _ h0
    constructor <;> linarith

/-- Fair coarse signs preserve the unit envelope of the disjoint paired tents. [This is the stated conclusion](goal). -/
-- @node: coarseTent_abs_le_one
lemma coarseTent_abs_le_one (M : ℕ) (σ : Fin (M/2) → Bool) (x : ℝ) :
    |coarseTent M σ x| ≤ 1 := by
  classical
  let f := fun j : Fin (M/2) =>
    tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*x-(2*j.val+1))
  by_cases hn : ∃ j, f j ≠ 0
  · obtain ⟨j, hj⟩ := hn
    have hs := coarseTent_pair_support M x j hj
    have hz : ∀ k : Fin (M/2), k ≠ j → f k = 0 := by
      intro k hkj
      by_contra hk
      have ht := coarseTent_pair_support M x k hk
      have he : k.val = j.val := by
        have h1 : (k.val:ℝ) < j.val+1 := by linarith
        have h2 : (j.val:ℝ) < k.val+1 := by linarith
        have h1' : k.val < j.val+1 := by exact_mod_cast h1
        have h2' : j.val < k.val+1 := by exact_mod_cast h2
        omega
      exact hkj (Fin.ext he)
    have he : coarseTent M σ x = signVal (σ j)*f j := by
      unfold coarseTent
      apply Finset.sum_eq_single j
      · intro k _ hk
        change signVal (σ k)*f k = 0
        rw [hz k hk, mul_zero]
      · simp
    rw [he, abs_mul]
    have hsign : |signVal (σ j)| = 1 := by cases σ j <;> norm_num [signVal]
    rw [hsign, one_mul]
    have h0 := tentBase_range ((M:ℝ)*x-2*j.val)
    have h1 := tentBase_range ((M:ℝ)*x-(2*j.val+1))
    exact abs_le.mpr ⟨by dsimp [f]; linarith, by dsimp [f]; linarith⟩
  · have hz : ∀ j, f j = 0 := by simpa using hn
    have he : coarseTent M σ x = 0 := by
      unfold coarseTent
      apply Finset.sum_eq_zero
      intro j _
      change signVal (σ j)*f j = 0
      rw [hz j, mul_zero]
    rw [he]
    norm_num

/-- The unit coordinate envelope and overlap give a coarse uniform field bound. This statement assumes [the hK condition](hyp:hK), [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: frameField_abs_le_two
lemma frameField_abs_le_two (K : ℕ) (hK : 0 < K) (coef : Fin (K+1) → ℝ)
    (hc : ∀ i, |coef i| ≤ 1) (x : unitInterval) : |frameField K coef x| ≤ 2 := by
  let S := Finset.univ.filter (fun i : Fin (K+1) => frameCoord K i x ≠ 0)
  have he : frameField K coef x = ∑ i ∈ S, coef i*frameCoord K i x := by
    unfold frameField
    apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro i _ hi
    have hz : frameCoord K i x = 0 := by simpa [S] using hi
    simp [hz]
  have hcoord (i : Fin (K+1)) : |frameCoord K i x| ≤ 1 := by
    unfold frameCoord
    split
    · exact Real.abs_cos_le_one _
    · split
      · exact Real.abs_sin_le_one _
      · norm_num
  rw [he]
  calc
    _ ≤ ∑ i ∈ S, |coef i*frameCoord K i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul (hc i) (hcoord i) (abs_nonneg _) (by norm_num)).trans (by norm_num)
    _ = (S.card:ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast frame_overlap K hK x

/-- Squared-frame interpolation preserves the coarse tent envelope. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_abs_le_one
lemma smoothedTent_abs_le_one (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M/2) → Bool) (x : unitInterval) : |smoothedTent K M σ x| ≤ 1 := by
  unfold smoothedTent
  calc
    _ ≤ ∑ i : Fin (K+1), |coarseTent M σ ((i:ℝ)/K)*frameCoord K i x^2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (K+1), frameCoord K i x^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (sq_nonneg (frameCoord K i x))]
      exact mul_le_of_le_one_left (sq_nonneg _) (coarseTent_abs_le_one _ _ _)
    _ = 1 := frame_partition K hK x

/-- All copula table coordinates are continuous finite frame expressions. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: continuous_copula_coordinates
lemma continuous_copula_coordinates (K M : ℕ) (hK : 0 < K) (a u : ℝ)
    (ν : Bool) (idx : CopulaIndex K M) :
    Continuous (copulaXi K M a idx) ∧ Continuous (copulaUpsilon K M u idx) ∧
      Continuous (copulaZeta ν K M a u idx) := by
  unfold copulaZeta copulaT smoothedTent copulaXi copulaUpsilon
  have hf := continuous_frameField K hK
  have hc := continuous_frameCoord K hK
  constructor
  · fun_prop
  constructor <;> fun_prop

/-- Small amplitudes keep both main coordinates and their corrected interaction interior. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: copula_coordinates_abs_bounds
lemma copula_coordinates_abs_bounds (K M : ℕ) (hK : 0 < K) (a u : ℝ)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (ν : Bool) (idx : CopulaIndex K M) (x : unitInterval) :
    |copulaXi K M a idx x| ≤ 1/8 ∧ |copulaUpsilon K M u idx x| ≤ 1/8 ∧
      |copulaZeta ν K M a u idx x| ≤ 1/8 := by
  have hsign (b : Bool) : |signVal b| ≤ 1 := by cases b <;> norm_num [signVal]
  have hξ : |copulaXi K M a idx x| ≤ 1/8 := by
    rw [copulaXi, abs_mul, abs_of_pos ha.1]
    have hf := frameField_abs_le_two K hK (fun i => signVal (idx.2 i).1) (fun i => hsign _) x
    nlinarith
  have hυ : |copulaUpsilon K M u idx x| ≤ 1/8 := by
    rw [copulaUpsilon, abs_mul, abs_of_pos hu.1]
    have hf := frameField_abs_le_two K hK (fun i => signVal (idx.2 i).2) (fun i => hsign _) x
    nlinarith
  have ha2 : a^2 ≤ 1/256 := by nlinarith [sq_nonneg (a-1/16)]
  have hd : 0 < 1-a^2 := by linarith
  have hau : a*u ≤ 1/256 := by nlinarith
  have ht : |copulaT ν K M a u idx x| ≤ 1/128 := by
    have hg := smoothedTent_abs_le_one K M hK idx.1 x
    cases ν
    · simp [copulaT]
    · simp only [copulaT, ↓reduceIte, kappa0, neg_mul, one_mul, abs_mul,
        abs_div, abs_neg, abs_of_pos ha.1, abs_of_pos hu.1, abs_of_pos hd]
      norm_num only [abs_one, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 16)]
      have hap : 0 < a := ha.1
      have hup : 0 < u := hu.1
      have hr : a*u*(1/16)/(1-a^2) ≤ 1/128 := by
        apply (div_le_iff₀ hd).mpr
        nlinarith
      calc
        _ ≤ (a*u*(1/16)/(1-a^2))*1 := by gcongr <;> positivity
        _ ≤ 1/128 := by simpa using hr
  have hξ2 : (copulaXi K M a idx x)^2 ≤ 1/64 := by
    have hh := abs_le.mp hξ
    nlinarith
  have hrem : |1-(copulaXi K M a idx x)^2| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    nlinarith [sq_nonneg (copulaXi K M a idx x)]
  refine ⟨hξ, hυ, ?_⟩
  unfold copulaZeta
  calc
    _ ≤ |copulaXi K M a idx x*copulaUpsilon K M u idx x|+
        |copulaT ν K M a u idx x*(1-copulaXi K M a idx x^2)| := abs_add_le _ _
    _ ≤ (1/8:ℝ)*(1/8)+(1/128)*1 := by
      simp only [abs_mul]
      gcongr
    _ ≤ 1/8 := by norm_num

/-- The six literal categories are nonnegative, with continuous interior coordinates. [This is the stated conclusion](goal). -/
-- @node: copula_table_valid
lemma copula_table_valid (n K M : ℕ) (a u ε L : ℝ) (h : CopulaDomain n K M a u ε L)
    (ν : Bool) (idx : CopulaIndex K M) :
    TableValid (copulaXi K M a idx) (copulaUpsilon K M u idx) (copulaZeta ν K M a u idx) ε L := by
  rcases h with ⟨hn, hk, hm, hKM, hM, ha, hu, hε, hL⟩
  have hK : 0 < K := by omega
  obtain ⟨hcξ, hcυ, hcζ⟩ := continuous_copula_coordinates K M hK a u ν idx
  refine ⟨hcξ, hcυ, hcζ, ?_, hε, hL, ?_⟩
  · intro x
    exact (copula_coordinates_abs_bounds K M hK a u ha hu ν idx x).1.trans_lt (by norm_num)
  · intro x cat
    obtain ⟨hξ, hυ, hζ⟩ := copula_coordinates_abs_bounds K M hK a u ha hu ν idx x
    have hξ' := abs_le.mp hξ
    have hυ' := abs_le.mp hυ
    have hζ' := abs_le.mp hζ
    rcases cat with ⟨label, mark⟩
    cases mark with
    | none =>
      cases label <;> simp only [markedTable, signVal, Bool.false_eq_true, ↓reduceIte,
        one_mul, neg_one_mul] <;> apply mul_nonneg (by linarith [hε.2]) <;> linarith
    | some sign =>
      cases label <;> cases sign <;> simp only [markedTable, signVal, Bool.false_eq_true,
        ↓reduceIte, one_mul, neg_one_mul, mul_one, mul_neg_one] <;>
        apply mul_nonneg (div_nonneg hε.1.le (by norm_num)) <;> linarith

/-- Each sign-copula coefficient-pair law is nonnegative within the unit tent envelope. This statement assumes [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
-- @node: pairWeight_nonneg
lemma pairWeight_nonneg (ν : Bool) (g : ℝ) (hg : |g| ≤ 1) (l h : Bool) :
    0 ≤ pairWeight ν g l h := by
  have hr := abs_le.mp hg
  cases ν <;> cases l <;> cases h <;> simp [pairWeight, kappa0, signVal] <;> linarith

/-- Summing all four coefficient pairs cancels the sign-copula tilt. [This is the stated conclusion](goal). -/
-- @node: pairWeight_sum
lemma pairWeight_sum (ν : Bool) (g : ℝ) :
    ∑ p : Bool × Bool, pairWeight ν g p.1 p.2 = 1 := by
  simp [Fintype.sum_prod_type, pairWeight, signVal]
  ring

/-- The complete finite copula weight sums to one, including the fair coarse signs. [This is the stated conclusion](goal). -/
-- @node: copulaWeight_sum
lemma copulaWeight_sum (ν : Bool) (K M : ℕ) :
    ∑ idx : CopulaIndex K M, copulaWeight ν K M idx = 1 := by
  simp only [copulaWeight, Fintype.sum_prod_type, ← Finset.mul_sum]
  have hs (σ : Fin (M/2) → Bool) :
      (∑ pairs : Fin (K+1) → Bool × Bool,
        ∏ i : Fin (K+1), pairWeight ν (coarseTent M σ ((i:ℝ)/K)) (pairs i).1 (pairs i).2) = 1 := by
    rw [← Fintype.prod_sum (fun (i : Fin (K+1)) (p : Bool × Bool) =>
      pairWeight ν (coarseTent M σ ((i:ℝ)/K)) p.1 p.2)]
    simp_rw [pairWeight_sum]
    simp
  simp_rw [hs]
  simp [Fintype.card_bool]

/-- Copula prior normalized: the displayed mathematical construction or bound. [This is the stated conclusion](goal). -/
-- @node: copula_prior_normalized
lemma copula_prior_normalized (n K M : ℕ) (a u ε L : ℝ) (h : CopulaDomain n K M a u ε L)
    (ν : Bool) (v : Params) : PriorNormalized (copulaPrior ν v K M a u ε L) := by
  constructor
  · intro i
    change 0 ≤ copulaWeight ν K M ((Fintype.equivFin (CopulaIndex K M)).symm i)
    unfold copulaWeight
    apply mul_nonneg (by positivity)
    apply Finset.prod_nonneg
    intro j _
    exact pairWeight_nonneg _ _ (coarseTent_abs_le_one _ _ _) _ _
  · change (∑ i : Fin (Fintype.card (CopulaIndex K M)),
      copulaWeight ν K M ((Fintype.equivFin (CopulaIndex K M)).symm i)) = 1
    rw [Equiv.sum_comp]
    exact copulaWeight_sum ν K M
/-- On a closed fine cell the field contains exactly its two endpoint coordinates. This statement assumes [the hK condition](hyp:hK), [the hj condition](hyp:hj), [the hl condition](hyp:hl), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: frameField_cell_formula
lemma frameField_cell_formula (K : ℕ) (hK : 0 < K) (coef : Fin (K+1) → ℝ)
    (j : ℕ) (hj : j < K) (x : unitInterval)
    (hl : (j:ℝ) ≤ (K:ℝ)*(x:ℝ)) (hu : (K:ℝ)*(x:ℝ) ≤ (j:ℝ)+1) :
    frameField K coef x =
      coef ⟨j, by omega⟩ * Real.cos (Real.pi*((K:ℝ)*(x:ℝ)-j)/2) +
      coef ⟨j+1, by omega⟩ * Real.sin (Real.pi*((K:ℝ)*(x:ℝ)-j)/2) := by
  let i0 : Fin (K+1) := ⟨j, by omega⟩
  let i1 : Fin (K+1) := ⟨j+1, by omega⟩
  have hi : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
  have h0 : frameCoord K i0 x = Real.cos (Real.pi*((K:ℝ)*(x:ℝ)-j)/2) := by
    rw [frameCoord_eq_clipped_cos K hK i0 x]
    change Real.cos (Real.pi * min 1 |(K:ℝ)*(x:ℝ)-(j:ℝ)| / 2) = _
    rw [abs_of_nonneg (by linarith), min_eq_right (by linarith)]
  have h1 : frameCoord K i1 x = Real.sin (Real.pi*((K:ℝ)*(x:ℝ)-j)/2) := by
    rw [frameCoord_eq_clipped_cos K hK i1 x]
    change Real.cos (Real.pi * min 1 |(K:ℝ)*(x:ℝ)-((j+1:ℕ):ℝ)| / 2) = _
    rw [Nat.cast_add, Nat.cast_one, abs_of_nonpos (by linarith), min_eq_right (by linarith)]
    have he : Real.pi * -((K:ℝ)*(x:ℝ)-((j:ℝ)+1))/2 =
        Real.pi/2-Real.pi*((K:ℝ)*(x:ℝ)-j)/2 := by ring
    rw [he, Real.cos_pi_div_two_sub]
  have hz (i : Fin (K+1)) (hmem : i ∉ ({i0,i1} : Finset (Fin (K+1)))) :
      coef i*frameCoord K i x = 0 := by
    have hval : i.val ≠ j ∧ i.val ≠ j+1 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff, i0, i1] using hmem
    have hzero : frameCoord K i x = 0 := by
      by_contra hn
      have ha := abs_lt.mp (frameCoord_nonzero_distance K hK i x hn)
      have hlo : (j:ℝ) < (i:ℝ)+1 := by linarith [ha.1]
      have hup : (i:ℝ) < ((j+2:ℕ):ℝ) := by push_cast; linarith [ha.2]
      have hlo' : j < i.val+1 := by exact_mod_cast hlo
      have hup' : i.val < j+2 := by exact_mod_cast hup
      omega
    rw [hzero, mul_zero]
  unfold frameField
  rw [← Finset.sum_subset (Finset.subset_univ ({i0,i1} : Finset (Fin (K+1))))
    (fun i _ hmem => hz i hmem)]
  simp only [Finset.sum_pair hi, h0, h1]
  rfl

/-- The unit coefficient envelope and the trigonometric partition give the sharp field envelope. This statement assumes [the hK condition](hyp:hK), [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: frameField_abs_le_sqrt_two
lemma frameField_abs_le_sqrt_two (K : ℕ) (hK : 0 < K) (coef : Fin (K+1) → ℝ)
    (hc : ∀ i, |coef i| ≤ 1) (x : unitInterval) :
    |frameField K coef x| ≤ Real.sqrt 2 := by
  obtain ⟨j, hj, hl, hu⟩ := frame_cell_index K hK x
  rw [frameField_cell_formula K hK coef j hj x hl hu]
  let t := Real.pi*((K:ℝ)*(x:ℝ)-j)/2
  have he := Real.cos_sq_add_sin_sq t
  have hb : |Real.cos t|+|Real.sin t| ≤ Real.sqrt 2 := by
    have hsq := sq_nonneg (|Real.cos t|-|Real.sin t|)
    have hr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2:ℝ)
    nlinarith [sq_abs (Real.cos t), sq_abs (Real.sin t)]
  calc
    _ ≤ |coef ⟨j, by omega⟩*Real.cos t|+|coef ⟨j+1, by omega⟩*Real.sin t| := abs_add_le _ _
    _ ≤ |Real.cos t|+|Real.sin t| := by
      simp only [abs_mul]
      apply add_le_add <;> exact mul_le_of_le_one_left (abs_nonneg _) (hc _)
    _ ≤ Real.sqrt 2 := hb

/-- Within one fine cell the two trigonometric coordinates give a rank-scaled Lipschitz bound. This statement assumes [the hK condition](hyp:hK), [the hc condition](hyp:hc), [the hj condition](hyp:hj), [the hx condition](hyp:hx), [the hz condition](hyp:hz). [This is the stated conclusion](goal). -/
-- @node: frameField_cell_lipschitz
lemma frameField_cell_lipschitz (K : ℕ) (hK : 0 < K) (coef : Fin (K+1) → ℝ)
    (hc : ∀ i, |coef i| ≤ 1) (j : ℕ) (hj : j < K) (x z : unitInterval)
    (hx : (j:ℝ) ≤ (K:ℝ)*(x:ℝ) ∧ (K:ℝ)*(x:ℝ) ≤ (j:ℝ)+1)
    (hz : (j:ℝ) ≤ (K:ℝ)*(z:ℝ) ∧ (K:ℝ)*(z:ℝ) ≤ (j:ℝ)+1) :
    |frameField K coef x-frameField K coef z| ≤ Real.pi*(K:ℝ)*|(x:ℝ)-(z:ℝ)| := by
  rw [frameField_cell_formula K hK coef j hj x hx.1 hx.2,
    frameField_cell_formula K hK coef j hj z hz.1 hz.2]
  let tx := Real.pi*((K:ℝ)*(x:ℝ)-j)/2
  let tz := Real.pi*((K:ℝ)*(z:ℝ)-j)/2
  have he : |tx-tz| = Real.pi*(K:ℝ)*|(x:ℝ)-(z:ℝ)|/2 := by
    dsimp [tx, tz]
    rw [show Real.pi*((K:ℝ)*(x:ℝ)-j)/2-Real.pi*((K:ℝ)*(z:ℝ)-j)/2 =
      (Real.pi*(K:ℝ)/2)*((x:ℝ)-(z:ℝ)) by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    ring
  calc
    _ = |coef ⟨j, by omega⟩*(Real.cos tx-Real.cos tz)+
      coef ⟨j+1, by omega⟩*(Real.sin tx-Real.sin tz)| := by congr 1; dsimp [tx, tz]; ring
    _ ≤ |coef ⟨j, by omega⟩*(Real.cos tx-Real.cos tz)|+
      |coef ⟨j+1, by omega⟩*(Real.sin tx-Real.sin tz)| := abs_add_le _ _
    _ ≤ |tx-tz|+|tx-tz| := by
      simp only [abs_mul]
      apply add_le_add
      · exact (mul_le_of_le_one_left (abs_nonneg _) (hc _)).trans (Real.abs_cos_sub_cos_le _ _)
      · exact (mul_le_of_le_one_left (abs_nonneg _) (hc _)).trans (Real.abs_sin_sub_sin_le _ _)
    _ = _ := by rw [he]; ring

/-- Two points less than one fine-cell width apart meet at most one interior grid boundary. This statement assumes [the hK condition](hyp:hK), [the hc condition](hyp:hc), [the hxz condition](hyp:hxz), [the hnear condition](hyp:hnear). [This is the stated conclusion](goal). -/
-- @node: frameField_near_lipschitz_ordered
lemma frameField_near_lipschitz_ordered (K : ℕ) (hK : 0 < K)
    (coef : Fin (K+1) → ℝ) (hc : ∀ i, |coef i| ≤ 1) (x z : unitInterval)
    (hxz : (x:ℝ) ≤ (z:ℝ)) (hnear : (K:ℝ)*((z:ℝ)-(x:ℝ)) < 1) :
    |frameField K coef x-frameField K coef z| ≤ Real.pi*(K:ℝ)*|(x:ℝ)-(z:ℝ)| := by
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  by_cases he : (x:ℝ) = (z:ℝ)
  · have he' : x = z := Subtype.ext he
    subst z
    simp
  have hxz' : (x:ℝ) < (z:ℝ) := lt_of_le_of_ne hxz he
  obtain ⟨j, hj, hjx, hxj⟩ := frame_cell_index K hK x
  obtain ⟨k, hk, hkz, hzk⟩ := frame_cell_index K hK z
  have hprod := mul_lt_mul_of_pos_left hxz' hKr
  have hjk : j ≤ k := by
    have : (j:ℝ) < ((k+1:ℕ):ℝ) := by push_cast; linarith
    have : j < k+1 := by exact_mod_cast this
    omega
  have hkj : k ≤ j+1 := by
    have : (k:ℝ) < ((j+2:ℕ):ℝ) := by push_cast; nlinarith
    have : k < j+2 := by exact_mod_cast this
    omega
  by_cases heq : k = j
  · subst k
    exact frameField_cell_lipschitz K hK coef hc j hj x z ⟨hjx, hxj⟩ ⟨hkz, hzk⟩
  have heq : k = j+1 := by omega
  subst k
  have hbound : (j:ℝ)+1 ≤ K := by exact_mod_cast (show j+1 ≤ K by omega)
  let y : unitInterval := ⟨((j:ℝ)+1)/K, ⟨by positivity, (div_le_one hKr).mpr hbound⟩⟩
  have hy : (K:ℝ)*(y:ℝ) = (j:ℝ)+1 := by dsimp [y]; field_simp
  have hxy : (x:ℝ) ≤ (y:ℝ) := by nlinarith
  have hyz : (y:ℝ) ≤ (z:ℝ) := by push_cast at hkz; nlinarith
  have h1 := frameField_cell_lipschitz K hK coef hc j hj x y
    ⟨hjx, hxj⟩ ⟨by rw [hy]; linarith, by rw [hy]⟩
  have h2 := frameField_cell_lipschitz K hK coef hc (j+1) hk y z
    ⟨by push_cast; rw [hy], by push_cast; rw [hy]; linarith⟩ ⟨hkz, hzk⟩
  calc
    _ ≤ |frameField K coef x-frameField K coef y|+|frameField K coef y-frameField K coef z| :=
      abs_sub_le _ _ _
    _ ≤ Real.pi*(K:ℝ)*|(x:ℝ)-(y:ℝ)|+Real.pi*(K:ℝ)*|(y:ℝ)-(z:ℝ)| := add_le_add h1 h2
    _ = _ := by
      rw [abs_of_nonpos (by linarith : (x:ℝ)-(y:ℝ) ≤ 0),
        abs_of_nonpos (by linarith : (y:ℝ)-(z:ℝ) ≤ 0),
        abs_of_nonpos (by linarith : (x:ℝ)-(z:ℝ) ≤ 0)]
      ring

/-- Reversing the points preserves the near-cell Lipschitz bound. This statement assumes [the hK condition](hyp:hK), [the hc condition](hyp:hc), [the hnear condition](hyp:hnear). [This is the stated conclusion](goal). -/
-- @node: frameField_near_lipschitz
lemma frameField_near_lipschitz (K : ℕ) (hK : 0 < K)
    (coef : Fin (K+1) → ℝ) (hc : ∀ i, |coef i| ≤ 1) (x z : unitInterval)
    (hnear : (K:ℝ)*|(x:ℝ)-(z:ℝ)| < 1) :
    |frameField K coef x-frameField K coef z| ≤ Real.pi*(K:ℝ)*|(x:ℝ)-(z:ℝ)| := by
  rcases le_total (x:ℝ) (z:ℝ) with h | h
  · apply frameField_near_lipschitz_ordered K hK coef hc x z h
    rwa [abs_of_nonpos (by linarith : (x:ℝ)-(z:ℝ) ≤ 0), neg_sub] at hnear
  · rw [abs_sub_comm (frameField K coef x), abs_sub_comm (x:ℝ)]
    rw [abs_sub_comm (x:ℝ)] at hnear
    apply frameField_near_lipschitz_ordered K hK coef hc z x h
    rwa [abs_of_nonpos (by linarith : (z:ℝ)-(x:ℝ) ≤ 0), neg_sub] at hnear

/-- The cellwise Lipschitz and uniform envelope bounds yield every exponent up to one. This statement assumes [the hK condition](hyp:hK), [the hs condition](hyp:hs), [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: frame_holder_bound
lemma frame_holder_bound (K : ℕ) (hK : 0 < K) (s : ℝ) (hs : 0 < s ∧ s ≤ 1)
    (coef : Fin (K+1) → ℝ) (hc : ∀ i, |coef i| ≤ 1) :
    (∀ x : unitInterval, |frameField K coef x| ≤ Real.sqrt 2) ∧
    ∀ x z : unitInterval, |frameField K coef x-frameField K coef z| ≤ 4*(K:ℝ)^s*|(x:ℝ)-(z:ℝ)|^s := by
  refine ⟨frameField_abs_le_sqrt_two K hK coef hc, ?_⟩
  intro x z
  let d : ℝ := (K:ℝ)*|(x:ℝ)-(z:ℝ)|
  have hd : 0 ≤ d := mul_nonneg (Nat.cast_nonneg K) (abs_nonneg _)
  have he : (K:ℝ)^s*|(x:ℝ)-(z:ℝ)|^s = d^s :=
    (Real.mul_rpow (Nat.cast_nonneg K) (abs_nonneg _)).symm
  rw [mul_assoc, he]
  by_cases hnear : d < 1
  · have hh := frameField_near_lipschitz K hK coef hc x z hnear
    have hp : d ≤ d^s := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' hd hnear.le hs.1.le hs.2)
    calc
      _ ≤ Real.pi*d := by simpa only [d, mul_assoc] using hh
      _ ≤ 4*d := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hd
      _ ≤ 4*d^s := mul_le_mul_of_nonneg_left hp (by norm_num)
  · have hp : 1 ≤ d^s := Real.one_le_rpow (le_of_not_gt hnear) hs.1.le
    have henv := add_le_add (frameField_abs_le_sqrt_two K hK coef hc x)
      (frameField_abs_le_sqrt_two K hK coef hc z)
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg (2:ℝ)]
    calc
      _ ≤ |frameField K coef x|+|frameField K coef z| := abs_sub _ _
      _ ≤ Real.sqrt 2+Real.sqrt 2 := henv
      _ ≤ 4 := by linarith
      _ ≤ 4*d^s := by linarith

end CausalSmith.Stat.FinitepHomogeneityDensegamma
