module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.Basic

/-! # PairMarks for the paired count-mixture comparison -/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

-- @node: pairObservedMonomial
/-- Polynomial likelihood monomial contributed by the observed marks at one
paired baseline label. Given [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `u`](hyp:u), [the specified input `x`](hyp:x), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). -/
noncomputable def pairObservedMonomial (q σ z u : ℝ) (x : Fin d)
    (counts : Obs d → ℕ) : ℝ :=
  ∏ o : Obs d,
    if o.X = x then pairObservedCoeff q σ z u o ^ counts o else 1

-- @node: pair_label_power_factorization
/-- The likelihood powers at one paired label split into a latent-mass power
and the observed-mark monomial. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `side`](hyp:side), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j). -/
lemma pair_label_power_factorization (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (counts : Obs d → ℕ)
    (j : Fin (pairCount n d)) (side : Bool) :
    (∏ o : Obs d,
      if o.X = pairLabel n d hd j side then
        countAtomMass n d q σ hd θ o ^ counts o else 1) =
      latentP n (θ.1 j) ^
          (∑ o : Obs d,
            if o.X = pairLabel n d hd j side then counts o else 0) *
        pairObservedMonomial q σ (latentZ n (θ.1 j))
          (orientation θ j side) (pairLabel n d hd j side) counts := by
  unfold pairObservedMonomial
  rw [← Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Obs d))
    (fun o => if o.X = pairLabel n d hd j side then counts o else 0)
    (latentP n (θ.1 j)), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro o _
  by_cases ho : o.X = pairLabel n d hd j side
  · simp only [ho, ↓reduceIte,
      countAtomMass_at_pair_label n d q σ hd θ o j side ho, mul_pow]
  · simp [ho]

-- @node: pairObservedMonomial_sign_flip
/-- Every one-label likelihood monomial transforms by latent-sign reflection
when the experiment sign is flipped. Given [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `u`](hyp:u), [the specified input `x`](hyp:x), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). -/
lemma pairObservedMonomial_sign_flip (q z u : ℝ) (x : Fin d)
    (counts : Obs d → ℕ) :
    pairObservedMonomial q (-1) z u x counts =
      pairObservedMonomial q 1 (-z) u x counts := by
  unfold pairObservedMonomial
  apply Finset.prod_congr rfl
  intro o _
  split_ifs
  · rw [pairObservedCoeff_sign_flip]
  · rfl

-- @node: pairObservedMonomial_orientation_sign_flip
/-- Orientation averaging preserves the exact latent-sign reflection of a
one-label likelihood monomial. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `x`](hyp:x), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j). -/
lemma pairObservedMonomial_orientation_sign_flip (n d : ℕ) (q z : ℝ)
    (x : Fin d) (counts : Obs d → ℕ) (θ : Theta n d)
    (j : Fin (pairCount n d)) :
    (∑ side : Bool,
      pairObservedMonomial q (-1) z (orientation θ j side) x counts) =
    ∑ side : Bool,
      pairObservedMonomial q 1 (-z) (orientation θ j side) x counts := by
  apply Finset.sum_congr rfl
  intro side _
  exact pairObservedMonomial_sign_flip q z (orientation θ j side) x counts

-- @node: pairObservedMonomial_mem_unit
/-- Under legal signs, every one-label pair likelihood monomial lies in the
unit interval. Given [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `u`](hyp:u), [the specified input `x`](hyp:x), [the specified input `counts`](hyp:counts), [the specified input `hz`](hyp:hz), [the specified input `hu`](hyp:hu), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq). -/
lemma pairObservedMonomial_mem_unit (q σ z u : ℝ) (x : Fin d)
    (counts : Obs d → ℕ) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1)
    (hu : u = -1 ∨ u = 1) :
    pairObservedMonomial q σ z u x counts ∈ Set.Icc 0 1 := by
  unfold pairObservedMonomial
  have hterm (o : Obs d) :
      (if o.X = x then pairObservedCoeff q σ z u o ^ counts o else 1) ∈
        Set.Icc (0 : ℝ) 1 := by
    split_ifs
    · constructor
      · exact pow_nonneg
          (pairObservedCoeff_nonneg q σ z u o hq hσ hz hu) _
      · exact pow_le_one₀
          (pairObservedCoeff_nonneg q σ z u o hq hσ hz hu)
          (pairObservedCoeff_le_one q σ z u o hq hσ hz hu)
    · exact Set.right_mem_Icc.mpr zero_le_one
  exact ⟨Finset.prod_nonneg fun o _ => (hterm o).1,
    Finset.prod_le_one (fun o _ => (hterm o).1) (fun o _ => (hterm o).2)⟩

-- @node: pairBlockCount
/-- Total observed count in the two labels belonging to one latent pair. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
def pairBlockCount (n d : ℕ) (hd : 1 ≤ d) (counts : Obs d → ℕ)
    (j : Fin (pairCount n d)) : ℕ :=
  ∑ side : Bool, ∑ o : Obs d,
    if o.X = pairLabel n d hd j side then counts o else 0

-- @node: fintype_nat_sum_eq_one
/-- A finite family of natural numbers summing to one has a unique unit entry. Given [the specified input `f`](hyp:f), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α). Given [the specified input `h`](hyp:h). -/
lemma fintype_nat_sum_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℕ) (h : (∑ i, f i) = 1) :
    ∃ i, f i = 1 ∧ ∀ j, j ≠ i → f j = 0 := by
  let d : α →₀ ℕ := Finsupp.equivFunOnFinite.symm f
  have hd : d.sum (fun _ n => n) = 1 := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa [d] using h
  obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff d).mp hd
  refine ⟨i, ?_, ?_⟩
  · have hfun := DFunLike.congr_fun hi i
    simpa [d] using hfun
  · intro j hji
    have hfun := DFunLike.congr_fun hi j
    simpa [d, hji] using hfun

-- @node: pairBlockMarkAverage
/-- Orientation-averaged observed-mark monomial for one pair block, written
without reference to the other latent coordinates. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
noncomputable def pairBlockMarkAverage (n d : ℕ) (q σ z : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) : ℝ :=
  ∑ base : Bool, ∏ side : Bool,
    pairObservedMonomial q σ z (if base == side then 1 else -1)
      (pairLabel n d hd j side) counts

-- @node: pairBlockMarkAverage_degree_zero
/-- A block with no observations has the same orientation-averaged mark
monomial under both experiment signs. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `hzero`](hyp:hzero), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
lemma pairBlockMarkAverage_degree_zero (n d : ℕ) (q z : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hzero : pairBlockCount n d hd counts j = 0) :
    pairBlockMarkAverage n d q (-1) z hd j counts =
      pairBlockMarkAverage n d q 1 z hd j counts := by
  have hcount (side : Bool) (o : Obs d)
      (ho : o.X = pairLabel n d hd j side) : counts o = 0 := by
    unfold pairBlockCount at hzero
    have hs := (Finset.sum_eq_zero_iff.mp hzero) side (Finset.mem_univ side)
    have ho' := (Finset.sum_eq_zero_iff.mp hs) o (Finset.mem_univ o)
    simpa [ho] using ho'
  unfold pairBlockMarkAverage pairObservedMonomial
  apply Finset.sum_congr rfl
  intro base _
  apply Finset.prod_congr rfl
  intro side _
  apply Finset.prod_congr rfl
  intro o _
  by_cases ho : o.X = pairLabel n d hd j side
  · simp [ho, hcount side o ho]
  · simp [ho]

-- @node: pairBlockMarkAverage_singleton
/-- If one specified observed atom is the unique record in a pair block, the
block mark monomial reduces to its orientation-averaged scalar coefficient. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `target`](hyp:target), [the specified input `o₀`](hyp:o₀), [the specified input `ho₀`](hyp:ho₀), [the specified input `hone`](hyp:hone), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j), [the specified input `hother`](hyp:hother). -/
lemma pairBlockMarkAverage_singleton (n d : ℕ) (q σ z : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (target : Bool) (o₀ : Obs d)
    (ho₀ : o₀.X = pairLabel n d hd j target) (hone : counts o₀ = 1)
    (hother : ∀ side o, o.X = pairLabel n d hd j side →
      (side ≠ target ∨ o ≠ o₀) → counts o = 0) :
    pairBlockMarkAverage n d q σ z hd j counts =
      ∑ base : Bool,
        pairObservedCoeff q σ z (if base == target then 1 else -1) o₀ := by
  unfold pairBlockMarkAverage
  apply Finset.sum_congr rfl
  intro base _
  rw [Finset.prod_eq_single target]
  · unfold pairObservedMonomial
    rw [Finset.prod_eq_single o₀]
    · simp [ho₀, hone]
    · intro o _ hne
      by_cases ho : o.X = pairLabel n d hd j target
      · simp [ho, hother target o ho (Or.inr hne)]
      · simp [ho]
    · simp
  · intro side _ hside
    unfold pairObservedMonomial
    apply Finset.prod_eq_one
    intro o _
    by_cases ho : o.X = pairLabel n d hd j side
    · simp [ho, hother side o ho (Or.inl hside)]
    · simp [ho]
  · simp

-- @node: pairBlockMarkAverage_degree_one
/-- A block with exactly one observation has the same orientation-averaged
mark monomial under both experiment signs. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `hone`](hyp:hone), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
lemma pairBlockMarkAverage_degree_one (n d : ℕ) (q z : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hone : pairBlockCount n d hd counts j = 1) :
    pairBlockMarkAverage n d q (-1) z hd j counts =
      pairBlockMarkAverage n d q 1 z hd j counts := by
  let f : Bool × Obs d → ℕ := fun so =>
    if so.2.X = pairLabel n d hd j so.1 then counts so.2 else 0
  have hfsum : (∑ so : Bool × Obs d, f so) = 1 := by
    rw [Fintype.sum_prod_type]
    simpa [f, pairBlockCount] using hone
  obtain ⟨⟨target, o₀⟩, hunit, hother⟩ := fintype_nat_sum_eq_one f hfsum
  have ho₀ : o₀.X = pairLabel n d hd j target := by
    by_contra ho
    simp [f, ho] at hunit
  have hcount₀ : counts o₀ = 1 := by simpa [f, ho₀] using hunit
  have hcount_other (side : Bool) (o : Obs d)
      (ho : o.X = pairLabel n d hd j side)
      (hne : side ≠ target ∨ o ≠ o₀) : counts o = 0 := by
    have hpair : (side, o) ≠ (target, o₀) := by
      intro h
      exact hne.elim (fun hs => hs (congrArg Prod.fst h))
        (fun hoo => hoo (congrArg Prod.snd h))
    simpa [f, ho] using hother (side, o) hpair
  rw [pairBlockMarkAverage_singleton n d q (-1) z hd j counts target o₀
      ho₀ hcount₀ hcount_other,
    pairBlockMarkAverage_singleton n d q 1 z hd j counts target o₀
      ho₀ hcount₀ hcount_other]
  exact pairObservedCoeff_bool_orientation_linear_cancel q z target o₀

-- @node: pairBlockMarkAverage_gap_le_two
/-- For legal overlap and latent signs, the absolute orientation-averaged mark
gap of one pair block is at most two. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `hz`](hyp:hz), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j), [the specified input `hq`](hyp:hq). -/
lemma pairBlockMarkAverage_gap_le_two (n d : ℕ) (q z : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (hz : z = -1 ∨ z = 1) :
    |pairBlockMarkAverage n d q (-1) z hd j counts -
      pairBlockMarkAverage n d q 1 z hd j counts| ≤ 2 := by
  have hterm (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) (base : Bool) :
      (∏ side : Bool,
        pairObservedMonomial q σ z (if base == side then 1 else -1)
          (pairLabel n d hd j side) counts) ∈ Set.Icc (0 : ℝ) 1 := by
    have hmono (side : Bool) :
        pairObservedMonomial q σ z (if base == side then 1 else -1)
          (pairLabel n d hd j side) counts ∈ Set.Icc (0 : ℝ) 1 := by
      apply pairObservedMonomial_mem_unit q σ z _ _ counts hq hσ hz
      split_ifs <;> simp
    exact ⟨Finset.prod_nonneg fun side _ => (hmono side).1,
      Finset.prod_le_one (fun side _ => (hmono side).1)
        (fun side _ => (hmono side).2)⟩
  have hsum (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) :
      pairBlockMarkAverage n d q σ z hd j counts ∈ Set.Icc (0 : ℝ) 2 := by
    unfold pairBlockMarkAverage
    constructor
    · exact Finset.sum_nonneg fun base _ => (hterm σ hσ base).1
    · calc
        _ ≤ ∑ _base : Bool, (1 : ℝ) :=
          Finset.sum_le_sum fun base _ => (hterm σ hσ base).2
        _ = 2 := by simp
  rcases hsum (-1) (Or.inl rfl) with ⟨hm0, hm2⟩
  rcases hsum 1 (Or.inr rfl) with ⟨hp0, hp2⟩
  rw [abs_le]
  constructor <;> linarith

-- @node: pairBlockMarkAverage_sign_flip
/-- Flipping the experiment sign is exactly reflection of the scalar latent
sign in the orientation-averaged block monomial. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
lemma pairBlockMarkAverage_sign_flip (n d : ℕ) (q z : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    pairBlockMarkAverage n d q (-1) z hd j counts =
      pairBlockMarkAverage n d q 1 (-z) hd j counts := by
  unfold pairBlockMarkAverage
  apply Finset.sum_congr rfl
  intro base _
  apply Finset.prod_congr rfl
  intro side _
  exact pairObservedMonomial_sign_flip q z _ _ counts

-- @node: pairBlockMarkAverage_gap_factor
/-- On the two-point latent-sign support, the signed block gap factors as the
latent sign times its value at positive sign. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `hz`](hyp:hz), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
lemma pairBlockMarkAverage_gap_factor (n d : ℕ) (q z : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hz : z = -1 ∨ z = 1) :
    pairBlockMarkAverage n d q (-1) z hd j counts -
        pairBlockMarkAverage n d q 1 z hd j counts =
      z * (pairBlockMarkAverage n d q (-1) 1 hd j counts -
        pairBlockMarkAverage n d q 1 1 hd j counts) := by
  rcases hz with rfl | rfl
  · rw [pairBlockMarkAverage_sign_flip n d q 1 hd j counts]
    have h := pairBlockMarkAverage_sign_flip n d q (-1) hd j counts
    norm_num at h ⊢
    rw [h]
  · ring

-- @node: signedExponentialSeriesTail
/-- The signed tail after truncating the power series of `exp (-x)` through
the displayed degree. Given [the specified input `degree`](hyp:degree), [the specified input `x`](hyp:x), [the stated mathematical conclusion holds](goal). -/
noncomputable def signedExponentialSeriesTail (degree : ℕ) (x : ℝ) : ℝ :=
  ∑' t : ℕ, if degree < t then (-x) ^ t / (t.factorial : ℝ) else 0

-- @node: exp_neg_eq_truncated_add_signed_tail
/-- Exact Taylor decomposition of the random-normalizer exponential. Given [the specified input `degree`](hyp:degree), [the specified input `x`](hyp:x), [the stated mathematical conclusion holds](goal). -/
lemma exp_neg_eq_truncated_add_signed_tail (degree : ℕ) (x : ℝ) :
    Real.exp (-x) =
      (∑ t ∈ Finset.range (degree + 1), (-x) ^ t / (t.factorial : ℝ)) +
        signedExponentialSeriesTail degree x := by
  let f : ℕ → ℝ := fun t => (-x) ^ t / (t.factorial : ℝ)
  let low : ℕ → ℝ := fun t => if t ≤ degree then f t else 0
  let high : ℕ → ℝ := fun t => if degree < t then f t else 0
  have hf : Summable f := Real.summable_pow_div_factorial (-x)
  have hlow : Summable low := by
    simpa only [low, show (fun t => if t ≤ degree then f t else 0) =
      (Set.Iic degree).indicator f by funext t; simp [Set.indicator]] using
      hf.indicator (Set.Iic degree)
  have hhigh : Summable high := by
    simpa only [high, show (fun t => if degree < t then f t else 0) =
      (Set.Ioi degree).indicator f by funext t; simp [Set.indicator]] using
      hf.indicator (Set.Ioi degree)
  have hsplit : (∑' t, f t) = (∑' t, low t) + ∑' t, high t := by
    rw [← hlow.tsum_add hhigh]
    apply tsum_congr
    intro t
    simp only [low, high]
    by_cases ht : t ≤ degree
    · simp [ht, Nat.not_lt_of_ge ht]
    · have hdt : degree < t := Nat.lt_of_not_ge ht
      simp [ht, hdt]
  rw [Real.exp_eq_exp_ℝ, ← (NormedSpace.expSeries_div_hasSum_exp (-x)).tsum_eq]
  change (∑' t, f t) = _
  rw [hsplit]
  congr 1
  · rw [tsum_eq_sum (s := Finset.range (degree + 1))]
    · apply Finset.sum_congr rfl
      intro t ht
      simp only [low]
      rw [if_pos]
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    · intro t ht
      simp only [low]
      rw [if_neg]
      have hge : degree + 1 ≤ t := by
        simpa only [Finset.mem_range, not_lt] using ht
      omega

-- @node: abs_signedExponentialSeriesTail_le
/-- The signed Taylor remainder is dominated by the ordinary positive
exponential-series tail. Given [the specified input `degree`](hyp:degree), [the specified input `x`](hyp:x), [the specified input `hx`](hyp:hx), [the stated mathematical conclusion holds](goal). -/
lemma abs_signedExponentialSeriesTail_le (degree : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    |signedExponentialSeriesTail degree x| ≤
      Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail degree x := by
  unfold signedExponentialSeriesTail
  have hnorm : (fun t : ℕ =>
      ‖if degree < t then (-x) ^ t / (t.factorial : ℝ) else 0‖) =
      fun t => if degree < t then x ^ t / (t.factorial : ℝ) else 0 := by
    funext t
    by_cases ht : degree < t
    · simp [ht, Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg hx,
        show (0 : ℝ) ≤ t.factorial by positivity]
    · simp [ht]
  have hsum : Summable (fun t : ℕ =>
      if degree < t then x ^ t / (t.factorial : ℝ) else 0) := by
    simpa only [show (fun t : ℕ => if degree < t then
        x ^ t / (t.factorial : ℝ) else 0) =
      (Set.Ioi degree).indicator
        (fun t => x ^ t / (t.factorial : ℝ)) by
          funext t; simp [Set.indicator]] using
      (Real.summable_pow_div_factorial x).indicator (Set.Ioi degree)
  calc
    _ ≤ ∑' t : ℕ,
        ‖if degree < t then (-x) ^ t / (t.factorial : ℝ) else 0‖ :=
      norm_tsum_le_tsum_norm (by rw [hnorm]; exact hsum)
    _ = _ := by
      unfold Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
      apply tsum_congr
      intro t
      by_cases ht : degree < t
      · simp [ht, Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg hx,
          show (0 : ℝ) ≤ t.factorial by positivity]
      · simp [ht]

-- @node: factorial_series_convolution
/-- The factorial-normalized Cauchy coefficient of two exponential series is
the corresponding coefficient at the sum of their arguments. Given [the specified input `a`](hyp:a), [the specified input `b`](hyp:b), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma factorial_series_convolution (a b : ℝ) (s : ℕ) :
    (∑ r ∈ Finset.range (s + 1),
      a ^ r / (r.factorial : ℝ) *
        (b ^ (s - r) / ((s - r).factorial : ℝ))) =
      (a + b) ^ s / (s.factorial : ℝ) := by
  rw [eq_div_iff (by positivity : (s.factorial : ℝ) ≠ 0)]
  rw [Finset.sum_mul, add_pow]
  apply Finset.sum_congr rfl
  intro r hr
  have hrs : r ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  rw [Nat.cast_choose ℝ hrs]
  field_simp

-- @node: exponentialSeriesTail_add_convolution
/-- The unmatched bidegrees of two factorial series regroup into the ordinary
exponential tail at the sum of the two arguments. Given [the specified input `degree`](hyp:degree), [the specified input `a`](hyp:a), [the specified input `b`](hyp:b), [the stated mathematical conclusion holds](goal). -/
lemma exponentialSeriesTail_add_convolution (degree : ℕ) (a b : ℝ) :
    (∑' s : ℕ, if degree < s then
      ∑ r ∈ Finset.range (s + 1),
        a ^ r / (r.factorial : ℝ) *
          (b ^ (s - r) / ((s - r).factorial : ℝ)) else 0) =
      Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
        degree (a + b) := by
  unfold Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
  apply tsum_congr
  intro s
  by_cases hs : degree < s
  · rw [if_pos hs, if_pos hs, factorial_series_convolution]
  · rw [if_neg hs, if_neg hs]

-- @node: latentWeight_nonneg_count
/-- Given [the specified input `n`](hyp:n), [the specified input `z`](hyp:z), [the stated mathematical conclusion holds](goal). -/
lemma latentWeight_nonneg_count (n : ℕ) (z : Latent n) :
    0 ≤ latentWeight n z := by
  cases z with
  | inl i =>
      exact div_nonneg
        (mul_nonneg (by unfold priorH; positivity) (abs_nonneg _))
        (le_of_lt (latentWeight_node_pos n i))
  | inr _ =>
      simp only [latentWeight]
      apply sub_nonneg.mpr
      calc
        (∑ i : Fin (priorK n),
            priorH n * |signedNodeWeight n i| / interpolationNode n i) ≤
            ∑ i : Fin (priorK n), |signedNodeWeight n i| := by
          apply Finset.sum_le_sum
          intro i _
          apply (div_le_iff₀ (latentWeight_node_pos n i)).mpr
          nlinarith [latentWeight_node_lower n i,
            abs_nonneg (signedNodeWeight n i)]
        _ ≤ 1 := latentWeight_signed_total_le_one n

-- @node: oneLatentLaw_toReal_count
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `z`](hyp:z), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma oneLatentLaw_toReal_count (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (z : Latent n) :
    (oneLatentLaw n d q hn hd hq z).toReal = latentWeight n z := by
  rw [oneLatentLaw, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (latentWeight_nonneg_count n z)]

-- @node: thetaLaw_product_factorization
/-- The full latent-and-orientation law factors coordinatewise for arbitrary
per-pair real statistics. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `f`](hyp:f). -/
lemma thetaLaw_product_factorization (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (f : Fin (pairCount n d) → Latent n → Bool → ℝ) :
    (∑ θ : Theta n d,
        (thetaLaw n d q hn hd hq θ).toReal *
          ∏ j : Fin (pairCount n d), f j (θ.1 j) (θ.2 j)) =
      ∏ j : Fin (pairCount n d),
        ∑ z : Latent n, latentWeight n z *
          ∑ b : Bool, (1 / 2 : ℝ) * f j z b := by
  simp only [thetaLaw, PMF.ofFintype_apply, thetaWeight,
    ENNReal.toReal_prod, ENNReal.toReal_mul, oneLatentLaw_toReal_count,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ u : Fin (pairCount n d) → Latent n,
        ∑ s : Fin (pairCount n d) → Bool,
          ∏ j : Fin (pairCount n d),
            latentWeight n (u j) * ((1 / 2 : ℝ) * f j (u j) (s j)) := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro s _
      have hhalf : ((1 / 2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
      rw [hhalf]
      have hleft :
          (∏ j : Fin (pairCount n d),
            latentWeight n (u j) * (1 / 2 : ℝ)) =
            (∏ j, latentWeight n (u j)) *
              ∏ _j : Fin (pairCount n d), (1 / 2 : ℝ) :=
        Finset.prod_mul_distrib
      have hright :
          (∏ j : Fin (pairCount n d),
            latentWeight n (u j) * ((1 / 2 : ℝ) * f j (u j) (s j))) =
            (∏ j, latentWeight n (u j)) *
              ((∏ _j : Fin (pairCount n d), (1 / 2 : ℝ)) *
                ∏ j, f j (u j) (s j)) := by
        calc
          _ = (∏ j, latentWeight n (u j)) *
              ∏ j, ((1 / 2 : ℝ) * f j (u j) (s j)) :=
            Finset.prod_mul_distrib
          _ = _ := by rw [Finset.prod_mul_distrib]
      rw [hleft, hright]
      ring
    _ = ∑ u : Fin (pairCount n d) → Latent n,
        ∏ j : Fin (pairCount n d),
          ∑ b : Bool, latentWeight n (u j) * ((1 / 2 : ℝ) * f j (u j) b) := by
      apply Finset.sum_congr rfl
      intro u _
      exact (Fintype.prod_sum (fun j : Fin (pairCount n d) => fun b : Bool =>
        latentWeight n (u j) * ((1 / 2 : ℝ) * f j (u j) b))).symm
    _ = ∑ u : Fin (pairCount n d) → Latent n,
        ∏ j : Fin (pairCount n d),
          latentWeight n (u j) *
            ∑ b : Bool, (1 / 2 : ℝ) * f j (u j) b := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.prod_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = _ := (Fintype.prod_sum
      (fun j : Fin (pairCount n d) => fun z : Latent n =>
        latentWeight n z * ∑ b : Bool, (1 / 2 : ℝ) * f j z b)).symm


end CausalSmith.Stat.MarNearcompleteFrontier
