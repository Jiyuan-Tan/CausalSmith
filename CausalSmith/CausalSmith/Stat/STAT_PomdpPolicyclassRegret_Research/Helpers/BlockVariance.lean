module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockSegmentDisjoint

/-!
# Covariance row summation for PHIW blocks

Each positive lag appears at most once on either side of a window. Summing
these envelopes gives the variance of the actual observable block average.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators

/-- An injective assignment of lags bounds a partial row by its nonnegative lag envelope,
including lags not present in that row. For [the ι](hyp:ι), [the state](hyp:s),
[the epoch index](hyp:t), [the code dimension](hyp:d), [the f](hyp:f),
[the observed word](hyp:w), [the code dimension assumption](hyp:hd),
[the dt assumption](hyp:hdt), [the observed word assumption](hyp:hw), and
[the f assumption](hyp:hf), this establishes
[the partial-history importance-weighted sum bound injective lag envelope result](goal). -/
-- @node: phiw_sum_le_injective_lag_envelope
lemma phiw_sum_le_injective_lag_envelope {ι : Type*}
    (s : Finset ι) (t : Finset Nat) (d : ι → Nat) (f : ι → ℝ) (w : Nat → ℝ)
    (hd : Set.InjOn d s) (hdt : ∀ i ∈ s, d i ∈ t)
    (hw : ∀ h ∈ t, 0 ≤ w h) (hf : ∀ i ∈ s, f i ≤ w (d i)) :
    (∑ i ∈ s, f i) ≤ ∑ h ∈ t, w h := by
  classical
  calc
    _ ≤ ∑ i ∈ s, w (d i) := Finset.sum_le_sum hf
    _ = ∑ h ∈ s.image d, w h := (Finset.sum_image hd).symm
    _ ≤ ∑ h ∈ t, w h := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro h hh; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh; exact hdt i hi)
      (by intro h hh _; exact hw h hh)

/-- A symmetric finite matrix has row sum at most its diagonal envelope plus two copies of the
positive-lag envelope. For [the effective sample size](hyp:N), [the c](hyp:c), [the d](hyp:D),
[the observed word](hyp:w), [the sym assumption](hyp:hsym), [the diag assumption](hyp:hdiag),
[the observed word assumption](hyp:hw), [the upper assumption](hyp:hupper), and [the i](hyp:i),
this establishes
[the partial-history importance-weighted covariance row bound lag envelope result](goal). -/
-- @node: phiw_covariance_row_le_lag_envelope
lemma phiw_covariance_row_le_lag_envelope (N : Nat) (c : Fin N → Fin N → ℝ)
    (D : ℝ) (w : Nat → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i ≤ D) (hw : ∀ h ∈ Finset.Ico 1 N, 0 ≤ w h)
    (hupper : ∀ i j, i < j → c i j ≤ w (j.val - i.val)) (i : Fin N) :
    (∑ j, c i j) ≤ D + 2 * ∑ h ∈ Finset.Ico 1 N, w h := by
  classical
  have hsplit : (∑ j, c i j) = c i i +
      (∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ j < i), c i j) +
      (∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ i < j), c i j) := by
    have heq : ∀ j, c i j = (if j = i then c i i else 0) +
        (if j < i then c i j else 0) + (if i < j then c i j else 0) := by
      intro j
      rcases lt_trichotomy j i with h | h | h <;> simp [ne_of_lt, ne_of_gt,
        not_lt_of_ge, le_of_lt, *]
    calc
      _ = ∑ j : Fin N, ((if j = i then c i i else 0) +
          (if j < i then c i j else 0) + (if i < j then c i j else 0)) :=
        Finset.sum_congr rfl (fun j _ ↦ heq j)
      _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite]
  have hleft : (∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ j < i), c i j) ≤
      ∑ h ∈ Finset.Ico 1 N, w h := by
    apply phiw_sum_le_injective_lag_envelope _ _ (fun j : Fin N ↦ i.val - j.val) _ w
    · intro j hj l hl heq
      dsimp only at heq
      have hj' := (Finset.mem_filter.mp hj).2
      have hl' := (Finset.mem_filter.mp hl).2
      apply Fin.ext
      change j.val < i.val at hj'
      change l.val < i.val at hl'
      omega
    · intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      change j.val < i.val at hj'
      simp only [Finset.mem_Ico]
      omega
    · exact hw
    · intro j hj
      rw [hsym]
      exact hupper j i (Finset.mem_filter.mp hj).2
  have hright : (∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ i < j), c i j) ≤
      ∑ h ∈ Finset.Ico 1 N, w h := by
    apply phiw_sum_le_injective_lag_envelope _ _ (fun j : Fin N ↦ j.val - i.val) _ w
    · intro j hj l hl heq
      dsimp only at heq
      have hj' := (Finset.mem_filter.mp hj).2
      have hl' := (Finset.mem_filter.mp hl).2
      apply Fin.ext
      change i.val < j.val at hj'
      change i.val < l.val at hl'
      omega
    · intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      change i.val < j.val at hj'
      simp only [Finset.mem_Ico]
      omega
    · exact hw
    · intro j hj
      exact hupper i j (Finset.mem_filter.mp hj).2
  rw [hsplit]
  linarith [hdiag i]

/-- Splitting positive lags at the history depth bounds their finite envelope by the overlap
geometric sum and twice the shifted disjoint geometric sum. For
[the effective sample size](hyp:N), [the history length](hyp:k),
[the action-overlap factor](hyp:L), [the contraction coefficient](hyp:α),
[the action-overlap factor assumption](hyp:hL), and
[the contraction coefficient assumption](hyp:hα), this establishes
[the partial-history importance-weighted piecewise lag sum bound result](goal). -/
-- @node: phiw_piecewise_lag_sum_le
lemma phiw_piecewise_lag_sum_le (N k : Nat) (L α : ℝ)
    (hL : 0 ≤ L) (hα : 0 ≤ α) :
    (∑ h ∈ Finset.Ico 1 N, if h ≤ k then L ^ (k + 1 - h)
      else 2 * α ^ (h - 1)) ≤
      (∑ h ∈ Finset.Ico 1 (k + 1), L ^ (k + 1 - h)) +
        2 * ∑ h ∈ Finset.Ico k N, α ^ h := by
  classical
  rw [Finset.sum_ite]
  have ho : (∑ h ∈ (Finset.Ico 1 N).filter (fun h ↦ h ≤ k), L ^ (k + 1 - h)) ≤
      ∑ h ∈ Finset.Ico 1 (k + 1), L ^ (k + 1 - h) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_Ico] at hh ⊢
      omega
    · intro h _ _; exact pow_nonneg hL _
  have hd : (∑ h ∈ (Finset.Ico 1 N).filter (fun h ↦ ¬h ≤ k), 2 * α ^ (h - 1)) ≤
      ∑ h ∈ Finset.Ico k N, 2 * α ^ h := by
    apply phiw_sum_le_injective_lag_envelope _ _ (fun h ↦ h - 1) _ (fun h ↦ 2 * α ^ h)
    · intro h hh l hl heq
      dsimp only at heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hh hl
      omega
    · intro h hh
      simp only [Finset.mem_filter, Finset.mem_Ico] at hh ⊢
      omega
    · intro h _; positivity
    · intro h _; exact le_rfl
  exact add_le_add ho (by simpa only [← Finset.mul_sum] using hd)

/-- Sharp diagonal and two-sided lag estimates give the advertised covariance row bound, with
the geometric constants from the paper's proof. For [the effective sample size](hyp:N),
[the history length](hyp:k), [the action-overlap factor](hyp:L),
[the contraction coefficient](hyp:α), [the action-overlap factor assumption](hyp:hL),
[the α0 assumption](hyp:hα0), [the α1 assumption](hyp:hα1), [the c](hyp:c),
[the sym assumption](hyp:hsym), [the diag assumption](hyp:hdiag), [the o assumption](hyp:ho),
[the code dimension assumption](hyp:hd), and [the i](hyp:i), this establishes
[the partial-history importance-weighted covariance row numeric bound result](goal). -/
-- @node: phiw_covariance_row_numeric_bound
lemma phiw_covariance_row_numeric_bound (N k : Nat) (L α : ℝ)
    (hL : 1 < L) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (c : Fin N → Fin N → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i ≤ L ^ (k + 1))
    (ho : ∀ i j, i < j → j.val - i.val ≤ k → c i j ≤ L ^ (k + 1 - (j.val - i.val)))
    (hd : ∀ i j, i < j → k < j.val - i.val → c i j ≤ 2 * α ^ (j.val - i.val - 1))
    (i : Fin N) :
    (∑ j, c i j) ≤ (1 + 2 / (L - 1) + 4 / (1 - α)) * L ^ (k + 1) := by
  have hr := phiw_covariance_row_le_lag_envelope N c (L ^ (k + 1))
    (fun h ↦ if h ≤ k then L ^ (k + 1 - h) else 2 * α ^ (h - 1)) hsym hdiag
    (by intro h _; split_ifs <;> positivity)
    (by intro i j hij; split_ifs with h
        · exact ho i j hij h
        · exact hd i j hij (by omega)) i
  have hs := phiw_piecewise_lag_sum_le N k L α (by linarith) hα0
  have hn := phiw_variance_lag_numeric_bound k N L α hL hα0 hα1
  linarith

/-- The valid windows in a raw block are exactly the `n-k` prefix-indexed windows, so their
normalized finite sum is the observable PHIW average. For [the sample size](hyp:n),
[the observed-state count](hyp:nX), [the history length](hyp:k), [the behavior policy](hyp:b),
[the target policy](hyp:e), and [the observed word](hyp:w), this establishes
[the partial-history importance-weighted raw equality prefix average result](goal). -/
-- @node: phiwRaw_eq_prefix_average
lemma phiwRaw_eq_prefix_average {n nX : Nat} (k : Nat) (b e : Policy nX)
    (w : ObsView n nX) :
    phiwRaw k b e w = (∑ r : Fin (n - k),
      phiwScore k b e w ⟨r.val + k, by omega⟩) / (n - k : Nat) := by
  have hs := phiw_sum_valid_windows_eq_range k (fun t ↦ phiwScore k b e w t)
    (fun r ↦ if ht : r + k < n then phiwScore k b e w ⟨r + k, ht⟩ else 0) (by
      intro t ht
      have heq : t.val - k + k = t.val := by omega
      simp only [heq, t.isLt, dif_pos, Fin.eta])
  have hr : (∑ r ∈ Finset.range (n - k),
      if ht : r + k < n then phiwScore k b e w ⟨r + k, ht⟩ else 0) =
      ∑ r : Fin (n - k), phiwScore k b e w ⟨r.val + k, by omega⟩ := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro r _
    simp only [show r.val + k < n by omega, dif_pos]
  rw [phiwRaw, hs, hr]
  simp only [div_eq_mul_inv, mul_comm]

/-- Equations (6), (8), and (9) assembled for the actual observable arbitrary start law yield
the variance half of the block-moment theorem. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the history length](hyp:k), and [the history length assumption](hyp:hk), this establishes
[the partial-history importance-weighted raw observed segment variance result](goal). -/
-- @node: phiwRaw_observedSegment_variance
lemma phiwRaw_observedSegment_variance {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (k : Nat) (hk : k < n) :
    variance (phiwRaw k m.Mx.b (m.Mx.E j))
      ((segmentLaw m hClass.finite_state nu n).map obsProj) ≤
      (1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
        policyFactor zeta ^ (k + 1) / (n - k : Nat) := by
  have : IsProbabilityMeasure ((segmentLaw m hClass.finite_state nu n).map obsProj) :=
    observedSegmentLaw_isProbability m hClass.sequential_ignorability.1
      hClass.finite_state nu hnu n
  let μ := (segmentLaw m hClass.finite_state nu n).map obsProj
  let X := fun (r : Fin (n - k)) (w : ObsView n m.nX) ↦
    phiwScore k m.Mx.b (m.Mx.E j) w ⟨r.val + k, by omega⟩
  have hX : ∀ r, MemLp (X r) 2 μ := fun r ↦
    phiwScore_observedSegment_memLp t0 zeta C m hClass j nu hnu r.val k (by omega) 2
  have hL : 1 < policyFactor zeta := Real.one_lt_exp_iff.mpr hzeta
  have hα0 : 0 ≤ mixingAlpha t0 := Real.exp_nonneg _
  have hα1 : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have heq : phiwRaw k m.Mx.b (m.Mx.E j) =
      (fun w ↦ (∑ r, X r w) / (n - k : Nat)) := by
    funext w
    exact phiwRaw_eq_prefix_average k _ _ w
  rw [heq]
  apply variance_average_le_of_covariance_rows μ (n - k) (by omega) X hX
  intro i
  apply phiw_covariance_row_numeric_bound (n - k) k (policyFactor zeta) (mixingAlpha t0)
    hL hα0 hα1 (fun i j ↦ covariance (X i) (X j) μ)
  · intro i j; exact covariance_comm _ _
  · intro i
    rw [covariance_self (hX i).aestronglyMeasurable.aemeasurable]
    exact phiwScore_observedSegment_variance t0 zeta C m hClass j nu hnu i.val k (by omega)
  · intro i l hil hlag
    have ht : i.val + (l.val - i.val) + k < n := by omega
    have h := phiwScore_observedSegment_overlap_covariance t0 zeta C m hClass hzeta.le j
      nu hnu i.val k (l.val - i.val) (by omega) ht
    have he : i.val + (l.val - i.val) + k = l.val + k := by omega
    exact (le_abs_self _).trans (by simpa only [he] using h)
  · intro i l hil hlag
    have ht : i.val + (l.val - i.val) + k < n := by omega
    have h := phiwScore_observedSegment_disjoint_covariance t0 zeta C m hClass j
      nu hnu i.val k (l.val - i.val) hlag ht
    have he : i.val + (l.val - i.val) + k = l.val + k := by omega
    exact (le_abs_self _).trans (by simpa only [he] using h)

end CausalSmith.Stat.PomdpPolicyclassRegret
