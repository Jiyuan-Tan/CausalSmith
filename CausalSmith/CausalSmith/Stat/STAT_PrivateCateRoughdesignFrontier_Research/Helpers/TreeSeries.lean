module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentTransport
public import Causalean.Mathlib.Algebra.BigOperators.ArithmeticGeometricSums
public import Mathlib.Data.Nat.Choose.Bounds
/-! Numerical summation of the labeled-tree envelope for sparse shared-sign components. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

open Causalean.Mathlib.Algebra.BigOperators

/-- In the sparse regime, the differentiated geometric envelope is at most three.  [the theorem's stated inputs and assumptions](hyp:N), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:z,hz,hzcap). -/
-- @node: shifted_geometric_sum_le_three
lemma shifted_geometric_sum_le_three (z : ℝ) (hz : 0 ≤ z) (hzcap : z ≤ 1 / 8)
    (N : ℕ) : (∑ i ∈ Finset.range N, ((i : ℝ) + 2) * z ^ i) ≤ 3 := by
  apply (shiftedArithmeticGeometric_sum_le z hz (by linarith) N).trans
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 - z))).mpr
  have hs : (7/8 : ℝ) ^ 2 ≤ (1 - z) ^ 2 := by nlinarith
  nlinarith

/-- Each tree-series coefficient is bounded by the differentiated geometric majorant. The result uses [the stated assumptions](hyp:ha) and establishes [the displayed conclusion](goal). -/
-- @node: tree_series_term_le
lemma tree_series_term_le (a : ℝ) (ha : 0 ≤ a) (i : ℕ) :
    ((i + 2 : ℕ) : ℝ) ^ ((i + 2) + 1) / ((i + 2).factorial : ℝ) * a ^ i ≤
      (Real.exp 1) ^ 2 * ((i : ℝ) + 2) * ((Real.exp 1) * a) ^ i := by
  have h :
      (((i + 2 : ℕ) : ℝ) ^ (i + 2)) / (((i + 2).factorial : ℕ) : ℝ) ≤
        (Real.exp 1) ^ (i + 2) := by
    have hExp := Real.pow_div_factorial_le_exp
      (x := ((i + 2 : ℕ) : ℝ)) (by positivity) (i + 2)
    simpa only [← Real.exp_nat_mul, mul_one] using hExp
  have hc : 0 ≤ ((i + 2 : ℕ) : ℝ) * a ^ i := by positivity
  have hm := mul_le_mul_of_nonneg_right h hc
  calc
    _ = ((i + 2 : ℕ) : ℝ) ^ (i + 2) / ((i + 2).factorial : ℝ) * (((i + 2 : ℕ) : ℝ) * a ^ i) := by rw [pow_succ]; ring
    _ ≤ (Real.exp 1) ^ (i + 2) * (((i + 2 : ℕ) : ℝ) * a ^ i) := hm
    _ = _ := by rw [pow_add, mul_pow]; push_cast; ring

/-- Summing the tree coefficients under the sparse cap gives the roadmap's constant thirty-two.  [the theorem's stated inputs and assumptions](hyp:hcap,N), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:a,ha). -/
-- @node: tree_series_sum_le_thirty_two
lemma tree_series_sum_le_thirty_two (a : ℝ) (ha : 0 ≤ a)
    (hcap : (Real.exp 1) * a ≤ 1 / 8) (N : ℕ) :
    (∑ i ∈ Finset.range N,
      ((i + 2 : ℕ) : ℝ) ^ ((i + 2) + 1) / ((i + 2).factorial : ℝ) * a ^ i) ≤ 32 := by
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        (Real.exp 1) ^ 2 * ((i : ℝ) + 2) * ((Real.exp 1) * a) ^ i :=
      Finset.sum_le_sum (fun i _ => tree_series_term_le a ha i)
    _ = (Real.exp 1) ^ 2 * ∑ i ∈ Finset.range N,
        ((i : ℝ) + 2) * ((Real.exp 1) * a) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (Real.exp 1) ^ 2 * 3 := mul_le_mul_of_nonneg_left
      (shifted_geometric_sum_le_three _ (mul_nonneg (Real.exp_pos 1).le ha) hcap N)
      (sq_nonneg _)
    _ ≤ 32 := by
      have he := Real.exp_one_lt_d9
      have hp := Real.exp_pos 1
      nlinarith

/-- The sample sparsity cap places the exponential tree-series argument below one eighth.  [the theorem's stated inputs and assumptions](hyp:hcap,n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:d,hd). -/
-- @node: sparse_tree_series_argument_le
lemma sparse_tree_series_argument_le (n : ℕ) (d : ℝ) (hd : 0 ≤ d)
    (hcap : (n : ℝ) * d ≤ 1 / 128) :
    (Real.exp 1) * (4 * (n : ℝ) * d) ≤ 1 / 8 := by
  have he := Real.exp_one_lt_three
  have hn : 0 ≤ (n : ℝ) * d := mul_nonneg (Nat.cast_nonneg n) hd
  have hm := mul_le_mul_of_nonneg_right he.le hn
  nlinarith

/-- The finite numerical tree series is uniformly bounded in the sparse sample regime.  [the theorem's stated inputs and assumptions](hyp:hcap,n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:N,d,hd). -/
-- @node: sparse_tree_series_sum_le
lemma sparse_tree_series_sum_le (n N : ℕ) (d : ℝ) (hd : 0 ≤ d)
    (hcap : (n : ℝ) * d ≤ 1 / 128) :
    (∑ i ∈ Finset.range N,
      ((i + 2 : ℕ) : ℝ) ^ ((i + 2) + 1) / ((i + 2).factorial : ℝ) * (4 * (n : ℝ) * d) ^ i) ≤ 32 := by
  exact tree_series_sum_le_thirty_two _ (by positivity)
    (sparse_tree_series_argument_le n d hd hcap) N

/-- Each cubic component-count envelope factors into the numerical tree coefficient.  [the theorem's stated inputs and assumptions](hyp:ht,hh,hd), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,i,t,d). -/
-- @node: cubic_tree_envelope_term_le
lemma cubic_tree_envelope_term_le (n i : ℕ) (t h d : ℝ)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hd : 0 ≤ d) :
    4 * t * ((i + 2 : ℕ) : ℝ) ^ 3 * (n.choose (i + 2) : ℝ) * (2 * h * ((i + 2 : ℕ) : ℝ) ^ i * (4 * d) ^ (i + 1)) ≤
    32 * t * (n : ℝ) ^ 2 * h * d * (((i + 2 : ℕ) : ℝ) ^ ((i + 2) + 1) / ((i + 2).factorial : ℝ) * (4 * (n : ℝ) * d) ^ i) := by
  have hb : (n.choose (i + 2) : ℝ) ≤
      (n : ℝ) ^ (i + 2) / (((i + 2).factorial : ℕ) : ℝ) :=
    Nat.choose_le_pow_div (i + 2) n
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 4 * t * ((i + 2 : ℕ) : ℝ) ^ 3 * (2 * h * ((i + 2 : ℕ) : ℝ) ^ i * (4 * d) ^ (i + 1)) by positivity)
  calc
    _ ≤ 4 * t * ((i + 2 : ℕ) : ℝ) ^ 3 * ((n : ℝ) ^ (i + 2) / ((i + 2).factorial : ℝ)) * (2 * h * ((i + 2 : ℕ) : ℝ) ^ i * (4 * d) ^ (i + 1)) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
    _ = _ := by
      rw [show (i + 2) + 1 = i + 3 by omega]
      simp only [pow_add, mul_pow]
      ring

/-- The full labeled-tree cubic envelope is at most the transport constant in the roadmap.  [the theorem's stated inputs and assumptions](hyp:ht,hh,hd,hcap,n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:N,t,d). -/
-- @node: cubic_tree_envelope_sum_le
lemma cubic_tree_envelope_sum_le (n N : ℕ) (t h d : ℝ)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (hcap : (n : ℝ) * d ≤ 1 / 128) :
    (∑ i ∈ Finset.range N, 4 * t * ((i + 2 : ℕ) : ℝ) ^ 3 * (n.choose (i + 2) : ℝ) * (2 * h * ((i + 2 : ℕ) : ℝ) ^ i * (4 * d) ^ (i + 1))) ≤
      1024 * t * (n : ℝ) ^ 2 * h * d := by
  calc
    _ ≤ ∑ i ∈ Finset.range N, 32 * t * (n : ℝ) ^ 2 * h * d * (((i + 2 : ℕ) : ℝ) ^ ((i + 2) + 1) / ((i + 2).factorial : ℝ) * (4 * (n : ℝ) * d) ^ i) :=
      Finset.sum_le_sum (fun i _ => cubic_tree_envelope_term_le n i t h d ht hh hd)
    _ = 32 * t * (n : ℝ) ^ 2 * h * d * ∑ i ∈ Finset.range N,
        (((i + 2 : ℕ) : ℝ) ^ ((i + 2) + 1) / ((i + 2).factorial : ℝ) * (4 * (n : ℝ) * d) ^ i) := by rw [Finset.mul_sum]
    _ ≤ 32 * t * (n : ℝ) ^ 2 * h * d * 32 :=
      mul_le_mul_of_nonneg_left (sparse_tree_series_sum_le n N d hd hcap) (by positivity)
    _ = _ := by ring

open Classical in
/-- The number of shared-sign components with a specified size, counted without repeated roots. -/
-- @node: sizeComponentCount
def sizeComponentCount (hL : ℝ) (n : ℕ) (x : Fin n → Covariate) (s : ℕ) : ℕ :=
  ((orderedComponents hL n x).toFinset.filter (fun C => C.card = s)).card

/-- Every ordered component has between one and the sample size many vertices.  [the theorem's stated inputs and assumptions](hyp:C,hC), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: orderedComponents_card_range
lemma orderedComponents_card_range (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (C : Finset (Fin n)) (hC : C ∈ orderedComponents hL n x) :
    1 ≤ C.card ∧ C.card ≤ n := by
  exact ⟨(orderedComponents_nonempty hL n x C hC).card_pos,
    (Finset.card_le_univ C).trans_eq (Fintype.card_fin n)⟩

/-- Empty components never contribute to the component-size count.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: sizeComponentCount_zero
lemma sizeComponentCount_zero (hL : ℝ) (n : ℕ) (x : Fin n → Covariate) :
    sizeComponentCount hL n x 0 = 0 := by
  classical
  unfold sizeComponentCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  obtain ⟨hC, hc⟩ := Finset.mem_filter.mp hC
  have hp := (orderedComponents_card_range hL n x C (List.mem_toFinset.mp hC)).1
  omega

/-- Grouping a component observable by size is an exact finite counting identity.  [the theorem's stated inputs and assumptions](hyp:hL,n,x,f), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:R). -/
-- @node: orderedComponents_sum_by_size
lemma orderedComponents_sum_by_size {R : Type*} [CommSemiring R]
    (hL : ℝ) (n : ℕ) (x : Fin n → Covariate) (f : ℕ → R) :
    (∑ C ∈ (orderedComponents hL n x).toFinset, f C.card) =
      ∑ s ∈ Finset.range (n + 1), (sizeComponentCount hL n x s : R) * f s := by
  classical
  have hsingle (C : Finset (Fin n)) (hC : C ∈ (orderedComponents hL n x).toFinset) :
      f C.card = ∑ s ∈ Finset.range (n + 1), if C.card = s then f s else 0 := by
    have hc := (orderedComponents_card_range hL n x C (List.mem_toFinset.mp hC)).2
    simp [Finset.mem_range, show C.card < n + 1 by omega]
  rw [Finset.sum_congr rfl (fun C hC => hsingle C hC), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_filter]
  have he : (∑ C ∈ (orderedComponents hL n x).toFinset.filter (fun C => C.card = s),
      f s) = (sizeComponentCount hL n x s : R) * f s := by
    simp [sizeComponentCount, nsmul_eq_mul]
  exact he

/-- Component counts are Borel because they are constant on each finite labeled-graph stratum. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: measurable_sizeComponentCount
@[fun_prop] lemma measurable_sizeComponentCount (hL : ℝ) (n s : ℕ) :
    Measurable (fun x => sizeComponentCount hL n x s) := by
  classical
  have hm : Measurable (fun x : Fin n → Covariate => ∑ G : SimpleGraph (Fin n),
      {x | sharedGraph hL n x = G}.indicator (fun _ =>
        ((componentsOfGraph n G).toFinset.filter (fun C => C.card = s)).card) x) := by
    apply Finset.measurable_sum
    intro G _
    exact measurable_const.indicator (measurableSet_sharedGraph_eq hL n G)
  convert hm using 1
  funext x
  simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rfl

/-- The expected nonsingleton cubic sum is exactly the sum of the expected component counts.  [the theorem's stated inputs and assumptions](hyp:μ), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,t). -/
-- @node: lintegral_component_cubic_sum_by_size
lemma lintegral_component_cubic_sum_by_size (hL : ℝ) (n : ℕ) (t : ℝ)
    (μ : Measure (Fin n → Covariate)) :
    (∫⁻ x, ∑ C ∈ (orderedComponents hL n x).toFinset,
      if C.card = 1 then 0 else ENNReal.ofReal (4 * t * (C.card : ℝ) ^ 3) ∂μ) =
    ∑ s ∈ Finset.range (n + 1), (if s = 1 then 0 else ENNReal.ofReal (4 * t * (s : ℝ) ^ 3)) * ∫⁻ x, (sizeComponentCount hL n x s : ℝ≥0∞) ∂μ := by
  classical
  simp_rw [orderedComponents_sum_by_size hL n _
    (fun s => if s = 1 then 0 else ENNReal.ofReal (4 * t * (s : ℝ) ^ 3))]
  rw [lintegral_finsetSum _ (fun s _ =>
    by fun_prop)]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [mul_comm (sizeComponentCount hL n _ s : ℝ≥0∞)]
  exact lintegral_const_mul _ (by fun_prop)

/-- Removing sizes zero and one reindexes any vanishing observable by nonsingleton sizes.  [the theorem's stated inputs and assumptions](hyp:f,h0,h1), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:R,n,hn). -/
-- @node: sum_sizes_eq_shifted
lemma sum_sizes_eq_shifted {R : Type*} [AddCommMonoid R] (n : ℕ) (hn : 1 ≤ n)
    (f : ℕ → R) (h0 : f 0 = 0) (h1 : f 1 = 0) :
    (∑ s ∈ Finset.range (n + 1), f s) = ∑ i ∈ Finset.range (n - 1), f (i + 2) := by
  rw [show n + 1 = 2 + (n - 1) by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_comm]

/-- The expected nonsingleton cubic component cost is indexed by sizes two through n.  [the theorem's stated inputs and assumptions](hyp:μ), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,hn,t). -/
-- @node: lintegral_component_cubic_sum_shifted
lemma lintegral_component_cubic_sum_shifted (hL : ℝ) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (μ : Measure (Fin n → Covariate)) :
    (∫⁻ x, ∑ C ∈ (orderedComponents hL n x).toFinset,
      if C.card = 1 then 0 else ENNReal.ofReal (4 * t * (C.card : ℝ) ^ 3) ∂μ) =
    ∑ i ∈ Finset.range (n - 1), ENNReal.ofReal (4 * t * ((i + 2 : ℕ) : ℝ) ^ 3) * ∫⁻ x, (sizeComponentCount hL n x (i + 2) : ℝ≥0∞) ∂μ := by
  rw [lintegral_component_cubic_sum_by_size]
  rw [sum_sizes_eq_shifted n hn _ (by simp) (by simp)]
  apply Finset.sum_congr rfl
  intro i _
  rw [if_neg (by omega : i + 2 ≠ 1)]

/-- Component-count expectations bounded by the labeled-tree envelope give the claimed cubic cost.
This implication leaves the geometric spanning - tree probability estimate as an explicit input,
without inserting it into a frozen paper theorem. The result uses [the stated assumptions](hyp:hL,hn,ht,hh,hd,hcap,hcounts) and establishes [the displayed conclusion](goal). -/
-- @node: lintegral_component_cubic_sum_le_tree_envelope
lemma lintegral_component_cubic_sum_le_tree_envelope (hL : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (t h d : ℝ) (ht : 0 ≤ t) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (hcap : (n : ℝ) * d ≤ 1 / 128) (μ : Measure (Fin n → Covariate))
    (hcounts : ∀ i ∈ Finset.range (n - 1),
      (∫⁻ x, (sizeComponentCount hL n x (i + 2) : ℝ≥0∞) ∂μ) ≤
        ENNReal.ofReal ((n.choose (i + 2) : ℝ) * (2 * h * ((i + 2 : ℕ) : ℝ) ^ i * (4 * d) ^ (i + 1)))) :
    (∫⁻ x, ∑ C ∈ (orderedComponents hL n x).toFinset,
      if C.card = 1 then 0 else ENNReal.ofReal (4 * t * (C.card : ℝ) ^ 3) ∂μ) ≤
      ENNReal.ofReal (1024 * t * (n : ℝ) ^ 2 * h * d) := by
  rw [lintegral_component_cubic_sum_shifted hL n hn]
  calc
    _ ≤ ∑ i ∈ Finset.range (n - 1), ENNReal.ofReal (4 * t * ((i + 2 : ℕ) : ℝ) ^ 3) * ENNReal.ofReal ((n.choose (i + 2) : ℝ) * (2 * h * ((i + 2 : ℕ) : ℝ) ^ i * (4 * d) ^ (i + 1))) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul le_rfl (hcounts i hi) zero_le zero_le)
    _ = ENNReal.ofReal (∑ i ∈ Finset.range (n - 1),
        4 * t * ((i + 2 : ℕ) : ℝ) ^ 3 * (n.choose (i + 2) : ℝ) * (2 * h * ((i + 2 : ℕ) : ℝ) ^ i * (4 * d) ^ (i + 1))) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      apply Finset.sum_congr rfl
      intro i _
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (cubic_tree_envelope_sum_le n (n - 1) t h d ht hh hd hcap)

/-- For the actual dataset coupling, the remaining tree-count probability estimate implies
its full sparse Hamming cost certificate. The result uses [the stated assumptions](hyp:hL,hhL,hn,hcap,hcounts) and establishes [the displayed conclusion](goal). -/
-- @node: commonMassCoupling_hamming_cost_le_of_tree_counts
lemma commonMassCoupling_hamming_cost_le_of_tree_counts (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) (hn : 1 ≤ n)
    (hcap : (n : ℝ) * deltaL hL ≤ 1 / 128)
    (hcounts : ∀ i ∈ Finset.range (n - 1),
      (∫⁻ x, (sizeComponentCount hL n x (i + 2) : ℝ≥0∞)
        ∂(Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))) ≤
        ENNReal.ofReal ((n.choose (i + 2) : ℝ) * (2 * hL * ((i + 2 : ℕ) : ℝ) ^ i * (4 * deltaL hL) ^ (i + 1)))) :
    (∫⁻ zw, (dHam n zw.1 zw.2 : ℝ≥0∞) ∂commonMassCoupling hL n) ≤
      ENNReal.ofReal (1024 * separation hL * (n : ℝ) ^ 2 * hL * deltaL hL) := by
  have hp : 0 < hL := hhL.1
  apply (commonMassCoupling_hamming_cost_le_cubic_sum hL hhL n).trans
  apply lintegral_component_cubic_sum_le_tree_envelope hL n hn
    (separation hL) hL (deltaL hL) _ hhL.1.le (by unfold deltaL; positivity) hcap _ hcounts
  unfold separation kappa
  positivity

end CausalSmith.Stat.PrivateCateRoughdesign
