module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Normalized paired prior and count experiment

The latent support, legal full laws, observed mixtures, independent Poisson count
experiment and parameter-independent count-ordering kernel are defined here.
All normalization and law-class obligations are separately named proof obligations.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators ENNReal NNReal

/-- [The interpolation degree](goal) is the logarithmic degree selected for [the sample size](hyp:n). -/
noncomputable def priorK (n : ℕ) : ℕ := Nat.ceil (8 * ell n)
/-- [The interpolation lower endpoint](goal) is determined by [the sample size](hyp:n). -/
noncomputable def priorH (n : ℕ) : ℝ := (priorK n : ℝ)⁻¹ ^ 2
/-- [The prior scale](goal) is determined by [the sample size](hyp:n). -/
noncomputable def priorB (n : ℕ) : ℝ := (priorK n : ℝ) / (1024 * n)
/-- [The number of paired coordinates](goal) is determined by [the sample size](hyp:n) and [the covariate dimension](hyp:d). -/
noncomputable def pairCount (n d : ℕ) : ℕ :=
  min ((d - 1) / 2) (Nat.floor ((n : ℝ) * ell n))
/-- [The residual filler mass](goal) is determined by [the sample size](hyp:n) and [the covariate dimension](hyp:d). -/
noncomputable def fillerMass (n d : ℕ) : ℝ :=
  1 - 2 * pairCount n d * priorH n * priorB n
/-- [The baseline Bernoulli mean](goal) is calibrated to [the arrival-floor parameter](hyp:q). -/
noncomputable def baseMean (q : ℝ) : ℝ :=
  (1 - delta q / 2) ^ 2 / (2 * q)

/-- Interpolation nodes on `[h,1]`. -/
noncomputable def interpolationNode (n : ℕ) (i : Fin (priorK n)) : ℝ :=
  (1 + priorH n) / 2 + (1 - priorH n) / 2 *
    Real.cos ((i : ℝ) * Real.pi / ((priorK n - 1 : ℕ) : ℝ))

/-- Cardinal Lagrange coefficient evaluated at zero. -/
noncomputable def lagrangeAtZero (n : ℕ) (i : Fin (priorK n)) : ℝ :=
  (Lagrange.basis Finset.univ (interpolationNode n) i).eval 0

/-- Total variation of the interpolation coefficients. -/
noncomputable def lagrangeNorm (n : ℕ) : ℝ :=
  ∑ i : Fin (priorK n), |lagrangeAtZero n i|

/-- Signed normalized interpolation weights. -/
noncomputable def signedNodeWeight (n : ℕ) (i : Fin (priorK n)) : ℝ :=
  lagrangeAtZero n i / lagrangeNorm n

/-- One latent pair is either an interpolation node or the residual zero atom. -/
abbrev Latent (n : ℕ) := Fin (priorK n) ⊕ Unit

/-- [The latent probability coordinate](goal) assigns each atom in [the sample-size-dependent support](hyp:n) its interpolation value or zero. -/
noncomputable def latentP (n : ℕ) : Latent n → ℝ
  | .inl i => priorB n * interpolationNode n i
  | .inr _ => 0

/-- [The latent sign coordinate](goal) assigns each atom in [the sample-size-dependent support](hyp:n) its signed interpolation orientation. -/
noncomputable def latentZ (n : ℕ) : Latent n → ℝ
  | .inl i => if 0 ≤ signedNodeWeight n i then 1 else -1
  | .inr _ => 1

/-- [The latent mixing weight](goal) assigns each atom in [the sample-size-dependent support](hyp:n) its normalized mass. -/
noncomputable def latentWeight (n : ℕ) : Latent n → ℝ
  | .inl i => priorH n * |signedNodeWeight n i| / interpolationNode n i
  | .inr _ => 1 - ∑ i : Fin (priorK n),
      priorH n * |signedNodeWeight n i| / interpolationNode n i

-- @node: latentWeight_node_lower
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `i`](hyp:i). -/
lemma latentWeight_node_lower (n : ℕ) (i : Fin (priorK n)) :
    priorH n ≤ interpolationNode n i := by
  have hh : priorH n ≤ 1 := by
    have hk : (1 : ℝ) ≤ priorK n := by
      have he : (0 : ℝ) < ell n := by
        unfold ell
        apply Real.log_pos
        have h := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
        exact lt_of_lt_of_le h (le_add_of_nonneg_right (Nat.cast_nonneg _))
      have hc : 8 * ell n ≤ (priorK n : ℝ) := Nat.le_ceil _
      have hp : (0 : ℝ) < priorK n := by linarith
      have hpn : 0 < priorK n := by exact_mod_cast hp
      exact_mod_cast (show 1 ≤ priorK n by omega)
    unfold priorH
    have hi : (priorK n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk
    have hnonneg : (0 : ℝ) ≤ (priorK n : ℝ)⁻¹ := by positivity
    nlinarith
  have hc := Real.neg_one_le_cos
    ((i : ℝ) * Real.pi / ((priorK n - 1 : ℕ) : ℝ))
  unfold interpolationNode
  nlinarith

-- @node: latentWeight_node_pos
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `i`](hyp:i). -/
lemma latentWeight_node_pos (n : ℕ) (i : Fin (priorK n)) :
    0 < interpolationNode n i := by
  have hk : (0 : ℝ) < priorK n := by
    have he : (0 : ℝ) < ell n := by
      unfold ell
      apply Real.log_pos
      have h := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
      exact lt_of_lt_of_le h (le_add_of_nonneg_right (Nat.cast_nonneg _))
    have hc : 8 * ell n ≤ (priorK n : ℝ) := Nat.le_ceil _
    linarith
  have hh : 0 < priorH n := by
    unfold priorH
    positivity
  exact lt_of_lt_of_le hh (latentWeight_node_lower n i)

-- @node: latentWeight_signed_total_le_one
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma latentWeight_signed_total_le_one (n : ℕ) :
    (∑ i : Fin (priorK n), |signedNodeWeight n i|) ≤ 1 := by
  have hnorm : 0 ≤ lagrangeNorm n := by
    unfold lagrangeNorm
    positivity
  by_cases hz : lagrangeNorm n = 0
  · simp [signedNodeWeight, hz]
  · have hp : 0 < lagrangeNorm n := lt_of_le_of_ne hnorm (Ne.symm hz)
    simp only [signedNodeWeight, abs_div, abs_of_nonneg hnorm, ← Finset.sum_div]
    rw [show (∑ i : Fin (priorK n), |lagrangeAtZero n i|) = lagrangeNorm n by
      rfl]
    simp [hz]

/-- For [a sample size of at least one](hyp:hn), [a positive dimension](hyp:hd), and [an admissible arrival floor](hyp:hq), [the latent weights sum to one](goal). -/
lemma latentWeight_sum (n d : ℕ) (q : ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    ∑ z : Latent n, ENNReal.ofReal (latentWeight n z) = 1 := by
  classical
  have hterm (i : Fin (priorK n)) :
      0 ≤ priorH n * |signedNodeWeight n i| / interpolationNode n i := by
    exact div_nonneg (mul_nonneg (by unfold priorH; positivity) (abs_nonneg _))
      (le_of_lt (latentWeight_node_pos n i))
  have hbound (i : Fin (priorK n)) :
      priorH n * |signedNodeWeight n i| / interpolationNode n i ≤
        |signedNodeWeight n i| := by
    apply (div_le_iff₀ (latentWeight_node_pos n i)).mpr
    nlinarith [latentWeight_node_lower n i, abs_nonneg (signedNodeWeight n i)]
  have hsum :
      (∑ i : Fin (priorK n),
        priorH n * |signedNodeWeight n i| / interpolationNode n i) ≤ 1 := by
    calc
      _ ≤ ∑ i : Fin (priorK n), |signedNodeWeight n i| :=
        Finset.sum_le_sum (fun i _ => hbound i)
      _ ≤ 1 := latentWeight_signed_total_le_one n
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, latentWeight]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hterm i)]
  rw [← ENNReal.ofReal_add
    (Finset.sum_nonneg (fun i _ => hterm i)) (sub_nonneg.mpr hsum)]
  simp

/-- Probability law of one latent pair, including the residual atom. -/
noncomputable def oneLatentLaw (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) : PMF (Latent n) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (latentWeight n z))
    (latentWeight_sum n d q hn hd hq)

/-- Latent draws and independent fair orientation signs for all pairs. -/
abbrev Theta (n d : ℕ) := (Fin (pairCount n d) → Latent n) ×
  (Fin (pairCount n d) → Bool)

/-- Product weight of all independent pair draws and fair signs. -/
noncomputable def thetaWeight (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (θ : Theta n d) : ℝ≥0∞ :=
  ∏ j : Fin (pairCount n d),
    oneLatentLaw n d q hn hd hq (θ.1 j) * (1 / 2 : ℝ≥0∞)

/-- For [a sample size of at least one](hyp:hn), [a positive dimension](hyp:hd), and [an admissible arrival floor](hyp:hq), [the joint weights of latent draws and orientations sum to one](goal). -/
lemma thetaWeight_sum (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    ∑ θ : Theta n d, thetaWeight n d q hn hd hq θ = 1 := by
  classical
  simp only [thetaWeight, Fintype.sum_prod_type, Finset.prod_mul_distrib]
  rw [← Fintype.sum_mul_sum]
  simp only [← Fintype.prod_sum]
  have hlat : (∑ z : Latent n, oneLatentLaw n d q hn hd hq z) = 1 := by
    simpa using (oneLatentLaw n d q hn hd hq).tsum_coe
  rw [hlat]
  simp only [Finset.prod_const_one, one_div, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, Fintype.card_pi, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, one_mul]
  rw [← mul_pow]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  simp

/-- For [a sample size](hyp:n), [a positive dimension](hyp:hd), and [an admissible arrival floor](hyp:hq), [the probability law of all latent draws and orientations is defined](goal). -/
noncomputable def thetaLaw (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) : PMF (Theta n d) :=
  PMF.ofFintype (thetaWeight n d q hn hd hq)
    (thetaWeight_sum n d q hn hd hq)

/-- Exact random total mass of the unnormalized filler and pair labels. -/
noncomputable def normalizationJ (n d : ℕ) (θ : Theta n d) : ℝ :=
  fillerMass n d + 2 * ∑ j : Fin (pairCount n d), latentP n (θ.1 j)

/-- The two orientations at a pair are opposite. -/
def orientation (θ : Theta n d) (j : Fin (pairCount n d)) (side : Bool) : ℝ :=
  if θ.2 j == side then 1 else -1

/-- Treatment arrival probability in one oriented pair under sign `σ`. -/
noncomputable def pairRho (q σ z u : ℝ) : ℝ :=
  1 - delta q / 2 * (1 + σ * z * u)
  -- @realizes rho(pair arrival probability 1-delta(1+sigma z u)/2)

/-- Treatment outcome mean at one pair label. -/
noncomputable def pairMu (q σ z u : ℝ) : ℝ :=
  ((1 - delta q / 2) / 2 + u / 16) / pairRho q σ z u
  -- @realizes mu(pair outcome mean (b/2+c0 u)/rho)

/-- For [a sample size](hyp:n) and [a positive dimension](hyp:hd), [the pair labels and filler label fit within the available covariate labels](goal). -/
lemma pair_labels_fit (n d : ℕ) (hd : 1 ≤ d) :
    2 * pairCount n d + 1 ≤ d := by
  have h : pairCount n d ≤ (d - 1) / 2 := by
    unfold pairCount
    exact min_le_left _ _
  omega

/-- The filler has label zero. -/
def fillerLabel (d : ℕ) (hd : 1 ≤ d) : Fin d := ⟨0, hd⟩

/-- For [a pair index](hyp:j), [a side of that pair](hyp:side), and [a positive dimension](hyp:hd), [the corresponding pair label is strictly below the dimension](goal). -/
lemma pairLabel_lt (n d : ℕ) (hd : 1 ≤ d)
    (j : Fin (pairCount n d)) (side : Bool) :
    2 * j.val + (if side then 1 else 2) < d := by
  have h := pair_labels_fit n d hd
  have hj := j.isLt
  split <;> omega

/-- Pair labels occupy the next `2M` positions. -/
def pairLabel (n d : ℕ) (hd : 1 ≤ d)
    (j : Fin (pairCount n d)) (side : Bool) : Fin d :=
  ⟨2 * j.val + (if side then 1 else 2), pairLabel_lt n d hd j side⟩

-- @node: pairLabel_injective
/-- A pair index and orientation determine a unique baseline label. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `side`](hyp:side), [the specified input `side'`](hyp:side'), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j), [the specified input `k`](hyp:k). -/
lemma pairLabel_injective (n d : ℕ) (hd : 1 ≤ d)
    (j k : Fin (pairCount n d)) (side side' : Bool)
    (h : pairLabel n d hd j side = pairLabel n d hd k side') :
    j = k ∧ side = side' := by
  have hv : 2 * j.val + (if side then 1 else 2) =
      2 * k.val + (if side' then 1 else 2) := congrArg Fin.val h
  cases side <;> cases side' <;> simp_all [pairLabel] <;> omega

-- @node: fillerLabel_ne_pairLabel
/-- The filler label is disjoint from every paired label. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `side`](hyp:side), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
lemma fillerLabel_ne_pairLabel (n d : ℕ) (hd : 1 ≤ d)
    (j : Fin (pairCount n d)) (side : Bool) :
    fillerLabel d hd ≠ pairLabel n d hd j side := by
  intro h
  have hv := congrArg Fin.val h
  cases side <;> simp [fillerLabel, pairLabel] at hv

/-- Bernoulli factor, totalized by the real arithmetic of the displayed model. -/
def bernoulliFactor (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

-- @node: bernoulliFactor_sum
/-- Given [the specified input `p`](hyp:p), [the stated mathematical conclusion holds](goal). -/
lemma bernoulliFactor_sum (p : ℝ) :
    ∑ b : Bool, bernoulliFactor p b = 1 := by
  simp [bernoulliFactor]

-- @node: bernoulliFactor_nonneg
/-- Given [the specified input `p`](hyp:p), [the specified input `hp`](hyp:hp), [the specified input `b`](hyp:b), [the stated mathematical conclusion holds](goal). -/
lemma bernoulliFactor_nonneg (p : ℝ) (hp : p ∈ Set.Icc 0 1) (b : Bool) :
    0 ≤ bernoulliFactor p b := by
  rcases hp with ⟨h0, h1⟩
  cases b <;> simp [bernoulliFactor] <;> linarith

-- @node: pairRho_mem_unit
/-- Given [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `u`](hyp:u), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `hq`](hyp:hq), [the specified input `ht`](hyp:ht). -/
lemma pairRho_mem_unit (q σ z u : ℝ) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (ht : σ * z * u ∈ Set.Icc (-1) 1) : pairRho q σ z u ∈ Set.Icc q 1 := by
  rcases hq with ⟨hq0, hq1⟩
  rcases ht with ⟨ht0, ht1⟩
  unfold pairRho delta
  constructor <;> nlinarith

-- @node: pairMu_mem_unit
/-- Given [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `u`](hyp:u), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `hq`](hyp:hq), [the specified input `hu`](hyp:hu), [the specified input `ht`](hyp:ht). -/
lemma pairMu_mem_unit (q σ z u : ℝ) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hu : u ∈ Set.Icc (-1) 1) (ht : σ * z * u ∈ Set.Icc (-1) 1) :
    pairMu q σ z u ∈ Set.Icc 0 1 := by
  have hρ := pairRho_mem_unit q σ z u hq ht
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq.1
  have hρpos : 0 < pairRho q σ z u := lt_of_lt_of_le hqpos hρ.1
  unfold pairMu
  constructor
  · apply div_nonneg
    · rcases hq with ⟨hq0, hq1⟩
      rcases hu with ⟨hu0, hu1⟩
      unfold delta
      linarith
    · exact le_of_lt hρpos
  · apply (div_le_iff₀ hρpos).mpr
    rcases hq with ⟨hq0, hq1⟩
    rcases hu with ⟨hu0, hu1⟩
    unfold delta
    linarith [hρ.1]

-- @node: latentZ_abs_one
/-- Given [the specified input `n`](hyp:n), [the specified input `z`](hyp:z), [the stated mathematical conclusion holds](goal). -/
lemma latentZ_abs_one (n : ℕ) (z : Latent n) : |latentZ n z| = 1 := by
  cases z with
  | inl i => simp only [latentZ]; split_ifs <;> norm_num
  | inr _ => simp [latentZ]

-- @node: orientation_abs_one
/-- Given [the specified input `side`](hyp:side), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j). -/
lemma orientation_abs_one (θ : Theta n d) (j : Fin (pairCount n d)) (side : Bool) :
    |orientation θ j side| = 1 := by
  simp only [orientation]
  split_ifs <;> norm_num

-- @node: pair_sign_mem_unit
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `side`](hyp:side), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `hσ`](hyp:hσ), [the specified input `j`](hyp:j). -/
lemma pair_sign_mem_unit (n d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-1) 1)
    (θ : Theta n d) (j : Fin (pairCount n d)) (side : Bool) :
    σ * latentZ n (θ.1 j) * orientation θ j side ∈ Set.Icc (-1) 1 := by
  have hz := latentZ_abs_one n (θ.1 j)
  have hu := orientation_abs_one θ j side
  have habsσ : |σ| ≤ 1 := abs_le.mpr hσ
  have habs : |σ * latentZ n (θ.1 j) * orientation θ j side| ≤ 1 := by
    rw [abs_mul, abs_mul, hz, hu]
    simpa using habsσ
  exact abs_le.mp habs

/-- Full atom mass at an oriented pair label, before normalization. -/
noncomputable def pairAtomWeight (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (j : Fin (pairCount n d)) (side : Bool)
    (w : FullAtom d) : ℝ :=
  if w.X = pairLabel n d hd j side ∧ w.S0 = false ∧ w.S1 = false ∧
      w.S = false ∧ w.Y0 = false ∧ w.Y = (if w.A then w.Y1 else w.Y0) then
    let p := latentP n (θ.1 j)
    let z := latentZ n (θ.1 j)
    let u := orientation θ j side
    let ρ := pairRho q σ z u
    let μ := pairMu q σ z u
    p / normalizationJ n d θ / 2 *
      bernoulliFactor μ w.Y1 *
      (if w.A then bernoulliFactor ρ w.R else if w.R then 1 else 0)
  else 0

-- @node: pairAtomWeight_other_pair_zero
/-- A paired component puts no mass on another pair's baseline label. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `side`](hyp:side), [the specified input `side'`](hyp:side'), [the specified input `w`](hyp:w), [the specified input `hw`](hyp:hw), [the specified input `hne`](hyp:hne), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j), [the specified input `k`](hyp:k). -/
lemma pairAtomWeight_other_pair_zero (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (j k : Fin (pairCount n d)) (side side' : Bool)
    (w : FullAtom d) (hw : w.X = pairLabel n d hd k side')
    (hne : j ≠ k ∨ side ≠ side') :
    pairAtomWeight n d q σ hd θ j side w = 0 := by
  have hx : w.X ≠ pairLabel n d hd j side := by
    intro heq
    obtain ⟨hjk, hside⟩ := pairLabel_injective n d hd k j side' side (hw.symm.trans heq)
    exact hne.elim (fun h => h hjk.symm) (fun h => h hside.symm)
  simp [pairAtomWeight, hx]

-- @node: latentP_nonneg
/-- Given [the specified input `n`](hyp:n), [the specified input `z`](hyp:z), [the stated mathematical conclusion holds](goal). -/
lemma latentP_nonneg (n : ℕ) (z : Latent n) : 0 ≤ latentP n z := by
  cases z with
  | inl i =>
      simp only [latentP]
      exact mul_nonneg (by unfold priorB; positivity)
        (le_trans (by unfold priorH; positivity) (latentWeight_node_lower n i))
  | inr _ => simp [latentP]

-- @node: pairAtomWeight_nonneg
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `hJ`](hyp:hJ), [the specified input `side`](hyp:side), [the specified input `w`](hyp:w), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `hq`](hyp:hq), [the specified input `hσ`](hyp:hσ), [the specified input `j`](hyp:j). -/
lemma pairAtomWeight_nonneg (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (hσ : σ ∈ Set.Icc (-1) 1)
    (θ : Theta n d) (hJ : 0 < normalizationJ n d θ)
    (j : Fin (pairCount n d)) (side : Bool) (w : FullAtom d) :
    0 ≤ pairAtomWeight n d q σ hd θ j side w := by
  by_cases h : w.X = pairLabel n d hd j side ∧ w.S0 = false ∧ w.S1 = false ∧
      w.S = false ∧ w.Y0 = false ∧ w.Y = (if w.A then w.Y1 else w.Y0)
  · simp only [pairAtomWeight, if_pos h]
    have hu : orientation θ j side ∈ Set.Icc (-1) 1 :=
      abs_le.mp (by rw [orientation_abs_one])
    have ht := pair_sign_mem_unit n d σ hσ θ j side
    have hμ := pairMu_mem_unit q σ (latentZ n (θ.1 j))
      (orientation θ j side) hq hu ht
    have hρ := pairRho_mem_unit q σ (latentZ n (θ.1 j))
      (orientation θ j side) hq ht
    have hq0 : 0 ≤ q := le_trans (by norm_num) hq.1
    have hlast : 0 ≤ (if w.A then
        bernoulliFactor (pairRho q σ (latentZ n (θ.1 j)) (orientation θ j side)) w.R
      else if w.R then (1 : ℝ) else 0) := by
      split_ifs <;> try positivity
      exact bernoulliFactor_nonneg _ ⟨hq0.trans hρ.1, hρ.2⟩ _
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg (div_nonneg (latentP_nonneg n (θ.1 j)) (le_of_lt hJ))
          (by norm_num))
        (bernoulliFactor_nonneg _ hμ _)) hlast
  · simp only [pairAtomWeight, if_neg h]
    norm_num

/-- Full atom mass at the fixed filler label, before normalization. -/
noncomputable def fillerAtomWeight (n d : ℕ) (q : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (w : FullAtom d) : ℝ :=
  if w.X = fillerLabel d hd ∧ w.S0 = false ∧ w.S1 = false ∧
      w.S = false ∧ w.Y0 = false ∧ w.Y = (if w.A then w.Y1 else w.Y0) ∧
      w.R = true then
    fillerMass n d / normalizationJ n d θ / 2 *
      bernoulliFactor (baseMean q) w.Y1
  else 0

-- @node: fillerAtomWeight_pair_zero
/-- The filler component puts no mass on a paired baseline label. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `side`](hyp:side), [the specified input `w`](hyp:w), [the specified input `hw`](hyp:hw), [the stated mathematical conclusion holds](goal). Given [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j). -/
lemma fillerAtomWeight_pair_zero (n d : ℕ) (q : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (j : Fin (pairCount n d)) (side : Bool)
    (w : FullAtom d) (hw : w.X = pairLabel n d hd j side) :
    fillerAtomWeight n d q hd θ w = 0 := by
  have hx : w.X ≠ fillerLabel d hd := by
    rw [hw]
    exact (fillerLabel_ne_pairLabel n d hd j side).symm
  simp [fillerAtomWeight, hx]

-- @node: pairAtomWeight_filler_zero
/-- Every paired component puts no mass on the filler baseline label. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `side`](hyp:side), [the specified input `w`](hyp:w), [the specified input `hw`](hyp:hw), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j). -/
lemma pairAtomWeight_filler_zero (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (j : Fin (pairCount n d)) (side : Bool)
    (w : FullAtom d) (hw : w.X = fillerLabel d hd) :
    pairAtomWeight n d q σ hd θ j side w = 0 := by
  have hx : w.X ≠ pairLabel n d hd j side := by
    rw [hw]
    exact fillerLabel_ne_pairLabel n d hd j side
  simp [pairAtomWeight, hx]

/-- Exact mass of a normalized causal full-data atom. -/
noncomputable def pairedAtomWeight (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (w : FullAtom d) : ℝ :=
  fillerAtomWeight n d q hd θ w +
    ∑ j : Fin (pairCount n d), ∑ side : Bool,
      pairAtomWeight n d q σ hd θ j side w


end CausalSmith.Stat.MarNearcompleteFrontier
