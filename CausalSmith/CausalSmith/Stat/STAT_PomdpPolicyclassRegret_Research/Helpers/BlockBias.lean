module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockPhiwMoments
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.Kernels
public import Causalean.Mathlib.Probability.FiniteMarkovOscillation

/-!
# Arbitrary-start finite-state PHIW bias

This module proves the deterministic transient estimate in equations (2)--(4)
of the block moment roadmap. Forward finite-state iteration uses the library's
structural Markov iteration; the pathwise change-of-measure identity remains a
separate obligation.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
  (markovIterate markovStep IsStochasticMatrix)
open MeasureTheory
open scoped BigOperators

/-- Any two probability vectors have total-variation distance at most one. For
[the index subset](hyp:S), [the policy](hyp:p), [the q](hyp:q), [the policy assumption](hyp:hp),
and [the q assumption](hyp:hq), this establishes
[the partial-history importance-weighted probability tv bound one result](goal). -/
-- @node: phiw_probability_tv_le_one
lemma phiw_probability_tv_le_one {S : Type*} [Fintype S]
    (p q : S → ℝ) (hp : ProbabilityVector p) (hq : ProbabilityVector q) :
    tvNorm (p - q) ≤ 1 := by
  have hsum : (∑ s, |p s - q s|) ≤ 2 := by
    calc
      _ ≤ ∑ s, (p s + q s) := Finset.sum_le_sum fun s _ ↦
        (abs_sub (p s) (q s)).trans_eq
          (by rw [abs_of_nonneg (hp.1 s), abs_of_nonneg (hq.1 s)])
      _ = 2 := by rw [Finset.sum_add_distrib, hp.2, hq.2]; norm_num
  dsimp [tvNorm]
  linarith

/-- Total variation satisfies the triangle inequality for finite vectors. For
[the index subset](hyp:S), [the policy](hyp:p), [the q](hyp:q), and [the code dimension](hyp:d),
this establishes [the partial-history importance-weighted tv triangle result](goal). -/
-- @node: phiw_tv_triangle
lemma phiw_tv_triangle {S : Type*} [Fintype S] (p q d : S → ℝ) :
    tvNorm (p - d) ≤ tvNorm (p - q) + tvNorm (q - d) := by
  have hsum : (∑ s, |p s - d s|) ≤
      (∑ s, |p s - q s|) + ∑ s, |q s - d s| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    exact abs_sub_le (p s) (q s) (d s)
  dsimp [tvNorm]
  linarith

/-- A stationary law is fixed by every structural forward iterate. For
[the index subset](hyp:S), [the probability law](hyp:P), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), and [the sample size](hyp:n), this establishes
[the partial-history importance-weighted markov iterate stationary result](goal). -/
-- @node: phiw_markovIterate_stationary
lemma phiw_markovIterate_stationary {S : Type*} [Fintype S]
    (P : S → S → ℝ) (d : S → ℝ) (hd : IsStationary P d) (n : Nat) :
    markovIterate P d n = d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change markovStep (markovIterate P d n) P = d
    rw [ih]
    funext s
    exact hd.2 s

/-- One-step total-variation contraction iterates with the geometric factor. For
[the index subset](hyp:S), [the probability law](hyp:P),
[the probability law assumption](hyp:hP), [the contraction coefficient](hyp:α),
[the contraction coefficient assumption](hyp:hα), [the c assumption](hyp:hc),
[the policy](hyp:p), [the q](hyp:q), [the policy assumption](hyp:hp),
[the q assumption](hyp:hq), and [the sample size](hyp:n), this establishes
[the partial-history importance-weighted markov iterate contraction result](goal). -/
-- @node: phiw_markovIterate_contraction
lemma phiw_markovIterate_contraction {S : Type*} [Fintype S]
    (P : S → S → ℝ) (hP : IsStochasticMatrix P) (α : ℝ) (hα : 0 ≤ α)
    (hc : ∀ p q, ProbabilityVector p → ProbabilityVector q →
      tvNorm (applyKernel p P - applyKernel q P) ≤ α * tvNorm (p - q))
    (p q : S → ℝ) (hp : ProbabilityVector p) (hq : ProbabilityVector q) (n : Nat) :
    tvNorm (markovIterate P p n - markovIterate P q n) ≤ α ^ n * tvNorm (p - q) := by
  induction n with
  | zero => simp [markovIterate]
  | succ n ih =>
    calc
      _ ≤ α * tvNorm (markovIterate P p n - markovIterate P q n) :=
        hc _ _ (hP.iterate_probability hp n) (hP.iterate_probability hq n)
      _ ≤ α * (α ^ n * tvNorm (p - q)) := mul_le_mul_of_nonneg_left ih hα
      _ = α ^ (n + 1) * tvNorm (p - q) := by rw [pow_succ]; ring

/-- An arbitrary initial law approaches a stationary law at geometric rate. For
[the index subset](hyp:S), [the probability law](hyp:P),
[the probability law assumption](hyp:hP), [the contraction coefficient](hyp:α),
[the contraction coefficient assumption](hyp:hα), [the c assumption](hyp:hc),
[the initial distribution](hyp:nu), [the code dimension](hyp:d),
[the initial distribution assumption](hyp:hnu), [the code dimension assumption](hyp:hd), and
[the reward symbol](hyp:r), this establishes
[the partial-history importance-weighted markov iterate transient tv result](goal). -/
-- @node: phiw_markovIterate_transient_tv
lemma phiw_markovIterate_transient_tv {S : Type*} [Fintype S]
    (P : S → S → ℝ) (hP : IsStochasticMatrix P) (α : ℝ) (hα : 0 ≤ α)
    (hc : ∀ p q, ProbabilityVector p → ProbabilityVector q →
      tvNorm (applyKernel p P - applyKernel q P) ≤ α * tvNorm (p - q))
    (nu d : S → ℝ) (hnu : ProbabilityVector nu) (hd : IsStationary P d) (r : Nat) :
    tvNorm (markovIterate P nu r - d) ≤ α ^ r := by
  have h := phiw_markovIterate_contraction P hP α hα hc nu d hnu hd.1 r
  rw [phiw_markovIterate_stationary P d hd r] at h
  calc
    _ ≤ α ^ r * tvNorm (nu - d) := h
    _ ≤ α ^ r * 1 := mul_le_mul_of_nonneg_left
      (phiw_probability_tv_le_one nu d hnu hd.1) (pow_nonneg hα r)
    _ = α ^ r := mul_one _

/-- Combining behavior transience, stationary overlap, and target contraction proves the
pointwise expectation bias in equation (4). For [the index subset](hyp:S), [the pb](hyp:Pb),
[the pe](hyp:Pe), [the pb assumption](hyp:hPb), [the pe assumption](hyp:hPe),
[the contraction coefficient](hyp:α), [the q](hyp:q),
[the contraction coefficient assumption](hyp:hα), [the cb assumption](hyp:hcb),
[the ce assumption](hyp:hce), [the initial distribution](hyp:nu), [the db](hyp:db),
[the de](hyp:de), [the initial distribution assumption](hyp:hnu), [the db assumption](hyp:hdb),
[the de assumption](hyp:hde), [the overlap assumption](hyp:hoverlap), [the g](hyp:g),
[the g assumption](hyp:hg), [the reward symbol](hyp:r), and [the history length](hyp:k), this
establishes [the partial-history importance-weighted finite state transient bias result](goal). -/
-- @node: phiw_finite_state_transient_bias
lemma phiw_finite_state_transient_bias {S : Type*} [Fintype S] [Nonempty S]
    (Pb Pe : S → S → ℝ) (hPb : IsStochasticMatrix Pb) (hPe : IsStochasticMatrix Pe)
    (α q : ℝ) (hα : 0 ≤ α)
    (hcb : ∀ p q, ProbabilityVector p → ProbabilityVector q →
      tvNorm (applyKernel p Pb - applyKernel q Pb) ≤ α * tvNorm (p - q))
    (hce : ∀ p q, ProbabilityVector p → ProbabilityVector q →
      tvNorm (applyKernel p Pe - applyKernel q Pe) ≤ α * tvNorm (p - q))
    (nu db de : S → ℝ) (hnu : ProbabilityVector nu)
    (hdb : IsStationary Pb db) (hde : IsStationary Pe de)
    (hoverlap : tvNorm (db - de) ≤ q)
    (g : S → ℝ) (hg : ∀ s, g s ∈ Set.Icc (0 : ℝ) 1) (r k : Nat) :
    |(∑ s, markovIterate Pe (markovIterate Pb nu r) k s * g s) -
        ∑ s, de s * g s| ≤ α ^ k * (q + α ^ r) := by
  have hp := hPb.iterate_probability hnu r
  have hdist : tvNorm (markovIterate Pb nu r - de) ≤ q + α ^ r := by
    calc
      _ ≤ tvNorm (markovIterate Pb nu r - db) + tvNorm (db - de) :=
        phiw_tv_triangle _ db de
      _ ≤ α ^ r + q := add_le_add
        (phiw_markovIterate_transient_tv Pb hPb α hα hcb nu db hnu hdb r) hoverlap
      _ = q + α ^ r := add_comm _ _
  have ht := phiw_markovIterate_contraction Pe hPe α hα hce
    (markovIterate Pb nu r) de hp hde.1 k
  rw [phiw_markovIterate_stationary Pe de hde k] at ht
  have hosc : OscillationBound 1 g := by
    intro x y
    exact abs_le.mpr ⟨by linarith [(hg x).1, (hg y).2],
      by linarith [(hg x).2, (hg y).1]⟩
  have hdual := abs_sum_sub_mul_le_oscillation_halfL1
    (hPe.iterate_probability hp k) hde.1 hosc
  have heq : (∑ s, markovIterate Pe (markovIterate Pb nu r) k s * g s) -
      ∑ s, de s * g s =
      ∑ s, (markovIterate Pe (markovIterate Pb nu r) k s - de s) * g s := by
    simp [sub_mul, Finset.sum_sub_distrib]
  rw [heq]
  have hdual' : |∑ s, (markovIterate Pe (markovIterate Pb nu r) k s - de s) * g s| ≤
      tvNorm (markovIterate Pe (markovIterate Pb nu r) k - de) := by
    simpa [tvNorm] using hdual
  exact hdual'.trans (ht.trans (mul_le_mul_of_nonneg_left hdist (pow_nonneg hα k)))

/-- The model-class contraction guarantees an actual target stationary law. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), and [the candidate index](hyp:j), this establishes
[the partial-history importance-weighted list target stationary result](goal). -/
-- @node: phiw_list_target_stationary
lemma phiw_list_target_stationary {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M) :
    IsStationary (listPolicyKernel m (m.Mx.E j)) (listStationaryLaw m (m.Mx.E j)) := by
  apply stationaryLaw_isStationary_of_exists
  apply exists_stationary_of_contraction
    (P := listPolicyKernel m (m.Mx.E j))
    (p0 := listStationaryLaw m m.Mx.b) (alpha := mixingAlpha t0)
  · exact policyKernel_probabilityVector m.Mx.toRawB m.kernel_law _
      (hClass.action_overlap j).1
  · exact hClass.stationary_start.1.1
  · exact Real.exp_nonneg _
  · rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hClass.t0_pos)
  · exact hClass.uniform_contraction j _ (Or.inr rfl)

/-- Stationary overlap in the list model gives precisely the bias radius `q`. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), and [the candidate index](hyp:j), this establishes
[the partial-history importance-weighted list stationary tv result](goal). -/
-- @node: phiw_list_stationary_tv
lemma phiw_list_stationary_tv {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M) :
    tvNorm (listStationaryLaw m m.Mx.b - listStationaryLaw m (m.Mx.E j)) ≤
      overlapRadius C := by
  have hd := phiw_list_target_stationary t0 zeta C m hClass j
  have hb := hClass.stationary_start.1
  have h := stationaryOverlap_l1 (listStationaryLaw m m.Mx.b)
    (listStationaryLaw m (m.Mx.E j)) C hClass.C_ge_one hd.1.1 hb.1.2 hd.1.2
    (hClass.latent_stationary_overlap.2 j).2
  have hsym : (∑ s, |listStationaryLaw m m.Mx.b s -
      listStationaryLaw m (m.Mx.E j) s|) =
      ∑ s, |listStationaryLaw m (m.Mx.E j) s - listStationaryLaw m m.Mx.b s| := by
    apply Finset.sum_congr rfl
    intro s _
    exact abs_sub_comm _ _
  dsimp [tvNorm]
  rw [hsym]
  have hCpos : 0 < C := by linarith [hClass.C_ge_one]
  have hq : overlapRadius C = 1 - 1 / C := by
    unfold overlapRadius
    field_simp
  rw [hq]
  linarith

/-- A probability policy's reward regression lies in the unit interval. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the policy](hyp:p), [the policy assumption](hyp:hp), and [the state](hyp:s), this establishes
[the partial-history importance-weighted list reward regression unit result](goal). -/
-- @node: phiw_list_reward_regression_unit
lemma phiw_list_reward_regression_unit {T M : Nat} (m : ModelIndex T M)
    (p : Policy m.nX) (hp : PolicyVector p) (s : JointState m.nX m.nH) :
    listRewardRegression m p s ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun a _ ↦
      mul_nonneg ((hp s.1).1 a) (phiw_kernel_reward_mean_unit m s a).1
  · calc
      _ ≤ ∑ a : Bool, p s.1 a * 1 := Finset.sum_le_sum fun a _ ↦
        mul_le_mul_of_nonneg_left (phiw_kernel_reward_mean_unit m s a).2 ((hp s.1).1 a)
      _ = 1 := by simpa using (hp s.1).2

/-- The class assumptions yield the arbitrary-start pointwise PHIW bias without any extra
regularity or mixing premises. This is equation (4) after chronological change of measure has
replaced a score by a finite-state mean. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), and [the history length](hyp:k), this establishes
[the partial-history importance-weighted list transient bias result](goal). -/
-- @node: phiw_list_transient_bias
lemma phiw_list_transient_bias {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) (r k : Nat) :
    |(∑ s, markovIterate (listPolicyKernel m (m.Mx.E j))
        (markovIterate (listPolicyKernel m m.Mx.b) nu r) k s *
        listRewardRegression m (m.Mx.E j) s) - policyValue m j| ≤
      mixingAlpha t0 ^ k * (overlapRadius C + mixingAlpha t0 ^ r) := by
  let : Nonempty (JointState m.nX m.nH) :=
    ⟨(⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩)⟩
  have hPb : IsStochasticMatrix (listPolicyKernel m m.Mx.b) := by
    have h := policyKernel_probabilityVector m.Mx.toRawB m.kernel_law
      m.Mx.b hClass.sequential_ignorability.1
    exact ⟨fun s s' ↦ (h s).1 s', fun s ↦ (h s).2⟩
  have hPe : IsStochasticMatrix (listPolicyKernel m (m.Mx.E j)) := by
    have h := policyKernel_probabilityVector m.Mx.toRawB m.kernel_law
      (m.Mx.E j) (hClass.action_overlap j).1
    exact ⟨fun s s' ↦ (h s).1 s', fun s ↦ (h s).2⟩
  exact phiw_finite_state_transient_bias _ _ hPb hPe _ _ (Real.exp_nonneg _)
    (hClass.uniform_contraction j _ (Or.inl rfl))
    (hClass.uniform_contraction j _ (Or.inr rfl)) nu _ _ hnu
    hClass.stationary_start.1 (phiw_list_target_stationary t0 zeta C m hClass j)
    (phiw_list_stationary_tv t0 zeta C m hClass j) _
    (phiw_list_reward_regression_unit m _ (hClass.action_overlap j).1) r k

/-- Averaging the finite-state score means gives the full block bias bound in equation (5);
identifying these means with trajectory integrals is the remaining change-of-measure step. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the effective sample size](hyp:N), [the history length](hyp:k), and
[the effective sample size assumption](hyp:hN), this establishes
[the partial-history importance-weighted list average transient bias result](goal). -/
-- @node: phiw_list_average_transient_bias
lemma phiw_list_average_transient_bias {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (N k : Nat) (hN : 0 < N) :
    |(∑ r ∈ Finset.range N, ∑ s,
        markovIterate (listPolicyKernel m (m.Mx.E j))
          (markovIterate (listPolicyKernel m m.Mx.b) nu r) k s *
          listRewardRegression m (m.Mx.E j) s) / (N : ℝ) - policyValue m j| ≤
      mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((N : ℝ) * (1 - mixingAlpha t0))) := by
  apply phiw_average_bias_of_pointwise N k hN _ _ _ (Real.exp_nonneg _)
  · rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hClass.t0_pos)
  · intro r _
    exact phiw_list_transient_bias t0 zeta C m hClass j nu hnu r k

end CausalSmith.Stat.PomdpPolicyclassRegret
