module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.Kernels
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences

/-! # Stationary laws of finite stochastic kernels -/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators Topology
open Filter

/-- Adding a positive refresh probability gives a stationary probability vector. For
[the index subset](hyp:S), [the probability law](hyp:P),
[the probability law assumption](hyp:hP), [the initial distribution](hyp:nu),
[the initial distribution assumption](hyp:hnu), [the action](hyp:a),
[the a0 assumption](hyp:ha0), and [the a1 assumption](hyp:ha1), this establishes
[the finite refresh stationary result](goal). -/
-- @node: finite_refresh_stationary
lemma finite_refresh_stationary {S : Type*} [Fintype S]
    (P : S → S → ℝ) (hP : ∀ s, ProbabilityVector (P s))
    (nu : S → ℝ) (hnu : ProbabilityVector nu)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∃ d, IsStationary (fun s s' ↦ (1 - a) * nu s' + a * P s s') d := by
  refine exists_stationary_of_contraction _ ?_ nu hnu a ha0 ha1 ?_
  · intro s
    constructor
    · intro s'
      exact add_nonneg (mul_nonneg (by linarith) (hnu.1 s'))
        (mul_nonneg ha0 ((hP s).1 s'))
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hnu.2, (hP s).2]
      ring
  · exact tvNorm_contraction_of_refresh a ha0 nu P hP

/-- Finite stochastic kernels have stationary laws, by compactness and vanishing refresh. For
[the index subset](hyp:S), [the probability law](hyp:P), and
[the probability law assumption](hyp:hP), this establishes
[the finite stochastic stationary exists result](goal). -/
-- @node: finite_stochastic_stationary_exists
lemma finite_stochastic_stationary_exists {S : Type*} [Fintype S] [Nonempty S]
    (P : S → S → ℝ) (hP : ∀ s, ProbabilityVector (P s)) :
    ∃ d, IsStationary P d := by
  classical
  let s0 : S := Classical.choice inferInstance
  let nu : S → ℝ := fun s ↦ if s = s0 then 1 else 0
  have hnu : ProbabilityVector nu := by
    constructor
    · intro s; dsimp [nu]; split_ifs <;> norm_num
    · simp [nu]
  let a : ℕ → ℝ := fun n ↦ (n : ℝ) / (n + 1)
  have ha0 (n) : 0 ≤ a n := by dsimp [a]; positivity
  have ha1 (n) : a n < 1 := by
    dsimp [a]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  choose d hd using fun n ↦ finite_refresh_stationary P hP nu hnu (a n) (ha0 n) (ha1 n)
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (isCompact_stdSimplex ℝ S).tendsto_subseq
    (fun n ↦ show d n ∈ stdSimplex ℝ S from (hd n).1)
  refine ⟨v, hv, ?_⟩
  have halim : Tendsto (a ∘ φ) atTop (𝓝 1) :=
    (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1).comp hφ.tendsto_atTop
  intro s'
  have hleft : Tendsto (fun n ↦ ∑ s, d (φ n) s *
      ((1 - a (φ n)) * nu s' + a (φ n) * P s s')) atTop
      (𝓝 (∑ s, v s * P s s')) := by
    apply tendsto_finsetSum
    intro s _
    have hs := (continuous_apply s).tendsto v |>.comp hlim
    simpa using hs.mul ((((tendsto_const_nhds (x := (1 : ℝ))).sub halim).mul
      (tendsto_const_nhds (x := nu s'))).add
      (halim.mul (tendsto_const_nhds (x := P s s'))))
  have hright : Tendsto (fun n ↦ d (φ n) s') atTop (𝓝 (v s')) :=
    (continuous_apply s').tendsto v |>.comp hlim
  exact tendsto_nhds_unique hleft (hright.congr (fun n ↦ ((hd (φ n)).2 s').symm))

end CausalSmith.Stat.PomdpPolicyclassRegret
