/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.NormedSpace.FiniteNets
public import Causalean.Mathlib.MeasureTheory.SupCountableDense
public import Causalean.Stat.Concentration.Covering.DudleyEntropy
public import Causalean.Stat.Concentration.Covering.SqrtLogIntegral

/-! # Entropy bounds for finite-dimensional Lipschitz parameter classes

This module compares empirical score metrics with Euclidean parameter distance and derives
the resulting finite-dimensional covering-number and Dudley-entropy bounds.
-/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal

open Causalean.Mathlib.Analysis.NormedSpace

namespace Causalean.Stat

open Causalean.Stat.Concentration

@[expose] public section

/-- The [chosen countable dense sequence in a closed ball](goal) is obtained
from the ambient separability sequence for the ball with [center](hyp:θ₀) and
[nonnegative radius](hyp:hδ). -/
noncomputable def closedBallDenseSeq
    {E : Type*} [PseudoMetricSpace E] [SecondCountableTopology E]
    (θ₀ : E) {δ : ℝ} (hδ : 0 ≤ δ) : ℕ → Metric.closedBall θ₀ δ := by
  letI : Nonempty (Metric.closedBall θ₀ δ) :=
    ⟨⟨θ₀, by simpa [Metric.mem_closedBall] using hδ⟩⟩
  exact denseSeq (Metric.closedBall θ₀ δ)

/-- [The empirical norm of a scalar function is at most the scaled empirical
envelope norm](goal) on [a finite sample](hyp:S), whenever [the
function](hyp:f) is [pointwise dominated](hyp:hf) by [a nonnegative
envelope](hyp:L,hL) times [a nonnegative scale](hyp:a,ha). -/
lemma empiricalNorm_le_mul
    {X : Type*} {n : ℕ} (S : Fin n → X) (f L : X → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hL : ∀ x, 0 ≤ L x)
    (hf : ∀ x, |f x| ≤ a * L x) :
    Concentration.empiricalNorm S f ≤ a * Concentration.empiricalNorm S L := by
  unfold Concentration.empiricalNorm
  rw [← Real.sqrt_sq ha]
  rw [← Real.sqrt_mul (sq_nonneg a)]
  apply Real.sqrt_le_sqrt
  have hsum : (∑ i : Fin n, f (S i) ^ 2) ≤
      ∑ i : Fin n, (a * L (S i)) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg ha (hL (S i)))]
    exact hf (S i)
  calc
    1 / (n : ℝ) * ∑ i : Fin n, f (S i) ^ 2
        ≤ 1 / (n : ℝ) * ∑ i : Fin n, (a * L (S i)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = a ^ 2 * (1 / (n : ℝ) * ∑ i : Fin n, L (S i) ^ 2) := by
      simp_rw [mul_pow, ← Finset.mul_sum]
      ring

/-- [A finite-dimensional closed ball has an internal finite net with the
standard volumetric cardinality bound](goal), for the ball with
[center](hyp:θ₀) and [nonnegative radius](hyp:hδ) at [any positive net
scale](hyp:r,hr). -/
lemma exists_closedBall_net_card_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (θ₀ : E) {δ r : ℝ} (hδ : 0 ≤ δ) (hr : 0 < r) :
    ∃ N : Finset E,
      (∀ η ∈ N, η ∈ Metric.closedBall θ₀ δ) ∧
      (∀ θ ∈ Metric.closedBall θ₀ δ, ∃ η ∈ N, ‖θ - η‖ < r) ∧
      (N.card : ℝ) ≤ (1 + 4 * δ / r) ^ Module.finrank ℝ E := by
  classical
  by_cases hδ0 : δ = 0
  · subst δ
    refine ⟨{θ₀}, ?_, ?_, ?_⟩
    · intro η hη
      simpa [Metric.mem_closedBall] using hη
    · intro θ hθ
      have hθeq : θ = θ₀ := by
        simpa [Metric.mem_closedBall] using hθ
      subst θ
      exact ⟨θ₀, by simp, by simpa using hr⟩
    · simp
  · have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
    let v : ℝ := r / (2 * δ)
    have hv : 0 < v := div_pos hr (mul_pos (by norm_num) hδpos)
    obtain ⟨M, hMsub, hMcover, hMcard⟩ :=
      exists_internal_net_card_le E {x : E | ‖x‖ ≤ 1} (by simp) hv
    let N : Finset E := M.image (fun y => θ₀ + δ • y)
    refine ⟨N, ?_, ?_, ?_⟩
    · intro η hη
      obtain ⟨y, hyM, rfl⟩ := Finset.mem_image.mp hη
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
      simpa using mul_le_mul_of_nonneg_left (hMsub y hyM) hδ
    · intro θ hθ
      let x : E := δ⁻¹ • (θ - θ₀)
      have hx : ‖x‖ ≤ 1 := by
        dsimp [x]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδpos]
        have hθnorm : ‖θ - θ₀‖ ≤ δ := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hθ
        rw [inv_mul_le_one₀ hδpos]
        exact hθnorm
      obtain ⟨y, hyM, hxy⟩ := hMcover x hx
      refine ⟨θ₀ + δ • y, Finset.mem_image.mpr ⟨y, hyM, rfl⟩, ?_⟩
      have hscale : θ = θ₀ + δ • x := by
        dsimp [x]
        rw [smul_smul, mul_inv_cancel₀ hδ0, one_smul]
        abel
      rw [hscale]
      have hnorm : ‖δ • (x - y)‖ ≤ δ * v := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
        exact mul_le_mul_of_nonneg_left hxy hδ
      have hdr : δ * v = r / 2 := by
        dsimp [v]
        field_simp
      calc
        ‖θ₀ + δ • x - (θ₀ + δ • y)‖ = ‖δ • (x - y)‖ := by
          congr 1
          module
        _ ≤ δ * v := hnorm
        _ = r / 2 := hdr
        _ < r := by linarith
    · calc
        (N.card : ℝ) ≤ (M.card : ℝ) := by exact_mod_cast Finset.card_image_le
        _ ≤ (1 + 2 / v) ^ Module.finrank ℝ E := hMcard
        _ = (1 + 4 * δ / r) ^ Module.finrank ℝ E := by
          congr 1
          dsimp [v]
          field_simp
          ring

/-- [The empirical distance between two class members is bounded by their
parameter distance times the empirical envelope norm](goal) on [a
sample](hyp:S).  The [scalar class](hyp:F) must obey [a Lipschitz bound](hyp:hLip)
with [nonnegative envelope](hyp:L,hL) throughout the ball with [center and
radius](hyp:θ₀,δ), and the [two parameters](hyp:θ,hθ,η,hη) must lie in
that ball. -/
lemma parametric_empiricalDist_le
    {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (S : Fin n → X) (F : E → X → ℝ) (L : X → ℝ)
    (hL : ∀ x, 0 ≤ L x)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ x,
      |F θ x - F η x| ≤ L x * ‖θ - η‖)
    (θ : E) (hθ : θ ∈ Metric.closedBall θ₀ δ)
    (η : E) (hη : η ∈ Metric.closedBall θ₀ δ) :
    Concentration.empiricalDist S (F θ) (F η) ≤
      ‖θ - η‖ * Concentration.empiricalNorm S L := by
  rw [Concentration.empiricalDist_def]
  apply empiricalNorm_le_mul S (F θ - F η) L ‖θ - η‖ (norm_nonneg _) hL
  intro x
  simpa [Pi.sub_apply, mul_comm] using hLip θ hθ η hη x

/-- [A scalar function class indexed by a finite-dimensional closed ball is
totally bounded in the empirical metric](goal) on [a sample](hyp:S), when [the
class](hyp:F) has [a nonnegative envelope](hyp:L,hL) and obeys [the corresponding
Lipschitz bound](hyp:hLip) on the ball with [center](hyp:θ₀),
[radius](hyp:δ), and [nonnegative radius proof](hyp:hδ). -/
lemma parametric_empirical_totallyBounded
    {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {n : ℕ} (S : Fin n → X) (F : E → X → ℝ) (L : X → ℝ)
    (hL : ∀ x, 0 ≤ L x)
    (θ₀ : E) (δ : ℝ)
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ x,
      |F θ x - F η x| ≤ L x * ‖θ - η‖)
    (hδ : 0 ≤ δ) :
    let ι := Metric.closedBall θ₀ δ
    TotallyBounded (Set.univ : Set (Concentration.EmpiricalFunctionSpace
      (fun θ : ι => F θ.1) S)) := by
  dsimp only
  classical
  rw [Metric.totallyBounded_iff]
  intro r hr
  let a := Concentration.empiricalNorm S L
  have ha : 0 ≤ a := by
    dsimp [a, Concentration.empiricalNorm]
    exact Real.sqrt_nonneg _
  let q : ℝ := r / (a + 1)
  have hq : 0 < q := div_pos hr (by linarith)
  obtain ⟨N, hNsub, hNcover, _hNcard⟩ :=
    exists_closedBall_net_card_le θ₀ hδ hq
  let T : Finset (Concentration.EmpiricalFunctionSpace
      (fun θ : Metric.closedBall θ₀ δ => F θ.1) S) :=
    N.attach.image fun y => ⟨⟨y.1, hNsub y.1 y.2⟩⟩
  refine ⟨(T : Set _), T.finite_toSet, ?_⟩
  intro z hz
  obtain ⟨η, hηN, hzη⟩ := hNcover z.index.1 z.index.2
  let c : Concentration.EmpiricalFunctionSpace
      (fun θ : Metric.closedBall θ₀ δ => F θ.1) S :=
    ⟨⟨η, hNsub η hηN⟩⟩
  refine Set.mem_iUnion_of_mem c ?_
  refine Set.mem_iUnion_of_mem ?_ ?_
  · exact Finset.mem_coe.mpr <| Finset.mem_image.mpr
      ⟨⟨η, hηN⟩, Finset.mem_attach _ _, rfl⟩
  · change Concentration.empiricalDist S (F z.index.1) (F η) < r
    have hd := parametric_empiricalDist_le S F L hL θ₀ hLip
      z.index.1 z.index.2 η (hNsub η hηN)
    calc
      Concentration.empiricalDist S (F z.index.1) (F η)
          ≤ ‖z.index.1 - η‖ * a := hd
      _ ≤ q * a := mul_le_mul_of_nonneg_right hzη.le ha
      _ < r := by
        dsimp [q]
        have hden : 0 < a + 1 := by linarith
        rw [div_mul_eq_mul_div]
        exact (div_lt_iff₀ hden).2 (by nlinarith)

/-- [The empirical covering number of a Lipschitz class obeys the
finite-dimensional volumetric bound](goal) on [a sample](hyp:S).  The [scalar
class](hyp:F) has [a nonnegative envelope](hyp:L,hL) and [Lipschitz
control](hyp:hLip) on the ball with [center](hyp:θ₀) and [nonnegative
radius](hyp:hδ), at [positive covering scale](hyp:hx). -/
lemma parametric_coveringNumber_le
    {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {n : ℕ} (S : Fin n → X) (F : E → X → ℝ) (L : X → ℝ)
    (hL : ∀ x, 0 ≤ L x)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      |F θ z - F η z| ≤ L z * ‖θ - η‖)
    (hδ : 0 ≤ δ) {x : ℝ} (hx : 0 < x) :
    let ι := Metric.closedBall θ₀ δ
    let htot := parametric_empirical_totallyBounded S F L hL θ₀ δ hLip hδ
    (Concentration.coveringNumber' htot x : ℝ) ≤
      (1 + 8 * δ * Concentration.empiricalNorm S L / x) ^ Module.finrank ℝ E := by
  dsimp only
  classical
  let a := Concentration.empiricalNorm S L
  have ha : 0 ≤ a := by
    dsimp [a, Concentration.empiricalNorm]
    exact Real.sqrt_nonneg _
  by_cases ha0 : a = 0
  · let z : Concentration.EmpiricalFunctionSpace
        (fun θ : Metric.closedBall θ₀ δ => F θ.1) S := ⟨⟨θ₀, by simp [hδ]⟩⟩
    let T : Finset (Concentration.EmpiricalFunctionSpace
        (fun θ : Metric.closedBall θ₀ δ => F θ.1) S) := {z}
    have hcover : (Set.univ : Set (Concentration.EmpiricalFunctionSpace
        (fun θ : Metric.closedBall θ₀ δ => F θ.1) S)) ⊆
        ⋃ y ∈ T, Metric.ball y x := by
      intro q hq
      refine Set.mem_iUnion_of_mem z ?_
      refine Set.mem_iUnion_of_mem (by simp [T] : z ∈ T) ?_
      change Concentration.empiricalDist S (F q.index.1) (F θ₀) < x
      exact (parametric_empiricalDist_le S F L hL θ₀ hLip q.index.1 q.index.2 θ₀
        (Metric.mem_closedBall_self hδ)).trans_lt
        (by simp [a, ha0, hx])
    rw [Concentration.coveringNumber'_eq
      (parametric_empirical_totallyBounded S F L hL θ₀ δ hLip hδ) hx]
    calc
      (Nat.find (Concentration.coveringNumber_exists
          (parametric_empirical_totallyBounded S F L hL θ₀ δ hLip hδ) hx) : ℝ)
          ≤ (T.card : ℝ) := by
            exact_mod_cast Nat.find_min'
              (Concentration.coveringNumber_exists
                (parametric_empirical_totallyBounded S F L hL θ₀ δ hLip hδ) hx)
              ⟨T, rfl, hcover⟩
      _ = 1 := by simp [T]
      _ ≤ (1 + 8 * δ * Concentration.empiricalNorm S L / x) ^
          Module.finrank ℝ E := by
        rw [show Concentration.empiricalNorm S L = 0 by simpa [a] using ha0]
        simp
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let q : ℝ := x / (2 * a)
    have hq : 0 < q := div_pos hx (mul_pos (by norm_num) hapos)
    obtain ⟨N, hNsub, hNcover, hNcard⟩ :=
      exists_closedBall_net_card_le θ₀ hδ hq
    let T : Finset (Concentration.EmpiricalFunctionSpace
        (fun θ : Metric.closedBall θ₀ δ => F θ.1) S) :=
      N.attach.image fun y => ⟨⟨y.1, hNsub y.1 y.2⟩⟩
    have hcover : (Set.univ : Set (Concentration.EmpiricalFunctionSpace
        (fun θ : Metric.closedBall θ₀ δ => F θ.1) S)) ⊆
        ⋃ y ∈ T, Metric.ball y x := by
      intro z hz
      obtain ⟨η, hηN, hzη⟩ := hNcover z.index.1 z.index.2
      let c : Concentration.EmpiricalFunctionSpace
          (fun θ : Metric.closedBall θ₀ δ => F θ.1) S :=
        ⟨⟨η, hNsub η hηN⟩⟩
      refine Set.mem_iUnion_of_mem c ?_
      refine Set.mem_iUnion_of_mem ?_ ?_
      · exact Finset.mem_coe.mpr <| Finset.mem_image.mpr
          ⟨⟨η, hηN⟩, Finset.mem_attach _ _, rfl⟩
      · change Concentration.empiricalDist S (F z.index.1) (F η) < x
        have hd := parametric_empiricalDist_le S F L hL θ₀ hLip
          z.index.1 z.index.2 η (hNsub η hηN)
        calc
          Concentration.empiricalDist S (F z.index.1) (F η)
              ≤ ‖z.index.1 - η‖ * a := hd
          _ < q * a := mul_lt_mul_of_pos_right hzη hapos
          _ = x / 2 := by dsimp [q]; field_simp
          _ < x := by linarith
    rw [Concentration.coveringNumber'_eq
      (parametric_empirical_totallyBounded S F L hL θ₀ δ hLip hδ) hx]
    calc
      (Nat.find (Concentration.coveringNumber_exists
          (parametric_empirical_totallyBounded S F L hL θ₀ δ hLip hδ) hx) : ℝ)
          ≤ (T.card : ℝ) := by
            exact_mod_cast Nat.find_min'
              (Concentration.coveringNumber_exists
                (parametric_empirical_totallyBounded S F L hL θ₀ δ hLip hδ) hx)
              ⟨T, rfl, hcover⟩
      _ ≤ (N.card : ℝ) := by
        dsimp [T]
        exact_mod_cast (Finset.card_image_le.trans_eq Finset.card_attach)
      _ ≤ (1 + 4 * δ / q) ^ Module.finrank ℝ E := hNcard
      _ = (1 + 8 * δ * Concentration.empiricalNorm S L / x) ^
          Module.finrank ℝ E := by
        congr 1
        dsimp [q, a]
        field_simp
        ring

/-- [The truncated Dudley entropy integral of a Lipschitz class is bounded by
dimension times radius](goal) on [a sample](hyp:S).  The [scalar
class](hyp:F) has [a nonnegative envelope](hyp:L,hL) and [Lipschitz
control](hyp:hLip) on the ball with [center](hyp:θ₀) and [positive
radius](hyp:hδ); the estimate assumes [positive empirical envelope
norm](hyp:ha), [positive cutoff](hyp:hε), and [a cutoff below the class
radius](hyp:hεR). -/
lemma parametric_entropyIntegral_le
    {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {n : ℕ} (S : Fin n → X) (F : E → X → ℝ) (L : X → ℝ)
    (hL : ∀ x, 0 ≤ L x)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      |F θ z - F η z| ≤ L z * ‖θ - η‖)
    (hδ : 0 < δ)
    (ha : 0 < Concentration.empiricalNorm S L)
    {ε : ℝ} (hε : 0 < ε)
    (hεR : ε ≤ δ * Concentration.empiricalNorm S L) :
    let ι := Metric.closedBall θ₀ δ
    let htot := parametric_empirical_totallyBounded S F L hL θ₀ δ hLip hδ.le
    (∫ x in ε..(δ * Concentration.empiricalNorm S L),
      Real.sqrt (Real.log (Concentration.coveringNumber' htot x))) ≤
        4 * (Module.finrank ℝ E + 1) *
          (δ * Concentration.empiricalNorm S L) := by
  dsimp only
  let R := δ * Concentration.empiricalNorm S L
  let d : ℝ := Module.finrank ℝ E
  let htot := parametric_empirical_totallyBounded S F L hL θ₀ δ hLip hδ.le
  have hR : 0 < R := mul_pos hδ ha
  have hd : 0 ≤ d := by positivity
  have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  letI : Nonempty (Concentration.EmpiricalFunctionSpace
      (fun θ : Metric.closedBall θ₀ δ => F θ.1) S) :=
    ⟨⟨⟨θ₀, by simp [hδ.le]⟩⟩⟩
  have hpoint : ∀ x ∈ Set.Icc ε R,
      Real.sqrt (Real.log (Concentration.coveringNumber' htot x)) ≤
        Real.sqrt (d * Real.log 9) +
          Real.sqrt d * Real.sqrt (Real.log (R / x)) := by
    intro x hx
    have hx0 : 0 < x := hε.trans_le hx.1
    have hxR : 1 ≤ R / x := (one_le_div hx0).2 hx.2
    have hbase : 0 < 9 * R / x := by positivity
    have hcov0 : 0 < (Concentration.coveringNumber' htot x : ℝ) := by
      exact_mod_cast Concentration.coveringNumber'_nonzero Set.univ_nonempty htot hx0
    have hcov := parametric_coveringNumber_le S F L hL θ₀ hLip hδ.le hx0
    have hbase_le :
        1 + 8 * δ * Concentration.empiricalNorm S L / x ≤ 9 * R / x := by
      dsimp [R]
      have hRx : x ≤ δ * Concentration.empiricalNorm S L := hx.2
      calc
        1 + 8 * δ * Concentration.empiricalNorm S L / x
            ≤ δ * Concentration.empiricalNorm S L / x +
                8 * δ * Concentration.empiricalNorm S L / x := by
              gcongr
        _ = 9 * (δ * Concentration.empiricalNorm S L) / x := by ring
    have hcov' : (Concentration.coveringNumber' htot x : ℝ) ≤
        (9 * R / x) ^ Module.finrank ℝ E := by
      exact hcov.trans (pow_le_pow_left₀ (by positivity) hbase_le _)
    have hlogcov : Real.log (Concentration.coveringNumber' htot x) ≤
        d * Real.log (9 * R / x) := by
      calc
        Real.log (Concentration.coveringNumber' htot x)
            ≤ Real.log ((9 * R / x) ^ Module.finrank ℝ E) :=
              Real.log_le_log hcov0 hcov'
        _ = d * Real.log (9 * R / x) := by
          rw [Real.log_pow]
    have hsplit : Real.log (9 * R / x) = Real.log 9 + Real.log (R / x) := by
      rw [show 9 * R / x = 9 * (R / x) by ring]
      exact Real.log_mul (by norm_num) (by positivity)
    have hlogRx : 0 ≤ Real.log (R / x) := Real.log_nonneg hxR
    have hmain := Real.sqrt_le_sqrt hlogcov
    have hsqrtadd : Real.sqrt (d * Real.log 9 + d * Real.log (R / x)) ≤
        Real.sqrt (d * Real.log 9) + Real.sqrt (d * Real.log (R / x)) := by
      have ha' : 0 ≤ d * Real.log 9 := mul_nonneg hd hlog9
      have hb' : 0 ≤ d * Real.log (R / x) := mul_nonneg hd hlogRx
      nlinarith [Real.sq_sqrt ha', Real.sq_sqrt hb',
        Real.sq_sqrt (add_nonneg ha' hb'),
        Real.sqrt_nonneg (d * Real.log 9),
        Real.sqrt_nonneg (d * Real.log (R / x))]
    calc
      Real.sqrt (Real.log (Concentration.coveringNumber' htot x))
          ≤ Real.sqrt (d * Real.log (9 * R / x)) := hmain
      _ = Real.sqrt (d * Real.log 9 + d * Real.log (R / x)) := by
        rw [hsplit]
        ring_nf
      _ ≤ Real.sqrt (d * Real.log 9) + Real.sqrt (d * Real.log (R / x)) := hsqrtadd
      _ = Real.sqrt (d * Real.log 9) +
          Real.sqrt d * Real.sqrt (Real.log (R / x)) := by
        rw [Real.sqrt_mul hd, Real.sqrt_mul hd]
  have hintLeft : IntervalIntegrable
      (fun x : ℝ => Real.sqrt (Real.log (Concentration.coveringNumber' htot x)))
      volume ε R := by
    apply AntitoneOn.intervalIntegrable
    refine antitoneOn_iff_forall_lt.mpr ?_
    intro a haI b hbI hab
    apply Real.sqrt_le_sqrt
    apply Real.log_le_log
    · exact_mod_cast Concentration.coveringNumber'_nonzero Set.univ_nonempty htot (by
        have hb' : b ∈ Set.Icc ε R := by
          rw [← Set.uIcc_of_le hεR]
          exact hbI
        exact hε.trans_le hb'.1)
    · norm_cast
      exact Concentration.coveringNumber'_antitone htot
        (by have ha' : a ∈ Set.Icc ε R := by
              rw [← Set.uIcc_of_le hεR]
              exact haI
            exact hε.trans_le ha'.1)
        (by have hb' : b ∈ Set.Icc ε R := by
              rw [← Set.uIcc_of_le hεR]
              exact hbI
            exact hε.trans_le hb'.1) hab.le
  have hintConst : IntervalIntegrable
      (fun _x : ℝ => Real.sqrt (d * Real.log 9)) volume ε R :=
    intervalIntegrable_const
  have hintKernel : IntervalIntegrable
      (fun x : ℝ => Real.sqrt d * Real.sqrt (Real.log (R / x))) volume ε R :=
    (Concentration.intervalIntegrable_sqrt_log_div hε hεR).const_mul _
  have hmono := intervalIntegral.integral_mono_on hεR hintLeft
    (hintConst.add hintKernel) hpoint
  have hkernel := Concentration.sqrtLog_integral_le hε hεR
  have hlog9le : Real.log 9 ≤ 8 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)).trans_eq (by norm_num)
  have hsqrtdlog : Real.sqrt (d * Real.log 9) ≤ d + 3 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · have hmul : d * Real.log 9 ≤ 8 * d := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hlog9le hd
      nlinarith [sq_nonneg d]
  have hsqrtd : Real.sqrt d ≤ d + 1 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith [sq_nonneg d]
  calc
    (∫ x in ε..R,
      Real.sqrt (Real.log (Concentration.coveringNumber' htot x)))
        ≤ ∫ x in ε..R, (Real.sqrt (d * Real.log 9) +
          Real.sqrt d * Real.sqrt (Real.log (R / x))) := hmono
    _ = (R - ε) * Real.sqrt (d * Real.log 9) +
          Real.sqrt d * (∫ x in ε..R, Real.sqrt (Real.log (R / x))) := by
      rw [intervalIntegral.integral_add hintConst hintKernel]
      rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
      simp [smul_eq_mul]
    _ ≤ R * Real.sqrt (d * Real.log 9) + Real.sqrt d * R := by
      have h1 : (R - ε) * Real.sqrt (d * Real.log 9) ≤
          R * Real.sqrt (d * Real.log 9) := by
        nlinarith [Real.sqrt_nonneg (d * Real.log 9)]
      have hkernelR : (∫ x in ε..R, Real.sqrt (Real.log (R / x))) ≤ R :=
        hkernel.trans (by linarith)
      have h2 := mul_le_mul_of_nonneg_left hkernelR (Real.sqrt_nonneg d)
      nlinarith
    _ ≤ 4 * (d + 1) * R := by nlinarith [hR.le]
    _ = 4 * (Module.finrank ℝ E + 1) *
          (δ * Concentration.empiricalNorm S L) := rfl


end
end Causalean.Stat
