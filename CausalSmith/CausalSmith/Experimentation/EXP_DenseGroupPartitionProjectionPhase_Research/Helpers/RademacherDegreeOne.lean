import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.RademacherPriors
import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.RademacherMoments
import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.TExactKneserIdentity
import Causalean.Experimentation.FinitePopulationMoments

/-!
# Degree-one slice bridges for additive schedules

This file connects centered inclusion-linear functions in the reusable Johnson
space to the paper-local uniform-slice expectation.
-/

open scoped BigOperators
open Filter
open Finset

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.FinitePopulationMoments
open Causalean.Mathlib.Combinatorics.JohnsonKneser

-- @node: mem_johnsonHarmonic_one_of_degreeOne_mean_zero
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,f,hf,hmean), [the stated membership property holds](goal). -/
lemma mem_johnsonHarmonic_one_of_degreeOne_mean_zero {n M : ℕ}
    (hM : M ≤ n) (f : SliceFn n M) (hf : f ∈ degreeAtMost n M 1)
    (hmean : mean f = 0) : f ∈ johnsonHarmonic n M 1 := by
  unfold johnsonHarmonic
  constructor
  · exact hf
  · intro g hg
    obtain ⟨c, rfl⟩ := (mem_degreeAtMost_zero_iff hM _).1 hg
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply, constFn]
    unfold mean at hmean
    have hcard : (Fintype.card
        (Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega n M) : ℝ) ≠ 0 := by
      rw [card_omega hM]
      exact_mod_cast (Nat.choose_pos hM).ne'
    have hsum : ∑ A, f A = 0 := by
      apply (mul_eq_zero.mp hmean).resolve_left
      exact inv_ne_zero hcard
    rw [← Finset.mul_sum, hsum, mul_zero]

-- @node: johnsonMean_sampleMean_eq_sliceExpectation
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,x), [the stated expectation identity holds](goal). -/
lemma johnsonMean_sampleMean_eq_sliceExpectation {n M : ℕ} (hM : M ≤ n)
    (x : Fin n → ℝ) :
    mean (WithLp.toLp 2 (fun A :
      Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega n M =>
        (∑ i ∈ A.1, x i) / (M : ℝ))) =
      (slice n M hM).E (sampleMean M x) := by
  classical
  let e : Omega n M ≃
      Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega n M :=
    { toFun := fun A => ⟨A.1, A.2⟩
      invFun := fun A => ⟨A.1, A.2⟩
      left_inv := fun A => by cases A; rfl
      right_inv := fun A => by cases A; rfl }
  unfold mean slice FiniteDesign.E completeRandomization sampleMean
  simp only [one_div]
  rw [← Finset.mul_sum]
  have hcard : Fintype.card
      (Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega n M) =
      Fintype.card (Omega n M) := by
    exact Fintype.card_congr e.symm
  rw [hcard]
  congr 1
  symm
  exact Fintype.sum_equiv e _ _ (fun A => by
    change (∑ i, if i ∈ A.1 then x i else 0) / (M : ℝ) =
      (∑ i ∈ (e A).1, x i) / (M : ℝ)
    rw [← Finset.sum_filter]
    congr 2
    have heA : (e A).1 = A.1 := by
      change A.1 = A.1
      rfl
    ext i
    simp [heA])

-- @node: sampleMean_mem_degreeAtMost_one
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,x), [the stated membership property holds](goal). -/
lemma sampleMean_mem_degreeAtMost_one {n M : ℕ} (x : Fin n → ℝ) :
    WithLp.toLp 2 (fun A :
      Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega n M =>
        (∑ i ∈ A.1, x i) / (M : ℝ)) ∈ degreeAtMost n M 1 := by
  have hgen (i : Fin n) : inclusionMonomial (M := M) {i} ∈ degreeAtMost n M 1 :=
    Submodule.subset_span ⟨{i}, by simp, rfl⟩
  have hsum : (∑ i : Fin n,
      (x i / (M : ℝ)) • inclusionMonomial (M := M) {i}) ∈
      degreeAtMost n M 1 :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hgen i))
  convert hsum using 1
  ext A
  simp [inclusionMonomial, Finset.sum_div]

-- @node: centeredSampleMean_mem_johnsonHarmonic_one
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMn,x), [the stated membership property holds](goal). -/
lemma centeredSampleMean_mem_johnsonHarmonic_one {n M : ℕ}
    (hMn : M ≤ n) (x : Fin n → ℝ) :
    WithLp.toLp 2 (fun A : Omega n M =>
      sampleMean M x A - (slice n M hMn).E (sampleMean M x)) ∈
      johnsonHarmonic n M 1 := by
  unfold Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega
  let f : WithLp 2 ({A : Finset (Fin n) // A.card = M} → ℝ) :=
    WithLp.toLp 2 (fun A => sampleMean M x A)
  have hf : f ∈ degreeAtMost n M 1 := by
    simpa [f, sampleMean,
      Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega] using
      sampleMean_mem_degreeAtMost_one (M := M) x
  have hm : mean f = (slice n M hMn).E (sampleMean M x) := by
    simpa [f, sampleMean,
      Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega] using
      johnsonMean_sampleMean_eq_sliceExpectation hMn x
  have heq : WithLp.toLp 2 (fun A : {A : Finset (Fin n) // A.card = M} =>
      sampleMean M x A - (slice n M hMn).E (sampleMean M x)) =
      f - WithLp.toLp 2 (fun _ : {A : Finset (Fin n) // A.card = M} => mean f) := by
    ext A
    simp [f, hm]
  rw [heq]
  apply mem_johnsonHarmonic_one_of_degreeOne_mean_zero hMn
  · apply Submodule.sub_mem
    · exact hf
    · apply degreeAtMost_mono (n := n) (M := M) (Nat.zero_le 1)
      have hc := (mem_degreeAtMost_zero_iff hMn
        (constFn (n := n) (M := M) (mean f))).2 ⟨mean f, rfl⟩
      simpa [constFn,
        Causalean.Mathlib.Combinatorics.JohnsonKneser.Omega] using hc
  · unfold mean
    change (Fintype.card ({A : Finset (Fin n) // A.card = M}) : ℝ)⁻¹ *
      ∑ A : {A : Finset (Fin n) // A.card = M}, (f A -
        (Fintype.card ({A : Finset (Fin n) // A.card = M}) : ℝ)⁻¹ * ∑ S, f S) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have hcard : (Fintype.card ({A : Finset (Fin n) // A.card = M}) : ℝ) ≠ 0 := by
      rw [Fintype.card_finset_len, Fintype.card_fin]
      exact_mod_cast (Nat.choose_pos hMn).ne'
    field_simp [hcard]
    ring

-- @node: johnsonProj_sampleMean_eq_centered
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMpos,h2M,J,hJohnson,x), [the stated equality holds](goal). -/
lemma johnsonProj_sampleMean_eq_centered {n M : ℕ} (hMpos : 0 < M)
    (h2M : 2 * M ≤ n) (J : JohnsonProjections n M)
    (hJohnson : JohnsonOrthogonalDecomposition n M J) (x : Fin n → ℝ) :
    J.proj ⟨1, by omega⟩ (sampleMean M x) =
      fun A => sampleMean M x A - (slice n M (by omega)).E (sampleMean M x) := by
  let k : Fin (M + 1) := ⟨1, by omega⟩
  let f : Omega n M → ℝ := sampleMean M x
  let fc : Omega n M → ℝ :=
    fun A => f A - (slice n M (by omega)).E f
  have hmem : fc ∈ johnsonHarmonicSpace n M J.slice_nonempty k := by
    unfold johnsonHarmonicSpace
    have hh := centeredSampleMean_mem_johnsonHarmonic_one
      (by omega : M ≤ n) x
    simpa [k, fc, f] using hh
  have hfix : J.proj k fc = fc := J.fixes_range _ _ hmem
  have hk : 0 < k.1 := by simp [k]
  have hcenter := johnson_proj_centered_eq h2M J hJohnson k hk f
  rw [← hcenter, hfix]

-- @node: degreeOneEnergy_independentPrior_eq_popVar
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMpos,h2M,hMn,J,hJohnson,u), [the stated variance result holds](goal). -/
lemma degreeOneEnergy_independentPrior_eq_popVar {n M : ℕ}
    (hMpos : 0 < M) (h2M : 2 * M ≤ n) (hMn : M ≤ n)
    (J : JohnsonProjections n M) (hJohnson : JohnsonOrthogonalDecomposition n M J)
    (u : Fin n × Bool → Bool) :
    degreeOneEnergy n M hMpos hMn J (independentPriorSchedule n M u) =
      (1 / (M : ℝ) - 1 / (n : ℝ)) *
        popVar (fun i => rademacherSign (u (i, true)) - rademacherSign (u (i, false))) := by
  let x : Fin n → ℝ := fun i =>
    rademacherSign (u (i, true)) - rademacherSign (u (i, false))
  have hf : (fun A => armTable n M (independentPriorSchedule n M u) true A -
      armTable n M (independentPriorSchedule n M u) false A) = sampleMean M x := by
    rw [armTable_independentPrior_eq_sampleMean,
      armTable_independentPrior_eq_sampleMean]
    funext A
    unfold sampleMean
    rw [← sub_div, ← Finset.sum_sub_distrib]
    apply congrArg (fun q : ℝ => q / (M : ℝ))
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ A.1 <;> simp [hi, x]
  unfold degreeOneEnergy
  rw [hf, johnsonProj_sampleMean_eq_centered hMpos h2M J hJohnson x]
  rw [show sliceNorm n M hMn
      (fun A => sampleMean M x A - (slice n M hMn).E (sampleMean M x)) ^ 2 =
      (slice n M hMn).Var (sampleMean M x) by
    unfold sliceNorm sliceNormSq sliceInner
    rw [Real.sq_sqrt]
    · rw [FiniteDesign.Var_eq]
      let m := (slice n M hMn).E (sampleMean M x)
      have hp : (fun A =>
          (sampleMean M x A - m) * (sampleMean M x A - m)) =
          fun A => sampleMean M x A ^ 2 - 2 * m * sampleMean M x A + m ^ 2 := by
        funext A
        ring
      rw [hp, (slice n M hMn).E_add, (slice n M hMn).E_sub,
        (slice n M hMn).E_const_mul, (slice n M hMn).E_const]
      dsimp [m]
      ring
    · exact (slice n M hMn).E_nonneg (fun A => mul_self_nonneg _)]
  unfold slice
  have hn2 : 2 ≤ n := by omega
  simpa using (Var_sampleMean (U := Fin n) M (by simpa using hMn) hMpos
    (by simpa using hn2) x)

-- @node: radCrossMean
/-- For [the stated inputs](hyp:n,u), [rad cross mean](goal) is defined by the formula below. -/
noncomputable def radCrossMean (n : ℕ) (u : Fin n × Bool → Bool) : ℝ :=
  (∑ i, rademacherSign (u (i, true)) * rademacherSign (u (i, false))) / (n : ℝ)

-- @node: radPair_E
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,i), [the rad pair e result holds](goal). -/
lemma radPair_E (n : ℕ) (i : Fin n) :
    (priorIndependent n).E (fun u =>
      rademacherSign (u (i, true)) * rademacherSign (u (i, false))) = 0 := by
  unfold priorIndependent
  rw [FiniteDesign.E_prod_apply₂ _ (by simp : (i, true) ≠ (i, false))]
  norm_num [coinDesign_E, rademacherSign]

-- @node: radPair_var
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,i), [the stated variance result holds](goal). -/
lemma radPair_var (n : ℕ) (i : Fin n) :
    (priorIndependent n).Var (fun u =>
      rademacherSign (u (i, true)) * rademacherSign (u (i, false))) = 1 := by
  rw [FiniteDesign.Var_eq, radPair_E]
  have hsquare : (fun u : Fin n × Bool → Bool =>
      (rademacherSign (u (i, true)) * rademacherSign (u (i, false))) ^ 2) =
      fun _ => (1 : ℝ) := by
    funext u
    cases u (i, true) <;> cases u (i, false) <;> norm_num [rademacherSign]
  rw [hsquare, FiniteDesign.E_const]
  norm_num

-- @node: radPair_cov_ne
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,i,j,hij), [the rad pair cov ne result holds](goal). -/
lemma radPair_cov_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (priorIndependent n).Cov
      (fun u => rademacherSign (u (i, true)) * rademacherSign (u (i, false)))
      (fun u => rademacherSign (u (j, true)) * rademacherSign (u (j, false))) = 0 := by
  unfold priorIndependent
  apply FiniteDesign.Cov_prod_disjoint_zero _
    ({(i, true), (i, false)} : Finset (Fin n × Bool))
    ({(j, true), (j, false)} : Finset (Fin n × Bool))
  · simp_all [eq_comm]
  · intro w w' hw
    rw [hw (i, true) (by simp), hw (i, false) (by simp)]
  · intro w w' hw
    rw [hw (j, true) (by simp), hw (j, false) (by simp)]

-- @node: radCrossMean_E
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n), [the rad cross mean e result holds](goal). -/
lemma radCrossMean_E (n : ℕ) :
    (priorIndependent n).E (radCrossMean n) = 0 := by
  unfold radCrossMean
  rw [show (fun u : Fin n × Bool → Bool =>
      (∑ i, rademacherSign (u (i, true)) * rademacherSign (u (i, false))) / (n : ℝ)) =
      (fun u => ∑ i, (1 / (n : ℝ)) *
        (rademacherSign (u (i, true)) * rademacherSign (u (i, false)))) by
    funext u
    rw [← Finset.mul_sum]
    ring]
  rw [FiniteDesign.E_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [FiniteDesign.E_const_mul]
  rw [radPair_E]
  ring

-- @node: radCrossMean_var
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n), [the stated variance result holds](goal). -/
lemma radCrossMean_var (n : ℕ) :
    (priorIndependent n).Var (radCrossMean n) =
      (n : ℝ) * (1 / (n : ℝ)) ^ 2 := by
  unfold radCrossMean
  rw [show (fun u : Fin n × Bool → Bool =>
      (∑ i, rademacherSign (u (i, true)) * rademacherSign (u (i, false))) / (n : ℝ)) =
      (fun u => ∑ i, (1 / (n : ℝ)) *
        (rademacherSign (u (i, true)) * rademacherSign (u (i, false)))) by
    funext u
    rw [← Finset.mul_sum]
    ring]
  rw [(priorIndependent n).Var_linear_comb]
  calc
    (∑ i, ∑ j,
        1 / (n : ℝ) * (1 / (n : ℝ)) *
          (priorIndependent n).Cov
            (fun u => rademacherSign (u (i, true)) * rademacherSign (u (i, false)))
            (fun u => rademacherSign (u (j, true)) * rademacherSign (u (j, false)))) =
        ∑ i : Fin n, (1 / (n : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [FiniteDesign.Cov_self, radPair_var]
        ring
      · intro j _ hji
        rw [radPair_cov_ne (Ne.symm hji)]
        ring
      · simp
    _ = (n : ℝ) * (1 / (n : ℝ)) ^ 2 := by simp

-- @node: radCrossMean_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:N,hN), [the indicated sequence converges to its stated limit](goal). -/
lemma radCrossMean_tendstoInProb (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    FiniteDesign.TendstoInProb (fun r => priorIndependent (N r))
      (fun r => radCrossMean (N r)) (fun _ => 0) := by
  have hv : Tendsto (fun r =>
      (priorIndependent (N r)).Var (radCrossMean (N r))) atTop (nhds 0) := by
    simp_rw [radCrossMean_var]
    have hNR : Tendsto (fun r => (N r : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hN
    have hinv := hNR.inv_tendsto_atTop
    convert hinv using 1
    funext r
    by_cases hz : N r = 0
    · simp [hz]
    · change (N r : ℝ) * (1 / (N r : ℝ)) ^ 2 = (N r : ℝ)⁻¹
      field_simp
  have h := FiniteDesign.tendstoInProb_of_var
    (D := fun r => priorIndependent (N r)) (X := fun r => radCrossMean (N r)) hv
  simpa [radCrossMean_E] using h

-- @node: popVar_independentDifference_eq
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,hn,u), [the stated variance result holds](goal). -/
lemma popVar_independentDifference_eq {n : ℕ} (hn : 2 ≤ n)
    (u : Fin n × Bool → Bool) :
    popVar (fun i => rademacherSign (u (i, true)) - rademacherSign (u (i, false))) =
      (n : ℝ) / ((n : ℝ) - 1) *
        (2 - 2 * radCrossMean n u -
          (radArmMean n true u - radArmMean n false u) ^ 2) := by
  unfold popVar popMean radCrossMean radArmMean
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1R : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hsignsq (i : Fin n) (z : Bool) : rademacherSign (u (i, z)) ^ 2 = 1 := by
    cases u (i, z) <;> norm_num [rademacherSign]
  simp_rw [sub_sq]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [hsignsq]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [Finset.sum_sub_distrib]
  rw [show (∑ x : Fin n,
      2 * rademacherSign (u (x, true)) * rademacherSign (u (x, false))) =
      2 * ∑ x : Fin n,
        rademacherSign (u (x, true)) * rademacherSign (u (x, false)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  field_simp [hnR, hn1R]
  ring

-- @node: FiniteDesign.TendstoInProb.deterministic_mul
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,X,x,c,a,hX,ha), [the deterministic mul result holds](goal). -/
lemma FiniteDesign.TendstoInProb.deterministic_mul
    {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)] {D : ∀ r, FiniteDesign (Ω r)}
    {X : ∀ r, Ω r → ℝ} {x c : ℝ} {a : ℕ → ℝ}
    (hX : FiniteDesign.TendstoInProb D X (fun _ => x))
    (ha : Tendsto a atTop (nhds c)) :
    FiniteDesign.TendstoInProb D (fun r w => a r * X r w) (fun _ => c * x) := by
  intro ε hε
  let K := |c| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hδX : 0 < ε / (2 * K) := by positivity
  have hδa : 0 < ε / (2 * (|x| + 1)) := by positivity
  have haOne : ∀ᶠ r in atTop, |a r - c| < 1 := by
    simpa [Real.dist_eq] using (Metric.tendsto_atTop.1 ha 1 zero_lt_one)
  have haClose : ∀ᶠ r in atTop, |a r - c| < ε / (2 * (|x| + 1)) := by
    simpa [Real.dist_eq] using (Metric.tendsto_atTop.1 ha _ hδa)
  apply squeeze_zero' (Eventually.of_forall fun r => (D r).Pr_nonneg _) _
    (hX (ε / (2 * K)) hδX)
  filter_upwards [haOne, haClose] with r har hac
  apply (D r).Pr_mono
  intro w hw
  by_contra hnear
  push Not at hnear
  have haBound : |a r| ≤ K := by
    have htri : |a r| ≤ |a r - c| + |c| := by
      calc
        |a r| = |(a r - c) + c| := by ring_nf
        _ ≤ |a r - c| + |c| := abs_add_le _ _
    dsimp [K]
    linarith
  have hprod : |a r * X r w - c * x| ≤
      |a r| * |X r w - x| + |a r - c| * |x| := by
    calc
      |a r * X r w - c * x| =
          |a r * (X r w - x) + (a r - c) * x| := by ring_nf
      _ ≤ |a r * (X r w - x)| + |(a r - c) * x| := abs_add_le _ _
      _ = |a r| * |X r w - x| + |a r - c| * |x| := by rw [abs_mul, abs_mul]
  have hfirst : |a r| * |X r w - x| < ε / 2 := by
    calc
      |a r| * |X r w - x| ≤ K * |X r w - x| :=
        mul_le_mul_of_nonneg_right haBound (abs_nonneg _)
      _ < K * (ε / (2 * K)) := mul_lt_mul_of_pos_left hnear hK
      _ = ε / 2 := by field_simp
  have hsecond : |a r - c| * |x| < ε / 2 := by
    have hxlt : |x| < |x| + 1 := by linarith
    calc
      |a r - c| * |x| ≤ |a r - c| * (|x| + 1) :=
        mul_le_mul_of_nonneg_left hxlt.le (abs_nonneg _)
      _ < (ε / (2 * (|x| + 1))) * (|x| + 1) :=
        mul_lt_mul_of_pos_right hac (by positivity)
      _ = ε / 2 := by field_simp
  linarith

-- @node: natCast_ratio_sub_one_tendsto
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:N,hN), [the indicated sequence converges to its stated limit](goal). -/
lemma natCast_ratio_sub_one_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun r => (N r : ℝ) / ((N r : ℝ) - 1)) atTop (nhds 1) := by
  have hNR : Tendsto (fun r => (N r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hInv : Tendsto (fun r => ((N r : ℝ))⁻¹) atTop (nhds 0) :=
    hNR.inv_tendsto_atTop
  have hden : Tendsto (fun r => 1 - ((N r : ℝ))⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hInv
  have hdenInv : Tendsto (fun r => (1 - ((N r : ℝ))⁻¹)⁻¹) atTop (nhds 1) := by
    simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply hdenInv.congr'
  filter_upwards [hN.eventually (eventually_ge_atTop 1)] with r hr
  have hne : (N r : ℝ) ≠ 0 := by exact_mod_cast (by omega : N r ≠ 0)
  field_simp

-- @node: independentDifferencePopVar_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:N,hNtwo,hN), [the indicated sequence converges to its stated limit](goal). -/
lemma independentDifferencePopVar_tendstoInProb (N : ℕ → ℕ)
    (hNtwo : ∀ r, 2 ≤ N r) (hN : Tendsto N atTop atTop) :
    FiniteDesign.TendstoInProb (fun r => priorIndependent (N r))
      (fun _r u => popVar (fun i =>
        rademacherSign (u (i, true)) - rademacherSign (u (i, false))))
      (fun _ => 2) := by
  let D := fun r => priorIndependent (N r)
  have hcross := radCrossMean_tendstoInProb N hN
  have hmean := (radArmMean_tendstoInProb N hN true).sub
    (radArmMean_tendstoInProb N hN false)
  have hmeanSq := FiniteDesign.tendstoInProb_continuousMap D
    (fun r u => radArmMean (N r) true u - radArmMean (N r) false u)
    0 (fun x => x ^ 2) (by simpa [D] using hmean) (continuousAt_id.pow 2)
  have hconst : FiniteDesign.TendstoInProb D (fun _ _ => (2 : ℝ)) (fun _ => 2) :=
    FiniteDesign.deterministic_tendstoInProb D (fun _ => 2) 2 tendsto_const_nhds
  have hinner := (hconst.add (hcross.const_mul (-2))).sub hmeanSq
  have hinner' : FiniteDesign.TendstoInProb D
      (fun r u => 2 - 2 * radCrossMean (N r) u -
        (radArmMean (N r) true u - radArmMean (N r) false u) ^ 2)
      (fun _ => 2) := by
    simpa [D, sub_eq_add_neg] using hinner
  have hratio := natCast_ratio_sub_one_tendsto N hN
  have hscaled := FiniteDesign.TendstoInProb.deterministic_mul hinner' hratio
  convert hscaled using 1
  · funext r u
    rw [popVar_independentDifference_eq (hNtwo r)]
  · funext r
    ring

-- @node: scheduleArray_independent_degreeOne_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,hGrowth,J,hJohnson), [the indicated sequence converges to its stated limit](goal). -/
lemma scheduleArray_independent_degreeOne_tendstoInProb {M : ℕ} (A : ScheduleArray M)
    (hGrowth : GroupCountGrowth A) (J : ∀ r, JohnsonProjections (A.popSize r) M)
    (hJohnson : ∀ r, JohnsonOrthogonalDecomposition (A.popSize r) M (J r)) :
    FiniteDesign.TendstoInProb (fun r => priorIndependent (A.popSize r))
      (fun r u => degreeOneEnergy (A.popSize r) M
        (A.groupSize_ge_two.trans' (by omega)) (A.groupSize_le r) (J r)
        (independentPriorSchedule (A.popSize r) M u))
      (fun _ => 2 / (M : ℝ)) := by
  have hN := A.popSize_tendsto_atTop hGrowth
  have hNtwo : ∀ r, 2 ≤ A.popSize r := fun r =>
    le_trans A.groupSize_ge_two (A.groupSize_le r)
  have hpop := independentDifferencePopVar_tendstoInProb A.popSize hNtwo hN
  have hNR : Tendsto (fun r => (A.popSize r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hInv : Tendsto (fun r => ((A.popSize r : ℝ))⁻¹) atTop (nhds 0) :=
    hNR.inv_tendsto_atTop
  have hcoef : Tendsto (fun r => 1 / (M : ℝ) - 1 / (A.popSize r : ℝ))
      atTop (nhds (1 / (M : ℝ))) := by
    have hc : Tendsto (fun _ : ℕ => (1 / (M : ℝ))) atTop
        (nhds (1 / (M : ℝ))) := tendsto_const_nhds
    simpa only [one_div, sub_zero] using hc.sub hInv
  have hscaled := FiniteDesign.TendstoInProb.deterministic_mul hpop hcoef
  convert hscaled using 1
  · funext r u
    have htpos := A.treated_pos r
    have htlt := A.treated_lt r
    have hGtwo : 2 ≤ A.groups r := by omega
    have h2M : 2 * M ≤ A.popSize r :=
      le_trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left M hGtwo)
        (A.grouped_le r)
    rw [degreeOneEnergy_independentPrior_eq_popVar
      (A.groupSize_ge_two.trans' (by omega)) h2M (A.groupSize_le r) (J r)
      (hJohnson r)]
  · funext r
    ring

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
