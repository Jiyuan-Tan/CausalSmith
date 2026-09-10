import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.TCr2PhaseFrontier
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sparse consistency beyond the birthday scale
-/

open scoped Topology
open Filter

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

/-- The benchmark group count `floor (n^(3/4) / M)`. -/
noncomputable def birthdayGroups (M n : ℕ) : ℕ :=
  ⌊Real.rpow (n : ℝ) (3 / 4 : ℝ) / (M : ℝ)⌋₊

/-- The corresponding grouped-unit count. -/
noncomputable def birthdayGroupedUnits (M n : ℕ) : ℕ := M * birthdayGroups M n
  -- @realizes N_n(M times floor of n to three-quarters over M)

/-- The three unconditional arithmetic facts of the birthday-scale benchmark. -/
def BirthdayBenchmark (M : ℕ) : Prop :=
  (∀ᶠ n in atTop, birthdayGroupedUnits M n ≤ n) ∧
  Tendsto (fun n => (birthdayGroupedUnits M n : ℝ) / (n : ℝ)) atTop (nhds 0) ∧
  Tendsto (fun n => ((birthdayGroupedUnits M n : ℝ) ^ 2) / (n : ℝ)) atTop atTop

/-- An array's grouped-unit counts agree row-by-row with the birthday benchmark. -/
def CountAlignment {groupSize : ℕ} (A : ScheduleArray groupSize) (M : ℕ) : Prop :=
  ∀ r, A.grouped r = birthdayGroupedUnits M (A.popSize r)

-- @node: birthdayGroupedUnits_ratio_identity
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,n,hM,hn), [the stated equality holds](goal). -/
lemma birthdayGroupedUnits_ratio_identity (M n : ℕ) (hM : 0 < M) (hn : 0 < n) :
    (birthdayGroupedUnits M n : ℝ) / (n : ℝ) =
      ((⌊Real.rpow (n : ℝ) (3 / 4 : ℝ) / (M : ℝ)⌋₊ : ℝ) /
        (Real.rpow (n : ℝ) (3 / 4 : ℝ) / (M : ℝ))) *
        Real.rpow (n : ℝ) (- (1 / 4 : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hpow : Real.rpow (n : ℝ) (- (1 / 4 : ℝ)) =
      Real.rpow (n : ℝ) (3 / 4 : ℝ) / (n : ℝ) := by
    calc
      Real.rpow (n : ℝ) (- (1 / 4 : ℝ)) =
          Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 1) := by norm_num
      _ = Real.rpow (n : ℝ) (3 / 4 : ℝ) / Real.rpow (n : ℝ) 1 :=
        Real.rpow_sub hnR _ _
      _ = Real.rpow (n : ℝ) (3 / 4 : ℝ) / (n : ℝ) := by
        congr 1
        exact Real.rpow_one _
  rw [birthdayGroupedUnits, birthdayGroups, Nat.cast_mul, hpow]
  have hp : Real.rpow (n : ℝ) (3 / 4 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hnR _)
  field_simp

-- @node: birthdayGroupedUnits_feasible
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,n,hM,hn), [the birthday grouped units feasible result holds](goal). -/
lemma birthdayGroupedUnits_feasible (M n : ℕ) (hM : 0 < M) (hn : 1 ≤ n) :
    birthdayGroupedUnits M n ≤ n := by
  have hreal : (birthdayGroupedUnits M n : ℝ) ≤ (n : ℝ) := by
    calc
      (birthdayGroupedUnits M n : ℝ) = (M : ℝ) *
          (⌊Real.rpow (n : ℝ) (3 / 4 : ℝ) / (M : ℝ)⌋₊ : ℝ) := by
            rw [birthdayGroupedUnits, birthdayGroups, Nat.cast_mul]
      _ ≤ (M : ℝ) * (Real.rpow (n : ℝ) (3 / 4 : ℝ) / (M : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Nat.floor_le (div_nonneg (Real.rpow_nonneg (by positivity) _) (Nat.cast_nonneg _)))
          (Nat.cast_nonneg _)
      _ = Real.rpow (n : ℝ) (3 / 4 : ℝ) := by
        field_simp [show (M : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hM)]
      _ ≤ (n : ℝ) := Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num)
  exact_mod_cast hreal

-- @node: birthdayGroupedUnits_lower_bound
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,n,hM), [the birthday grouped units lower bound result holds](goal). -/
lemma birthdayGroupedUnits_lower_bound (M n : ℕ) (hM : 0 < M) :
    Real.rpow (n : ℝ) (3 / 4 : ℝ) - (M : ℝ) ≤ birthdayGroupedUnits M n := by
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hf := Nat.lt_floor_add_one
    (Real.rpow (n : ℝ) (3 / 4 : ℝ) / (M : ℝ))
  have hmul := mul_lt_mul_of_pos_left hf hMR
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMR
  simp only [mul_div_cancel₀ _ hMne, mul_add] at hmul
  rw [birthdayGroupedUnits, birthdayGroups, Nat.cast_mul]
  linarith

-- @node: birthdayGroupedUnits_power_identity
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,hn), [the stated equality holds](goal). -/
lemma birthdayGroupedUnits_power_identity (n : ℕ) (hn : 0 < n) :
    (Real.rpow (n : ℝ) (3 / 4 : ℝ) / 2) ^ 2 / (n : ℝ) =
      (1 / 4 : ℝ) * Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsq : (Real.rpow (n : ℝ) (3 / 4 : ℝ)) ^ 2 =
      Real.rpow (n : ℝ) (3 / 2 : ℝ) := by
    calc
      _ = Real.rpow (Real.rpow (n : ℝ) (3 / 4 : ℝ)) (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (n : ℝ) ((3 / 4 : ℝ) * 2) :=
        (Real.rpow_mul (le_of_lt hnR) _ _).symm
      _ = _ := by norm_num
  rw [div_pow, hsq]
  have hdiv : Real.rpow (n : ℝ) (3 / 2 : ℝ) / (n : ℝ) =
      Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
    calc
      _ = Real.rpow (n : ℝ) (3 / 2 : ℝ) / Real.rpow (n : ℝ) 1 := by
        congr 1
        exact (Real.rpow_one _).symm
      _ = Real.rpow (n : ℝ) ((3 / 2 : ℝ) - 1) := (Real.rpow_sub hnR _ _).symm
      _ = _ := by norm_num
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
  calc
    Real.rpow (n : ℝ) (3 / 2 : ℝ) / 4 / (n : ℝ) =
        (1 / 4 : ℝ) * (Real.rpow (n : ℝ) (3 / 2 : ℝ) / (n : ℝ)) := by ring
    _ = _ := by rw [hdiv]

-- @node: birthdayBenchmark_proof
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM), [the birthday benchmark proof result holds](goal). -/
lemma birthdayBenchmark_proof (M : ℕ) (hM : 0 < M) : BirthdayBenchmark M := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (3 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp hcast
  have hx : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (3 / 4 : ℝ) / (M : ℝ))
      atTop atTop := hpow.atTop_div_const (by exact_mod_cast hM)
  have hfloorRatio : Tendsto (fun n : ℕ =>
      (⌊Real.rpow (n : ℝ) (3 / 4 : ℝ) / (M : ℝ)⌋₊ : ℝ) /
        (Real.rpow (n : ℝ) (3 / 4 : ℝ) / (M : ℝ))) atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop.comp hx
  have hneg : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (- (1 / 4 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hcast
  have hratio : Tendsto (fun n => (birthdayGroupedUnits M n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    convert hfloorRatio.mul hneg using 1
    · funext n
      by_cases hn : n = 0
      · subst n
        simp [birthdayGroupedUnits, birthdayGroups]
      · exact birthdayGroupedUnits_ratio_identity M n hM (Nat.pos_of_ne_zero hn)
    · norm_num
  refine ⟨?_, hratio, ?_⟩
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    exact birthdayGroupedUnits_feasible M n hM hn
  · have hsqrt : Tendsto (fun n : ℕ =>
        (1 / 4 : ℝ) * Real.rpow (n : ℝ) (1 / 2 : ℝ)) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hcast).const_mul_atTop
        (by norm_num)
    apply tendsto_atTop_mono' atTop _ hsqrt
    filter_upwards [hpow.eventually (eventually_ge_atTop (2 * (M : ℝ))),
      eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hlarge hn
    have hnpos : 0 < n := by omega
    have hlower := birthdayGroupedUnits_lower_bound M n hM
    have hhalf : Real.rpow (n : ℝ) (3 / 4 : ℝ) / 2 ≤
        (birthdayGroupedUnits M n : ℝ) := by nlinarith
    have hpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (3 / 4 : ℝ) / 2 :=
      div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num)
    have hgroup_nonneg : 0 ≤ (birthdayGroupedUnits M n : ℝ) := Nat.cast_nonneg _
    calc
      (1 / 4 : ℝ) * Real.rpow (n : ℝ) (1 / 2 : ℝ) =
          (Real.rpow (n : ℝ) (3 / 4 : ℝ) / 2) ^ 2 / (n : ℝ) :=
        (birthdayGroupedUnits_power_identity n hnpos).symm
      _ ≤ ((birthdayGroupedUnits M n : ℝ) ^ 2) / (n : ℝ) := by gcongr

-- @node: sparse_dense_ratio_consistency
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,p,B,cSigma,hClass), [the sparse dense ratio consistency result holds](goal). -/
lemma sparse_dense_ratio_consistency {M : ℕ} (hM : 2 ≤ M) (A : ScheduleArray M)
    (p B cSigma : ℝ) (hClass : DenseScheduleClass A p 0 B cSigma) :
    FiniteDesign.TendstoInProb A.design
      (fun r w => A.cr2 r w / A.variance r) (fun _ => 1) := by
  let J : ∀ r, JohnsonProjections (A.popSize r) M :=
    fun r => canonicalJohnsonProjections (A.popSize r) M (A.groupSize_le r)
  have hfront := cr2_phase_frontier hM A p 0 B cSigma J hClass
    (fun r => canonicalJohnsonOrthogonalDecomposition (A.popSize r) M (A.groupSize_le r))
    (fun r => canonicalKneserAdjacencySpectrum (A.popSize r) M)
  apply hfront.2.2.2.mpr
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

-- @node: thm:sparse-beyond-birthday
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM), [the sparse beyond birthday result holds](goal). -/
theorem sparse_beyond_birthday {M : ℕ} (hM : 2 ≤ M) :
    (∀ (A : ScheduleArray M) (p B cSigma : ℝ),
      DenseScheduleClass A p 0 B cSigma →
      FiniteDesign.TendstoInProb A.design
        (fun r w => A.cr2 r w / A.variance r) (fun _ => 1)) ∧
    BirthdayBenchmark M ∧
    (∀ (A : ScheduleArray M) (p B cSigma : ℝ),
      CountAlignment A M →
      GroupCountGrowth A →
      StableTreatmentFraction A p →
      BoundedSchedule A B →
      ScaledVarianceNondegenerate A cSigma →
      FiniteDesign.TendstoInProb A.design
        (fun r w => A.cr2 r w / A.variance r) (fun _ => 1)) := by
  have hMpos : 0 < M := by omega
  have hbench := birthdayBenchmark_proof M hMpos
  refine ⟨?_, hbench, ?_⟩
  · intro A p B cSigma hClass
    exact sparse_dense_ratio_consistency hM A p B cSigma hClass
  · intro A p B cSigma hAlign hGrowth hFraction hBounded hNondegenerate
    have hpop : Tendsto A.popSize atTop atTop := by
      apply tendsto_atTop_mono (fun r => ?_) hGrowth
      exact le_trans (Nat.le_mul_of_pos_left (A.groups r) hMpos) (A.grouped_le r)
    have hsampLimit : Tendsto (fun r => (A.grouped r : ℝ) / (A.popSize r : ℝ))
        atTop (nhds 0) := by
      convert hbench.2.1.comp hpop using 1
      funext r
      simp only [Function.comp_apply]
      rw [hAlign r]
    have hClass : DenseScheduleClass A p 0 B cSigma :=
      ⟨hGrowth, hFraction, ⟨le_rfl, zero_le_one, hsampLimit⟩, hBounded, hNondegenerate⟩
    exact sparse_dense_ratio_consistency hM A p B cSigma hClass

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
