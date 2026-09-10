import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.RademacherPriors
import Causalean.Experimentation.FinitePopulationMoments

/-!
# Finite-product Rademacher moments

Exact slice-variance formulas and the basic product-design law of large numbers
used by the Rademacher mixture separation argument.
-/

open scoped BigOperators Topology
open Filter Finset

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.FinitePopulationMoments

-- @node: radMean
/-- For [the stated inputs](hyp:n,u), [rad mean](goal) is defined by the formula below. -/
noncomputable def radMean (n : ℕ) (u : Fin n → Bool) : ℝ :=
  (∑ i, rademacherSign (u i)) / (n : ℝ)

-- @node: radMean_E
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n), [the rad mean e result holds](goal). -/
lemma radMean_E (n : ℕ) : (priorSame n).E (radMean n) = 0 := by
  unfold priorSame radMean
  rw [show (fun u : Fin n → Bool => (∑ i, rademacherSign (u i)) / (n : ℝ)) =
      (fun u => ∑ i, (1 / (n : ℝ)) * rademacherSign (u i)) by
    funext u
    rw [← Finset.mul_sum]
    ring]
  rw [FiniteDesign.E_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [show (fun u : Fin n → Bool => 1 / (n : ℝ) * rademacherSign (u i)) =
      fun u => 1 / (n : ℝ) * (fun b => rademacherSign b) (u i) by rfl,
    FiniteDesign.E_const_mul, FiniteDesign.E_prod_apply, coinDesign_E]
  norm_num [rademacherSign]

-- @node: radMean_var
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n), [the stated variance result holds](goal). -/
lemma radMean_var (n : ℕ) :
    (priorSame n).Var (radMean n) = (n : ℝ) * (1 / (n : ℝ)) ^ 2 := by
  unfold priorSame radMean
  rw [show (fun u : Fin n → Bool => (∑ i, rademacherSign (u i)) / (n : ℝ)) =
      (fun u => ∑ i, (1 / (n : ℝ)) * rademacherSign (u i)) by
    funext u
    rw [← Finset.mul_sum]
    ring]
  rw [FiniteDesign.Var_prod_linear_comb]
  simp only [FiniteDesign.Var_eq, coinDesign_E, rademacherSign]
  norm_num

-- @node: popVar_rademacher
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,hn,u), [the stated variance result holds](goal). -/
lemma popVar_rademacher {n : ℕ} (hn : 0 < n) (u : Fin n → Bool) :
    popVar (fun i => rademacherSign (u i)) =
      (n : ℝ) / ((n : ℝ) - 1) * (1 - radMean n u ^ 2) := by
  unfold popVar popMean radMean
  have hncast : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsq (i : Fin n) : rademacherSign (u i) ^ 2 = 1 := by
    cases u i <;> simp [rademacherSign]
  simp_rw [sub_sq, hsq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (∑ x, 2 * rademacherSign (u x) *
      ((∑ x, rademacherSign (u x)) / (n : ℝ))) =
      2 * (∑ x, rademacherSign (u x)) *
      ((∑ x, rademacherSign (u x)) / (n : ℝ)) by
    rw [Finset.mul_sum, Finset.sum_mul]]
  rw [show (∑ _x : Fin n, ((∑ x, rademacherSign (u x)) / (n : ℝ)) ^ 2) =
      (n : ℝ) * ((∑ x, rademacherSign (u x)) / (n : ℝ)) ^ 2 by simp]
  field_simp
  ring

-- @node: radMean_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:N,hN), [the indicated sequence converges to its stated limit](goal). -/
lemma radMean_tendstoInProb (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    FiniteDesign.TendstoInProb (fun r => priorSame (N r))
      (fun r => radMean (N r)) (fun _ => 0) := by
  have hv : Tendsto (fun r => (priorSame (N r)).Var (radMean (N r)))
      atTop (nhds 0) := by
    simp_rw [radMean_var]
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
    (D := fun r => priorSame (N r)) (X := fun r => radMean (N r)) hv
  simpa [radMean_E] using h

-- @node: radArmMean
/-- For [the stated inputs](hyp:n,z,u), [rad arm mean](goal) is defined by the formula below. -/
noncomputable def radArmMean (n : ℕ) (z : Bool)
    (u : Fin n × Bool → Bool) : ℝ :=
  (∑ i, rademacherSign (u (i, z))) / (n : ℝ)

-- @node: radArmMean_E
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,z), [the rad arm mean e result holds](goal). -/
lemma radArmMean_E (n : ℕ) (z : Bool) :
    (priorIndependent n).E (radArmMean n z) = 0 := by
  unfold priorIndependent radArmMean
  rw [show (fun u : Fin n × Bool → Bool =>
      (∑ i, rademacherSign (u (i, z))) / (n : ℝ)) =
      (fun u => ∑ i, (1 / (n : ℝ)) * rademacherSign (u (i, z))) by
    funext u
    rw [← Finset.mul_sum]
    ring]
  rw [FiniteDesign.E_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [show (fun u : Fin n × Bool → Bool =>
      1 / (n : ℝ) * rademacherSign (u (i, z))) =
      fun u => 1 / (n : ℝ) * (fun b => rademacherSign b) (u (i, z)) by rfl,
    FiniteDesign.E_const_mul, FiniteDesign.E_prod_apply, coinDesign_E]
  norm_num [rademacherSign]

-- @node: radArmMean_var
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,z), [the stated variance result holds](goal). -/
lemma radArmMean_var (n : ℕ) (z : Bool) :
    (priorIndependent n).Var (radArmMean n z) =
      (n : ℝ) * (1 / (n : ℝ)) ^ 2 := by
  unfold priorIndependent radArmMean
  rw [show (fun u : Fin n × Bool → Bool =>
      (∑ i, rademacherSign (u (i, z))) / (n : ℝ)) =
      (fun u => ∑ q : Fin n × Bool,
        (if q.2 = z then 1 / (n : ℝ) else 0) * rademacherSign (u q)) by
    funext u
    rw [Fintype.sum_prod_type]
    cases z <;> simp [← Finset.mul_sum] <;> ring]
  rw [FiniteDesign.Var_prod_linear_comb]
  simp only [FiniteDesign.Var_eq, coinDesign_E, rademacherSign]
  norm_num
  rw [Fintype.sum_prod_type]
  cases z <;> simp

-- @node: radArmMean_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:N,hN,z), [the indicated sequence converges to its stated limit](goal). -/
lemma radArmMean_tendstoInProb (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (z : Bool) :
    FiniteDesign.TendstoInProb (fun r => priorIndependent (N r))
      (fun r => radArmMean (N r) z) (fun _ => 0) := by
  have hv : Tendsto (fun r =>
      (priorIndependent (N r)).Var (radArmMean (N r) z)) atTop (nhds 0) := by
    simp_rw [radArmMean_var]
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
    (D := fun r => priorIndependent (N r))
    (X := fun r => radArmMean (N r) z) hv
  simpa [radArmMean_E] using h

-- @node: rademacherSliceCoefficient_tendsto
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,N,hN), [the indicated sequence converges to its stated limit](goal). -/
lemma rademacherSliceCoefficient_tendsto {M : ℕ} (hM : 0 < M)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun r =>
      (1 / (M : ℝ) - 1 / (N r : ℝ)) * (N r : ℝ) / ((N r : ℝ) - 1))
      atTop (nhds (1 / (M : ℝ))) := by
  have hNR : Tendsto (fun r => (N r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hInv : Tendsto (fun r => ((N r : ℝ))⁻¹) atTop (nhds 0) :=
    hNR.inv_tendsto_atTop
  have hRatio : Tendsto (fun r => (N r : ℝ) / ((N r : ℝ) - 1))
      atTop (nhds 1) := by
    have hden : Tendsto (fun r => 1 - ((N r : ℝ))⁻¹) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hInv
    have hdenInv : Tendsto (fun r => (1 - ((N r : ℝ))⁻¹)⁻¹) atTop (nhds 1) := by
      simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hrewrite : ∀ᶠ r in atTop,
        (N r : ℝ) / ((N r : ℝ) - 1) = (1 - ((N r : ℝ))⁻¹)⁻¹ := by
      filter_upwards [hN.eventually (eventually_ge_atTop 1)] with r hr
      have hne : (N r : ℝ) ≠ 0 := by exact_mod_cast (by omega : N r ≠ 0)
      field_simp
    have hrewrite' : (fun r => (1 - ((N r : ℝ))⁻¹)⁻¹) =ᶠ[atTop]
        (fun r => (N r : ℝ) / ((N r : ℝ) - 1)) :=
      hrewrite.mono fun _ hr => hr.symm
    exact hdenInv.congr' hrewrite'
  have hleft : Tendsto (fun r => 1 / (M : ℝ) - ((N r : ℝ))⁻¹)
      atTop (nhds (1 / (M : ℝ))) := by
    simpa using (tendsto_const_nhds.sub hInv)
  convert hleft.mul hRatio using 1 <;> ring

-- @node: armTable_samePrior_eq_sampleMean
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,u,z), [the stated equality holds](goal). -/
lemma armTable_samePrior_eq_sampleMean {n M : ℕ} (u : Fin n → Bool) (z : Bool) :
    armTable n M (samePriorSchedule n M u) z =
      sampleMean M (fun i => rademacherSign (u i)) := by
  funext A
  simp only [armTable, samePriorSchedule, sampleMean]
  congr 1
  calc
    _ = ∑ x ∈ A.1, rademacherSign (u x) := Finset.sum_attach _ _
    _ = _ := by simp

-- @node: armTable_independentPrior_eq_sampleMean
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,u,z), [the stated equality holds](goal). -/
lemma armTable_independentPrior_eq_sampleMean {n M : ℕ}
    (u : Fin n × Bool → Bool) (z : Bool) :
    armTable n M (independentPriorSchedule n M u) z =
      sampleMean M (fun i => rademacherSign (u (i, z))) := by
  funext A
  simp only [armTable, independentPriorSchedule, sampleMean]
  congr 1
  calc
    _ = ∑ x ∈ A.1, rademacherSign (u (x, z)) := Finset.sum_attach _ _
    _ = _ := by simp

-- @node: armVar_samePrior_eq_popVar
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,hMpos,hn,u,z), [the stated variance result holds](goal). -/
lemma armVar_samePrior_eq_popVar {n M : ℕ} (hM : M ≤ n) (hMpos : 0 < M)
    (hn : 2 ≤ n) (u : Fin n → Bool) (z : Bool) :
    armVar n M hM (samePriorSchedule n M u) z =
      (1 / (M : ℝ) - 1 / (n : ℝ)) * popVar (fun i => rademacherSign (u i)) := by
  unfold armVar
  rw [armTable_samePrior_eq_sampleMean]
  unfold slice
  simpa using (Var_sampleMean (U := Fin n) M (by simpa using hM) hMpos
    (by simpa using hn) (fun i => rademacherSign (u i)))

-- @node: armVar_independentPrior_eq_popVar
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,hMpos,hn,u,z), [the stated variance result holds](goal). -/
lemma armVar_independentPrior_eq_popVar {n M : ℕ} (hM : M ≤ n) (hMpos : 0 < M)
    (hn : 2 ≤ n) (u : Fin n × Bool → Bool) (z : Bool) :
    armVar n M hM (independentPriorSchedule n M u) z =
      (1 / (M : ℝ) - 1 / (n : ℝ)) *
        popVar (fun i => rademacherSign (u (i, z))) := by
  unfold armVar
  rw [armTable_independentPrior_eq_sampleMean]
  unfold slice
  simpa using (Var_sampleMean (U := Fin n) M (by simpa using hM) hMpos
    (by simpa using hn) (fun i => rademacherSign (u (i, z))))

-- @node: armVar_samePrior_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,N,hMN,hNtwo,hN,z), [the indicated sequence converges to its stated limit](goal). -/
lemma armVar_samePrior_tendstoInProb {M : ℕ} (hM : 0 < M)
    (N : ℕ → ℕ) (hMN : ∀ r, M ≤ N r) (hNtwo : ∀ r, 2 ≤ N r)
    (hN : Tendsto N atTop atTop) (z : Bool) :
    FiniteDesign.TendstoInProb (fun r => priorSame (N r))
      (fun r u => armVar (N r) M (hMN r) (samePriorSchedule (N r) M u) z)
      (fun _ => 1 / (M : ℝ)) := by
  let c : ℕ → ℝ := fun r =>
    (1 / (M : ℝ) - 1 / (N r : ℝ)) * (N r : ℝ) / ((N r : ℝ) - 1)
  have hc : Tendsto c atTop (nhds (1 / (M : ℝ))) :=
    rademacherSliceCoefficient_tendsto hM N hN
  have hm := radMean_tendstoInProb N hN
  have hm2 := FiniteDesign.tendstoInProb_continuousMap
    (fun r => priorSame (N r)) (fun r => radMean (N r)) 0 (fun x => x ^ 2) hm
      (continuousAt_id.pow 2)
  intro ε hε
  have ht := hm2 (ε / 2) (by linarith)
  have hec : ∀ᶠ r in atTop, |c r - 1 / (M : ℝ)| < ε / 2 := by
    simpa [Real.dist_eq] using (Metric.tendsto_atTop.1 hc (ε / 2) (by linarith))
  apply squeeze_zero' (Eventually.of_forall fun r => (priorSame (N r)).Pr_nonneg _) _ ht
  filter_upwards [hec] with r hcr
  apply (priorSame (N r)).Pr_mono
  intro u hu
  rw [armVar_samePrior_eq_popVar (hMN r) hM (hNtwo r),
    popVar_rademacher (lt_of_lt_of_le hM (hMN r))] at hu
  have hform :
      (1 / (M : ℝ) - 1 / (N r : ℝ)) *
          ((N r : ℝ) / ((N r : ℝ) - 1) * (1 - radMean (N r) u ^ 2)) =
        c r * (1 - radMean (N r) u ^ 2) := by
    dsimp [c]
    ring
  rw [hform] at hu
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNtwoR : (2 : ℝ) ≤ N r := by exact_mod_cast hNtwo r
  have hNr : (0 : ℝ) < N r := by linarith
  have hNr1 : (0 : ℝ) < (N r : ℝ) - 1 := by linarith
  have hMNreal : (M : ℝ) ≤ N r := by exact_mod_cast hMN r
  have hc_formula : c r =
      ((N r : ℝ) - M) / ((M : ℝ) * ((N r : ℝ) - 1)) := by
    dsimp [c]
    field_simp
  have hc_nonneg : 0 ≤ c r := by
    rw [hc_formula]
    exact div_nonneg (sub_nonneg.mpr hMNreal) (mul_nonneg hMr.le hNr1.le)
  have hc_le_one : c r ≤ 1 := by
    rw [hc_formula, div_le_one (mul_pos hMr hNr1)]
    nlinarith [mul_nonneg hNr.le (sub_nonneg.mpr hMone)]
  have hbound :
      |c r * (1 - radMean (N r) u ^ 2) - 1 / (M : ℝ)| ≤
        |c r - 1 / (M : ℝ)| + radMean (N r) u ^ 2 := by
    have hid : c r * (1 - radMean (N r) u ^ 2) - 1 / (M : ℝ) =
        (c r - 1 / (M : ℝ)) - c r * radMean (N r) u ^ 2 := by ring
    calc
      _ = |(c r - 1 / (M : ℝ)) - c r * radMean (N r) u ^ 2| := by rw [hid]
      _ ≤ |c r - 1 / (M : ℝ)| + |c r * radMean (N r) u ^ 2| := abs_sub _ _
      _ ≤ |c r - 1 / (M : ℝ)| + radMean (N r) u ^ 2 := by
        rw [abs_of_nonneg (mul_nonneg hc_nonneg (sq_nonneg _))]
        nlinarith [mul_le_mul_of_nonneg_right hc_le_one
          (sq_nonneg (radMean (N r) u))]
  have hsquare : ε / 2 ≤ radMean (N r) u ^ 2 := by linarith
  rw [zero_pow (by omega : 2 ≠ 0), sub_zero, abs_of_nonneg (sq_nonneg _)]
  exact hsquare

-- @node: armVar_independentPrior_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,N,hMN,hNtwo,hN,z), [the indicated sequence converges to its stated limit](goal). -/
lemma armVar_independentPrior_tendstoInProb {M : ℕ} (hM : 0 < M)
    (N : ℕ → ℕ) (hMN : ∀ r, M ≤ N r) (hNtwo : ∀ r, 2 ≤ N r)
    (hN : Tendsto N atTop atTop) (z : Bool) :
    FiniteDesign.TendstoInProb (fun r => priorIndependent (N r))
      (fun r u => armVar (N r) M (hMN r) (independentPriorSchedule (N r) M u) z)
      (fun _ => 1 / (M : ℝ)) := by
  let c : ℕ → ℝ := fun r =>
    (1 / (M : ℝ) - 1 / (N r : ℝ)) * (N r : ℝ) / ((N r : ℝ) - 1)
  have hc : Tendsto c atTop (nhds (1 / (M : ℝ))) :=
    rademacherSliceCoefficient_tendsto hM N hN
  have hm := radArmMean_tendstoInProb N hN z
  have hm2 := FiniteDesign.tendstoInProb_continuousMap
    (fun r => priorIndependent (N r)) (fun r => radArmMean (N r) z) 0
      (fun x => x ^ 2) hm (continuousAt_id.pow 2)
  intro ε hε
  have ht := hm2 (ε / 2) (by linarith)
  have hec : ∀ᶠ r in atTop, |c r - 1 / (M : ℝ)| < ε / 2 := by
    simpa [Real.dist_eq] using (Metric.tendsto_atTop.1 hc (ε / 2) (by linarith))
  apply squeeze_zero'
    (Eventually.of_forall fun r => (priorIndependent (N r)).Pr_nonneg _) _ ht
  filter_upwards [hec] with r hcr
  apply (priorIndependent (N r)).Pr_mono
  intro u hu
  rw [armVar_independentPrior_eq_popVar (hMN r) hM (hNtwo r),
    popVar_rademacher (lt_of_lt_of_le hM (hMN r))] at hu
  change ε ≤ |(1 / (M : ℝ) - 1 / (N r : ℝ)) *
    ((N r : ℝ) / ((N r : ℝ) - 1) * (1 - radArmMean (N r) z u ^ 2)) -
      1 / (M : ℝ)| at hu
  have hform :
      (1 / (M : ℝ) - 1 / (N r : ℝ)) *
          ((N r : ℝ) / ((N r : ℝ) - 1) * (1 - radArmMean (N r) z u ^ 2)) =
        c r * (1 - radArmMean (N r) z u ^ 2) := by
    dsimp [c]
    ring
  rw [hform] at hu
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNtwoR : (2 : ℝ) ≤ N r := by exact_mod_cast hNtwo r
  have hNr : (0 : ℝ) < N r := by linarith
  have hNr1 : (0 : ℝ) < (N r : ℝ) - 1 := by linarith
  have hMNreal : (M : ℝ) ≤ N r := by exact_mod_cast hMN r
  have hc_formula : c r =
      ((N r : ℝ) - M) / ((M : ℝ) * ((N r : ℝ) - 1)) := by
    dsimp [c]
    field_simp
  have hc_nonneg : 0 ≤ c r := by
    rw [hc_formula]
    exact div_nonneg (sub_nonneg.mpr hMNreal) (mul_nonneg hMr.le hNr1.le)
  have hc_le_one : c r ≤ 1 := by
    rw [hc_formula, div_le_one (mul_pos hMr hNr1)]
    nlinarith [mul_nonneg hNr.le (sub_nonneg.mpr hMone)]
  have hbound :
      |c r * (1 - radArmMean (N r) z u ^ 2) - 1 / (M : ℝ)| ≤
        |c r - 1 / (M : ℝ)| + radArmMean (N r) z u ^ 2 := by
    have hid : c r * (1 - radArmMean (N r) z u ^ 2) - 1 / (M : ℝ) =
        (c r - 1 / (M : ℝ)) - c r * radArmMean (N r) z u ^ 2 := by ring
    calc
      _ = |(c r - 1 / (M : ℝ)) - c r * radArmMean (N r) z u ^ 2| := by rw [hid]
      _ ≤ |c r - 1 / (M : ℝ)| + |c r * radArmMean (N r) z u ^ 2| := abs_sub _ _
      _ ≤ |c r - 1 / (M : ℝ)| + radArmMean (N r) z u ^ 2 := by
        rw [abs_of_nonneg (mul_nonneg hc_nonneg (sq_nonneg _))]
        nlinarith [mul_le_mul_of_nonneg_right hc_le_one
          (sq_nonneg (radArmMean (N r) z u))]
  have hsquare : ε / 2 ≤ radArmMean (N r) z u ^ 2 := by linarith
  rw [zero_pow (by omega : 2 ≠ 0), sub_zero, abs_of_nonneg (sq_nonneg _)]
  exact hsquare

-- @node: scheduleArray_same_armVar_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,hGrowth,z), [the indicated sequence converges to its stated limit](goal). -/
lemma scheduleArray_same_armVar_tendstoInProb {M : ℕ} (A : ScheduleArray M)
    (hGrowth : GroupCountGrowth A) (z : Bool) :
    FiniteDesign.TendstoInProb (fun r => priorSame (A.popSize r))
      (fun r u => armVar (A.popSize r) M (A.groupSize_le r)
        (samePriorSchedule (A.popSize r) M u) z)
      (fun _ => 1 / (M : ℝ)) := by
  exact armVar_samePrior_tendstoInProb
    (A.groupSize_ge_two.trans' (by omega)) A.popSize A.groupSize_le
    (fun r => le_trans A.groupSize_ge_two (A.groupSize_le r))
    (A.popSize_tendsto_atTop hGrowth) z

-- @node: scheduleArray_independent_armVar_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,hGrowth,z), [the indicated sequence converges to its stated limit](goal). -/
lemma scheduleArray_independent_armVar_tendstoInProb {M : ℕ} (A : ScheduleArray M)
    (hGrowth : GroupCountGrowth A) (z : Bool) :
    FiniteDesign.TendstoInProb (fun r => priorIndependent (A.popSize r))
      (fun r u => armVar (A.popSize r) M (A.groupSize_le r)
        (independentPriorSchedule (A.popSize r) M u) z)
      (fun _ => 1 / (M : ℝ)) := by
  exact armVar_independentPrior_tendstoInProb
    (A.groupSize_ge_two.trans' (by omega)) A.popSize A.groupSize_le
    (fun r => le_trans A.groupSize_ge_two (A.groupSize_le r))
    (A.popSize_tendsto_atTop hGrowth) z

-- @node: degreeOneEnergy_samePrior
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMpos,hM,J,u), [the degree one energy same prior result holds](goal). -/
lemma degreeOneEnergy_samePrior {n M : ℕ} (hMpos : 0 < M) (hM : M ≤ n)
    (J : JohnsonProjections n M) (u : Fin n → Bool) :
    degreeOneEnergy n M hMpos hM J (samePriorSchedule n M u) = 0 := by
  unfold degreeOneEnergy
  have hz : (fun A => armTable n M (samePriorSchedule n M u) true A -
      armTable n M (samePriorSchedule n M u) false A) = 0 := by
    funext A
    simp [armTable, samePriorSchedule]
  rw [hz]
  have hpzero : J.proj ⟨1, by omega⟩ 0 = 0 := by
    have hzero := J.map_smul ⟨1, by omega⟩ 0 (fun _ : Omega n M => (0 : ℝ))
    funext A
    change J.proj ⟨1, by omega⟩ (fun _ => 0) A = 0
    simpa only [zero_mul] using congrFun hzero A
  rw [hpzero]
  simp [sliceNorm, sliceNormSq, sliceInner]

-- @node: scheduleArray_same_degreeOne_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,J), [the indicated sequence converges to its stated limit](goal). -/
lemma scheduleArray_same_degreeOne_tendstoInProb {M : ℕ} (A : ScheduleArray M)
    (J : ∀ r, JohnsonProjections (A.popSize r) M) :
    FiniteDesign.TendstoInProb (fun r => priorSame (A.popSize r))
      (fun r u => degreeOneEnergy (A.popSize r) M
        (A.groupSize_ge_two.trans' (by omega)) (A.groupSize_le r)
        (J r) (samePriorSchedule (A.popSize r) M u)) (fun _ => 0) := by
  intro ε hε
  have hzero : (fun r => (priorSame (A.popSize r)).Pr (fun u =>
      ε ≤ |degreeOneEnergy (A.popSize r) M
        (A.groupSize_ge_two.trans' (by omega)) (A.groupSize_le r)
        (J r) (samePriorSchedule (A.popSize r) M u) - 0|)) = fun _ => 0 := by
    funext r
    unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
    simp [degreeOneEnergy_samePrior, not_le.mpr hε]
  rw [hzero]
  exact tendsto_const_nhds

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
