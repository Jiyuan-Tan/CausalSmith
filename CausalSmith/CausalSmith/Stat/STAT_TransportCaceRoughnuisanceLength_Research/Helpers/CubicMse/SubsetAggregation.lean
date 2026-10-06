module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CellPairCovariance

/-! # Cell-pair aggregation for one, two, or three residual blocks -/

public section

open scoped BigOperators

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The diagonal/off-diagonal cell-pair estimate uniformly for any finite
number `q` of factored residual blocks.  The cubic proof consumes `q=1,2,3`.  Under [the displayed assumptions and inputs](hyp:K,q,c,κ,C,D,O,hC,hD,hO,hc,hκdiag,hκoff), [the stated conclusion holds](goal). -/
lemma abs_cellPair_product_sum_le {K q : ℕ} (c : Fin K → ℝ)
    (κ : Fin q → Fin K → Fin K → ℝ) (C D O : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hO : 0 ≤ O)
    (hc : ∀ l, |c l| ≤ C)
    (hκdiag : ∀ t l, |κ t l l| ≤ D)
    (hκoff : ∀ t l r, l ≠ r → |κ t l r| ≤ O) :
    |∑ l : Fin K, ∑ r : Fin K, c l * c r * ∏ t : Fin q, κ t l r| ≤
      (K : ℝ) * C ^ 2 * D ^ q + (K : ℝ) ^ 2 * C ^ 2 * O ^ q := by
  calc
    |∑ l : Fin K, ∑ r : Fin K, c l * c r * ∏ t : Fin q, κ t l r| ≤
        ∑ l : Fin K, ∑ r : Fin K, |c l * c r * ∏ t : Fin q, κ t l r| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ l : Fin K, ∑ r : Fin K,
        if l = r then C ^ 2 * D ^ q else C ^ 2 * O ^ q := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul, abs_mul, Finset.abs_prod]
      have hcc : |c l| * |c r| ≤ C ^ 2 := by
        simpa [pow_two] using mul_le_mul (hc l) (hc r) (abs_nonneg _) hC
      by_cases hlr : l = r
      · subst r
        simp only [if_pos rfl]
        have hp : ∏ t : Fin q, |κ t l l| ≤ D ^ q := by
          calc
            ∏ t : Fin q, |κ t l l| ≤ ∏ _t : Fin q, D :=
              Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun t _ => hκdiag t l)
            _ = D ^ q := by simp
        exact mul_le_mul hcc hp (Finset.prod_nonneg fun _ _ => abs_nonneg _) (sq_nonneg C)
      · simp only [if_neg hlr]
        have hp : ∏ t : Fin q, |κ t l r| ≤ O ^ q := by
          calc
            ∏ t : Fin q, |κ t l r| ≤ ∏ _t : Fin q, O :=
              Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun t _ => hκoff t l r hlr)
            _ = O ^ q := by simp
        exact mul_le_mul hcc hp (Finset.prod_nonneg fun _ _ => abs_nonneg _) (sq_nonneg C)
    _ ≤ ∑ l : Fin K, (C ^ 2 * D ^ q + (K : ℝ) * C ^ 2 * O ^ q) := by
      apply Finset.sum_le_sum
      intro l _
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
      simp only [if_pos rfl]
      have hnonneg : 0 ≤ C ^ 2 * O ^ q :=
        mul_nonneg (sq_nonneg C) (pow_nonneg hO q)
      have herase : ∑ r ∈ Finset.univ.erase l,
          (if l = r then C ^ 2 * D ^ q else C ^ 2 * O ^ q) =
          (Finset.univ.erase l).card * (C ^ 2 * O ^ q) := by
        calc
          _ = ∑ _r ∈ Finset.univ.erase l, C ^ 2 * O ^ q := by
            apply Finset.sum_congr rfl
            intro r hr
            simp only [Finset.mem_erase] at hr
            simp [hr.1.symm]
          _ = _ := by simp
      rw [herase]
      have hcard : (((Finset.univ.erase l).card : ℕ) : ℝ) ≤ K := by
        norm_cast
        simp
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcard hnonneg
    _ = (K : ℝ) * C ^ 2 * D ^ q + (K : ℝ) ^ 2 * C ^ 2 * O ^ q := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Variance of a cell sum after a `q`-block conditional covariance has
factored into its blockwise cell-pair covariances.  Under [the displayed assumptions and inputs](hyp:Ω,K,q,Y,c,κ,C,D,O,hC,hD,hO,hY,hcov,hc,hκdiag,hκoff), [the stated conclusion holds](goal). -/
-- @node: variance_cellSum_factored_le
lemma variance_cellSum_factored_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {K q : ℕ} (Y : Fin K → Ω → ℝ) (c : Fin K → ℝ)
    (κ : Fin q → Fin K → Fin K → ℝ) (C D O : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hO : 0 ≤ O)
    (hY : ∀ l, MeasureTheory.MemLp (Y l) 2 μ)
    (hcov : ∀ l r, ProbabilityTheory.covariance (Y l) (Y r) μ =
      c l * c r * ∏ t : Fin q, κ t l r)
    (hc : ∀ l, |c l| ≤ C)
    (hκdiag : ∀ t l, |κ t l l| ≤ D)
    (hκoff : ∀ t l r, l ≠ r → |κ t l r| ≤ O) :
    ProbabilityTheory.variance (fun ω => ∑ l : Fin K, Y l ω) μ ≤
      (K : ℝ) * C ^ 2 * D ^ q + (K : ℝ) ^ 2 * C ^ 2 * O ^ q := by
  rw [ProbabilityTheory.variance_fun_sum hY]
  calc
    ∑ l : Fin K, ∑ r : Fin K, ProbabilityTheory.covariance (Y l) (Y r) μ =
        ∑ l : Fin K, ∑ r : Fin K, c l * c r * ∏ t : Fin q, κ t l r := by
          apply Finset.sum_congr rfl
          intro l _
          apply Finset.sum_congr rfl
          intro r _
          exact hcov l r
    _ ≤ |∑ l : Fin K, ∑ r : Fin K,
          c l * c r * ∏ t : Fin q, κ t l r| := le_abs_self _
    _ ≤ _ := abs_cellPair_product_sum_le c κ C D O hC hD hO hc hκdiag hκoff

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
