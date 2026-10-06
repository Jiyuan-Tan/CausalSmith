module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreLedger

/-! Exact outcome-free treatment coefficients and telescoping of their dyadic corrections. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Differencing the single-record scores removes the clipped outcome exactly. [This is the stated conclusion](goal). -/
-- @node: hScore_treatment_coefficient
lemma hScore_treatment_coefficient (n J : ℕ) (b : Bool) (T : ℝ) (data : Dataset n) :
    hScore n b J T 0 data-hScore n b J T 1 data = hTreatment n b J data := by
  simp only [hScore, zero_smul, one_smul, sub_zero]
  module

/-- Differencing the ordered-pair scores removes the clipped outcome exactly. [This is the stated conclusion](goal). -/
-- @node: uScore_treatment_coefficient
lemma uScore_treatment_coefficient (n J : ℕ) (b : Bool)
    (G : unitInterval → unitInterval → ℝ) (T : ℝ) (data : Dataset n) :
    uScore n b J G T 0 data-uScore n b J G T 1 data = uTreatment n b J G data := by
  simp only [uScore, zero_smul, one_smul, sub_zero]
  module

/-- Treatment-weighted pair averages preserve subtraction of histogram kernels. [This is the stated conclusion](goal). -/
-- @node: uTreatment_diffKernel
lemma uTreatment_diffKernel (n J K : ℕ) (b : Bool) (data : Dataset n) :
    uTreatment n b J (diffKernel K) data =
      uTreatment n b J (projKernel (2*K)) data-uTreatment n b J (projKernel K) data := by
  simp only [uTreatment, diffKernel]
  by_cases hn : n < 4
  · simp [hn]
  · simp only [if_neg hn, mul_sub, sub_mul, sub_smul, Finset.sum_sub_distrib, smul_sub]

/-- The initial treatment correction and its increments telescope to the final histogram rank. [This is the stated conclusion](goal). -/
-- @node: uTreatment_dyadic_telescope
lemma uTreatment_dyadic_telescope (n J L : ℕ) (b : Bool) (data : Dataset n) :
    uTreatment n b J (projKernel J) data+
      (∑ j : Fin L, uTreatment n b J (diffKernel (2^j.val*J)) data) =
    uTreatment n b J (projKernel (2^L*J)) data := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Fin.sum_univ_castSucc, ← add_assoc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, uTreatment_diffKernel, pow_succ]
    have hr : 2*(2^L*J) = 2^L*2*J := by ring
    rw [hr]
    module

/-- Multilevel treatment coefficients have no tail terms: all correction levels telescope. [This is the stated conclusion](goal). -/
-- @node: multiresScore_treatment_coefficient
lemma multiresScore_treatment_coefficient (n J L : ℕ) (b : Bool)
    (T0 : ℝ) (T : Fin L → ℝ) (data : Dataset n) :
    multiresScore n b J L T0 T 0 data-multiresScore n b J L T0 T 1 data =
      hTreatment n b J data-uTreatment n b J (projKernel (2^L*J)) data := by
  have hh := hScore_treatment_coefficient n J b T0 data
  have hu := uScore_treatment_coefficient n J b (projKernel J) T0 data
  have hd := fun j : Fin L => uScore_treatment_coefficient n J b
    (diffKernel (2^j.val*J)) (T j) data
  have hs : (∑ j : Fin L, uScore n b J (diffKernel (2^j.val*J)) (T j) 0 data)-
      (∑ j : Fin L, uScore n b J (diffKernel (2^j.val*J)) (T j) 1 data) =
      ∑ j : Fin L, uTreatment n b J (diffKernel (2^j.val*J)) data := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [hd]
  have ht := uTreatment_dyadic_telescope n J L b data
  unfold multiresScore
  calc
    _ = (hScore n b J T0 0 data-hScore n b J T0 1 data)-
        (uScore n b J (projKernel J) T0 0 data-uScore n b J (projKernel J) T0 1 data)-
        ((∑ j : Fin L, uScore n b J (diffKernel (2^j.val*J)) (T j) 0 data)-
         (∑ j : Fin L, uScore n b J (diffKernel (2^j.val*J)) (T j) 1 data)) := by module
    _ = _ := by rw [hh, hu, hs, ← ht]; module

end CausalSmith.Stat.FinitepHomogeneityDensegamma
