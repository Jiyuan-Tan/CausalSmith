module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.PilotMoments

/-! # Exact cancellation of one within-cell projection residual -/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- [The cell average object](goal) is defined from [the supplied inputs](hyp:f,K). -/

noncomputable def cellAverage (f : ℝ → ℝ) (K : ℕ) (ℓ : Fin K) : ℝ :=
  (K : ℝ) * ∫ x in cell K ℓ, f x
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,i), [the stated result about one residual cell cancellation holds](goal). -/

lemma one_residual_cell_cancellation (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ)
    (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (ℓ : Fin K) (i : Fin 7) :
    ∫ x in cell K ℓ,
      (markedDensityVector c_f C_f L P n hP x i -
        cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K ℓ) = 0 := by
  let f := fun x => markedDensityVector c_f C_f L P n hP x i
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hcell : volume (cell K ℓ) = ENNReal.ofReal (1 / (K : ℝ)) := by
    unfold cell
    split_ifs with hlast
    · have hlast' : (ℓ.val : ℝ) + 1 = K := by exact_mod_cast hlast
      simp only [Real.volume_Icc]
      congr 1
      field_simp
      linarith
    · simp only [Real.volume_Ico]
      congr 1
      field_simp
      ring
  have hfinite : volume (cell K ℓ) ≠ ⊤ := by rw [hcell]; exact ENNReal.ofReal_ne_top
  have havg : cellAverage f K ℓ = ⨍ x in cell K ℓ, f x := by
    rw [MeasureTheory.setAverage_eq]
    have hreal : volume.real (cell K ℓ) = 1 / (K : ℝ) := by
      rw [MeasureTheory.Measure.real, hcell]
      simp [hKreal.le]
    simp only [cellAverage, hreal, smul_eq_mul]
    congr 1
    field_simp
  change ∫ x in cell K ℓ, f x - cellAverage f K ℓ = 0
  rw [havg]
  exact MeasureTheory.setAverage_sub_setAverage hfinite f

/-- Any cell-constant Taylor coefficient and any finite collection of
cell-constant projected factors can multiply one residual without changing
its zero integral. This covers every one-residual quadratic and cubic term.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,q,hP,hK,i,a,d,ha,hd), [the stated conclusion holds](goal). -/
-- @node: one_residual_cell_product_cancellation
lemma one_residual_cell_product_cancellation (c_f C_f L : ℝ)
    (P : TransportLaw) (n K q : ℕ)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (ℓ : Fin K) (i : Fin 7) (a : ℝ → ℝ) (d : Fin q → ℝ → ℝ)
    (a₀ : ℝ) (d₀ : Fin q → ℝ)
    (ha : ∀ x ∈ cell K ℓ, a x = a₀)
    (hd : ∀ j, ∀ x ∈ cell K ℓ, d j x = d₀ j) :
    (∫ x in cell K ℓ, a x * (∏ j : Fin q, d j x) *
      (markedDensityVector c_f C_f L P n hP x i -
        cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K ℓ)) = 0 := by
  classical
  calc
    _ = ∫ x in cell K ℓ, (a₀ * ∏ j : Fin q, d₀ j) *
        (markedDensityVector c_f C_f L P n hP x i -
          cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K ℓ) := by
      apply setIntegral_congr_fun (by unfold cell; split_ifs <;> measurability)
      intro x hx
      dsimp only
      rw [ha x hx]
      congr 2
      exact Finset.prod_congr rfl (fun j _ => hd j x hx)
    _ = (a₀ * ∏ j : Fin q, d₀ j) * ∫ x in cell K ℓ,
        (markedDensityVector c_f C_f L P n hP x i -
          cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K ℓ) :=
      integral_const_mul _ _
    _ = 0 := by
      rw [one_residual_cell_cancellation c_f C_f L P n K hP hK ℓ i, mul_zero]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
