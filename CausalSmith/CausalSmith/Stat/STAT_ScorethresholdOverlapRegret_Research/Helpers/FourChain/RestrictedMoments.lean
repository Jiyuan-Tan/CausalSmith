module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.Welfare
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Integration

/-! # Restricted chain moments

Steps (7) and (8) of the four-chain roadmap: an offset-mass bound controls
restricted score moments, and independence expands the squared sum of marks.
These results do not assume the maximal inequality or its symmetrization.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

/-- The offset-mass bound on a Borel chain union controls its second and fourth
score moments, with the constants in roadmap equation (7). -/
-- @node: chain_restricted_score_moments
lemma chain_restricted_score_moments (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a z : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4) (B : Set ℝ)
    (hB : MeasurableSet B) (hmass : (∫ x in B, offsetG a P.logger x ∂P.PX) ≤ z) :
    (∫ o in {o | o.X ∈ B}, zScore a P.logger o ^ 2 ∂P.obsLaw) ≤ 6*z/a ∧
    (∫ o in {o | o.X ∈ B}, zScore a P.logger o ^ 4 ∂P.obsLaw) ≤ 24*z/a^3 := by
  have h := regularization_inequality α γ θ n P e hP a (fun _ => false) ha
    (Or.inl (fun _ _ => rfl))
  constructor
  · calc
      _ ≤ ∫ x in B, 6 * offsetG a P.logger x / a ∂P.PX := h.2.2.1 B hB
      _ = 6 * (∫ x in B, offsetG a P.logger x ∂P.PX) / a := by
        rw [integral_div, integral_const_mul]
      _ ≤ 6*z/a := div_le_div_of_nonneg_right (by linarith) ha.1.le
  · calc
      _ ≤ ∫ x in B, 24 * offsetG a P.logger x / a^3 ∂P.PX := h.2.2.2 B hB
      _ = 24 * (∫ x in B, offsetG a P.logger x ∂P.PX) / a^3 := by
        rw [integral_div, integral_const_mul]
      _ ≤ 24*z/a^3 := div_le_div_of_nonneg_right (by linarith) (pow_nonneg ha.1.le _)

/-- Different coordinates of a product sample factor their mark expectations. -/
-- @node: chain_product_mark_cross_integral
lemma chain_product_mark_cross_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (f : Ω → ℝ)
    (hf : AEMeasurable f μ) (i j : Fin n) (hij : i ≠ j) :
    (∫ d, f (d i) * f (d j) ∂Measure.pi (fun _ : Fin n => μ)) =
      (∫ x, f x ∂μ)^2 := by
  have hind := ProbabilityTheory.iIndepFun_pi (fun _ : Fin n => hf)
  have hfi := hf.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => μ) i)
  have hfj := hf.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => μ) j)
  rw [(hind.indepFun hij).integral_fun_mul_eq_mul_integral
    hfi.aestronglyMeasurable hfj.aestronglyMeasurable,
    integral_comp_eval hf.aestronglyMeasurable,
    integral_comp_eval hf.aestronglyMeasurable, pow_two]

/-- The squared sum of bounded marks has the exact iid diagonal/off-diagonal
expansion in roadmap equation (8). The bound supplies integrability, not content. -/
-- @node: chain_product_sum_sq_integral
lemma chain_product_sum_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (f : Ω → ℝ)
    (hf : AEMeasurable f μ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ᵐ x ∂μ, |f x| ≤ K) :
    (∫ d, (∑ i : Fin n, f (d i))^2 ∂Measure.pi (fun _ : Fin n => μ)) =
      (n : ℝ) * (∫ x, f x ^ 2 ∂μ) +
      (n : ℝ) * ((n : ℝ)-1) * (∫ x, f x ∂μ)^2 := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  have hm (i : Fin n) : AEMeasurable (fun d => f (d i)) ν :=
    hf.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)
  have hb' (i : Fin n) : ∀ᵐ d ∂ν, |f (d i)| ≤ K :=
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => μ) (i := i)) hb
  have hint (i j : Fin n) : Integrable (fun d => f (d i) * f (d j)) ν := by
    apply score_bounded_integrable (K*K) ((hm i).mul (hm j))
    filter_upwards [hb' i, hb' j] with d hi hj
    change |f (d i) * f (d j)| ≤ K*K
    rw [abs_mul]
    exact mul_le_mul hi hj (abs_nonneg _) hK
  have hexpand (d : Fin n → Ω) :
      (∑ i, f (d i))^2 = ∑ i, ∑ j, f (d i) * f (d j) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j)]
  have hpair (i j : Fin n) :
      (∫ d, f (d i) * f (d j) ∂ν) =
        if j = i then (∫ x, f x^2 ∂μ) else (∫ x, f x ∂μ)^2 := by
    by_cases hji : j = i
    · subst j
      simp only [← pow_two]
      exact integral_comp_eval (μ := fun _ : Fin n => μ) (i := i)
        (hf.pow_const 2).aestronglyMeasurable
    · rw [if_neg hji]
      exact chain_product_mark_cross_integral μ n f hf i j (Ne.symm hji)
  change (∑ i, ∑ j, ∫ d, f (d i) * f (d j) ∂ν) = _
  simp_rw [hpair]
  have hsum (i : Fin n) :
      (∑ j : Fin n, if j = i then (∫ x, f x^2 ∂μ) else (∫ x, f x ∂μ)^2) =
        (∫ x, f x^2 ∂μ) + ((n : ℝ)-1) * (∫ x, f x ∂μ)^2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [Finset.sum_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
    simp only [if_true, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn : 1 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
    rw [Nat.cast_sub hn]
    norm_num
  simp_rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Independence and the restricted score moments give the squared energy
bound in roadmap equation (8), before Rademacher maximal inequalities. -/
-- @node: chain_score_energy_second_moment
lemma chain_score_energy_second_moment (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e) (hn : 0 < n)
    (a z : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4) (B : Set ℝ)
    (hB : MeasurableSet B) (hmass : (∫ x in B, offsetG a P.logger x ∂P.PX) ≤ z) :
    (∫ d, (∑ i : Fin n,
      ({o : Observation | o.X ∈ B}.indicator
        (fun o => zScore a P.logger o^2)) (d i))^2 ∂sampleLaw P n) ≤
        24*(n : ℝ)*z/a^3 + 36*(n : ℝ)^2*z^2/a^2 := by
  have : IsProbabilityMeasure P.full := hP.wf.1
  have : IsProbabilityMeasure P.obsLaw :=
    Measure.isProbabilityMeasure_map score_observation_map_measurable.aemeasurable
  let C : Set Observation := {o | o.X ∈ B}
  have hC : MeasurableSet C := hB.preimage score_observation_X_measurable
  let f : Observation → ℝ := C.indicator (fun o => zScore a P.logger o^2)
  have hf : AEMeasurable f P.obsLaw := by
    exact ((score_z_aemeasurable P hP.wf a).pow_const 2).indicator hC
  have hbound : ∀ᵐ o ∂P.obsLaw, |f o| ≤ (2/a)^2 := by
    have hs := (regularization_inequality α γ θ n P e hP a
      (fun _ => false) ha (Or.inl (fun _ _ => rfl))).2.1
    filter_upwards [hs] with o ho
    by_cases hc : o ∈ C
    · rw [show f o = zScore a P.logger o^2 from Set.indicator_of_mem hc _,
        abs_of_nonneg (sq_nonneg _)]
      have hr : 0 ≤ 2/a := div_nonneg (by norm_num) ha.1.le
      have hh := pow_le_pow_left₀ (abs_nonneg (zScore a P.logger o)) ho 2
      simpa only [sq_abs] using hh
    · simp only [f, Set.indicator_of_notMem hc, abs_zero]
      positivity
  have hfirst : (∫ o, f o ∂P.obsLaw) =
      ∫ o in C, zScore a P.logger o^2 ∂P.obsLaw := integral_indicator hC
  have hfourth : (∫ o, f o^2 ∂P.obsLaw) =
      ∫ o in C, zScore a P.logger o^4 ∂P.obsLaw := by
    rw [← integral_indicator hC]
    apply integral_congr_ae
    exact ae_of_all _ (fun o => by
      by_cases hc : o ∈ C <;> simp [f, Set.indicator, hc, ← pow_mul])
  have hexpand := chain_product_sum_sq_integral P.obsLaw n f hf ((2/a)^2)
    (sq_nonneg _) hbound
  have hlocal := chain_restricted_score_moments α γ θ n P e hP a z ha B hB hmass
  have hf0 : 0 ≤ ∫ o, f o ∂P.obsLaw := integral_nonneg (fun o => by
    exact Set.indicator_nonneg (fun o _ => sq_nonneg _) o)
  have hf1 : (∫ o, f o ∂P.obsLaw) ≤ 6*z/a := by
    rw [hfirst]
    exact hlocal.1
  have hf2 : (∫ o, f o^2 ∂P.obsLaw) ≤ 24*z/a^3 := by
    rw [hfourth]
    exact hlocal.2
  have hsquare : (∫ o, f o ∂P.obsLaw)^2 ≤ (6*z/a)^2 :=
    pow_le_pow_left₀ hf0 hf1 2
  have hnr : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hn1 : 0 ≤ (n : ℝ)-1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hn)
  have hdiag := mul_le_mul_of_nonneg_left hf2 hnr
  have hoff := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hnr hn1)
  have hcount : (n : ℝ)*((n : ℝ)-1) ≤ (n : ℝ)^2 := by nlinarith
  have hoff' := mul_le_mul_of_nonneg_right hcount (sq_nonneg (6*z/a))
  have htotal := add_le_add hdiag (hoff.trans hoff')
  change (∫ d, (∑ i : Fin n, f (d i))^2 ∂Measure.pi (fun _ : Fin n => P.obsLaw)) ≤ _
  rw [hexpand]
  calc
    _ ≤ (n : ℝ) * (24*z/a^3) + (n : ℝ)^2 * (6*z/a)^2 := htotal
    _ = _ := by ring

end CausalSmith.Stat.ScorethresholdOverlapRegret
