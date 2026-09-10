import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Basic
import Mathlib.Data.Real.Basic

set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-! The outcome-null perturbation used by the positive full-law converse. -/

open scoped BigOperators
open Finset Matrix

namespace CausalSmith.SCM.ProxyTargetspanTransport

variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]

-- @node: def:outcome-null-perturbation
/-- [The model, positivity certificate, proxy matrix, target vector, separator, treatment,
outcomes, proxy coordinate, and amplitude](hyp:Mdl,hM,Bx,bvec,h,x,y,ycirc,wstar,t) determine
[the outcome-null perturbation](goal): it [uses the positive proxy cell as its denominator](step:1),
[adds the separator shift to the selected outcome](step:2), [subtracts it from the comparison
outcome](step:3), and [leaves every other kernel cell unchanged](step:4). -/
noncomputable def outcomeNullPerturbation (Mdl : LatentShiftSCM E U W X Y)
    (hM : PositiveLatentShiftClass Mdl)
    (Bx : Matrix W E ℝ) (bvec : W → ℝ) (h : failureSeparator Bx bvec)
    (x : X) (y : Y) (ycirc : {ycirc : Y // ycirc ≠ y})
    (wstar : W) (t : ℝ) : X → Y → U → W → ℝ :=
  fun x' y' u w =>
    let denom : {r : ℝ // 0 < r} :=
      ⟨Mdl.M wstar u, hM.positivity.2.2.1 wstar u⟩
    if x' = x ∧ w = wstar ∧ y' = y then
      Mdl.f x' y' u w + t * latentSeparator Mdl h.1 u / denom.1
    else if x' = x ∧ w = wstar ∧ y' = ycirc.1 then
      Mdl.f x' y' u w - t * latentSeparator Mdl h.1 u / denom.1
    else Mdl.f x' y' u w
-- @realizes f^{(t)}(opposite-sign two-cell outcome perturbation)
-- @realizes w_{\star}(edited proxy cell) @realizes t(real path index)

/-- The model obtained by installing the perturbed outcome kernel and recomputing both full laws.
The normalization obligations are deliberately exposed to Stage 3 through scaffolded proof fields. -/
noncomputable def perturbedModel (Mdl : LatentShiftSCM E U W X Y)
    (hM : PositiveLatentShiftClass Mdl)
    (Bx : Matrix W E ℝ) (bvec : W → ℝ) (h : failureSeparator Bx bvec)
    (x : X) (y : Y) (ycirc : {ycirc : Y // ycirc ≠ y})
    (wstar : W) (t : ℝ)
    (hf_nonneg : ∀ x' y' u w,
      0 ≤ outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar t x' y' u w)
    (hf_col : ∀ x' u w,
      ∑ y', outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar t x' y' u w = 1) :
    LatentShiftSCM E U W X Y where
  environment_nonempty := Mdl.environment_nonempty
  treatment_nonempty := Mdl.treatment_nonempty
  latent_card := Mdl.latent_card
  proxy_card := Mdl.proxy_card
  outcome_card := Mdl.outcome_card
  pi := Mdl.pi
  S := Mdl.S
  M := Mdl.M
  a := Mdl.a
  f := outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar t
  q := Mdl.q
  PM := fun e u w x' y' =>
    Mdl.pi e * Mdl.S u e * Mdl.M w u * Mdl.a x' u *
      outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar t x' y' u w
  QM := fun u w x' y' =>
    Mdl.q u * Mdl.M w u * Mdl.a x' u *
      outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar t x' y' u w
  pi_nonneg := Mdl.pi_nonneg
  pi_sum := Mdl.pi_sum
  S_nonneg := Mdl.S_nonneg
  S_col := Mdl.S_col
  M_nonneg := Mdl.M_nonneg
  M_col := Mdl.M_col
  a_nonneg := Mdl.a_nonneg
  a_col := Mdl.a_col
  f_nonneg := hf_nonneg
  f_col := hf_col
  q_nonneg := Mdl.q_nonneg
  q_sum := Mdl.q_sum
  PM_nonneg := by
    intro e u w x' y'
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (Mdl.pi_nonneg e) (Mdl.S_nonneg u e))
          (Mdl.M_nonneg w u))
        (Mdl.a_nonneg x' u))
      (hf_nonneg x' y' u w)
  PM_sum := by
    simp_rw [← Finset.mul_sum, hf_col, mul_one]
    simp_rw [← Finset.mul_sum, Mdl.a_col, mul_one]
    simp_rw [← Finset.mul_sum, Mdl.M_col, mul_one]
    simp_rw [← Finset.mul_sum, Mdl.S_col, mul_one]
    exact Mdl.pi_sum
  QM_nonneg := by
    intro u w x' y'
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Mdl.q_nonneg u) (Mdl.M_nonneg w u))
        (Mdl.a_nonneg x' u))
      (hf_nonneg x' y' u w)
  QM_sum := by
    simp_rw [← Finset.mul_sum, hf_col, mul_one]
    simp_rw [← Finset.mul_sum, Mdl.a_col, mul_one]
    simp_rw [← Finset.mul_sum, Mdl.M_col, mul_one]
    exact Mdl.q_sum
-- @realizes \mathcal M_t(model with f replaced and laws recomputed)

/-- Given [the positive latent-shift condition, the distinct comparison outcome, the required strict positivity condition](hyp:hM,ycirc,hpos), [a strictly positive baseline outcome kernel admits a positive perturbation radius preserving nonnegativity](goal). -/
lemma perturbation_positive_radius (Mdl : LatentShiftSCM E U W X Y)
    (hM : PositiveLatentShiftClass Mdl)
    (Bx : Matrix W E ℝ) (bvec : W → ℝ) (h : failureSeparator Bx bvec)
    (x : X) (y : Y) (ycirc : {ycirc : Y // ycirc ≠ y}) (wstar : W)
    (hpos : StrictPrimitivePositivity Mdl) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, |t| < ε →
      ∀ x' y' u w,
        0 < outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar t x' y' u w := by
  have hzero : ∀ x' y' u w,
      outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar 0 x' y' u w =
        Mdl.f x' y' u w := by
    intros
    simp [outcomeNullPerturbation]
  have hev_one : ∀ x' y' u w, ∀ᶠ t in nhds (0 : ℝ),
      0 < outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar t x' y' u w := by
    intro x' y' u w
    have hc : ContinuousAt
        (fun t : ℝ => outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar t x' y' u w) 0 := by
      unfold outcomeNullPerturbation
      split_ifs <;> fun_prop
    have hbase : 0 < outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar 0 x' y' u w := by
      rw [hzero]
      exact hpos.2.2.2.2.1 x' y' u w
    exact hc.eventually (eventually_gt_nhds hbase)
  have hev : ∀ᶠ t in nhds (0 : ℝ), ∀ x' y' u w,
      0 < outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar t x' y' u w := by
    simpa only [Filter.eventually_all] using hev_one
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hev⟩ := hev
  exact ⟨ε, hε, fun t ht => hev (by simpa [Real.dist_eq] using ht)⟩
-- @realizes \varepsilon(positive perturbation radius)

-- @node: outcomeNullPerturbation_sum
/-- Given [the positive latent-shift condition, the distinct comparison outcome](hyp:hM,ycirc), [the outcome-null perturbation sums to zero over outcome categories](goal). -/
lemma outcomeNullPerturbation_sum (Mdl : LatentShiftSCM E U W X Y)
    (hM : PositiveLatentShiftClass Mdl)
    (Bx : Matrix W E ℝ) (bvec : W → ℝ) (h : failureSeparator Bx bvec)
    (x : X) (y : Y) (ycirc : {ycirc : Y // ycirc ≠ y})
    (wstar : W) (t : ℝ) : ∀ x' u w,
    ∑ y', outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar t x' y' u w = 1 := by
  intro x' u w
  let d := t * latentSeparator Mdl h.1 u / Mdl.M wstar u
  have hneq : y ≠ ycirc.1 := Ne.symm ycirc.property
  have hp (y' : Y) :
      outcomeNullPerturbation Mdl hM Bx bvec h x y ycirc wstar t x' y' u w =
        Mdl.f x' y' u w + (if x' = x ∧ w = wstar ∧ y' = y then d else 0) -
          (if x' = x ∧ w = wstar ∧ y' = ycirc.1 then d else 0) := by
    unfold outcomeNullPerturbation
    by_cases h1 : x' = x ∧ w = wstar ∧ y' = y
    · simp [h1, hneq, d]
    · by_cases h2 : x' = x ∧ w = wstar ∧ y' = ycirc.1
      · simp [h2, ycirc.property, d]
      · simp [h1, h2]
  simp_rw [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Mdl.f_col]
  by_cases hx : x' = x
  · subst x'
    by_cases hw : w = wstar
    · subst w
      simp [hneq]
    · simp [hw]
  · simp [hx]

-- @node: perturbedModel_interventionalProb_sub
/-- Given [the positive latent-shift condition, the distinct comparison outcome, nonnegativity of the perturbed outcome kernel, normalization of the perturbed outcome kernel, the required strict positivity condition, the admissible perturbation-amplitude bound](hyp:hM,ycirc,hf_nonneg,hf_col,hpos,hb), [the perturbed model changes the selected interventional probability by the separator-target inner product times the perturbation amplitude](goal). -/
lemma perturbedModel_interventionalProb_sub (Mdl : LatentShiftSCM E U W X Y)
    (hM : PositiveLatentShiftClass Mdl)
    (bvec : W → ℝ) (x : X) (h : failureSeparator (condProxyMatrix Mdl x) bvec)
    (y : Y) (ycirc : {ycirc : Y // ycirc ≠ y}) (wstar : W) (t : ℝ)
    (hf_nonneg : ∀ x' y' u w,
      0 ≤ outcomeNullPerturbation Mdl hM (condProxyMatrix Mdl x) bvec h
        x y ycirc wstar t x' y' u w)
    (hf_col : ∀ x' u w,
      ∑ y', outcomeNullPerturbation Mdl hM (condProxyMatrix Mdl x) bvec h
        x y ycirc wstar t x' y' u w = 1)
    (hpos : StrictPrimitivePositivity Mdl)
    (hb : targetProxyVector Mdl = bvec) :
    interventionalProb
        (perturbedModel Mdl hM (condProxyMatrix Mdl x) bvec h
          x y ycirc wstar t hf_nonneg hf_col) x y -
      interventionalProb Mdl x y = t * dotProduct h.1 bvec := by
  have htarget : targetProxyVector Mdl = Mdl.M.mulVec Mdl.q := rfl
  have hslope : dotProduct (latentSeparator Mdl h.1) Mdl.q = dotProduct h.1 bvec := by
    calc
      _ = dotProduct h.1 (Mdl.M.mulVec Mdl.q) := by
        unfold latentSeparator
        rw [Matrix.dotProduct_mulVec]
      _ = dotProduct h.1 (targetProxyVector Mdl) := by rw [htarget]
      _ = _ := congrArg (dotProduct h.1) hb
  have hinner (u : U) :
      (∑ w, Mdl.q u * Mdl.M w u *
          outcomeNullPerturbation Mdl hM (condProxyMatrix Mdl x) bvec h
            x y ycirc wstar t x y u w) =
        (∑ w, Mdl.q u * Mdl.M w u * Mdl.f x y u w) +
          Mdl.q u * t * latentSeparator Mdl h.1 u := by
    have hp (w : W) :
        outcomeNullPerturbation Mdl hM (condProxyMatrix Mdl x) bvec h
            x y ycirc wstar t x y u w =
          Mdl.f x y u w +
            if w = wstar then t * latentSeparator Mdl h.1 u / Mdl.M wstar u else 0 := by
      unfold outcomeNullPerturbation
      by_cases hw : w = wstar
      · subst w
        simp
      · simp [hw]
    simp_rw [hp, mul_add, Finset.sum_add_distrib]
    congr 1
    simp
    field_simp [ne_of_gt (hpos.2.2.1 wstar u)]
  unfold interventionalProb
  simp only [perturbedModel]
  simp_rw [hinner, Finset.sum_add_distrib]
  rw [sub_eq_iff_eq_add, add_comm]
  congr 1
  rw [← hslope]
  unfold dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Given [the positive latent-shift condition, the distinct comparison outcome, nonnegativity of the perturbed outcome kernel, normalization of the perturbed outcome kernel](hyp:hM,ycirc,hf_nonneg,hf_col), [the outcome-null perturbation leaves the complete observed law unchanged](goal). -/
lemma perturbedModel_preserves_observedLaw (Mdl : LatentShiftSCM E U W X Y)
    (hM : PositiveLatentShiftClass Mdl)
    (bvec : W → ℝ) (x : X) (h : failureSeparator (condProxyMatrix Mdl x) bvec)
    (y : Y) (ycirc : {ycirc : Y // ycirc ≠ y})
    (wstar : W) (t : ℝ)
    (hf_nonneg : ∀ x' y' u w,
      0 ≤ outcomeNullPerturbation Mdl hM (condProxyMatrix Mdl x) bvec h
        x y ycirc wstar t x' y' u w)
    (hf_col : ∀ x' u w,
      ∑ y', outcomeNullPerturbation Mdl hM (condProxyMatrix Mdl x) bvec h
        x y ycirc wstar t x' y' u w = 1)
    :
    observedLaw
        (perturbedModel Mdl hM (condProxyMatrix Mdl x) bvec h
          x y ycirc wstar t hf_nonneg hf_col) = observedLaw Mdl := by
  let _ : Nonempty U := Fintype.card_pos_iff.mp
    (lt_of_lt_of_le (by omega : 0 < 2) Mdl.latent_card)
  have hfac := (observable_factorization Mdl hM x y).1
  have hnull : (latentPosterior Mdl x).vecMul (latentSeparator Mdl h.1) = 0 := by
    change (h.1 ᵥ* Mdl.M) ᵥ* latentPosterior Mdl x = 0
    rw [vecMul_vecMul, ← hfac]
    exact h.2.1
  have hrho (e : E) : 0 < sourceTreatmentProb Mdl x e := by
    exact Finset.sum_pos (fun u _ => mul_pos (hM.positivity.2.2.2.1 x u)
      (hM.positivity.2.1 u e)) Finset.univ_nonempty
  have hdelta (e : E) :
      (∑ u, Mdl.pi e * Mdl.S u e * Mdl.M wstar u * Mdl.a x u *
          (t * latentSeparator Mdl h.1 u / Mdl.M wstar u)) = 0 := by
    calc
      _ = ∑ u, Mdl.pi e * Mdl.S u e * Mdl.a x u *
            (t * latentSeparator Mdl h.1 u) := by
              apply Finset.sum_congr rfl
              intro u _
              field_simp [ne_of_gt (hM.positivity.2.2.1 wstar u)]
      _ = Mdl.pi e * sourceTreatmentProb Mdl x e * t *
            ((latentPosterior Mdl x).vecMul (latentSeparator Mdl h.1)) e := by
              simp only [Matrix.vecMul, latentPosterior, dotProduct]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro u _
              field_simp [ne_of_gt (hrho e)]
      _ = 0 := by rw [hnull]; simp
  ext e w' x' y'
  simp only [observedLaw, perturbedModel]
  rw [show (∑ u, Mdl.PM e u w' x' y') =
      ∑ u, Mdl.pi e * Mdl.S u e * Mdl.M w' u * Mdl.a x' u * Mdl.f x' y' u w' by
    apply Finset.sum_congr rfl
    intro u _
    exact hM.factorization e u w' x' y']
  by_cases hx : x' = x
  · subst x'
    by_cases hw : w' = wstar
    · subst w'
      by_cases hy' : y' = y
      · subst y'
        simp only [outcomeNullPerturbation, true_and, and_self, ↓reduceIte]
        calc
          _ = (∑ u, Mdl.pi e * Mdl.S u e * Mdl.M wstar u * Mdl.a x u *
                Mdl.f x y u wstar) +
              ∑ u, Mdl.pi e * Mdl.S u e * Mdl.M wstar u * Mdl.a x u *
                (t * latentSeparator Mdl h.1 u / Mdl.M wstar u) := by
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro u _
                  ring
          _ = _ := by rw [hdelta]; ring
      · by_cases hyc : y' = ycirc.1
        · subst y'
          simp only [outcomeNullPerturbation, true_and, and_self, ycirc.property, ↓reduceIte]
          calc
            _ = (∑ u, Mdl.pi e * Mdl.S u e * Mdl.M wstar u * Mdl.a x u *
                  Mdl.f x ycirc.1 u wstar) -
                ∑ u, Mdl.pi e * Mdl.S u e * Mdl.M wstar u * Mdl.a x u *
                  (t * latentSeparator Mdl h.1 u / Mdl.M wstar u) := by
                    rw [← Finset.sum_sub_distrib]
                    apply Finset.sum_congr rfl
                    intro u _
                    ring
            _ = _ := by rw [hdelta]; ring
        · simp [outcomeNullPerturbation, hy', hyc]
    · simp [outcomeNullPerturbation, hw]
  · simp [outcomeNullPerturbation, hx]

end CausalSmith.SCM.ProxyTargetspanTransport
