import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Cr2Concentration

/-!
# CR2 ratio and convergence helpers
-/

open scoped Topology
open Filter

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

-- @node: cr2_ratio_leading_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,p,rho,B,cSigma,J,hClass,hJohnson,hKneser), [the indicated sequence converges to its stated limit](goal). -/
lemma cr2_ratio_leading_tendstoInProb {M : ℕ} (hM : 2 ≤ M) (A : ScheduleArray M)
    (p rho B cSigma : ℝ) (J : ∀ r, JohnsonProjections (A.popSize r) M)
    (hClass : DenseScheduleClass A p rho B cSigma)
    (hJohnson : ∀ r, JohnsonOrthogonalDecomposition (A.popSize r) M (J r))
    (hKneser : ∀ r, KneserAdjacencySpectrum (A.popSize r) M) :
    FiniteDesign.TendstoInProb A.design
      (fun r w => A.cr2 r w / A.variance r)
      (fun r => A.leadingVariance r /
        (A.leadingVariance r - rho * A.degreeOne (by omega) J r)) := by
  let d : ℕ → ℝ := fun r =>
    A.leadingVariance r - rho * A.degreeOne (by omega) J r
  have hu := cr2_centered_tendstoInProb hM A p B J hClass.growth hClass.fraction
    hClass.bounded hJohnson hKneser
  obtain ⟨C0, hC0, hdense⟩ := dense_projection_limit hM p rho B
  have hv := (hdense A J hClass.growth hClass.fraction hClass.sampling hClass.bounded
    hJohnson hKneser).1
  have hxlow := scaledVariance_eventually_lower A cSigma hClass.nondegenerate
  have herr : ∀ᶠ r in atTop,
      |(A.groups r : ℝ) * A.variance r - d r| < cSigma / 4 := by
    have heps : 0 < cSigma / 4 := by linarith [hClass.nondegenerate.1]
    simpa [Real.dist_eq, d] using (Metric.tendsto_atTop.1 hv (cSigma / 4) heps)
  have hdlow : ∀ᶠ r in atTop, cSigma / 4 < d r := by
    filter_upwards [hxlow, herr] with r hx he
    have hab := (le_abs_self ((A.groups r : ℝ) * A.variance r - d r)).trans_lt he
    linarith
  have hf (z : Arm) : ∀ r S,
      |armTable (A.popSize r) M (A.schedule r) z S| ≤ B := fun r S =>
    armTable_abs_le_of_boundedSchedule A B hClass.bounded r z S
  have hV (z : Arm) (r : ℕ) : A.armVariance r z ≤ B ^ 2 :=
    sliceVar_le_sq_of_abs_le (A.groupSize_le r) _ B (hf z r)
  have hpEv : ∀ᶠ r in atTop, p / 2 < A.treatmentFraction r :=
    (tendsto_order.1 hClass.fraction.2.2).1 (p / 2) (by linarith [hClass.fraction.1])
  have hqEv : ∀ᶠ r in atTop, (1 - p) / 2 < 1 - A.treatmentFraction r := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have hq := hone.sub hClass.fraction.2.2
    exact (tendsto_order.1 hq).1 ((1 - p) / 2) (by linarith [hClass.fraction.2.1])
  let Rmax := B ^ 2 / (p / 2) + B ^ 2 / ((1 - p) / 2)
  have hRbound : ∀ᶠ r in atTop, |A.leadingVariance r| ≤ Rmax := by
    filter_upwards [hpEv, hqEv] with r hp hq
    have hp0 : 0 < A.treatmentFraction r := lt_trans (by linarith [hClass.fraction.1]) hp
    have hq0 : 0 < 1 - A.treatmentFraction r :=
      lt_trans (by linarith [hClass.fraction.2.1]) hq
    have hR0 : 0 ≤ A.leadingVariance r := by
      unfold ScheduleArray.leadingVariance indepGroupVar
      exact add_nonneg (div_nonneg ((slice _ _ _).Var_nonneg _) hp0.le)
        (div_nonneg ((slice _ _ _).Var_nonneg _) hq0.le)
    rw [abs_of_nonneg hR0]
    unfold ScheduleArray.leadingVariance indepGroupVar Rmax
    apply add_le_add
    · exact div_le_div₀ (sq_nonneg B) (hV true r)
        (by linarith [hClass.fraction.1]) hp.le
    · exact div_le_div₀ (sq_nonneg B) (hV false r)
        (by linarith [hClass.fraction.2.1]) hq.le
  have hdInvEv : ∀ᶠ r in atTop, |(d r)⁻¹| ≤ 4 / cSigma := by
    filter_upwards [hdlow] with r hd
    have hd0 : 0 < d r := by linarith [hClass.nondegenerate.1]
    rw [abs_inv, abs_of_pos hd0]
    rw [inv_eq_one_div, le_div_iff₀ hClass.nondegenerate.1]
    rw [div_mul_eq_mul_div, div_le_iff₀ hd0]
    nlinarith [hClass.nondegenerate.1]
  obtain ⟨Kd, hKd⟩ := exists_global_abs_bound_of_eventually (fun r => (d r)⁻¹)
    (4 / cSigma) hdInvEv
  have hKd0 : 0 ≤ Kd := le_trans (abs_nonneg ((d 0)⁻¹)) (hKd 0)
  have hdinvB := boundedInProb_of_pointwise_bound A.design (fun r _ => (d r)⁻¹) Kd
    (fun r _ => hKd r)
  have hnumErr := hu.mul_boundedInProb hdinvB
  have hnum : FiniteDesign.TendstoInProb A.design
      (fun r w => ((A.groups r : ℝ) * A.cr2 r w) / d r)
      (fun r => A.leadingVariance r / d r) := by
    intro ε hε
    have ht := hnumErr ε hε
    apply Tendsto.congr' _ ht
    filter_upwards [] with r
    apply (A.design r).Pr_congr
    intro w
    have heq : ((A.groups r : ℝ) * A.cr2 r w) / d r -
        A.leadingVariance r / d r =
      ((A.groups r : ℝ) * A.cr2 r w - A.leadingVariance r) * (d r)⁻¹ := by
      simp only [div_eq_mul_inv]
      ring
    rw [heq]
    simp
  have hyOrd : Tendsto (fun r => ((A.groups r : ℝ) * A.variance r) / d r)
      atTop (nhds 1) := by
    have hzero : Tendsto (fun r =>
        ((A.groups r : ℝ) * A.variance r - d r) / d r) atTop (nhds 0) := by
      have hvabs : Tendsto (fun r =>
          |(A.groups r : ℝ) * A.variance r - d r|) atTop (nhds 0) :=
        (tendsto_zero_iff_abs_tendsto_zero (fun r =>
          (A.groups r : ℝ) * A.variance r - d r)).1 hv
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero (g := fun r =>
        |(A.groups r : ℝ) * A.variance r - d r| * Kd)
        (fun r => abs_nonneg _) (fun r => ?_) ?_
      · change |((A.groups r : ℝ) * A.variance r - d r) / d r| ≤ _
        rw [abs_div, div_eq_mul_inv]
        have h := hKd r
        rw [abs_inv] at h
        exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
      · simpa using hvabs.mul_const Kd
    have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hzero
    have heq : ∀ᶠ r in atTop, 1 +
        ((A.groups r : ℝ) * A.variance r - d r) / d r =
        ((A.groups r : ℝ) * A.variance r) / d r := by
      filter_upwards [hdlow] with r hd
      have hdne : d r ≠ 0 := ne_of_gt (by linarith [hClass.nondegenerate.1])
      field_simp
      ring
    simpa using this.congr' heq
  have hy := FiniteDesign.deterministic_tendstoInProb A.design _ 1 hyOrd
  have haEv : ∀ᶠ r in atTop, |A.leadingVariance r / d r| ≤ Rmax * (4 / cSigma) := by
    filter_upwards [hRbound, hdInvEv] with r hR hd
    rw [div_eq_mul_inv, abs_mul]
    have hRmax0 : 0 ≤ Rmax := by
      dsimp [Rmax]
      exact add_nonneg (div_nonneg (sq_nonneg B) (by linarith [hClass.fraction.1]))
        (div_nonneg (sq_nonneg B) (by linarith [hClass.fraction.2.1]))
    exact mul_le_mul hR hd (abs_nonneg _) hRmax0
  obtain ⟨Ka, hKa⟩ := exists_global_abs_bound_of_eventually
    (fun r => A.leadingVariance r / d r) (Rmax * (4 / cSigma)) haEv
  have hratio := FiniteDesign.tendstoInProb_div_one A.design
    (fun r w => ((A.groups r : ℝ) * A.cr2 r w) / d r)
    (fun r w => ((A.groups r : ℝ) * A.variance r) / d r)
    (fun r => A.leadingVariance r / d r) Ka hKa hnum hy
  intro ε hε
  have ht := hratio ε hε
  apply Tendsto.congr' _ ht
  filter_upwards [hdlow, hxlow] with r hd hx
  apply (A.design r).Pr_congr
  intro w
  have hdne : d r ≠ 0 := ne_of_gt (by linarith [hClass.nondegenerate.1])
  have hGne : (A.groups r : ℝ) ≠ 0 := by exact_mod_cast (A.groups_pos r).ne'
  have hvne : A.variance r ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hx
    linarith [hClass.nondegenerate.1]
  have heq : ((A.groups r : ℝ) * A.cr2 r w / d r) /
      ((A.groups r : ℝ) * A.variance r / d r) = A.cr2 r w / A.variance r := by
    field_simp
  rw [heq]

-- @node: FiniteDesign.TendstoInProb.retarget
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,X,a,c,hX,ha), [the retarget result holds](goal). -/
lemma FiniteDesign.TendstoInProb.retarget
    {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)] {D : ∀ r, FiniteDesign (Ω r)}
    {X : ∀ r, Ω r → ℝ} {a : ℕ → ℝ} {c : ℝ}
    (hX : FiniteDesign.TendstoInProb D X a) (ha : Tendsto a atTop (nhds c)) :
    FiniteDesign.TendstoInProb D X (fun _ => c) := by
  have hdet := FiniteDesign.deterministic_tendstoInProb D a c ha
  have hsum := hX.add hdet
  intro ε hε
  have ht := hsum ε hε
  apply Tendsto.congr' _ ht
  filter_upwards [] with r
  apply (D r).Pr_congr
  intro w
  constructor <;> intro hh
  · convert hh using 1; ring
  · convert hh using 1; ring

-- @node: tendsto_of_deterministic_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,a,c,h), [the indicated sequence converges to its stated limit](goal). -/
lemma tendsto_of_deterministic_tendstoInProb
    {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)] {D : ∀ r, FiniteDesign (Ω r)}
    {a : ℕ → ℝ} {c : ℝ}
    (h : FiniteDesign.TendstoInProb D (fun r _ => a r) (fun _ => c)) :
    Tendsto a atTop (nhds c) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have ht := h ε hε
  have hev : ∀ᶠ r in atTop,
      (D r).Pr (fun _ => ε ≤ |a r - c|) < 1 / 2 :=
    (tendsto_order.1 ht).2 (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun r hrN => ?_⟩
  have hr := hN r hrN
  rw [Real.dist_eq]
  by_contra hnot
  have hge : ε ≤ |a r - c| := le_of_not_gt hnot
  have hone : (D r).Pr (fun _ => ε ≤ |a r - c|) = 1 := by
    unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
    simp [hge, (D r).p_sum]
  rw [hone] at hr
  norm_num at hr

-- @node: tendstoInProb_target_unique
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,X,a,c,ha,hc), [the indicated sequence converges to its stated limit](goal). -/
lemma tendstoInProb_target_unique
    {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)] {D : ∀ r, FiniteDesign (Ω r)}
    {X : ∀ r, Ω r → ℝ} {a : ℕ → ℝ} {c : ℝ}
    (ha : FiniteDesign.TendstoInProb D X a)
    (hc : FiniteDesign.TendstoInProb D X (fun _ => c)) :
    Tendsto a atTop (nhds c) := by
  have hrefl : FiniteDesign.TendstoInProb D (fun r _ => a r) a := by
    intro ε hε
    simp [FiniteDesign.Pr, FiniteDesign.E, FiniteDesign.ind, not_le.mpr hε]
  have hsum := (hrefl.sub ha).add hc
  apply tendsto_of_deterministic_tendstoInProb (D := D)
  intro ε hε
  have ht := hsum ε hε
  apply Tendsto.congr' _ ht
  filter_upwards [] with r
  apply (D r).Pr_congr
  intro w
  constructor <;> intro hh
  · convert hh using 1; ring
  · convert hh using 1; ring

-- @node: lower_tail_vanishes_of_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,X,a,hX,ha), [the indicated sequence converges to its stated limit](goal). -/
lemma lower_tail_vanishes_of_tendstoInProb
    {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)] {D : ∀ r, FiniteDesign (Ω r)}
    {X : ∀ r, Ω r → ℝ} {a : ℕ → ℝ}
    (hX : FiniteDesign.TendstoInProb D X a) (ha : ∀ᶠ r in atTop, 1 ≤ a r) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun r => (D r).Pr (fun w => X r w < 1 - ε)) atTop (nhds 0) := by
  intro ε hε
  have ht := hX ε hε
  apply squeeze_zero' (Eventually.of_forall fun r => (D r).Pr_nonneg _) _ ht
  filter_upwards [ha] with r har
  apply (D r).Pr_mono
  intro w hw
  have hdiff : ε < a r - X r w := by linarith
  exact le_trans hdiff.le (by simpa using neg_le_abs (X r w - a r))

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
