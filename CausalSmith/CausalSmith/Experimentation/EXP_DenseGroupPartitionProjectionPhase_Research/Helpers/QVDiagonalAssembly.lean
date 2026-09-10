import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.DiagonalSupport

/-!
# Diagonal lower-bound assembly helpers

Finite-design conditioning and deterministic-array membership facts used by the
one-realization impossibility argument.
-/

open scoped Topology
open Filter

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

-- @node: ScheduleArray.withSchedule
/-- Replace only the deterministic schedule in a fixed design skeleton. -/
def ScheduleArray.withSchedule {M : ℕ} (A : ScheduleArray M)
    (Y : ∀ r, PotentialOutcome (A.popSize r) M) : ScheduleArray M where
  groupSize_ge_two := A.groupSize_ge_two
  popSize := A.popSize
  groups := A.groups
  treated := A.treated
  groups_pos := A.groups_pos
  grouped_le := A.grouped_le
  treated_pos := A.treated_pos
  treated_lt := A.treated_lt
  treated_le := A.treated_le
  schedule := Y

-- @node: abs_conditionedExpectation_sub_le_two_compl
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,f,hf,hq), [the stated expectation identity holds](goal). -/
lemma abs_conditionedExpectation_sub_le_two_compl
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (D : FiniteDesign Ω) (Γ : Finset Ω) (f : Ω → ℝ)
    (hf : ∀ w, 0 ≤ f w ∧ f w ≤ 1)
    (hq : 0 < D.Pr (fun w => w ∈ Γ)) :
    |D.E (fun w => if w ∈ Γ then f w else 0) /
        D.Pr (fun w => w ∈ Γ) - D.E f| ≤
      2 * (1 - D.Pr (fun w => w ∈ Γ)) := by
  let q := D.Pr (fun w => w ∈ Γ)
  let a := D.E (fun w => if w ∈ Γ then f w else 0)
  let b := D.E (fun w => if w ∈ Γ then 0 else f w)
  have hqpos : 0 < q := by simpa [q] using hq
  have ha0 : 0 ≤ a := by
    dsimp [a]
    apply D.E_nonneg
    intro w
    by_cases hw : w ∈ Γ <;> simp [hw, (hf w).1]
  have hb0 : 0 ≤ b := by
    dsimp [b]
    apply D.E_nonneg
    intro w
    by_cases hw : w ∈ Γ <;> simp [hw, (hf w).1]
  have haq : a ≤ q := by
    unfold a q FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : w ∈ Γ
    · simpa [hw] using mul_le_mul_of_nonneg_left (hf w).2 (D.p_nonneg w)
    · simp [hw]
  have hbq : b ≤ 1 - q := by
    have hcomp : D.Pr (fun w => w ∉ Γ) = 1 - q := by
      unfold q FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
      rw [← D.p_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : w ∈ Γ <;> simp [hw, D.p_sum]
    rw [← hcomp]
    unfold b FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : w ∈ Γ
    · simp [hw]
    · simpa [hw] using mul_le_mul_of_nonneg_left (hf w).2 (D.p_nonneg w)
  have hef : D.E f = a + b := by
    unfold a b FiniteDesign.E
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w ∈ Γ <;> simp [hw]
  have hq1 : q ≤ 1 := D.Pr_le_one _
  have hx0 : 0 ≤ a * (1 - q) / q :=
    div_nonneg (mul_nonneg ha0 (sub_nonneg.mpr hq1)) hqpos.le
  have hxq : a * (1 - q) / q ≤ 1 - q := by
    rw [div_le_iff₀ hqpos]
    nlinarith
  rw [hef]
  have hid : a / q - (a + b) = a * (1 - q) / q - b := by
    field_simp [hqpos.ne']
    ring
  rw [hid, abs_le]
  constructor <;> nlinarith

-- @node: denseClass_withSchedule_of_scaled_tendsto
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,p,rho,B,c,d,hg,hp,hr,hB,hc,hcd,Y,hb,ht), [the indicated sequence converges to its stated limit](goal). -/
lemma denseClass_withSchedule_of_scaled_tendsto {M : ℕ} (A : ScheduleArray M)
    (p rho B c d : ℝ) (hg : GroupCountGrowth A)
    (hp : StableTreatmentFraction A p) (hr : SamplingFractionLimit A rho)
    (hB : 0 < B) (hc : 0 < c) (hcd : c < d)
    (Y : ∀ r, PotentialOutcome (A.popSize r) M)
    (hb : ∀ r S i z, |Y r S i z| ≤ B)
    (ht : Tendsto (fun r => (A.groups r : ℝ) * sigmaSq (Y r)
      (A.grouped_le r) (A.treated_pos r) (A.treated_lt r)) atTop (nhds d)) :
    DenseScheduleClass (A.withSchedule Y) p rho B c := by
  refine ⟨hg, hp, hr, ⟨hB, hb⟩, hc, ?_⟩
  have ht' : Tendsto (fun r => (((A.groups r : ℝ) * sigmaSq (Y r)
      (A.grouped_le r) (A.treated_pos r) (A.treated_lt r) : ℝ) : EReal))
      atTop (nhds (d : EReal)) := EReal.tendsto_coe.2 ht
  change (c : EReal) ≤ Filter.liminf (fun r => (((A.groups r : ℝ) *
    sigmaSq (Y r) (A.grouped_le r) (A.treated_pos r) (A.treated_lt r) : ℝ) : EReal)) atTop
  rw [ht'.liminf_eq]
  exact_mod_cast hcd.le

-- @node: tendsto_of_uniform_support_error
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:X,c,Γ,e,he,_he0,hbound,u,hu), [the indicated sequence converges to its stated limit](goal). -/
lemma tendsto_of_uniform_support_error {Ω : ℕ → Type*}
    (X : ∀ r, Ω r → ℝ) (c : ℝ) (Γ : ∀ r, Finset (Ω r)) (e : ℕ → ℝ)
    (he : Tendsto e atTop (nhds 0)) (_he0 : ∀ r, 0 < e r)
    (hbound : ∀ r w, w ∈ Γ r → |X r w - c| < e r)
    (u : ∀ r, Ω r) (hu : ∀ r, u r ∈ Γ r) :
    Tendsto (fun r => X r (u r)) atTop (nhds c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev : ∀ᶠ r in atTop, e r < ε := (tendsto_order.1 he).2 ε hε
  apply eventually_atTop.1
  filter_upwards [hev] with r hr
  simpa [Real.dist_eq] using (hbound r (u r) (hu r)).trans hr

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
