module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Scales

/-! Finite-moment homogeneity testing: Helpers/PhaseAlgebra. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- The public domain makes every phase denominator positive, and bounds the tail ratio by one half. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: phase_denominators
lemma phase_denominators (v : Params) (hv : v.Valid) :
    0 < v.p ∧ 0 < v.p-1 ∧ 0 < v.γ ∧ 0 < sumReg v ∧
    0 < qExp v ∧ qExp v ≤ 1/2 ∧ 0 < 2*v.γ+qExp v ∧ 0 < Dp v := by
  have hp : 0 < v.p := by linarith [hv.1.1]
  have hm : 0 < v.p-1 := by linarith [hv.1.1]
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have hs : 0 < sumReg v := add_pos hv.2.1.1 hv.2.2.1.1
  have hq : 0 < qExp v := div_pos hm hp
  have hqh : qExp v ≤ 1/2 := by
    unfold qExp
    apply (div_le_iff₀ hp).2
    linarith [hv.1.2]
  have hd : 0 < Dp v := by
    have hα := hv.2.1.1
    have hβ := hv.2.2.1.1
    unfold Dp
    positivity
  exact ⟨hp, hm, hg, hs, hq, hqh, by positivity, hd⟩

/-- Subtracting the two channels gives a positive factor times the phase functional minus one. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: phase_channel_difference
lemma phase_channel_difference (v : Params) (hv : v.Valid) :
    E4 v-E0 v = (2*v.γ*qExp v/((2*v.γ+qExp v)*Dp v))*(Fphase v-1) := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  have heq : v.p*qExp v = v.p-1 := by
    unfold qExp
    field_simp
  unfold E4 E0 Fphase
  field_simp [ne_of_gt hd, ne_of_gt he]
  unfold Dp sumReg
  field_simp [ne_of_gt hq, ne_of_gt hg, ne_of_gt hm]
  linear_combination -4*v.γ*v.α*heq

/-- The sign of the channel difference determines which exponent is the minimum, including equality. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: phase_channel_selection
lemma phase_channel_selection (v : Params) (hv : v.Valid) :
    (1 ≤ Fphase v → Eexp v=E0 v) ∧ (Fphase v < 1 → Eexp v=E4 v) := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hf : 0 < 2*v.γ*qExp v/((2*v.γ+qExp v)*Dp v) := by positivity
  have hid := phase_channel_difference v hv
  constructor
  · intro h
    have hz := mul_nonneg hf.le (sub_nonneg.mpr h)
    exact min_eq_left (by linarith)
  · intro h
    have hz := mul_neg_of_pos_of_neg hf (sub_neg.mpr h)
    exact min_eq_right (by linarith)

/-- Raising the moment exponent to two decreases the rough denominator and the phase functional. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: phase_bounded_identities
lemma phase_bounded_identities (v : Params) (hv : v.Valid) :
    Dp v = Dp (v.withP 2)+v.β*(2-v.p)/(v.p-1) ∧
    Fphase v = Fphase (v.withP 2)+(2*v.α+v.β)*(2-v.p)/(v.p-1) := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  constructor <;> simp only [Dp, Fphase, qExp, sumReg, Params.withP] <;>
    field_simp <;> ring

/-- At second moment the pure-tail channel has the displayed closed denominator. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: phase_bounded_tail_difference
lemma phase_bounded_tail_difference (v : Params) (hv : v.Valid) :
    E0 (v.withP 2)-E0 v =
      4*v.γ^2*(2-v.p)/((4*v.γ+1)*(2*v.γ*v.p+v.p-1)) := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hd' : 0 < 2*v.γ*v.p+v.p-1 := by
    have hprod := mul_pos hg hp
    linarith
  have hg4 : 0 < 4*v.γ+1 := by positivity
  have hgn : 0 < 1/2+v.γ*2 := by positivity
  have hdn : 0 < -1+v.γ*v.p*2+v.p := by nlinarith
  have hb : E0 (v.withP 2) = 2*v.γ/(4*v.γ+1) := by
    norm_num [E0, qExp, Params.withP]
    field_simp [ne_of_gt hgn, ne_of_gt hg4]
    ring
  have ht : E0 v = 2*v.γ*(v.p-1)/(2*v.γ*v.p+v.p-1) := by
    unfold E0
    field_simp [ne_of_gt he, ne_of_gt hd']
    ring_nf
    field_simp [ne_of_gt hdn]
    have heq : v.p*qExp v = v.p-1 := by
      unfold qExp
      field_simp
    linear_combination 2*v.γ*heq
  rw [hb, ht]
  field_simp [ne_of_gt hg4, ne_of_gt hd']
  ring_nf
  field_simp [ne_of_gt hdn]
  field_simp [show -1+2*v.γ*v.p+v.p ≠ 0 by nlinarith]
  ring

/-- Subtracting the rough channels retains exactly the baseline smoothness and tail inflation. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: phase_bounded_rough_difference
lemma phase_bounded_rough_difference (v : Params) (hv : v.Valid) :
    E4 (v.withP 2)-E4 v =
      2*sumReg v*v.β*(2-v.p)/((v.p-1)*Dp v*Dp (v.withP 2)) := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hv2 : (v.withP 2).Valid := ⟨by norm_num [Params.withP], hv.2⟩
  have hd2 := (phase_denominators (v.withP 2) hv2).2.2.2.2.2.2.2
  have hid := (phase_bounded_identities v hv).1
  have hcross : (Dp v-Dp (v.withP 2))*(v.p-1) = v.β*(2-v.p) := by
    rw [hid]
    field_simp
    ring
  change 2*sumReg v/Dp (v.withP 2)-2*sumReg v/Dp v = _
  field_simp [ne_of_gt hd, ne_of_gt hd2, ne_of_gt hm]
  nlinarith [hcross]

/-- Exponent phase algebra: the displayed mathematical construction or bound. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: exponent_phase_algebra
lemma exponent_phase_algebra (v : Params) (hv : v.Valid) :
    0 < qExp v ∧ 0 < Dp v ∧ 0 < Eexp v ∧
    E4 v-E0 v = (2*v.γ*qExp v/((2*v.γ+qExp v)*Dp v))*(Fphase v-1) ∧
    (1 ≤ Fphase v → Eexp v=E0 v) ∧ (Fphase v < 1 → Eexp v=E4 v) ∧
    Eexp v/v.γ ≤ 1 ∧ Eexp v/sumReg v < 2 ∧ Eexp v/(v.p-1) < 1 ∧
    (v.p < 2 → Eexp v < Eexp (Params.ofBounded v.toSmooth3)) := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  have h0 : 0 < E0 v := div_pos (by positivity) he
  have h4 : 0 < E4 v := div_pos (by positivity) hd
  have hsel := phase_channel_selection v hv
  have hle0 : Eexp v ≤ E0 v := min_le_left _ _
  have hle4 : Eexp v ≤ E4 v := min_le_right _ _
  refine ⟨hq, hd, lt_min h0 h4, phase_channel_difference v hv, hsel.1, hsel.2, ?_, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hg).2
    have hb : E0 v ≤ v.γ := by
      unfold E0
      apply (div_le_iff₀ he).2
      nlinarith [hv.2.2.2.1]
    simpa only [one_mul] using hle0.trans hb
  · apply (div_lt_iff₀ hs).2
    have hd1 : 1 < Dp v := by
      unfold Dp
      have hα := hv.2.1.1
      have hβ := div_pos hv.2.2.1.1 hq
      have hS := div_pos hs (by positivity : 0 < 2*v.γ)
      linarith
    have hb : E4 v < 2*sumReg v := by
      unfold E4
      apply (div_lt_iff₀ hd).2
      nlinarith
    exact hle4.trans_lt hb
  · apply (div_lt_iff₀ hm).2
    have hb : E0 v < v.p-1 := by
      unfold E0
      apply (div_lt_iff₀ he).2
      have heq : v.p*qExp v = v.p-1 := by
        unfold qExp
        field_simp
      have hprod := mul_pos hm (by positivity : 0 < 2*v.γ+qExp v)
      nlinarith [mul_pos hm hq, mul_pos hg hm]
    simpa only [one_mul] using hle0.trans_lt hb
  · intro hlt
    have hv2 : (v.withP 2).Valid := ⟨by norm_num [Params.withP], hv.2⟩
    have htail : E0 v < E0 (v.withP 2) := by
      have hid := phase_bounded_tail_difference v hv
      have hpos : 0 < 4*v.γ^2*(2-v.p)/((4*v.γ+1)*(2*v.γ*v.p+v.p-1)) := by
        have : 0 < 2-v.p := by linarith
        have hd' : 0 < 2*v.γ*v.p+v.p-1 := by nlinarith
        positivity
      linarith
    have hrough : E4 v < E4 (v.withP 2) := by
      have hid := phase_bounded_rough_difference v hv
      have hd2 := (phase_denominators (v.withP 2) hv2).2.2.2.2.2.2.2
      have hpos : 0 < 2*sumReg v*v.β*(2-v.p)/((v.p-1)*Dp v*Dp (v.withP 2)) := by
        have : 0 < 2-v.p := by linarith
        have hβ := hv.2.2.1.1
        positivity
      linarith
    change Eexp v < min (E0 (v.withP 2)) (E4 (v.withP 2))
    exact lt_min (hle0.trans_lt htail) (hle4.trans_lt hrough)
/-- The explicit three-row difference of the bounded and finite-moment exponents. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def phaseDifference (v : Params) : ℝ :=
  if 1 ≤ Fphase (v.withP 2) then
    4*v.γ^2*(2-v.p)/((4*v.γ+1)*(2*v.γ*v.p+v.p-1))
  else if 1 ≤ Fphase v then
    E4 (v.withP 2)-E0 v
  else 2*sumReg v*v.β*(2-v.p)/((v.p-1)*Dp v*Dp (v.withP 2))
/-- Phase difference eq: the displayed mathematical construction or bound. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: phase_difference_eq
lemma phase_difference_eq (v : Params) (hv : v.Valid) : Eexp (v.withP 2)-Eexp v=phaseDifference v := by
  have hv2 : (v.withP 2).Valid := ⟨by norm_num [Params.withP], hv.2⟩
  have hsel := phase_channel_selection v hv
  have hsel2 := phase_channel_selection (v.withP 2) hv2
  have hmono : Fphase (v.withP 2) ≤ Fphase v := by
    rw [(phase_bounded_identities v hv).2]
    have hm : 0 < v.p-1 := by linarith [hv.1.1]
    have hnum : 0 ≤ (2*v.α+v.β)*(2-v.p) :=
      mul_nonneg (by linarith [hv.2.1.1, hv.2.2.1.1]) (by linarith [hv.1.2])
    have := div_nonneg hnum hm.le
    linarith
  unfold phaseDifference
  split
  · rename_i h
    rw [hsel2.1 h, hsel.1 (h.trans hmono)]
    exact phase_bounded_tail_difference v hv
  · rename_i h
    have h2 : Fphase (v.withP 2) < 1 := lt_of_not_ge h
    rw [hsel2.2 h2]
    split
    · rename_i h1
      rw [hsel.1 h1]
    · rename_i h1
      rw [hsel.2 (lt_of_not_ge h1)]
      exact phase_bounded_rough_difference v hv

end CausalSmith.Stat.FinitepHomogeneityDensegamma
