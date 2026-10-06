module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveRegularization
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialVanTreesIntegrals

/-! # Order and limit calculus for the sequential local minimax lower bound -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

/-- Every admissible local alternative's risk is bounded by the corresponding
local worst risk. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,H,n,h,hh), these specify the stated inputs. -/
lemma localRisk_le_localWorstRisk {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p H : ℝ) (n : ℕ)
    (h : TrialParameter) (hh : h ∈ localIndexSet θ n H) :
    localRisk P θ h p n ≤ localWorstRisk P θ p H n := by
  unfold localWorstRisk
  apply le_sSup
  exact ⟨h, hh, rfl⟩

/-- Every fixed direction whose Euclidean norm is at most the radius is
eventually admissible at an interior base parameter. For [the displayed inputs and conditions](hyp:theta,h,H), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:htheta,hh), these specify the stated inputs. -/
lemma eventually_mem_localIndexSet (theta h : TrialParameter) (H : ℝ)
    (htheta : InteriorMeans theta)
    (hh : Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) ≤ H) :
    ∀ᶠ n in atTop, h ∈ localIndexSet theta n H := by
  filter_upwards [eventually_localAlternative_interior theta h htheta] with n hn
  exact ⟨hh, hn⟩

/-- Consequently, the risk at any fixed bounded direction is eventually below
the local worst-risk sequence. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,theta,p,H,h,htheta,hh), these specify the stated inputs. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma eventually_localRisk_le_localWorstRisk {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (theta : TrialParameter) (p H : ℝ)
    (h : TrialParameter) (htheta : InteriorMeans theta)
    (hh : Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) ≤ H) :
    ∀ᶠ n in atTop,
      localRisk P theta h p n ≤ localWorstRisk P theta p H n := by
  filter_upwards [eventually_mem_localIndexSet theta h H htheta hh] with n hn
  exact localRisk_le_localWorstRisk P theta p H n h hn

/-- A lower bound on the liminf at one positive radius is already a lower bound
on the outer-radius local asymptotic risk. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,H,hH,v,hlim), these specify the stated inputs. -/
lemma le_localAsymptoticRisk_of_le_liminf {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p H : ℝ)
    (hH : 0 < H) (v : ℝ≥0∞)
    (hlim : v ≤ liminf (fun n => localWorstRisk P θ p H n) atTop) :
    v ≤ localAsymptoticRisk P θ p := by
  unfold localAsymptoticRisk
  exact hlim.trans (le_sSup ⟨H, hH, rfl⟩)

/-- An eventually valid finite-sample lower envelope transfers through the
liminf and the outer radius supremum. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,H,hH,b,v,hb,hlower), these specify the stated inputs. -/
lemma le_localAsymptoticRisk_of_eventually_ge_of_tendsto {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p H : ℝ)
    (hH : 0 < H) (b : ℕ → ℝ≥0∞) (v : ℝ≥0∞)
    (hb : Tendsto b atTop (nhds v))
    (hlower : ∀ᶠ n in atTop, b n ≤ localWorstRisk P θ p H n) :
    v ≤ localAsymptoticRisk P θ p := by
  apply le_localAsymptoticRisk_of_le_liminf P θ p H hH v
  rw [← hb.liminf_eq]
  exact liminf_le_liminf hlower (by isBoundedDefault) (by isBoundedDefault)

/-- A real finite-sample Bayes envelope converging to `v` gives the exact
`ENNReal.ofReal v` local asymptotic lower bound. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,H,hH,b,v,hb,hlower), these specify the stated inputs. -/
lemma ofReal_le_localAsymptoticRisk_of_bayes_envelope {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p H : ℝ)
    (hH : 0 < H) (b : ℕ → ℝ) (v : ℝ)
    (hb : Tendsto b atTop (nhds v))
    (hlower : ∀ᶠ n in atTop,
      ENNReal.ofReal (b n) ≤ localWorstRisk P θ p H n) :
    ENNReal.ofReal v ≤ localAsymptoticRisk P θ p := by
  apply le_localAsymptoticRisk_of_eventually_ge_of_tendsto
    P θ p H hH (fun n => ENNReal.ofReal (b n)) (ENNReal.ofReal v)
  · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb
  · exact hlower

/-- The result identifies the relation called tendsto nat div const add nat mul: given the declared inputs and assumptions, the stated mathematical conclusion holds. Under [the stated assumptions](hyp:hI,hinfo), [the tendsto nat div const add nat mul](goal).

Under the stated assumptions, the tendsto nat div const add nat mul. -/
    lemma tendsto_nat_div_const_add_nat_mul (c : ℝ) (info : ℕ → ℝ) (I : ℝ) (hI : 0 < I)
    (hinfo : Tendsto info atTop (nhds I)) :
    Tendsto (fun n : ℕ => (n : ℝ) / (c + (n : ℝ) * info n))
      atTop (nhds (1 / I)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hc : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hinv
  have hquot : Tendsto (fun n : ℕ => 1 / (c / (n : ℝ) + info n))
      atTop (nhds (1 / I)) := by
    change Tendsto ((fun _ : ℕ ↦ (1 : ℝ)) /
      (fun n : ℕ ↦ c / (n : ℝ) + info n)) atTop (nhds (1 / I))
    simpa only [zero_add] using
      tendsto_const_nhds.div (hc.add hinfo) (by simpa using ne_of_gt hI)
  apply hquot.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn1 => hn1⟩] with n hn1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn1)
  field_simp

/-- The preceding real van Trees envelope also converges after embedding into
nonnegative extended reals. For [the displayed inputs and conditions](hyp:c,info,I,hI), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:hinfo), these specify the stated inputs. -/
lemma tendsto_ofReal_nat_div_const_add_nat_mul
    (c : ℝ) (info : ℕ → ℝ) (I : ℝ) (hI : 0 < I)
    (hinfo : Tendsto info atTop (nhds I)) :
    Tendsto (fun n : ℕ => ENNReal.ofReal
      ((n : ℝ) / (c + (n : ℝ) * info n)))
      atTop (nhds (ENNReal.ofReal (1 / I))) := by
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_nat_div_const_add_nat_mul c info I hI hinfo)

/-- A finite-n van Trees lower bound with a convergent per-sample information
envelope yields the exact local asymptotic reciprocal-information bound. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,H,c,I,hH,hI,info,hinfo,hbayes), these specify the stated inputs. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma inv_le_localAsymptoticRisk_of_finite_vanTrees {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p H c I : ℝ)
    (hH : 0 < H) (hI : 0 < I) (info : ℕ → ℝ)
    (hinfo : Tendsto info atTop (nhds I))
    (hbayes : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal ((n : ℝ) / (c + (n : ℝ) * info n)) ≤
        localWorstRisk P θ p H n) :
    ENNReal.ofReal (1 / I) ≤ localAsymptoticRisk P θ p := by
  exact le_localAsymptoticRisk_of_eventually_ge_of_tendsto
    P θ p H hH _ _
    (tendsto_ofReal_nat_div_const_add_nat_mul c info I hI hinfo) hbayes

end CausalSmith.Stat.LdpAteEfficiencySurface
