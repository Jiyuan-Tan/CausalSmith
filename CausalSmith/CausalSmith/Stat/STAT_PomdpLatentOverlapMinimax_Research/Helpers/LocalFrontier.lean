module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.ObservedKL

set_option linter.style.longLine false

/-! # Shrinking-overlap derivation handle -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- A selector decision is either immediate weighting or a strictly positive,
valid partial-history depth. -/
inductive LocalFrontierChoice (T : Nat) where
  | immediate
  | weighted (k : Nat) (positive : 0 < k) (valid : k < T)

/-- The history depth encoded by a local-frontier selector decision. -/
def LocalFrontierChoice.historyDepth {T : Nat} : LocalFrontierChoice T → Nat
  | .immediate => 0
  | .weighted k _ _ => k

/-- Interface for a data-dependent selector.  The rule receives the complete
partial-history score family at the observed path, the testing modulus, and the
exact risk target; `LocalFrontierChoice` enforces that its selected depth is
valid for the current horizon. -/
abbrev LocalFrontierSelector :=
  (T nX : Nat) → Policy nX → Policy nX → ObsView T nX →
    ((k : Nat) → Fin T → ℝ) → ℝ → ℝ → LocalFrontierChoice T

/-- Non-assertive data carried by the local-overlap derivation handle.  The
scaled family satisfies the required stationary-ratio bound, its testing
modulus is the observed-path KL divergence, and the selector returns a valid
history depth whose selected score is a member of the PHIW score family. -/
structure LocalFrontierHandle (t0 zeta : ℝ) (delta : Nat → ℝ) (Q : Nat) where
  t0_positive : 0 < t0
  zeta_positive : 0 < zeta
  depth_positive : 1 ≤ Q
  overlapExcess : Nat → ℝ
  excess_nonnegative : ∀ T, 0 ≤ overlapExcess T
  localRadius : Nat → ℝ
  depth : Nat
  scaledFamily : (T : Nat) → Bool → RawPomdpExperiment T 1 (2 * (Q + 1))
  stationaryRatioConstraint : ∀ (T : Nat) (v : Bool) (s : JointState 1 (2 * (Q + 1))),
    stationaryLaw (policyKernel (scaledFamily T v) (scaledFamily T v).e) s ≤
      localRadius T * (scaledFamily T v).init s
  testingModulus : Nat → ℝ
  testingModulus_spec : ∀ T,
    testingModulus T = (InformationTheory.klDiv
      (obsLaw (scaledFamily T true)) (obsLaw (scaledFamily T false))).toReal
  scoreFamily : (T nX k : Nat) → Policy nX → Policy nX →
    ObsView T nX → Fin T → ℝ
  riskTarget : Nat → ℝ
  selectorRule : LocalFrontierSelector
  selector : (T nX : Nat) → Policy nX → Policy nX → ObsView T nX →
    LocalFrontierChoice T
  selector_rule_spec : ∀ (T nX : Nat) (b e : Policy nX)
      (w : ObsView T nX),
    selector T nX b e w =
      selectorRule T nX b e w
        (fun k t ↦ scoreFamily T nX k b e w t)
        (testingModulus T) (riskTarget T)
  selectedScore : (T nX : Nat) → Policy nX → Policy nX →
    ObsView T nX → Fin T → ℝ
  selectedScore_spec : ∀ (T nX : Nat) (b e : Policy nX)
      (w : ObsView T nX) (t : Fin T),
    selectedScore T nX b e w t =
      scoreFamily T nX (selector T nX b e w).historyDepth b e w t

/-- The stationary-ratio calculation for the locally scaled signed-depth device.
Unlike the prior handle signature, this is derived from the construction rather than supplied
by the caller.  The finite device has a well-defined zero-perturbation extension at `delta T = 0`. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the hdelta condition](hyp:hdelta); and [the h Q condition](hyp:hQ). [the stated conclusion](goal). -/
lemma localFrontier_stationaryRatio (t0 zeta : ℝ) (delta : Nat → ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hdelta : ∀ T, 0 ≤ delta T)
    (Q : Nat) (hQ : 1 ≤ Q) :
    ∀ (T : Nat) (v : Bool) (s : JointState 1 (2 * (Q + 1))),
      stationaryLaw (policyKernel
          (embed (signedDepthFinite T t0 zeta (1 + delta T) Q v))
          (embed (signedDepthFinite T t0 zeta (1 + delta T) Q v)).e) s ≤
        (1 + delta T) *
          (embed (signedDepthFinite T t0 zeta (1 + delta T) Q v)).init s := by
  intro T v s
  by_cases hpos : 0 < delta T
  · rcases s with ⟨x, h⟩
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    have hC : 1 < 1 + delta T := by linarith
    calc
      stationaryLaw (policyKernel
          (embed (signedDepthFinite T t0 zeta (1 + delta T) Q v))
          (embed (signedDepthFinite T t0 zeta (1 + delta T) Q v)).e) (0, h) ≤
          (1 + epsC (1 + delta T)) *
            (embed (signedDepthFinite T t0 zeta (1 + delta T) Q v)).init (0, h) :=
        signedDepth_stationary_overlap_base ht0 hzeta hC.le hQ h
      _ ≤ (1 + delta T) *
            (embed (signedDepthFinite T t0 zeta (1 + delta T) Q v)).init (0, h) := by
        apply mul_le_mul_of_nonneg_right
        · exact signedDepth_eps_bound hC.le
        · change 0 ≤ ((signedDepthFinite T t0 zeta (1 + delta T) Q v).init (0, h)).toReal
          exact ENNReal.toReal_nonneg
  · have hzero : delta T = 0 := le_antisymm (le_of_not_gt hpos) (hdelta T)
    rw [hzero]
    rcases s with ⟨x, h⟩
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simpa [epsC, signedDepthFamilyAtLeastOne] using
      (signedDepth_stationary_overlap_base (T := T) (Q := Q) (t0 := t0)
        (zeta := zeta) (C := (1 : ℝ)) (v := v) ht0 hzeta (by norm_num) hQ h)

-- @node: def:local-frontier-handle
/-- The scaled signed-depth perturbation, its proved stationary-ratio constraint,
observed-path testing modulus, data-dependent valid-depth PHIW selector, and
resulting exact minimax-risk target. -/
noncomputable def localFrontierHandle (t0 zeta : ℝ) (delta : Nat → ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hdelta : ∀ T, 0 ≤ delta T)
    (Q : Nat) (hQ : 1 ≤ Q) (selectorRule : LocalFrontierSelector) :
    LocalFrontierHandle t0 zeta delta Q where
  t0_positive := ht0 -- @realizes \(t_0\)(positive domain)
  zeta_positive := hzeta -- @realizes \(\zeta\)(positive domain)
  depth_positive := hQ -- @realizes \(Q\)(positive hidden depth)
  overlapExcess := delta -- @realizes \(\delta_T\)(nonnegative overlap-excess sequence)
  excess_nonnegative := hdelta -- @realizes \(\delta_T\)(values in [0,∞))
  localRadius T := 1 + delta T -- @realizes \(\delta_T\)(local radius 1+delta_T)
  depth := Q
  scaledFamily T v := embed (signedDepthFinite T t0 zeta (1 + delta T) Q v)
  stationaryRatioConstraint := localFrontier_stationaryRatio t0 zeta delta ht0 hzeta hdelta Q hQ
  testingModulus T := (InformationTheory.klDiv
    (obsLaw (embed (signedDepthFinite T t0 zeta (1 + delta T) Q true)))
    (obsLaw (embed (signedDepthFinite T t0 zeta (1 + delta T) Q false)))).toReal
  testingModulus_spec := by intro T; rfl
  scoreFamily T nX k b e w t := phiwScore k b e w t
  riskTarget T := minimaxRisk T t0 zeta (1 + delta T)
  selectorRule := selectorRule
  selector T nX b e w := selectorRule T nX b e w
    (fun k t ↦ phiwScore k b e w t)
    (InformationTheory.klDiv
      (obsLaw (embed (signedDepthFinite T t0 zeta (1 + delta T) Q true)))
      (obsLaw (embed (signedDepthFinite T t0 zeta (1 + delta T) Q false)))).toReal
    (minimaxRisk T t0 zeta (1 + delta T))
  selector_rule_spec := by intros; rfl
  selectedScore T nX b e w t :=
    phiwScore ((selectorRule T nX b e w
      (fun k t ↦ phiwScore k b e w t)
      (InformationTheory.klDiv
        (obsLaw (embed (signedDepthFinite T t0 zeta (1 + delta T) Q true)))
        (obsLaw (embed (signedDepthFinite T t0 zeta (1 + delta T) Q false)))).toReal
      (minimaxRisk T t0 zeta (1 + delta T))).historyDepth) b e w t
  selectedScore_spec := by intros; rfl
    -- @realizes \(\mathfrak H_{\mathrm{loc}}\)(sharp-risk derivation handle)

end CausalSmith.Stat.PomdpLatentOverlapMinimax
