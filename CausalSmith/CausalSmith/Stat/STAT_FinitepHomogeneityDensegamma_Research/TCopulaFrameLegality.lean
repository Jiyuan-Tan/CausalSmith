module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CopulaAlternativeLegality
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CopulaGeometry
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.SmoothedTentIntegrals

/-! Finite-moment homogeneity testing: TCopulaFrameLegality. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- [Copula frame legality](goal).
Put \(q=(p-1)/p\), \(S=\alpha+\beta\), and \(F(p)=2\alpha/(p-1)+\beta/q+S/(2\gamma)\). Suppose
\(F(p)<1\). For dyadic \(K\ge16M\), \(M\ge2\), \(M\le K^{S/\gamma}\), use Definition
\(\mathrm{def:copula\mbox{-}frame\mbox{-}priors}\) with \[  a=K^{-\alpha}/16,\quad
b=K^{-\beta}/256,\quad  u=1/16,\quad\varepsilon=(16b)^{1/q},\quad L=\varepsilon^{-1/p}. \] Every
support law of \(\pi_0\) belongs to \(H_0(v)\); every support law of \(\pi_1\) belongs to
\(\mathcal M_v\) and has deterministic, centered effect \[
\tau_P=-\frac{2ab\kappa}{1-a^2}\widetilde g_\sigma,\qquad  2^{-17}K^{-S}\le
d(P)\le2^{-14}K^{-S}<d_0. \] Every conditional arm raw \(p\)-moment equals one. For the bounded
version take \(v=(2,w)\), \(F(2)<1\), keep \(a,b\), and instead use \(u=2b\),
\(\varepsilon=1/2\), \(L=1\). Its supports are bounded nulls and bounded alternatives with
exactly the same effect and distance bounds. Its conditional arm raw second moment is \(1/2\).
-/
-- @node: lem:copula-frame-legality
lemma copula_frame_legality :
    (∀ v : Params, v.Valid → Fphase v < 1 → ∀ K M : ℕ, LegalityRanks v K M →
      (∀ idx : CopulaIndex K M,
        let law := copulaLaw false v K M (legalityA v K) (1/16) (legalityRarity v K) (legalityMagnitude v K) idx
        InNull v law ∧
        ∀ a : Bool, ∀ x : unitInterval, ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂law.Q a x=1) ∧
      (∀ idx : CopulaIndex K M,
        let law := copulaLaw true v K M (legalityA v K) (1/16) (legalityRarity v K) (legalityMagnitude v K) idx
        InModel v law ∧ CopulaEffectConclusion v K M idx law ∧
        ∀ a : Bool, ∀ x : unitInterval, ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂law.Q a x=1)) ∧
    (∀ w : Smooth3, w.Valid →
      let v := Params.ofBounded w
      Fphase v < 1 → ∀ K M : ℕ, LegalityRanks v K M →
      (∀ idx : CopulaIndex K M,
        let law := copulaLaw false v K M (legalityA v K) (2*legalityB v K) (1/2) 1 idx
        InBoundedNull w law ∧
        ∀ a : Bool, ∀ x : unitInterval, ∫⁻ y, ENNReal.ofReal (|y|^(2:ℝ)) ∂law.Q a x=1/2) ∧
      (∀ idx : CopulaIndex K M,
        let law := copulaLaw true v K M (legalityA v K) (2*legalityB v K) (1/2) 1 idx
        InBoundedModel w law ∧ CopulaEffectConclusion v K M idx law ∧
        ∀ a : Bool, ∀ x : unitInterval, ∫⁻ y, ENNReal.ofReal (|y|^(2:ℝ)) ∂law.Q a x=1/2)) := by
  constructor
  · intro v hv hphase K M hranks
    constructor
    · intro idx
      refine ⟨?_, (legality_arm_moments v hv K M hranks false idx).1⟩
      have hd := (legality_copula_domains v hv K M hranks).1
      have hK : 1 ≤ K := by have := hranks.2.2.1; have := hranks.2.2.2.1; omega
      have hid := legality_tuning_identities v hv K hK
      exact legality_null_inNull v hv K M hranks _ _ _ hd hid.2 (by rw [hid.1]; norm_num) idx
    · intro idx
      refine ⟨?_, ?_, (legality_arm_moments v hv K M hranks true idx).1⟩
      · have hd := (legality_copula_domains v hv K M hranks).1
        have hK : 1 ≤ K := by have := hranks.2.2.1; have := hranks.2.2.2.1; omega
        have hid := legality_tuning_identities v hv K hK
        exact legality_alternative_inModel v hv hphase K M hranks _ _ _ hd hid.2
          (by rw [hid.1]; norm_num) idx
      · have hK : 1 ≤ K := by have := hranks.2.2.1; have := hranks.2.2.2.1; omega
        have hmean : (∫ x : unitInterval, smoothedTent K M idx.1 x ∂design) = 0 := by
          exact smoothedTent_integral_zero_of_legalityRanks v K M hranks idx.1
        have hsecond := smoothedTent_second_moment_lower_of_legalityRanks v K M hranks idx.1
        exact legality_separation_of_moments v hv K M hK idx _
          (legality_effect_formulas v hv K M hranks idx).1 hmean
          ⟨hsecond, smoothedTent_second_moment_le_one K M (by omega) idx.1⟩
  · intro w hw
    dsimp only
    intro hphase K M hranks
    have hv : (Params.ofBounded w).Valid := ⟨by norm_num [Params.ofBounded], hw⟩
    constructor
    · intro idx
      refine ⟨?_, (legality_arm_moments (Params.ofBounded w) hv K M hranks false idx).2⟩
      have hd := (legality_copula_domains (Params.ofBounded w) hv K M hranks).2
      have hnull := legality_null_inNull (Params.ofBounded w) hv K M hranks _ _ _ hd
        (by ring) (by norm_num [Params.ofBounded]) idx
      have ht := copula_table_valid 2 K M _ _ _ _ hd false idx
      have hb : BoundedOutcome (copulaLaw false (Params.ofBounded w) K M
          (legalityA (Params.ofBounded w) K) (2*legalityB (Params.ofBounded w) K) (1/2) 1 idx) :=
        tableObservedLaw_unit_bounded _ _ _ _ ht
      exact ⟨hnull.uniform, hnull.overlap, hnull.propensitySmooth, hnull.baselineSmooth,
        hnull.effectSmooth, hnull.baselineCap, hnull.effectCap, hnull.rawMoment, hb,
        hnull.nullConstancy⟩
    · intro idx
      refine ⟨?_, ?_, (legality_arm_moments (Params.ofBounded w) hv K M hranks true idx).2⟩
      · have hd := (legality_copula_domains (Params.ofBounded w) hv K M hranks).2
        have hm := legality_alternative_inModel (Params.ofBounded w) hv hphase K M hranks
          _ _ _ hd (by ring) (by norm_num [Params.ofBounded]) idx
        have ht := copula_table_valid 2 K M _ _ _ _ hd true idx
        have hb : BoundedOutcome (copulaLaw true (Params.ofBounded w) K M
            (legalityA (Params.ofBounded w) K) (2*legalityB (Params.ofBounded w) K) (1/2) 1 idx) :=
          tableObservedLaw_unit_bounded _ _ _ _ ht
        exact ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
          hm.effectSmooth, hm.baselineCap, hm.effectCap, hm.rawMoment, hb⟩
      · have hK : 1 ≤ K := by have := hranks.2.2.1; have := hranks.2.2.2.1; omega
        have hmean : (∫ x : unitInterval, smoothedTent K M idx.1 x ∂design) = 0 := by
          exact smoothedTent_integral_zero_of_legalityRanks (Params.ofBounded w) K M hranks idx.1
        have hsecond := smoothedTent_second_moment_lower_of_legalityRanks (Params.ofBounded w) K M hranks idx.1
        exact legality_separation_of_moments (Params.ofBounded w) hv K M hK idx _
          (legality_effect_formulas (Params.ofBounded w) hv K M hranks idx).2 hmean
          ⟨hsecond, smoothedTent_second_moment_le_one K M (by omega) idx.1⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma
