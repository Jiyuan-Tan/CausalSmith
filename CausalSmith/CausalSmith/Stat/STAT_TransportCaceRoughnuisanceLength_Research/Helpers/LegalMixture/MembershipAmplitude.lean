module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.ProbabilitySupport

/-! # Uniform amplitude ceiling for mixture membership

Roadmap (9) chooses one positive ceiling independent of the sample size,
strength, signs, and continuum index. The resulting height bound discharges
the density envelopes before the remaining smoothness and assignment checks.
-/

public section

open Set MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The tile-height scaling never increases a nonnegative amplitude.  Under [the displayed assumptions and inputs](hyp:cStar,n,hc,hn), [the stated conclusion holds](goal). -/
-- @node: lowerHeight_le_amplitude
lemma lowerHeight_le_amplitude (cStar : ℝ) (n : ℕ)
    (hc : 0 ≤ cStar) (hn : threshold ≤ n) :
    lowerHeight cStar n ≤ cStar := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by have : 256 ≤ n := hn; omega)
  have hK1 : (1 : ℝ) ≤ lowerCells n :=
    (Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans
      (Nat.le_ceil _)
  have hscale := Real.rpow_le_one_of_one_le_of_nonpos hK1
    (by norm_num : (-(1 / 8 : ℝ)) ≤ 0)
  simpa only [lowerHeight, mul_one] using
    mul_le_mul_of_nonneg_left hscale hc

/-- A positive ceiling satisfies all five margin restrictions in roadmap (9),
with the smaller admissibility ceiling already established in Lean.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,hf,hF,hL), [the stated conclusion holds](goal). -/
-- @node: exists_membership_amplitude_ceiling
lemma exists_membership_amplitude_ceiling (c_f C_f L : ℝ)
    (hf : c_f < 1) (hF : 1 < C_f) (hL : 1 < L) :
    ∃ cap : ℝ, 0 < cap ∧ cap < 1 ∧ cap ≤ 1 / 100 ∧
      cap ≤ 1 - c_f ∧ cap ≤ C_f - 1 ∧
      cap ≤ (L - 1) / (1 + 2 * Real.pi) ∧
      cap ≤ (L - 3 / 4) / (6 * Real.pi) := by
  let cap := min (1 / 100 : ℝ) (min (1 - c_f) (min (C_f - 1)
    (min ((L - 1) / (1 + 2 * Real.pi)) ((L - 3 / 4) / (6 * Real.pi)))))
  have hp : 0 < cap := by
    dsimp [cap]
    apply lt_min (by norm_num)
    apply lt_min (by linarith)
    apply lt_min (by linarith)
    apply lt_min
    · exact div_pos (by linarith) (by positivity)
    · exact div_pos (by linarith) (by positivity)
  have hb : cap ≤ 1 / 100 ∧ cap ≤ 1 - c_f ∧ cap ≤ C_f - 1 ∧
      cap ≤ (L - 1) / (1 + 2 * Real.pi) ∧
      cap ≤ (L - 3 / 4) / (6 * Real.pi) := by
    have h : cap ≤ min (1 / 100 : ℝ) (min (1 - c_f) (min (C_f - 1)
      (min ((L - 1) / (1 + 2 * Real.pi)) ((L - 3 / 4) / (6 * Real.pi))))) := le_rfl
    simpa only [le_min_iff] using h
  exact ⟨cap, hp, lt_of_le_of_lt hb.1 (by norm_num), hb⟩

/-- The ceiling and admissibility bounds verify both density identities,
the density envelopes, and propensity overlap for every component. Under [the displayed assumptions and inputs](hyp:a,c_f,C_f,cStar,n,sgn,hf,hF,hn,ha,hc,hlo,hhi,hτ), [the stated conclusion holds](goal). -/
-- @node: legalIVComponent_density_overlap_of_ceiling
lemma legalIVComponent_density_overlap_of_ceiling (a c_f C_f cStar τ : ℝ)
    (n : ℕ) (sgn : Fin (lowerCells n) → Bool)
    (hf : 0 < c_f ∧ c_f < 1) (hF : 1 < C_f)
    (hn : threshold ≤ n) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hc : 0 < cStar ∧ cStar ≤ 1 / 100)
    (hlo : cStar ≤ 1 - c_f) (hhi : cStar ≤ C_f - 1)
    (hτ : τ ∈ Icc (-1 : ℝ) 1) :
    SourceDensityBounds c_f C_f (legalIVComponent a n cStar τ sgn) ∧
      TargetDensityBounds c_f C_f (legalIVComponent a n cStar τ sgn) ∧
      PropensityOverlap (legalIVComponent a n cStar τ sgn) := by
  have hb := actualStrength_bounds a n hn ha
  have hAdm := lower_admissible_of_small_amplitude n a cStar hn ha hc
  have hnpos : 0 < n := by have : 256 ≤ n := hn; omega
  have hh := lowerHeight_le_amplitude cStar n hc.1.le hn
  refine ⟨legalIVComponent_sourceDensityBounds a c_f C_f n cStar τ sgn
    hf hF hb hAdm hτ hnpos,
    legalIVComponent_targetDensityBounds a c_f C_f n cStar τ sgn
      hb hAdm hτ hnpos (hh.trans hlo) (hh.trans hhi) hf.1, ?_⟩
  intro x hx
  have hu := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hc.1.le
  change (1 / 4 : ℝ) ≤ 1 / 2 + tiledPerturbation cStar n sgn x ∧
    1 / 2 + tiledPerturbation cStar n sgn x ≤ 3 / 4
  constructor <;> linarith [neg_abs_le (tiledPerturbation cStar n sgn x),
    le_abs_self (tiledPerturbation cStar n sgn x), hAdm.2.1]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
