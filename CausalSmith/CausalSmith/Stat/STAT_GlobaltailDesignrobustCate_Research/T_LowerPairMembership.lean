module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairHolder
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairExchangeability
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairInformation
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairSemantics

/-! # Membership and information bound for the binary two-law pair -/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory InformationTheory
open scoped ENNReal

-- @node: prop:lower-pair-membership
/-- Both signed binary witnesses belong to the same fixed-constant class;
their regression gap and observed-product KL have the stated sizes. -/
theorem lower_pair_membership (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ δ₀ K : ℝ, 0 < δ₀ ∧ 0 < K ∧
      ∀ (δ : ℝ) (j n : ℕ), 0 < δ → δ ≤ δ₀ → 1 ≤ n →
        let h := dyadicWidth j
        let Pplus := lowerPair d β (tailExponent γ) h δ M true
        let Pminus := lowerPair d β (tailExponent γ) h δ M false
        LawClass d β γ C L M Pplus ∧
        LawClass d β γ C L M Pminus ∧
        supLoss Pplus.mu1 Pminus.mu1 = ENNReal.ofReal (2 * δ * h ^ β) ∧
        klDiv (Measure.pi (fun _ : Fin n => Pplus.obs))
          (Measure.pi (fun _ : Fin n => Pminus.obs)) ≤
          ENNReal.ofReal (K * (n : ℝ) * h ^ (2 * β + effectiveDimension d γ)) := by
  rcases hparam with ⟨hd, hβ, hγ, hC, hL, hM⟩
  obtain ⟨B, hB, hball⟩ := witnessMean_uniform_holderBall_euclid d β hβ
  refine ⟨min (L / B) (M / 4), 1, lt_min (div_pos hL hB) (by positivity),
    by norm_num, ?_⟩
  intro δ j n hδ hδsmall hn
  dsimp only
  have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have hh1 : dyadicWidth j ≤ 1 := by
    rw [dyadicWidth, one_div]
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by norm_num)
  have hq : 0 < tailExponent γ := by unfold tailExponent; linarith
  have hsmall : δ ≤ M / 4 := hδsmall.trans (min_le_right _ _)
  have hδB : δ * B ≤ L :=
    (le_div_iff₀ hB).mp (hδsmall.trans (min_le_left _ _))
  have hholder (sign : Bool) :
      TreatedHolder (lowerPair d β (tailExponent γ) (dyadicWidth j) δ M sign) β L := by
    refine ⟨fun x => witnessMean d β δ (dyadicWidth j) sign (WithLp.ofLp x),
      ?_, fun _ _ => rfl⟩
    obtain ⟨hsmooth, hderiv, hmod⟩ := hball δ (dyadicWidth j) hδ.le hh hh1 sign
    refine ⟨hsmooth, ?_, ?_⟩
    · intro k hk x
      exact (hderiv k hk x).trans hδB
    · intro x y
      exact (hmod x y).trans
        (mul_le_mul_of_nonneg_right hδB (Real.rpow_nonneg (norm_nonneg _) _))
  have hclass (sign : Bool) :
      LawClass d β γ C L M (lowerPair d β (tailExponent γ) (dyadicWidth j) δ M sign) := by
    exact {
      parameters := ⟨hd, hβ, hγ, hC, hL, hM⟩
      semantics := lowerPair_lawSemantics d β (tailExponent γ) (dyadicWidth j) δ M
        hd hq hβ hδ.le hh hh1 hM hsmall sign
      iid := lowerPair_iidSampling d β (tailExponent γ) (dyadicWidth j) δ M
        hd hq hβ hδ.le hh hh1 hM hsmall sign
      uniformDesign := lowerPair_uniformDesign d β (tailExponent γ) (dyadicWidth j) δ M
        hd hq hβ hδ.le hh hh1 hM hsmall sign
      boundedOutcomes := lowerPair_boundedOutcomes d β (tailExponent γ)
        (dyadicWidth j) δ M hM.le sign
      consistency := lowerPair_consistency d β (tailExponent γ) (dyadicWidth j) δ M sign
      exchangeability := lowerPair_exchangeability d β (tailExponent γ)
        (dyadicWidth j) δ M hd hq hβ hδ.le hh hh1 hM hsmall sign
      measurablePropensity := lowerPair_measurablePropensity d β (tailExponent γ)
        (dyadicWidth j) δ M hd hq sign
      globalTail := lowerPair_globalTail d β γ C (dyadicWidth j) δ M
        hd hγ hC hβ hδ.le hh hh1 hM hsmall sign
      treatedHolder := hholder sign }
  refine ⟨hclass true, hclass false,
    lowerPair_supLoss d β (tailExponent γ) (dyadicWidth j) δ M hδ.le hh, ?_⟩
  simpa only [one_mul] using lowerPair_product_klDiv_le_unit d n β γ
    (dyadicWidth j) δ M hd hγ hβ hδ.le hh hh1 hM hsmall

end CausalSmith.Stat.GlobalTailDesignRobustCate
