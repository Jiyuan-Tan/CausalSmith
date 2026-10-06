module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LowerLength

/-! # Monotone-IV continuum lower bound for every honest measurable set -/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @node: thm:honest-lower-full-elbow
/-- Given [the supplied inputs](hyp:α,c_f,C_f,L,hα,hf,hF,hL), [the stated result about honest lower full elbow holds](goal). -/
theorem honest_lower_full_elbow (α c_f C_f L : ℝ)
    (hα : 0 < α ∧ α < 1) (hf : 0 < c_f ∧ c_f < 1)
    (hF : 1 < C_f) (hL : 1 < L) :
    ∃ c0 : ℝ, 0 < c0 ∧ -- @realizes c_0(positive lower constant)
      ∀ n : ℕ, threshold ≤ n →
      ∀ a : ℝ, 0 < a → a ≤ 1 / 4 →
        (∀ C : TwoSample n n → Set ℝ,
          (∀ ω, C ω ⊆ parameterSpace) →
          MeasurableSet {p : TwoSample n n × ℝ | p.2 ∈ C p.1} →
          (∀ P : TransportLaw, ModelClass c_f C_f L P n →
            1 - α ≤ (dataLaw P n n {ω | targetCACE P ∈ C ω}).toReal) →
          c0 * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) ≤
            ⨆ P : {P // P ∈ StrengthSlice c_f C_f L a n},
              expectedLength P.1 n n C) ∧
        c0 * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) ≤
          lengthFrontier α c_f C_f L a n  := by
  classical
  obtain ⟨cStar, hcStar, hcStar1, hAdm, hmix⟩ :=
    legal_iv_mixture_full_elbow α c_f C_f L hα hf hF hL
  let c0 := (1 - α) * (2 : ℝ) ^ ((3 : ℝ) / 4) * cStar ^ 2
  have hαpos : 0 < 1 - α := by linarith [hα.2]
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  refine ⟨c0, hc0, ?_⟩
  intro n hn a ha ha4
  obtain ⟨hτall, hcenter, hcenterμ, hcenterθ, hJlo, hJhi⟩ := hmix n hn a ha ha4
  have hPcenter : ModelClass c_f C_f L (mixtureCenter a n) n := hcenter.2.2.1
  let := dataLaw_isProbabilityMeasure_of_model c_f C_f L (mixtureCenter a n) n hPcenter
  have hnpos : 0 < n := by have : 256 ≤ n := hn; omega
  have hrate : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hb : 0 < actualStrength a n := (actualStrength_bounds a n hn ⟨ha, ha4⟩).1
  have hJ : 0 < separation cStar n := lt_of_lt_of_le (by positivity) hJlo
  let r := separation cStar n / actualStrength a n
  have hr : 0 < r := div_pos hJ hb
  have hr1 : r ≤ 1 := by
    have hcomp := (hτall (-1) (by norm_num)).1 (fun _ => false)
    have hθ := (transported_cace_identification c_f C_f L _ n hf hF hL
      hcomp.1.2.2.1).2.2.2.2.2.2
    rw [hcomp.2.2.2] at hθ
    change _ ∈ Icc (-1 : ℝ) 1 at hθ
    simpa [r] using hθ.2
  have hscale : c0 * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) ≤ (1 - α) * r := by
    rw [← actualStrength_rate_identity a n ha hnpos]
    have h := div_le_div_of_nonneg_right hJlo hb.le
    have h' := mul_le_mul_of_nonneg_left h (by linarith [hα.2] : 0 ≤ 1 - α)
    dsimp only [c0, r]
    convert h' using 1 <;> first | rfl | ring
  have hrow : ∀ C : TwoSample n n → Set ℝ,
      (∀ ω, C ω ⊆ parameterSpace) →
      MeasurableSet {p : TwoSample n n × ℝ | p.2 ∈ C p.1} →
      (∀ P : TransportLaw, ModelClass c_f C_f L P n →
        1 - α ≤ (dataLaw P n n {ω | targetCACE P ∈ C ω}).toReal) →
      c0 * min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) ≤
        ⨆ P : {P // P ∈ StrengthSlice c_f C_f L a n}, expectedLength P.1 n n C := by
    intro C hsub hgraph hhonest
    have hpoint : ∀ t ∈ Icc (-r) r,
        (1 - α) / 2 ≤ (dataLaw (mixtureCenter a n) n n {ω | t ∈ C ω}).toReal := by
      intro t ht
      let τ := -t / r
      have hτ : τ ∈ Icc (-1 : ℝ) 1 := by
        constructor
        · apply (le_div_iff₀ hr).2
          linarith [ht.2]
        · apply (div_le_iff₀ hr).2
          linarith [ht.1]
      obtain ⟨hcomp, hchi, htv, _hac, _hint⟩ := hτall τ hτ
      let Q := fun sgn : Fin (lowerCells n) → Bool =>
        dataLaw (legalIVComponent a n cStar τ sgn) n n
      let hQ : ∀ sgn, IsProbabilityMeasure (Q sgn) := fun sgn =>
        dataLaw_isProbabilityMeasure_of_model c_f C_f L _ n (hcomp sgn).1.2.2.1
      have hparam (sgn : Fin (lowerCells n) → Bool) :
          targetCACE (legalIVComponent a n cStar τ sgn) = t := by
        rw [(hcomp sgn).2.2.2]
        dsimp [τ, r]
        field_simp
      have hcover : 1 - α ≤ (lowerMixture a n cStar τ {ω | t ∈ C ω}).toReal := by
        rw [lowerMixture_eq_uniform_data]
        apply uniform_data_mixture_coverage Q _ (1 - α)
        intro sgn
        simpa only [hparam sgn] using hhonest _ (hcomp sgn).1.2.2.1
      let hprob : IsProbabilityMeasure (lowerMixture a n cStar τ) := by
        rw [lowerMixture_eq_uniform_data]
        exact Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability Q
      have hE : MeasurableSet {ω | t ∈ C ω} :=
        hgraph.preimage (measurable_id.prodMk measurable_const)
      have hgap := Causalean.Stat.measureReal_sub_le_tvDist
        (μ := dataLaw (mixtureCenter a n) n n) (ν := lowerMixture a n cStar τ) hE
      rw [Causalean.Stat.tvDist_symm] at hgap
      change (lowerMixture a n cStar τ {ω | t ∈ C ω}).toReal -
        (dataLaw (mixtureCenter a n) n n {ω | t ∈ C ω}).toReal ≤ _ at hgap
      linarith
    have hlength := expectedLength_lower_of_inclusion (mixtureCenter a n) n C
      hgraph r ((1 - α) / 2) hr.le hr1 hpoint
    have hcenterlower : (1 - α) * r ≤ expectedLength (mixtureCenter a n) n n C := by
      nlinarith [hlength]
    have hbdd : BddAbove (range (fun P : {P // P ∈ StrengthSlice c_f C_f L a n} =>
        expectedLength P.1 n n C)) := by
      refine ⟨2, ?_⟩
      rintro _ ⟨P, rfl⟩
      let := dataLaw_isProbabilityMeasure_of_model c_f C_f L P.1 n P.2.2.2.1
      exact expectedLength_le_two P.1 n C
    exact hscale.trans (hcenterlower.trans (le_ciSup hbdd ⟨mixtureCenter a n, hcenter⟩))
  refine ⟨hrow, ?_⟩
  let : Nonempty {C // C ∈ HonestIntervals α c_f C_f L n} :=
    ⟨⟨fun _ => parameterSpace, parameterSpace_honest α c_f C_f L hα n⟩⟩
  unfold lengthFrontier
  apply le_ciInf
  intro C
  rcases C.2 with ⟨_, _, hsub, hgraph, hhonest⟩
  exact hrow C.1 (fun ω => (hsub ω).1) hgraph hhonest

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
