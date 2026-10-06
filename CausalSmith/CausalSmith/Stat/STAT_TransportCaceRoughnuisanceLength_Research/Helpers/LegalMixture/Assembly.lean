module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.SourceOverlap

/-! # Legal-mixture two-channel assembly -/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- [The covariate center is probability object](goal) is defined without additional inputs. -/

noncomputable def covariateCenter_isProbability :
    IsProbabilityMeasure (volume.restrict covariateSpace) := by
  apply isProbabilityMeasure_iff.mpr
  simp [covariateSpace]
/-- [The lower explicit source is probability object](goal) is defined from [the supplied inputs](hyp:a,n,cStar,sgn,hb,hAdm). -/

noncomputable def lowerExplicitSource_isProbability
    (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1) :
    IsProbabilityMeasure
      (explicitSourceLaw (actualStrength a n)
        (tiledPerturbation cStar n sgn)
        (fun x => τ * tiledPerturbation cStar n sgn x)) := by
  apply explicitSourceLaw_isProbability_of_nonneg
  · exact tiledPerturbation_measurable cStar n sgn
  · exact lowerSourceCellMass_nonneg a n cStar τ sgn hb hAdm hτ
/-- [The lower target density is probability object](goal) is defined from [the supplied inputs](hyp:cStar,n,sgn,hn,hAdm). -/

noncomputable def lowerTargetDensity_isProbability
    (cStar : ℝ) (n : ℕ) (sgn : Fin (lowerCells n) → Bool)
    (hn : 0 < n) (hAdm : LowerAdmissible n a cStar) :
    IsProbabilityMeasure
      ((volume.restrict covariateSpace).withDensity
        (fun x => ENNReal.ofReal (1 + tiledPerturbation cStar n sgn x))) := by
  apply isProbabilityMeasure_iff.mpr
  apply targetDensity_univ cStar n sgn hn
  intro x
  have hu := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
  have hu' : |tiledPerturbation cStar n sgn x| ≤ 3 / 16 := le_trans hu hAdm.2.1
  linarith [neg_abs_le (tiledPerturbation cStar n sgn x)]
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,hb,hAdm,hn,hτ), [the stated result about legal data law eq product holds](goal). -/

lemma legal_dataLaw_eq_product (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1)
    (hn : 0 < n) :
    dataLaw (legalIVComponent a n cStar τ sgn) n n =
      (Measure.pi (fun _ : Fin n =>
        explicitSourceLaw (actualStrength a n)
          (tiledPerturbation cStar n sgn)
          (fun x => τ * tiledPerturbation cStar n sgn x))).prod
      (Measure.pi (fun _ : Fin n =>
        (volume.restrict covariateSpace).withDensity
          (fun x => ENNReal.ofReal (1 + tiledPerturbation cStar n sgn x)))) := by
  unfold dataLaw legalIVComponent lawFromMass
  dsimp
  rw [lowerSourceLaw_eq_explicit a n cStar τ sgn hb hAdm hτ,
    legalTargetLaw_eq_density a n cStar τ sgn hb hAdm hτ hn]
  rfl
/-- Given [the supplied inputs](hyp:a,n,hb), [the stated result about center data law eq product holds](goal). -/

lemma center_dataLaw_eq_product (a : ℝ) (n : ℕ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) :
    dataLaw (mixtureCenter a n) n n =
      (Measure.pi (fun _ : Fin n =>
        explicitSourceLaw (actualStrength a n) (fun _ => 0) (fun _ => 0))).prod
      (Measure.pi (fun _ : Fin n => volume.restrict covariateSpace)) := by
  unfold dataLaw mixtureCenter lawFromMass
  dsimp
  rw [centerSourceLaw_eq_explicit a n hb,
    centerTargetLaw_eq_volume a n hb]
/-- Given [the supplied inputs](hyp:a,n,cStar,hb,hAdm,hn,hτ), [the stated result about lower mixture eq uniform mixture holds](goal). -/

lemma lowerMixture_eq_uniformMixture (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1)
    (hn : 0 < n) :
    lowerMixture a n cStar τ =
      Causalean.Stat.Minimax.Mixture.uniformMixture (fun sgn :
        Fin (lowerCells n) → Bool =>
        (Measure.pi (fun _ : Fin n =>
          explicitSourceLaw (actualStrength a n)
            (tiledPerturbation cStar n sgn)
            (fun x => τ * tiledPerturbation cStar n sgn x))).prod
        (Measure.pi (fun _ : Fin n =>
          (volume.restrict covariateSpace).withDensity
            (fun x => ENNReal.ofReal
              (1 + tiledPerturbation cStar n sgn x))))) := by
  classical
  unfold lowerMixture Causalean.Stat.Minimax.Mixture.uniformMixture
    Causalean.Stat.mixture
  simp_rw [legal_dataLaw_eq_product a n cStar τ _ hb hAdm hτ hn]
  rw [Finset.smul_sum]
  simp [Fintype.card_fun, Fintype.card_fin]

/-- Finite mixtures inherit domination and square-integrable density deviations
from their integrable pairwise density products.  Under [the displayed assumptions and inputs](hyp:Ω,S,Q,P,hac,hpair), [the stated conclusion holds](goal). -/
-- @node: uniformMixture_finite_chiSquare
lemma uniformMixture_finite_chiSquare {Ω S : Type*} [MeasurableSpace Ω]
    [Fintype S] [Nonempty S] (Q : S → Measure Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] [∀ s, IsProbabilityMeasure (Q s)]
    (hac : ∀ s, Q s ≪ P)
    (hpair : ∀ s t, Integrable
      (fun x => ((Q s).rnDeriv P x).toReal *
        ((Q t).rnDeriv P x).toReal) P) :
    (Causalean.Stat.Minimax.Mixture.uniformMixture Q) ≪ P ∧
    Integrable (fun x =>
      (((Causalean.Stat.Minimax.Mixture.uniformMixture Q).rnDeriv P x).toReal - 1) ^ 2)
      P := by
  classical
  let M := Causalean.Stat.Minimax.Mixture.uniformMixture Q
  let d (s : S) (x : Ω) : ℝ := ((Q s).rnDeriv P x).toReal
  let p (x : Ω) : ℝ := (M.rnDeriv P x).toReal
  let card : ℝ := Fintype.card S
  letI : IsProbabilityMeasure M :=
    Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability Q
  have hdouble : Integrable (fun x => ∑ s : S, ∑ t : S,
      d s x * d t x) P := by
    exact integrable_finsetSum Finset.univ (fun s _ =>
      integrable_finsetSum Finset.univ (fun t _ => hpair s t))
  have hpoint : ∀ᵐ x ∂P, p x ^ 2 =
      (∑ s : S, ∑ t : S, d s x * d t x) / card ^ 2 := by
    filter_upwards [Causalean.Stat.Minimax.Mixture.uniformMixture_rnDeriv
      Q P hac] with x hx
    change p x = (∑ s : S, d s x) / card at hx
    rw [hx, div_pow, sq, Finset.sum_mul_sum]
  have hsq : Integrable (fun x => p x ^ 2) P :=
    (hdouble.div_const (card ^ 2)).congr (hpoint.mono fun x hx => hx.symm)
  have hp : Integrable p P := Measure.integrable_toReal_rnDeriv
  have hdev : Integrable (fun x => (p x - 1) ^ 2) P := by
    have heq : (fun x => (p x - 1) ^ 2) =
        (fun x => p x ^ 2 - 2 * p x + 1) := by
      funext x
      ring
    rw [heq]
    exact (hsq.sub (hp.const_mul 2)).add (integrable_const 1)
  exact ⟨Causalean.Stat.Minimax.Mixture.uniformMixture_absolutelyContinuous Q P hac,
    hdev⟩
/-- Given [the supplied inputs](hyp:Ω,S,Q,P,hac,hpair), [the stated result about tv uniform mixture le half sqrt holds](goal). -/

lemma tv_uniformMixture_le_half_sqrt {Ω S : Type*} [MeasurableSpace Ω]
    [Fintype S] [Nonempty S] (Q : S → Measure Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] [∀ s, IsProbabilityMeasure (Q s)]
    (hac : ∀ s, Q s ≪ P)
    (hpair : ∀ s t, Integrable
      (fun x => ((Q s).rnDeriv P x).toReal *
        ((Q t).rnDeriv P x).toReal) P) :
    Causalean.Stat.tvDist
      (Causalean.Stat.Minimax.Mixture.uniformMixture Q) P ≤
      (1 / 2) * Real.sqrt (Causalean.Stat.chiSqDiv
        (Causalean.Stat.Minimax.Mixture.uniformMixture Q) P) := by
  letI := Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability Q
  have h := uniformMixture_finite_chiSquare Q P hac hpair
  exact Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv _ P h.1 h.2
/-- Given [the supplied inputs](hyp:b,hb,hτ), [the stated result about source overlap coefficient le holds](goal). -/

lemma sourceOverlapCoefficient_le (b τ : ℝ)
    (hb : 0 ≤ b ∧ b ≤ 1 / 4) (hτ : τ ∈ Icc (-1 : ℝ) 1) :
    0 ≤ sourceOverlapCoefficient b τ ∧
      sourceOverlapCoefficient b τ + 1 ≤ 139 / 15 := by
  have hbden : (15 / 16 : ℝ) ≤ 1 - b ^ 2 := by nlinarith [sq_nonneg b]
  have hbden0 : 0 < 1 - b ^ 2 := lt_of_lt_of_le (by norm_num) hbden
  have hτsq : τ ^ 2 ≤ 1 := by nlinarith [hτ.1, hτ.2]
  have hfrac : τ ^ 2 / (1 - b ^ 2) ≤ 16 / 15 := by
    apply (div_le_iff₀ hbden0).2
    nlinarith [sq_nonneg τ]
  unfold sourceOverlapCoefficient
  constructor
  · positivity
  · calc
      4 + 4 * τ ^ 2 / (1 - b ^ 2) + 1 =
          4 + 4 * (τ ^ 2 / (1 - b ^ 2)) + 1 := by ring
      _ ≤
          4 + 4 * (16 / 15 : ℝ) + 1 := by gcongr
      _ = 139 / 15 := by norm_num
/-- Given [the supplied inputs](hyp:n,K,cStar,G,hn,hK,hbase,hG0,hG), [the stated result about sample height exponent bound holds](goal). -/

lemma sample_height_exponent_bound (n K : ℕ) (cStar G : ℝ)
    (hn : 0 < n) (hK : 0 < K)
    (hbase : (n : ℝ) ^ ((4 : ℝ) / 3) ≤ K)
    (hG0 : 0 ≤ G) (hG : G ≤ 139 / 15) :
    ((((n : ℝ) * (G * (cStar * (K : ℝ) ^ (-(1 / 8 : ℝ))) ^ 2 / 2)) ^ 2) /
        (2 * (K : ℝ))) ≤ mixConstant * cStar ^ 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hpow : (n : ℝ) ^ 2 ≤ (K : ℝ) ^ ((3 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow (by positivity :
      0 ≤ (n : ℝ) ^ ((4 : ℝ) / 3)) hbase
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [← Real.rpow_mul hnR.le] at h
    norm_num at h ⊢
    simpa [Real.rpow_natCast] using h
  have hGsq : G ^ 2 ≤ (139 / 15 : ℝ) ^ 2 := by nlinarith
  have hscale :
      (K : ℝ) ^ ((3 : ℝ) / 2) *
          ((K : ℝ) ^ (-(1 / 8 : ℝ))) ^ 4 /
          (K : ℝ) = 1 := by
    rw [← Real.rpow_mul_natCast hKR.le]
    norm_num
    rw [← Real.rpow_add hKR]
    norm_num
    exact Nat.ne_of_gt hK
  unfold mixConstant
  have hc4 : 0 ≤ cStar ^ 4 := by positivity
  have hkfac : 0 ≤ ((K : ℝ) ^ (-(1 / 8 : ℝ))) ^ 4 := by positivity
  have hmul := mul_le_mul hpow hGsq (sq_nonneg G) (by positivity : 0 ≤ (K : ℝ) ^ ((3 : ℝ) / 2))
  calc
    ((n : ℝ) * (G * (cStar * (K : ℝ) ^ (-(1 / 8 : ℝ))) ^ 2 / 2)) ^ 2 /
          (2 * (K : ℝ)) =
        ((n : ℝ) ^ 2 * G ^ 2 * cStar ^ 4 *
          ((K : ℝ) ^ (-(1 / 8 : ℝ))) ^ 4) /
          (8 * (K : ℝ)) := by ring
    _ ≤ (((K : ℝ) ^ ((3 : ℝ) / 2)) * (139 / 15 : ℝ) ^ 2 *
          cStar ^ 4 * ((K : ℝ) ^ (-(1 / 8 : ℝ))) ^ 4) /
          (8 * (K : ℝ)) := by
        gcongr
    _ = (19321 / 1800 : ℝ) * cStar ^ 4 := by
        rw [show ((K : ℝ) ^ ((3 : ℝ) / 2) * (139 / 15 : ℝ) ^ 2 *
            cStar ^ 4 * ((K : ℝ) ^ (-(1 / 8 : ℝ))) ^ 4) /
            (8 * (K : ℝ)) =
          ((139 / 15 : ℝ) ^ 2 / 8) * cStar ^ 4 *
            (((K : ℝ) ^ ((3 : ℝ) / 2) *
              ((K : ℝ) ^ (-(1 / 8 : ℝ))) ^ 4) / K) by ring]
        rw [hscale]
        norm_num
/-- Given [the supplied inputs](hyp:a,n,cStar,hn,ha,hc,hτ), [the stated result about legal two channel exp bound holds](goal). -/

lemma legal_twoChannel_exp_bound (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (hτ : τ ∈ Icc (-1 : ℝ) 1) (hn : threshold ≤ n)
    (ha : 0 < a ∧ a ≤ 1 / 4) (hc : 0 < cStar ∧ cStar ≤ 1 / 100) :
    1 + Causalean.Stat.chiSqDiv
      (lowerMixture a n cStar τ)
      (dataLaw (mixtureCenter a n) n n) ≤
    Real.exp ((((n : ℝ) *
          (sourceOverlapCoefficient (actualStrength a n) τ *
            lowerHeight cStar n ^ 2 / 2) +
        (n : ℝ) * (lowerHeight cStar n ^ 2 / 2)) ^ 2) /
      (2 * (lowerCells n : ℝ))) := by
  let K := lowerCells n
  let a0 := actualStrength a n
  let μ1 := explicitSourceLaw a0 (fun _ => 0) (fun _ => 0)
  let μ2 := volume.restrict covariateSpace
  let Q1 : (Fin K → Bool) → Measure SourceObs := fun s =>
    explicitSourceLaw a0 (tiledPerturbation cStar n s)
      (fun x => τ * tiledPerturbation cStar n s x)
  let Q2 : (Fin K → Bool) → Measure ℝ := fun s =>
    μ2.withDensity
      (fun x => ENNReal.ofReal (1 + tiledPerturbation cStar n s x))
  let L1 : (Fin K → Bool) → SourceObs → ℝ := fun s =>
    sourceObsLikelihood a0 τ (tiledPerturbation cStar n s)
  let L2 : (Fin K → Bool) → ℝ → ℝ := fun s x =>
    1 + tiledPerturbation cStar n s x
  have hb := actualStrength_bounds a n hn ha
  have ha0 : 0 < a0 ∧ a0 < 1 := ⟨hb.1, lt_of_le_of_lt hb.2 (by norm_num)⟩
  have hAdm := lower_admissible_of_small_amplitude n a cStar hn ha hc
  have hn0 : 0 < n := by have : 256 ≤ n := hn; omega
  have hK : 0 < K := by
    unfold K lowerCells
    exact Nat.ceil_pos.mpr (by positivity)
  letI : NeZero K := ⟨Nat.ne_of_gt hK⟩
  letI : IsProbabilityMeasure μ1 := explicitCenterSourceLaw_isProbability a0 ha0
  letI : IsProbabilityMeasure μ2 := covariateCenter_isProbability
  letI : ∀ s, IsProbabilityMeasure (Q1 s) := fun s =>
    lowerExplicitSource_isProbability a n cStar τ s hb hAdm hτ
  letI : ∀ s, IsProbabilityMeasure (Q2 s) := fun s =>
    lowerTargetDensity_isProbability cStar n s hn0 hAdm
  have hL1 (s : Fin K → Bool) : Measurable (L1 s) :=
    sourceObsLikelihood_measurable a0 τ _
      (tiledPerturbation_measurable cStar n s)
  have hL2 (s : Fin K → Bool) : Measurable (L2 s) :=
    measurable_const.add (tiledPerturbation_measurable cStar n s)
  have hL10 (s : Fin K → Bool) (o : SourceObs) : 0 ≤ L1 s o :=
    lowerSourceLikelihood_nonneg a n cStar τ s hb hAdm hτ o
  have hL20 (s : Fin K → Bool) (x : ℝ) : 0 ≤ L2 s x := by
    have hu := tiledPerturbation_abs_le_lowerHeight cStar n s x hAdm.1.le
    have hu' : |tiledPerturbation cStar n s x| ≤ 3 / 16 := le_trans hu hAdm.2.1
    linarith [neg_abs_le (tiledPerturbation cStar n s x)]
  have hQ1 (s : Fin K → Bool) : Q1 s =
      μ1.withDensity (fun o => ENNReal.ofReal (L1 s o)) := by
    exact explicitSourceLaw_eq_withDensity a0 τ
      (tiledPerturbation cStar n s) ha0
      (tiledPerturbation_measurable cStar n s)
  have hQ2 (s : Fin K → Bool) : Q2 s =
      μ2.withDensity (fun x => ENNReal.ofReal (L2 s x)) := rfl
  have hInt1 (s t : Fin K → Bool) :
      Integrable (fun o => L1 s o * L1 t o) μ1 :=
    sourceLikelihood_pair_integrable a0 τ cStar n s t ha0
  have hInt2 (s t : Fin K → Bool) :
      Integrable (fun x => L2 s x * L2 t x) μ2 :=
    targetLikelihood_pair_integrable cStar n s t hn0
  have hPair1 (s t : Fin K → Bool) :
      (∫ o, L1 s o * L1 t o ∂μ1) =
        1 + (sourceOverlapCoefficient a0 τ * lowerHeight cStar n ^ 2 / 2) *
          Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign s t / (K : ℝ) :=
    sourceLikelihood_pair_integral a0 τ cStar n s t ha0
      (hL10 s) (hL10 t) hn0
  have hPair2 (s t : Fin K → Bool) :
      (∫ x, L2 s x * L2 t x ∂μ2) =
        1 + (lowerHeight cStar n ^ 2 / 2) *
          Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign s t / (K : ℝ) :=
    targetLikelihood_pair_integral cStar n s t hn0
  have hmain := Causalean.Stat.Minimax.Mixture.TwoChannel.one_add_chiSqDiv_uniformMixture_twoChannel_sign_le_exp
      K n n μ1 μ2 Q1 Q2 L1 L2 hL1 hL2 hL10 hL20 hQ1 hQ2
      hInt1 hInt2
      (sourceOverlapCoefficient a0 τ * lowerHeight cStar n ^ 2 / 2)
      (lowerHeight cStar n ^ 2 / 2) hPair1 hPair2
  rw [← lowerMixture_eq_uniformMixture a n cStar τ hb hAdm hτ hn0,
    ← center_dataLaw_eq_product a n hb] at hmain
  exact hmain

/-- The legal product mixture has an integrable squared likelihood deviation. Under [the displayed assumptions and inputs](hyp:a,n,cStar,hn,ha,hc,hτ), [the stated conclusion holds](goal). -/
-- @node: legal_mixture_finite_chiSquare_support
lemma legal_mixture_finite_chiSquare_support (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (hτ : τ ∈ Icc (-1 : ℝ) 1) (hn : threshold ≤ n)
    (ha : 0 < a ∧ a ≤ 1 / 4) (hc : 0 < cStar ∧ cStar ≤ 1 / 100) :
    (lowerMixture a n cStar τ) ≪ (dataLaw (mixtureCenter a n) n n) ∧
    Integrable (fun ω : TwoSample n n =>
      (((lowerMixture a n cStar τ).rnDeriv
        (dataLaw (mixtureCenter a n) n n) ω).toReal - 1) ^ 2)
      (dataLaw (mixtureCenter a n) n n) := by
  let K := lowerCells n
  let a0 := actualStrength a n
  let μ1 := explicitSourceLaw a0 (fun _ => 0) (fun _ => 0)
  let μ2 := volume.restrict covariateSpace
  let Q1 : (Fin K → Bool) → Measure SourceObs := fun s =>
    explicitSourceLaw a0 (tiledPerturbation cStar n s)
      (fun x => τ * tiledPerturbation cStar n s x)
  let Q2 : (Fin K → Bool) → Measure ℝ := fun s =>
    μ2.withDensity
      (fun x => ENNReal.ofReal (1 + tiledPerturbation cStar n s x))
  let L1 : (Fin K → Bool) → SourceObs → ℝ := fun s =>
    sourceObsLikelihood a0 τ (tiledPerturbation cStar n s)
  let L2 : (Fin K → Bool) → ℝ → ℝ := fun s x =>
    1 + tiledPerturbation cStar n s x
  let Q : (Fin K → Bool) → Measure (TwoSample n n) := fun s =>
    (Measure.pi (fun _ : Fin n => Q1 s)).prod
      (Measure.pi (fun _ : Fin n => Q2 s))
  let P : Measure (TwoSample n n) :=
    (Measure.pi (fun _ : Fin n => μ1)).prod
      (Measure.pi (fun _ : Fin n => μ2))
  have hb := actualStrength_bounds a n hn ha
  have ha0 : 0 < a0 ∧ a0 < 1 := ⟨hb.1, lt_of_le_of_lt hb.2 (by norm_num)⟩
  have hAdm := lower_admissible_of_small_amplitude n a cStar hn ha hc
  have hn0 : 0 < n := by have : 256 ≤ n := hn; omega
  have hK : 0 < K := by
    unfold K lowerCells
    exact Nat.ceil_pos.mpr (by positivity)
  letI : NeZero K := ⟨Nat.ne_of_gt hK⟩
  letI : IsProbabilityMeasure μ1 := explicitCenterSourceLaw_isProbability a0 ha0
  letI : IsProbabilityMeasure μ2 := covariateCenter_isProbability
  letI : ∀ s, IsProbabilityMeasure (Q1 s) := fun s =>
    lowerExplicitSource_isProbability a n cStar τ s hb hAdm hτ
  letI : ∀ s, IsProbabilityMeasure (Q2 s) := fun s =>
    lowerTargetDensity_isProbability cStar n s hn0 hAdm
  letI : IsProbabilityMeasure P := by unfold P; infer_instance
  letI : ∀ s, IsProbabilityMeasure (Q s) := fun s => by unfold Q; infer_instance
  have hL1 (s : Fin K → Bool) : Measurable (L1 s) :=
    sourceObsLikelihood_measurable a0 τ _
      (tiledPerturbation_measurable cStar n s)
  have hL2 (s : Fin K → Bool) : Measurable (L2 s) :=
    measurable_const.add (tiledPerturbation_measurable cStar n s)
  have hL10 (s : Fin K → Bool) (o : SourceObs) : 0 ≤ L1 s o :=
    lowerSourceLikelihood_nonneg a n cStar τ s hb hAdm hτ o
  have hL20 (s : Fin K → Bool) (x : ℝ) : 0 ≤ L2 s x := by
    have hu := tiledPerturbation_abs_le_lowerHeight cStar n s x hAdm.1.le
    have hu' : |tiledPerturbation cStar n s x| ≤ 3 / 16 := le_trans hu hAdm.2.1
    linarith [neg_abs_le (tiledPerturbation cStar n s x)]
  have hQ1 (s : Fin K → Bool) : Q1 s =
      μ1.withDensity (fun o => ENNReal.ofReal (L1 s o)) :=
    explicitSourceLaw_eq_withDensity a0 τ _ ha0
      (tiledPerturbation_measurable cStar n s)
  have hQ2 (s : Fin K → Bool) : Q2 s =
      μ2.withDensity (fun x => ENNReal.ofReal (L2 s x)) := rfl
  have hInt1 (s t : Fin K → Bool) :
      Integrable (fun o => L1 s o * L1 t o) μ1 :=
    sourceLikelihood_pair_integrable a0 τ cStar n s t ha0
  have hInt2 (s t : Fin K → Bool) :
      Integrable (fun x => L2 s x * L2 t x) μ2 :=
    targetLikelihood_pair_integrable cStar n s t hn0
  have hac (s : Fin K → Bool) : Q s ≪ P := by
    unfold Q P
    exact (Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
      μ1 (Q1 s) (L1 s) (hQ1 s) n).prod
      (Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
        μ2 (Q2 s) (L2 s) (hQ2 s) n)
  have hpair (s t : Fin K → Bool) : Integrable
      (fun x => ((Q s).rnDeriv P x).toReal *
        ((Q t).rnDeriv P x).toReal) P := by
    unfold Q P
    apply Causalean.Stat.Minimax.Mixture.product_pair_integrable
    · exact Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
        μ1 (Q1 s) (L1 s) (hQ1 s) n
    · exact Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
        μ1 (Q1 t) (L1 t) (hQ1 t) n
    · exact Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
        μ2 (Q2 s) (L2 s) (hQ2 s) n
    · exact Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
        μ2 (Q2 t) (L2 t) (hQ2 t) n
    · exact Causalean.Stat.Minimax.Mixture.iid_pair_integrable_of_likelihood
        μ1 (Q1 s) (Q1 t) (L1 s) (L1 t) (hL1 s) (hL1 t)
        (hL10 s) (hL10 t) (hQ1 s) (hQ1 t) (hInt1 s t) n
    · exact Causalean.Stat.Minimax.Mixture.iid_pair_integrable_of_likelihood
        μ2 (Q2 s) (Q2 t) (L2 s) (L2 t) (hL2 s) (hL2 t)
        (hL20 s) (hL20 t) (hQ2 s) (hQ2 t) (hInt2 s t) n
  have h := uniformMixture_finite_chiSquare Q P hac hpair
  rw [← lowerMixture_eq_uniformMixture a n cStar τ hb hAdm hτ hn0] at h
  dsimp [P, μ1, μ2, a0] at h
  rw [← center_dataLaw_eq_product a n hb] at h
  exact h
/-- Given [the supplied inputs](hyp:a,n,cStar,hn,ha,hc,hτ), [the stated result about legal tv le half sqrt chi holds](goal). -/

lemma legal_tv_le_half_sqrt_chi (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (hτ : τ ∈ Icc (-1 : ℝ) 1) (hn : threshold ≤ n)
    (ha : 0 < a ∧ a ≤ 1 / 4) (hc : 0 < cStar ∧ cStar ≤ 1 / 100) :
    Causalean.Stat.tvDist
      (lowerMixture a n cStar τ)
      (dataLaw (mixtureCenter a n) n n) ≤
      (1 / 2) * Real.sqrt (Causalean.Stat.chiSqDiv
        (lowerMixture a n cStar τ)
        (dataLaw (mixtureCenter a n) n n)) := by
  let K := lowerCells n
  let a0 := actualStrength a n
  let μ1 := explicitSourceLaw a0 (fun _ => 0) (fun _ => 0)
  let μ2 := volume.restrict covariateSpace
  let Q1 : (Fin K → Bool) → Measure SourceObs := fun s =>
    explicitSourceLaw a0 (tiledPerturbation cStar n s)
      (fun x => τ * tiledPerturbation cStar n s x)
  let Q2 : (Fin K → Bool) → Measure ℝ := fun s =>
    μ2.withDensity
      (fun x => ENNReal.ofReal (1 + tiledPerturbation cStar n s x))
  let L1 : (Fin K → Bool) → SourceObs → ℝ := fun s =>
    sourceObsLikelihood a0 τ (tiledPerturbation cStar n s)
  let L2 : (Fin K → Bool) → ℝ → ℝ := fun s x =>
    1 + tiledPerturbation cStar n s x
  let Q : (Fin K → Bool) → Measure (TwoSample n n) := fun s =>
    (Measure.pi (fun _ : Fin n => Q1 s)).prod
      (Measure.pi (fun _ : Fin n => Q2 s))
  let P : Measure (TwoSample n n) :=
    (Measure.pi (fun _ : Fin n => μ1)).prod
      (Measure.pi (fun _ : Fin n => μ2))
  have hb := actualStrength_bounds a n hn ha
  have ha0 : 0 < a0 ∧ a0 < 1 := ⟨hb.1, lt_of_le_of_lt hb.2 (by norm_num)⟩
  have hAdm := lower_admissible_of_small_amplitude n a cStar hn ha hc
  have hn0 : 0 < n := by have : 256 ≤ n := hn; omega
  have hK : 0 < K := by
    unfold K lowerCells
    exact Nat.ceil_pos.mpr (by positivity)
  letI : NeZero K := ⟨Nat.ne_of_gt hK⟩
  letI : IsProbabilityMeasure μ1 := explicitCenterSourceLaw_isProbability a0 ha0
  letI : IsProbabilityMeasure μ2 := covariateCenter_isProbability
  letI : ∀ s, IsProbabilityMeasure (Q1 s) := fun s =>
    lowerExplicitSource_isProbability a n cStar τ s hb hAdm hτ
  letI : ∀ s, IsProbabilityMeasure (Q2 s) := fun s =>
    lowerTargetDensity_isProbability cStar n s hn0 hAdm
  letI : IsProbabilityMeasure P := by unfold P; infer_instance
  letI : ∀ s, IsProbabilityMeasure (Q s) := fun s => by unfold Q; infer_instance
  have hL1 (s : Fin K → Bool) : Measurable (L1 s) :=
    sourceObsLikelihood_measurable a0 τ _
      (tiledPerturbation_measurable cStar n s)
  have hL2 (s : Fin K → Bool) : Measurable (L2 s) :=
    measurable_const.add (tiledPerturbation_measurable cStar n s)
  have hL10 (s : Fin K → Bool) (o : SourceObs) : 0 ≤ L1 s o :=
    lowerSourceLikelihood_nonneg a n cStar τ s hb hAdm hτ o
  have hL20 (s : Fin K → Bool) (x : ℝ) : 0 ≤ L2 s x := by
    have hu := tiledPerturbation_abs_le_lowerHeight cStar n s x hAdm.1.le
    have hu' : |tiledPerturbation cStar n s x| ≤ 3 / 16 := le_trans hu hAdm.2.1
    linarith [neg_abs_le (tiledPerturbation cStar n s x)]
  have hQ1 (s : Fin K → Bool) : Q1 s =
      μ1.withDensity (fun o => ENNReal.ofReal (L1 s o)) :=
    explicitSourceLaw_eq_withDensity a0 τ _ ha0
      (tiledPerturbation_measurable cStar n s)
  have hQ2 (s : Fin K → Bool) : Q2 s =
      μ2.withDensity (fun x => ENNReal.ofReal (L2 s x)) := rfl
  have hInt1 (s t : Fin K → Bool) :
      Integrable (fun o => L1 s o * L1 t o) μ1 :=
    sourceLikelihood_pair_integrable a0 τ cStar n s t ha0
  have hInt2 (s t : Fin K → Bool) :
      Integrable (fun x => L2 s x * L2 t x) μ2 :=
    targetLikelihood_pair_integrable cStar n s t hn0
  have hac (s : Fin K → Bool) : Q s ≪ P := by
    unfold Q P
    exact (Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
      μ1 (Q1 s) (L1 s) (hQ1 s) n).prod
      (Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
        μ2 (Q2 s) (L2 s) (hQ2 s) n)
  have hpair (s t : Fin K → Bool) : Integrable
      (fun x => ((Q s).rnDeriv P x).toReal *
        ((Q t).rnDeriv P x).toReal) P := by
    unfold Q P
    apply Causalean.Stat.Minimax.Mixture.product_pair_integrable
    · exact Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
        μ1 (Q1 s) (L1 s) (hQ1 s) n
    · exact Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
        μ1 (Q1 t) (L1 t) (hQ1 t) n
    · exact Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
        μ2 (Q2 s) (L2 s) (hQ2 s) n
    · exact Causalean.Stat.Minimax.Mixture.iid_absolutelyContinuous_of_likelihood
        μ2 (Q2 t) (L2 t) (hQ2 t) n
    · exact Causalean.Stat.Minimax.Mixture.iid_pair_integrable_of_likelihood
        μ1 (Q1 s) (Q1 t) (L1 s) (L1 t) (hL1 s) (hL1 t)
        (hL10 s) (hL10 t) (hQ1 s) (hQ1 t) (hInt1 s t) n
    · exact Causalean.Stat.Minimax.Mixture.iid_pair_integrable_of_likelihood
        μ2 (Q2 s) (Q2 t) (L2 s) (L2 t) (hL2 s) (hL2 t)
        (hL20 s) (hL20 t) (hQ2 s) (hQ2 t) (hInt2 s t) n
  have h := tv_uniformMixture_le_half_sqrt Q P hac hpair
  change Causalean.Stat.tvDist
      (Causalean.Stat.Minimax.Mixture.uniformMixture Q) P ≤ _ at h
  rw [← lowerMixture_eq_uniformMixture a n cStar τ hb hAdm hτ hn0] at h
  dsimp [P, μ1, μ2, a0] at h
  rw [← center_dataLaw_eq_product a n hb] at h
  exact h
/-- Given [the supplied inputs](hyp:a,n,cStar,hn,ha,hc,hτ), [the stated result about legal chi exp bound holds](goal). -/

lemma legal_chi_exp_bound (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (hτ : τ ∈ Icc (-1 : ℝ) 1) (hn : threshold ≤ n)
    (ha : 0 < a ∧ a ≤ 1 / 4) (hc : 0 < cStar ∧ cStar ≤ 1 / 100) :
    1 + Causalean.Stat.chiSqDiv
      (lowerMixture a n cStar τ)
      (dataLaw (mixtureCenter a n) n n) ≤
        Real.exp (mixConstant * cStar ^ 4) := by
  have hraw := legal_twoChannel_exp_bound a n cStar τ hτ hn ha hc
  apply hraw.trans
  apply Real.exp_le_exp.mpr
  have hb := actualStrength_bounds a n hn ha
  have hG := sourceOverlapCoefficient_le (actualStrength a n) τ
    ⟨hb.1.le, hb.2⟩ hτ
  have hn0 : 0 < n := by have : 256 ≤ n := hn; omega
  have hK : 0 < lowerCells n := by
    unfold lowerCells
    exact Nat.ceil_pos.mpr (by positivity)
  have hbase : (n : ℝ) ^ ((4 : ℝ) / 3) ≤ lowerCells n := by
    unfold lowerCells
    exact Nat.le_ceil _
  have hscale := sample_height_exponent_bound n (lowerCells n) cStar
    (sourceOverlapCoefficient (actualStrength a n) τ + 1)
    hn0 hK hbase (by linarith [hG.1]) hG.2
  have heq :
      (((n : ℝ) *
            (sourceOverlapCoefficient (actualStrength a n) τ *
              lowerHeight cStar n ^ 2 / 2) +
          (n : ℝ) * (lowerHeight cStar n ^ 2 / 2)) ^ 2) /
        (2 * (lowerCells n : ℝ)) =
      (((n : ℝ) *
          ((sourceOverlapCoefficient (actualStrength a n) τ + 1) *
            (cStar * (lowerCells n : ℝ) ^ (-(1 / 8 : ℝ))) ^ 2 / 2)) ^ 2) /
        (2 * (lowerCells n : ℝ)) := by
    unfold lowerHeight
    ring
  rw [heq]
  exact hscale

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
