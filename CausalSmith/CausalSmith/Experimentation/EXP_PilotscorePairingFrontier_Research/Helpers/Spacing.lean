module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic
public import Causalean.Stat.OrderStatistic.Comparison

/-! # Uniform spacing and score quantiles -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

variable {d m N : ℕ} {β L cX CX cg Cg h c0 c1 C1 C2 : ℝ}

open MeasureTheory

private lemma pairLoss_adjSort_eq_alternating_gaps (hN : Even N) (hN2 : 2 ≤ N)
    (s : Fin N → ℝ) :
    (1 / 2 : ℝ) * ∑ i : Fin N, (s i - s ((adjSortMatching s hN hN2).val i)) ^ 2 =
      ∑ j ∈ Finset.range (N / 2),
        (Causalean.Stat.OrderStatistic.sortedGap N (2 * j) s) ^ 2 := by
  classical
  let M := adjSortMatching s hN hN2
  obtain ⟨π, hπ, hpair⟩ :=
    (Classical.choose_spec (exists_adjSortMatching s hN hN2) : AdjSortSpec s M)
  have hmono : Monotone (s ∘ π) := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact (hπ i j hij).elim le_of_lt (fun h => h.1.le)
  have hsorted : s ∘ π = Causalean.Stat.OrderStatistic.sortedSample N s :=
    (Tuple.comp_sort_eq_comp_iff_monotone (f := s) (σ := π)).2 hmono
  obtain ⟨k, hk⟩ := hN
  subst N
  have hlo (j : Fin k) : (2 * j.val : ℕ) < k + k := by omega
  have hhi (j : Fin k) : 2 * j.val + 1 < k + k := by omega
  let lo (j : Fin k) : Fin (k + k) := ⟨2 * j.val, hlo j⟩
  let hi (j : Fin k) : Fin (k + k) := ⟨2 * j.val + 1, hhi j⟩
  let e : Fin k × Fin 2 ≃ Fin (k + k) :=
    (finProdFinEquiv (m := k) (n := 2)).trans
      (Fin.castOrderIso (show k * 2 = k + k by omega)).toEquiv
  have hMlo (j : Fin k) : M.val (π (lo j)) = π (hi j) := by
    apply hpair
    · simp [lo, hi]
    · change Even (2 * j.val)
      exact ⟨j.val, by omega⟩
  have hMhi (j : Fin k) : M.val (π (hi j)) = π (lo j) := by
    rw [← hMlo j]
    exact M.property.1 (π (lo j))
  have hsum :
      (∑ i : Fin (k + k), (s i - s (M.val i)) ^ 2) =
        2 * ∑ j : Fin k, (s (π (hi j)) - s (π (lo j))) ^ 2 := by
    rw [← Equiv.sum_comp π]
    rw [← Equiv.sum_comp e]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he0 : e (j, (0 : Fin 2)) = lo j := by
      apply Fin.ext
      simp [e, lo]
    have he1 : e (j, (1 : Fin 2)) = hi j := by
      apply Fin.ext
      simp [e, hi]
      omega
    rw [he0, he1]
    rw [hMlo, hMhi]
    ring
  rw [hsum]
  have hgap (j : Fin k) :
      Causalean.Stat.OrderStatistic.sortedGap (k + k) (2 * j.val) s =
        s (π (hi j)) - s (π (lo j)) := by
    rw [Causalean.Stat.OrderStatistic.sortedGap, dif_pos (hhi j)]
    change (Causalean.Stat.OrderStatistic.sortedSample (k + k) s) (hi j) -
        (Causalean.Stat.OrderStatistic.sortedSample (k + k) s) (lo j) = _
    rw [← hsorted]
    rfl
  rw [show (k + k) / 2 = k by omega]
  rw [show (∑ j ∈ Finset.range k,
      (Causalean.Stat.OrderStatistic.sortedGap (k + k) (2 * j) s) ^ 2) =
      ∑ j : Fin k, (Causalean.Stat.OrderStatistic.sortedGap (k + k) (2 * j.val) s) ^ 2 by
        exact (Fin.sum_univ_eq_sum_range _ k).symm]
  simp_rw [hgap]
  ring

lemma score_oracle_spacing_bound (hN : Even N) (hN2 : 2 ≤ N)
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (hpars : ValidClassParameters d β L cX CX cg Cg)
    (hmodel : RegularScoreModel P g L β cX CX cg Cg) :
    1 / (Cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤
      oracleLoss P g N (fun x => oracleMatching g x hN hN2) ∧
    oracleLoss P g N (fun x => oracleMatching g x hN hN2) ≤
      1 / (cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
  classical
  let q : UnitRecord d → ℝ := fun u => g u.1
  let ν : Measure ℝ := P.map q
  let ρ : Measure ℝ := (volume : Measure ℝ).restrict scoreInterval
  have hP : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure P := hP
  have hreg : ν ≪ ρ ∧
      ∀ᵐ t ∂ρ, cg ≤ (ν.rnDeriv ρ t).toReal ∧ (ν.rnDeriv ρ t).toReal ≤ Cg := by
    simpa [RegularScoreModel, RegularScorePushforward, ν, ρ, q] using
      hmodel.regular_score_pushforward
  rcases hpars with ⟨_, _, _, _, _, _, _, hcg, hcg2, hCg0⟩
  have hCg : cg ≤ Cg := (hcg2.trans hCg0).le
  have hρne : ρ ≠ 0 := by
    intro hz
    have hz' := congrArg (fun μ : Measure ℝ => μ scoreInterval) hz
    norm_num [ρ, scoreInterval, Real.volume_Icc] at hz'
  have hνne : ν ≠ 0 := by
    intro hz
    have hb := hreg.2
    rw [hz] at hb
    have hf : ∀ᵐ _t ∂ρ, False := by
      filter_upwards [hb, Measure.rnDeriv_zero ρ] with t ht ht0
      have : cg ≤ 0 := by simpa [ht0] using ht.1
      linarith
    letI : (ae ρ).NeBot := (ae_neBot.mpr hρne)
    exact (Filter.Eventually.exists hf).choose_spec
  have hq : AEMeasurable q P := AEMeasurable.of_map_ne_zero hνne
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hq
  let p : ℝ → ℝ := scoreInterval.indicator (fun t => (ν.rnDeriv ρ t).toReal)
  have hμ : ν = volume.withDensity (fun t => ENNReal.ofReal (p t)) := by
    calc
      ν = ρ.withDensity (ν.rnDeriv ρ) :=
        (Measure.withDensity_rnDeriv_eq ν ρ hreg.1).symm
      _ = ρ.withDensity (fun t => ENNReal.ofReal (ν.rnDeriv ρ t).toReal) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_ne_top ν ρ] with t ht
        exact (ENNReal.ofReal_toReal ht).symm
      _ = volume.withDensity (fun t => ENNReal.ofReal (p t)) := by
        dsimp [ρ]
        rw [← withDensity_indicator
          (show MeasurableSet scoreInterval by exact measurableSet_Icc)]
        congr 1
        funext t
        by_cases ht : t ∈ scoreInterval <;> simp [p, ρ, ht]
  have hsupp : ν scoreIntervalᶜ = 0 := by
    apply hreg.1
    simp [ρ, scoreInterval]
  have hbound : ∀ᵐ t ∂(volume.restrict scoreInterval), cg ≤ p t ∧ p t ≤ Cg := by
    filter_upwards [hreg.2, ae_restrict_mem measurableSet_Icc] with t ht hmem
    simpa [p, hmem] using ht
  have hcomparison :=
    Causalean.Stat.OrderStatistic.real_alternating_gap_second_moment_bounds
      ν (1 / 4 : ℝ) (3 / 4 : ℝ) cg Cg p hcg hCg hμ
      (by simpa [scoreInterval] using hsupp)
      (by simpa [scoreInterval] using hbound) N hN
  let F : (Fin N → UnitRecord d) → (Fin N → ℝ) := fun us i => q (us i)
  let H : (Fin N → ℝ) → ℝ := fun s =>
    ∑ j ∈ Finset.range (N / 2),
      (Causalean.Stat.OrderStatistic.sortedGap N (2 * j) s) ^ 2
  have hindex (j : ℕ) (hj : j ∈ Finset.range (N / 2)) : 2 * j + 1 < N := by
    obtain ⟨k, hk⟩ := hN
    simp only [Finset.mem_range] at hj
    omega
  have hHint : Integrable H (Causalean.Stat.OrderStatistic.iidSample ν N) := by
    apply integrable_finsetSum
    intro j hj
    exact Causalean.Stat.OrderStatistic.sortedGap_square_integrable_of_interval_support
      ν (1 / 4 : ℝ) (3 / 4 : ℝ) (by simpa [scoreInterval] using hsupp)
      N (2 * j) (hindex j hj)
  have hF : AEMeasurable F (Measure.pi fun _ : Fin N => P) := by
    exact aemeasurable_pi_lambda _ fun i =>
      hq.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun _ : Fin N => P) i)
  have hmap : (Measure.pi fun _ : Fin N => P).map F =
      Causalean.Stat.OrderStatistic.iidSample ν N := by
    rw [Measure.pi_map_pi (fun _ : Fin N => hq)]
    rfl
  have horacle : oracleLoss P g N (fun x => oracleMatching g x hN hN2) =
      (1 / (N : ℝ)) * ∫ s, H s ∂Causalean.Stat.OrderStatistic.iidSample ν N := by
    unfold oracleLoss
    rw [← hmap]
    have hHint' := hHint
    rw [← hmap] at hHint'
    rw [integral_map hF hHint'.aestronglyMeasurable]
    simp only [F, H, q, oracleMatching]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with us
    unfold pairLoss
    rw [pairLoss_adjSort_eq_alternating_gaps hN hN2 (fun i => g (us i).1)]
    ring
  rw [horacle]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  constructor
  · calc
      1 / (Cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) =
          (1 / (N : ℝ)) * ((1 / Cg ^ 2) *
            ((N : ℝ) / ((N + 1 : ℕ) * (N + 2 : ℕ)))) := by
              field_simp
              <;> norm_num [Nat.cast_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcomparison.1 (by positivity)
  · calc
      _ ≤ (1 / (N : ℝ)) * ((1 / cg ^ 2) *
          ((N : ℝ) / ((N + 1 : ℕ) * (N + 2 : ℕ)))) :=
        mul_le_mul_of_nonneg_left hcomparison.2 (by positivity)
      _ = 1 / (cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
        field_simp
        <;> norm_num [Nat.cast_add]

/-- In one covariate dimension, adjacent pairing by the covariate itself has the
same sharp spacing bound as an oracle score whose density is bounded. -/
lemma coordinate_oracle_spacing_bound_one_dim (hN : Even N) (hN2 : 2 ≤ N)
    (P : Measure (UnitRecord 1)) (hcov : CovariateDensity P cX CX)
    (hcX : 0 < cX) (hCX : cX ≤ CX) :
    1 / (CX ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤
      oracleLoss P (fun x : XSpace 1 => x 0) N
        (fun x => oracleMatching (fun z : XSpace 1 => z 0) x hN hN2) ∧
    oracleLoss P (fun x : XSpace 1 => x 0) N
        (fun x => oracleMatching (fun z : XSpace 1 => z 0) x hN hN2) ≤
      1 / (cX ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
  classical
  let μX : Measure (XSpace 1) := P.map Prod.fst
  let ρ : Measure (XSpace 1) := cubeMeasure 1
  let e : XSpace 1 ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  let ν : Measure ℝ := μX.map e
  letI : IsProbabilityMeasure P := hcov.1
  letI : IsProbabilityMeasure μX := by
    dsimp [μX]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have heρ : MeasurePreserving e ρ (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hc : e ⁻¹' Set.Icc (0 : ℝ) 1 = cube 1 := by
      ext x
      simp [cube, e]
    dsimp [ρ, cubeMeasure]
    rw [← hc]
    exact (measurePreserving_funUnique (volume : Measure ℝ) (Fin 1)).restrict_preimage
      measurableSet_Icc
  have hνprob : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  letI : IsProbabilityMeasure ν := hνprob
  letI : SigmaFinite ρ := by
    dsimp [ρ, cubeMeasure]
    infer_instance
  have hνρ : ν ≪ volume.restrict (Set.Icc (0 : ℝ) 1) := by
    rw [← heρ.map_eq]
    exact e.measurableEmbedding.absolutelyContinuous_map hcov.2.1
  have hrn :
      (fun x => (ν.rnDeriv (volume.restrict (Set.Icc (0 : ℝ) 1)) (e x)).toReal) =ᵐ[ρ]
        fun x => (μX.rnDeriv ρ x).toReal := by
    have h := e.measurableEmbedding.rnDeriv_map μX ρ
    rw [heρ.map_eq] at h
    exact h.fun_comp ENNReal.toReal
  have hboundν : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      cX ≤ (ν.rnDeriv (volume.restrict (Set.Icc (0 : ℝ) 1)) t).toReal ∧
        (ν.rnDeriv (volume.restrict (Set.Icc (0 : ℝ) 1)) t).toReal ≤ CX := by
    rw [← heρ.map_eq, e.measurableEmbedding.ae_map_iff]
    filter_upwards [hcov.2.2, hrn] with x hx hrnx
    rw [heρ.map_eq, hrnx]
    simpa [μX, ρ] using hx
  let p : ℝ → ℝ := (Set.Icc (0 : ℝ) 1).indicator
    (fun t => (ν.rnDeriv (volume.restrict (Set.Icc (0 : ℝ) 1)) t).toReal)
  have hν : ν = volume.withDensity (fun t => ENNReal.ofReal (p t)) := by
    calc
      ν = (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
          (ν.rnDeriv (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
        (Measure.withDensity_rnDeriv_eq ν _ hνρ).symm
      _ = (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
          (fun t => ENNReal.ofReal
            (ν.rnDeriv (volume.restrict (Set.Icc (0 : ℝ) 1)) t).toReal) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_ne_top ν
          (volume.restrict (Set.Icc (0 : ℝ) 1))] with t ht
        exact (ENNReal.ofReal_toReal ht).symm
      _ = volume.withDensity (fun t => ENNReal.ofReal (p t)) := by
        rw [← withDensity_indicator measurableSet_Icc]
        congr 1
        funext t
        by_cases ht : t ∈ Set.Icc (0 : ℝ) 1 <;> simp [p, ht]
  have hsupp : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    apply hνρ
    simp
  have hbound : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      cX ≤ p t ∧ p t ≤ CX := by
    filter_upwards [hboundν, ae_restrict_mem measurableSet_Icc] with t ht hmem
    simpa [p, hmem] using ht
  have hcomparison :=
    Causalean.Stat.OrderStatistic.real_alternating_gap_second_moment_bounds
      ν 0 1 cX CX p hcX hCX hν hsupp hbound N hN
  let q : UnitRecord 1 → ℝ := fun u => u.1 0
  let F : (Fin N → UnitRecord 1) → (Fin N → ℝ) := fun us i => q (us i)
  let H : (Fin N → ℝ) → ℝ := fun s =>
    ∑ j ∈ Finset.range (N / 2),
      (Causalean.Stat.OrderStatistic.sortedGap N (2 * j) s) ^ 2
  have hindex (j : ℕ) (hj : j ∈ Finset.range (N / 2)) : 2 * j + 1 < N := by
    obtain ⟨k, hk⟩ := hN
    simp only [Finset.mem_range] at hj
    omega
  have hHint : Integrable H (Causalean.Stat.OrderStatistic.iidSample ν N) := by
    apply integrable_finsetSum
    intro j hj
    exact Causalean.Stat.OrderStatistic.sortedGap_square_integrable_of_interval_support
      ν 0 1 hsupp N (2 * j) (hindex j hj)
  have hq : AEMeasurable q P := by
    exact (e.measurable.comp measurable_fst).aemeasurable
  have hνmap : P.map q = ν := by
    symm
    calc
      ν = μX.map e := rfl
      _ = P.map (e ∘ Prod.fst) := by
        dsimp [μX]
        exact Measure.map_map e.measurable measurable_fst
      _ = P.map q := by rfl
  have hF : AEMeasurable F (Measure.pi fun _ : Fin N => P) := by
    exact aemeasurable_pi_lambda _ fun i =>
      hq.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun _ : Fin N => P) i)
  have hmap : (Measure.pi fun _ : Fin N => P).map F =
      Causalean.Stat.OrderStatistic.iidSample ν N := by
    rw [Measure.pi_map_pi (fun _ : Fin N => hq)]
    simp [Causalean.Stat.OrderStatistic.iidSample, hνmap]
  have horacle :
      oracleLoss P (fun x : XSpace 1 => x 0) N
          (fun x => oracleMatching (fun z : XSpace 1 => z 0) x hN hN2) =
        (1 / (N : ℝ)) *
          ∫ s, H s ∂Causalean.Stat.OrderStatistic.iidSample ν N := by
    unfold oracleLoss
    rw [← hmap]
    have hHint' := hHint
    rw [← hmap] at hHint'
    rw [integral_map hF hHint'.aestronglyMeasurable]
    simp only [F, H, q, oracleMatching]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with us
    unfold pairLoss
    rw [pairLoss_adjSort_eq_alternating_gaps hN hN2 (fun i => (us i).1 0)]
    ring
  rw [horacle]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  constructor
  · calc
      1 / (CX ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) =
          (1 / (N : ℝ)) * ((1 / CX ^ 2) *
            ((N : ℝ) / ((N + 1 : ℕ) * (N + 2 : ℕ)))) := by
              field_simp
              <;> norm_num [Nat.cast_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcomparison.1 (by positivity)
  · calc
      _ ≤ (1 / (N : ℝ)) * ((1 / cX ^ 2) *
          ((N : ℝ) / ((N + 1 : ℕ) * (N + 2 : ℕ)))) :=
        mul_le_mul_of_nonneg_left hcomparison.2 (by positivity)
      _ = 1 / (cX ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
        field_simp
        <;> norm_num [Nat.cast_add]

/-- The adjacent-coordinate loss is integrable under a one-dimensional iid
main sample. -/
lemma integrable_coordinate_oracle_loss_one_dim (hN : Even N) (hN2 : 2 ≤ N)
    (P : Measure (UnitRecord 1)) (hcov : CovariateDensity P cX CX) :
    Integrable (fun us : Fin N → UnitRecord 1 =>
      pairLoss (fun x : XSpace 1 => x 0) (fun i => (us i).1)
        (oracleMatching (fun x : XSpace 1 => x 0) (fun i => (us i).1) hN hN2) /
          (N : ℝ))
      (Measure.pi fun _ : Fin N => P) := by
  classical
  let q : UnitRecord 1 → ℝ := fun u => u.1 0
  let ν : Measure ℝ := P.map q
  let F : (Fin N → UnitRecord 1) → (Fin N → ℝ) := fun us i => q (us i)
  let H : (Fin N → ℝ) → ℝ := fun s =>
    ∑ j ∈ Finset.range (N / 2),
      (Causalean.Stat.OrderStatistic.sortedGap N (2 * j) s) ^ 2
  letI : IsProbabilityMeasure P := hcov.1
  have hq : AEMeasurable q P := by
    exact ((measurable_pi_apply (0 : Fin 1)).comp measurable_fst).aemeasurable
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hq
  have hcube_meas : MeasurableSet (cube 1) := by
    unfold cube
    measurability
  have hcube : ∀ᵐ x ∂P.map Prod.fst, x ∈ cube 1 := by
    change cube 1 ∈ ae (P.map Prod.fst)
    rw [mem_ae_iff]
    apply hcov.2.1
    simp [cubeMeasure, hcube_meas]
  have hqmem : ∀ᵐ u ∂P, q u ∈ Set.Icc (0 : ℝ) 1 := by
    have hx := ae_of_ae_map measurable_fst.aemeasurable hcube
    filter_upwards [hx] with u hu
    simpa [q, cube] using hu (0 : Fin 1)
  have hsupp : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    rw [← mem_ae_iff]
    dsimp [ν]
    change ∀ᵐ t ∂P.map q, t ∈ Set.Icc (0 : ℝ) 1
    exact (ae_map_iff hq measurableSet_Icc).2 hqmem
  have hindex (j : ℕ) (hj : j ∈ Finset.range (N / 2)) : 2 * j + 1 < N := by
    obtain ⟨k, hk⟩ := hN
    simp only [Finset.mem_range] at hj
    omega
  have hHint : Integrable H (Causalean.Stat.OrderStatistic.iidSample ν N) := by
    apply integrable_finsetSum
    intro j hj
    exact Causalean.Stat.OrderStatistic.sortedGap_square_integrable_of_interval_support
      ν 0 1 hsupp N (2 * j) (hindex j hj)
  have hF : AEMeasurable F (Measure.pi fun _ : Fin N => P) := by
    exact aemeasurable_pi_lambda _ fun i =>
      hq.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun _ : Fin N => P) i)
  have hmap : (Measure.pi fun _ : Fin N => P).map F =
      Causalean.Stat.OrderStatistic.iidSample ν N := by
    rw [Measure.pi_map_pi (fun _ : Fin N => hq)]
    rfl
  have hback : Integrable (fun us => H (F us)) (Measure.pi fun _ : Fin N => P) := by
    have hHint' := hHint
    rw [← hmap] at hHint'
    exact hHint'.comp_aemeasurable hF
  have heq (us : Fin N → UnitRecord 1) :
      pairLoss (fun x : XSpace 1 => x 0) (fun i => (us i).1)
          (oracleMatching (fun x : XSpace 1 => x 0) (fun i => (us i).1) hN hN2) /
            (N : ℝ) =
        (1 / (N : ℝ)) * H (F us) := by
    unfold pairLoss
    simp only [oracleMatching]
    rw [pairLoss_adjSort_eq_alternating_gaps hN hN2 (fun i => (us i).1 0)]
    dsimp [H, F, q]
    ring
  exact (hback.const_mul (1 / (N : ℝ))).congr
    (Filter.Eventually.of_forall fun us => (heq us).symm)

end CausalSmith.Experimentation.PilotscorePairingFrontier
