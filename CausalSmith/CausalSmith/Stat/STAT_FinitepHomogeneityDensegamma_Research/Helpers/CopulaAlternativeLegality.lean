module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CopulaLegalityBasics
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PhaseAlgebra
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.SmoothedTentSmoothness

/-! Primitive model membership of the alternative copula tables. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- In the rough phase the sum of nuisance exponents is below the effect exponent. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: legality_rough_regularity
lemma legality_rough_regularity (v : Params) (hv : v.Valid) (hf : Fphase v < 1) :
    sumReg v < v.γ ∧ v.β ≤ v.γ := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, _, _⟩ := phase_denominators v hv
  have ha : v.α ≤ v.α/(v.p-1) := (le_div_iff₀ hm).mpr (by nlinarith [hv.1.2, hv.2.1.1])
  have hb : 2*v.β ≤ v.β/qExp v := (le_div_iff₀ hq).mpr (by nlinarith [hv.2.2.1.1])
  have ha2 : 2*v.α ≤ 2*v.α/(v.p-1) := by rw [mul_div_assoc]; linarith
  have hl : 2*sumReg v+sumReg v/(2*v.γ) ≤ Fphase v := by
    dsimp [Fphase, sumReg]
    linarith
  have hc : sumReg v < v.γ := by
    have hdiv := (div_le_iff₀ (by positivity : 0 < 2*v.γ)).mp
      (show sumReg v/(2*v.γ) ≤ Fphase v-2*sumReg v by linarith)
    by_contra h
    have hS := le_of_not_gt h
    have hgam := hv.2.2.2.1
    nlinarith
  exact ⟨hc, by dsimp [sumReg] at hc; linarith [hv.2.1.1]⟩

/-- Rank constraints cancel the amplitude powers needed by the effect and baseline Hölder bounds. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hr condition](hyp:hr). [This is the stated conclusion](goal). -/
-- @node: legality_alternative_power_bounds
lemma legality_alternative_power_bounds (v : Params) (hv : v.Valid) (hf : Fphase v < 1)
    (K M : ℕ) (hr : LegalityRanks v K M) :
    legalityA v K*legalityB v K*(M:ℝ)^v.γ ≤ 1/4096 ∧
    legalityA v K*legalityB v K*(M:ℝ)^v.β ≤ 1/4096 ∧
    legalityA v K^2*legalityB v K*(K:ℝ)^v.β ≤ 1/65536 := by
  have hK : 0 < K := by have := hr.2.2.1; have := hr.2.2.2.1; omega
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  have hm : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by have := hr.2.2.2.1; omega)
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have hab : legalityA v K*legalityB v K = (K:ℝ)^(-sumReg v)/4096 := by
    rw [legalityA, legalityB]
    rw [div_mul_div_comm, ← Real.rpow_add hk]
    congr 1
    · congr 1; dsimp [sumReg]; ring
    · norm_num
  have hpow : (M:ℝ)^v.γ ≤ (K:ℝ)^(sumReg v) := by
    have hb := Real.rpow_le_rpow (Nat.cast_nonneg M) hr.2.2.2.2 hg.le
    rw [← Real.rpow_mul hk.le, div_mul_cancel₀ _ hg.ne'] at hb
    exact hb
  have hγ : legalityA v K*legalityB v K*(M:ℝ)^v.γ ≤ 1/4096 := by
    rw [hab]
    calc
      _ ≤ ((K:ℝ)^(-sumReg v)/4096)*(K:ℝ)^(sumReg v) := by gcongr
      _ = _ := by rw [div_mul_eq_mul_div, ← Real.rpow_add hk, neg_add_cancel, Real.rpow_zero]
  have ha0 := (legality_tuning_bounds v hv K (by omega)).1.1.le
  have hb0 := (legality_tuning_bounds v hv K (by omega)).2.1.1.le
  refine ⟨hγ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hm (legality_rough_regularity v hv hf).2)
      (mul_nonneg ha0 hb0)).trans hγ
  · have ha := (legality_tuning_bounds v hv K (by omega)).1
    have hb := (legality_amplitude_power_identities v K hK).2
    calc
      _ = legalityA v K^2*(legalityB v K*(K:ℝ)^v.β) := by ring
      _ = legalityA v K^2/256 := by rw [hb]; ring
      _ ≤ (1/16:ℝ)^2/256 := by gcongr <;> linarith [ha.1, ha.2]
      _ = _ := by norm_num

/-- The alternative table baseline includes exactly the deterministic correction times one plus propensity coordinate. This statement assumes [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: copulaLaw_alternative_primitives
lemma copulaLaw_alternative_primitives (v : Params) (K M : ℕ) (a u ε L : ℝ)
    (hd : CopulaDomain 2 K M a u ε L) (idx : CopulaIndex K M) (x : unitInterval) :
    (copulaLaw true v K M a u ε L idx).e x = (1+copulaXi K M a idx x)/2 ∧
    (copulaLaw true v K M a u ε L idx).m0 x =
      ε*L*u*frameField K (fun i => signVal (idx.2 i).2) x +
      (a*(ε*L*u)*kappa0/(1-a^2))*smoothedTent K M idx.1 x*(1+copulaXi K M a idx x) ∧
    (copulaLaw true v K M a u ε L idx).tau x =
      -(2*a*(ε*L*u)*kappa0/(1-a^2))*smoothedTent K M idx.1 x := by
  have ht := copula_table_valid 2 K M a u ε L hd true idx
  have hx := abs_lt.mp (ht.2.2.2.1 x)
  have hden : 1-copulaXi K M a idx x ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [copulaLaw, tableObservedLaw, dif_pos ht, ContinuousMap.coe_mk, tableProp]
  · simp only [copulaLaw, tableObservedLaw, dif_pos ht, ContinuousMap.coe_mk, tableM0,
      copulaZeta, copulaT, if_true, copulaUpsilon]
    field_simp
    ring
  · rw [copulaLaw_tau_formula v 2 K M a u ε L hd true idx x]
    simp only [copulaT, if_true]
    ring

/-- Under either public mark tuning, every alternative support law satisfies the original model predicates. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hr condition](hyp:hr), [the hd condition](hyp:hd), [the hmean condition](hyp:hmean), [the hmoment condition](hyp:hmoment). [This is the stated conclusion](goal). -/
-- @node: legality_alternative_inModel
lemma legality_alternative_inModel (v : Params) (hv : v.Valid) (hf : Fphase v < 1)
    (K M : ℕ) (hr : LegalityRanks v K M) (u ε L : ℝ)
    (hd : CopulaDomain 2 K M (legalityA v K) u ε L)
    (hmean : ε*L*u = legalityB v K) (hmoment : ε*L^v.p ≤ 10)
    (idx : CopulaIndex K M) :
    InModel v (copulaLaw true v K M (legalityA v K) u ε L idx) := by
  let a := legalityA v K
  let b := legalityB v K
  let C := a*b*kappa0/(1-a^2)
  let law := copulaLaw true v K M a u ε L idx
  have hK : 0 < K := by have := hr.2.2.1; have := hr.2.2.2.1; omega
  obtain ⟨ha, hb, _, _⟩ := legality_tuning_bounds v hv K (by omega)
  have hapos : 0 < a := ha.1
  have hbpos : 0 < b := hb.1
  have ha16 : a ≤ 1/16 := ha.2
  have hb256 : b ≤ 1/256 := hb.2
  have hden : 1/2 ≤ 1-a^2 := by nlinarith
  have hdenpos : 0 < 1-a^2 := by linarith
  have hkappa : 0 < kappa0 := by norm_num [kappa0]
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCbound : C ≤ 2*a*b*kappa0 := by
    dsimp [C]
    apply (div_le_iff₀ hdenpos).mpr
    have hab : 0 ≤ a*b*kappa0 := by positivity
    nlinarith
  have hCsmall : C ≤ 1/32768 := by
    have hab : a*b ≤ (1/16:ℝ)*(1/256) := mul_le_mul ha16 hb256 hbpos.le (by norm_num)
    norm_num [kappa0] at hCbound
    nlinarith
  obtain ⟨hγ, hβ, hKβ⟩ := legality_alternative_power_bounds v hv hf K M hr
  have hCMγ : C*(M:ℝ)^v.γ ≤ 1/32768 := by
    calc
      _ ≤ (2*a*b*kappa0)*(M:ℝ)^v.γ := by gcongr
      _ = (2*kappa0)*(a*b*(M:ℝ)^v.γ) := by ring
      _ ≤ (2*kappa0)*(1/4096) := by gcongr <;> norm_num [kappa0]
      _ = _ := by norm_num [kappa0]
  have hCMβ : C*(M:ℝ)^v.β ≤ 1/32768 := by
    calc
      _ ≤ (2*a*b*kappa0)*(M:ℝ)^v.β := by gcongr
      _ = (2*kappa0)*(a*b*(M:ℝ)^v.β) := by ring
      _ ≤ (2*kappa0)*(1/4096) := by gcongr <;> norm_num [kappa0]
      _ = _ := by norm_num [kappa0]
  have hCaKβ : C*a*(K:ℝ)^v.β ≤ 1/524288 := by
    calc
      _ ≤ (2*a*b*kappa0)*a*(K:ℝ)^v.β := by gcongr
      _ = (2*kappa0)*(a^2*b*(K:ℝ)^v.β) := by ring
      _ ≤ (2*kappa0)*(1/65536) := by gcongr <;> norm_num [kappa0]
      _ = _ := by norm_num [kappa0]
  have hsign (z : Bool) : |signVal z| ≤ 1 := by cases z <;> norm_num [signVal]
  have hH := frame_holder_bound K hK v.β hv.2.2.1
    (fun i => signVal (idx.2 i).2) (fun i => hsign _)
  have hF := frame_holder_bound K hK v.β hv.2.2.1
    (fun i => signVal (idx.2 i).1) (fun i => hsign _)
  have hbp : b*(K:ℝ)^v.β = 1/256 := (legality_amplitude_power_identities v K hK).2
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
  have hξ (x : unitInterval) : |copulaXi K M a idx x| ≤ 1/8 := by
    simp only [copulaXi, abs_mul, abs_of_pos hapos]
    calc
      _ ≤ a*Real.sqrt 2 := mul_le_mul_of_nonneg_left (hF.1 x) hapos.le
      _ ≤ (1/16:ℝ)*2 := mul_le_mul ha16 hsqrt (Real.sqrt_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hξdiff (x z : unitInterval) :
      |copulaXi K M a idx x-copulaXi K M a idx z| ≤
        a*(4*(K:ℝ)^v.β*|(x:ℝ)-(z:ℝ)|^v.β) := by
    simp only [copulaXi, ← mul_sub, abs_mul, abs_of_pos hapos]
    exact mul_le_mul_of_nonneg_left (hF.2 x z) hapos.le
  have hform := copulaLaw_alternative_primitives v K M a u ε L hd idx
  have hm (x : unitInterval) : law.m0 x =
      b*frameField K (fun i => signVal (idx.2 i).2) x +
      C*smoothedTent K M idx.1 x*(1+copulaXi K M a idx x) := by
    rw [(hform x).2.1, hmean]
  have hτ (x : unitInterval) : law.tau x = -(2*C)*smoothedTent K M idx.1 x := by
    rw [(hform x).2.2, hmean]
    dsimp [C]
    ring
  have hbase (x : unitInterval) : |law.m0 x| ≤ 1/2 := by
    have hg := smoothedTent_abs_le_one K M hK idx.1 x
    have hplus : |1+copulaXi K M a idx x| ≤ 2 :=
      (abs_add_le _ _).trans (by simpa using (show |(1:ℝ)|+|copulaXi K M a idx x| ≤ 2 by norm_num; linarith [hξ x]))
    rw [hm]
    calc
      _ ≤ |b*frameField K (fun i => signVal (idx.2 i).2) x| +
        |C*smoothedTent K M idx.1 x*(1+copulaXi K M a idx x)| := abs_add_le _ _
      _ ≤ b*2+C*1*2 := by
        simp only [abs_mul, abs_of_pos hbpos, abs_of_pos hCpos]
        gcongr
        exact (hH.1 x).trans hsqrt
      _ ≤ 1/2 := by linarith
  have heffect (x : unitInterval) : |law.tau x| ≤ 1/2 := by
    rw [hτ, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2*C)]
    calc
      _ ≤ 2*C*1 := mul_le_mul_of_nonneg_left (smoothedTent_abs_le_one K M hK idx.1 x) (by positivity)
      _ ≤ _ := by linarith
  have hnull := legality_null_inNull v hv K M hr u ε L hd hmean hmoment idx
  have he : law.e = (copulaLaw false v K M a u ε L idx).e := by
    ext x
    exact (hform x).1.trans ((copulaLaw_null_primitives v K M a u ε L hd idx x).1.symm)
  have ht := copula_table_valid 2 K M a u ε L hd true idx
  refine ⟨?_, ?_, ?_, ?_, ?_, hbase, heffect, ?_⟩
  · change Measure.map X (tableObservedLaw (copulaXi K M a idx) (copulaUpsilon K M u idx)
      (copulaZeta true K M a u idx) ε L).P = design
    simp only [tableObservedLaw, dif_pos ht]
    rw [tableLaw_eq_compProd _ _ _ ε L ht]
    letI : IsProbabilityMeasure design := by change IsProbabilityMeasure (volume : Measure unitInterval); infer_instance
    letI := recordKernel_markov _ (measurable_tableProp _ _ _ ε L ht) _
      (table_certificate _ _ _ ε L ht).2.2.1 (tableArm_markov _ _ _ ε L ht)
    exact Measure.fst_compProd _ _
  · change ∀ x, 1/4 ≤ law.e x ∧ law.e x ≤ 3/4
    rw [he]
    exact hnull.overlap
  · change holderBall v.α law.e
    rw [he]
    exact hnull.propensitySmooth
  · refine ⟨law.m0.continuous, fun x => (hbase x).trans (by norm_num), ?_⟩
    intro x z
    let d := |(x:ℝ)-(z:ℝ)|^v.β
    have hd0 : 0 ≤ d := by dsimp [d]; positivity
    have hg := smoothedTent_holder_bound K M hK idx.1 v.β hv.2.2.1.1.le hv.2.2.1.2 x z
    have hgz := smoothedTent_abs_le_one K M hK idx.1 z
    have hplus : |1+copulaXi K M a idx x| ≤ 2 := by
      have hh := abs_add_le (1:ℝ) (copulaXi K M a idx x)
      norm_num at hh
      linarith [hξ x]
    rw [hm, hm]
    have heq : b*frameField K (fun i => signVal (idx.2 i).2) x +
        C*smoothedTent K M idx.1 x*(1+copulaXi K M a idx x)-
        (b*frameField K (fun i => signVal (idx.2 i).2) z +
        C*smoothedTent K M idx.1 z*(1+copulaXi K M a idx z)) =
        b*(frameField K (fun i => signVal (idx.2 i).2) x-frameField K (fun i => signVal (idx.2 i).2) z)+
        C*((smoothedTent K M idx.1 x-smoothedTent K M idx.1 z)*(1+copulaXi K M a idx x)+
          smoothedTent K M idx.1 z*(copulaXi K M a idx x-copulaXi K M a idx z)) := by ring
    rw [heq]
    calc
      _ ≤ |b*(frameField K (fun i => signVal (idx.2 i).2) x-frameField K (fun i => signVal (idx.2 i).2) z)|+
        |C| *(|(smoothedTent K M idx.1 x-smoothedTent K M idx.1 z)*(1+copulaXi K M a idx x)|+
        |smoothedTent K M idx.1 z*(copulaXi K M a idx x-copulaXi K M a idx z)|) := by
          apply (abs_add_le _ _).trans
          apply add_le_add le_rfl
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg C)
      _ ≤ b*(4*(K:ℝ)^v.β*d)+C*((32*(M:ℝ)^v.β*d)*2+1*(a*(4*(K:ℝ)^v.β*d))) := by
        simp only [abs_mul, abs_of_pos hbpos, abs_of_pos hCpos]
        gcongr <;> first | exact hH.2 x z | exact hg | exact hξdiff x z
      _ = (4*(b*(K:ℝ)^v.β)+64*(C*(M:ℝ)^v.β)+4*(C*a*(K:ℝ)^v.β))*d := by ring
      _ ≤ (4*(1/256:ℝ)+64*(1/32768)+4*(1/524288))*d := by gcongr; exact hbp.le
      _ ≤ 20*d := by gcongr; norm_num
  · refine ⟨law.tau.continuous, fun x => (heffect x).trans (by norm_num), ?_⟩
    intro x z
    rw [hτ, hτ, ← mul_sub, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2*C)]
    calc
      _ ≤ (2*C)*(32*(M:ℝ)^v.γ*|(x:ℝ)-(z:ℝ)|^v.γ) := by
        gcongr
        exact smoothedTent_holder_bound K M hK idx.1 v.γ (by linarith [hv.2.2.2.1]) hv.2.2.2.2 x z
      _ = 64*(C*(M:ℝ)^v.γ)*|(x:ℝ)-(z:ℝ)|^v.γ := by ring
      _ ≤ 64*(1/32768:ℝ)*|(x:ℝ)-(z:ℝ)|^v.γ := by gcongr
      _ ≤ 20*|(x:ℝ)-(z:ℝ)|^v.γ := by gcongr; norm_num
  · intro arm
    filter_upwards [] with x
    rw [copulaLaw_raw_moment v 2 K M a u ε L v.p hd (by linarith [hv.1.1]) true idx arm x]
    exact (ENNReal.ofReal_le_ofReal hmoment).trans_eq (by norm_num)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
