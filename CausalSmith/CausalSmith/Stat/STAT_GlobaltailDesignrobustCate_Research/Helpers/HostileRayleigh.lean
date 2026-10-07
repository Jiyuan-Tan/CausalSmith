module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.HostileRayleighBasic

/-! # Normalized thin-slab Rayleigh bounds -/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory Filter
open scoped BigOperators

lemma hostileCube_volume (d j : ℕ) :
    volume.real (hostileCube d j) = ((4 : ℝ) ^ (-(j : ℤ))) ^ d := by
  have hset : hostileCube d j =
      Set.Icc (fun _ : Fin d => (4 : ℝ) ^ (-(j : ℤ)))
        (fun _ : Fin d => 2 * (4 : ℝ) ^ (-(j : ℤ))) := by
    ext x
    simp only [hostileCube, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
    aesop
  have hle : (fun _ : Fin d => (4 : ℝ) ^ (-(j : ℤ))) ≤
      (fun _ : Fin d => 2 * (4 : ℝ) ^ (-(j : ℤ))) := by
    intro i
    have : 0 < (4 : ℝ) ^ (-(j : ℤ)) := by positivity
    linarith
  rw [hset, measureReal_def, Real.volume_Icc_pi_toReal hle]
  simp only [mul_sub, one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  ring

lemma hostileCube_volume_ne_top (d j : ℕ) : volume (hostileCube d j) ≠ ⊤ := by
  have hset : hostileCube d j =
      Set.Icc (fun _ : Fin d => (4 : ℝ) ^ (-(j : ℤ)))
        (fun _ : Fin d => 2 * (4 : ℝ) ^ (-(j : ℤ))) := by
    ext x
    simp only [hostileCube, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
    aesop
  rw [hset, Real.volume_Icc_pi]
  simp

lemma hostileSlab_volume (d j : ℕ) (q : ℝ) (hd : 1 ≤ d) (hq : 0 < q) :
    volume.real (hostileSlab d j q) =
      ((4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / (3 * q)) *
        ((4 : ℝ) ^ (-(j : ℤ))) ^ d := by
  let h : ℝ := (4 : ℝ) ^ (-(j : ℤ))
  let η : ℝ := h ^ ((d : ℝ) / (3 * q))
  let i0 : Fin d := ⟨0, hd⟩
  let lo : Fin d → ℝ := fun i => if i = i0 then h * (3 / 2 - η / 2) else h
  let hi : Fin d → ℝ := fun i => if i = i0 then h * (3 / 2 + η / 2) else 2 * h
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    have hh0 : 0 ≤ h := by dsimp [h]; positivity
    have hh1 : h ≤ 1 := by
      dsimp [h]
      rw [zpow_neg, zpow_natCast]
      exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
    exact Real.rpow_le_one hh0 hh1 (by positivity)
  have hset : hostileSlab d j q = Set.Icc lo hi := by
    ext x
    simp only [hostileSlab, show 0 < d by omega, dif_pos, hostileCube,
      Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
    dsimp [lo, hi, i0, h, η]
    constructor
    · rintro ⟨hcube, hslab⟩
      rw [abs_le] at hslab
      constructor
      · intro i
        by_cases hi0 : i = ⟨0, hd⟩
        · subst i
          simp only [ite_true]
          have hh : 0 < (4 : ℝ) ^ (-(j : ℤ)) := by positivity
          field_simp [hh.ne] at hslab ⊢
          nlinarith [hslab.1]
        · simpa [hi0] using (hcube i).1
      · intro i
        by_cases hi0 : i = ⟨0, hd⟩
        · subst i
          simp only [ite_true]
          have hh : 0 < (4 : ℝ) ^ (-(j : ℤ)) := by positivity
          field_simp [hh.ne] at hslab ⊢
          nlinarith [hslab.2]
        · simpa [hi0] using (hcube i).2
    · intro hrect
      constructor
      · intro i
        by_cases hi0 : i = ⟨0, hd⟩
        · subst i
          simpa only [ite_true] using And.intro
                ((show (4 : ℝ) ^ (-(j : ℤ)) ≤
                (4 : ℝ) ^ (-(j : ℤ)) * (3 / 2 -
                  ((4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / (3 * q)) / 2) by
                have hh : 0 < (4 : ℝ) ^ (-(j : ℤ)) := by positivity
                dsimp [h, η] at hη1
                nlinarith) |>.trans (hrect.1 ⟨0, hd⟩))
            ((hrect.2 ⟨0, hd⟩).trans (show
              (4 : ℝ) ^ (-(j : ℤ)) * (3 / 2 +
                  ((4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / (3 * q)) / 2) ≤
                2 * (4 : ℝ) ^ (-(j : ℤ)) by
              have hh : 0 < (4 : ℝ) ^ (-(j :ℤ)) := by positivity
              dsimp [h, η] at hη1
              nlinarith))
        · exact ⟨by simpa [hi0] using hrect.1 i, by simpa [hi0] using hrect.2 i⟩
      · rw [abs_le]
        have hh : 0 < (4 : ℝ) ^ (-(j : ℤ)) := by positivity
        have hr := And.intro (hrect.1 ⟨0, hd⟩) (hrect.2 ⟨0, hd⟩)
        simp only [ite_true] at hr
        field_simp [hh.ne] at ⊢
        constructor <;> nlinarith [hr.1, hr.2]
  have hle : lo ≤ hi := by
    intro i
    dsimp [lo, hi]
    split_ifs
    · have hh : 0 ≤ h := by dsimp [h]; positivity
      nlinarith
    · have hh : 0 ≤ h := by dsimp [h]; positivity
      nlinarith
  rw [hset, measureReal_def, Real.volume_Icc_pi_toReal hle]
  have hdiff : ∀ i : Fin d, hi i - lo i = if i = i0 then h * η else h := by
    intro i
    dsimp [hi, lo]
    split_ifs <;> ring
  simp_rw [hdiff]
  have hfactor : (∏ i : Fin d, if i = i0 then h * η else h) =
      (∏ _i : Fin d, h) * ∏ i : Fin d, if i = i0 then η else 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [hfactor]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hi0mem : i0 ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ _
  rw [Finset.prod_ite_eq' Finset.univ i0, if_pos hi0mem]
  dsimp [h, η]
  ring

lemma baselinePropensity_measurable (d : ℕ) (q : ℝ) (hq : 0 < q) : Measurable (baselinePropensity d q) := by
  unfold baselinePropensity
  have hmax : Measurable (maxCoordinate (d := d)) := by
    unfold maxCoordinate
    convert Measurable.sSup (α := ℝ) (δ := Fin d → ℝ) (ι := Fin d)
      (s := Set.univ) Set.countable_univ
      (fun i _ => measurable_pi_apply i) using 1
    ext x
    simp
  exact (Real.continuous_rpow_const (by positivity)).measurable.comp hmax

lemma rawGramEntry_integrable (d j : ℕ) (q : ℝ) (hd : 1 ≤ d) (hq : 0 < q)
    (a b : Fin (d + 1)) : IntegrableOn
      (fun x => hostilePropensity d q x * rawLinearFeature d j x a *
        rawLinearFeature d j x b) (hostileCube d j) volume := by
  have hmeasP : Measurable (hostilePropensity d q) := by
    have hraised : MeasurableSet {x : Fin d → ℝ |
        ∃ k : ℕ, 1 ≤ k ∧ x ∈ hostileSlab d k q} := by
      rw [show {x : Fin d → ℝ | ∃ k : ℕ, 1 ≤ k ∧ x ∈ hostileSlab d k q} =
        ⋃ k : {k : ℕ // 1 ≤ k}, hostileSlab d k q by ext x; simp]
      exact MeasurableSet.iUnion fun k => hostileSlab_measurable d k q
    unfold hostilePropensity
    exact Measurable.ite hraised measurable_const (by
      unfold baselinePropensity
      have hmax : Measurable (maxCoordinate (d := d)) := by
        unfold maxCoordinate
        convert Measurable.sSup (α := ℝ) (δ := Fin d → ℝ) (ι := Fin d)
          (s := Set.univ) Set.countable_univ
          (fun i _ => measurable_pi_apply i) using 1
        ext x
        simp
      exact (Real.continuous_rpow_const (by positivity)).measurable.comp hmax)
  have hmeasF (c : Fin (d + 1)) :
      Measurable (fun x : Fin d → ℝ => rawLinearFeature d j x c) := by
    unfold rawLinearFeature
    split
    · exact measurable_const
    · fun_prop
  apply (integrableOn_const (C := (1 +
      (2 * (4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / q))) (by
    have hset : hostileCube d j =
        Set.Icc (fun _ : Fin d => (4 : ℝ) ^ (-(j : ℤ)))
          (fun _ : Fin d => 2 * (4 : ℝ) ^ (-(j : ℤ))) := by
      ext x
      simp only [hostileCube, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
      aesop
    rw [hset, Real.volume_Icc_pi]
    simp)).mono'
      ((hmeasP.mul (hmeasF a) |>.mul (hmeasF b)).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem (hostileCube_measurable d j)] with x hx
  rw [Real.norm_eq_abs]
  have hmax0 : 0 ≤ maxCoordinate x := by
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have hle : x ⟨0, hd⟩ ≤ maxCoordinate x := by
      unfold maxCoordinate
      exact le_csSup ⟨2 * (4 : ℝ) ^ (-(j : ℤ)), by
        rintro y ⟨i, rfl⟩
        exact (hx i).2⟩ ⟨⟨0, hd⟩, rfl⟩
    exact (zpow_nonneg (by norm_num) _).trans ((hx ⟨0, hd⟩).1.trans hle)
  have hp0 : 0 ≤ hostilePropensity d q x := by
    unfold hostilePropensity
    split_ifs
    · norm_num
    · exact Real.rpow_nonneg hmax0 _
  have hp1 : hostilePropensity d q x ≤
      1 + (2 * (4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / q) := by
    unfold hostilePropensity
    split_ifs
    · nlinarith [Real.rpow_nonneg
          (by positivity : 0 ≤ 2 * (4 : ℝ) ^ (-(j : ℤ))) ((d : ℝ) / q)]
    · exact (baselinePropensity_upper_on_hostileCube d j q hd hq x hx).trans
        (le_add_of_nonneg_left (by norm_num))
  have ha := show |rawLinearFeature d j x a| ≤ 1 by
    unfold rawLinearFeature
    split_ifs with hzero
    · simp
    · have hh : 0 < (4 : ℝ) ^ (-(j : ℤ)) := by positivity
      have hi := hx ⟨a.val - 1, by have := a.isLt; omega⟩
      rw [abs_le]
      constructor
      · have := div_nonneg (sub_nonneg.mpr hi.1) hh.le
        linarith
      · apply (div_le_iff₀ hh).2
        linarith [hi.2]
  have hb := show |rawLinearFeature d j x b| ≤ 1 by
    unfold rawLinearFeature
    split_ifs with hzero
    · simp
    · have hh : 0 < (4 : ℝ) ^ (-(j : ℤ)) := by positivity
      have hi := hx ⟨b.val - 1, by have := b.isLt; omega⟩
      rw [abs_le]
      constructor
      · have := div_nonneg (sub_nonneg.mpr hi.1) hh.le
        linarith
      · apply (div_le_iff₀ hh).2
        linarith [hi.2]
  change |hostilePropensity d q x * rawLinearFeature d j x a *
    rawLinearFeature d j x b| ≤ _
  rw [abs_mul, abs_mul, abs_of_nonneg hp0]
  have hab : |rawLinearFeature d j x a| * |rawLinearFeature d j x b| ≤ 1 := by
    nlinarith [abs_nonneg (rawLinearFeature d j x a),
      abs_nonneg (rawLinearFeature d j x b),
      mul_nonneg (abs_nonneg (rawLinearFeature d j x a))
        (abs_nonneg (rawLinearFeature d j x b))]
  calc
    hostilePropensity d q x * |rawLinearFeature d j x a| *
        |rawLinearFeature d j x b| = hostilePropensity d q x *
          (|rawLinearFeature d j x a| * |rawLinearFeature d j x b|) := by ring
    _ ≤ hostilePropensity d q x * 1 := mul_le_mul_of_nonneg_left hab hp0
    _ ≤ _ := by simpa using hp1

lemma rawHostileGram_quadraticForm (d j : ℕ) (q : ℝ) (hd : 1 ≤ d) (hq : 0 < q)
    (a : Fin (d + 1) → ℝ) :
    quadraticForm (rawHostileGram d j q) a =
      (∫ x in hostileCube d j, hostilePropensity d q x *
        (∑ i, a i * rawLinearFeature d j x i) ^ 2 ∂volume) /
      (∫ x in hostileCube d j, hostilePropensity d q x ∂volume) := by
  have hint (i k : Fin (d + 1)) : IntegrableOn
      (fun x => hostilePropensity d q x * rawLinearFeature d j x i *
        rawLinearFeature d j x k) (hostileCube d j) volume := by
    exact rawGramEntry_integrable d j q hd hq i k
  unfold quadraticForm rawHostileGram
  let D := ∫ x in hostileCube d j, hostilePropensity d q x ∂volume
  calc
    (∑ i, ∑ k, a i *
        ((∫ x in hostileCube d j, hostilePropensity d q x *
          rawLinearFeature d j x i * rawLinearFeature d j x k ∂volume) / D) * a k) =
        (∑ i, ∑ k, a i *
          (∫ x in hostileCube d j, hostilePropensity d q x *
            rawLinearFeature d j x i * rawLinearFeature d j x k ∂volume) * a k) / D := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (∫ x in hostileCube d j, hostilePropensity d q x *
        (∑ i, a i * rawLinearFeature d j x i) ^ 2 ∂volume) / D := by
      congr 1
      have hterm (i k : Fin (d + 1)) : IntegrableOn
          (fun x => hostilePropensity d q x *
            (a i * rawLinearFeature d j x i) *
            (a k * rawLinearFeature d j x k)) (hostileCube d j) volume := by
        have hb := hint i k
        change Integrable _ (volume.restrict (hostileCube d j))
        change Integrable _ (volume.restrict (hostileCube d j)) at hb
        convert hb.const_mul (a i * a k) using 1
        funext x
        ring
      calc
        (∑ i, ∑ k, a i *
            (∫ x in hostileCube d j, hostilePropensity d q x *
              rawLinearFeature d j x i * rawLinearFeature d j x k ∂volume) * a k) =
            ∑ i, ∑ k, ∫ x in hostileCube d j, hostilePropensity d q x *
              (a i * rawLinearFeature d j x i) *
              (a k * rawLinearFeature d j x k) ∂volume := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro k hk
          rw [← integral_const_mul, ← integral_mul_const]
          apply integral_congr_ae
          filter_upwards with x
          ring
        _ = ∫ x in hostileCube d j, ∑ i, ∑ k,
              hostilePropensity d q x * (a i * rawLinearFeature d j x i) *
                (a k * rawLinearFeature d j x k) ∂volume := by
          rw [integral_finset_sum Finset.univ (fun i _ =>
            integrable_finset_sum Finset.univ fun k _ => hterm i k)]
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_finset_sum Finset.univ (fun k _ => hterm i k)]
        _ = ∫ x in hostileCube d j, hostilePropensity d q x *
              (∑ i, a i * rawLinearFeature d j x i) ^ 2 ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          rw [sq, Finset.sum_mul]
          simp_rw [Finset.mul_sum]
          ring

lemma weightedEnergy_integrable (d j : ℕ) (q : ℝ) (hd : 1 ≤ d) (hq : 0 < q)
    (a : Fin (d + 1) → ℝ) : IntegrableOn
      (fun x => hostilePropensity d q x *
        (∑ i, a i * rawLinearFeature d j x i) ^ 2)
      (hostileCube d j) volume := by
  have hterm (i k : Fin (d + 1)) : IntegrableOn
      (fun x => hostilePropensity d q x *
        (a i * rawLinearFeature d j x i) *
        (a k * rawLinearFeature d j x k)) (hostileCube d j) volume := by
    have hb := rawGramEntry_integrable d j q hd hq i k
    change Integrable _ (volume.restrict (hostileCube d j))
    change Integrable _ (volume.restrict (hostileCube d j)) at hb
    convert hb.const_mul (a i * a k) using 1
    funext x
    ring
  have hsum : IntegrableOn (fun x => ∑ i, ∑ k,
      hostilePropensity d q x * (a i * rawLinearFeature d j x i) *
        (a k * rawLinearFeature d j x k)) (hostileCube d j) volume :=
    integrable_finset_sum Finset.univ fun i _ =>
      integrable_finset_sum Finset.univ fun k _ => hterm i k
  apply hsum.congr_fun
  · intro x hx
    change (∑ i, ∑ k, hostilePropensity d q x *
      (a i * rawLinearFeature d j x i) * (a k * rawLinearFeature d j x k)) =
        hostilePropensity d q x * (∑ i, a i * rawLinearFeature d j x i) ^ 2
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    ring
  · exact hostileCube_measurable d j

lemma hostileDenominator_lower (d j : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hj : 1 ≤ j) :
    volume.real (hostileSlab d j q) ≤
      ∫ x in hostileCube d j, hostilePropensity d q x ∂volume := by
  have hpint : IntegrableOn (hostilePropensity d q) (hostileCube d j) volume := by
    have h := rawGramEntry_integrable d j q hd hq
      (0 : Fin (d + 1)) (0 : Fin (d + 1))
    simpa [rawLinearFeature] using h
  calc
    volume.real (hostileSlab d j q) =
        ∫ _x in hostileSlab d j q, (1 : ℝ) ∂volume := by
      rw [setIntegral_const]
      simp
    _ = ∫ x in hostileSlab d j q, hostilePropensity d q x ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (hostileSlab_measurable d j q)] with x hx
      rw [hostilePropensity_eq_one_on_slab d j q hj x hx]
    _ ≤ ∫ x in hostileCube d j, hostilePropensity d q x ∂volume := by
      apply setIntegral_mono_set hpint
      · filter_upwards [ae_restrict_mem (hostileCube_measurable d j)] with x hx
        exact (by
          unfold hostilePropensity
          split_ifs
          · norm_num
          · exact Real.rpow_nonneg (by
              letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
              have hle : x ⟨0, hd⟩ ≤ maxCoordinate x := by
                unfold maxCoordinate
                exact le_csSup ⟨2 * (4 : ℝ) ^ (-(j : ℤ)), by
                  rintro y ⟨i, rfl⟩; exact (hx i).2⟩ ⟨⟨0, hd⟩, rfl⟩
              exact (zpow_nonneg (by norm_num) _).trans ((hx ⟨0, hd⟩).1.trans hle)) _)
      · exact ae_of_all _ fun x hx => hx.1

lemma hostileNumerator_upper (d j : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hj : 1 ≤ j) :
    (∫ x in hostileCube d j, hostilePropensity d q x *
      (∑ i, unitHostileDirection d i * rawLinearFeature d j x i) ^ 2 ∂volume) ≤
      ((((4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / (3 * q))) ^ 2 / 5) *
          volume.real (hostileSlab d j q) +
        ((2 * (4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / q) / 5) *
          volume.real (hostileCube d j) := by
  let f : (Fin d → ℝ) → ℝ := fun x => hostilePropensity d q x *
    (∑ i, unitHostileDirection d i * rawLinearFeature d j x i) ^ 2
  let u : ℝ := (((4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / (3 * q))) ^ 2 / 5
  let v : ℝ := (2 * (4 : ℝ) ^ (-(j : ℤ))) ^ ((d : ℝ) / q) / 5
  have hf : IntegrableOn f (hostileCube d j) volume :=
    weightedEnergy_integrable d j q hd hq (unitHostileDirection d)
  have hslabsub : hostileSlab d j q ⊆ hostileCube d j := fun x hx => hx.1
  have hsplit : hostileCube d j = hostileSlab d j q ∪
      (hostileCube d j \ hostileSlab d j q) := by
    ext x
    aesop
  conv_lhs => rw [hsplit]
  rw [setIntegral_union Set.disjoint_sdiff_right
    ((hostileCube_measurable d j).diff (hostileSlab_measurable d j q))
    (hf.mono_set hslabsub)
    (hf.mono_set Set.diff_subset)]
  apply add_le_add
  · calc
      (∫ x in hostileSlab d j q, f x ∂volume) ≤
          ∫ _x in hostileSlab d j q, u ∂volume := by
        apply setIntegral_mono_ae_restrict (hf.mono_set hslabsub)
          (integrableOn_const (ne_top_of_le_ne_top
            (hostileCube_volume_ne_top d j) (measure_mono hslabsub)))
        filter_upwards [ae_restrict_mem (hostileSlab_measurable d j q)] with x hx
        dsimp [f, u]
        rw [hostilePropensity_eq_one_on_slab d j q hj x hx, one_mul]
        exact unitHostileDirection_slab_sq_bound d j q hd x hx
      _ = u * volume.real (hostileSlab d j q) := by
        rw [setIntegral_const]
        simp [mul_comm]
  · calc
      (∫ x in hostileCube d j \ hostileSlab d j q, f x ∂volume) ≤
          ∫ _x in hostileCube d j \ hostileSlab d j q, v ∂volume := by
        apply setIntegral_mono_ae_restrict (hf.mono_set Set.diff_subset)
          (integrableOn_const (ne_top_of_le_ne_top
            (hostileCube_volume_ne_top d j) (measure_mono Set.diff_subset)))
        filter_upwards [ae_restrict_mem ((hostileCube_measurable d j).diff
          (hostileSlab_measurable d j q))] with x hx
        dsimp [f, v]
        rw [hostilePropensity_eq_baseline_off_slab d j q hd x hx.1 hx.2]
        have hp := baselinePropensity_upper_on_hostileCube d j q hd hq x hx.1
        have he := unitHostileDirection_cube_sq_bound d j hd x hx.1
        have hp0 : 0 ≤ baselinePropensity d q x := by
          exact Real.rpow_nonneg (by
            letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
            have hle : x ⟨0, hd⟩ ≤ maxCoordinate x := by
              unfold maxCoordinate
              exact le_csSup ⟨2 * (4 : ℝ) ^ (-(j : ℤ)), by
                rintro y ⟨i, rfl⟩; exact (hx.1 i).2⟩ ⟨⟨0, hd⟩, rfl⟩
            exact (zpow_nonneg (by norm_num) _).trans ((hx.1 ⟨0, hd⟩).1.trans hle)) _
        nlinarith [sq_nonneg (∑ i, unitHostileDirection d i * rawLinearFeature d j x i),
          Real.rpow_nonneg (by positivity : 0 ≤ 2 * (4 : ℝ) ^ (-(j : ℤ))) ((d : ℝ) / q)]
      _ = v * volume.real (hostileCube d j \ hostileSlab d j q) := by
        rw [setIntegral_const]
        simp [mul_comm]
      _ ≤ v * volume.real (hostileCube d j) := by
        apply mul_le_mul_of_nonneg_left
        · exact measureReal_mono Set.diff_subset (hostileCube_volume_ne_top d j)
        · dsimp [v]
          positivity

lemma unitRayleigh_upper (d j : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hj : 1 ≤ j) :
    quadraticForm (rawHostileGram d j q) (unitHostileDirection d) ≤
      ((4 : ℝ) / 5) * (1 / 4 + (2 : ℝ) ^ ((d : ℝ) / q - 2)) *
        ((4 : ℝ) ^ (-(j : ℤ))) ^ ((2 * (d : ℝ)) / (3 * q)) := by
  let h : ℝ := (4 : ℝ) ^ (-(j : ℤ))
  let η : ℝ := h ^ ((d : ℝ) / (3 * q))
  let den : ℝ := ∫ x in hostileCube d j, hostilePropensity d q x ∂volume
  let num : ℝ := ∫ x in hostileCube d j, hostilePropensity d q x *
    (∑ i, unitHostileDirection d i * rawLinearFeature d j x i) ^ 2 ∂volume
  have hh : 0 < h := by dsimp [h]; positivity
  have hη : 0 < η := Real.rpow_pos_of_pos hh _
  have hcube : volume.real (hostileCube d j) = h ^ d := by
    simpa [h] using hostileCube_volume d j
  have hslab : volume.real (hostileSlab d j q) = η * h ^ d := by
    simpa [h, η] using hostileSlab_volume d j q hd hq
  have hdpos : 0 < den := by
    have hlower := hostileDenominator_lower d j q hd hq hj
    rw [hslab] at hlower
    exact lt_of_lt_of_le (mul_pos hη (pow_pos hh d)) hlower
  have hnum := hostileNumerator_upper d j q hd hq hj
  change num ≤ _ at hnum
  rw [hslab, hcube] at hnum
  have hpow : h ^ ((d : ℝ) / q) = η ^ 3 := by
    dsimp [η]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    congr 1
    field_simp
    norm_num
  have hmul : (2 * h) ^ ((d : ℝ) / q) =
      (2 : ℝ) ^ ((d : ℝ) / q) * h ^ ((d : ℝ) / q) := by
    exact Real.mul_rpow (by norm_num) hh.le
  have hupper : num / den ≤
      (1 / 5 + (2 : ℝ) ^ ((d : ℝ) / q) / 5) * η ^ 2 := by
    apply (div_le_iff₀ hdpos).2
    have hden := hostileDenominator_lower d j q hd hq hj
    rw [hslab] at hden
    have hcoef : 0 ≤ (1 / 5 + (2 : ℝ) ^ ((d : ℝ) / q) / 5) * η ^ 2 := by
      positivity
    calc
      num ≤ (η ^ 2 / 5) * (η * h ^ d) +
          ((2 * h) ^ ((d : ℝ) / q) / 5) * h ^ d := hnum
      _ = (1 / 5 + (2 : ℝ) ^ ((d : ℝ) / q) / 5) * η ^ 2 *
          (η * h ^ d) := by rw [hmul, hpow]; ring
      _ ≤ (1 / 5 + (2 : ℝ) ^ ((d : ℝ) / q) / 5) * η ^ 2 * den :=
        mul_le_mul_of_nonneg_left hden hcoef
  rw [rawHostileGram_quadraticForm d j q hd hq]
  change num / den ≤ _
  calc
    num / den ≤ (1 / 5 + (2 : ℝ) ^ ((d : ℝ) / q) / 5) * η ^ 2 := hupper
    _ = ((4 : ℝ) / 5) * (1 / 4 + (2 : ℝ) ^ ((d : ℝ) / q - 2)) *
        h ^ ((2 * (d : ℝ)) / (3 * q)) := by
      have htwo : (2 : ℝ) ^ ((d : ℝ) / q - 2) =
          (2 : ℝ) ^ ((d : ℝ) / q) / 4 := by
        rw [Real.rpow_sub (by norm_num), show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num]
      have heta : η ^ 2 = h ^ ((2 * (d : ℝ)) / (3 * q)) := by
        dsimp [η]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
        congr 1
        field_simp
        ring
      rw [htwo, heta]
      ring
    _ = _ := by rfl

lemma hostilePropensity_nonneg_on_hostileCube (d j : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (x : Fin d → ℝ) (hx : x ∈ hostileCube d j) :
    0 ≤ hostilePropensity d q x := by
  have hmax0 : 0 ≤ maxCoordinate x := by
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have hle : x ⟨0, hd⟩ ≤ maxCoordinate x := by
      unfold maxCoordinate
      exact le_csSup ⟨2 * (4 : ℝ) ^ (-(j : ℤ)), by
        rintro y ⟨i, rfl⟩; exact (hx i).2⟩ ⟨⟨0, hd⟩, rfl⟩
    exact (zpow_nonneg (by norm_num) _).trans ((hx ⟨0, hd⟩).1.trans hle)
  unfold hostilePropensity
  split_ifs
  · norm_num
  · exact Real.rpow_nonneg hmax0 _

lemma rawHostileMinEigenvalue_tendsto_zero (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) :
    Tendsto (fun j : ℕ => rawHostileMinEigenvalue d j q) atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_atTop.2 ⟨1, fun j hj => hj⟩] with j hj
    unfold rawHostileMinEigenvalue
    apply le_csInf
    · exact ⟨quadraticForm (rawHostileGram d j q) (unitHostileDirection d),
        unitHostileDirection d, unitHostileDirection_norm_sq d hd, rfl⟩
    · intro r hr
      rcases hr with ⟨a, ha, rfl⟩
      rw [rawHostileGram_quadraticForm d j q hd hq]
      apply div_nonneg
      · apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem (hostileCube_measurable d j)] with x hx
        exact mul_nonneg (hostilePropensity_nonneg_on_hostileCube d j q hd x hx)
          (sq_nonneg _)
      · exact measureReal_nonneg.trans (hostileDenominator_lower d j q hd hq hj)
  · filter_upwards [eventually_atTop.2 ⟨1, fun j hj => hj⟩] with j hj
    unfold rawHostileMinEigenvalue
    have hbdd : BddBelow {r : ℝ | ∃ a : Fin (d + 1) → ℝ,
        (∑ i, a i ^ 2) = 1 ∧ quadraticForm (rawHostileGram d j q) a = r} := by
      refine ⟨0, ?_⟩
      intro r hr
      rcases hr with ⟨a, ha, rfl⟩
      rw [rawHostileGram_quadraticForm d j q hd hq]
      apply div_nonneg
      · apply integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem (hostileCube_measurable d j)] with x hx
        exact mul_nonneg (hostilePropensity_nonneg_on_hostileCube d j q hd x hx)
          (sq_nonneg _)
      · exact measureReal_nonneg.trans (hostileDenominator_lower d j q hd hq hj)
    exact (csInf_le hbdd ⟨unitHostileDirection d,
      unitHostileDirection_norm_sq d hd, rfl⟩).trans
        (unitRayleigh_upper d j q hd hq hj)
  · exact hostileRayleighUpper_tendsto_zero d q hd hq

end CausalSmith.Stat.GlobalTailDesignRobustCate
