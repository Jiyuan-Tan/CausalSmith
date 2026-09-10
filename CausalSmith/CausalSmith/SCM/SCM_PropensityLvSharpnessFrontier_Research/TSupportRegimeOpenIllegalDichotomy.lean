import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.OpenIllegal

/-! # Support-regime illegal-region dichotomy -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open Set

/-- Every generator outside the hinge frontier has one common nonempty open
binary region illegal in both support regimes, with either slack divergence or
a zero-divergence face.  For the specified model objects, [the stated conditions](hyp:hPos,hf,hNot), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:support-regime-open-illegal-dichotomy
theorem support_regime_open_illegal_dichotomy (e : ℝ) (f : ℝ → ℝ)
    (hPos : StrictPositivity e) (hf : AdmissibleGenerator f)
    (hNot : f ∉ hingeClassSet (1 / e)) :
    SupportRegimeOpenIllegalDichotomy f e := by
  let c : ℝ := 1 / e
  have he0 : e ≠ 0 := ne_of_gt hPos.1
  have hc1 : 1 < c := by
    dsimp [c]
    rw [one_div]
    exact (one_lt_inv₀ hPos.1).2 hPos.2
  have hc0 : 0 < c := lt_trans zero_lt_one hc1
  by_cases hna : ¬ ∃ b : ℝ, ∀ t ∈ Set.Icc 0 c, f t = b * (t - 1)
  · let x : ℝ := 1 / 2
    let q₀ : ℝ := (1 - x) / (c - x)
    let p₀ : ℝ := c * q₀
    have hcx : 0 < c - x := by dsimp [x]; linarith
    have hq0 : 0 < q₀ := by dsimp [q₀, x]; positivity
    have hq1 : q₀ < 1 := by
      dsimp [q₀, x]
      rw [div_lt_one hcx]
      linarith
    have hp0 : 0 < p₀ := mul_pos hc0 hq0
    have hp1 : p₀ < 1 := by
      dsimp [p₀, q₀, x]
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ hcx).2 (by nlinarith)
    have hratio1 : p₀ / q₀ = c := by
      dsimp [p₀]
      field_simp [ne_of_gt hq0]
    have hratio0 : (1 - p₀) / (1 - q₀) = x := by
      have hqeq : q₀ * (c - x) = 1 - x := by
        dsimp [q₀]
        exact div_mul_cancel₀ _ (ne_of_gt hcx)
      rw [div_eq_iff (ne_of_gt (sub_pos.mpr hq1))]
      dsimp [p₀]
      nlinarith
    have hstrict := chord_strict_at_half_of_nonaffine f c hc1 hf.2.1 hna hf.2.2
    have hdiv0 : binaryDiv f (p₀, q₀) < divRadius f e := by
      dsimp [binaryDiv]
      rw [hratio1, hratio0]
      calc
        q₀ * f c + (1 - q₀) * f x <
            q₀ * f c + (1 - q₀) *
              ((1 - x / c) * f 0 + (x / c) * f c) := by
          have hw := mul_lt_mul_of_pos_left (by simpa [x] using hstrict)
            (sub_pos.mpr hq1)
          simpa [x] using add_lt_add_left hw (q₀ * f c)
        _ = divRadius f e := by
          have h2e : 2 - e ≠ 0 :=
            ne_of_gt (sub_pos.mpr (lt_trans hPos.2 (by norm_num)))
          have hqformula : q₀ = e / (2 - e) := by
            dsimp [q₀, x, c]
            field_simp [he0, h2e]
            ring
          rw [hqformula]
          dsimp [x, c, divRadius]
          field_simp [he0, h2e]
          ring
    let V : Set (ℝ × ℝ) :=
      (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) ∩ binaryDiv f ⁻¹' Set.Iio (divRadius f e)
    have hVopen : IsOpen V := by
      have hcdiv := continuousOn_binaryDiv f hf
      obtain ⟨u, hu, heu⟩ := (continuousOn_iff'.mp hcdiv)
        (Set.Iio (divRadius f e)) isOpen_Iio
      dsimp [V]
      rw [inter_comm, heu, inter_comm]
      exact (isOpen_Ioo.prod isOpen_Ioo).inter hu
    have hzV : (p₀, q₀) ∈ V := ⟨⟨⟨hp0, hp1⟩, ⟨hq0, hq1⟩⟩, hdiv0⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVopen (p₀, q₀) hzV
    let eps : ℝ := min (r / 2) (q₀ / 2)
    let q₁ : ℝ := q₀ - eps
    have heps : 0 < eps := lt_min (half_pos hr) (half_pos hq0)
    have hepsr : eps < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
    have hdist : dist (p₀, q₁) (p₀, q₀) < r := by
      simp [Prod.dist_eq, q₁, abs_of_nonneg heps.le, hepsr, hr]
    have hz1V : (p₀, q₁) ∈ V := hball hdist
    let O : Set (ℝ × ℝ) := V ∩ {z | z.2 < e * z.1}
    have hOopen : IsOpen O :=
      hVopen.inter (isOpen_lt continuous_snd (continuous_const.mul continuous_fst))
    have hcap0 : q₀ = e * p₀ := by
      dsimp [p₀, c]
      field_simp [he0]
    have hz1O : (p₀, q₁) ∈ O := by
      refine ⟨hz1V, ?_⟩
      dsimp [q₁]
      rw [← hcap0]
      linarith
    refine ⟨O, hOopen, ⟨(p₀, q₁), hz1O⟩, ?_, ?_, Or.inl ⟨hna, ?_⟩⟩
    · intro z hz
      exact hz.1.1
    · intro z hz
      exact hz.2
    · intro z hz
      have hsq := hz.1.1
      have hlt : binaryDiv f z < divRadius f e := hz.1.2
      have hfd : fDiv f (binaryLaw z.1) (binaryLaw z.2) <
          (divRadius f e : EReal) := by
        rw [binaryLaw_fDiv_eq f z.1 z.2 hsq.1 hsq.2]
        exact_mod_cast hlt
      have hcommon := binaryLaw_common_illegal_of_lt f e z.1 z.2 hPos hf hsq.1 hsq.2
        hz.2 (le_of_lt hfd)
      exact ⟨hcommon.1, hcommon.2, hfd⟩
  · push Not at hna
    obtain ⟨b, hb⟩ := hna
    let g : ℝ → ℝ := fun t => f t - b * (t - 1)
    have hgzero (t : ℝ) (ht : t ∈ Set.Icc 0 c) : g t = 0 := by
      dsimp [g]
      rw [hb t ht]
      ring
    have haffConcave : ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ => b * (t - 1)) := by
      rw [concaveOn_iff_forall_pos]
      refine ⟨convex_Ici 0, ?_⟩
      intro u hu v hv A B hA hB hsum
      simp only [smul_eq_mul]
      have heq : b * (A * u + B * v - 1) =
          A * (b * (u - 1)) + B * (b * (v - 1)) := by
        calc
          b * (A * u + B * v - 1) =
              b * (A * u + B * v - (A + B)) := by rw [hsum]
          _ = A * (b * (u - 1)) + B * (b * (v - 1)) := by ring
      exact heq.symm.le
    have hgconv : ConvexOn ℝ (Set.Ici 0) g := hf.2.1.sub haffConcave
    have houtside : ∃ d : ℝ, c < d ∧ g d ≤ 0 := by
      by_contra hn
      push Not at hn
      apply hNot
      refine
        { positivity := ?_
          admissible := hf
          affine_hinge := ⟨b, ?_, hn⟩ }
      · simpa [c, he0] using hPos
      · intro t ht0 htc
        exact hgzero t ⟨ht0, htc⟩
    obtain ⟨d, hcd, hgdle⟩ := houtside
    have h0c : g 0 ≤ g c := by
      rw [hgzero 0 ⟨le_rfl, hc0.le⟩, hgzero c ⟨hc0.le, le_rfl⟩]
    have hnonneg (t : ℝ) (hct : c ≤ t) : 0 ≤ g t := by
      have hmono := hgconv.le_right_of_left_le''
        (show 0 ∈ Set.Ici (0 : ℝ) by simp)
        (show t ∈ Set.Ici (0 : ℝ) by exact le_trans hc0.le hct)
        hc0 hct h0c
      rw [hgzero c ⟨hc0.le, le_rfl⟩] at hmono
      exact hmono
    have hgd : g d = 0 := le_antisymm hgdle (hnonneg d hcd.le)
    have hd0 : 0 < d := lt_trans hc0 hcd
    have hzeroD (t : ℝ) (ht : t ∈ Set.Icc 0 d) : g t = 0 := by
      by_cases htc : t ≤ c
      · exact hgzero t ⟨ht.1, htc⟩
      · have hct : c ≤ t := le_of_not_ge htc
        apply le_antisymm
        · have h := hgconv.2 (show 0 ∈ Set.Ici (0 : ℝ) by simp)
            (show d ∈ Set.Ici (0 : ℝ) by exact hd0.le)
            (show 0 ≤ 1 - t / d by rw [sub_nonneg, div_le_one hd0]; exact ht.2)
            (show 0 ≤ t / d by exact div_nonneg ht.1 hd0.le) (by ring)
          simpa only [smul_eq_mul, mul_zero, zero_add,
            div_mul_cancel₀ t (ne_of_gt hd0), hgzero 0 ⟨le_rfl, hc0.le⟩,
            hgd, mul_zero, add_zero] using h
        · exact hnonneg t hct
    let x : ℝ := 1 / 2
    let y : ℝ := (c + d) / 2
    let q₀ : ℝ := (1 - x) / (y - x)
    let p₀ : ℝ := y * q₀
    have hcy : c < y := by dsimp [y]; linarith
    have hyd : y < d := by dsimp [y]; linarith
    have hy1 : 1 < y := lt_trans hc1 hcy
    have hyx : 0 < y - x := by dsimp [x]; linarith
    have hq0 : 0 < q₀ := by dsimp [q₀, x]; positivity
    have hq1 : q₀ < 1 := by
      dsimp [q₀, x]
      rw [div_lt_one hyx]
      linarith
    have hp0 : 0 < p₀ := mul_pos (lt_trans zero_lt_one hy1) hq0
    have hp1 : p₀ < 1 := by
      dsimp [p₀, q₀, x]
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ hyx).2 (by nlinarith)
    have hqeq : q₀ * (y - x) = 1 - x := by
      dsimp [q₀]
      exact div_mul_cancel₀ _ (ne_of_gt hyx)
    have hratio1 : p₀ / q₀ = y := by
      dsimp [p₀]
      field_simp [ne_of_gt hq0]
    have hratio0 : (1 - p₀) / (1 - q₀) = x := by
      rw [div_eq_iff (ne_of_gt (sub_pos.mpr hq1))]
      dsimp [p₀]
      nlinarith
    let O : Set (ℝ × ℝ) :=
      (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) ∩
        {z | c * z.2 < z.1} ∩ {z | z.1 < d * z.2} ∩
          {z | 1 - z.1 < d * (1 - z.2)}
    have hOopen : IsOpen O := by
      exact (((isOpen_Ioo.prod isOpen_Ioo).inter
        (isOpen_lt (continuous_const.mul continuous_snd) continuous_fst)).inter
        (isOpen_lt continuous_fst (continuous_const.mul continuous_snd))).inter
        (isOpen_lt (continuous_const.sub continuous_fst)
          (continuous_const.mul (continuous_const.sub continuous_snd)))
    have hzO : (p₀, q₀) ∈ O := by
      refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · refine ⟨⟨⟨hp0, hp1⟩, ⟨hq0, hq1⟩⟩, ?_⟩
          dsimp [p₀]
          exact mul_lt_mul_of_pos_right hcy hq0
        · dsimp [p₀]
          exact mul_lt_mul_of_pos_right hyd hq0
      · change 1 - p₀ < d * (1 - q₀)
        have hxyd : x < d := by dsimp [x]; linarith [hd0]
        have honeq : 1 - p₀ = x * (1 - q₀) := by
          rw [← div_eq_iff (ne_of_gt (sub_pos.mpr hq1))]
          exact hratio0
        rw [honeq]
        exact mul_lt_mul_of_pos_right hxyd (sub_pos.mpr hq1)
    refine ⟨O, hOopen, ⟨(p₀, q₀), hzO⟩, ?_, ?_, Or.inr ⟨b, d, hcd, ?_, ?_⟩⟩
    · intro z hz
      exact hz.1.1.1
    · intro z hz
      have hcz : c * z.2 < z.1 := hz.1.1.2
      dsimp [c] at hcz
      have hquot : z.2 / e < z.1 := by
        simpa [div_eq_mul_inv, mul_comm] using hcz
      simpa [mul_comm] using (div_lt_iff₀ hPos.1).1 hquot
    · intro t ht
      exact hzeroD t ht
    · intro z hz
      have hsq := hz.1.1.1
      have hqpos : 0 < z.2 := hsq.2.1
      have h1qpos : 0 < 1 - z.2 := sub_pos.mpr hsq.2.2
      have hr1 : z.1 / z.2 ∈ Set.Icc (0 : ℝ) d := by
        exact ⟨div_nonneg hsq.1.1.le hqpos.le,
          (div_lt_iff₀ hqpos).2 hz.1.2 |>.le⟩
      have hr0 : (1 - z.1) / (1 - z.2) ∈ Set.Icc (0 : ℝ) d := by
        exact ⟨div_nonneg (sub_nonneg.mpr hsq.1.2.le) h1qpos.le,
          (div_lt_iff₀ h1qpos).2 hz.2 |>.le⟩
      have hbin : binaryDiv f z = 0 := by
        have hf1 := hzeroD (z.1 / z.2) hr1
        have hf0 := hzeroD ((1 - z.1) / (1 - z.2)) hr0
        dsimp [g] at hf1 hf0
        dsimp [binaryDiv]
        rw [show f (z.1 / z.2) = b * (z.1 / z.2 - 1) by linarith,
          show f ((1 - z.1) / (1 - z.2)) =
            b * ((1 - z.1) / (1 - z.2) - 1) by linarith]
        field_simp [ne_of_gt hqpos, ne_of_gt h1qpos]
        ring
      have hfd : fDiv f (binaryLaw z.1) (binaryLaw z.2) = 0 := by
        rw [binaryLaw_fDiv_eq f z.1 z.2 hsq.1 hsq.2, hbin]
        rfl
      have hrad : divRadius f e = 0 := by
        have hfC := hgzero c ⟨hc0.le, le_rfl⟩
        have hfZ := hgzero 0 ⟨le_rfl, hc0.le⟩
        dsimp [g, c, divRadius] at hfC hfZ ⊢
        field_simp [he0] at hfC
        have hfZ' : f 0 = -b := by linarith
        have hfC' : e * f (1 / e) = b * (1 - e) := by linarith
        rw [hfC', hfZ']
        ring
      have hcommon := binaryLaw_common_illegal_of_lt f e z.1 z.2 hPos hf hsq.1 hsq.2
        (by
          have hcz : c * z.2 < z.1 := hz.1.1.2
          dsimp [c] at hcz
          have hquot : z.2 / e < z.1 := by
            simpa [div_eq_mul_inv, mul_comm] using hcz
          simpa [mul_comm] using (div_lt_iff₀ hPos.1).1 hquot)
        (by rw [hfd, hrad]; rfl)
      exact ⟨hcommon.1, hcommon.2, hfd⟩

end CausalSmith.SCM.PropensityLvSharpnessFrontier
