module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.Estimators

/-!
# A finite jump product rule

This is the deterministic integration by parts identity for a left-continuous
finite product and a continuously differentiable factor.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

@[no_expose]
noncomputable def finiteJumpProductLeft (E : Finset ℝ) (q : ℝ → ℝ)
    (t : ℝ) : ℝ :=
  ∏ u ∈ E.filter (fun u => u < t), q u

lemma finiteJumpProductRule_of_integral_eq_sub
    (E : Finset ℝ) (q F f : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hE : ∀ u ∈ E, a ≤ u ∧ u ≤ b)
    (hFTC : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      (∫ t in x..y, f t) = F y - F x)
    (hstep : IntervalIntegrable
      (fun t => finiteJumpProductLeft E q t * f t) volume a b) :
    (∏ u ∈ E, q u) * F b - F a =
      (∫ t in a..b, finiteJumpProductLeft E q t * f t) +
        ∑ u ∈ E, finiteJumpProductLeft E q u * (q u - 1) * F u := by
  classical
  induction hcard : E.card using Nat.strong_induction_on generalizing E a b with
  | h k ih =>
      by_cases hEmpty : E = ∅
      · subst E
        simpa [finiteJumpProductLeft] using (hFTC a b le_rfl hab le_rfl).symm
      · have hNonempty : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
        let u : ℝ := E.max' hNonempty
        let E' : Finset ℝ := E.erase u
        have huE : u ∈ E := E.max'_mem hNonempty
        have hu : a ≤ u ∧ u ≤ b := hE u huE
        have hlt : E'.card < k := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem huE
        have hE' : ∀ v ∈ E', a ≤ v ∧ v ≤ u := by
          intro v hv
          have hvE : v ∈ E := Finset.mem_of_mem_erase hv
          exact ⟨(hE v hvE).1, Finset.le_max' E v hvE⟩
        have hFTC' : ∀ x y, a ≤ x → x ≤ y → y ≤ u →
            (∫ t in x..y, f t) = F y - F x := by
          intro x y hax hxy hyu
          exact hFTC x y hax hxy (hyu.trans hu.2)
        have hleftEq : ∀ t, t ≤ u →
            finiteJumpProductLeft E q t = finiteJumpProductLeft E' q t := by
          intro t htu
          rw [← Finset.insert_erase huE]
          have hut : ¬ u < t := not_lt_of_ge htu
          unfold finiteJumpProductLeft
          rw [Finset.filter_insert]
          simp [hut, E']
        have hstep' : IntervalIntegrable
            (fun t => finiteJumpProductLeft E' q t * f t) volume a u := by
          apply (hstep.mono_set (by
            rw [Set.uIcc_of_le hab, Set.uIcc_of_le hu.1]
            intro t ht
            exact ⟨ht.1, ht.2.trans hu.2⟩)).congr
          intro t ht
          rw [Set.uIoc_of_le hu.1] at ht
          change finiteJumpProductLeft E q t * f t =
            finiteJumpProductLeft E' q t * f t
          rw [hleftEq t ht.2]
        have hind := ih E'.card hlt E' hu.1 hE' hFTC' hstep' rfl
        have hAllLt : ∀ v ∈ E', v < u := by
          intro v hv
          have hvE : v ∈ E := Finset.mem_of_mem_erase hv
          exact lt_of_le_of_ne (Finset.le_max' E v hvE)
            (Finset.mem_erase.mp hv).1
        have hstepAt : finiteJumpProductLeft E q u = ∏ v ∈ E', q v := by
          unfold finiteJumpProductLeft
          rw [← Finset.insert_erase huE, Finset.filter_insert]
          have huu : ¬ u < u := lt_irrefl u
          rw [if_neg huu]
          rw [Finset.filter_eq_self.mpr hAllLt]
        have hprod : (∏ v ∈ E, q v) = (∏ v ∈ E', q v) * q u := by
          exact (Finset.prod_erase_mul E q huE).symm
        have hstepRight : ∀ t, u < t →
            finiteJumpProductLeft E q t = ∏ v ∈ E, q v := by
          intro t hut
          unfold finiteJumpProductLeft
          rw [Finset.filter_eq_self.mpr]
          intro v hv
          exact lt_of_le_of_lt (Finset.le_max' E v hv) hut
        have hstepLeftE : IntervalIntegrable
            (fun t => finiteJumpProductLeft E q t * f t) volume a u :=
          hstep.mono_set (by
            rw [Set.uIcc_of_le hab, Set.uIcc_of_le hu.1]
            intro t ht
            exact ⟨ht.1, ht.2.trans hu.2⟩)
        have hstepTail : IntervalIntegrable
            (fun t => finiteJumpProductLeft E q t * f t) volume u b :=
          hstep.mono_set (by
            rw [Set.uIcc_of_le hab, Set.uIcc_of_le hu.2]
            intro t ht
            exact ⟨hu.1.trans ht.1, ht.2⟩)
        have hFTCtail := hFTC u b hu.1 hu.2 le_rfl
        have htail :
            (∫ t in u..b, finiteJumpProductLeft E q t * f t) =
              (∏ v ∈ E, q v) * (F b - F u) := by
          calc
            _ = ∫ t in u..b, (∏ v ∈ E, q v) * f t := by
              apply intervalIntegral.integral_congr_ae
              apply Filter.Eventually.of_forall
              intro t ht
              rw [Set.uIoc_of_le hu.2] at ht
              rw [hstepRight t ht.1]
            _ = (∏ v ∈ E, q v) * (∫ t in u..b, f t) := by
              exact intervalIntegral.integral_const_mul _ _
            _ = _ := by rw [hFTCtail]
        have hleftIntegral :
            (∫ t in a..u, finiteJumpProductLeft E q t * f t) =
              ∫ t in a..u, finiteJumpProductLeft E' q t * f t := by
          apply intervalIntegral.integral_congr_ae
          apply Filter.Eventually.of_forall
          intro t ht
          rw [Set.uIoc_of_le hu.1] at ht
          rw [hleftEq t ht.2]
        have hintegral :
            (∫ t in a..b, finiteJumpProductLeft E q t * f t) =
              (∫ t in a..u, finiteJumpProductLeft E' q t * f t) +
                (∏ v ∈ E, q v) * (F b - F u) := by
          rw [← htail, ← hleftIntegral]
          exact (intervalIntegral.integral_add_adjacent_intervals
            hstepLeftE hstepTail).symm
        have hjumpErase :
            (∑ v ∈ E', finiteJumpProductLeft E q v * (q v - 1) * F v) =
              ∑ v ∈ E', finiteJumpProductLeft E' q v * (q v - 1) * F v := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hleftEq v (Finset.le_max' E v (Finset.mem_of_mem_erase hv))]
        have hjump :
            (∑ v ∈ E, finiteJumpProductLeft E q v * (q v - 1) * F v) =
              (∑ v ∈ E', finiteJumpProductLeft E' q v * (q v - 1) * F v) +
                (∏ v ∈ E', q v) * (q u - 1) * F u := by
          rw [← Finset.sum_erase_add E
            (fun v => finiteJumpProductLeft E q v * (q v - 1) * F v) huE,
            hjumpErase, hstepAt]
        rw [hintegral, hjump, hprod]
        have hind' :
            (∫ t in a..u, finiteJumpProductLeft E' q t * f t) =
              (∏ v ∈ E', q v) * F u - F a -
                ∑ v ∈ E', finiteJumpProductLeft E' q v * (q v - 1) * F v := by
          linarith [hind]
        rw [hind']
        ring

lemma deathKM_finiteJumpProductRule_of_integral_eq_sub {n : ℕ} (a : Arm)
    (s : Fin n → ObsHistory) (F f : ℝ → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hExitNonneg : ∀ i : Fin n, 0 ≤ (s i).exit)
    (hFTC : ∀ x y, (0 : ℝ) ≤ x → x ≤ y → y ≤ T →
      (∫ t in x..y, f t) = F y - F x)
    (hstep : IntervalIntegrable
      (fun t => deathKMLeft a s t * f t) volume 0 T) :
    deathKM a s T * F T - F 0 =
      (∫ t in (0 : ℝ)..T, deathKMLeft a s t * f t) +
        ∑ u ∈ (exitTimes s).filter (fun u => u ≤ T),
          deathKMLeft a s u *
            ((1 - invRisk a s u * deathJump a s u) - 1) * F u := by
  classical
  let E : Finset ℝ := (exitTimes s).filter (fun u => u ≤ T)
  let q : ℝ → ℝ := fun u => 1 - invRisk a s u * deathJump a s u
  have hE : ∀ u ∈ E, (0 : ℝ) ≤ u ∧ u ≤ T := by
    intro u hu
    have hu := Finset.mem_filter.mp hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu.1
    exact ⟨hExitNonneg i, hu.2⟩
  have hleft : ∀ t ∈ Set.Icc (0 : ℝ) T,
      finiteJumpProductLeft E q t = deathKMLeft a s t := by
    intro t ht
    unfold finiteJumpProductLeft deathKMLeft
    apply Finset.prod_congr
    · ext u
      simp only [E, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hu, _⟩, hut⟩
        exact ⟨hu, hut⟩
      · rintro ⟨hu, hut⟩
        exact ⟨⟨hu, hut.le.trans ht.2⟩, hut⟩
    · intro u hu
      rfl
  have hprod : (∏ u ∈ E, q u) = deathKM a s T := by
    simp only [E, q, deathKM]
  have hstep' : IntervalIntegrable
      (fun t => finiteJumpProductLeft E q t * f t) volume 0 T := by
    apply hstep.congr
    intro t ht
    rw [Set.uIoc_of_le hT] at ht
    change deathKMLeft a s t * f t = finiteJumpProductLeft E q t * f t
    rw [hleft t ⟨ht.1.le, ht.2⟩]
  have hmain := finiteJumpProductRule_of_integral_eq_sub
    E q F f hT hE hFTC hstep'
  rw [hprod] at hmain
  have hintegral :
      (∫ t in (0 : ℝ)..T, finiteJumpProductLeft E q t * f t) =
        ∫ t in (0 : ℝ)..T, deathKMLeft a s t * f t := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le hT] at ht
    rw [hleft t ⟨ht.1.le, ht.2⟩]
  have hsum :
      (∑ u ∈ E, finiteJumpProductLeft E q u * (q u - 1) * F u) =
        ∑ u ∈ E, deathKMLeft a s u * (q u - 1) * F u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hleft u (hE u hu)]
  rw [hintegral, hsum] at hmain
  simpa only [E, q] using hmain

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
