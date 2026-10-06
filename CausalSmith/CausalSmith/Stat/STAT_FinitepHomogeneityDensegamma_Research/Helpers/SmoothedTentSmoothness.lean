module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentSmoothness
public import Causalean.Mathlib.Analysis.PiecewiseLipschitz

/-! Cell interpolation and Hölder bounds for the squared-frame paired tent. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- On a fine cell the smoothed tent is the squared sine/cosine interpolation of its endpoint values. This statement assumes [the hK condition](hyp:hK), [the hj condition](hyp:hj), [the hl condition](hyp:hl), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_cell_formula
lemma smoothedTent_cell_formula (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M/2) → Bool) (j : ℕ) (hj : j < K) (x : unitInterval)
    (hl : (j:ℝ) ≤ (K:ℝ)*(x:ℝ)) (hu : (K:ℝ)*(x:ℝ) ≤ (j:ℝ)+1) :
    smoothedTent K M σ x =
      coarseTent M σ ((j:ℝ)/K)*Real.cos (Real.pi*((K:ℝ)*(x:ℝ)-j)/2)^2 +
      coarseTent M σ (((j:ℝ)+1)/K)*Real.sin (Real.pi*((K:ℝ)*(x:ℝ)-j)/2)^2 := by
  let i0 : Fin (K+1) := ⟨j, by omega⟩
  let i1 : Fin (K+1) := ⟨j+1, by omega⟩
  have hi : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
  have h0 : frameCoord K i0 x = Real.cos (Real.pi*((K:ℝ)*(x:ℝ)-j)/2) := by
    rw [frameCoord_eq_clipped_cos K hK i0 x]
    change Real.cos (Real.pi * min 1 |(K:ℝ)*(x:ℝ)-(j:ℝ)| / 2) = _
    rw [abs_of_nonneg (by linarith), min_eq_right (by linarith)]
  have h1 : frameCoord K i1 x = Real.sin (Real.pi*((K:ℝ)*(x:ℝ)-j)/2) := by
    rw [frameCoord_eq_clipped_cos K hK i1 x]
    change Real.cos (Real.pi * min 1 |(K:ℝ)*(x:ℝ)-((j+1:ℕ):ℝ)| / 2) = _
    rw [Nat.cast_add, Nat.cast_one, abs_of_nonpos (by linarith), min_eq_right (by linarith)]
    rw [show Real.pi * -((K:ℝ)*(x:ℝ)-((j:ℝ)+1))/2 =
      Real.pi/2-Real.pi*((K:ℝ)*(x:ℝ)-j)/2 by ring, Real.cos_pi_div_two_sub]
  have hz (i : Fin (K+1)) (hm : i ∉ ({i0,i1} : Finset (Fin (K+1)))) : frameCoord K i x = 0 := by
    have hv : i.val ≠ j ∧ i.val ≠ j+1 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff, i0, i1] using hm
    by_contra hn
    have ha := abs_lt.mp (frameCoord_nonzero_distance K hK i x hn)
    have hlow : j < i.val+1 := by exact_mod_cast (show (j:ℝ) < (i:ℝ)+1 by linarith)
    have hup : i.val < j+2 := by
      exact_mod_cast (show (i:ℝ) < ((j+2:ℕ):ℝ) by push_cast; linarith)
    omega
  unfold smoothedTent
  rw [← Finset.sum_subset (Finset.subset_univ ({i0,i1} : Finset (Fin (K+1))))
    (fun i _ hm => by rw [hz i hm]; simp)]
  simp only [Finset.sum_pair hi, h0, h1]
  simp [i0, i1, Nat.cast_add, Nat.cast_one]

/-- A sine-square interpolation inherits the difference of its endpoint values. [This is the stated conclusion](goal). -/
-- @node: squared_tent_profile_lipschitz
lemma squared_tent_profile_lipschitz (g h t s : ℝ) :
    |(g*Real.cos (Real.pi*t/2)^2+h*Real.sin (Real.pi*t/2)^2)-
      (g*Real.cos (Real.pi*s/2)^2+h*Real.sin (Real.pi*s/2)^2)| ≤
      |h-g| *Real.pi*|t-s| := by
  have hc := Real.cos_sq_add_sin_sq (Real.pi*t/2)
  have hd := Real.cos_sq_add_sin_sq (Real.pi*s/2)
  have he : (g*Real.cos (Real.pi*t/2)^2+h*Real.sin (Real.pi*t/2)^2)-
      (g*Real.cos (Real.pi*s/2)^2+h*Real.sin (Real.pi*s/2)^2) =
      (h-g)*(Real.sin (Real.pi*t/2)-Real.sin (Real.pi*s/2))*
        (Real.sin (Real.pi*t/2)+Real.sin (Real.pi*s/2)) := by
    linear_combination g*hc-g*hd
  rw [he, abs_mul, abs_mul]
  have hb : |Real.sin (Real.pi*t/2)+Real.sin (Real.pi*s/2)| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith [Real.abs_sin_le_one (Real.pi*t/2), Real.abs_sin_le_one (Real.pi*s/2)])
  have hs := Real.abs_sin_sub_sin_le (Real.pi*t/2) (Real.pi*s/2)
  have ha : |Real.pi*t/2-Real.pi*s/2| = Real.pi/2*|t-s| := by
    rw [show Real.pi*t/2-Real.pi*s/2 = (Real.pi/2)*(t-s) by ring,
      abs_mul, abs_of_pos (by positivity : 0 < Real.pi/2)]
  calc
    _ ≤ (|h-g| *(Real.pi/2*|t-s|))*2 := by gcongr; rwa [ha] at hs
    _ = _ := by ring

/-- Telescoping across the fine grid gives a Lipschitz constant proportional only to the coarse rank. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_abs_sub_le
lemma smoothedTent_abs_sub_le (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M/2) → Bool) (x z : unitInterval) :
    |smoothedTent K M σ x-smoothedTent K M σ z| ≤ 32*(M:ℝ)*|(x:ℝ)-(z:ℝ)| := by
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  let G (j : ℕ) (t : ℝ) := coarseTent M σ ((j:ℝ)/K)*Real.cos (Real.pi*t/2)^2 +
    coarseTent M σ (((j:ℝ)+1)/K)*Real.sin (Real.pi*t/2)^2
  have hlocal (j : ℕ) (hj : j < K) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
      (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : |G j t-G j s| ≤ (32*(M:ℝ)/K)*|t-s| := by
    have hb := coarseTent_abs_sub_le M σ (((j:ℝ)+1)/K) ((j:ℝ)/K)
    rw [show ((j:ℝ)+1)/K-(j:ℝ)/K = 1/(K:ℝ) by ring,
      abs_of_pos (by positivity : 0 < 1/(K:ℝ))] at hb
    calc
      _ ≤ |coarseTent M σ (((j:ℝ)+1)/K)-coarseTent M σ ((j:ℝ)/K)| *Real.pi*|t-s| :=
        squared_tent_profile_lipschitz _ _ _ _
      _ ≤ (8*(M:ℝ)*(1/K))*4*|t-s| := by gcongr; exact Real.pi_lt_four.le
      _ = _ := by ring
  have hend (j : ℕ) (hj : j+1 < K) : G j 1 = G (j+1) 0 := by
    simp [G, Real.cos_pi_div_two, Real.sin_pi_div_two, Nat.cast_add, Nat.cast_one]
  have hordered (x z : unitInterval) (hxz : (x:ℝ) ≤ (z:ℝ)) :
      |smoothedTent K M σ x-smoothedTent K M σ z| ≤ 32*(M:ℝ)*|(x:ℝ)-(z:ℝ)| := by
    by_cases he : (x:ℝ) = (z:ℝ)
    · have : x = z := Subtype.ext he
      subst z
      simp
    have hstrict : (x:ℝ) < (z:ℝ) := lt_of_le_of_ne hxz he
    have hprod := mul_lt_mul_of_pos_left hstrict hk
    obtain ⟨i, hi, hix, hxi⟩ := frame_cell_index K hK x
    obtain ⟨j, hj, hjz, hzj⟩ := frame_cell_index K hK z
    have hij : i ≤ j := by
      have hlt : (i:ℝ) < ((j+1:ℕ):ℝ) := by push_cast; nlinarith
      have : i < j+1 := by exact_mod_cast hlt
      omega
    have hb := Causalean.Mathlib.Analysis.piecewiseLipschitz_chain_bound K G (32*(M:ℝ)/K)
      hlocal hend i j hij hj ((K:ℝ)*(x:ℝ)-i) ((K:ℝ)*(z:ℝ)-j)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by nlinarith)
    rw [smoothedTent_cell_formula K M hK σ i hi x hix hxi,
      smoothedTent_cell_formula K M hK σ j hj z hjz hzj]
    change |G i ((K:ℝ)*(x:ℝ)-i)-G j ((K:ℝ)*(z:ℝ)-j)| ≤ _
    calc
      _ ≤ _ := hb
      _ = _ := by
        rw [abs_of_nonpos (by linarith : (x:ℝ)-(z:ℝ) ≤ 0)]
        field_simp
        ring
  rcases le_total (x:ℝ) (z:ℝ) with h | h
  · exact hordered x z h
  · rw [abs_sub_comm (smoothedTent K M σ x), abs_sub_comm (x:ℝ)]
    exact hordered z x h

/-- The coarse Lipschitz bound and unit envelope give every Hölder exponent up to one. This statement assumes [the hK condition](hyp:hK), [the hs condition](hyp:hs), [the hs1 condition](hyp:hs1). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_holder_bound
lemma smoothedTent_holder_bound (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M/2) → Bool) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (x z : unitInterval) :
    |smoothedTent K M σ x-smoothedTent K M σ z| ≤ 32*(M:ℝ)^s*|(x:ℝ)-(z:ℝ)|^s := by
  let d := (M:ℝ)*|(x:ℝ)-(z:ℝ)|
  have hd : 0 ≤ d := by dsimp [d]; positivity
  rw [mul_assoc, ← Real.mul_rpow (Nat.cast_nonneg M) (abs_nonneg _)]
  change _ ≤ 32*d^s
  by_cases hsmall : d ≤ 1
  · have hb := smoothedTent_abs_sub_le K M hK σ x z
    have hr := Real.self_le_rpow_of_le_one hd hsmall hs1
    calc
      _ ≤ 32*d := by simpa only [d, mul_assoc] using hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by norm_num)
  · have hr := Real.one_le_rpow (le_of_not_ge hsmall) hs
    have hb := (abs_sub (smoothedTent K M σ x) (smoothedTent K M σ z)).trans
      (add_le_add (smoothedTent_abs_le_one K M hK σ x) (smoothedTent_abs_le_one K M hK σ z))
    linarith

end CausalSmith.Stat.FinitepHomogeneityDensegamma
