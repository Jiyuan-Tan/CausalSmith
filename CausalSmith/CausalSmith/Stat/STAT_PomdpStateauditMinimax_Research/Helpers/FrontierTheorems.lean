module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.FrontierCollision
public import Causalean.Mathlib.Probability.Birthday.Threshold
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Finite collision and witness lemmas for the clone-budget frontier. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory Filter

-- @node: collisionEnvelope_zero
/-- With no audits, the collision envelope vanishes for every positive clone budget. -/
lemma collisionEnvelope_zero (T m : Nat) (_hm : 1 ≤ m) :
    collisionEnvelope T 0 m = 0 := by
  unfold collisionEnvelope
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hzero : r = 0
  · subst r
    simp
  · have hpos : 0 < r := Nat.pos_of_ne_zero hzero
    simp [hzero]

-- @node: cloneBudget_zero
/-- The least admissible clone budget at zero audit probability is one. -/
lemma cloneBudget_zero (T : Nat) (delta : ℝ)
    (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) :
    cloneBudget T 0 delta hdelta = 1 := by
  unfold cloneBudget
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨by omega, by simpa [collisionEnvelope_zero T 1 (by omega)] using
      (le_of_lt hdelta.1)⟩
  · exact (Nat.sInf_mem (show {m : Nat | 1 ≤ m ∧ collisionEnvelope T 0 m ≤ delta}.Nonempty
      from ⟨1, ⟨by omega, by simpa [collisionEnvelope_zero T 1 (by omega)] using
        (le_of_lt hdelta.1)⟩⟩)).1

-- @node: collisionEnvelope_nonneg
/-- The binomial collision envelope is nonnegative on the audit-probability domain. -/
lemma collisionEnvelope_nonneg (T m : Nat) (eta : ℝ)
    (hm : 1 ≤ m) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ collisionEnvelope T eta m := by
  unfold collisionEnvelope
  apply Finset.sum_nonneg
  intro r hr
  have heta0 : 0 ≤ eta := heta.1
  have heta1 : 0 ≤ 1 - eta := sub_nonneg.mpr heta.2
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hfac : (Nat.descFactorial m r : ℝ) ≤ (m : ℝ) ^ r := by
    exact_mod_cast Nat.descFactorial_le_pow m r
  have hlast : 0 ≤ 1 - (Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r := by
    have hpow : 0 < (m : ℝ) ^ r := pow_pos hmpos _
    have hdiv : (Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r ≤ 1 :=
      (div_le_iff₀ hpow).2 (by simpa using hfac)
    linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg heta0 _))
    (pow_nonneg heta1 _)) hlast

-- @node: collisionEnvelope_le_one
/-- The collision envelope is at most the mass of its binomial audit-count law. -/
lemma collisionEnvelope_le_one (T m : Nat) (eta : ℝ)
    (hm : 1 ≤ m) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    collisionEnvelope T eta m ≤ 1 := by
  have hsum : (∑ r ∈ Finset.range (T + 1),
      (Nat.choose T r : ℝ) * eta ^ r * (1 - eta) ^ (T - r)) = 1 := by
    have h := add_pow eta (1 - eta) T
    have hleft : eta + (1 - eta) = (1 : ℝ) := by ring
    rw [hleft, one_pow] at h
    calc
      _ = ∑ r ∈ Finset.range (T + 1),
          eta ^ r * (1 - eta) ^ (T - r) * (Nat.choose T r : ℝ) := by
            apply Finset.sum_congr rfl
            intro r hr
            ring
      _ = 1 := h.symm
  calc
    collisionEnvelope T eta m ≤
      ∑ r ∈ Finset.range (T + 1),
        (Nat.choose T r : ℝ) * eta ^ r * (1 - eta) ^ (T - r) := by
      unfold collisionEnvelope
      apply Finset.sum_le_sum
      intro r hr
      have hw : 0 ≤ (Nat.choose T r : ℝ) * eta ^ r * (1 - eta) ^ (T - r) := by
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg heta.1 _))
          (pow_nonneg (sub_nonneg.mpr heta.2) _)
      have hfac : 0 ≤ (Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r := by positivity
      nlinarith
    _ = 1 := hsum

-- @node: collisionEnvelope_two
/-- With two epochs, a collision requires both audits and matching clone coordinates. -/
lemma collisionEnvelope_two (m : Nat) (hm : 1 ≤ m) (eta : ℝ) :
    collisionEnvelope 2 eta m = eta ^ 2 / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hsub : ((m - 1 : Nat) : ℝ) = (m : ℝ) - 1 := by
    norm_cast
  simp [collisionEnvelope, Finset.sum_range_succ, hsub]
  field_simp
  ring

-- @node: collisionEnvelope_one
/-- A one-epoch experiment cannot contain two audited queries of the same atom. -/
lemma collisionEnvelope_one (m : Nat) (hm : 1 ≤ m) (eta : ℝ) :
    collisionEnvelope 1 eta m = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp [collisionEnvelope, Finset.sum_range_succ, hm0]

-- @node: collisionEnvelope_fullAudit
/-- At full audit probability, only the all-audited binomial cell remains. -/
lemma collisionEnvelope_fullAudit (T m : Nat) :
    collisionEnvelope T 1 m =
      1 - (Nat.descFactorial m T : ℝ) / (m : ℝ) ^ T := by
  unfold collisionEnvelope
  rw [Finset.sum_eq_single T]
  · simp
  · intro r hr hne
    have hlt : r < T := by
      have hle : r ≤ T := by simpa using Finset.mem_range.mp hr
      omega
    have hpos : 0 < T - r := by omega
    simp [hpos.ne']
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

-- @node: collisionEnvelope_fullAudit_overflow
/-- More audited epochs than clone coordinates force a collision at full audit. -/
lemma collisionEnvelope_fullAudit_overflow (T m : Nat) (h : m < T) :
    collisionEnvelope T 1 m = 1 := by
  rw [collisionEnvelope_fullAudit]
  simp [Nat.descFactorial_eq_zero_iff_lt.mpr h]

-- @node: cloneBudget_one
/-- One clone suffices at horizon one for every positive collision tolerance. -/
lemma cloneBudget_one (eta delta : ℝ) (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) :
    cloneBudget 1 eta delta hdelta = 1 := by
  unfold cloneBudget
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨by omega, by simpa [collisionEnvelope_one 1 (by omega) eta] using
      (le_of_lt hdelta.1)⟩
  · exact (Nat.sInf_mem (show {m : Nat | 1 ≤ m ∧ collisionEnvelope 1 eta m ≤ delta}.Nonempty
      from ⟨1, ⟨by omega, by simpa [collisionEnvelope_one 1 (by omega) eta] using
        (le_of_lt hdelta.1)⟩⟩)).1

-- @node: cloneBudget_minimal_of_exists
/-- Once some positive clone multiplicity meets the tolerance, the infimum is
itself admissible and every smaller positive multiplicity exceeds the tolerance. -/
lemma cloneBudget_minimal_of_exists (T : Nat) (eta delta : ℝ)
    (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1)
    (hex : ∃ m : Nat, 1 ≤ m ∧ collisionEnvelope T eta m ≤ delta) :
    1 ≤ cloneBudget T eta delta hdelta ∧
    collisionEnvelope T eta (cloneBudget T eta delta hdelta) ≤ delta ∧
    ∀ m : Nat, 1 ≤ m → m < cloneBudget T eta delta hdelta →
      delta < collisionEnvelope T eta m := by
  let S : Set Nat := {m | 1 ≤ m ∧ collisionEnvelope T eta m ≤ delta}
  have hS : S.Nonempty := hex
  have hmem : cloneBudget T eta delta hdelta ∈ S := by
    simpa [cloneBudget, S] using (Nat.sInf_mem hS)
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro m hm hlt
  have hnot : m ∉ S := by
    intro h
    have hle : cloneBudget T eta delta hdelta ≤ m := by
      simpa [cloneBudget, S] using (Nat.sInf_le h)
    omega
  exact lt_of_not_ge (by
    intro hle
    exact hnot ⟨hm, hle⟩)

-- @node: cloneBudget_fullAudit_cardinality
/-- A full-audit budget meeting a strict collision tolerance has at least one
clone coordinate for each epoch. -/
lemma cloneBudget_fullAudit_cardinality (T : Nat) (delta : ℝ)
    (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1)
    (hex : ∃ m : Nat, 1 ≤ m ∧ collisionEnvelope T 1 m ≤ delta) :
    T ≤ cloneBudget T 1 delta hdelta := by
  have hgood := (cloneBudget_minimal_of_exists T 1 delta hdelta hex).2.1
  by_contra h
  have hlt : cloneBudget T 1 delta hdelta < T := by omega
  rw [collisionEnvelope_fullAudit_overflow T _ hlt] at hgood
  exact (not_le_of_gt hdelta.2) hgood

-- @node: frontier_fixed_permutation_tv_upper
/-- The fixed-permutation audited mixture obeys the collision envelope for every
base law with full-history factorization, including horizons above the label count. -/
lemma frontier_fixed_permutation_tv_upper {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hK : FullFiltrationPomdp M) (hA : FullFiltrationRandomization M)
    (hStart : StationaryStart M) (eta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.tvDist (permutationMixture M hm eta)
      (freshLabelLaw M hn hm eta) ≤ collisionEnvelope T eta m := by
  have hAudit : BernoulliAudits eta M (auditJointLaw eta M) := ⟨heta, rfl⟩
  have h := overflow_safe_fixed_permutation_tv M hn hm hK hA hStart eta hAudit
    auditRecord_atomic_labels
  exact h.2.2.2.2.2.1

-- @node: frontier_collisionEnvelope_upper
/-- The collision envelope is bounded by one and by the audited-pair union bound. -/
lemma frontier_collisionEnvelope_upper (T m : Nat) (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    collisionEnvelope T eta m ≤ min 1 (collisionScale T eta / (m : ℝ)) := by
  apply le_min
  · exact collisionEnvelope_le_one T m eta hm heta
  · calc
      collisionEnvelope T eta m ≤ eta ^ 2 * T * (T - 1) / (2 * m : ℝ) :=
        collisionEnvelope_pair_bound T m hm eta heta
      _ = collisionScale T eta / (m : ℝ) := by
        unfold collisionScale
        ring

-- @node: frontier_cloneBudget_exists
/-- The audited-pair bound tends below every positive tolerance at a finite clone budget. -/
lemma frontier_cloneBudget_exists (T : Nat) (eta delta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hdelta : 0 < delta) :
    ∃ m : Nat, 1 ≤ m ∧ collisionEnvelope T eta m ≤ delta := by
  have hscale : 0 ≤ collisionScale T eta := by
    by_cases hT : T = 0
    · subst T
      simp [collisionScale]
    · have hT' : (1 : ℝ) ≤ T := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
      unfold collisionScale
      positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (collisionScale T eta / delta)
  have hmpos : 1 ≤ m := by
    have hnonneg : 0 ≤ collisionScale T eta / delta := div_nonneg hscale hdelta.le
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro hzero
      subst m
      simp only [Nat.cast_zero] at hm
      exact (not_lt_of_ge hnonneg) hm)
  refine ⟨m, hmpos, ?_⟩
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  calc
    collisionEnvelope T eta m ≤ collisionScale T eta / (m : ℝ) :=
      (frontier_collisionEnvelope_upper T m hmpos eta heta).trans (min_le_right _ _)
    _ ≤ delta := by
      apply (div_le_iff₀ hmreal).2
      exact (le_of_lt ((div_lt_iff₀ hdelta).1 hm)).trans_eq (mul_comm _ _)

-- @node: probeConstantPath
noncomputable def probeConstantPath (T n k : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    FullPath T 1 n k :=
  (fun _ => ((⟨0, by omega⟩ : Fin 1), (⟨0, by omega⟩ : Fin n)),
    fun _ => ((⟨0, by omega⟩ : Fin k), 0))

-- @node: probeConstantModel
noncomputable def probeConstantModel (T n k : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    PomdpModel T 1 n k where
  K := fun _ _ => Measure.dirac (0,
    ((⟨0, by omega⟩ : Fin 1), (⟨0, by omega⟩ : Fin n)))
  b := fun _ a => if a = (⟨0, by omega⟩ : Fin k) then 1 else 0
  e := fun _ a => if a = (⟨0, by omega⟩ : Fin k) then 1 else 0
  law := Measure.dirac (probeConstantPath T n k hn hk)
  law_prob := by infer_instance

-- @node: collisionEnvelope_eq_birthdayRepeat
lemma collisionEnvelope_eq_birthdayRepeat (T m : Nat) (eta : ℝ) :
    collisionEnvelope T eta m =
      Causalean.Mathlib.Probability.Birthday.birthdayRepeat T m eta := by
  rfl

-- @node: collisionScale_eq_birthdayPairScale
lemma collisionScale_eq_birthdayPairScale (T : Nat) (eta : ℝ) :
    collisionScale T eta =
      Causalean.Mathlib.Probability.Birthday.pairScale T eta := by
  unfold collisionScale Causalean.Mathlib.Probability.Birthday.pairScale
  rw [Nat.cast_choose_two]
  ring

-- @node: cloneBudget_eq_birthdayMStar
lemma cloneBudget_eq_birthdayMStar (T : Nat) (eta delta : ℝ)
    (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) :
    cloneBudget T eta delta hdelta =
      Causalean.Mathlib.Probability.Birthday.mStar T eta delta := by
  simp only [cloneBudget, Causalean.Mathlib.Probability.Birthday.mStar,
    collisionEnvelope_eq_birthdayRepeat, Nat.lt_iff_add_one_le]

end CausalSmith.Stat.PomdpStateauditMinimax
