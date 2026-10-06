module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentPartition

/-! Fine-grid geometry and disclosure localization for component coefficient blocks. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Replacing disclosed coordinates by their observed values leaves undisclosed coordinates untouched. This makes shared disclosed coordinates deterministic. This statement assumes [the δ parameter](hyp:δ), [the p parameter](hyp:p). [This is the stated defined object](goal). -/
-- @node: disclosureClamp
def disclosureClamp {K : ℕ} (δ : Disclosure K) (p : CoefficientPairs K) :
    CoefficientPairs K := fun i => (δ i).getD (p i)

/-- Every coefficient vector with nonzero conditional mass agrees with its disclosure. This statement assumes [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_nonzero_clamp
lemma conditionalPairWeight_nonzero_clamp (ν : Bool) (K M : ℕ)
    (σ : Fin (M / 2) → Bool) (δ : Disclosure K) (p : CoefficientPairs K)
    (hp : conditionalPairWeight ν K M σ δ p ≠ 0) : disclosureClamp δ p = p := by
  classical
  funext i
  cases hd : δ i with
  | none => simp [disclosureClamp, hd]
  | some q =>
    have he : p i = q := by
      by_contra hne
      apply hp
      unfold conditionalPairWeight
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hd, hne]
    simp [disclosureClamp, hd, he]

/-- A likelihood can be evaluated with disclosed coefficients fixed before averaging: vectors inconsistent with those coefficients have exactly zero prior mass. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_clamp_average
lemma conditionalPairWeight_clamp_average (ν : Bool) (K M : ℕ)
    (σ : Fin (M / 2) → Bool) (δ : Disclosure K) (f : CoefficientPairs K → ℝ) :
    (∑ p, conditionalPairWeight ν K M σ δ p * f (disclosureClamp δ p)) =
      ∑ p, conditionalPairWeight ν K M σ δ p * f p := by
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : conditionalPairWeight ν K M σ δ p = 0
  · rw [hp, zero_mul, zero_mul]
  · rw [conditionalPairWeight_nonzero_clamp ν K M σ δ p hp]

/-- The undisclosed coefficient coordinates that are active on at least one record of a component. This statement assumes [the aug parameter](hyp:aug), [the C parameter](hyp:C). [This is the stated defined object](goal). -/
-- @node: activeUndisclosedSupport
def activeUndisclosedSupport {n K : ℕ} (aug : Augmentation n K)
    (C : Finset (Fin n)) : Finset (Fin (K + 1)) :=
  Finset.univ.filter fun j =>
    aug.2.2 j = none ∧ ∃ i ∈ C, frameCoord K j (aug.1 i) ≠ 0

/-- A nonzero frame coordinate is one of the two nodes adjacent to the covariate's fine cell. This statement assumes [the hK condition](hyp:hK), [the hj condition](hyp:hj). [This is the stated conclusion](goal). -/
-- @node: frameCoord_nonzero_fineIndex
lemma frameCoord_nonzero_fineIndex (K : ℕ) (hK : 0 < K) (x : unitInterval)
    (j : Fin (K + 1)) (hj : frameCoord K j x ≠ 0) :
    j.val = fineIndex K x ∨ j.val = fineIndex K x + 1 := by
  have hd := abs_lt.mp (frameCoord_nonzero_distance K hK j x hj)
  by_cases hx : x = 1
  · subst x
    have hone : (((1 : unitInterval) : ℝ) = 1) := rfl
    simp only [hone, mul_one] at hd
    simp only [fineIndex, hone, mul_one, Nat.floor_natCast,
      Nat.min_eq_left (by omega : K - 1 ≤ K)]
    have hjK : j.val = K := by
      have hle : j.val ≤ K := by omega
      have hlt : (K : ℝ) < (j.val : ℝ) + 1 := by linarith [hd.2]
      have hlt' : K < j.val + 1 := by exact_mod_cast hlt
      omega
    omega
  · have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 (by
      intro he
      apply hx
      exact Subtype.ext he)
    have hfloor : Nat.floor ((K : ℝ) * (x : ℝ)) < K :=
      (Nat.floor_lt (mul_nonneg (by positivity) x.property.1)).2 (by
        have hKr : (0 : ℝ) < K := by exact_mod_cast hK
        nlinarith)
    unfold fineIndex
    rw [Nat.min_eq_right (by omega)]
    have hflo := Nat.floor_le (mul_nonneg (by positivity : (0 : ℝ) ≤ K) x.property.1)
    have hfup := Nat.lt_floor_add_one ((K : ℝ) * (x : ℝ))
    have hlo : Nat.floor ((K : ℝ) * (x : ℝ)) < j.val + 1 := by
      exact_mod_cast (show (Nat.floor ((K : ℝ) * (x : ℝ)) : ℝ) < j.val + 1 by
        linarith [hd.1])
    have hup : j.val < Nat.floor ((K : ℝ) * (x : ℝ)) + 2 := by
      exact_mod_cast (show (j.val : ℝ) < Nat.floor ((K : ℝ) * (x : ℝ)) + 2 by
        linarith [hd.2])
    omega

/-- Fine-cell indices refine coarse-cell indices when the ranks divide. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv). [This is the stated conclusion](goal). -/
-- @node: fineIndex_refinement
lemma fineIndex_refinement (K M : ℕ) (hK : 0 < K) (hM : 0 < M)
    (hdiv : M ∣ K) (x : unitInterval) :
    fineIndex K x / (K / M) = fineIndex M x := by
  let q := K / M
  have hKM : M * q = K := Nat.mul_div_cancel' hdiv
  have hq : 0 < q := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hK hdiv
    · exact hM
  by_cases hx : x = 1
  · subst x
    have hone : (((1 : unitInterval) : ℝ) = 1) := rfl
    simp only [fineIndex, hone, mul_one, Nat.floor_natCast,
      Nat.min_eq_left (by omega : K - 1 ≤ K), Nat.min_eq_left (by omega : M - 1 ≤ M)]
    change (K - 1) / q = M - 1
    apply Nat.div_eq_of_lt_le (k := M - 1)
    · have hlt : (M - 1) * q < M * q :=
        Nat.mul_lt_mul_of_pos_right (Nat.sub_lt hM (by omega)) hq
      omega
    · have hMs : M - 1 + 1 = M := by omega
      rw [hMs, hKM]
      omega
  · have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 (by
      intro he
      apply hx
      exact Subtype.ext he)
    have hfloorK : Nat.floor ((K : ℝ) * (x : ℝ)) < K :=
      (Nat.floor_lt (mul_nonneg (by positivity) x.property.1)).2 (by
        have hKR : (0 : ℝ) < K := by exact_mod_cast hK
        nlinarith)
    have hfloorM : Nat.floor ((M : ℝ) * (x : ℝ)) < M :=
      (Nat.floor_lt (mul_nonneg (by positivity) x.property.1)).2 (by
        have hMR : (0 : ℝ) < M := by exact_mod_cast hM
        nlinarith)
    unfold fineIndex
    rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
    change Nat.floor ((K : ℝ) * (x : ℝ)) / q = _
    have hKMR : (K : ℝ) = (M : ℝ) * (q : ℝ) := by exact_mod_cast hKM.symm
    calc
      _ = Nat.floor (((M : ℝ) * (x : ℝ)) * q) / q := by
        congr 2
        rw [hKMR]
        ring
      _ = Nat.floor ((M : ℝ) * (x : ℝ)) :=
        Nat.mul_cast_floor_div_cancel hq.ne' ((M : ℝ) * (x : ℝ))

/-- Two records activating the same undisclosed node are joined by the component relation. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the hactual condition](hyp:hactual), [the hji condition](hyp:hji), [the hjk condition](hyp:hjk), [the hjnone condition](hyp:hjnone). [This is the stated conclusion](goal). -/
-- @node: componentEdge_of_shared_active_undisclosed
lemma componentEdge_of_shared_active_undisclosed (n K M : ℕ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K)
    (aug : Augmentation n K) (q : CoefficientPairs K)
    (hactual : aug.2.2 = disclose K M q)
    {i k : Fin n} {j : Fin (K + 1)}
    (hji : frameCoord K j (aug.1 i) ≠ 0)
    (hjk : frameCoord K j (aug.1 k) ≠ 0)
    (hjnone : aug.2.2 j = none) :
    componentEdge n K M aug i k := by
  let d := K / M
  have hKM : M * d = K := Nat.mul_div_cancel' hdiv
  have hd : 0 < d := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hK hdiv
    · exact hM
  have hjnot : ¬ boundaryNode K M j := by
    intro hb
    rw [hactual] at hjnone
    simp [disclose, hb] at hjnone
  have hjmod : j.val % d ≠ 0 := by
    intro hz
    apply hjnot
    unfold boundaryNode
    apply Nat.mod_eq_zero_of_dvd
    have hdj : d ∣ j.val := (Nat.dvd_iff_mod_eq_zero).2 hz
    obtain ⟨t, ht⟩ := hdj
    use t
    rw [ht, ← hKM]
    ring
  have hjpos : 0 < j.val := by
    apply Nat.pos_of_ne_zero
    intro hz
    simp [hz] at hjmod
  have hpred : (j.val - 1) / d = j.val / d := by
    apply Nat.div_eq_of_lt_le (k := j.val / d)
    · have he : j.val % d + (j.val / d) * d = j.val := by
        simpa [Nat.mul_comm] using Nat.mod_add_div j.val d
      omega
    · have he : j.val % d + (j.val / d) * d = j.val := by
        simpa [Nat.mul_comm] using Nat.mod_add_div j.val d
      have hr := Nat.mod_lt j.val hd
      rw [Nat.add_mul]
      omega
  have hi := frameCoord_nonzero_fineIndex K hK (aug.1 i) j hji
  have hk := frameCoord_nonzero_fineIndex K hK (aug.1 k) j hjk
  have hquot : fineIndex K (aug.1 i) / d = fineIndex K (aug.1 k) / d := by
    rcases hi with hi | hi <;> rcases hk with hk | hk
    · have he : fineIndex K (aug.1 i) = fineIndex K (aug.1 k) := by omega
      rw [he]
    · have hii : fineIndex K (aug.1 i) = j.val := by omega
      have hkk : fineIndex K (aug.1 k) = j.val - 1 := by omega
      rw [hii, hkk, hpred]
    · have hii : fineIndex K (aug.1 i) = j.val - 1 := by omega
      have hkk : fineIndex K (aug.1 k) = j.val := by omega
      rw [hii, hkk, hpred]
    · have he : fineIndex K (aug.1 i) = fineIndex K (aug.1 k) := by omega
      rw [he]
  constructor
  · rw [← fineIndex_refinement K M hK hM hdiv,
      ← fineIndex_refinement K M hK hM hdiv]
    exact hquot
  · have hadj :
        fineIndex K (aug.1 i) = fineIndex K (aug.1 k) ∨
          ((fineIndex K (aug.1 i) + 1 = fineIndex K (aug.1 k) ∨
            fineIndex K (aug.1 k) + 1 = fineIndex K (aug.1 i)) ∧
            max (fineIndex K (aug.1 i)) (fineIndex K (aug.1 k)) = j.val) := by
      rcases hi with hi | hi <;> rcases hk with hk | hk <;> omega
    rcases hadj with heq | ⟨hadj, hmax⟩
    · exact Or.inl heq
    · exact Or.inr ⟨hadj, by rw [hmax]; exact hjnot⟩

/-- Actual boundary disclosure makes the active undisclosed coefficient supports of distinct observation components disjoint. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the hactual condition](hyp:hactual). [This is the stated conclusion](goal). -/
-- @node: activeUndisclosedSupport_pairwiseDisjoint
lemma activeUndisclosedSupport_pairwiseDisjoint (n K M : ℕ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K)
    (aug : Augmentation n K)
    (hactual : ∃ q : CoefficientPairs K, aug.2.2 = disclose K M q) :
    (↑(components n K M aug) : Set (Finset (Fin n))).PairwiseDisjoint
      (activeUndisclosedSupport aug) := by
  classical
  obtain ⟨q, hq⟩ := hactual
  intro C hC D hD hne
  apply Finset.disjoint_left.mpr
  intro j hjC hjD
  obtain ⟨hjnone, i, hiC, hji⟩ := Finset.mem_filter.mp hjC |>.2
  obtain ⟨_, k, hkD, hjk⟩ := Finset.mem_filter.mp hjD |>.2
  have hedge := componentEdge_of_shared_active_undisclosed n K M hK hM hdiv
    aug q hq hji hjk hjnone
  apply hne
  rw [← componentOf_eq_of_mem n K M aug hC hiC,
    ← componentOf_eq_of_mem n K M aug hD hkD]
  exact componentOf_eq_of_connected n K M aug (.single hedge)

/-- For positive even coarse rank, the pair containing any coarse cell is a valid sign index. This statement assumes [the hM condition](hyp:hM), [the heven condition](hyp:heven). [This is the stated conclusion](goal). -/
-- @node: fineIndex_half_lt
lemma fineIndex_half_lt (M : ℕ) (hM : 0 < M) (heven : 2 ∣ M)
    (x : unitInterval) : fineIndex M x / 2 < M / 2 := by
  have hle : fineIndex M x ≤ M - 1 := by
    unfold fineIndex
    exact (Nat.min_le_left _ _).trans (by omega)
  obtain ⟨m, hm⟩ := heven
  omega

/-- Every enumerated component owns a valid paired coarse-sign coordinate. This statement assumes [the hM condition](hyp:hM), [the heven condition](hyp:heven), [the hC condition](hyp:hC). [This is the stated conclusion](goal). -/
-- @node: pairIndex_lt_half
lemma pairIndex_lt_half (n K M : ℕ) (hM : 0 < M) (heven : 2 ∣ M)
    (aug : Augmentation n K) {C : Finset (Fin n)}
    (hC : C ∈ components n K M aug) : pairIndex M aug C < M / 2 := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
  rw [pairIndex_eq_of_mem_component n K M aug
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    (self_mem_componentOf n K M aug i)]
  exact fineIndex_half_lt M hM heven (aug.1 i)

/-- At a covariate point, a paired coarse tent depends only on the sign owning its coarse cell. This statement assumes [the hM condition](hyp:hM), [the heven condition](hyp:heven), [the hστ condition](hyp:hστ). [This is the stated conclusion](goal). -/
-- @node: coarseTent_eq_of_eq_fineIndex_pair
lemma coarseTent_eq_of_eq_fineIndex_pair (M : ℕ) (hM : 0 < M) (heven : 2 ∣ M)
    (σ τ : Fin (M / 2) → Bool) (x : unitInterval)
    (hστ : σ ⟨fineIndex M x / 2, fineIndex_half_lt M hM heven x⟩ =
      τ ⟨fineIndex M x / 2, fineIndex_half_lt M hM heven x⟩) :
    coarseTent M σ x = coarseTent M τ x := by
  classical
  unfold coarseTent
  apply Finset.sum_congr rfl
  intro l _
  let f := tentBase ((M : ℝ) * (x : ℝ) - 2 * l.val) -
    tentBase ((M : ℝ) * (x : ℝ) - (2 * l.val + 1))
  by_cases hf : f = 0
  · simp [f, hf]
  have hs := coarseTent_pair_support M (x : ℝ) l hf
  have heven' := heven
  obtain ⟨m, hm⟩ := heven
  have hlM : 2 * l.val + 2 ≤ M := by
    rw [hm] at l
    omega
  have hxlt : (x : ℝ) < 1 := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have htop : (M : ℝ) * (x : ℝ) < M := by
      exact lt_of_lt_of_le hs.2 (by exact_mod_cast hlM)
    nlinarith
  have hxne : x ≠ 1 := by
    intro hx
    subst x
    norm_num at hxlt
  have hfloor : Nat.floor ((M : ℝ) * (x : ℝ)) < M :=
    (Nat.floor_lt (mul_nonneg (by positivity) x.property.1)).2 (by
      have hMr : (0 : ℝ) < M := by exact_mod_cast hM
      nlinarith)
  have hfi : fineIndex M x = Nat.floor ((M : ℝ) * (x : ℝ)) := by
    unfold fineIndex
    rw [Nat.min_eq_right (by omega)]
  have hfl := Nat.floor_le (mul_nonneg (by positivity : (0 : ℝ) ≤ M) x.property.1)
  have hfu := Nat.lt_floor_add_one ((M : ℝ) * (x : ℝ))
  have hlo : 2 * l.val < Nat.floor ((M : ℝ) * (x : ℝ)) + 1 := by
    exact_mod_cast (show (2 * l.val : ℝ) < Nat.floor ((M : ℝ) * (x : ℝ)) + 1 by
      linarith [hs.1, hfu])
  have hup : Nat.floor ((M : ℝ) * (x : ℝ)) < 2 * l.val + 2 := by
    exact_mod_cast (show (Nat.floor ((M : ℝ) * (x : ℝ)) : ℝ) < 2 * l.val + 2 by
      linarith [hs.2, hfl])
  have hl : l.val = fineIndex M x / 2 := by
    rw [hfi]
    omega
  have hleq : l = ⟨fineIndex M x / 2, fineIndex_half_lt M hM heven' x⟩ := Fin.ext hl
  rw [hleq, hστ]

/-- At every active undisclosed node of a component, the global coarse tent can be replaced by the constant sign carried by that component's owning pair. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven), [the hactual condition](hyp:hactual), [the hC condition](hyp:hC), [the hj condition](hyp:hj). [This is the stated conclusion](goal). -/
-- @node: coarseTent_activeUndisclosedSupport_local
lemma coarseTent_activeUndisclosedSupport_local (n K M : ℕ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (aug : Augmentation n K)
    (hactual : ∃ q : CoefficientPairs K, aug.2.2 = disclose K M q)
    {C : Finset (Fin n)} (hC : C ∈ components n K M aug)
    {j : Fin (K + 1)} (hj : j ∈ activeUndisclosedSupport aug C)
    (σ : Fin (M / 2) → Bool) :
    coarseTent M σ ((j : ℝ) / K) =
      coarseTent M
        (fun _ => σ ⟨pairIndex M aug C, pairIndex_lt_half n K M hM heven aug hC⟩)
        ((j : ℝ) / K) := by
  obtain ⟨q, hq⟩ := hactual
  obtain ⟨hjnone, i, hiC, hji⟩ := Finset.mem_filter.mp hj |>.2
  have hjnot : ¬ boundaryNode K M j := by
    intro hb
    rw [hq] at hjnone
    simp [disclose, hb] at hjnone
  have hjle : j.val ≤ K := by omega
  have hjlt : j.val < K := by
    by_contra h
    have hjeq : j.val = K := by omega
    apply hjnot
    unfold boundaryNode
    rw [hjeq]
    simp
  let d := K / M
  have hKM : M * d = K := Nat.mul_div_cancel' hdiv
  have hd : 0 < d := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hK hdiv
    · exact hM
  have hjmod : j.val % d ≠ 0 := by
    intro hz
    apply hjnot
    unfold boundaryNode
    apply Nat.mod_eq_zero_of_dvd
    have hdj : d ∣ j.val := (Nat.dvd_iff_mod_eq_zero).2 hz
    obtain ⟨t, ht⟩ := hdj
    use t
    rw [ht, ← hKM]
    ring
  have hjpos : 0 < j.val := by
    apply Nat.pos_of_ne_zero
    intro hz
    simp [hz] at hjmod
  have hpred : (j.val - 1) / d = j.val / d := by
    apply Nat.div_eq_of_lt_le (k := j.val / d)
    · have he : j.val % d + (j.val / d) * d = j.val := by
        simpa [Nat.mul_comm] using Nat.mod_add_div j.val d
      omega
    · have he : j.val % d + (j.val / d) * d = j.val := by
        simpa [Nat.mul_comm] using Nat.mod_add_div j.val d
      have hr := Nat.mod_lt j.val hd
      rw [Nat.add_mul]
      omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  let xj : unitInterval :=
    ⟨(j : ℝ) / K, div_nonneg (by positivity) hKr.le,
      (div_le_one hKr).2 (by exact_mod_cast hjle)⟩
  have hgridK : fineIndex K xj = j.val := by
    have hratio : (K : ℝ) * (xj : ℝ) = j.val := by
      dsimp [xj]
      field_simp
    unfold fineIndex
    rw [hratio, Nat.floor_natCast, Nat.min_eq_right (by omega)]
  have hactive := frameCoord_nonzero_fineIndex K hK (aug.1 i) j hji
  have hquot : fineIndex K xj / d = fineIndex K (aug.1 i) / d := by
    rw [hgridK]
    rcases hactive with hi | hi
    · have he : fineIndex K (aug.1 i) = j.val := by omega
      rw [he]
    · have he : fineIndex K (aug.1 i) = j.val - 1 := by omega
      rw [he, hpred]
  have hcoarse : fineIndex M xj = fineIndex M (aug.1 i) := by
    rw [← fineIndex_refinement K M hK hM hdiv,
      ← fineIndex_refinement K M hK hM hdiv]
    exact hquot
  have hpair : fineIndex M xj / 2 = pairIndex M aug C := by
    rw [pairIndex_eq_of_mem_component n K M aug hC hiC, hcoarse]
  change coarseTent M σ xj =
    coarseTent M
      (fun _ => σ ⟨pairIndex M aug C, pairIndex_lt_half n K M hM heven aug hC⟩) xj
  apply coarseTent_eq_of_eq_fineIndex_pair M hM heven
  congr 1
  exact Fin.ext hpair

/-- Clamping makes a component frame field depend only on its active undisclosed support. This statement assumes [the hp condition](hyp:hp), [the hi condition](hyp:hi). [This is the stated conclusion](goal). -/
-- @node: disclosureClamp_frameField_local
lemma disclosureClamp_frameField_local {n K : ℕ} (aug : Augmentation n K)
    (C : Finset (Fin n)) (p p' : CoefficientPairs K)
    (hp : ∀ j ∈ activeUndisclosedSupport aug C, p j = p' j)
    (i : Fin n) (hi : i ∈ C) (r : Bool) :
    frameField K (fun j => signVal (if r then (disclosureClamp aug.2.2 p j).1
      else (disclosureClamp aug.2.2 p j).2)) (aug.1 i) =
    frameField K (fun j => signVal (if r then (disclosureClamp aug.2.2 p' j).1
      else (disclosureClamp aug.2.2 p' j).2)) (aug.1 i) := by
  unfold frameField
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : frameCoord K j (aug.1 i) = 0
  · simp [hj]
  congr 1
  cases hd : aug.2.2 j with
  | some q => simp [disclosureClamp, hd]
  | none =>
      have hjS : j ∈ activeUndisclosedSupport aug C := by
        simp only [activeUndisclosedSupport, Finset.mem_filter, Finset.mem_univ, true_and, hd]
        exact ⟨i, hi, hj⟩
      simp only [disclosureClamp, hd, Option.getD_none]
      rw [hp j hjS]

/-- The clamped component likelihood depends only on its active undisclosed coefficient support. This statement assumes [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: componentLikelihood_clamp_local
lemma componentLikelihood_clamp_local (ν : Bool) {n K M : ℕ} (a u : ℝ)
    (σ : Fin (M / 2) → Bool) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) (p p' : CoefficientPairs K)
    (hp : ∀ j ∈ activeUndisclosedSupport aug C, p j = p' j) :
    (∏ i ∈ C, labelDensity ν K M a u (σ, disclosureClamp aug.2.2 p)
      (aug.1 i) (aug.2.1 i) (labels i)) =
    ∏ i ∈ C, labelDensity ν K M a u (σ, disclosureClamp aug.2.2 p')
      (aug.1 i) (aug.2.1 i) (labels i) := by
  apply Finset.prod_congr rfl
  intro i hi
  have hxi : frameField K (fun j => signVal (disclosureClamp aug.2.2 p j).1) (aug.1 i) =
      frameField K (fun j => signVal (disclosureClamp aug.2.2 p' j).1) (aug.1 i) := by
    simpa using disclosureClamp_frameField_local aug C p p' hp i hi true
  have hupsilon : frameField K (fun j => signVal (disclosureClamp aug.2.2 p j).2) (aug.1 i) =
      frameField K (fun j => signVal (disclosureClamp aug.2.2 p' j).2) (aug.1 i) := by
    simpa using disclosureClamp_frameField_local aug C p p' hp i hi false
  unfold labelDensity copulaZeta copulaXi copulaUpsilon copulaT
  rw [hxi, hupsilon]

end CausalSmith.Stat.FinitepHomogeneityDensegamma
