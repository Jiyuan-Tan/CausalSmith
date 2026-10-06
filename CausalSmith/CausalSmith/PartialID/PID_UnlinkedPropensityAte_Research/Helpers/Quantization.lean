module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.OrderedIntervalPartition
public import Causalean.Mathlib.Analysis.Quantization.Main
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Paired scalar quantization with a common measurable partition. -/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:S,k,β,B,z), [this definition](goal) introduces the corresponding object. -/
def pairedPartitionCost (S k : ℕ) (β : Fin S → ℝ → ℝ → ℝ)
    (B : Fin k → Set ℝ) (z : Fin k → Fin S → ℝ) : ℝ :=
  ∑ j : Fin k, ∑ s : Fin S,
    ∫ x in B j, β s x (z j s) * |x - z j s|

/-- For [the specified mathematical inputs](hyp:a,b,S,k,β), [this definition](goal) introduces the corresponding object. -/
def optimalPairedCost (a b : ℝ) (S k : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ (B : Fin k → Set ℝ) (z : Fin k → Fin S → ℝ),
    IsIntervalPartition a b k B ∧
      (∀ j s, z j s ∈ Set.Icc a b) ∧
      v = pairedPartitionCost S k β B z}

/-- For [the specified mathematical inputs](hyp:S,β,x), [this definition](goal) introduces the corresponding object. -/
def pairedDiagonalWeight (S : ℕ) (β : Fin S → ℝ → ℝ → ℝ)
    (x : ℝ) : ℝ :=
  ∑ s : Fin S, β s x x

-- @node: pairedDiagonalWeight_pos
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,S,hS,β,hpos,x,hx), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedDiagonalWeight_pos (a b : ℝ) (S : ℕ) (hS : 0 < S)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z)
    (x : ℝ) (hx : x ∈ Set.Icc a b) :
    0 < pairedDiagonalWeight S β x := by
  unfold pairedDiagonalWeight
  have : Nonempty (Fin S) := Fin.pos_iff_nonempty.mp hS
  exact Finset.sum_pos (fun s _ => hpos s x x hx hx) Finset.univ_nonempty

-- @node: pairedDiagonalWeight_continuousOn
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,S,β,hcont), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedDiagonalWeight_continuousOn (a b : ℝ) (S : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn
      (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b)) :
    ContinuousOn (pairedDiagonalWeight S β) (Set.Icc a b) := by
  unfold pairedDiagonalWeight
  apply continuousOn_finsetSum
  intro s hs
  exact (hcont s).comp (continuousOn_id.prodMk continuousOn_id)
    (fun x hx => ⟨hx, hx⟩)

-- @node: pairedDiagonalWeight_uniform_bounds
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,S,hS,β,hcont,hpos), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedDiagonalWeight_uniform_bounds (a b : ℝ)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn
      (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ Set.Icc a b,
      c ≤ pairedDiagonalWeight S β x ∧ pairedDiagonalWeight S β x ≤ C := by
  have hc := pairedDiagonalWeight_continuousOn a b S β hcont
  obtain ⟨c, hcpos, hclower⟩ :=
    isCompact_Icc.exists_forall_le' hc (fun x hx =>
      pairedDiagonalWeight_pos a b S hS β hpos x hx)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨c, C, hcpos, ?_⟩
  intro x hx
  exact ⟨hclower x hx, le_trans (le_abs_self _) (by simpa using hC x hx)⟩

-- @node: pairedCoefficient_uniform_bounds
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab,β,hcont,hpos), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedCoefficient_uniform_bounds (a b : ℝ) (hab : a ≤ b)
    (β : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => β p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β x z) :
    ∃ c C : ℝ, 0 < c ∧
      ∀ x ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b, c ≤ β x z ∧ β x z ≤ C := by
  have hcompact : IsCompact (Set.Icc a b ×ˢ Set.Icc a b) :=
    isCompact_Icc.prod isCompact_Icc
  have hne : (Set.Icc a b ×ˢ Set.Icc a b).Nonempty :=
    ⟨(a, a), ⟨⟨le_refl a, hab⟩, ⟨le_refl a, hab⟩⟩⟩
  obtain ⟨c, hcpos, hclower⟩ :=
    hcompact.exists_forall_le' hcont (fun p hp => hpos p.1 p.2 hp.1 hp.2)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨c, C, hcpos, ?_⟩
  intro x hx z hz
  exact ⟨hclower (x, z) ⟨hx, hz⟩,
    le_trans (le_abs_self _) (by simpa using hC (x, z) ⟨hx, hz⟩)⟩

-- @node: pairedCoefficients_uniform_bounds
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab,S,hS,β,hcont,hpos), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedCoefficients_uniform_bounds (a b : ℝ) (hab : a ≤ b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn
      (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∃ c C : ℝ, 0 < c ∧
      ∀ s, ∀ x ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b, c ≤ β s x z ∧ β s x z ≤ C := by
  classical
  have hsingle : ∀ s : Fin S, ∃ c C : ℝ, 0 < c ∧
      ∀ x ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
        c ≤ β s x z ∧ β s x z ≤ C := by
    intro s
    exact pairedCoefficient_uniform_bounds a b hab (β s) (hcont s) (hpos s)
  choose c C hc hbound using hsingle
  have hne : (Finset.univ : Finset (Fin S)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hS)
  obtain ⟨smin, _, hmin⟩ := Finset.exists_min_image Finset.univ c hne
  obtain ⟨smax, _, hmax⟩ := Finset.exists_max_image Finset.univ C hne
  refine ⟨c smin, C smax, hc smin, ?_⟩
  intro s x hx z hz
  have hsmin := hmin s (Finset.mem_univ s)
  have hsmax := hmax s (Finset.mem_univ s)
  exact ⟨hsmin.trans (hbound s x hx z hz).1,
    (hbound s x hx z hz).2.trans hsmax⟩

/-- For [the specified mathematical inputs](hyp:a,b,S,k,j,β), [this definition](goal) introduces the corresponding object. -/
def pairedBoundary (a b : ℝ) (S k j : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ Set.Icc a b ∧
    (j : ℝ) / k *
      (∫ t in a..b, Real.sqrt (pairedDiagonalWeight S β t)) ≤
        ∫ t in a..x, Real.sqrt (pairedDiagonalWeight S β t)}

-- @node: pairedBoundary_zero
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab,S,k,β), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedBoundary_zero (a b : ℝ) (hab : a ≤ b) (S k : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) :
    pairedBoundary a b S k 0 β = a := by
  unfold pairedBoundary
  apply IsLeast.csInf_eq
  constructor
  · simp [hab]
  · rintro x ⟨hx, _⟩
    exact hx.1

-- @node: pairedBoundary_mem_Icc
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab,S,k,j,hk,hj,β), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedBoundary_mem_Icc (a b : ℝ) (hab : a ≤ b) (S k j : ℕ)
    (hk : 0 < k) (hj : j ≤ k)
    (β : Fin S → ℝ → ℝ → ℝ) :
    pairedBoundary a b S k j β ∈ Set.Icc a b := by
  let I : ℝ := ∫ t in a..b, Real.sqrt (pairedDiagonalWeight S β t)
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg_of_forall hab
    (fun t => Real.sqrt_nonneg _)
  have hjk : (j : ℝ) / k ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hk)).mpr
    exact_mod_cast hj
  have hratio : 0 ≤ (j : ℝ) / k := by positivity
  have hfeasible : b ∈ {x : ℝ | x ∈ Set.Icc a b ∧
      (j : ℝ) / k * I ≤ ∫ t in a..x, Real.sqrt (pairedDiagonalWeight S β t)} := by
    refine ⟨⟨hab, le_refl b⟩, ?_⟩
    simpa [I] using mul_le_of_le_one_left hI hjk
  have hlower : a ≤ sInf {x : ℝ | x ∈ Set.Icc a b ∧
      (j : ℝ) / k * I ≤ ∫ t in a..x, Real.sqrt (pairedDiagonalWeight S β t)} := by
    apply le_csInf ⟨b, hfeasible⟩
    rintro x ⟨hx, _⟩
    exact hx.1
  have hupper : sInf {x : ℝ | x ∈ Set.Icc a b ∧
      (j : ℝ) / k * I ≤ ∫ t in a..x, Real.sqrt (pairedDiagonalWeight S β t)} ≤ b := by
    apply csInf_le ⟨a, ?_⟩ hfeasible
    rintro x ⟨hx, _⟩
    exact hx.1
  exact ⟨hlower, hupper⟩

-- @node: pairedBoundary_mono
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab,S,k,i,j,hk,hij,hj,β), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedBoundary_mono (a b : ℝ) (hab : a ≤ b) (S k i j : ℕ)
    (hk : 0 < k) (hij : i ≤ j) (hj : j ≤ k)
    (β : Fin S → ℝ → ℝ → ℝ) :
    pairedBoundary a b S k i β ≤ pairedBoundary a b S k j β := by
  let I : ℝ := ∫ t in a..b, Real.sqrt (pairedDiagonalWeight S β t)
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg_of_forall hab
    (fun t => Real.sqrt_nonneg _)
  have hsubset :
      {x : ℝ | x ∈ Set.Icc a b ∧ (j : ℝ) / k * I ≤
        ∫ t in a..x, Real.sqrt (pairedDiagonalWeight S β t)} ⊆
      {x : ℝ | x ∈ Set.Icc a b ∧ (i : ℝ) / k * I ≤
        ∫ t in a..x, Real.sqrt (pairedDiagonalWeight S β t)} := by
    rintro x ⟨hx, hbound⟩
    refine ⟨hx, ?_⟩
    have hratio : (i : ℝ) / k ≤ (j : ℝ) / k := by
      apply div_le_div_of_nonneg_right (by exact_mod_cast hij)
      exact_mod_cast hk.le
    exact (mul_le_mul_of_nonneg_right hratio hI).trans hbound
  unfold pairedBoundary
  change sInf {x : ℝ | x ∈ Set.Icc a b ∧ (i : ℝ) / k * I ≤
      ∫ t in a..x, Real.sqrt (pairedDiagonalWeight S β t)} ≤
    sInf {x : ℝ | x ∈ Set.Icc a b ∧ (j : ℝ) / k * I ≤
      ∫ t in a..x, Real.sqrt (pairedDiagonalWeight S β t)}
  apply le_csInf
  · refine ⟨b, ?_⟩
    have hjk : (j : ℝ) / k ≤ 1 :=
      (div_le_one (by exact_mod_cast hk)).mpr (by exact_mod_cast hj)
    exact ⟨⟨hab, le_refl b⟩, by
      simpa [I] using mul_le_of_le_one_left hI hjk⟩
  · intro x hx
    apply csInf_le
    · exact ⟨a, fun y hy => hy.1.1⟩
    · exact hsubset hx

-- @node: pairedBoundary_last
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab,S,k,hS,hk,β,hcont,hpos), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedBoundary_last (a b : ℝ) (hab : a < b) (S k : ℕ) (hS : 0 < S)
    (hk : 0 < k) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn
      (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    pairedBoundary a b S k k β = b := by
  let f : ℝ → ℝ := fun t => Real.sqrt (pairedDiagonalWeight S β t)
  have hf : ContinuousOn f (Set.Icc a b) := by
    exact Real.continuous_sqrt.continuousOn.comp
      (pairedDiagonalWeight_continuousOn a b S β hcont)
      (fun _ _ => Set.mem_univ _)
  have hfp : ∀ x ∈ Set.Icc a b, 0 < f x := by
    intro x hx
    exact Real.sqrt_pos.2 (pairedDiagonalWeight_pos a b S hS β hpos x hx)
  have hratio : (k : ℝ) / k = 1 :=
    div_self (by exact_mod_cast (Nat.ne_of_gt hk))
  have hset :
      {x : ℝ | x ∈ Set.Icc a b ∧
        (k : ℝ) / k * (∫ t in a..b, f t) ≤ ∫ t in a..x, f t} = {b} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, htarget⟩
      by_contra hne
      have hxb : x < b := lt_of_le_of_ne hx.2 hne
      have hfxb : ContinuousOn f (Set.Icc x b) :=
        hf.mono (Set.Icc_subset_Icc_left hx.1)
      have hposxb : 0 < ∫ t in x..b, f t := by
        apply intervalIntegral.integral_pos hxb hfxb
        · intro t ht
          exact (hfp t ⟨hx.1.trans ht.1.le, ht.2⟩).le
        · exact ⟨x, ⟨le_refl x, hxb.le⟩, hfp x hx⟩
      have hfax : IntervalIntegrable f volume a x :=
        (hf.mono (Set.Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1
      have hfxb' : IntervalIntegrable f volume x b :=
        hfxb.intervalIntegrable_of_Icc hxb.le
      have hadd := intervalIntegral.integral_add_adjacent_intervals hfax hfxb'
      rw [hratio, one_mul] at htarget
      linarith
    · intro h
      subst x
      refine ⟨⟨hab.le, le_refl b⟩, ?_⟩
      rw [hratio, one_mul]
  unfold pairedBoundary
  change sInf {x : ℝ | x ∈ Set.Icc a b ∧
    (k : ℝ) / k * (∫ t in a..b, f t) ≤ ∫ t in a..x, f t} = b
  rw [hset]
  simp

/-- For [the specified mathematical inputs](hyp:a,b,S,k,β,j), [this definition](goal) introduces the corresponding object. -/
def pairedCompandingCell (a b : ℝ) (S k : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) (j : Fin k) : Set ℝ :=
  if j.val + 1 = k then
    Set.Icc (pairedBoundary a b S k j.val β)
      (pairedBoundary a b S k (j.val + 1) β)
  else
    Set.Ico (pairedBoundary a b S k j.val β)
      (pairedBoundary a b S k (j.val + 1) β)

/-- For [the specified mathematical inputs](hyp:a,b,S,k,β,j,_s), [this definition](goal) introduces the corresponding object. -/
def pairedCompandingMidpoint (a b : ℝ) (S k : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) (j : Fin k) (_s : Fin S) : ℝ :=
  (pairedBoundary a b S k j.val β +
    pairedBoundary a b S k (j.val + 1) β) / 2

-- @node: pairedCompandingMidpoint_mem_Icc
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab,S,k,hk,β), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedCompandingMidpoint_mem_Icc (a b : ℝ) (hab : a ≤ b)
    (S k : ℕ) (hk : 0 < k) (β : Fin S → ℝ → ℝ → ℝ) :
    ∀ j s, pairedCompandingMidpoint a b S k β j s ∈ Set.Icc a b := by
  intro j s
  have hleft := pairedBoundary_mem_Icc a b hab S k j.val hk (Nat.le_of_lt j.isLt) β
  have hright := pairedBoundary_mem_Icc a b hab S k (j.val + 1) hk j.isLt β
  unfold pairedCompandingMidpoint
  constructor <;> linarith [hleft.1, hleft.2, hright.1, hright.2]

-- @node: abs_deviation_integral_midpoint
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab), this result [establishes the stated mathematical conclusion](goal). -/
lemma abs_deviation_integral_midpoint (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, |x - (a + b) / 2|) = (b - a) ^ 2 / 4 := by
  let m : ℝ := (a + b) / 2
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hleft : (∫ x in a..m, |x - m|) =
      m * (m - a) - (m ^ 2 - a ^ 2) / 2 := by
    have heq : ∀ x ∈ Set.uIcc a m, |x - m| = m - x := by
      intro x hx
      rw [Set.uIcc_of_le ham] at hx
      rw [abs_of_nonpos (by linarith [hx.2])]
      ring
    rw [intervalIntegral.integral_congr heq]
    rw [intervalIntegral.integral_sub]
    · simp [intervalIntegral.integral_const, integral_id, smul_eq_mul]
      ring
    · exact continuous_const.intervalIntegrable a m
    · exact continuous_id.intervalIntegrable a m
  have hright : (∫ x in m..b, |x - m|) =
      (b ^ 2 - m ^ 2) / 2 - m * (b - m) := by
    have heq : ∀ x ∈ Set.uIcc m b, |x - m| = x - m := by
      intro x hx
      rw [Set.uIcc_of_le hmb] at hx
      exact abs_of_nonneg (by linarith [hx.1])
    rw [intervalIntegral.integral_congr heq]
    rw [intervalIntegral.integral_sub]
    · simp [intervalIntegral.integral_const, integral_id, smul_eq_mul]
      ring
    · exact continuous_id.intervalIntegrable m b
    · exact continuous_const.intervalIntegrable m b
  have hi₁ : IntervalIntegrable (fun x : ℝ => |x - m|) volume a m :=
    (by fun_prop : Continuous (fun x : ℝ => |x - m|)).intervalIntegrable a m
  have hi₂ : IntervalIntegrable (fun x : ℝ => |x - m|) volume m b :=
    (by fun_prop : Continuous (fun x : ℝ => |x - m|)).intervalIntegrable m b
  change (∫ x in a..b, |x - m|) = _
  rw [(intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂).symm,
    hleft, hright]
  dsimp [m]
  ring

-- @node: pairedWeightedAbsDeviation_lower
/-- Given [the stated mathematical inputs and assumptions](hyp:S,γ,z,x,hγ), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedWeightedAbsDeviation_lower {S : ℕ} (γ : Fin S → ℝ)
    (z : Fin S → ℝ) (x : ℝ) (hγ : ∀ s, 0 ≤ γ s) :
    |(∑ s, γ s) * x - ∑ s, γ s * z s| ≤
      ∑ s, γ s * |x - z s| := by
  have hsum : (∑ s, γ s) * x - ∑ s, γ s * z s =
      ∑ s, γ s * (x - z s) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    congr 1
    funext s
    ring
  rw [hsum]
  calc
    |∑ s, γ s * (x - z s)| ≤ ∑ s, |γ s * (x - z s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, γ s * |x - z s| := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [abs_mul, abs_of_nonneg (hγ s)]

-- @node: pairedBadPoint_cost_lower
/-- Given [the stated mathematical inputs and assumptions](hyp:S,β,z,x,c,δ,hc,hδ,hβ,hbad), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedBadPoint_cost_lower {S : ℕ} (β : Fin S → ℝ → ℝ → ℝ)
    (z : Fin S → ℝ) (x c δ : ℝ)
    (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hβ : ∀ s, c ≤ β s x (z s))
    (hbad : ∃ s, δ ≤ |x - z s|) :
    c * δ ≤ ∑ s : Fin S, β s x (z s) * |x - z s| := by
  obtain ⟨s, hs⟩ := hbad
  have hsingle : c * δ ≤ β s x (z s) * |x - z s| :=
    mul_le_mul (hβ s) hs hδ (hc.trans (hβ s))
  have hnonneg : ∀ t : Fin S, 0 ≤ β t x (z t) * |x - z t| := by
    intro t
    exact mul_nonneg (hc.trans (hβ t)) (abs_nonneg _)
  exact hsingle.trans (Finset.single_le_sum
    (fun t _ => hnonneg t) (Finset.mem_univ s))

-- @node: pairedGoodCell_diameter
/-- Given [the stated mathematical inputs and assumptions](hyp:S,hS,z,x,y,δ,hx,hy), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedGoodCell_diameter {S : ℕ} (hS : 0 < S)
    (z : Fin S → ℝ) (x y δ : ℝ)
    (hx : ∀ s, |x - z s| ≤ δ)
    (hy : ∀ s, |y - z s| ≤ δ) :
    |x - y| ≤ 2 * δ := by
  let s : Fin S := ⟨0, hS⟩
  calc
    |x - y| = |(x - z s) + (z s - y)| := by ring
    _ ≤ |x - z s| + |z s - y| := abs_add_le _ _
    _ ≤ δ + δ := add_le_add (hx s) (by simpa [abs_sub_comm] using hy s)
    _ = 2 * δ := by ring

-- @node: pairedBadSet_measure_cost
/-- Given [the stated mathematical inputs and assumptions](hyp:S,β,z,G,c,δ,hG,hGfinite,hc,hδ,hβ,hbad,hInt), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedBadSet_measure_cost {S : ℕ} (β : Fin S → ℝ → ℝ → ℝ)
    (z : Fin S → ℝ) (G : Set ℝ) (c δ : ℝ)
    (hG : MeasurableSet G) (hGfinite : volume G < ⊤)
    (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hβ : ∀ x ∈ G, ∀ s, c ≤ β s x (z s))
    (hbad : ∀ x ∈ G, ∃ s, δ ≤ |x - z s|)
    (hInt : IntegrableOn
      (fun x => ∑ s : Fin S, β s x (z s) * |x - z s|) G volume) :
    c * δ * volume.real G ≤
      ∫ x in G, ∑ s : Fin S, β s x (z s) * |x - z s| := by
  have : IsFiniteMeasure (volume.restrict G) :=
    ⟨by simpa using hGfinite⟩
  have hmono := integral_mono_ae (integrable_const (c * δ)) hInt (by
    filter_upwards [ae_restrict_mem hG] with x hx
    exact pairedBadPoint_cost_lower β z x c δ hc hδ (hβ x hx) (hbad x hx))
  simpa [Measure.real_def, smul_eq_mul, mul_comm] using hmono

-- @node: pairedBadSet_measure_le
/-- Given [the stated mathematical inputs and assumptions](hyp:S,β,z,G,c,δ,C,k,hG,hGfinite,hc,hδ,hk,hβ,hbad,hInt,hcost), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedBadSet_measure_le {S : ℕ} (β : Fin S → ℝ → ℝ → ℝ)
    (z : Fin S → ℝ) (G : Set ℝ) (c δ C : ℝ) (k : ℕ)
    (hG : MeasurableSet G) (hGfinite : volume G < ⊤)
    (hc : 0 < c) (hδ : 0 < δ) (hk : 0 < k)
    (hβ : ∀ x ∈ G, ∀ s, c ≤ β s x (z s))
    (hbad : ∀ x ∈ G, ∃ s, δ ≤ |x - z s|)
    (hInt : IntegrableOn
      (fun x => ∑ s : Fin S, β s x (z s) * |x - z s|) G volume)
    (hcost : (∫ x in G, ∑ s : Fin S, β s x (z s) * |x - z s|) ≤ C / k) :
    volume.real G ≤ C / (c * δ * k) := by
  have hbound := pairedBadSet_measure_cost β z G c δ hG hGfinite
    hc.le hδ.le hβ hbad hInt
  have hcdk : 0 < c * δ * k := by positivity
  apply (le_div_iff₀ hcdk).2
  calc
    volume.real G * (c * δ * k) = (c * δ * volume.real G) * k := by ring
    _ ≤ (C / k) * k := mul_le_mul_of_nonneg_right (hbound.trans hcost) (by positivity)
    _ = C := by field_simp

-- @node: pairedPartitionCost_nonneg
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,S,k,β,B,z,hB,hz,hβ), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedPartitionCost_nonneg (a b : ℝ) (S k : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) (B : Fin k → Set ℝ)
    (z : Fin k → Fin S → ℝ)
    (hB : IsIntervalPartition a b k B)
    (hz : ∀ j s, z j s ∈ Set.Icc a b)
    (hβ : ∀ s x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → 0 ≤ β s x y) :
    0 ≤ pairedPartitionCost S k β B z := by
  unfold pairedPartitionCost
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro s hs
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (hB.1 j)] with x hx
  have hxI : x ∈ Set.Icc a b := by
    rw [← hB.2.2]
    exact Set.mem_iUnion_of_mem j hx
  exact mul_nonneg (hβ s x (z j s) hxI (hz j s)) (abs_nonneg _)

-- @node: optimalPairedCost_nonneg
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab,S,k,hk,β,hβ), this result [establishes the stated mathematical conclusion](goal). -/
lemma optimalPairedCost_nonneg (a b : ℝ) (hab : a ≤ b) (S k : ℕ) (hk : 0 < k)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hβ : ∀ s x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → 0 ≤ β s x y) :
    0 ≤ optimalPairedCost a b S k β := by
  unfold optimalPairedCost
  apply le_csInf
  · let j₀ : Fin k := ⟨0, hk⟩
    let B : Fin k → Set ℝ := fun j => if j = j₀ then Set.Icc a b else ∅
    let z : Fin k → Fin S → ℝ := fun _ _ => a
    refine ⟨pairedPartitionCost S k β B z, B, z, ?_, ?_, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro j
        dsimp [B]
        split_ifs <;> measurability
      · intro i j hij
        by_cases hi : i = j₀
        · by_cases hj : j = j₀
          · exact (hij (hi.trans hj.symm)).elim
          · simp [B, hi, hj]
        · simp [B, hi]
      · ext x
        simp [B, j₀]
    · intro j s
      exact ⟨le_refl a, hab⟩
  · rintro v ⟨B, z, hB, hz, rfl⟩
    exact pairedPartitionCost_nonneg a b S k β B z hB hz hβ

-- @node: optimalPairedCost_le_feasible
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,S,k,β,B,z,hB,hz,hβ), this result [establishes the stated mathematical conclusion](goal). -/
lemma optimalPairedCost_le_feasible (a b : ℝ) (S k : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) (B : Fin k → Set ℝ)
    (z : Fin k → Fin S → ℝ)
    (hB : IsIntervalPartition a b k B)
    (hz : ∀ j s, z j s ∈ Set.Icc a b)
    (hβ : ∀ s x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → 0 ≤ β s x y) :
    optimalPairedCost a b S k β ≤ pairedPartitionCost S k β B z := by
  unfold optimalPairedCost
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨B', z', hB', hz', rfl⟩
    exact pairedPartitionCost_nonneg a b S k β B' z' hB' hz' hβ
  · exact ⟨B, z, hB, hz, rfl⟩

-- @node: lem:paired-high-resolution-quantization
/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,hab,S,hS,β,hcont,hpos), this result [establishes the stated mathematical conclusion](goal). -/
lemma pairedQuantization_tendsto (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn
      (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    Tendsto (fun k : ℕ => (k : ℝ) * optimalPairedCost a b S k β)
      atTop (nhds ((1 / 4 : ℝ) *
        (∫ x in a..b, Real.sqrt (pairedDiagonalWeight S β x)) ^ 2)) ∧
    Tendsto (fun k : ℕ => (k : ℝ) *
      pairedPartitionCost S k β
        (pairedCompandingCell a b S k β)
        (pairedCompandingMidpoint a b S k β))
      atTop (nhds ((1 / 4 : ℝ) *
        (∫ x in a..b, Real.sqrt (pairedDiagonalWeight S β x)) ^ 2)) ∧
    (∀ k, 0 < k →
      IsIntervalPartition a b k (pairedCompandingCell a b S k β) ∧
      ∀ j s, pairedCompandingMidpoint a b S k β j s ∈ Set.Icc a b) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      Causalean.Mathlib.Analysis.Quantization.optimal_scaled_cost_tendsto
        a b hab S hS β hcont hpos
  · exact
      Causalean.Mathlib.Analysis.Quantization.companding_scaled_cost_tendsto
        a b hab S hS β hcont hpos
  · intro k hk
    refine ⟨?_, pairedCompandingMidpoint_mem_Icc a b hab.le S k hk β⟩
    let f : ℕ → ℝ := fun j => pairedBoundary a b S k j β
    have hm : ∀ i j, i ≤ j → j ≤ k → f i ≤ f j := by
      intro i j hij hj
      exact pairedBoundary_mono a b hab.le S k i j hk hij hj β
    have hpart := orderedIntervalCells_partition f k hk hm
    have hzero : f 0 = a := pairedBoundary_zero a b hab.le S k β
    have hlast : f k = b := pairedBoundary_last a b hab S k hS hk β hcont hpos
    rw [hzero, hlast] at hpart
    change IsIntervalPartition a b k (fun j : Fin k =>
      if j.val + 1 = k then
        Set.Icc (pairedBoundary a b S k j.val β)
          (pairedBoundary a b S k (j.val + 1) β)
      else
        Set.Ico (pairedBoundary a b S k j.val β)
          (pairedBoundary a b S k (j.val + 1) β))
    exact hpart

end
end CausalSmith.PartialID.UnlinkedPropensityAte
