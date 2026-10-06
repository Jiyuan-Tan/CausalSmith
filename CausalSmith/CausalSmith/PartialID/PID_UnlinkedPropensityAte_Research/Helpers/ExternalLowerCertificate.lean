module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.External
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLaw
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.TotalVariation
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Trial and external-log testing certificates for excess confidence length. -/

@[expose] public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,J,g), [this definition](goal) introduces the corresponding object. -/
def fiberTripleSeparation {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) : ℝ :=
  sSup {v : ℝ | ∃ (r : LabelSpace J)
      (e₁ e₂ e₃ : ScoreSpace ε),
    e₁ < e₂ ∧ e₂ < e₃ ∧ g e₁ = r ∧ g e₂ = r ∧ g e₃ = r ∧
    v = (((e₃ : ℝ) - e₂) * (1 - (e₁ : ℝ) / e₂)) /
      Real.sqrt (((e₃ : ℝ) - e₂) ^ 2 +
        ((e₃ : ℝ) - e₁) ^ 2 + ((e₂ : ℝ) - e₁) ^ 2)}

/-- For [the specified mathematical inputs](hyp:ρ), [this definition](goal) introduces the corresponding object. -/
def ratioFilter (ρ : ℝ) : Filter (ℕ × ℕ) :=
  (atTop ×ˢ atTop) ⊓ Filter.comap
    (fun nm : ℕ × ℕ => (nm.1 : ℝ) / (nm.2 : ℝ)) (nhds ρ)
  -- @realizes rho(positive trial-to-log sample ratio)

-- @node: ratioFilter_neBot
/-- Given [the stated mathematical inputs and assumptions](hyp:ρ,hρ), this result [establishes the stated mathematical conclusion](goal). -/
lemma ratioFilter_neBot (ρ : ℝ) (hρ : 0 < ρ) : (ratioFilter ρ).NeBot := by
  let seq : ℕ → ℕ × ℕ := fun m => (⌈ρ * (m : ℝ)⌉₊, m)
  have hmul : Tendsto (fun m : ℕ => ρ * (m : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hρ).2 tendsto_natCast_atTop_atTop
  have hceil : Tendsto (fun m : ℕ => ⌈ρ * (m : ℝ)⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp hmul
  have hpair : Tendsto seq atTop (atTop ×ˢ atTop) :=
    hceil.prodMk tendsto_id
  have hratio : Tendsto (fun m : ℕ =>
      (⌈ρ * (m : ℝ)⌉₊ : ℝ) / (m : ℝ)) atTop (nhds ρ) :=
    (tendsto_nat_ceil_mul_div_atTop hρ.le).comp tendsto_natCast_atTop_atTop
  have hseq : Tendsto seq atTop (ratioFilter ρ) := by
    unfold ratioFilter
    apply tendsto_inf.mpr
    refine ⟨hpair, ?_⟩
    apply tendsto_comap_iff.mpr
    exact hratio
  exact (Filter.map_neBot_iff seq).2 inferInstance |>.mono hseq
/-- For [the specified mathematical inputs](hyp:α), [this definition](goal) introduces the corresponding object. -/
def trialCertificate (α : ℝ) : ℝ :=
  (1 - 2 * α) * Real.sqrt (Real.log (1 + (1 - 2 * α) ^ 2)) / 4
/-- For [the specified mathematical inputs](hyp:ε,J,g,α), [this definition](goal) introduces the corresponding object. -/
def logCertificate {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ) : ℝ :=
  (1 - 2 * α) * Real.sqrt (Real.log (1 + (1 - 2 * α) ^ 2)) /
    (2 * Real.sqrt 3) * fiberTripleSeparation g

-- @node: fiberTriple_exists
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma fiberTriple_exists {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε) :
    ∃ r : LabelSpace J, ∃ e₁ e₂ e₃ : ScoreSpace ε,
      e₁ < e₂ ∧ e₂ < e₃ ∧ g e₁ = r ∧ g e₂ = r ∧ g e₃ = r := by
  have hε : ε < 1 - ε := by rcases hOverlap with ⟨_, h⟩; linarith
  let : Infinite (ScoreSpace ε) := Set.Icc.infinite hε
  obtain ⟨r, hr⟩ := Finite.exists_infinite_fiber g
  have hset : (g ⁻¹' {r}).Infinite := Set.infinite_coe_iff.mp hr
  by_contra hn
  push Not at hn
  have hfinite : (g ⁻¹' {r}).Finite := by
    apply Set.finite_of_forall_not_lt_lt
    intro e₁ he₁ e₂ he₂ e₃ he₃ h₁₂ h₂₃
    exact hn r e₁ e₂ e₃ h₁₂ h₂₃ he₁ he₂ he₃
  exact hset hfinite

-- @node: fiberTriple_ratio_bounds
/-- Given [the stated mathematical inputs and assumptions](hyp:x,y,z,hx,hxy,hyz), this result [establishes the stated mathematical conclusion](goal). -/
lemma fiberTriple_ratio_bounds (x y z : ℝ)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    0 < ((z - y) * (1 - x / y)) /
      Real.sqrt ((z - y) ^ 2 + (z - x) ^ 2 + (y - x) ^ 2) ∧
    ((z - y) * (1 - x / y)) /
      Real.sqrt ((z - y) ^ 2 + (z - x) ^ 2 + (y - x) ^ 2) ≤ 1 := by
  have hy : 0 < y := lt_trans hx hxy
  have hd : 0 < z - y := sub_pos.mpr hyz
  have hfrac₀ : 0 < x / y := div_pos hx hy
  have hfrac₁ : x / y < 1 := (div_lt_one hy).mpr hxy
  have hsquare : 0 ≤ (z - y) ^ 2 + (z - x) ^ 2 + (y - x) ^ 2 := by positivity
  have hsquare_pos : 0 < (z - y) ^ 2 + (z - x) ^ 2 + (y - x) ^ 2 := by
    nlinarith [sq_nonneg (z - x), sq_nonneg (y - x), sq_pos_of_pos hd]
  have hden : 0 < Real.sqrt ((z - y) ^ 2 + (z - x) ^ 2 + (y - x) ^ 2) :=
    Real.sqrt_pos.2 hsquare_pos
  have hden_lower : z - y ≤
      Real.sqrt ((z - y) ^ 2 + (z - x) ^ 2 + (y - x) ^ 2) := by
    have hroot := Real.sq_sqrt hsquare
    nlinarith [Real.sqrt_nonneg ((z - y) ^ 2 + (z - x) ^ 2 + (y - x) ^ 2),
      sq_nonneg (z - x), sq_nonneg (y - x)]
  constructor
  · exact div_pos (mul_pos hd (by linarith)) hden
  · apply (div_le_one hden).mpr
    nlinarith [mul_nonneg (le_of_lt hd) (le_of_lt hfrac₀)]

-- @node: fiberTripleSeparation_bounds
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap), this result [establishes the stated mathematical conclusion](goal). -/
lemma fiberTripleSeparation_bounds {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε) :
    0 < fiberTripleSeparation g ∧ fiberTripleSeparation g ≤ 1 := by
  let T : Set ℝ := {v | ∃ (r : LabelSpace J) (e₁ e₂ e₃ : ScoreSpace ε),
    e₁ < e₂ ∧ e₂ < e₃ ∧ g e₁ = r ∧ g e₂ = r ∧ g e₃ = r ∧
    v = (((e₃ : ℝ) - e₂) * (1 - (e₁ : ℝ) / e₂)) /
      Real.sqrt (((e₃ : ℝ) - e₂) ^ 2 +
        ((e₃ : ℝ) - e₁) ^ 2 + ((e₂ : ℝ) - e₁) ^ 2)}
  have hbound : ∀ v ∈ T, 0 < v ∧ v ≤ 1 := by
    rintro v ⟨r, e₁, e₂, e₃, h₁₂, h₂₃, _, _, _, rfl⟩
    exact fiberTriple_ratio_bounds _ _ _
      (lt_of_lt_of_le hOverlap.1 e₁.property.1) h₁₂ h₂₃
  obtain ⟨r, e₁, e₂, e₃, h₁₂, h₂₃, hr₁, hr₂, hr₃⟩ :=
    fiberTriple_exists g hOverlap
  let v : ℝ := (((e₃ : ℝ) - e₂) * (1 - (e₁ : ℝ) / e₂)) /
    Real.sqrt (((e₃ : ℝ) - e₂) ^ 2 +
      ((e₃ : ℝ) - e₁) ^ 2 + ((e₂ : ℝ) - e₁) ^ 2)
  have hv : v ∈ T := ⟨r, e₁, e₂, e₃, h₁₂, h₂₃, hr₁, hr₂, hr₃, rfl⟩
  have hbdd : BddAbove T := ⟨1, fun v hv => (hbound v hv).2⟩
  change 0 < sSup T ∧ sSup T ≤ 1
  exact ⟨lt_of_lt_of_le (hbound v hv).1 (le_csSup hbdd hv),
    csSup_le ⟨v, hv⟩ (fun v hv => (hbound v hv).2)⟩

-- @node: fiberTriple_perturbation_identities
/-- Given [the stated mathematical inputs and assumptions](hyp:x,y,z,hxy,hyz), this result [establishes the stated mathematical conclusion](goal). -/
lemma fiberTriple_perturbation_identities (x y z : ℝ) (hxy : x < y) (hyz : y < z) :
    (z - y) - (z - x) + (y - x) = 0 ∧
    x * (z - y) - y * (z - x) + z * (y - x) = 0 ∧
    0 < z - y ∧ 0 < y - x := by
  constructor
  · ring
  constructor
  · ring
  exact ⟨sub_pos.mpr hyz, sub_pos.mpr hxy⟩

-- @node: fiberTriple_upperEndpoint_shift
/-- Given [the stated mathematical inputs and assumptions](hyp:x,y,z,t,u,hy), this result [establishes the stated mathematical conclusion](goal). -/
lemma fiberTriple_upperEndpoint_shift (x y z t u : ℝ) (hy : y ≠ 0) :
    ((1 / 3 + u * (z - y)) +
        (t - x * (1 / 3 + u * (z - y))) / y) -
      ((1 / 3 : ℝ) + (t - x * (1 / 3)) / y) =
        u * (z - y) * (1 - x / y) := by
  field_simp
  ring

-- @node: fiberTriple_chisq_identity
/-- Given [the stated mathematical inputs and assumptions](hyp:x,y,z,u), this result [establishes the stated mathematical conclusion](goal). -/
lemma fiberTriple_chisq_identity (x y z u : ℝ) :
    ((u * (z - y)) ^ 2 + (u * (z - x)) ^ 2 +
      (u * (y - x)) ^ 2) / (1 / 3 : ℝ) =
        3 * u ^ 2 * ((z - y) ^ 2 + (z - x) ^ 2 + (y - x) ^ 2) := by
  ring

-- @node: externalCertificate_constants_pos
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,α,hOverlap,hα), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalCertificate_constants_pos {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2) :
    0 < trialCertificate α ∧ 0 < logCertificate g α := by
  have hgap : 0 < 1 - 2 * α := by linarith [hα.2]
  have hlog : 0 < Real.log (1 + (1 - 2 * α) ^ 2) := by
    apply Real.log_pos
    nlinarith [sq_pos_of_pos hgap]
  have hroot : 0 < Real.sqrt (Real.log (1 + (1 - 2 * α) ^ 2)) :=
    Real.sqrt_pos.2 hlog
  have hsep := (fiberTripleSeparation_bounds g hOverlap).1
  constructor
  · unfold trialCertificate
    positivity
  · unfold logCertificate
    positivity

-- @node: normalizedCertificate_trial
/-- Given [the stated mathematical inputs and assumptions](hyp:n,m,hn,hm,c,R,hR), this result [establishes the stated mathematical conclusion](goal). -/
lemma normalizedCertificate_trial (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (c R : ℝ) (hR : c * (Real.sqrt (n : ℝ))⁻¹ ≤ R) :
    c * Real.sqrt (m : ℝ) /
        (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) ≤
      externalNormalizer n m * R := by
  have hn' : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  have hm' : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
  have hnorm : 0 ≤ externalNormalizer n m := by
    unfold externalNormalizer
    positivity
  have hid : externalNormalizer n m * (c * (Real.sqrt (n : ℝ))⁻¹) =
      c * Real.sqrt (m : ℝ) /
        (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) := by
    unfold externalNormalizer
    field_simp
    ring
  rw [← hid]
  exact mul_le_mul_of_nonneg_left hR hnorm

-- @node: normalizedCertificate_log
/-- Given [the stated mathematical inputs and assumptions](hyp:n,m,hn,hm,c,R,hR), this result [establishes the stated mathematical conclusion](goal). -/
lemma normalizedCertificate_log (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (c R : ℝ) (hR : c * (Real.sqrt (m : ℝ))⁻¹ ≤ R) :
    c * Real.sqrt (n : ℝ) /
        (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) ≤
      externalNormalizer n m * R := by
  have hn' : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  have hm' : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
  have hnorm : 0 ≤ externalNormalizer n m := by
    unfold externalNormalizer
    positivity
  have hid : externalNormalizer n m * (c * (Real.sqrt (m : ℝ))⁻¹) =
      c * Real.sqrt (n : ℝ) /
        (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) := by
    unfold externalNormalizer
    field_simp
    ring
  rw [← hid]
  exact mul_le_mul_of_nonneg_left hR hnorm

-- @node: ratioFilter_eventually_pos
/-- Given [the stated mathematical inputs and assumptions](hyp:ρ), this result [establishes the stated mathematical conclusion](goal). -/
lemma ratioFilter_eventually_pos (ρ : ℝ) :
    ∀ᶠ nm : ℕ × ℕ in ratioFilter ρ, 0 < nm.1 ∧ 0 < nm.2 := by
  apply Filter.Eventually.filter_mono (by unfold ratioFilter; exact inf_le_left)
  exact (eventually_gt_atTop (0 : ℕ)).prod_mk (eventually_gt_atTop (0 : ℕ))

-- @node: ratioFilter_ratio_tendsto
/-- Given [the stated mathematical inputs and assumptions](hyp:ρ), this result [establishes the stated mathematical conclusion](goal). -/
lemma ratioFilter_ratio_tendsto (ρ : ℝ) :
    Tendsto (fun nm : ℕ × ℕ => (nm.1 : ℝ) / (nm.2 : ℝ))
      (ratioFilter ρ) (nhds ρ) := by
  exact (tendsto_iff_comap).2 (by
    unfold ratioFilter
    exact inf_le_right)

-- @node: normalizedCertificate_ratio_trial
/-- Given [the stated mathematical inputs and assumptions](hyp:ρ,hρ), this result [establishes the stated mathematical conclusion](goal). -/
lemma normalizedCertificate_ratio_trial (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun nm : ℕ × ℕ =>
      Real.sqrt (nm.2 : ℝ) /
        (Real.sqrt (nm.1 : ℝ) + Real.sqrt (nm.2 : ℝ)))
      (ratioFilter ρ) (nhds (1 / (1 + Real.sqrt ρ))) := by
  have hr := ratioFilter_ratio_tendsto ρ
  have hcomp : Tendsto (fun nm : ℕ × ℕ =>
      1 / (1 + Real.sqrt ((nm.1 : ℝ) / (nm.2 : ℝ))))
      (ratioFilter ρ) (nhds (1 / (1 + Real.sqrt ρ))) := by
    have hcont : ContinuousAt (fun x : ℝ => 1 / (1 + Real.sqrt x)) ρ := by
      have hden : 1 + Real.sqrt ρ ≠ 0 := ne_of_gt (by positivity)
      fun_prop (disch := assumption)
    exact hcont.tendsto.comp hr
  apply hcomp.congr'
  filter_upwards [hr.eventually (eventually_gt_nhds hρ)] with nm hratio
  have hm : 0 < nm.2 := by
    by_contra h
    have hzero : nm.2 = 0 := by omega
    simp [hzero] at hratio
  have hsm : 0 < Real.sqrt (nm.2 : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  rw [Real.sqrt_div (by positivity : 0 ≤ (nm.1 : ℝ)) (nm.2 : ℝ)]
  field_simp
  ring

-- @node: normalizedCertificate_ratio_log
/-- Given [the stated mathematical inputs and assumptions](hyp:ρ,hρ), this result [establishes the stated mathematical conclusion](goal). -/
lemma normalizedCertificate_ratio_log (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun nm : ℕ × ℕ =>
      Real.sqrt (nm.1 : ℝ) /
        (Real.sqrt (nm.1 : ℝ) + Real.sqrt (nm.2 : ℝ)))
      (ratioFilter ρ)
      (nhds (Real.sqrt ρ / (1 + Real.sqrt ρ))) := by
  have hr := ratioFilter_ratio_tendsto ρ
  have hcomp : Tendsto (fun nm : ℕ × ℕ =>
      Real.sqrt ((nm.1 : ℝ) / (nm.2 : ℝ)) /
        (1 + Real.sqrt ((nm.1 : ℝ) / (nm.2 : ℝ))))
      (ratioFilter ρ)
      (nhds (Real.sqrt ρ / (1 + Real.sqrt ρ))) := by
    have hcont : ContinuousAt (fun x : ℝ =>
        Real.sqrt x / (1 + Real.sqrt x)) ρ := by
      have hden : 1 + Real.sqrt ρ ≠ 0 := ne_of_gt (by positivity)
      fun_prop (disch := assumption)
    exact hcont.tendsto.comp hr
  apply hcomp.congr'
  filter_upwards [hr.eventually (eventually_gt_nhds hρ)] with nm hratio
  have hm : 0 < nm.2 := by
    by_contra h
    have hzero : nm.2 = 0 := by omega
    simp [hzero] at hratio
  have hsm : 0 < Real.sqrt (nm.2 : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hm)
  rw [Real.sqrt_div (by positivity : 0 ≤ (nm.1 : ℝ)) (nm.2 : ℝ)]
  field_simp
  ring

end
end CausalSmith.PartialID.UnlinkedPropensityAte
