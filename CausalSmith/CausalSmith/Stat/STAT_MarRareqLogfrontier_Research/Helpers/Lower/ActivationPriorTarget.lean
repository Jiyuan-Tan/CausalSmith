module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationTarget

/-! Extend independent rare-cell priors to the full alphabet and identify the
actual activated ATE with the reciprocal target in equations (7)--(12). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:n,q,hq), [the stated mathematical conclusion holds](goal). -/
-- @node: lowerEndpoint_one_le
lemma lowerEndpoint_one_le (n : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    1 ≤ lowerEndpoint n q := by
  have hN : 0 ≤ effectiveSize n q := by unfold effectiveSize; positivity
  have hlog : 1 ≤ logScale n q := by
    unfold logScale
    have h := Real.log_le_log (Real.exp_pos (1 : ℝ))
      (show Real.exp 1 ≤ Real.exp 1 + effectiveSize n q by linarith)
    simpa using h
  have hceil : (1 : ℝ) ≤ lowerDegree n q :=
    hlog.trans (Nat.le_ceil (logScale n q))
  unfold lowerEndpoint
  nlinarith

/-- For [the specified inputs and assumptions](hyp:η,n,d,q,z,x), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: activationExtendRare
noncomputable def activationExtendRare (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin (rareCount η n d q) → ℝ) (x : Fin d) : ℝ :=
  if h : x.val < rareCount η n d q then z ⟨x.val, h⟩ else lowerEndpoint n q

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,x), [the stated mathematical conclusion holds](goal). -/
-- @node: activationExtendRare_eval
lemma activationExtendRare_eval (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin (rareCount η n d q) → ℝ) (x : Fin (rareCount η n d q)) :
    activationExtendRare η n d q z
      (x.castLE ((min_le_left _ _).trans (Nat.sub_le d 1))) = z x := by
  change (if h : x.val < rareCount η n d q then z ⟨x.val, h⟩ else
    lowerEndpoint n q) = z x
  rw [dif_pos x.isLt]

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hq,z,hz), [the stated mathematical conclusion holds](goal). -/
-- @node: activationExtendRare_support
lemma activationExtendRare_support (η : ℝ) (n d : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (z : Fin (rareCount η n d q) → ℝ)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q)) :
    ∀ x, activationExtendRare η n d q z x ∈ Icc (1 : ℝ) (lowerEndpoint n q) := by
  intro x
  unfold activationExtendRare
  split_ifs with h
  · exact hz ⟨x.val, h⟩
  · exact ⟨lowerEndpoint_one_le n q hq, le_rfl⟩

/-- Given [the specified inputs and assumptions](hyp:H,π,hπ,J), [the stated mathematical conclusion holds](goal). -/
-- @node: finiteReciprocalPrior_pi_ae_support
lemma finiteReciprocalPrior_pi_ae_support {H : ℝ} {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior H π) (J : ℕ) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin J => π), ∀ x, z x ∈ Icc (1 : ℝ) H := by
  let := hπ.1
  obtain ⟨s, hs, hsupport⟩ := hπ.2
  have hae : ∀ᵐ z ∂π, z ∈ (s : Set ℝ) :=
    (ae_mem_iff_measure_eq s.measurableSet.nullMeasurableSet).2 (by simpa using hs)
  have hinterval : ∀ᵐ z ∂π, z ∈ Icc (1 : ℝ) H := by
    filter_upwards [hae] with z hz
    exact hsupport z hz
  rw [ae_all_iff]
  intro x
  exact Measure.tendsto_eval_ae_ae.eventually hinterval

/-- For [the specified inputs and assumptions](hyp:η,n,d,q,hd,hb,hq,hslice,z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: activatedRarePriorATE
noncomputable def activatedRarePriorATE (η : ℝ) (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q) (z : Fin (rareCount η n d q) → ℝ) : ℝ :=
  if hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q) then
    ate (activatedFullLaw η n d q (activationExtendRare η n d q z)
      hd hb hq hslice (activationExtendRare_support η n d q hq.le z hz))
  else 0

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hd,hb,hq,hslice,π,hπ), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedRarePriorATE_ae_eq
lemma activatedRarePriorATE_ae_eq (η : ℝ) (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π) :
    activatedRarePriorATE η n d q hd hb hq hslice =ᵐ[
      Measure.pi (fun _ : Fin (rareCount η n d q) => π)]
      intervalPriorTarget (rareCount η n d q) (rareMass η n q) := by
  filter_upwards [finiteReciprocalPrior_pi_ae_support hπ (rareCount η n d q)] with z hz
  rw [activatedRarePriorATE, dif_pos hz, activatedFullLaw_ate]
  congr 1
  funext x
  exact activationExtendRare_eval η n d q z x

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hd,hb,hq,hslice,π,hπ), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedRarePriorATE_integral
lemma activatedRarePriorATE_integral (η : ℝ) (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π) :
    (∫ z, activatedRarePriorATE η n d q hd hb hq hslice z
      ∂Measure.pi (fun _ : Fin (rareCount η n d q) => π)) =
      (rareCount η n d q : ℝ) * rareMass η n q * ∫ z, z⁻¹ ∂π := by
  rw [integral_congr_ae (activatedRarePriorATE_ae_eq η n d q hd hb hq hslice hπ)]
  exact intervalPriorTarget_integral hπ _ _

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hd,hb,hq,hslice,π,hπ), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedRarePriorATE_variance_le
lemma activatedRarePriorATE_variance_le (η : ℝ) (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q) {π : Measure ℝ}
    (hπ : FiniteReciprocalPrior (lowerEndpoint n q) π) :
    variance (activatedRarePriorATE η n d q hd hb hq hslice)
      (Measure.pi (fun _ : Fin (rareCount η n d q) => π)) ≤
        (rareCount η n d q : ℝ) * (rareMass η n q) ^ 2 / 4 := by
  rw [variance_congr (activatedRarePriorATE_ae_eq η n d q hd hb hq hslice hπ)]
  exact intervalPriorTarget_variance_le hπ _ _

/-- Given [the specified inputs and assumptions](hyp:η,n,d,M,q,u,hd,hb,hq,hslice,π₀,π₁,h₀,h₁,hu,hM,hgap,hJ), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedRarePriorATE_grid_concentration
lemma activatedRarePriorATE_grid_concentration (η : ℝ) (n d M : ℕ) (q u : ℝ)
    (hd : 1 ≤ d) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q) {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (hu : 0 < u) (hM : 1 ≤ M)
    (hgap : 1 / 12 ≤ |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀|)
    (hJ : 18432 * (M : ℝ) ^ 2 / u ≤ (rareCount η n d q : ℝ)) :
    ∀ j : Fin (M + 1),
      (Measure.pi (fun _ : Fin (rareCount η n d q) =>
        intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))).real
        {z | ((rareCount η n d q : ℝ) * rareMass η n q *
          |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀|) / (8 * M) <
          |activatedRarePriorATE η n d q hd hb hq hslice z -
            ((rareCount η n d q : ℝ) * rareMass η n q * (∫ z, z⁻¹ ∂π₀) +
              (j : ℝ) * ((rareCount η n d q : ℝ) * rareMass η n q *
                ((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀) / M))|} ≤ u / 8 := by
  intro j
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have ht : (j : ℝ) / M ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one hMr).mpr ?_⟩
    exact_mod_cast (by omega : j.val ≤ M)
  have hae := activatedRarePriorATE_ae_eq η n d q hd hb hq hslice
    (finiteReciprocalPrior_interpolate h₀ h₁ ht)
  have hevent :
      {z | ((rareCount η n d q : ℝ) * rareMass η n q *
          |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀|) / (8 * M) <
          |activatedRarePriorATE η n d q hd hb hq hslice z -
            ((rareCount η n d q : ℝ) * rareMass η n q * (∫ z, z⁻¹ ∂π₀) +
              (j : ℝ) * ((rareCount η n d q : ℝ) * rareMass η n q *
                ((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀) / M))|} =ᵐ[
        Measure.pi (fun _ : Fin (rareCount η n d q) =>
          intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))]
      {z | ((rareCount η n d q : ℝ) * rareMass η n q *
          |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀|) / (8 * M) <
          |intervalPriorTarget (rareCount η n d q) (rareMass η n q) z -
            ((rareCount η n d q : ℝ) * rareMass η n q * (∫ z, z⁻¹ ∂π₀) +
              (j : ℝ) * ((rareCount η n d q : ℝ) * rareMass η n q *
                ((∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀) / M))|} := by
    filter_upwards [hae] with z hz
    change (_ < |activatedRarePriorATE η n d q hd hb hq hslice z - _|) =
      (_ < |intervalPriorTarget (rareCount η n d q) (rareMass η n q) z - _|)
    rw [hz]
  unfold Measure.real
  rw [measure_congr hevent]
  exact intervalInterpolatedPrior_grid_concentration h₀ h₁ (rareCount η n d q)
    M (rareMass η n q) u hb hu hM hgap hJ j

end CausalSmith.Stat.MarRareqLogfrontier
