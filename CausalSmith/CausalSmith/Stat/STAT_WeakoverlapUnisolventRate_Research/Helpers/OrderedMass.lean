module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass.Ranking

/-! # Uniform ordered treated-mass bound -/
public section
set_option linter.style.haveILetI false
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory

/-- Rewrite the nonnegative geometric microcell volume as an ordinary real power. [For the stated inputs and conditions](hyp:d,m,j,hη), [the asserted conclusion holds](goal). -/
lemma orderedMass_microcell_volume_toReal (d m j : ℕ)
    (hη : 0 ≤ templateEta d m) :
    (ENNReal.ofReal (templateEta d m * meshWidth j) ^ d).toReal =
      (templateEta d m * meshWidth j) ^ d := by
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal]
  exact mul_nonneg hη (by unfold meshWidth; positivity)

/-- Separate the cell volume and rank powers after division by the rank. [For the stated inputs and conditions](hyp:d,k,a,b,γ,hk,ha,hb,hγ), [the asserted conclusion holds](goal). -/
lemma orderedMass_rank_power_identity (d k : ℕ) (a b γ : ℝ)
    (hk : 0 < k) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 1 < γ) :
    ((k : ℝ) * (a * b ^ d)) ^ (γ / (γ - 1)) / (k : ℝ) =
      a ^ (γ / (γ - 1)) * b ^ ((d : ℝ) * γ / (γ - 1)) *
        (k : ℝ) ^ (1 / (γ - 1)) := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hne : γ - 1 ≠ 0 := ne_of_gt (by linarith)
  have hp : γ / (γ - 1) = 1 / (γ - 1) + 1 := by
    field_simp [hne]
    ring
  rw [Real.mul_rpow hk'.le (mul_nonneg ha (pow_nonneg hb _)),
    Real.mul_rpow ha (pow_nonneg hb _)]
  have hbpow : (b ^ d) ^ (γ / (γ - 1)) =
      b ^ ((d : ℝ) * γ / (γ - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
    congr 1
    ring
  rw [hbpow, hp, Real.rpow_add hk', Real.rpow_one]
  field_simp

-- @node: lem:ordered-mass
/-- One constant works uniformly over the compact range of overlap exponents.
The first inequality is the layer-cake setwise bound; the second is the
ordered weakest-cell profile. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hparams,hγmin,hγrange), [the asserted conclusion holds](goal). -/
lemma orderedTreatedMass_lower (d : ℕ) (β B L C c_f γ_min γ_max : ℝ)
    (hparams : ModelParameterDomain d β B L C c_f)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (γ : ℝ), γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩ →
      ∀ (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
        (μ₁ e : (Fin d → ℝ) → ℝ),
        GlobalTailModel β B L C c_f γ Pc μ₁ e →
        (∀ E : Set (Fin d → ℝ), MeasurableSet E → E ⊆ cube d →
          ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
              (covariateLaw (Pc.map observed)).real E ^ (γ / (γ - 1)) ≤
            (Pc.map observed).real {z | z.2.1 = true ∧ z.1 ∈ E}) ∧
        (∀ j : ℕ, ∀ k : ℕ,
          1 ≤ k → k ≤ (2 ^ j) ^ d →
          κ * meshWidth j ^ effectiveDimension d γ *
              (k : ℝ) ^ ((1 : ℝ) / (γ - 1)) ≤
            (@orderedCubeMass d (Pc.map observed)
              (Measure.isProbabilityMeasure_map (by unfold observed; fun_prop))
              (polynomialDegree β) j).getD
                (k - 1) 0) := by
  let m := polynomialDegree β
  let a := c_f * templateEta d m ^ d
  have hC : 1 ≤ C := hparams.2.2.2.2.1
  have hcf : 0 < c_f := hparams.2.2.2.2.2.1
  have hη : 0 < templateEta d m := by
    unfold templateEta
    apply lt_min
    · positivity
    · exact div_pos (templateLambda_pos d m) (by linarith [templateLip_nonneg d m])
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨κ, hκ, hκle⟩ := orderedMass_uniform_coefficient C a γ_min γ_max
    (by linarith) ha hγmin hγrange
  refine ⟨κ, hκ, ?_⟩
  intro γ hγ Pc _ μ₁ e hmodel
  have hγ' : 1 < γ := lt_of_lt_of_le hγmin hγ.1
  constructor
  · intro E hE _
    exact orderedMass_setwise_lower β B L C c_f γ Pc μ₁ e hmodel hC hγ' E hE
  · intro j k hk hkmax
    letI : IsProbabilityMeasure (Pc.map observed) :=
      Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
    obtain ⟨S, ℓ, hS, hupper⟩ :=
      orderedMass_ranked_union_upper (Pc.map observed) m j k hkmax
    have hlower := orderedMass_selectedMicrocells_treated_lower d m j
      β B L C c_f γ Pc μ₁ e hmodel hC hγ' (le_of_lt hcf) S ℓ
    rw [hS, orderedMass_microcell_volume_toReal d m j hη.le] at hlower
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have hmesh : 0 ≤ meshWidth j := by unfold meshWidth; positivity
    have hpow : 0 ≤ a ^ (γ / (γ - 1)) *
        meshWidth j ^ effectiveDimension d γ *
          (k : ℝ) ^ (1 / (γ - 1)) := by positivity
    have hrewrite :
        ((k : ℝ) * (c_f * (templateEta d m * meshWidth j) ^ d)) ^
            (γ / (γ - 1)) / (k : ℝ) =
        a ^ (γ / (γ - 1)) * meshWidth j ^ effectiveDimension d γ *
          (k : ℝ) ^ (1 / (γ - 1)) := by
      have hbase : c_f * (templateEta d m * meshWidth j) ^ d =
          a * meshWidth j ^ d := by
        rw [mul_pow]
        dsimp [a]
        ring
      rw [hbase]
      simpa only [effectiveDimension, div_eq_mul_inv, mul_assoc] using
        orderedMass_rank_power_identity d k a (meshWidth j) γ hk ha.le hmesh hγ'
    have hcoeff := hκle γ hγ
    have halgebra :
        κ * meshWidth j ^ effectiveDimension d γ *
          (k : ℝ) ^ (1 / (γ - 1)) ≤
        (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
          ((k : ℝ) * (c_f * (templateEta d m * meshWidth j) ^ d)) ^
            (γ / (γ - 1))) / (k : ℝ) := by
      rw [mul_div_assoc, hrewrite]
      have hfactor : 0 ≤ meshWidth j ^ effectiveDimension d γ *
          (k : ℝ) ^ (1 / (γ - 1)) := by positivity
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff hfactor
    have hresult := hlower.trans hupper
    exact halgebra.trans ((div_le_iff₀ hk').2 (by
      simpa only [mul_comm] using hresult))
end CausalSmith.Stat.WeakOverlap
