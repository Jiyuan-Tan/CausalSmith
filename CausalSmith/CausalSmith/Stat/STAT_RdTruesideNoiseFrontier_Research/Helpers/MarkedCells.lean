module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.MarkedConvolution

/-!
# Treated-cell convolution formulas for the actual witness probabilities

The full continuation restricts to the compact block on the treated arm. Applying
Gaussian convolution to the witness success and failure probabilities gives ML.1,
and the existing two-cell integral bound supplies ML.2 for these convolutions.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- On the treated arm the full continuation has exactly the compact convolution. Given [the displayed inputs and assumptions](hyp:b,σ,m,hb,w), [the stated mathematical conclusion holds](goal). -/
lemma legalExtension_treated_convolution (b σ : ℝ) (m : ℕ)
    (hb : b ∈ Ioc (0 : ℝ) 1) (w : ℝ) :
    (∫ x in (0 : ℝ)..1, legalExtension b m x * phi σ (w-x)) =
      markedConvolution b m σ w := by
  have hbp := hb.1
  have hc : Continuous (fun x => legalExtension b m x * phi σ (w-x)) := by
    fun_prop
  have hlocal : (∫ x in (0 : ℝ)..b, legalExtension b m x * phi σ (w-x)) =
      markedConvolution b m σ w := by
    apply intervalIntegral.integral_congr_Ioo_of_le hb.1.le
    intro x hx
    simp [legalExtension, not_lt.mpr hx.1.le, hx.2.le]
  have htail : (∫ x in b..1, legalExtension b m x * phi σ (w-x)) = 0 := by
    calc
      _ = ∫ x in b..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hb.2
        intro x hx
        simp [legalExtension, not_lt.mpr (hb.1.le.trans hx.1.le), not_le.mpr hx.1]
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 b) (hc.intervalIntegrable b 1), hlocal, htail, add_zero]

/-- Convolving the actual success probability gives the first treated cell of ML.1. Given [the displayed inputs and assumptions](hyp:β,b,σ,m,s,hb,w), [the stated mathematical conclusion holds](goal). -/
lemma altProbability_success_convolution (β b σ : ℝ) (m : ℕ) (s : Bool)
    (hb : b ∈ Ioc (0 : ℝ) 1) (w : ℝ) :
    (1/2 : ℝ) * (∫ x in (0 : ℝ)..1, altProbability β b m s x * phi σ (w-x)) =
      treatedConvolution σ w / 4 +
        witnessSign s * kappa * (b/(m : ℝ)^2)^β * markedConvolution b m σ w / 2 := by
  have hbp := hb.1
  have hp : Continuous (fun x => phi σ (w-x)) := by fun_prop
  have hv : Continuous (fun x => legalExtension b m x * phi σ (w-x)) := by fun_prop
  have he : (fun x => altProbability β b m s x * phi σ (w-x)) =
      (fun x => (1/2 : ℝ) * phi σ (w-x) +
        (witnessSign s * kappa * (b/(m : ℝ)^2)^β) *
          (legalExtension b m x * phi σ (w-x))) := by
    funext x
    unfold altProbability
    ring
  rw [he, intervalIntegral.integral_add
    ((hp.const_mul _).intervalIntegrable 0 1)
    ((hv.const_mul _).intervalIntegrable 0 1)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    legalExtension_treated_convolution b σ m hb w]
  change (1/2 : ℝ) * ((1/2 : ℝ) * treatedConvolution σ w + _) = _
  ring

/-- Convolving the failure probability gives the second treated cell of ML.1. Given [the displayed inputs and assumptions](hyp:β,b,σ,m,s,hb,w), [the stated mathematical conclusion holds](goal). -/
lemma altProbability_failure_convolution (β b σ : ℝ) (m : ℕ) (s : Bool)
    (hb : b ∈ Ioc (0 : ℝ) 1) (w : ℝ) :
    (1/2 : ℝ) * (∫ x in (0 : ℝ)..1, (1-altProbability β b m s x) * phi σ (w-x)) =
      treatedConvolution σ w / 4 -
        witnessSign s * kappa * (b/(m : ℝ)^2)^β * markedConvolution b m σ w / 2 := by
  have hbp := hb.1
  have hp : Continuous (fun x => phi σ (w-x)) := by fun_prop
  have hv : Continuous (fun x => altProbability β b m s x * phi σ (w-x)) := by fun_prop
  have he : (fun x => (1-altProbability β b m s x) * phi σ (w-x)) =
      (fun x => phi σ (w-x) - altProbability β b m s x * phi σ (w-x)) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_sub (hp.intervalIntegrable 0 1)
    (hv.intervalIntegrable 0 1)]
  have hs := altProbability_success_convolution β b σ m s hb w
  change (1/2 : ℝ) * (treatedConvolution σ w - _) = _
  linarith

/-- The two treated-cell convolutions induced by the actual witness probabilities.
The factor one half is the uniform latent score density. Given [the displayed inputs and assumptions](hyp:β,b,σ,m,s,y,w), [this definition specifies the stated object](goal). -/
def witnessTreatedCellConvolution (β b σ : ℝ) (m : ℕ) (s y : Bool) (w : ℝ) : ℝ :=
  (1/2 : ℝ) * ∫ x in (0 : ℝ)..1,
    (if y then altProbability β b m s x else 1-altProbability β b m s x) * phi σ (w-x)

/-- Both actual treated-cell convolutions have the displayed ML.1 form. Given [the displayed inputs and assumptions](hyp:β,b,σ,m,s,y,hb,w), [the stated mathematical conclusion holds](goal). -/
lemma witnessTreatedCellConvolution_eq (β b σ : ℝ) (m : ℕ) (s y : Bool)
    (hb : b ∈ Ioc (0 : ℝ) 1) (w : ℝ) :
    witnessTreatedCellConvolution β b σ m s y w = treatedConvolution σ w/4 +
      witnessSign y * witnessSign s * kappa * (b/(m : ℝ)^2)^β *
        markedConvolution b m σ w/2 := by
  cases y
  · change (1/2 : ℝ) * (∫ x in (0 : ℝ)..1,
        (1-altProbability β b m s x) * phi σ (w-x)) = _
    rw [altProbability_failure_convolution β b σ m s hb w]
    simp only [witnessSign, Bool.false_eq_true, if_false]
    ring
  · change (1/2 : ℝ) * (∫ x in (0 : ℝ)..1,
        altProbability β b m s x * phi σ (w-x)) = _
    rw [altProbability_success_convolution β b σ m s hb w]
    simp only [witnessSign, if_true, one_mul]

/-- The actual minus-cell convolutions stay strictly positive everywhere. Given [the displayed inputs and assumptions](hyp:hleg,β,b,σ,m,s,y,hβ,hb,hm,hσ,w), [the stated mathematical conclusion holds](goal). -/
lemma witnessTreatedCellConvolution_lower (hleg : ClassicalLegendreFacts)
    (β b σ : ℝ) (m : ℕ) (s y : Bool) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) (hσ : 0 < σ) (w : ℝ) :
    treatedConvolution σ w/8 ≤ witnessTreatedCellConvolution β b σ m s y w := by
  have hd := marked_cell_denominator_lower (treatedConvolution σ w)
    (markedConvolution b m σ w) (kappa * (b/(m : ℝ)^2)^β)
    (treatedConvolution_pos σ w hσ).le (markedConvolution_abs_le hleg b σ m hb w)
    (marked_likelihood_amplitude_bound β b m hβ hb hm)
  rw [witnessTreatedCellConvolution_eq β b σ m s y hb w]
  cases s <;> cases y <;> simp only [witnessSign, Bool.false_eq_true, if_false, if_true]
  all_goals nlinarith [hd.1, hd.2]

/-- Summing the squared differences over both actual treated cells gives precisely
 the integrand already bounded in ML.2. Given [the displayed inputs and assumptions](hyp:β,b,σ,m,hb,w), [the stated mathematical conclusion holds](goal). -/
lemma witnessTreatedCellConvolution_square_difference_sum (β b σ : ℝ) (m : ℕ)
    (hb : b ∈ Ioc (0 : ℝ) 1) (w : ℝ) :
    (∑ y : Bool, (witnessTreatedCellConvolution β b σ m true y w -
      witnessTreatedCellConvolution β b σ m false y w)^2 /
        witnessTreatedCellConvolution β b σ m false y w) =
      ((kappa * (b/(m : ℝ)^2)^β)*markedConvolution b m σ w)^2 /
        (treatedConvolution σ w/4-kappa*(b/(m : ℝ)^2)^β*markedConvolution b m σ w/2) +
      ((kappa * (b/(m : ℝ)^2)^β)*markedConvolution b m σ w)^2 /
        (treatedConvolution σ w/4+kappa*(b/(m : ℝ)^2)^β*markedConvolution b m σ w/2) := by
  simp only [Fintype.sum_bool, witnessTreatedCellConvolution_eq β b σ m _ _ hb w,
    witnessSign, Bool.false_eq_true, if_false, if_true]
  ring

/-- The sum of the actual treated-cell likelihood contributions is integrable
on the whole real proxy line. Given [the displayed inputs and assumptions](hyp:hleg,β,b,σ,m,hβ,hb,hm,hσ), [the stated mathematical conclusion holds](goal). -/
lemma witnessTreatedCellConvolution_square_difference_integrable (hleg : ClassicalLegendreFacts)
    (β b σ : ℝ) (m : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) (hσ : 0 < σ) :
    Integrable (fun w : ℝ => ∑ y : Bool,
      (witnessTreatedCellConvolution β b σ m true y w -
        witnessTreatedCellConvolution β b σ m false y w)^2 /
          witnessTreatedCellConvolution β b σ m false y w) := by
  simp_rw [witnessTreatedCellConvolution_square_difference_sum β b σ m hb]
  exact marked_two_cell_square_integrable hleg b σ (kappa * (b/(m : ℝ)^2)^β) m hb hσ
    (marked_likelihood_amplitude_bound β b m hβ hb hm)

/-- ML.2 now applies to the convolutions of the actual witness probabilities,
with both outcomes summed and no restriction on the real proxy domain. Given [the displayed inputs and assumptions](hyp:hleg,β,b,σ,m,hβ,hb,hm,hσ), [the stated mathematical conclusion holds](goal). -/
lemma witnessTreatedCellConvolution_integral_bound (hleg : ClassicalLegendreFacts)
    (β b σ : ℝ) (m : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) (hσ : 0 < σ) :
    (∫ w : ℝ, ∑ y : Bool, (witnessTreatedCellConvolution β b σ m true y w -
      witnessTreatedCellConvolution β b σ m false y w)^2 /
        witnessTreatedCellConvolution β b σ m false y w) ≤
      16*kappa^2*(b/(m : ℝ)^2)^(2*β) *
        ∫ w : ℝ, markedConvolution b m σ w^2 / treatedConvolution σ w := by
  simp_rw [witnessTreatedCellConvolution_square_difference_sum β b σ m hb]
  exact marked_likelihood_density_integral_bound hleg β b σ m hβ hb hm hσ

end CausalSmith.Stat.RdTruesideNoiseFrontier
