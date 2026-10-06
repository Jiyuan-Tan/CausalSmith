module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Basic
public import Causalean.Stat.Privacy.LaplaceMechanism

/-! # Published custom Laplace comparator

The custom Horvitz–Thompson score is released with independent centered
Laplace noise at the published sensitivity scale. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- @env: S6
variable (p ε : ℝ)

/-- For [the supplied quantities and conditions](hyp:p), the [sensitivity](goal) is the mathematical object specified below. -/
def sensitivity (p : ℝ) : ℝ :=
  p⁻¹ + (controlProb p)⁻¹
  -- @realizes \Delta_A(1/p+1/q)

/-- For the supplied quantities and conditions, the comparator noise law is the mathematical object specified below. [The comparator Noise Law](goal) is determined by [the displayed parameters](hyp:p,ε). -/
def comparatorNoiseLaw (p ε : ℝ) : Measure ℝ :=
  Causalean.Stat.Privacy.laplaceMeasure (sensitivity p / ε)
  -- @realizes L_i(Laplace marginal at Delta_A/epsilon)

/-- The observed-record/noise pairs are jointly independent across subjects; each noise has the published Laplace marginal and is independent of its observed private record. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The Comparator Noise](goal) is determined by [the displayed parameters](hyp:μ,W,Y,L,p,ε). -/
def ComparatorNoise {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W Y L : ℕ → Ω → ℝ) (p ε : ℝ) : Prop :=
  iIndepFun (fun i ω => (privateRecord W Y i ω, L i ω)) μ ∧
  (∀ i, μ.map (L i) = comparatorNoiseLaw p ε) ∧
  (∀ i, IndepFun (L i) (privateRecord W Y i) μ)

/-- For the supplied quantities and conditions, the oa release value is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The oa Release Value](goal) is determined by [the displayed parameters](hyp:W,Y,L,p,i,ω). -/
def oaReleaseValue {Ω : Type*} (W Y L : ℕ → Ω → ℝ) (p : ℝ)
    (i : ℕ) (ω : Ω) : ℝ :=
  W i ω * Y i ω / p -
    (1 - W i ω) * Y i ω / controlProb p + L i ω
  -- @realizes \widetilde A_i(private custom release)

-- @node: def:oa-release
/-- the oa release is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The oa Release](goal) is determined by [the displayed parameters](hyp:μ,W,Y,L,A,τhat,p,ε,Δ). -/
def oaRelease {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W Y L A : ℕ → Ω → ℝ)
    (τhat : ℕ → Ω → ℝ) (p ε Δ : ℝ) : Prop :=
  InteriorAssignment p ∧
  0 < ε ∧
  Δ = sensitivity p ∧
  Δ = 1 / (p * controlProb p) ∧
  ComparatorNoise μ W Y L p ε ∧
  (∀ i ω, A i ω = oaReleaseValue W Y L p i ω) ∧
  (∀ n ≥ 1, ∀ ω, τhat n ω = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, A i ω)

/-- For the supplied quantities and conditions, the tau oa is the mathematical object specified below. [The tau OA](goal) is determined by [the displayed parameters](hyp:W,Y,L,p,n,ω). -/
def tauOA {Ω : Type*} (W Y L : ℕ → Ω → ℝ) (p : ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, oaReleaseValue W Y L p i ω
  -- @realizes \widehat\tau_{\mathrm{OA}}(sample mean release)

/-- For the supplied quantities and conditions, the vhat oa is the mathematical object specified below. [The Vhat OA](goal) is determined by [the displayed parameters](hyp:W,Y,L,p,n,ω). -/
def VhatOA {Ω : Type*} (W Y L : ℕ → Ω → ℝ) (p : ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    (oaReleaseValue W Y L p i ω - tauOA W Y L p n ω) ^ 2

-- @node: VhatOA_eq_second_moment_sub_sq
/-- [the vhat oa eq second moment sub sq assertion](goal) holds. For [the displayed quantities and conditions](hyp:W,Y,L,p,n,hn), these specify the stated inputs. -/
lemma VhatOA_eq_second_moment_sub_sq {Ω : Type*}
    (W Y L : ℕ → Ω → ℝ) (p : ℝ) (n : ℕ) (hn : 0 < n) (ω : Ω) :
    VhatOA W Y L p n ω =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        (oaReleaseValue W Y L p i ω) ^ 2 -
      (tauOA W Y L p n ω) ^ 2 := by
  let a : ℕ → ℝ := fun i => oaReleaseValue W Y L p i ω
  let m : ℝ := tauOA W Y L p n ω
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hm : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i = m := rfl
  simp only [VhatOA, a, m, sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hcross :
      (∑ i ∈ Finset.range n, 2 * a i * m) =
        2 * m * ∑ i ∈ Finset.range n, a i := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  simp only [Finset.sum_const, Finset.card_range]
  change (n : ℝ)⁻¹ *
      ((∑ i ∈ Finset.range n, a i ^ 2) -
        (∑ i ∈ Finset.range n, 2 * a i * m) + n • m ^ 2) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i ^ 2 - m ^ 2
  rw [hcross]
  simp only [nsmul_eq_mul]
  field_simp at hm ⊢
  rw [hm]
  ring

/-- For the supplied quantities and conditions, the voa is the mathematical object specified below. [The VOA](goal) is determined by [the displayed parameters](hyp:θ,p,ε). -/
def VOA (θ : TrialParameter) (p ε : ℝ) : ℝ :=
  θ 1 / p + θ 0 / controlProb p -
    (contrast θ) ^ 2 + 2 * (sensitivity p) ^ 2 / ε ^ 2
  -- @realizes V_{\mathrm{OA}}(\theta,p,\varepsilon)(asymptotic variance)

end CausalSmith.Stat.LdpAteEfficiencySurface
