module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Deterministic sample split and multinomial factorial statistic
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open scoped BigOperators

/-- For [the displayed parameters](hyp:n), [pilotSize](goal) is the object specified by this definition. -/
def pilotSize (n : ℕ) : ℕ := n / 2
  -- @realizes \(n_{\mathrm p}\)(floor half sample)

/-- For [the displayed parameters](hyp:n,hn), [evalSize](goal) is the object specified by this definition. -/
def evalSize (n : ℕ) (_hn : 1 ≤ n) : ℕ := n - pilotSize n
  -- @realizes \(n_{\mathrm e}\)(remaining sample)

/-- For [the displayed parameters](hyp:n), [pilotIndices](goal) is the object specified by this definition. -/
def pilotIndices (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < pilotSize n)
  -- @realizes \(I_{\mathrm p}\)(pilot indices)

/-- For [the displayed parameters](hyp:n), [evalIndices](goal) is the object specified by this definition. -/
def evalIndices (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => pilotSize n ≤ i.val)
  -- @realizes \(I_{\mathrm e}\)(evaluation indices)

/-- For [the displayed parameters](hyp:n,d,o,j), [pilotCount](goal) is the object specified by this definition. -/
def pilotCount {n d : ℕ} (o : Fin n → Obs d) (j : Obs d) : ℕ :=
  ∑ i ∈ pilotIndices n, if o i = j then 1 else 0
  -- @realizes \(N_j^{\mathrm p}\)(pilot category count)
  -- @realizes \(N^{\mathrm p}\)(pilot histogram)

/-- For [the displayed parameters](hyp:n,d,o,j), [evalCount](goal) is the object specified by this definition. -/
def evalCount {n d : ℕ} (o : Fin n → Obs d) (j : Obs d) : ℕ :=
  ∑ i ∈ evalIndices n, if o i = j then 1 else 0
  -- @realizes \(N_j^{\mathrm e}\)(evaluation category count)
  -- @realizes \(N^{\mathrm e}\)(evaluation histogram)

-- @node: def:fixed-sample-factorial
/-- For [the displayed parameters](hyp:d,n,hn,o,b,h,hh), [multinomialFactorialLift](goal) is the object specified by this definition. -/
noncomputable def multinomialFactorialLift {d : ℕ}
    {n : ℕ} (hn : 1 ≤ n) (o : Fin n → Obs d) (b : Obs d → ℝ) (h : Obs d → ℕ)
    (_hh : (∑ j : Obs d, h j) ≤ evalSize n hn) : ℝ :=
  let Ne := evalCount o
  let ne := evalSize n hn
  ∑ t ∈ Fintype.piFinset (fun j : Obs d => Finset.range (h j + 1)),
    (∏ j : Obs d, ((h j).choose (t j) : ℝ) * (-b j) ^ (h j - t j)) *
      (∏ j : Obs d, ((Ne j).descFactorial (t j) : ℝ)) /
      (ne.descFactorial (∑ j : Obs d, t j) : ℝ)
  -- @realizes \(\boldsymbol h\)(factorial multi-index)
  -- @realizes \(\boldsymbol t\)(summation multi-index)
  -- @realizes \(\boldsymbol r\)(overlap index in mixed moments)
  -- @realizes \(b\)(centering vector)
  -- @realizes \(U_{\boldsymbol h}(N^{\mathrm e};b)\)(centered multinomial lift)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
