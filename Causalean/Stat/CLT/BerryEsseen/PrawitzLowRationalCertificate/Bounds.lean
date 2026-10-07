module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Tables00
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Tables01
public import Causalean.Stat.CLT.BerryEsseen.PrawitzLowRationalCertificate.Tables02

/-! # Low Prawitz certificate: selector for the candidate bound tables

Assembles the ten-row tables into one lookup indexed by the parameter cell.
-/

@[expose] public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxRecDepth 1000000

/-- The list of candidate integer upper bounds for parameter cell j: row
j mod 10 of the ⌊j/10⌋-th of twenty-seven ten-row tables, and the empty list
when j is out of range. The candidates are data; each is checked separately
by the certificate. -/
def lowBounds (j : ℕ) : List ℤ :=
  ((#[lowBounds00, lowBounds01, lowBounds02, lowBounds03, lowBounds04, lowBounds05, lowBounds06, lowBounds07, lowBounds08, lowBounds09, lowBounds10, lowBounds11, lowBounds12, lowBounds13, lowBounds14, lowBounds15, lowBounds16, lowBounds17, lowBounds18, lowBounds19, lowBounds20, lowBounds21, lowBounds22, lowBounds23, lowBounds24, lowBounds25, lowBounds26].getD (j / 10) #[]).getD (j % 10) [])

end Causalean.Stat.CLT.BerryEsseen
