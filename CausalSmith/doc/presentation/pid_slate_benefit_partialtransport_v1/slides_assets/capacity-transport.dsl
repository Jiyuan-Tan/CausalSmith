node observed-law | Observed law | selected compliers
node lower-capacity | Lower-arm capacity | Y₀ submargin
node upper-capacity | Upper-arm capacity | Y₁ submargin
node unequal-totals | Unequal totals | selection can differ
node survivor-mass | Survivor mass | exact m(x) | each cell
node partial-transport | Partial transport | exact-mass pairing
node benefit-mass | Benefit mass | Y₁ strictly above Y₀
edge observed-law -> lower-capacity
edge observed-law -> upper-capacity
edge lower-capacity -> unequal-totals
edge upper-capacity -> unequal-totals
edge lower-capacity -> survivor-mass
edge upper-capacity -> survivor-mass
edge survivor-mass -> partial-transport
edge lower-capacity -> partial-transport
edge upper-capacity -> partial-transport
edge partial-transport -> benefit-mass
