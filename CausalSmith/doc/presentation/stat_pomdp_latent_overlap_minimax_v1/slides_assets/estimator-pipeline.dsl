node trajectory | Observed Trajectory | behavior path | horizon T
node policies | Known Policies | behavior and target
node overlap | Overlap Radius | latent stationary | q_C
node contraction | Contraction Bias | remote history fades | after window k
node ratio-variance | Ratio Variance | extra steps multiply | policy ratios
node depth | Calibrated Depth | window length k | from Tq_C²
node averaging | Clipped Averaging | partial-history weights | bounded contribution
node estimate | Target Estimate | stationary value | illustrative
edge trajectory -> depth
edge overlap -> depth
edge contraction -> depth
edge ratio-variance -> depth
edge trajectory -> averaging
edge policies -> averaging
edge depth -> averaging
edge averaging -> estimate
