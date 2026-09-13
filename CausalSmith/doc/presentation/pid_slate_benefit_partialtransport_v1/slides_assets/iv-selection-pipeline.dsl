node instrument-offer | Instrument offer | changes training receipt
node treatment-receipt | Treatment receipt | training state
node employment-selection | Employment selection | wages observed after
node wage-category | Wage category | ordered outcome
node iv-compliers | IV compliers | receipt shifted
node always-selected | Always-selected | observed both states
node survivor-compliers | Survivor-compliers | combined target group
node benefit-target | Same-unit target | strictly better off
edge instrument-offer -> treatment-receipt
edge treatment-receipt -> employment-selection
edge employment-selection -> wage-category
edge instrument-offer -> iv-compliers
edge treatment-receipt -> iv-compliers
edge employment-selection -> always-selected
edge iv-compliers -> survivor-compliers
edge always-selected -> survivor-compliers
edge survivor-compliers -> benefit-target
edge wage-category -> benefit-target
