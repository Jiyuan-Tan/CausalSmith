node same-sign | Same sign | same across arms
node independent-sign | Independent sign | separately by arm
node observation-law | Observation law | assigned-arm outcomes | same mixture
node statistic | Any statistic | one realization
node same-variance | Exact variance | same-sign limit
node independent-variance | Exact variance | independent-sign limit
node separated-limits | Separated limits | when ρ > 0
edge same-sign -> observation-law
edge independent-sign -> observation-law
edge observation-law -> statistic
edge same-sign -> same-variance
edge independent-sign -> independent-variance
edge same-variance -> separated-limits
edge independent-variance -> separated-limits
