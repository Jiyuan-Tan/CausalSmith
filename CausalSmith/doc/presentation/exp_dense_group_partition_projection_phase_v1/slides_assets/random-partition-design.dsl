node finite-pop | Finite pop | size n
node grouping | Random grouping | disjoint groups | common size M
node groups | Realized groups | Gₙ groups | Nₙ=M Gₙ
node sampling | Sampling fraction | Nₙ/n → ρ | study-group share
node assignment | Assignment | balanced groups | pₙ=G₁ₙ/Gₙ
node outcomes | Outcomes | observed group | outcomes
edge finite-pop -> grouping
edge grouping -> groups
edge groups -> sampling
edge groups -> assignment
edge groups -> outcomes
edge assignment -> outcomes
