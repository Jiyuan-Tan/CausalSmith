node population-law | Population law | same population
node labeled-records | Labeled records | n records | X,A,Y
node auxiliary-records | Auxiliary records | m records | X,A
node xa-table | XA table | P_XA sharpened
node outcome-reg | Outcome regressions | outcome information
node ate-estimate | ATE estimate | final target
edge population-law -> labeled-records
edge population-law -> auxiliary-records
edge labeled-records -> xa-table
edge auxiliary-records -> xa-table
edge labeled-records -> outcome-reg
edge xa-table -> ate-estimate
edge outcome-reg -> ate-estimate
