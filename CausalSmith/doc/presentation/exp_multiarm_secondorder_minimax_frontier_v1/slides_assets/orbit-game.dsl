node labeled-schedule | Labeled schedule | unit labels arbitrary
node labeled-procedure | Labeled procedure | before relabel averaging
node invariant-procedure | Invariant procedure | common relabel average
node response-counts | Response-type counts | m = counts(z)
node observed-counts | Observed counts | allocation counts | arm-success counts
node orbit-procedure | Orbit procedure | same count rules
node orbit-game | Finite orbit game | finite decision problem
edge labeled-procedure -> invariant-procedure
edge invariant-procedure -> orbit-procedure
edge labeled-schedule -> response-counts
edge labeled-schedule -> observed-counts
edge response-counts -> orbit-game
edge observed-counts -> orbit-game
edge orbit-procedure -> orbit-game
