node coarse-pair | Coarse pair | Shared sign σⱼ
node left-cell | Left coarse cell | Interior fine cell | Disjoint fine-node sign
node right-cell | Right coarse cell | Interior fine cell | Disjoint fine-node sign
node left-nonzero | Nonzero outcome
node left-zero | Zero outcome
node right-nonzero | Nonzero outcome
node right-zero | Zero outcome
edge coarse-pair -> left-cell
edge coarse-pair -> right-cell
edge left-cell -> left-nonzero
edge left-cell -> left-zero
edge right-cell -> right-nonzero
edge right-cell -> right-zero
