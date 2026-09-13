node observed-state | Observed state | one constant state
node observed-path | Observed path | actions and rewards
node hidden-coords | Hidden coords | depth and sign
node rare-histories | Rare histories | move latent state
node terminal-depth | Terminal depth | hard to detect
node reward-plus | Reward sign | terminal +
node reward-minus | Reward sign | terminal −
node target-value | Target value | differs by sign
edge observed-state -> observed-path
edge hidden-coords -> rare-histories
edge observed-path -> rare-histories
edge rare-histories -> terminal-depth
edge terminal-depth -> reward-plus
edge terminal-depth -> reward-minus
edge hidden-coords -> reward-plus
edge hidden-coords -> reward-minus
edge reward-plus -> target-value
edge reward-minus -> target-value
