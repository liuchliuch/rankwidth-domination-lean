import Mathlib.Tactic

namespace RankwidthDomination.WitnessMachine

inductive Register
  | input | remaining | index | output | scratch
  | size | transitions | power | layerSize | checkerSize | vertices
  | temporary | temporary2 | length | blocks
  | target | layers | countIndex | countRemaining | counterScratch
  deriving DecidableEq, Fintype


end RankwidthDomination.WitnessMachine
