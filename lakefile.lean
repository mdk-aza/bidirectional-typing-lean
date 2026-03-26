import Lake
open Lake DSL

package «bidirectional-typing-lean» where
  version := v!"0.1.0"
  defaultTargets := #[`BidirectionalTypingLean]

lean_lib BidirectionalTypingLean where
  globs := #[Glob.submodules `BidirectionalTypingLean]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"
