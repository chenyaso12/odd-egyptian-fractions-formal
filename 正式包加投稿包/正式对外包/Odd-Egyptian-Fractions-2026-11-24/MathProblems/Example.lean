module

import Mathlib.Tactic.Ring

example (n : Nat) : n * (n + 1) = n ^ 2 + n := by
  ring
