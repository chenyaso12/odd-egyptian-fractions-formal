module

public import MathProblems.OddEgyptian.MaximumFiberCore
public import MathProblems.OddEgyptian.MaximumFiberPadding
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

/-- A family with a common prefix and many distinct endings gives as many large
maximum fibers as representations per fiber, at either adjacent odd length. -/
theorem maximumFamilies_of_prefix {m Q k : ℕ} {P Y : Finset ℕ} (h : IsPrefixFamily m Q P Y)
    (hm : 3 ≤ m) (hY : 2 ≤ Y.card) (hk : k = 2*m-1 ∨ k = 2*m+1) :
    HasMaximumFamilies k Q (Y.card/2-2*m) := by
  have base := MaximumFiberCore.maximumFamilies_base h hm hY
  rcases hk with rfl | rfl
  · exact base
  · rw [show 2*m+1 = (2*m-1)+2 by omega]
    exact maximumFamilies_pad base

end OddEgyptian
