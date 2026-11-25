module

public import MathProblems.OddEgyptian.TailPrefix
public import MathProblems.OddEgyptian.TernaryTail

@[expose] public section

namespace OddEgyptian

/-- Every positive integer has a representation above every prescribed cutoff. -/
theorem oddTailBasis : OddTailBasis := oddTailBasis_of_ternary ternary_proper

end OddEgyptian
