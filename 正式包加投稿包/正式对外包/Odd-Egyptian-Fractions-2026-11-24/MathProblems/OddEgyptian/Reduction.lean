module

public import MathProblems.OddEgyptian.Main
public import MathProblems.OddEgyptian.Layers
public import MathProblems.OddEgyptian.PrefixConstruction
public import MathProblems.OddEgyptian.TailBasis

@[expose] public section

namespace OddEgyptian

theorem short_of_layeredDigits (hd : LayeredDigitTarget) : HTarget :=
  hTarget_of_small_and_basis (smallNumerator_of_layeredDigits oddTailBasis hd) oddTailBasis

theorem counting_of_layeredDigits (hd : LayeredDigitTarget) : CTarget :=
  counting_of_short (short_of_layeredDigits hd)

end OddEgyptian
