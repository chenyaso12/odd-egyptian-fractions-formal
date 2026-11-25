module

public import MathProblems.OddEgyptian.DigitConclusion
public import MathProblems.OddEgyptian.Reduction
public import MathProblems.OddEgyptian.MaximumTheorem
public import MathProblems.OddEgyptian.PrimePowerBridge

@[expose] public section

namespace OddEgyptian

/-- The two main conclusions of the manuscript from the quantitative three-prime theorem. -/
theorem main_of_threePrimeInput (vinogradov : ThreePrimeInput) : HTarget ∧ CTarget := by
  have h := short_of_layeredDigits (layeredDigits_of_threePrimeInput vinogradov)
  exact ⟨h, counting_of_short h⟩

/-- The classical unweighted formulation may count the prime two. -/
theorem main_of_allPrimeTriples (vinogradov : AllPrimeTripleInput) : HTarget ∧ CTarget :=
  main_of_threePrimeInput (threePrimeInput_of_allPrimes vinogradov)

theorem main_of_logWeightedPrimes (vinogradov : LogWeightedPrimeTripleInput) : HTarget ∧ CTarget :=
  main_of_threePrimeInput (threePrimeInput_of_logWeighted vinogradov)

theorem main_of_mangoldt (vinogradov : MangoldtTripleInput) : HTarget ∧ CTarget :=
  main_of_threePrimeInput (threePrimeInput_of_mangoldt vinogradov)

theorem maximum_of_threePrimeInput (vinogradov : ThreePrimeInput) : MaximumTarget :=
  maximum_of_short (main_of_threePrimeInput vinogradov).1

end OddEgyptian
