module

public import MathProblems.OddEgyptian.Research
public import MathProblems.OddEgyptian.LengthOptimality
public import MathProblems.OddEgyptian.PrimorialLength
public import MathProblems.OddEgyptian.CommonPrefix
public import MathProblems.OddEgyptian.MultiplicityGrowth

@[expose] public section

namespace OddEgyptian

/-- Main results of the revised English manuscript. Field names follow the paper. -/
structure EnglishManuscriptResults : Prop where
  uniformLength : UniformMinLengthTarget
  maximumAndMeanLength : LengthStatisticsTarget
  leastLengthWithPrescribedPrimes : PrimorialLengthTarget
  commonPrefix : CommonPrefixTarget
  totalCount : CTarget
  multiplicityAtMaximum : MaximumMultiplicityTarget

/-- A single, quantitative three-odd-prime input implies all four numbered results. -/
theorem englishManuscript_of_threePrimeInput (vinogradov : ThreePrimeInput) :
    EnglishManuscriptResults := by
  obtain ⟨short,count⟩ := main_of_threePrimeInput vinogradov
  have maximum := maximum_of_short short
  have common := commonPrefix_of_maximum maximum
  exact ⟨uniformMinLength_of_short short, lengthStatistics_of_short short,
    primorialLength_of_maximum maximum, common, count, maximumMultiplicity_of_commonPrefix common⟩

/-- The weighted version can be used through the existing prime-power conversion. -/
theorem englishManuscript_of_mangoldt (vinogradov : MangoldtTripleInput) :
    EnglishManuscriptResults :=
  englishManuscript_of_threePrimeInput (threePrimeInput_of_mangoldt vinogradov)

end OddEgyptian
