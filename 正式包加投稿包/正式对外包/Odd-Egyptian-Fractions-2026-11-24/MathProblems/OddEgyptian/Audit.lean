import Lean.Util.CollectAxioms
import MathProblems.OddEgyptian

#check OddEgyptian.englishManuscript_of_threePrimeInput
#check OddEgyptian.englishManuscript_of_mangoldt
#print OddEgyptian.EnglishManuscriptResults
#print OddEgyptian.UniformMinLengthTarget
#print OddEgyptian.LengthStatisticsTarget
#print OddEgyptian.PrimorialLengthTarget
#print OddEgyptian.CommonPrefixTarget
#print OddEgyptian.IsPrefixFamily
#print OddEgyptian.MaximumMultiplicityTarget
#print OddEgyptian.HasMaximumFamilies
#print axioms OddEgyptian.englishManuscript_of_threePrimeInput
#print axioms OddEgyptian.englishManuscript_of_mangoldt

#check OddEgyptian.main_of_threePrimeInput
#check OddEgyptian.main_of_mangoldt
#check OddEgyptian.mangoldtInput_of_singularSeries
#check OddEgyptian.main_of_allPrimeTriples
#check OddEgyptian.main_of_logWeightedPrimes
#check OddEgyptian.counting_of_short
#check OddEgyptian.oddCount_le_sharp
#check OddEgyptian.oddCount_exp_upper_two
#check OddEgyptian.markedExact_of_threePrimeInput
#check OddEgyptian.oddCount_exp_upper
#check OddEgyptian.finitenessTarget
#check OddEgyptian.represents_one_odd_card
#check OddEgyptian.oddTailBasis
#check OddEgyptian.maximum_of_short
#check OddEgyptian.maximum_of_threePrimeInput

#print OddEgyptian.HTarget
#print OddEgyptian.CTarget
#print OddEgyptian.ThreePrimeInput
#print OddEgyptian.MaximumTarget
#print OddEgyptian.MarkedExactTarget
#print axioms OddEgyptian.main_of_threePrimeInput
#print axioms OddEgyptian.main_of_mangoldt
#print axioms OddEgyptian.mangoldtInput_of_singularSeries
#print axioms OddEgyptian.main_of_allPrimeTriples
#print axioms OddEgyptian.main_of_logWeightedPrimes
#print axioms OddEgyptian.counting_of_short
#print axioms OddEgyptian.oddCount_le_sharp
#print axioms OddEgyptian.oddCount_exp_upper_two
#print axioms OddEgyptian.markedExact_of_threePrimeInput
#print axioms OddEgyptian.oddCount_exp_upper
#print axioms OddEgyptian.finitenessTarget
#print axioms OddEgyptian.represents_one_odd_card
#print axioms OddEgyptian.oddTailBasis
#print axioms OddEgyptian.maximum_of_short
#print axioms OddEgyptian.maximum_of_threePrimeInput

-- Published definition: https://prove2.me/theorems/f0c405a4-66a9-4864-8b3d-0917ce24ebe6
open Finset
noncomputable section
namespace ExternalDefinitionCheck

noncomputable def R (n : ℕ) : ℝ :=
  ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1),
    if a + b + c = n then
      (ArithmeticFunction.vonMangoldt a : ℝ) * (ArithmeticFunction.vonMangoldt b : ℝ)
        * (ArithmeticFunction.vonMangoldt c : ℝ)
    else 0

theorem published_R_eq_local (n : ℕ) : R n = OddEgyptian.mangoldtTripleSum n := by rfl
#print axioms published_R_eq_local

end ExternalDefinitionCheck

/- Check the transitive Lean axiom dependencies of every exported research declaration. -/
run_cmd do
  let env ← Lean.getEnv
  let names := env.constants.fold (init := #[]) fun acc name _ =>
    if (`OddEgyptian).isPrefixOf name || name == ``ExternalDefinitionCheck.published_R_eq_local
    then acc.push name else acc
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let unexpected := (← Lean.collectAxioms name).filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependencies for {name}: {unexpected}"
  Lean.logInfo m!"Axiom audit passed for {names.size} declarations."
