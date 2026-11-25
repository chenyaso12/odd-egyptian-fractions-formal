module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

public section

namespace OddEgyptian

/-- A finite certificate for the ternary digit 2. All denominators are coprime to 6.
The small denominators add up to 1 without the entry 1; adjoining it represents 2. -/
private def digitTwo : Finset ℕ :=
  {1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 55, 65, 77,
    85, 91, 95, 377, 4655, 156275, 275852353, 8801304090425,
    13043116600361939, 717371413019906645}

set_option maxRecDepth 20000 in
private theorem digitTwo_sum : (∑ c ∈ digitTwo, (1:ℚ)/c) = 2 := by decide +kernel

set_option maxRecDepth 20000 in
private theorem digitTwo_spec : ∀ c ∈ digitTwo, Odd c ∧ ¬3 ∣ c ∧ c ≤ 717371413019906645 :=
  by decide +kernel

/-- A single fixed supply of pairwise distinct, odd, 3-free denominators for all three digits. -/
theorem ternaryDigitWitness : ∃ R : ℕ, ∀ m : ℕ, m < 3 → ∃ S : Finset ℕ,
    (∑ c ∈ S, (1:ℚ)/c) = m ∧ ∀ c ∈ S, Odd c ∧ ¬3 ∣ c ∧ c ≤ R := by
  refine ⟨717371413019906645, ?_⟩
  intro m hm
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by simp, by simp⟩
  · exact ⟨digitTwo, by simpa using digitTwo_sum, digitTwo_spec⟩

end OddEgyptian
