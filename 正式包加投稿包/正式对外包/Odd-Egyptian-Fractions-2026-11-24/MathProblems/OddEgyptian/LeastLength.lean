module

public import MathProblems.OddEgyptian.Definitions
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace OddEgyptian

/-- The least cardinality in an inhabited family of denominator sets.
The natural-number infimum of an empty family is zero. -/
noncomputable def leastDenominatorCard (P : Finset ℕ → Prop) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, ∃ s : Finset ℕ, P s ∧ s.card = k then Nat.find h else 0

theorem leastDenominatorCard_attained {P : Finset ℕ → Prop} (h : ∃ s, P s) :
    ∃ s, P s ∧ s.card = leastDenominatorCard P := by
  classical
  obtain ⟨s, hs⟩ := h
  have hex : ∃ k : ℕ, ∃ t : Finset ℕ, P t ∧ t.card = k := ⟨s.card, s, hs, rfl⟩
  simpa only [leastDenominatorCard, dite_eq_left hex] using Nat.find_spec hex

theorem leastDenominatorCard_le {P : Finset ℕ → Prop} {s : Finset ℕ} (hs : P s) :
    leastDenominatorCard P ≤ s.card := by
  classical
  have hex : ∃ k : ℕ, ∃ t : Finset ℕ, P t ∧ t.card = k := ⟨s.card, s, hs, rfl⟩
  simpa only [leastDenominatorCard, dite_eq_left hex] using Nat.find_min' hex
    (show ∃ t, P t ∧ t.card = s.card from ⟨s,hs,rfl⟩)

end OddEgyptian
