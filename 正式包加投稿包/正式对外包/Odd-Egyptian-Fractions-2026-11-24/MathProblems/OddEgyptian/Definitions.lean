module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace OddEgyptian

def Represents (q : ℚ) (s : Finset ℕ) : Prop :=
  (∀ n ∈ s, 1 < n ∧ Odd n) ∧ s.sum (fun n => (1 : ℚ) / (n : ℚ)) = q

def Solutions (k : ℕ) : Type :=
  {s : Finset ℕ // Represents 1 s ∧ s.card = k}

noncomputable def oddCount (k : ℕ) : ℕ := Nat.card (Solutions k)

def FinitenessTarget : Prop := ∀ k : ℕ, Finite (Solutions k)

def HTarget : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, 3 ≤ b → Odd b → 1 ≤ a → a < b →
    ∃ s : Finset ℕ, Represents ((a : ℚ) / (b : ℚ)) s ∧
      (s.card : ℝ) ≤ C * (1 + Real.log (Real.log (b : ℝ)))

def CTarget : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Odd k →
    Real.exp (Real.exp (c * (k : ℝ))) ≤ (oddCount k : ℝ) ∧
      (oddCount k : ℝ) ≤ Real.exp (Real.exp (C * (k : ℝ)))

end OddEgyptian
