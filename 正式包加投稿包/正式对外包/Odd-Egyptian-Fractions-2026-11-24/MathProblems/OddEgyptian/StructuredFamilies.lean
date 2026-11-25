module

public import MathProblems.OddEgyptian.MaximumTheorem
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

/-- A common increasing prefix followed by two odd denominators. The index is the last one. -/
def IsPrefixFamily (k Q : ℕ) (P Y : Finset ℕ) : Prop :=
  P.card + 2 = k ∧ ∀ y ∈ Y, ∃ x : ℕ, (∀ p ∈ P, p < x) ∧ x < y ∧
    Represents 1 (insert y (insert x P)) ∧ Q ∣ y

/-- Theorem 1.3: one prefix of length k-2 with doubly exponentially many endings. -/
def CommonPrefixTarget : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Odd k →
    ∃ P Y : Finset ℕ, IsPrefixFamily k (FirstOddProduct ⌊Real.exp (c * (k : ℝ))⌋₊) P Y ∧
      Real.exp (Real.exp (c * (k : ℝ))) ≤ (Y.card : ℝ)

/-- At least n distinct maxima, each attained by at least n distinct solutions. -/
def HasMaximumFamilies (k Q n : ℕ) : Prop :=
  ∃ M : Finset ℕ, n ≤ M.card ∧ ∀ y ∈ M, Q ∣ y ∧ ∃ S : Finset (Finset ℕ),
    n ≤ S.card ∧ ∀ s ∈ S, Represents 1 s ∧ s.card = k ∧ s.sup id = y

/-- Corollary 1.4: the same lower bound holds both for the number of maxima and for
the number of representations at each such maximum. -/
def MaximumMultiplicityTarget : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Odd k →
    HasMaximumFamilies k (FirstOddProduct ⌊Real.exp (c * (k : ℝ))⌋₊)
      ⌈Real.exp (Real.exp (c * (k : ℝ)))⌉₊

theorem firstOddProduct_dvd_of_le {a b : ℕ} (hab : a ≤ b) :
    FirstOddProduct a ∣ FirstOddProduct b := by
  induction b, hab using Nat.le_induction with
  | base => exact dvd_refl _
  | succ b _ ih =>
    have step : FirstOddProduct (b+1) = FirstOddProduct b * Nat.nth Nat.Prime (b+1) :=
      Finset.prod_range_succ ..
    exact ih.trans (step ▸ dvd_mul_right ..)

end OddEgyptian
