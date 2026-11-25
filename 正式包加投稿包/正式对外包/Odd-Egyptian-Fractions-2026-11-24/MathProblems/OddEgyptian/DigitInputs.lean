module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Finset.Prod

@[expose] public section

namespace OddEgyptian

noncomputable def NatResidueGood (F : Finset ℕ) (p : ℕ) : Prop :=
  (p:ℝ)^(3/4:ℝ) < ((F.image (· % p)).card:ℝ)

def GoodPrime (F : Finset ℕ) (p : ℕ) : Prop := p.Prime ∧ Odd p ∧ NatResidueGood F p

def ThreeGood (F : Finset ℕ) (m : ℕ) : Prop :=
  ∃ p q t : ℕ, GoodPrime F p ∧ GoodPrime F q ∧ GoodPrime F t ∧ p+q+t=m

/-- Ordered representations; equal primes are allowed and 2 is excluded. -/
def threePrimeReps (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (m+1)) ×ˢ ((Finset.range (m+1)) ×ˢ Finset.range (m+1))).filter
    fun (a,b,c) => a+b+c=m ∧ a.Prime ∧ Odd a ∧ b.Prime ∧ Odd b ∧ c.Prime ∧ Odd c

/-- The quantitative form of Vinogradov used in the manuscript. -/
def ThreePrimeInput : Prop :=
  ∃ v : ℝ, 0 < v ∧ ∃ m₀ : ℕ, 7 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → Odd m →
    v*(m:ℝ)^2 / (Real.log (m:ℝ))^3 ≤ ((threePrimeReps m).card:ℝ)

end OddEgyptian
