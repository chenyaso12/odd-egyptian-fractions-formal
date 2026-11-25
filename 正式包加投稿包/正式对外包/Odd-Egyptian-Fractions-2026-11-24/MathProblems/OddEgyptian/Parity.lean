module

public import MathProblems.OddEgyptian.Definitions
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace OddEgyptian

/-- Clear the (odd) common denominator before taking parity. -/
theorem represents_one_odd_card {s : Finset ℕ} (hs : Represents 1 s) : Odd s.card := by
  let D := s.prod id
  have hD : D ≡ 1 [MOD 2] := Nat.ModEq.prod_one fun n hn => by
    simpa [Nat.ModEq, Nat.odd_iff] using (hs.1 n hn).2
  have hdvd (n) (hn : n ∈ s) : n ∣ D := Finset.dvd_prod_of_mem id hn
  have hodd (n) (hn : n ∈ s) : Odd (D / n) := by
    have h : Odd ((D / n) * n) := by
      rw [Nat.div_mul_cancel (hdvd n hn)]
      simpa [Nat.ModEq, Nat.odd_iff] using hD
    exact (Nat.odd_mul.mp h).1
  have hsum : ∑ n ∈ s, D / n = D := by
    have hrat : (∑ n ∈ s, ((D / n : ℕ) : ℚ)) = D := calc
      _ = ∑ n ∈ s, (D : ℚ) * (1 / n) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [show (D : ℚ) * (1 / n) = D / n by ring, eq_div_iff (by have := (hs.1 n hn).1; positivity)]
        exact_mod_cast Nat.div_mul_cancel (hdvd n hn)
      _ = _ := by rw [← Finset.mul_sum, hs.2, mul_one]
    exact_mod_cast hrat
  have hm := Nat.ModEq.sum (s := s) (g := fun _ => 1) (n := 2)
    (fun n hn => (show D / n ≡ 1 [MOD 2] by simpa [Nat.ModEq, Nat.odd_iff] using hodd n hn))
  rw [hsum] at hm
  have : s.card ≡ 1 [MOD 2] := (by simpa using hm.symm : s.card ≡ D [MOD 2]).trans hD
  simpa [Nat.ModEq, Nat.odd_iff] using this

end OddEgyptian
