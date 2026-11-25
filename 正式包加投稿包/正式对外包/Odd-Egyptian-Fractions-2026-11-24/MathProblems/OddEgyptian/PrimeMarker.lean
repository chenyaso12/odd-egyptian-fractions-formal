module

public import MathProblems.OddEgyptian.Growth
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

/-- The marked denominator specified in the manuscript: exactly the first r odd primes. -/
noncomputable def FirstOddProduct (r : ℕ) : ℕ :=
  ∏ i ∈ Finset.range r, Nat.nth Nat.Prime (i+1)

private theorem nthPrime_upper (i : ℕ) : Nat.nth Nat.Prime i ≤ 2^(i+1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    let q := Nat.nth Nat.Prime i
    obtain ⟨p, hp, hqp, hpq⟩ := Nat.bertrand q (Nat.prime_nth_prime _).ne_zero
    have hnext : Nat.nth Nat.Prime (i+1) ≤ p := by
      by_contra! h
      exact hqp.not_ge (Nat.le_nth_of_lt_nth_succ h hp)
    calc
      _ ≤ p := hnext
      _ ≤ 2*q := hpq
      _ ≤ 2*2^(i+1) := Nat.mul_le_mul_left 2 ih
      _ = 2^(i+1+1) := by ring

private theorem firstOddProduct_counts (r : ℕ) :
    Odd (FirstOddProduct r) ∧ (FirstOddProduct r).divisors.card = 2^r ∧
      (FirstOddProduct r).primeFactors.card = r := by
  induction r with
  | zero => simp [FirstOddProduct]
  | succ r ih =>
    let p := Nat.nth Nat.Prime (r+1)
    have hp : p.Prime := Nat.prime_nth_prime _
    have hp3 : 2 < p := by have := Nat.add_two_le_nth_prime (r+1); omega
    have cop : (FirstOddProduct r).Coprime p := by
      apply Nat.coprime_prod_left_iff.mpr
      intro j hj
      exact (Nat.coprime_primes (Nat.prime_nth_prime _) hp).mpr
        ((Nat.nth_strictMono Nat.infinite_setOfPred_prime)
          (show j+1 < r+1 by have := Finset.mem_range.mp hj; omega)).ne
    have div2 : p.divisors.card = 2 := by rw [hp.divisors]; simp [hp.ne_one.symm]
    rw [show FirstOddProduct (r+1) = FirstOddProduct r * p from Finset.prod_range_succ ..]
    refine ⟨ih.1.mul (hp.odd_of_ne_two hp3.ne'), ?_, ?_⟩
    · rw [cop.card_divisors_mul, ih.2.1, div2, pow_succ]
    · rw [cop.primeFactors_mul, Finset.card_union_of_disjoint cop.disjoint_primeFactors,
        ih.2.2, hp.primeFactors, Finset.card_singleton]

theorem firstOddProduct_primeFactors_card (r : ℕ) : (FirstOddProduct r).primeFactors.card = r :=
  (firstOddProduct_counts r).2.2

theorem firstOddProduct_spec (r : ℕ) (hr : 3 ≤ r) :
    3 ≤ FirstOddProduct r ∧ Odd (FirstOddProduct r) ∧
      Real.log (Real.log (FirstOddProduct r : ℝ)) ≤ 2*Real.log (r : ℝ) ∧
      (FirstOddProduct r).divisors.card = 2^r := by
  obtain ⟨hodd, hcard, _⟩ := firstOddProduct_counts r
  have h2 := Nat.pow_le_pow_right (by decide : 0 < 2) hr
  have hq : 3 ≤ FirstOddProduct r := by have := Nat.card_divisors_le_self (FirstOddProduct r); omega
  have prodBound : FirstOddProduct r ≤ (2^(r+1))^r := by
    calc
      _ ≤ ∏ _i ∈ Finset.range r, 2^(r+1) := by
        apply Finset.prod_le_prod
        intro i hi
        exact (nthPrime_upper (i+1)).trans (Nat.pow_le_pow_right (by decide)
          (by have := Finset.mem_range.mp hi; omega))
      _ = _ := by simp
  refine ⟨hq, hodd, ?_, hcard⟩
  have qPos : (0 : ℝ) < FirstOddProduct r := by exact_mod_cast hodd.pos
  have bound := Real.log_le_log qPos
    (show (FirstOddProduct r : ℝ) ≤ ((2 : ℝ)^(r+1))^r by exact_mod_cast prodBound)
  rw [Real.log_pow, Real.log_pow] at bound
  push_cast at bound
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have log2 : Real.log 2 ≤ 3/4 := by linarith [Real.log_two_lt_d9]
  have factor : ((r : ℝ)+1)*Real.log 2 ≤ r := by
    linarith [mul_le_mul_of_nonneg_left log2 (by positivity : 0 ≤ (r : ℝ)+1)]
  have hlog : Real.log (FirstOddProduct r : ℝ) ≤ (r : ℝ)^2 := by
    simpa [pow_two] using bound.trans (mul_le_mul_of_nonneg_left factor (Nat.cast_nonneg r))
  have hpos : 0 < Real.log (FirstOddProduct r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < FirstOddProduct r by omega))
  simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hpos hlog

end OddEgyptian
