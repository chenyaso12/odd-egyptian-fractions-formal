module

public import Mathlib.NumberTheory.LSeries.WeakPNT
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

@[expose] public section

open Filter

namespace OddEgyptian

/-- The odd squarefree primorial at a real cutoff. -/
noncomputable def oddPrimeProduct (x : ℝ) : ℕ :=
  ∏ p ∈ (Nat.primesLE ⌊x⌋₊).erase 2, p

/-- The exact growth inequalities used from Chebyshev estimates. Both lower
constants can be taken to be 1/2, and 2 is a common upper constant. -/
theorem chebyshevInputs :
    (∃ t : ℝ, 3 ≤ t ∧ ∀ x : ℝ, t ≤ x →
      (1 / 2 : ℝ) * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
      (1 / 2 : ℝ) * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ 2 * x) ∧
    ∀ x : ℝ, 0 < x → Real.log (oddPrimeProduct x : ℝ) ≤ 2 * x := by
  have hlogfour : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hub (x : ℝ) (hx : 0 ≤ x) : Chebyshev.theta x ≤ 2 * x :=
    (Chebyshev.theta_le_log4_mul_x hx).trans (mul_le_mul_of_nonneg_right hlogfour hx)
  constructor
  · have hp : ∀ᶠ x : ℝ in atTop, (1 / 2 : ℝ) < Chebyshev.theta x / x :=
      Chebyshev.tendsto_theta_div_atTop.eventually_const_lt (by norm_num)
    obtain ⟨t, ht⟩ := eventually_atTop.mp hp
    refine ⟨max 3 t, le_max_left .., ?_⟩
    intro x hx
    have hx3 : (3 : ℝ) ≤ x := (le_max_left ..).trans hx
    have hx0 : 0 < x := by linarith
    have hl : (1 / 2 : ℝ) * x ≤ Chebyshev.theta x :=
      ((lt_div_iff₀ hx0).mp (ht x ((le_max_right ..).trans hx))).le
    exact ⟨(div_le_iff₀ (Real.log_pos (by linarith))).2
      (hl.trans (Chebyshev.theta_le_pi_mul_log' x)), hl, hub x hx0.le⟩
  · intro x hx
    have hprime (p : ℕ) (hp : p ∈ Nat.primesLE ⌊x⌋₊) := Nat.prime_of_mem_primesLE hp
    have hpos : 0 < oddPrimeProduct x :=
      Finset.prod_pos (fun p hp ↦ (hprime p (Finset.mem_of_mem_erase hp)).pos)
    have hle : oddPrimeProduct x ≤ primorial ⌊x⌋₊ := by
      rw [oddPrimeProduct, primorial_eq_prod_primesLE]
      exact Finset.prod_le_prod_of_subset_of_one_le (Finset.erase_subset ..)
        (fun p hp _ ↦ (hprime p hp).one_lt.le)
    have h : Real.log (oddPrimeProduct x : ℝ) ≤ Real.log (primorial ⌊x⌋₊ : ℝ) :=
      Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
    rw [← Chebyshev.theta_eq_log_primorial] at h
    exact h.trans (hub x hx.le)

private theorem divisors_card_of_prime_product (s : Finset ℕ)
    (h : ∀ p ∈ s, Nat.Prime p) :
    (∏ p ∈ s, p).divisors.card = 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hprime := h p (Finset.mem_insert_self ..)
    have hrest := fun q (hq : q ∈ s) ↦ h q (Finset.mem_insert_of_mem hq)
    have hco : p.Coprime (∏ q ∈ s, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hprime (hrest q hq)).mpr (by rintro rfl; exact hp hq)
    have htwo : p.divisors.card = 2 := by rw [hprime.divisors]; simp [Ne.symm hprime.ne_one]
    rw [Finset.prod_insert hp, Finset.card_insert_of_notMem hp, hco.card_divisors_mul,
      htwo, ih hrest, pow_succ, Nat.mul_comm]

/-- Every choice of a subset of the allowed primes gives one divisor, including the empty choice. -/
theorem oddPrimeProduct_card_divisors (x : ℝ) (hx : 2 ≤ x) :
    (oddPrimeProduct x).divisors.card = 2 ^ (Nat.primeCounting ⌊x⌋₊ - 1) := by
  have h2 : 2 ∈ Nat.primesLE ⌊x⌋₊ := Nat.mem_primesLE.mpr ⟨Nat.le_floor (by simpa using hx), Nat.prime_two⟩
  rw [oddPrimeProduct, divisors_card_of_prime_product _ (fun p hp ↦
    Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hp)),
    Finset.card_erase_of_mem h2, Nat.primesLE_card_eq_primeCounting]

/-- Exponentially many squarefree odd smooth integers, with an explicitly
absolute coefficient in the logarithm of their number. -/
theorem log_card_oddPrimeProduct_divisors :
    ∃ t : ℝ, 3 ≤ t ∧ ∀ x : ℝ, t ≤ x →
      (Real.log 2 / 4) * x / Real.log x ≤ Real.log ((oddPrimeProduct x).divisors.card : ℝ) := by
  obtain ⟨t, ht, h⟩ := chebyshevInputs.1
  refine ⟨t, ht, ?_⟩
  intro x hx
  have hx3 := ht.trans hx
  have hp := (h x hx).1
  have hπ : 2 ≤ Nat.primeCounting ⌊x⌋₊ := by
    exact (show 2 ≤ Nat.primeCounting 3 by decide).trans
      (Nat.monotone_primeCounting (Nat.le_floor (by simpa using hx3)))
  have half : (Nat.primeCounting ⌊x⌋₊ : ℝ) / 2 ≤ (Nat.primeCounting ⌊x⌋₊ - 1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ Nat.primeCounting ⌊x⌋₊), Nat.cast_one]
    have : (2 : ℝ) ≤ Nat.primeCounting ⌊x⌋₊ := by exact_mod_cast hπ
    linarith
  rw [oddPrimeProduct_card_divisors x (by linarith), Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow]
  have hmain : ((1 / 2 : ℝ) * x / Real.log x) / 2 ≤ (Nat.primeCounting ⌊x⌋₊ - 1 : ℕ) :=
    (div_le_div_of_nonneg_right hp (by norm_num)).trans half
  convert mul_le_mul_of_nonneg_right hmain (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) using 1
  ring

end OddEgyptian
