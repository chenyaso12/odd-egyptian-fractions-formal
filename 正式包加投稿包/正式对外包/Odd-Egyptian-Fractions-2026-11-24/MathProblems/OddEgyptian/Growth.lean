module

public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

public section

namespace OddEgyptian

private noncomputable def dyadicPrime (i : ℕ) : ℕ :=
  (Nat.bertrand (2 ^ (i + 1)) (by positivity)).choose

private theorem dyadicPrime_spec (i : ℕ) : (dyadicPrime i).Prime ∧
    2 ^ (i + 1) < dyadicPrime i ∧ dyadicPrime i ≤ 2 ^ (i + 2) := by
  simpa [dyadicPrime, pow_succ, Nat.mul_comm] using
    (Nat.bertrand (2 ^ (i + 1)) (by positivity)).choose_spec

private theorem dyadicPrime_strictMono : StrictMono dyadicPrime := by
  apply strictMono_nat_of_lt_succ
  intro i
  exact (dyadicPrime_spec i).2.2.trans_lt (dyadicPrime_spec (i + 1)).2.1

private noncomputable def markerProduct (r : ℕ) : ℕ :=
  ∏ i ∈ Finset.range r, dyadicPrime i

private theorem markerProduct_spec (r : ℕ) :
    Odd (markerProduct r) ∧ (markerProduct r).divisors.card = 2 ^ r := by
  induction r with
  | zero => simp [markerProduct]
  | succ r ih =>
    have hp := (dyadicPrime_spec r).1
    have hpgt : 2 < dyadicPrime r :=
      (dyadicPrime_spec 0).2.1.trans_le (dyadicPrime_strictMono.monotone (Nat.zero_le r))
    have hc : (markerProduct r).Coprime (dyadicPrime r) := by
      apply Nat.coprime_prod_left_iff.mpr
      intro j hj
      exact (Nat.coprime_primes (dyadicPrime_spec j).1 hp).mpr
        (dyadicPrime_strictMono (Finset.mem_range.mp hj)).ne
    have htwo : (dyadicPrime r).divisors.card = 2 := by
      rw [hp.divisors]
      simp [Ne.symm hp.ne_one]
    rw [show markerProduct (r + 1) = markerProduct r * dyadicPrime r from
      Finset.prod_range_succ ..]
    exact ⟨ih.1.mul (hp.odd_of_ne_two hpgt.ne'), by
      rw [hc.card_divisors_mul, ih.2, htwo, pow_succ]⟩

/-- One prime per dyadic interval suffices for the counting argument. The
prime-counting asymptotic is unnecessary for this witness. -/
theorem richOddMarker (r : ℕ) (hr : 3 ≤ r) :
    ∃ Q : ℕ, 3 ≤ Q ∧ Odd Q ∧
      Real.log (Real.log (Q : ℝ)) ≤ 2 * Real.log (r : ℝ) ∧ Q.divisors.card = 2 ^ r := by
  let Q := markerProduct r
  obtain ⟨hodd, hcard⟩ := markerProduct_spec r
  have hpowers : 2 ^ 3 ≤ (2 : ℕ) ^ r := Nat.pow_le_pow_right (by decide) hr
  have hQ : 3 ≤ Q := by
    have h := Nat.card_divisors_le_self Q
    change Q.divisors.card = 2 ^ r at hcard
    omega
  have hb : Q ≤ (2 ^ (r + 1)) ^ r := by
    calc
      Q ≤ ∏ _i ∈ Finset.range r, 2 ^ (r + 1) := by
        apply Finset.prod_le_prod
        intro i hi
        exact (dyadicPrime_spec i).2.2.trans (Nat.pow_le_pow_right (by decide)
          (by have := Finset.mem_range.mp hi; omega))
      _ = _ := by simp
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQlog : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hbound := Real.log_le_log hQpos (show (Q : ℝ) ≤ ((2 : ℝ) ^ (r + 1)) ^ r by
    exact_mod_cast hb)
  rw [Real.log_pow, Real.log_pow] at hbound
  push_cast at hbound
  have hrreal : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hlogtwo : Real.log 2 ≤ (3 / 4 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hfac : ((r : ℝ) + 1) * Real.log 2 ≤ r := by
    have h := mul_le_mul_of_nonneg_left hlogtwo (by positivity : 0 ≤ (r : ℝ) + 1)
    linarith
  have hlogQ : Real.log (Q : ℝ) ≤ (r : ℝ) ^ 2 := by
    simpa [pow_two] using hbound.trans (mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg _))
  refine ⟨Q, hQ, hodd, ?_, hcard⟩
  simpa [Real.log_pow] using Real.log_le_log hQlog hlogQ

private theorem square_le_two_pow_pred (r : ℕ) (hr : 8 ≤ r) :
    r ^ 2 ≤ 2 ^ (r - 1) := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    have he : t = (t - 1) + 1 := by omega
    calc
      (t + 1) ^ 2 ≤ 2 * t ^ 2 := by
        nlinarith [Nat.mul_le_mul ht (Nat.le_refl t)]
      _ ≤ 2 * 2 ^ (t - 1) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (t + 1 - 1) := by
        rw [Nat.mul_comm, ← pow_succ, ← he]
        simp

/-- For any fixed linear cost per old denominator, a logarithmic number of them leaves at
least half of the choices once the number of prime factors is large enough. -/
theorem seedCount_budget (A : ℝ) (D : ℕ) : ∃ R : ℕ, 3 ≤ R ∧
    ∀ r : ℕ, R ≤ r → ∀ m : ℕ, (m : ℝ) ≤ A * Real.log (r : ℝ) →
      2 ^ (r - 1) + (1 + D * m) ≤ 2 ^ r := by
  let K := ⌈A⌉₊
  refine ⟨max 8 (D * K + 2), by omega, ?_⟩
  intro r hr m hm
  have hr8 : 8 ≤ r := (le_max_left ..).trans hr
  have hrK : D * K + 2 ≤ r := (le_max_right ..).trans hr
  have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
  have hmr : m ≤ K * r := by
    have h := hm.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil A) (Real.log_nonneg hr1))
    have h' := h.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_self (Nat.cast_nonneg r)) (Nat.cast_nonneg K))
    exact_mod_cast h'
  have hb : 1 + D * m ≤ r ^ 2 := by
    nlinarith [Nat.mul_le_mul hrK (Nat.le_refl r), Nat.mul_le_mul_left D hmr]
  have he : r = (r - 1) + 1 := by omega
  calc
    2 ^ (r - 1) + (1 + D * m) ≤ 2 ^ (r - 1) + 2 ^ (r - 1) :=
      Nat.add_le_add_left (hb.trans (square_le_two_pow_pred r hr8)) _
    _ = 2 ^ r := by nth_rw 3 [he]; rw [pow_succ]; omega

/-- A short family with exponentially many members, together with same-parity
padding, gives a doubly exponential count at every sufficiently large odd length. -/
theorem doubleExpLower_of_seedFamily (count : ℕ → ℕ) {A : ℝ} (hA : 0 < A)
    (r₀ : ℕ)
    (hseed : ∀ r : ℕ, r₀ ≤ r → ∃ L : ℕ, Odd L ∧
      (L : ℝ) ≤ A * Real.log (r : ℝ) ∧ 2 ^ (r - 1) ≤ count L)
    (hpad : ∀ i j : ℕ, Odd i → Odd j → i ≤ j → count i ≤ count j) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Odd k →
      Real.exp (Real.exp ((1 / (4 * A)) * (k : ℝ))) ≤ (count k : ℝ) := by
  let bound := (2 * A) * ((r₀ : ℝ) + 8)
  refine ⟨⌈bound⌉₊, ?_⟩
  intro k hk hkOdd
  have hk' : bound ≤ (k : ℝ) := (Nat.le_ceil bound).trans (by exact_mod_cast hk)
  let t := (k : ℝ) / (2 * A)
  have ht : (r₀ : ℝ) + 8 ≤ t := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * A)).2
    simpa [bound, mul_comm] using hk'
  have htwo : 0 < 2 * A := by positivity
  have htk : t * (2 * A) = (k : ℝ) := div_mul_cancel₀ _ htwo.ne'
  let r := ⌊Real.exp t⌋₊
  have hr₀ : r₀ ≤ r := Nat.le_floor (by linarith [Real.add_one_le_exp t])
  have hr1 : 1 ≤ r := Nat.le_floor (by
    push_cast
    linarith [Real.add_one_le_exp t, Nat.cast_nonneg (α := ℝ) r₀])
  have hrPos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hrupper : (r : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
  obtain ⟨L, hLodd, hlength, hcount⟩ := hseed r hr₀
  have hlog : Real.log (r : ℝ) ≤ t := by
    simpa using Real.log_le_log hrPos hrupper
  have hLk : L ≤ k := by
    have h1 := hlength.trans (mul_le_mul_of_nonneg_left hlog hA.le)
    have hkNonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    exact_mod_cast (show (L : ℝ) ≤ (k : ℝ) by nlinarith only [h1, htk, hkNonneg])

  -- The rounding error in r costs at most two after subtracting one.
  let x := Real.exp (t / 2)
  have hx : 4 ≤ x := by
    dsimp [x]
    linarith [Real.add_one_le_exp (t / 2), Nat.cast_nonneg (α := ℝ) r₀]
  have hsq : x * x = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hround : Real.exp t < (r : ℝ) + 1 := Nat.lt_floor_add_one _
  have hxr : 2 * x ≤ (r : ℝ) - 1 := by
    nlinarith only [hsq, hround, hx, sq_nonneg (x - 2)]
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hsub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr1, Nat.cast_one]
  have hxpow : x ≤ ((r - 1 : ℕ) : ℝ) * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg (α := ℝ) (r - 1))
    rw [hsub] at hmul ⊢
    linarith
  have hexponent : 1 / (4 * A) * (k : ℝ) = t / 2 := by
    dsimp [t]
    field_simp
    ring
  calc
    Real.exp (Real.exp ((1 / (4 * A)) * (k : ℝ))) = Real.exp x := by rw [hexponent]
    _ ≤ Real.exp (((r - 1 : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hxpow
    _ = (2 : ℝ) ^ (r - 1) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (count k : ℝ) := by exact_mod_cast hcount.trans (hpad L k hLodd hkOdd hLk)

end OddEgyptian
