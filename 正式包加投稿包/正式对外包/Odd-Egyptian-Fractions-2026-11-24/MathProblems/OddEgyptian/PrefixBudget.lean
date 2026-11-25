module

public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace OddEgyptian

private theorem prefix_power_budget (k : ℕ) (hk : 128 ≤ k) : (45045*(12*(k+1)))^2 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    have hsq : 2*(k+1)^2 ≥ ((k+1)+1)^2 := by nlinarith [Nat.mul_le_mul hk hk]
    calc
      _ = (45045*12)^2*((k+1)+1)^2 := by ring
      _ ≤ (45045*12)^2*(2*(k+1)^2) := Nat.mul_le_mul_left _ hsq
      _ = (45045*(12*(k+1)))^2*2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ ih

/-- The horizon is one more than the integer binary logarithm of six times the bit length. -/
theorem prefix_horizon (b : ℕ) (hb : 2^128 ≤ b) :
    ∃ T : ℕ, (45045*2^T)^2 ≤ b ∧
      (2/3 : ℝ)^(2^T)*(b : ℝ)^3 ≤ 1 ∧
      6+(T : ℝ) ≤ 80*(1+Real.log (Real.log b)) := by
  let k := Nat.log 2 b
  let h := k+1
  let T := Nat.log 2 (6*h)+1
  have hb3 : 3 ≤ b := (by decide : 3 ≤ 2^128).trans hb
  have hk : 128 ≤ k := Nat.le_log_of_pow_le (by decide) hb
  have hkb : 2^k ≤ b := Nat.pow_log_le_self _ (by omega)
  have hbh : b ≤ 2^h := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) b).le
  have lo : 6*h ≤ 2^T := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (6*h)).le
  have hi : 2^T ≤ 12*h := by
    have hn := Nat.pow_log_le_self 2 (show 6*h ≠ 0 by dsimp [h]; omega)
    dsimp [T]
    rw [pow_succ]
    omega
  refine ⟨T, (Nat.pow_le_pow_left (Nat.mul_le_mul_left 45045 hi) 2).trans
    ((prefix_power_budget k hk).trans hkb), ?_, ?_⟩
  · have hp : (2/3 : ℝ)^(2^T) ≤ (2/3 : ℝ)^(6*h) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) lo
    have hb' : (b : ℝ)^3 ≤ ((2 : ℝ)^h)^3 :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hbh) _
    calc
      (2/3 : ℝ)^(2^T)*(b : ℝ)^3 ≤ (2/3 : ℝ)^(6*h)*((2:ℝ)^h)^3 :=
        mul_le_mul hp hb' (by positivity) (by positivity)
      _ = (((2/3:ℝ)^6) * 2^3)^h := by rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
      _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  · have hbR : 1 ≤ Real.log (b : ℝ) := by
      rw [← Real.exp_le_exp, Real.exp_log (by positivity : 0 < (b : ℝ))]
      exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hb3)
    have hl₂ : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hkr : (k : ℝ)*Real.log 2 ≤ Real.log b := by
      have := Real.log_le_log (by positivity : 0 < (2:ℝ)^k)
        (by exact_mod_cast hkb : (2:ℝ)^k ≤ b)
      simpa only [Real.log_pow] using this
    have hh : (h : ℝ) ≤ 3*Real.log b := by
      dsimp [h]
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sub_nonneg.mpr hl₂)]
    have htar : (2:ℝ)^T ≤ 36*Real.log b := calc
      _ ≤ 12*(h : ℝ) := by exact_mod_cast hi
      _ ≤ _ := by linarith
    have htlog := Real.log_le_log (by positivity : 0 < (2:ℝ)^T) htar
    rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at htlog
    have hlmax := Real.log_le_self (by norm_num : (0:ℝ) ≤ 36)
    have hll := Real.log_nonneg hbR
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) T) (sub_nonneg.mpr hl₂)]

end OddEgyptian

