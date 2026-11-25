module

public import MathProblems.OddEgyptian.Counting
public import MathProblems.OddEgyptian.Growth
public import MathProblems.OddEgyptian.Parity
public import MathProblems.OddEgyptian.UpperBound
public import MathProblems.OddEgyptian.SharpUpper
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

namespace OddEgyptian

/-- The representation of (Q-1)/Q stays fixed for all splitting choices for the same Q. -/
private theorem short_seed_family (hH : HTarget)
    (split_count : ∀ {n : ℕ}, 3 ≤ n → Odd n → ∀ E : Finset ℕ,
      Represents (1 - 1 / (n : ℚ)) E →
        n.divisors.card - 1 - 2 * E.card ≤ oddCount (E.card + 3)) :
    ∃ A : ℝ, 0 < A ∧ ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
      ∃ L : ℕ, Odd L ∧ (L : ℝ) ≤ A * Real.log (r : ℝ) ∧
        2^(r-1) ≤ oddCount L := by
  obtain ⟨C, hC, hrep⟩ := hH
  obtain ⟨R, hR, hbudget⟩ := seedCount_budget (3*C) 2
  refine ⟨3*C+3, by positivity, R, ?_⟩
  intro r hr
  have hr3 := hR.trans hr
  have hr3' : (3:ℝ) ≤ r := by exact_mod_cast hr3
  have hrlog : 1 ≤ Real.log (r:ℝ) :=
    (Real.le_log_iff_exp_le (by positivity)).mpr (Real.exp_one_lt_three.le.trans hr3')
  obtain ⟨Q, hQ, hoQ, hsize, hdiv⟩ := richOddMarker r hr3
  obtain ⟨E, hE, hm⟩ := hrep (Q-1) Q hQ hoQ (by omega) (by omega)
  have hval : ((Q-1 : ℕ) : ℚ) / Q = 1 - 1 / Q := by
    rw [Nat.cast_sub (by omega : 1 ≤ Q)]
    push_cast
    field_simp
  rw [hval] at hE
  have hml : (E.card:ℝ) ≤ (3*C)*Real.log (r:ℝ) := calc
    _ ≤ C * (1+Real.log (Real.log (Q:ℝ))) := hm
    _ ≤ C * (1+2*Real.log (r:ℝ)) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hrlog)]
  have hl := split_count hQ hoQ E hE
  rw [hdiv] at hl
  have hb := hbudget r hr E.card hml
  have hmcount : 2^(r-1) ≤ oddCount (E.card+3) := by omega
  have hpos : 0 < Nat.card (Solutions (E.card+3)) :=
    lt_of_lt_of_le (by positivity) hmcount
  obtain ⟨x⟩ := Finite.card_pos_iff.mp hpos
  refine ⟨E.card+3, x.2.2 ▸ represents_one_odd_card x.2.1, ?_, hmcount⟩
  push_cast
  linarith

/-- H is the sole research assumption of this implication; the upper estimate is unconditional. -/
theorem counting_of_short (hH : HTarget) : CTarget := by
  obtain ⟨A, hA, R, hseed⟩ := short_seed_family hH count_splits
  obtain ⟨k₀, hk₀⟩ := doubleExpLower_of_seedFamily oddCount hA R hseed
    (fun _ _ hi hj hij => oddCount_mono_odd hij hi hj)
  refine ⟨1/(4*A), 2, by positivity, by norm_num, max k₀ 1, ?_⟩
  intro k hk hodd
  exact ⟨hk₀ k ((le_max_left ..).trans hk) hodd,
    oddCount_exp_upper_two k ((le_max_right ..).trans hk)⟩

end OddEgyptian
