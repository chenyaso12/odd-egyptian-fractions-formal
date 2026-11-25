module

public import MathProblems.OddEgyptian.Maximum
public import MathProblems.OddEgyptian.PrimeMarker
public import MathProblems.OddEgyptian.Growth

@[expose] public section

namespace OddEgyptian

/-- The maximum denominator is divisible by each of the first r odd primes. -/
def MaximumTarget : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
    ∃ s : Finset ℕ, Represents 1 s ∧ (s.card : ℝ) ≤ A*Real.log (r:ℝ) ∧
      FirstOddProduct r ∣ s.sup id

theorem maximum_of_short (hH : HTarget) : MaximumTarget := by
  obtain ⟨C,hC,short⟩ := hH
  obtain ⟨R,hR,budget⟩ := seedCount_budget (3*C) 8
  refine ⟨12*C+3, by positivity, max R 5, ?_⟩
  intro r hr
  have hrR : R ≤ r := (le_max_left ..).trans hr
  have hr3 := hR.trans hrR
  have hr5 : 5 ≤ r := (le_max_right ..).trans hr
  obtain ⟨hQ,ho,hsize,hdiv⟩ := firstOddProduct_spec r hr3
  let Q := FirstOddProduct r
  have hQr : (0:ℚ) < Q := by exact_mod_cast (show 0<Q by omega)
  obtain ⟨E, hE, hm⟩ := short (Q-1) Q hQ ho (by omega) (by omega)
  have hv : ((Q-1 : ℕ) : ℚ) / Q = 1-1/Q := by
    rw [Nat.cast_sub (by omega : 1≤Q)]
    push_cast
    field_simp
  rw [hv] at hE
  have hlog : 1 ≤ Real.log (r:ℝ) :=
    (Real.le_log_iff_exp_le (by positivity)).mpr (Real.exp_one_lt_three.le.trans
      (by exact_mod_cast hr3))
  have hml : (E.card:ℝ) ≤ (3*C)*Real.log (r:ℝ) := calc
    _ ≤ C*(1+Real.log (Real.log (Q:ℝ))) := hm
    _ ≤ C*(1+2*Real.log (r:ℝ)) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hlog)]
  have hb := budget r hrR E.card hml
  have hp : 2^4 ≤ (2:ℕ)^(r-1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hbudget : 8*E.card+7 < Q.divisors.card := by
    rw [show Q.divisors.card = 2^r from hdiv]
    omega
  obtain ⟨s,hs,hcard,hdvd⟩ := maximum_multiple_of_complement Q hQ ho E hE hbudget
  refine ⟨s,hs,?_,hdvd⟩
  have hreal : (s.card:ℝ) ≤ 4*E.card+3 := by exact_mod_cast hcard
  nlinarith

end OddEgyptian
