module

public import MathProblems.OddEgyptian.A1
public import MathProblems.OddEgyptian.DigitParameters
public import MathProblems.OddEgyptian.DigitSieve
public import MathProblems.OddEgyptian.DigitAssembly
import Mathlib.Tactic

public section

namespace OddEgyptian

open Real

/-- A single base, residue fiber and cutoff serve every digit. The threshold for b is
chosen after the absolute template bound R and before selecting b or any of its digits. -/
theorem layeredDigits_of_threePrimeInput (input : ThreePrimeInput) : LayeredDigitTarget := by
  classical
  obtain ⟨J, smallDigits⟩ := a1_uniform input
  obtain ⟨v, hv, m₀, hm₀, threePrimeCount⟩ := input
  refine ⟨max (J+1) 10, 262145, by norm_num, ?_⟩
  intro R
  obtain ⟨b₀, chooseData⟩ := exists_digitParameterData R m₀ v hv
  refine ⟨b₀, ?_⟩
  intro b hlarge hb3 _
  obtain ⟨data⟩ := chooseData b hlarge hb3
  let P := oddPrimeProduct data.y
  let B := data.B
  let F := P.divisors.filter fun d => d % B = data.r
  let T := ⌊exp (digitBreak (1/8192) (log B))⌋₊
  have prim : B.Prime := data.primeB
  have h3 : 3 < B := by exact_mod_cast data.hy.trans_lt data.base_gt_y
  have hoB : Odd B := prim.odd_of_ne_two (by omega)
  have hP := oddPrimeProduct_odd data.y
  have hBP : ¬ B ∣ P := prime_not_dvd_oddPrimeProduct prim data.base_gt_y
  have hsq : (P^2)^2 = P^4 := by ring
  refine ⟨B, P^2, data.L, prim, hoB, hP.pow, data.not_dvd_b,
    fun hd => hBP (prim.dvd_of_dvd_pow hd), ?_, data.capacity, data.R_lt_B,
    ?_, data.length_bound, ?_⟩
  · rw [hsq]
    exact data.scale_lt
  · rw [hsq]
    exact data.scale_mul_lt
  have sub : F ⊆ P.divisors := Finset.filter_subset _ _
  apply assembleFractionDigits (B := B) (T := T) hP prim.one_lt sub data.r_lt_B
    (fun d hd => (Finset.mem_filter.mp hd).2) data.nonroot
  · intro m hm _
    have hmexp : (m : ℝ) ≤ exp (digitBreak (1/8192) (log B)) :=
      (Nat.cast_le.mpr hm).trans (Nat.floor_le (exp_pos _).le)
    obtain ⟨hdiv, hsmall⟩ := a1_small_support (m := m) (B := B) (y := data.y)
      (by norm_num : (0:ℝ)<1/8192) (by norm_num) data.logB_gt_one data.logB_le_y
      data.small_lo data.small_hi hmexp
    exact ⟨a1Prime m, hdiv, hsmall, smallDigits m⟩
  · intro m hm hmB odd
    have cutoff : m₀ ≤ m := data.cutoff.trans (Nat.le_of_lt hm)
    exact goodTriple_of_count m P F v data.y (hm₀.trans cutoff) (oddPrimeProduct_pos data.y)
      (fun _ hd => Nat.le_of_dvd (oddPrimeProduct_pos data.y) (Nat.mem_divisors.mp (sub hd)).1)
      (chebyshevInputs.2 _ (by linarith [data.hy])) (data.fiber_size m hmB)
      (threePrimeCount m cutoff odd) (data.large_error m hm hmB)

end OddEgyptian
