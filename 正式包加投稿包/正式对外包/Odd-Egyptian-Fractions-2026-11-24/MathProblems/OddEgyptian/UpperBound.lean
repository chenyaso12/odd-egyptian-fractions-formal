module

public import MathProblems.OddEgyptian.Finiteness
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace OddEgyptian

/-- An unconditional upper bound, allowing a non-optimized absolute constant. -/
theorem oddCount_exp_upper (k : ℕ) (hk : 1 ≤ k) :
    (oddCount k : ℝ) ≤ Real.exp (Real.exp (4 * (k : ℝ))) := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hkE : (k:ℝ) ≤ Real.exp k := by linarith [Real.add_one_le_exp (k:ℝ)]
  have htwo : (2:ℝ)^k ≤ Real.exp k := calc
    _ ≤ (Real.exp 1)^k := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; simp
  have hheight : (height k : ℝ) ≤ Real.exp ((k:ℝ) * 2^k) := calc
    _ = ((k:ℝ)+1)^(2^k) := by simp [height]
    _ ≤ (Real.exp k)^(2^k) := by gcongr; exact Real.add_one_le_exp _
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; congr 1; ring
  have hsub : (height k : ℝ) + 1 ≤ Real.exp (1 + (k:ℝ) * 2^k) := by
    rw [Real.exp_add]
    have hone : 1 ≤ Real.exp ((k:ℝ) * 2^k) := Real.one_le_exp (by positivity)
    calc
      _ ≤ 2 * Real.exp ((k:ℝ) * 2^k) := by linarith
      _ ≤ _ := by gcongr
  have hexp : (k:ℝ) * (1 + (k:ℝ) * 2^k) ≤ Real.exp (4 * (k:ℝ)) := by
    have ht : 2 ≤ Real.exp (k:ℝ) := he.trans (Real.exp_le_exp.mpr hk')
    have hge : 1 ≤ Real.exp (2 * (k:ℝ)) := Real.one_le_exp (by positivity)
    have hke : (k:ℝ) * 2^k ≤ Real.exp (2*(k:ℝ)) := calc
      _ ≤ Real.exp k * Real.exp k := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
    calc
      _ ≤ Real.exp k * (2 * Real.exp (2*(k:ℝ))) := by
        apply mul_le_mul hkE (by linarith) (by positivity) (by positivity)
      _ ≤ Real.exp k * (Real.exp k * Real.exp (2*(k:ℝ))) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc
    (oddCount k : ℝ) ≤ ((height k : ℝ)+1)^k := by exact_mod_cast oddCount_le_pow k
    _ ≤ (Real.exp (1+(k:ℝ)*2^k))^k := by gcongr
    _ = Real.exp ((k:ℝ)*(1+(k:ℝ)*2^k)) := (Real.exp_nat_mul ..).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexp

end OddEgyptian
