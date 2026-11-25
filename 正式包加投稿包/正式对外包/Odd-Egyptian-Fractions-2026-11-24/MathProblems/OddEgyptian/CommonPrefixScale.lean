module

public import MathProblems.OddEgyptian.Growth

@[expose] public section

namespace OddEgyptian

/-- Choose enough prime factors for both the divisibility threshold and the number
of distinct maxima, leaving two final slots in the prescribed length. -/
theorem commonPrefix_scale (A : ℝ) (hA : 0 < A) (R : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ r : ℕ,
      R ≤ r ∧ 3 ≤ r ∧ A*Real.log (r:ℝ)+2 ≤ k ∧
      ⌊Real.exp (c*(k:ℝ))⌋₊ ≤ r ∧
      Real.exp (Real.exp (c*(k:ℝ))) ≤ ((2^r-1 : ℕ):ℝ) := by
  let R' := max R 3
  let bound := (2*A)*((R':ℝ)+8)
  let c := 1/(4*A)
  refine ⟨c, by dsimp [c]; positivity, max 4 ⌈bound⌉₊, ?_⟩
  intro k hk
  have h4 : 4 ≤ k := (le_max_left ..).trans hk
  have hk' : bound ≤ (k:ℝ) := (Nat.le_ceil bound).trans
    (by exact_mod_cast (le_max_right 4 ⌈bound⌉₊).trans hk)
  let t := (k:ℝ)/(2*A)
  have ht : (R':ℝ)+8 ≤ t := by
    apply (le_div_iff₀ (by positivity : 0 < 2*A)).2
    simpa [bound, mul_comm] using hk'
  have htk : t*(2*A) = (k:ℝ) := div_mul_cancel₀ _ (by positivity)
  let r := ⌊Real.exp t⌋₊
  have hr : R' ≤ r := Nat.le_floor (by linarith [Real.add_one_le_exp t])
  have hr3 : 3 ≤ r := (le_max_right ..).trans hr
  have hrpos : 0 < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hlog : Real.log (r:ℝ) ≤ t := by
    simpa using Real.log_le_log hrpos (Nat.floor_le (Real.exp_pos t).le)
  have hc : c*(k:ℝ) = t/2 := by
    dsimp [c,t]
    field_simp
    ring
  refine ⟨r, (le_max_left ..).trans hr, hr3, ?_, ?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left hlog hA.le
    have hfour : (4:ℝ) ≤ k := by exact_mod_cast h4
    nlinarith only [hm,htk,hfour]
  · rw [hc]
    exact Nat.floor_mono (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α:=ℝ) R']))
  · let x := Real.exp (t/2)
    have hx : 4 ≤ x := by
      dsimp [x]
      linarith [Real.add_one_le_exp (t/2), Nat.cast_nonneg (α:=ℝ) R']
    have hsq : x*x = Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hround : Real.exp t < (r:ℝ)+1 := Nat.lt_floor_add_one _
    have hxr : 2*x ≤ (r:ℝ)-1 := by
      nlinarith only [hsq,hround,hx,sq_nonneg (x-2)]
    have hsub : ((r-1:ℕ):ℝ) = (r:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hlogtwo : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hxpow : x ≤ ((r-1:ℕ):ℝ)*Real.log 2 := by
      have hm := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg (α:=ℝ) (r-1))
      rw [hsub] at hm ⊢
      linarith
    have hpow : 2^(r-1) ≤ 2^r-1 := by
      have he : r-1+1=r := by omega
      have hrw : (2:ℕ)^r = 2^(r-1)*2 := by nth_rw 1 [←he]; rw [pow_succ]
      have hp : 0 < (2:ℕ)^(r-1) := by positivity
      omega
    calc
      _ = Real.exp x := by rw [hc]
      _ ≤ Real.exp (((r-1:ℕ):ℝ)*Real.log 2) := Real.exp_le_exp.mpr hxpow
      _ = (2:ℝ)^(r-1) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
      _ ≤ _ := by exact_mod_cast hpow

end OddEgyptian
