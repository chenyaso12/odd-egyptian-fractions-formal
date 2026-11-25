module

public import MathProblems.OddEgyptian.MaximumFibers
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

/-- Taking half the indices and excluding two collisions per inserted denominator
still leaves the required integer ceiling of a smaller double exponential. -/
private theorem fiber_budget {c d : ℝ} {k m T : ℕ} (hd : 0 < d) (hk : 1 ≤ k) (hm : m ≤ k)
    (hlarge : 32 ≤ d^2 * (k : ℝ)) (hscale : 2 * (d * (k : ℝ)) ≤ c * (m : ℝ))
    (hT : Real.exp (Real.exp (c * (m : ℝ))) ≤ (T : ℝ)) :
    ⌈Real.exp (Real.exp (d * (k : ℝ)))⌉₊ ≤ T/2 - 2*m := by
  let x := Real.exp (d * (k : ℝ))
  let z := Real.exp x
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hmR : (m : ℝ) ≤ k := by exact_mod_cast hm
  have hhalf : 0 ≤ d * (k : ℝ) / 2 := by positivity
  have hsq : (d * (k : ℝ) / 2)^2 ≤ x := calc
    _ ≤ (Real.exp (d * (k : ℝ) / 2))^2 :=
      pow_le_pow_left₀ hhalf (by linarith [Real.add_one_le_exp (d * (k : ℝ) / 2)]) 2
    _ = x := by dsimp [x]; rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hx : 8 * (k : ℝ) ≤ x := by
    nlinarith only [hsq, mul_le_mul_of_nonneg_right hlarge (Nat.cast_nonneg (α := ℝ) k)]
  have hex : x + x ≤ Real.exp (c * (m : ℝ)) := calc
    _ ≤ x * x := by
      have hx2 : 2 ≤ x := by linarith
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx2) (Real.exp_pos (d*k)).le]
    _ = Real.exp (2 * (d * (k : ℝ))) := by rw [two_mul, Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr hscale
  have zz : z*z ≤ (T : ℝ) := calc
    _ = Real.exp (x+x) := (Real.exp_add ..).symm
    _ ≤ _ := (Real.exp_le_exp.mpr hex).trans hT
  have hz : x+1 ≤ z := Real.add_one_le_exp _
  have zpos : 0 ≤ z := (Real.exp_pos x).le
  have hz3 : 3 ≤ z := by linarith
  have hceil := Nat.ceil_lt_add_one zpos
  have hnat : 2 * ⌈z⌉₊ + 4 * m ≤ T := by
    exact_mod_cast (show 2 * (⌈z⌉₊ : ℝ) + 4*(m:ℝ) ≤ T by
      nlinarith only [hceil, zz, hz, hx, hmR, hkR, mul_nonneg (by linarith : 0 ≤ z-3) zpos])
  change ⌈z⌉₊ ≤ T/2 - 2*m
  omega

/-- Convert the finite two-index construction at lengths 2m-1 and 2m+1 into
the all-odd-length statement, keeping the prescribed prime factors. -/
theorem maximumMultiplicity_of_commonPrefix
    (h : CommonPrefixTarget) : MaximumMultiplicityTarget := by
  obtain ⟨c,hc,m₀,seed⟩ := h
  let d := c/6
  have hd : 0 < d := by dsimp [d]; positivity
  let K := max (4*(m₀+3)) ⌈32/d^2⌉₊
  refine ⟨d,hd,K,?_⟩
  intro k hk hkOdd
  let m := 2*((k-1)/4)+1
  have hk₁ : 4*(m₀+3) ≤ k := (le_max_left ..).trans hk
  have hk₂ : ⌈32/d^2⌉₊ ≤ k := (le_max_right ..).trans hk
  have hm : 3 ≤ m := by dsimp [m]; omega
  have hm₀ : m₀ ≤ m := by dsimp [m]; omega
  have hmOdd : Odd m := ⟨(k-1)/4, rfl⟩
  have parity : k = 2*m-1 ∨ k = 2*m+1 := by
    obtain ⟨z,hz⟩ := hkOdd
    dsimp [m]
    omega
  have hmk : m ≤ k := by omega
  have scale : 2 * (d * (k : ℝ)) ≤ c * (m : ℝ) := by
    have hsmall : (k : ℝ) ≤ 3*(m:ℝ) := by exact_mod_cast (show k ≤ 3*m by omega)
    dsimp [d]
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hc.le]
  obtain ⟨P,Y,family,hT⟩ := seed m hm₀ hmOdd
  have size : 32 ≤ d^2 * (k : ℝ) := by
    have := (Nat.ceil_le.mp hk₂ : 32/d^2 ≤ (k:ℝ))
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < d^2)).mp this
  have y2 : 2 ≤ Y.card := by
    have hui : 1 ≤ Real.exp (c * (m : ℝ)) :=
      (Real.one_le_exp_iff).mpr (by positivity)
    have three := (Real.add_one_le_exp (Real.exp (c * (m : ℝ)))).trans hT
    exact_mod_cast (show (2:ℝ) ≤ Y.card by linarith)
  obtain ⟨M,hM,g⟩ := maximumFamilies_of_prefix family hm y2 parity
  have hbudget := fiber_budget hd (by omega : 1 ≤ k) hmk size scale hT
  have hprime : FirstOddProduct ⌊Real.exp (d * (k : ℝ))⌋₊ ∣
      FirstOddProduct ⌊Real.exp (c * (m : ℝ))⌋₊ :=
    firstOddProduct_dvd_of_le (Nat.floor_mono (Real.exp_le_exp.mpr
      (by linarith [show 0 ≤ d*(k:ℝ) by positivity])))
  refine ⟨M,hbudget.trans hM,?_⟩
  intro y hy
  obtain ⟨div,S,hS,hs⟩ := g y hy
  exact ⟨hprime.trans div,S,hbudget.trans hS,hs⟩

end OddEgyptian
