module

public import MathProblems.OddEgyptian.NumericSelection
public import MathProblems.OddEgyptian.DigitEstimates
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Real Filter

noncomputable def digitCutoff (B : ℕ) : ℕ :=
  ⌊exp (digitBreak (1/8192) (log (B : ℝ)))⌋₊

noncomputable def digitFiber (y : ℝ) (B r : ℕ) : Finset ℕ :=
  (oddPrimeProduct y).divisors.filter fun d ↦ d % B = r

/-- A single choice for every digit at a given denominator. The template bound
R and the lower threshold in the three-prime estimate are fixed before it. -/
structure DigitParameterData (R b m₀ : ℕ) (v : ℝ) where
  y : ℝ
  B : ℕ
  L : ℕ
  r : ℕ
  hy : 3 ≤ y
  primeB : B.Prime
  base_gt_y : y < (B : ℝ)
  not_dvd_b : ¬B ∣ b
  R_lt_B : R < B
  scale_lt : (oddPrimeProduct y)^4 < b
  scale_mul_lt : (oddPrimeProduct y)^4 * R < b
  capacity : b ≤ B^L
  length_bound : (L : ℝ) ≤ 262145 * log (log (b : ℝ))
  logB_gt_one : 1 < log (B : ℝ)
  logB_le_y : log (B : ℝ) ≤ y
  small_lo : log 2 ≤ digitBreak (1/8192) (log (B : ℝ))
  small_hi : digitBreak (1/8192) (log (B : ℝ)) + log 3 ≤ log (B : ℝ)
  cutoff : m₀ ≤ digitCutoff B
  r_lt_B : r < B
  nonroot : ¬B ∣ 2*r^2 + 1
  fiber_size : ∀ m : ℕ, m < B → 2*(m : ℝ)^(3/4 : ℝ) ≤ ((digitFiber y B r).card : ℝ)
  large_error : ∀ m : ℕ, digitCutoff B < m → m < B →
    (24/log 2)*y*(log (m : ℝ))^3 < v*(m : ℝ)^(1/4 : ℝ)

private theorem scale_bounds {y : ℝ} {R b : ℕ} (hy : 0 < y) (hRy : (R : ℝ) < y)
    (hb : 0 < b) (hbLog : log (b : ℝ) = 32*y) :
    (oddPrimeProduct y)^4 < b ∧ (oddPrimeProduct y)^4*R < b := by
  let P := oddPrimeProduct y
  have hP : (0 : ℝ) < P := by exact_mod_cast oddPrimeProduct_pos y
  have hp4 : (P : ℝ)^4 ≤ exp (8*y) := by
    calc (P : ℝ)^4 = exp (log ((P : ℝ)^4)) := (exp_log (by positivity)).symm
      _ ≤ _ := exp_le_exp.mpr (by rw [log_pow]; norm_num; linarith [chebyshevInputs.2 y hy])
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hre : (R : ℝ) ≤ exp y := by linarith [add_one_le_exp y]
  have h1 : (P : ℝ)^4 < b := by
    calc (P : ℝ)^4 ≤ exp (8*y) := hp4
      _ < exp (log (b : ℝ)) := exp_lt_exp.mpr (by rw [hbLog]; linarith)
      _ = _ := exp_log hbpos
  have h2 : (P : ℝ)^4 * R < b := by
    calc (P : ℝ)^4 * R ≤ exp (8*y) * exp y := by gcongr
      _ = exp (8*y+y) := (exp_add ..).symm
      _ < exp (log (b : ℝ)) := exp_lt_exp.mpr (by rw [hbLog]; linarith)
      _ = _ := exp_log hbpos
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

private theorem length_bounds {y : ℝ} {B b : ℕ} (hy : 3 ≤ y) (hly : 1 ≤ log y)
    (hb : 0 < b) (hbLog : log (b : ℝ) = 32*y) (hB : 0 < B)
    (hlam : 1 < log (B : ℝ)) (hlow : (1/8192 : ℝ)*y/log y ≤ log (B : ℝ)) :
    ∃ L : ℕ, b ≤ B^L ∧ (L : ℝ) ≤ 262145 * log (log (b : ℝ)) := by
  let s := log (b : ℝ) / log (B : ℝ)
  let L := ⌈s⌉₊
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hlp : 0 < log (B : ℝ) := by linarith
  have hlyp : 0 < log y := by linarith
  have hs : 0 ≤ s := by dsimp [s]; rw [hbLog]; positivity
  have hL : b ≤ B^L := by
    have h0 : log (b : ℝ) ≤ log ((B : ℝ)^L) := by
      rw [log_pow]
      exact (div_le_iff₀ hlp).mp (Nat.le_ceil s)
    have := (Real.log_le_log_iff hbp (pow_pos hBp L)).mp h0
    exact_mod_cast this
  have hsl : s ≤ 262144 * log y := by
    apply (div_le_iff₀ hlp).mpr
    rw [hbLog]
    have e := (div_le_iff₀ hlyp).mp hlow
    linarith
  have hll : log y ≤ log (log (b : ℝ)) := log_le_log (by linarith) (by rw [hbLog]; linarith)
  have hl1 := Nat.ceil_lt_add_one hs
  refine ⟨L, hL, ?_⟩
  dsimp only [L]
  linarith

private theorem lower_bound_fiber {y : ℝ} {B r : ℕ} (hB : B.Prime) (hy : 0 < y)
    (hlog : (log 2/4)*y/log y ≤ log ((oddPrimeProduct y).divisors.card : ℝ))
    (hupp : log (B : ℝ) ≤ 2*(1/8192 : ℝ)*y/log y) (hly : 0 < log y)
    (hcount : (oddPrimeProduct y).divisors.card ≤ 2*B*(digitFiber y B r).card) :
    ∀ m : ℕ, m < B → 2*(m : ℝ)^(3/4 : ℝ) ≤ ((digitFiber y B r).card : ℝ) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB.pos
  have hdpos : (0 : ℝ) < (oddPrimeProduct y).divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (oddPrimeProduct_pos y).ne'⟩
  have hfour : B^4 ≤ (oddPrimeProduct y).divisors.card := by
    have he : log ((B : ℝ)^4) ≤ log ((oddPrimeProduct y).divisors.card : ℝ) := by
      rw [log_pow]
      norm_num
      apply le_trans _ hlog
      have hscale : (8*(1/8192 : ℝ))*y/log y ≤ (log 2/4)*y/log y :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [Real.log_two_gt_d9]) hy.le) hly.le
      calc 4 * log (B : ℝ) ≤ 4 * (2*(1/8192 : ℝ)*y/log y) := by linarith
           _ = (8*(1/8192 : ℝ))*y/log y := by ring
           _ ≤ _ := hscale
    exact_mod_cast (Real.log_le_log_iff (by positivity) hdpos).mp he
  have hbase : 4 ≤ B^2 := (Nat.pow_le_pow_left hB.two_le 2)
  have hcnt : 2*B ≤ (digitFiber y B r).card := by
    have hw : 2*B*(2*B) ≤ B^4 := by nlinarith [Nat.mul_le_mul_right (B^2) hbase]
    exact Nat.le_of_mul_le_mul_left (hw.trans (hfour.trans hcount)) (Nat.mul_pos (by decide) hB.pos)
  intro m hm
  have hmB : (m : ℝ) ≤ B := by exact_mod_cast hm.le
  have hpow := (Real.rpow_le_rpow (Nat.cast_nonneg _) hmB (by norm_num : 0 ≤ (3/4 : ℝ))).trans
    (Real.rpow_le_self_of_one_le (by exact_mod_cast hB.one_lt.le) (by norm_num))
  have hcnt' : 2*(B : ℝ) ≤ ((digitFiber y B r).card : ℝ) := by exact_mod_cast hcnt
  linarith

theorem exists_digitParameterData (R m₀ : ℕ) (v : ℝ) (hv : 0 < v) :
    ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → 3 ≤ b → Nonempty (DigitParameterData R b m₀ v) := by
  obtain ⟨tp, _, hprime⟩ := auxiliary_prime_interval
  obtain ⟨td, _, hd⟩ := log_card_oddPrimeProduct_divisors
  let ε : ℝ := 1/8192
  have hε : 0 < ε := by norm_num [ε]
  obtain ⟨t, ht⟩ := eventually_atTop.mp
    ((digit_thresholds hε hε (max (R : ℝ) tp) (log ((m₀ : ℝ)+1))).and (digit_large_uniform hε hε hv))
  let Y := max td t
  refine ⟨⌈exp (32*Y)⌉₊, ?_⟩
  intro b hb hb3
  have hbp : 0 < b := by omega
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hbp
  let y := log (b : ℝ) / 32
  have hbLog : log (b : ℝ) = 32*y := by dsimp [y]; ring
  have hY : Y ≤ y := by
    have he : exp (32*Y) ≤ (b : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hb)
    have h := Real.log_le_log (exp_pos _) he
    rw [Real.log_exp] at h
    dsimp [y]
    linarith
  obtain ⟨hthreshold, herr⟩ := ht y ((le_max_right ..).trans hY)
  obtain ⟨hy, hR, hly, hX, hlog8, _, hlambda⟩ := hthreshold
  have hypos : 0 < y := by linarith
  let a := ε*y/log y
  let X := exp a
  have hRy : (R : ℝ) < y := (le_max_left ..).trans_lt hR
  have hty : tp < y := (le_max_right ..).trans_lt hR
  have hyX : y < X := by change y < exp (ε*y/log y); linarith
  obtain ⟨B, hp, hXB, hB8, hBb⟩ := hprime X (hty.trans hyX).le b hbp (by
    rw [hbLog]
    change 32*y < 2*exp (ε*y/log y)
    linarith)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hp.pos
  have hlow : ε*y/log y ≤ log (B : ℝ) := by
    simpa [X, a] using (log_lt_log (exp_pos a) hXB).le
  have hhigh : log (B : ℝ) ≤ 2*ε*y/log y := by
    have h := log_le_log hBpos hB8
    rw [log_mul (by norm_num) (exp_pos a).ne', log_exp] at h
    dsimp [a] at h
    calc log (B : ℝ) ≤ log 8 + ε*y/log y := h
         _ ≤ 2*(ε*y/log y) := by linarith
         _ = 2*ε*y/log y := by ring
  obtain ⟨he2, hBy, hM, hsmall, hsmall'⟩ := hlambda (log (B : ℝ)) hlow hhigh
  have hl1 : 1 < log (B : ℝ) := by linarith [add_one_le_exp 2]
  have hcut : m₀ ≤ digitCutoff B := by
    apply Nat.le_floor
    have hh := Real.exp_le_exp.mpr hM
    rw [exp_log (by positivity)] at hh
    linarith
  obtain ⟨r, _, hrB, hnroot, hcount⟩ := common_nonroot_class y B hy hp (hyX.trans hXB)
  have hdiv := hd y ((le_max_left ..).trans hY)
  have hf := lower_bound_fiber hp hypos hdiv hhigh (by linarith) hcount
  obtain ⟨L, hcapacity, hlength⟩ := length_bounds hy hly hbp hbLog hp.pos hl1 hlow
  obtain ⟨hscale, hscR⟩ := scale_bounds hypos hRy hbp hbLog
  refine ⟨⟨y, B, L, r, hy, hp, hyX.trans hXB, hBb, ?_, hscale, hscR, hcapacity, hlength,
    hl1, hBy, hsmall, hsmall', hcut, hrB, hnroot, hf, ?_⟩⟩
  · exact_mod_cast hRy.trans (hyX.trans hXB)
  · intro m hm hb'
    have hm0 : 0 < m := by omega
    have hbefore : exp (digitBreak ε (log (B : ℝ))) < (m : ℝ) :=
      (Nat.floor_lt (Real.exp_pos _).le).mp hm
    apply herr (log (B : ℝ)) (m : ℝ) hl1 hlow hBy (by exact_mod_cast hm0)
    · simpa using (log_lt_log (exp_pos _) hbefore).le
    · exact log_le_log (by exact_mod_cast hm0) (by exact_mod_cast hb'.le)

end OddEgyptian
