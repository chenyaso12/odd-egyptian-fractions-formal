module

public import MathProblems.OddEgyptian.PrimePowerBridge
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Filter Asymptotics

/-- A lower bound for the real part of a complex main term survives an error of
at most half its guaranteed size. -/
private theorem real_ge_of_close {r scale a : ℝ} {z : ℂ}
    (hmain : a*scale ≤ z.re)
    (hclose : ‖(r : ℂ) - z‖ ≤ (a/2)*scale) : (a/2)*scale ≤ r := by
  have hreal := (abs_le.mp ((Complex.abs_re_le_norm ((r : ℂ) - z)).trans hclose)).1
  simp only [Complex.sub_re, Complex.ofReal_re] at hreal
  linarith

/-- A quadratic lower bound for the main term and a complex little-o error imply
a quadratic lower bound for the real additive convolution, retaining half the constant. -/
theorem circle_eventually_lower {R : ℕ → ℝ} {M : ℕ → ℂ} {a : ℝ} (ha : 0 < a)
    (hmain : ∀ᶠ n : ℕ in atTop, Odd n → a*(n : ℝ)^2 ≤ (M n).re)
    (herr : (fun n : ℕ => (R n : ℂ) - M n) =o[atTop] (fun n : ℕ => (n : ℝ)^2)) :
    ∀ᶠ n : ℕ in atTop, Odd n → (a/2)*(n : ℝ)^2 ≤ R n := by
  filter_upwards [hmain, herr.bound (show 0 < a / 2 by positivity)] with n hn he ho
  exact real_ge_of_close (hn ho) (by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n : ℝ))] using he)

private theorem mangoldtInput_of_lower {R : ℕ → ℝ} {v : ℝ} (hv : 0 < v)
    (hR : ∀ n, R n = mangoldtTripleSum n)
    (h : ∀ᶠ n : ℕ in atTop, Odd n → v*(n : ℝ)^2 ≤ R n) : MangoldtTripleInput := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  exact ⟨v, hv, N, fun n hn ho => (hN n hn ho).trans_eq (hR n)⟩

theorem mangoldtInput_of_circle {R : ℕ → ℝ} {M : ℕ → ℂ} {a : ℝ} (ha : 0 < a)
    (hR : ∀ n, R n = mangoldtTripleSum n)
    (hmain : ∀ᶠ n : ℕ in atTop, Odd n → a*(n : ℝ)^2 ≤ (M n).re)
    (herr : (fun n : ℕ => (R n : ℂ) - M n) =o[atTop] (fun n : ℕ => (n : ℝ)^2)) :
    MangoldtTripleInput :=
  mangoldtInput_of_lower (half_pos ha) hR (circle_eventually_lower ha hmain herr)

/-- Direct interface for a per-odd-integer quadratic lower bound with constant 1/4. -/
theorem mangoldtInput_of_quarter {R : ℕ → ℝ} (hR : ∀ n, R n = mangoldtTripleSum n)
    (h : ∀ᶠ n : ℕ in atTop, Odd n → (1/4 : ℝ)*(n : ℝ)^2 ≤ R n) : MangoldtTripleInput :=
  mangoldtInput_of_lower (by norm_num : (0 : ℝ) < 1/4) hR h

/-- The singular-series normalization used by the complex ternary circle method. -/
noncomputable def circleMainTerm (singSeries : ℤ → ℂ) (n : ℕ) : ℂ :=
  (1/2 : ℂ) * singSeries (n : ℤ) * (n : ℂ)^2

private theorem circleMainTerm_real_ge {S : ℤ → ℂ} {n : ℕ}
    (hS : 1 ≤ (S (n : ℤ)).re) :
    (1/2 : ℝ)*(n : ℝ)^2 ≤ (circleMainTerm S n).re := by
  have hcast : (n : ℂ)^2 = (((n : ℝ)^2 : ℝ) : ℂ) := by norm_cast
  rw [circleMainTerm, hcast, Complex.re_mul_ofReal]
  norm_num [Complex.mul_re]
  nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sq_nonneg (n : ℝ))]

private theorem circle_quarter {r : ℝ} {S : ℤ → ℂ} {n : ℕ}
    (hS : 1 ≤ (S (n : ℤ)).re)
    (hclose : ‖(r : ℂ) - circleMainTerm S n‖ ≤ (1/4 : ℝ)*(n : ℝ)^2) :
    (1/4 : ℝ)*(n : ℝ)^2 ≤ r := by
  have hhalf : (1 / 2 : ℝ) / 2 = 1 / 4 := by norm_num
  rw [← hhalf] at hclose ⊢
  exact real_ge_of_close (circleMainTerm_real_ge hS) hclose

/-- Pointwise quarter bound in the normalization of the circle-method main term. -/
theorem circle_quarter_of_close {r : ℝ} {S : ℤ → ℂ} {n : ℕ} (ho : Odd n)
    (hpos : ∀ k : ℤ, ¬(2 : ℤ) ∣ k → 1 ≤ (S k).re)
    (hclose : ‖(r : ℂ) - circleMainTerm S n‖ ≤ (1/4 : ℝ)*(n : ℝ)^2) :
    (1/4 : ℝ)*(n : ℝ)^2 ≤ r :=
  circle_quarter (hpos n (by exact_mod_cast ho.not_two_dvd_nat)) hclose

/-- The singular series need only be bounded below at positive odd arguments. -/
theorem mangoldtInput_of_singularSeries_nat {R : ℕ → ℝ} {S : ℤ → ℂ}
    (hR : ∀ n, R n = mangoldtTripleSum n)
    (hpos : ∀ n : ℕ, Odd n → 1 ≤ (S (n : ℤ)).re)
    (herr : (fun n : ℕ => (R n : ℂ) - circleMainTerm S n) =o[atTop]
      (fun n : ℕ => (n : ℝ)^2)) : MangoldtTripleInput := by
  apply mangoldtInput_of_quarter hR
  filter_upwards [herr.bound (show (0 : ℝ) < 1/4 by norm_num)] with n he ho
  apply circle_quarter (hpos n ho)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n : ℝ))] using he

/-- A singular series bounded below by one at odd integers and a complex o(n²)
remainder give the project's Mangoldt input with constant 1/4. -/
theorem mangoldtInput_of_singularSeries {R : ℕ → ℝ} {S : ℤ → ℂ}
    (hR : ∀ n, R n = mangoldtTripleSum n)
    (hpos : ∀ k : ℤ, ¬(2 : ℤ) ∣ k → 1 ≤ (S k).re)
    (herr : (fun n : ℕ => (R n : ℂ) - circleMainTerm S n) =o[atTop]
      (fun n : ℕ => (n : ℝ)^2)) : MangoldtTripleInput :=
  mangoldtInput_of_singularSeries_nat hR
    (fun n ho => hpos n (by exact_mod_cast ho.not_two_dvd_nat)) herr

end OddEgyptian
