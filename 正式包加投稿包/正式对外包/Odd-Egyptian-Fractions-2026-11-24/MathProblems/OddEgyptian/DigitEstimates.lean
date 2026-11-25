module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Filter Real
open scoped Topology

/-- Any fixed natural power of the logarithm is eventually less than an arbitrarily
small positive multiple of any positive real power. -/
theorem digit_log_power_bound (n : ℕ) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, (log y)^n ≤ c*y^r := by
  have bound := (isLittleO_log_rpow_rpow_atTop (n:ℝ) hr).bound hc
  filter_upwards [bound, eventually_gt_atTop (1:ℝ)] with y h hy
  have hl := log_pos hy
  have hy0 : 0 < y := by linarith
  simpa only [rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hl.le _),
    abs_of_nonneg (rpow_nonneg hy0.le _)] using h

theorem digit_ratio_atTop (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun y : ℝ ↦ a*y/(log y)^n) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  have hpos : 0 < |K|+1 := by positivity
  filter_upwards [digit_log_power_bound n (r := 1) one_pos (div_pos ha hpos),
    eventually_gt_atTop (1:ℝ)] with y h hy
  rw [rpow_one] at h
  have hlog := log_pos hy
  have hlpow := pow_pos hlog n
  apply (le_div_iff₀ hlpow).mpr
  have hmul : (log y)^n*(|K|+1) ≤ a*y := by
    rw [div_mul_eq_mul_div] at h
    exact (le_div_iff₀ hpos).mp h
  calc K*(log y)^n ≤ (|K|+1)*(log y)^n := mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) hlpow.le
       _ ≤ _ := by linarith

/-- The uniform error in the large-digit interval goes to zero. -/
theorem digit_error_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun y : ℝ ↦ y^4*exp (-(a*y/(log y)^2))) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_inv_atTop_zero (𝕜 := ℝ))
  · exact Filter.Eventually.of_forall fun y ↦ by positivity
  · filter_upwards [digit_log_power_bound 3 (r := 1) one_pos (show 0 < a/5 by positivity),
      eventually_gt_atTop (1:ℝ)] with y h hy
    have hl := log_pos hy
    have hy0 : 0 < y := by linarith
    rw [rpow_one] at h
    have hx : 5*log y ≤ a*y/(log y)^2 := (le_div_iff₀ (sq_pos_of_pos hl)).2 (by nlinarith)
    have he : exp (-(a*y/(log y)^2)) ≤ (y^5)⁻¹ := by
      calc exp (-(a*y/(log y)^2)) ≤ exp (-(5*log y)) := exp_le_exp.mpr (by linarith)
           _ = (y^5)⁻¹ := by
             have H : log (y^5) = 5*log y := by simp [Real.log_pow]
             rw [← H, exp_neg, exp_log (by positivity)]
    calc y^4*exp (-(a*y/(log y)^2)) ≤ y^4*(y^5)⁻¹ := mul_le_mul_of_nonneg_left he (by positivity)
         _ = y⁻¹ := by field_simp

/-- Smoothness cutoff in A1, shared with the small-digit argument. -/
noncomputable def digitSmooth (K m : ℝ) : ℝ := K * log (2*m) * log (log (3*m))

/-- A1 needs many divisors and a negligible exceptional part at the same cutoff.
The explicit K = 128 is an admissible absolute choice. -/
theorem digit_a1_eventually {cV : ℝ} (hcV : 0 < cV) :
    ∀ᶠ m : ℝ in atTop,
      3 ≤ digitSmooth 128 m ∧
      2*log m ≤ (log 2/4)*digitSmooth 128 m/log (digitSmooth 128 m) ∧
      (24/log 2)*digitSmooth 128 m*(log m)^3 < cV*m^(1/4 : ℝ) := by
  have loglog := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have htwo : (1:ℝ)/2 < log 2 := by linarith [Real.log_two_gt_d9]
  have hc : 0 < cV/100000 := by positivity
  filter_upwards [loglog.eventually_ge_atTop (log 512+1),
    loglog.eventually_ge_atTop 2, eventually_ge_atTop (3:ℝ),
    digit_log_power_bound 5 (r := (1/4 : ℝ)) (by norm_num) hc] with m h512 hll hm herr
  change log (log m) ≥ _ at h512 hll
  have hm0 : 0 < m := by linarith
  have hl := log_pos (show 1 < m by linarith)
  have hlo : log m ≤ log (2*m) := log_le_log hm0 (by linarith)
  have hhi : log (2*m) ≤ 2*log m := by
    rw [log_mul (by norm_num) hm0.ne']
    linarith [log_le_log (by norm_num : 0 < (2:ℝ)) (show 2 ≤ m by linarith)]
  have h₃ : log m ≤ log (3*m) := log_le_log hm0 (by linarith)
  have h₄ : log (3*m) ≤ 2*log m := by
    rw [log_mul (by norm_num) hm0.ne']
    linarith [log_le_log (by norm_num : 0 < (3:ℝ)) hm]
  have hllo := log_le_log hl h₃
  have hllhi := log_le_log (hl.trans_le h₃) h₄
  rw [log_mul (by norm_num) hl.ne'] at hllhi
  have hllhi' : log (log (3*m)) ≤ 2*log m := by
    linarith [log_le_self hl.le, Real.log_two_lt_d9]
  have hlbig : 1 ≤ log m := by linarith [log_le_self hl.le]
  have hYlo : 128 * log m * log (log m) ≤ digitSmooth 128 m := by
    unfold digitSmooth
    gcongr; linarith
  have hYhi : digitSmooth 128 m ≤ 512*(log m)^2 := by
    unfold digitSmooth
    calc 128*log (2*m)*log (log (3*m)) ≤ 128*(2*log m)*(2*log m) := by gcongr; linarith
         _ = _ := by ring
  have hY : 3 ≤ digitSmooth 128 m := by
    nlinarith [mul_le_mul_of_nonneg_left hll hl.le]
  have hlogY : log (digitSmooth 128 m) ≤ 3*log (log m) := by
    have H := log_le_log (by linarith : 0 < digitSmooth 128 m) hYhi
    rw [log_mul (by norm_num) (by positivity), log_pow] at H
    norm_num at H
    linarith
  refine ⟨hY, (le_div_iff₀ (log_pos (by linarith))).mpr ?_, ?_⟩
  · have hcoef : 1/8 < log 2/4 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlogY (by positivity : 0 ≤ 2*log m),
      mul_le_mul_of_nonneg_right hcoef.le (by linarith : 0 ≤ digitSmooth 128 m),
      mul_nonneg hl.le (show 0 ≤ log (log m) by linarith)]
  · have h48 : 24/log 2 ≤ 48 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    have hb : (24/log 2)*digitSmooth 128 m*(log m)^3 ≤ 24576*(log m)^5 := calc
      _ ≤ 48*(512*(log m)^2)*(log m)^3 := by gcongr
      _ = _ := by ring
    have hpow := rpow_pos_of_pos hm0 (1/4 : ℝ)
    nlinarith [mul_pos hcV hpow]

/-- The point where the large- and small-digit arguments meet, before its exponential is floored. -/
noncomputable def digitBreak (δ lam : ℝ) : ℝ := δ*lam/log lam

/-- Analytic conditions needed before an auxiliary prime is chosen. The interval endpoint is
X = exp (η y / log y). Everything after the final quantifier is uniform in log B. -/
theorem digit_thresholds {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (R M : ℝ) :
    ∀ᶠ y : ℝ in atTop,
      3 ≤ y ∧ R < y ∧ 1 ≤ log y ∧
      32*y < exp (η*y/log y) ∧ log 8 ≤ η*y/log y ∧ 2*η*y/log y ≤ y ∧
      ∀ lam : ℝ, η*y/log y ≤ lam → lam ≤ 2*η*y/log y →
        exp 2 ≤ lam ∧ lam ≤ y ∧ M ≤ digitBreak δ lam ∧ log 2 ≤ digitBreak δ lam ∧
        digitBreak δ lam + log 3 ≤ lam := by
  have hratio : Tendsto (fun y : ℝ ↦ η*y/log y) atTop atTop := by
    simpa only [pow_one] using digit_ratio_atTop 1 hη
  have hbreak : Tendsto (digitBreak δ) atTop atTop := by
    change Tendsto (fun x : ℝ ↦ δ*x/log x) atTop atTop
    simpa only [pow_one] using digit_ratio_atTop 1 hδ
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    (show ∀ᶠ lam : ℝ in atTop, exp 2 ≤ lam ∧ M ≤ digitBreak δ lam ∧ log 2 ≤ digitBreak δ lam ∧
        digitBreak δ lam + log 3 ≤ lam by
      filter_upwards [eventually_ge_atTop (exp 2), hbreak.eventually_ge_atTop M,
        hbreak.eventually_ge_atTop (log 2), tendsto_log_atTop.eventually_ge_atTop (2*δ),
        eventually_ge_atTop (2*log 3)] with lam h₁ h₂ h₃ h₄ h₅
      refine ⟨h₁, h₂, h₃, ?_⟩
      have hlam := (exp_pos 2).trans_le h₁
      have hl : 0 < log lam := by linarith
      have hs : digitBreak δ lam ≤ lam/2 := (div_le_iff₀ hl).2 (by nlinarith [mul_le_mul_of_nonneg_right h₄ hlam.le])
      linarith)
  filter_upwards [eventually_ge_atTop (33:ℝ), eventually_gt_atTop R,
    tendsto_log_atTop.eventually_ge_atTop (max 1 (2*η)), hratio.eventually_ge_atTop (log 8),
    hratio.eventually_ge_atTop L, digit_log_power_bound 2 (r := 1) one_pos
      (show 0 < η/2 by positivity)] with y hy hR hl h8 hL' hpow
  have hy0 : 0 < y := by linarith
  have hl1 : 1 ≤ log y := (le_max_left ..).trans hl
  have hlη : 2*η ≤ log y := (le_max_right ..).trans hl
  have hlp : 0 < log y := by linarith
  rw [rpow_one] at hpow
  have hx : y^2 ≤ exp (η*y/log y) := by
    have hz : log (y^2) ≤ η*y/log y := by
      rw [log_pow]
      apply (le_div_iff₀ hlp).mpr
      norm_num
      nlinarith
    simpa only [exp_log (by positivity : 0 < y^2)] using (exp_le_exp.mpr hz)
  have hlammax : 2*η*y/log y ≤ y := (div_le_iff₀ hlp).mpr (by nlinarith [mul_le_mul_of_nonneg_right hlη hy0.le])
  refine ⟨by linarith, hR, hl1, ?_, h8, hlammax, ?_⟩
  · apply lt_of_lt_of_le _ hx
    nlinarith [mul_pos hy0 (show 0 < y-32 by linarith)]
  · intro lam hlow hhigh
    obtain ⟨he, hi, hj, hk⟩ := hL lam (hL'.trans hlow)
    exact ⟨he, hhigh.trans hlammax, hi, hj, hk⟩

/-- Uniform small-digit estimate. Taking K=128, δ=1/8192 makes
four times the logarithmic smoothness bound strictly less than lam. -/
theorem digit_small_smooth_bound {δ lam m : ℝ} (hδ : 0 < δ) (hlam : 1 < lam) (hm : 1 ≤ m)
    (hlm : log m ≤ digitBreak δ lam) (hs : log 2 ≤ digitBreak δ lam)
    (hslam : digitBreak δ lam + log 3 ≤ lam) : digitSmooth 128 m ≤ 256*δ*lam := by
  have hm0 : 0 < m := by linarith
  have hloglam := log_pos hlam
  have h2 : log (2*m) ≤ 2*digitBreak δ lam := by rw [log_mul (by norm_num) hm0.ne']; linarith
  have h3 : log (3*m) ≤ lam := by rw [log_mul (by norm_num) hm0.ne']; linarith
  have hm3 : 1 < 3*m := by linarith
  have hll : log (log (3*m)) ≤ log lam := log_le_log (log_pos hm3) h3
  have hpos : 0 ≤ log (log (3*m)) := by
    apply log_nonneg
    have h := log_le_log (by norm_num : 0 < (3:ℝ)) (show 3 ≤ 3*m by linarith)
    linarith [log_three_gt_d9]
  have hbreak : 0 ≤ digitBreak δ lam := (log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans hs
  calc digitSmooth 128 m ≤ 128*(2*digitBreak δ lam)*log lam := by
         unfold digitSmooth
         gcongr
       _ = 256*δ*lam := by unfold digitBreak; field_simp; ring

/-- Uniform large-digit bound in the exact normalization used by the bad-prime count.
For a natural m exceeding floor(exp(digitBreak δ lam)), the logarithmic lower bound used
here follows directly from exp(digitBreak δ lam) < m, with no rounding loss. -/
theorem digit_large_uniform {η δ cV : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hV : 0 < cV) :
    ∀ᶠ y : ℝ in atTop, ∀ lam m : ℝ, 1 < lam → η*y/log y ≤ lam → lam ≤ y →
      1 ≤ m → digitBreak δ lam ≤ log m → log m ≤ lam →
      (24/log 2)*y*(log m)^3 < cV*m^(1/4 : ℝ) := by
  let g := δ*η/4
  have hg : 0 < g := by dsimp [g]; positivity
  have hA : 0 < 24/log 2 := div_pos (by norm_num) (log_pos (by norm_num))
  filter_upwards [(digit_error_tendsto hg).eventually_lt_const (div_pos hV hA),
    eventually_gt_atTop (1:ℝ)] with y herr hy
  intro lam m hlam hl hlo hm hsl hmu
  have hlp := log_pos hy
  have hlamp := log_pos hlam
  have ho : log lam ≤ log y := log_le_log (by linarith) hlo
  have hlow : (δ*η*y)/(log y)^2 ≤ log m := calc
    _ = (δ*(η*y/log y))/log y := by field_simp
    _ ≤ (δ*lam)/log y := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hδ.le) hlp.le
    _ ≤ (δ*lam)/log lam := div_le_div_of_nonneg_left (by positivity) hlamp ho
    _ ≤ log m := hsl
  have hp : exp (g*y/(log y)^2) ≤ m^(1/4 : ℝ) := by
    rw [rpow_def_of_pos (by linarith : 0 < m)]
    apply exp_le_exp.mpr
    dsimp [g]
    linarith [show δ*η/4*y/(log y)^2 = (δ*η*y/(log y)^2)/4 by ring]
  change y^4*exp (-(g*y/(log y)^2)) < cV/(24/log 2) at herr
  rw [exp_neg, ← div_eq_mul_inv] at herr
  have hmain := (div_lt_div_iff₀ (exp_pos _) hA).mp herr
  calc (24/log 2)*y*(log m)^3 ≤ (24/log 2)*y*y^3 := by
         exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (log_nonneg hm) (hmu.trans hlo) 3) (by positivity)
       _ = y^4*(24/log 2) := by ring
       _ < cV*exp (g*y/(log y)^2) := hmain
       _ ≤ cV*m^(1/4 : ℝ) := mul_le_mul_of_nonneg_left hp hV.le

end OddEgyptian

