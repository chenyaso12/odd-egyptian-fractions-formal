module

public import MathProblems.OddEgyptian.DigitAssembly
public import MathProblems.OddEgyptian.DigitSieve
public import MathProblems.OddEgyptian.NumericSelection
public import MathProblems.OddEgyptian.DigitEstimates
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Filter Real
open scoped Topology

/-- The common odd primorial supporting digit m. Clipping the argument at one includes
the zero digit in the monotonicity statement. -/
noncomputable def a1Prime (m : ℕ) : ℕ :=
  oddPrimeProduct (digitSmooth 128 (max 1 (m:ℝ)))

private theorem smooth_positive {m : ℝ} (hm : 1 ≤ m) : 0 < digitSmooth 128 m := by
  have h3 := log_le_log (by norm_num : 0 < (3 : ℝ)) (show 3 ≤ 3*m by linarith)
  have h2 := log_pos (show 1 < 2*m by linarith)
  have hll := log_pos (show 1 < log (3*m) by linarith [log_three_gt_d9])
  unfold digitSmooth
  positivity

private theorem smooth_mono {m n : ℝ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    digitSmooth 128 m ≤ digitSmooth 128 n := by
  have h2 := log_pos (show 1 < 2*m by linarith)
  have h3 := log_pos (show 1 < 3*m by linarith)
  have h4 := log_le_log (by norm_num : 0 < (3 : ℝ)) (show 3 ≤ 3*m by linarith)
  have hll := log_pos (show 1 < log (3*m) by linarith [log_three_gt_d9])
  have h2n := log_pos (show 1 < 2*n by linarith)
  unfold digitSmooth
  gcongr

theorem a1Prime_dvd_succ (m : ℕ) : a1Prime m ∣ a1Prime (m+1) :=
  oddPrimeProduct_dvd_of_le (smooth_mono (le_max_left ..) (max_le_max_left _ (by exact_mod_cast
    (show m ≤ m+1 by omega))))

/-- For any input satisfying the three-prime count, one absolute number of terms works
at every nonnegative integer, for the explicitly specified monotone primorial. -/
theorem a1_uniform (input : ThreePrimeInput) :
    ∃ J : ℕ, ∀ m : ℕ, SmoothExpansion (a1Prime m) J m (fun _ => True) := by
  obtain ⟨v, hv, m₀, hm₀, hcount⟩ := input
  obtain ⟨t, _, hcard⟩ := log_card_oddPrimeProduct_divisors
  have toReal : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have toLog := Real.tendsto_log_atTop.comp toReal
  have toLoglog := Real.tendsto_log_atTop.comp toLog
  have eventuallyGood : ∀ᶠ m : ℕ in atTop, Odd m → ThreeGood (a1Prime m).divisors m := by
    filter_upwards [toReal.eventually (digit_a1_eventually hv), eventually_ge_atTop m₀,
      toLog.eventually_ge_atTop (max t 1), toLoglog.eventually_ge_atTop 1] with
        m hA hm hmt hlm ho
    change log (m:ℝ) ≥ max t 1 at hmt
    change log (log (m:ℝ)) ≥ 1 at hlm
    have hm7 : 7 ≤ m := hm₀.trans hm
    have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    let Y := digitSmooth 128 (m:ℝ)
    have hP : a1Prime m = oddPrimeProduct Y := by simp [a1Prime, max_eq_right hmR, Y]
    rw [hP]
    obtain ⟨hY3, hmain, herr⟩ := hA
    have h₂ : log (m:ℝ) ≤ log (2*m) := by apply log_le_log <;> linarith
    have h₃ : log (m:ℝ) ≤ log (3*m) := by apply log_le_log <;> linarith
    have hlog : 1 ≤ log (m:ℝ) := (le_max_right ..).trans hmt
    have hll : 1 ≤ log (log (3*m)) := hlm.trans (log_le_log (by linarith) h₃)
    have hYt : t ≤ Y := by
      dsimp [Y, digitSmooth]
      have hh := mul_le_mul_of_nonneg_left hll (by linarith : 0 ≤ 128*log (2*m))
      linarith [(le_max_left t 1).trans hmt]
    have hcard' := hmain.trans (hcard Y hYt)
    have hPpos := oddPrimeProduct_pos Y
    have hcpos : 0 < (oddPrimeProduct Y).divisors.card := by
      apply Finset.card_pos.mpr
      exact ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, hPpos.ne'⟩⟩
    have hsize : (m:ℝ)^2 ≤ (oddPrimeProduct Y).divisors.card := by
      have hlog' : log ((m:ℝ)^2) ≤ log ((oddPrimeProduct Y).divisors.card:ℝ) := by
        simpa only [log_pow, Nat.cast_ofNat] using hcard'
      exact (log_le_log_iff (by positivity) (by exact_mod_cast hcpos)).mp hlog'
    have hrs : (m:ℝ)^(3/4:ℝ) ≤ m := by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hmR (by norm_num : (3/4:ℝ) ≤ 1)
    apply goodTriple_of_count m (oddPrimeProduct Y) _ v Y hm7 hPpos
      (fun z hz ↦ Nat.le_of_dvd hPpos (Nat.dvd_of_mem_divisors hz))
      (chebyshevInputs.2 Y (by change 3 ≤ Y at hY3; linarith))
      _ (hcount m hm ho) herr
    have hr7 : (7:ℝ) ≤ m := by exact_mod_cast hm7
    nlinarith [mul_nonneg (sub_nonneg.mpr hr7) (show 0 ≤ (m:ℝ) by positivity)]
  obtain ⟨M, hM⟩ := eventually_atTop.mp eventuallyGood
  exact ⟨max 10 M, boundedSmoothExpansions a1Prime (fun m ↦ oddPrimeProduct_odd _)
    a1Prime_dvd_succ M hM⟩

/-- The support of every small digit divides the ambient primorial, and its square is
strictly below the auxiliary prime. This also covers m = 0. -/
theorem a1_small_support {B m : ℕ} {y δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1/8192)
    (hlam : 1 < log B) (hlamy : log B ≤ y)
    (hs : log 2 ≤ digitBreak δ (log B)) (hslam : digitBreak δ (log B) + log 3 ≤ log B)
    (hm : (m:ℝ) ≤ exp (digitBreak δ (log B))) :
    a1Prime m ∣ oddPrimeProduct y ∧ (a1Prime m)^2 < B := by
  let m' : ℝ := max 1 (m:ℝ)
  have hmp : 1 ≤ m' := le_max_left .. 
  have hs0 : 0 ≤ digitBreak δ (log B) := (log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans hs
  have hm' : m' ≤ exp (digitBreak δ (log B)) := max_le (one_le_exp hs0) hm
  have hlm : log m' ≤ digitBreak δ (log B) := by
    simpa only [log_exp] using log_le_log (by linarith) hm'
  let Y := digitSmooth 128 m'
  have hY : Y ≤ 256*δ*log B := digit_small_smooth_bound hδ hlam hmp hlm hs hslam
  have hlB : 0 < log (B:ℝ) := by linarith
  have hYsm : 4*Y < log B := by
    have h := mul_le_mul_of_nonneg_right hδmax hlB.le
    nlinarith
  have hYpos : 0 < Y := smooth_positive hmp
  refine ⟨oddPrimeProduct_dvd_of_le (show Y ≤ y by linarith), ?_⟩
  have hP := oddPrimeProduct_pos Y
  have hb : 0 < B := by by_contra! H; norm_num [show B = 0 by omega] at hlam
  have hlogP := chebyshevInputs.2 Y hYpos
  have hstrict : log (((oddPrimeProduct Y:ℕ) : ℝ)^2) < log (B:ℝ) := by
    rw [log_pow]
    norm_num
    linarith
  have hh := (log_lt_log_iff (by positivity) (by exact_mod_cast hb)).mp hstrict
  exact_mod_cast hh

end OddEgyptian

