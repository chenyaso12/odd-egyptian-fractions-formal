module

public import MathProblems.OddEgyptian.Finiteness
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Finset Real

/-- Each denominator is chosen in 1,...,M. Removing it squares the budget. -/
private def denominatorChoices : ℕ → ℕ → Finset (Finset ℕ)
  | 0, _ => {∅}
  | j+1, M => ((range M) ×ˢ denominatorChoices j (M^2)).image fun p => insert (p.1+1) p.2

private theorem denominatorChoices_card (j M : ℕ) :
    (denominatorChoices j M).card ≤ M^(2^j-1) := by
  induction j generalizing M with
  | zero => simp [denominatorChoices]
  | succ j ih =>
    have ht : 0 < 2^j := by positivity
    have hexp : 1+2*(2^j-1) = 2^(j+1)-1 := by rw [pow_succ]; omega
    calc
      (denominatorChoices (j+1) M).card ≤ (range M ×ˢ denominatorChoices j (M^2)).card := card_image_le
      _ ≤ M*(M^2)^(2^j-1) := by rw [card_product, card_range]; exact Nat.mul_le_mul_left _ (ih _)
      _ = M^1 * M^(2*(2^j-1)) := by rw [pow_one, pow_mul]
      _ = M^(2^(j+1)-1) := by rw [← pow_add, hexp]

private theorem mem_denominatorChoices (j : ℕ) (s : Finset ℕ) (K M b : ℕ) (a : ℤ)
    (hb : 0 < b) (hM : K*b ≤ M) (hcard : s.card = j) (hK : s.card ≤ K)
    (hp : ∀ d ∈ s, 0 < d) (hs : ∑ d ∈ s, (1 : ℚ)/d = (a : ℚ)/b) :
    s ∈ denominatorChoices j M := by
  induction j generalizing s M a b with
  | zero => simp [denominatorChoices, card_eq_zero.mp hcard]
  | succ j ih =>
    have hne : s.Nonempty := card_pos.mp (by omega)
    let n := s.min' hne
    have hn : n ∈ s := s.min'_mem hne
    have hnpos := hp n hn
    have hmin (d) (hd : d ∈ s) : n ≤ d := s.min'_le d hd
    have hpos : 0 < (a : ℚ)/b := by
      rw [← hs]
      exact sum_pos (fun d hd => by have := hp d hd; positivity) hne
    have ha : (1 : ℤ) ≤ a := by
      have hh : (0 : ℚ) < a := (div_pos_iff_of_pos_right (by exact_mod_cast hb)).mp hpos
      exact Int.add_one_le_iff.mpr (by exact_mod_cast hh)
    have ratio : (a : ℚ)/b ≤ (K : ℚ)/n := calc
      _ = ∑ d ∈ s, (1 : ℚ)/d := hs.symm
      _ ≤ ∑ _d ∈ s, (1 : ℚ)/n := sum_le_sum fun d hd =>
        one_div_le_one_div_of_le (by exact_mod_cast hnpos) (by exact_mod_cast hmin d hd)
      _ = (s.card : ℚ)/n := by simp [div_eq_mul_inv]
      _ ≤ _ := by gcongr
    have hnM : n ≤ M := by
      apply le_trans _ hM
      have prod := (div_le_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hnpos)).mp ratio
      have hprod : (1 : ℚ)*n ≤ (a : ℚ)*n := mul_le_mul_of_nonneg_right (by exact_mod_cast ha) (by positivity)
      exact_mod_cast (show (n : ℚ) ≤ (K : ℚ)*b by linarith)
    have newBudget : K*(b*n) ≤ M^2 := by rw [← Nat.mul_assoc, sq]; exact Nat.mul_le_mul hM hnM
    have tailSum : ∑ d ∈ s.erase n, (1 : ℚ)/d = ((a*(n:ℤ)-(b:ℤ) : ℤ):ℚ)/(b*n:ℕ) := by
      have h := s.sum_erase_add (fun d : ℕ => (1:ℚ)/d) hn
      rw [hs] at h
      push_cast
      rw [eq_sub_of_add_eq h]
      field_simp
    have tail := ih (s.erase n) (M^2) (b*n) (a*n-b) (Nat.mul_pos hb hnpos) newBudget
      (by rw [card_erase_of_mem hn,hcard]; omega) ((card_le_card (erase_subset _ _)).trans hK)
      (fun d hd => hp d (mem_of_mem_erase hd)) tailSum
    apply mem_image.mpr
    refine ⟨(n-1,s.erase n), mem_product.mpr ⟨mem_range.mpr (by omega), tail⟩, ?_⟩
    simpa [show n-1+1=n by omega] using insert_erase hn

/-- The manuscript's coordinatewise count for increasing distinct denominators. -/
theorem oddCount_le_sharp (k : ℕ) : oddCount k ≤ k^(2^k-1) := by
  let encode (x : Solutions k) : ↥(denominatorChoices k k) := ⟨x.1,
    mem_denominatorChoices k x.1 k k 1 1 (by decide) (by simp) x.2.2 x.2.2.le
      (fun d hd => by have := (x.2.1.1 d hd).1; omega) (by simpa using x.2.1.2)⟩
  calc
    oddCount k ≤ Nat.card ↥(denominatorChoices k k) := Nat.card_le_card_of_injective encode
      (fun x y eq => Subtype.ext (congrArg (fun w : ↥(denominatorChoices k k) => w.val) eq))
    _ = (denominatorChoices k k).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ _ := denominatorChoices_card k k

private theorem oddCount_cast_upper (k : ℕ) (hk : 1 ≤ k) : (oddCount k : ℝ) ≤ (k : ℝ)^(2^k : ℕ) := by
  exact_mod_cast (oddCount_le_sharp k).trans (Nat.pow_le_pow_right hk (Nat.sub_le _ _))

/-- This double-logarithmic estimate uses the classical domain 1 < S(k). -/
theorem oddCount_loglog_sharp (k : ℕ) (hk : 2 ≤ k) (hc : 1 < oddCount k) :
    log (log (oddCount k : ℝ)) ≤ (k : ℝ)*log 2 + log (log (k : ℝ)) := by
  have hkr : 1 < (k : ℝ) := by exact_mod_cast hk
  have hcr : 1 < (oddCount k : ℝ) := by exact_mod_cast hc
  calc
    _ ≤ log ((2 : ℝ)^k * log (k : ℝ)) := by
      apply log_le_log (log_pos hcr)
      have h := log_le_log (by linarith : (0 : ℝ) < oddCount k) (oddCount_cast_upper k (by omega))
      simpa only [log_pow, Nat.cast_pow, Nat.cast_ofNat] using h
    _ = _ := by rw [log_mul (by positivity) (ne_of_gt (log_pos hkr)), log_pow]

/-- A uniform double exponential upper bound with the manuscript's constant 2. -/
theorem oddCount_exp_upper_two (k : ℕ) (hk : 1 ≤ k) :
    (oddCount k : ℝ) ≤ exp (exp (2*(k : ℝ))) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ht : (2 : ℝ)^k ≤ exp k := calc
    _ ≤ (exp 1)^k := by gcongr; linarith [add_one_le_exp (1:ℝ)]
    _ = _ := by rw [← exp_nat_mul]; simp
  have hl : log (k : ℝ) ≤ exp k := by linarith [log_le_sub_one_of_pos hkr, add_one_le_exp (k:ℝ)]
  calc
    (oddCount k : ℝ) ≤ (k : ℝ)^(2^k : ℕ) := oddCount_cast_upper k hk
    _ = exp (((2^k : ℕ) : ℝ)*log (k : ℝ)) := by rw [exp_nat_mul, exp_log hkr]
    _ = exp ((2 : ℝ)^k*log (k : ℝ)) := by push_cast; rfl
    _ ≤ exp (exp (2*(k : ℝ))) := by
      apply exp_le_exp.mpr
      calc
        _ ≤ (exp k)*(exp k) := mul_le_mul ht hl (log_nonneg (by exact_mod_cast hk)) (exp_pos _).le
        _ = _ := by rw [← exp_add]; congr 1; ring

/-- On lengths where the double logarithm is defined, its upper slope is at most two. -/
theorem oddCount_loglog_upper_two (k : ℕ) (hk : 1 ≤ k) (hc : 1 < oddCount k) :
    log (log (oddCount k : ℝ)) ≤ 2*(k : ℝ) := by
  have hcr : 1 < (oddCount k : ℝ) := by exact_mod_cast hc
  apply (log_le_iff_le_exp (log_pos hcr)).mpr
  exact (log_le_iff_le_exp (by linarith : (0 : ℝ) < oddCount k)).mpr (oddCount_exp_upper_two k hk)

end OddEgyptian
