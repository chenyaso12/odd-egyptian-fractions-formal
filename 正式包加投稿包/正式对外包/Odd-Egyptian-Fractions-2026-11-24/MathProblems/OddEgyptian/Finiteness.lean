module

public import MathProblems.OddEgyptian.Definitions
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace OddEgyptian

/-- Removing the least denominator squares the budget K*b for the remaining denominators. -/
theorem denominator_bound (j K : ℕ) (hK : 0 < K) (s : Finset ℕ) (b : ℕ) (a : ℤ)
    (hb : 0 < b) (hKcard : s.card ≤ K) (hj : s.card ≤ j)
    (hp : ∀ d ∈ s, 0 < d) (hs : ∑ d ∈ s, (1 : ℚ) / d = (a : ℚ) / b) :
    ∀ x ∈ s, x ≤ (K*b)^(2^j) := by
  induction j generalizing s b a with
  | zero =>
    have he : s = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [he]
  | succ j ih =>
    intro x hx
    let n := s.min' ⟨x, hx⟩
    have hn : n ∈ s := s.min'_mem _
    have hnpos := hp n hn
    have hmin (y) (hy : y ∈ s) : n ≤ y := s.min'_le y hy
    have habpos : 0 < (a : ℚ) / b := by
      rw [← hs]
      exact Finset.sum_pos (fun y hy => by have := hp y hy; positivity) ⟨n, hn⟩
    have ha : (1 : ℤ) ≤ a := by
      have : (0 : ℚ) < a := (div_pos_iff_of_pos_right (by exact_mod_cast hb)).mp habpos
      exact Int.add_one_le_iff.mpr (by exact_mod_cast this)
    have hsum : (a : ℚ) / b ≤ (K : ℚ) / n := calc
      _ = ∑ d ∈ s, (1 : ℚ)/d := hs.symm
      _ ≤ ∑ _d ∈ s, (1 : ℚ)/n := Finset.sum_le_sum fun y hy =>
        one_div_le_one_div_of_le (by exact_mod_cast hnpos) (by exact_mod_cast hmin y hy)
      _ = (s.card : ℚ)/n := by simp [div_eq_mul_inv]
      _ ≤ _ := by gcongr
    have hnb : n ≤ K*b := by
      have hprod := (div_le_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hnpos)).mp hsum
      have hprod' : (1 : ℚ) * n ≤ (a : ℚ) * n :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast ha) (by positivity)
      exact_mod_cast (show (n : ℚ) ≤ (K : ℚ) * b by linarith)
    have hbase : 0 < K*b := Nat.mul_pos hK hb
    by_cases hxn : x = n
    · rw [hxn]
      exact hnb.trans (Nat.le_self_pow (by positivity) _)
    · let t := s.erase n
      have ht : ∑ d ∈ t, (1 : ℚ)/d = ((a*(n:ℤ)-(b:ℤ) : ℤ):ℚ)/(b*n:ℕ) := by
        have h := s.sum_erase_add (fun d : ℕ => (1:ℚ)/d) hn
        change (∑ d ∈ t, (1:ℚ)/d) + 1/n = _ at h
        rw [hs] at h
        push_cast
        rw [eq_sub_of_add_eq h]
        field_simp
      have hrest := ih t (b*n) (a*n-b) (Nat.mul_pos hb hnpos)
        ((Finset.card_le_card (Finset.erase_subset _ _)).trans hKcard)
        (by simp [t, Finset.card_erase_of_mem hn]; omega)
        (fun y hy => hp y (Finset.mem_of_mem_erase hy)) ht x (Finset.mem_erase.mpr ⟨hxn,hx⟩)
      calc
        x ≤ (K*(b*n))^(2^j) := hrest
        _ ≤ ((K*b)^2)^(2^j) := by
          apply Nat.pow_le_pow_left
          calc
            K*(b*n) = (K*b)*n := (Nat.mul_assoc ..).symm
            _ ≤ (K*b)*(K*b) := Nat.mul_le_mul_left _ hnb
            _ = _ := (sq _).symm
        _ = (K*b)^(2^(j+1)) := by rw [← pow_mul, pow_succ]; congr 1; omega

def height (k : ℕ) : ℕ := (k+1)^(2^k)

theorem solution_mem_universe {k : ℕ} (x : Solutions k) :
    x.1 ∈ (Finset.range (height k + 1)).powersetCard k := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_,x.2.2⟩
  intro n hn
  apply Finset.mem_range.mpr
  have h := denominator_bound k (k+1) (by omega) x.1 1 1 (by decide) (by rw [x.2.2]; omega)
    x.2.2.le (fun d hd => by have := (x.2.1.1 d hd).1; omega) (by simpa using x.2.1.2) n hn
  simpa [height, Nat.lt_succ_iff] using h

private def boundedSolution {k : ℕ} (x : Solutions k) :
    ↥((Finset.range (height k + 1)).powersetCard k) := ⟨x.1, solution_mem_universe x⟩

instance solutionsFinite (k : ℕ) : Finite (Solutions k) :=
  Finite.of_injective boundedSolution (fun _ _ h => Subtype.ext (by simpa only [boundedSolution, Subtype.mk.injEq] using h))

theorem finitenessTarget : FinitenessTarget := fun _ => inferInstance

theorem oddCount_le_pow (k : ℕ) : oddCount k ≤ (height k + 1)^k := by
  calc
    oddCount k ≤ Nat.card ↥((Finset.range (height k + 1)).powersetCard k) :=
      Nat.card_le_card_of_injective boundedSolution (fun _ _ h => Subtype.ext (by simpa only [boundedSolution, Subtype.mk.injEq] using h))
    _ = (height k + 1).choose k := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard, Finset.card_range]
    _ ≤ _ := Nat.choose_le_pow _ _

end OddEgyptian
