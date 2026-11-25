module

public import MathProblems.OddEgyptian.PrefixCore
public import MathProblems.OddEgyptian.Templates
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Finset
open scoped BigOperators

/-- The small-numerator conclusion S, with an unreduced denominator and an absolute cutoff. -/
def SmallNumeratorTarget : Prop :=
  ∃ bS : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ a b : ℕ, bS ≤ b → 3 ≤ b → Odd b → 0 < a → a^2 ≤ b →
      ∃ s : Finset ℕ, Represents ((a : ℚ)/b) s ∧ (s.card : ℝ) ≤ C*Real.log (Real.log b)

/-- The quantitative prefix conclusion. On nonzero output the incoming fraction minus the
prefix is A/B, small enough to apply S. The last inequality separates every prefix denominator
from any positive-unit-fraction expansion of A/B. -/
def QuantitativePrefixTarget : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ bS : ℕ, ∃ b₀ : ℕ,
    ∀ a b : ℕ, b₀ ≤ b → 3 ≤ b → Odd b → 0 < a → a < b →
      ∃ (p : Finset ℕ) (A B : ℕ),
        Represents ((a : ℚ)/b - (A : ℚ)/B) p ∧
        (p.card : ℝ) ≤ K*(1 + Real.log (Real.log b)) ∧
        (A = 0 ∨
          (0 < A ∧ A^2 ≤ B ∧ bS ≤ B ∧ 3 ≤ B ∧ Odd B ∧ B ≤ b^6 ∧
            ∀ x ∈ p, (A : ℚ)/B < 1/(x : ℚ)))

/-- A strict bound on the entire residual separates every term of every positive tail. -/
theorem prefix_splice {q r : ℚ} {p s : Finset ℕ}
    (hp : Represents (q-r) p) (hs : Represents r s)
    (hgap : ∀ x ∈ p, r < 1/(x : ℚ)) :
    Represents q (p ∪ s) ∧ (p ∪ s).card = p.card + s.card := by
  have hd : Disjoint p s := by
    apply disjoint_left.mpr
    intro x hxp hxs
    have hle : (1 : ℚ)/(x : ℚ) ≤ ∑ z ∈ s, (1 : ℚ)/(z : ℚ) :=
      single_le_sum (f := fun z : ℕ ↦ (1 : ℚ) / (z : ℚ)) (fun z _ ↦ by positivity) hxs
    rw [hs.2] at hle
    exact (hgap x hxp).not_ge hle
  refine ⟨⟨?_, ?_⟩, card_union_of_disjoint hd⟩
  · intro x hx
    rcases mem_union.mp hx with h | h
    · exact hp.1 x h
    · exact hs.1 x h
  · rw [sum_union hd, hp.2, hs.2]
    ring

/-- An integer representation becomes a fractional one by multiplying all denominators by b. -/
theorem prefix_scale {a b : ℕ} {s : Finset ℕ} (hb : 0 < b) (ho : Odd b)
    (hs : Represents (a : ℚ) s) :
    ∃ t : Finset ℕ, Represents ((a : ℚ)/b) t ∧ t.card = s.card := by
  let f : ℕ ↪ ℕ := ⟨(b*·), fun _ _ h ↦ Nat.eq_of_mul_eq_mul_left hb h⟩
  refine ⟨s.map f, ⟨?_, ?_⟩, card_map _⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    obtain ⟨h1, hodd⟩ := hs.1 x hx
    change 1 < b*x ∧ Odd (b*x)
    have hle : x ≤ b*x := by simpa using Nat.mul_le_mul_right x (show 1 ≤ b by omega)
    exact ⟨h1.trans_le hle, ho.mul hodd⟩
  · rw [sum_map]
    change (∑ x ∈ s, (1 : ℚ)/((b*x : ℕ) : ℚ)) = (a : ℚ)/b
    simp only [Nat.cast_mul, one_div, mul_inv_rev, ← sum_mul]
    have h := hs.2
    simp only [one_div] at h
    rw [h, div_eq_mul_inv]

private theorem prefix_bounded_inputs (basis : OddTailBasis) (N : ℕ) :
    ∃ M : ℕ, ∀ a b : ℕ, b < N → 0 < b → Odd b → 0 < a → a < b →
      ∃ s : Finset ℕ, Represents ((a : ℚ)/b) s ∧ s.card ≤ M := by
  classical
  have exists_rep (j : ℕ) : ∃ s : Finset ℕ, Represents ((j+1 : ℕ) : ℚ) s := by
    obtain ⟨s, hs, _⟩ := basis (j+1) (by omega) 1
    exact ⟨s, hs⟩
  choose f hf using exists_rep
  refine ⟨(range N).sup (fun j ↦ (f j).card), ?_⟩
  intro a b hbN hb ho ha hab
  have hs := hf (a-1)
  have heq : a-1+1 = a := by omega
  rw [heq] at hs
  obtain ⟨s, hs, hcard⟩ := prefix_scale hb ho hs
  refine ⟨s, hs, hcard.trans_le ?_⟩
  exact le_sup (f := fun j ↦ (f j).card) (mem_range.mpr (show a-1 < N by omega))

theorem prefix_loglog_nonneg {b : ℕ} (hb : 3 ≤ b) : 0 ≤ Real.log (Real.log b) := by
  apply Real.log_nonneg
  rw [← Real.exp_le_exp, Real.exp_log (by positivity : (0 : ℝ) < b)]
  exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hb)

private theorem prefix_tail_log {b B : ℕ} (hb : 3 ≤ b) (hB : 3 ≤ B) (hmax : B ≤ b^6) :
    Real.log (Real.log B) ≤ Real.log (Real.log b) + Real.log 6 := by
  have hb' : 1 < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
  have hB' : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hlog := Real.log_le_log (by positivity : 0 < (B : ℝ))
    (show (B : ℝ) ≤ (b : ℝ)^6 by exact_mod_cast hmax)
  rw [Real.log_pow] at hlog
  have := Real.log_le_log (Real.log_pos hB') hlog
  simpa [Real.log_mul (by norm_num : (6:ℝ) ≠ 0) (Real.log_pos hb').ne', add_comm] using this

/-- The exact H conclusion follows from S, E4 and the quantitative prefix inequalities. -/
theorem hTarget_of_prefix_and_small (pref : QuantitativePrefixTarget)
    (small : SmallNumeratorTarget) (basis : OddTailBasis) : HTarget := by
  obtain ⟨bS, C, hC, hS⟩ := small
  obtain ⟨K, hK, hp⟩ := pref
  obtain ⟨b₀, hp⟩ := hp bS
  obtain ⟨M, hM⟩ := prefix_bounded_inputs basis b₀
  let L := K + C*(1+Real.log 6) + M
  have hl6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hcoeff : 0 ≤ C*(1+Real.log 6) := mul_nonneg hC.le (by linarith)
  have hLK : K ≤ L := by dsimp [L]; linarith [Nat.cast_nonneg (α := ℝ) M]
  have hLM : (M : ℝ) ≤ L := by dsimp [L]; linarith
  refine ⟨L, hK.trans_le hLK, ?_⟩
  intro a b hb ho ha hab
  have htt := prefix_loglog_nonneg hb
  by_cases hlarge : b₀ ≤ b
  · obtain ⟨p, A, B, hP, hcard, hz | hrest⟩ := hp a b hlarge hb ho ha hab
    · subst A
      exact ⟨p, by simpa using hP, hcard.trans (mul_le_mul_of_nonneg_right hLK (by linarith))⟩
    · obtain ⟨hA, hAB, hBS, hB, hOB, hmax, hgap⟩ := hrest
      obtain ⟨s, hs, hsc⟩ := hS A B hBS hB hOB hA hAB
      obtain ⟨hrep, hsize⟩ := prefix_splice hP hs hgap
      refine ⟨_, hrep, ?_⟩
      rw [hsize, Nat.cast_add]
      have htail := mul_le_mul_of_nonneg_left (prefix_tail_log hb hB hmax) hC.le
      dsimp [L]
      nlinarith [mul_nonneg (mul_nonneg hC.le hl6) htt,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) M) htt]
  · obtain ⟨s, hs, hm⟩ := hM a b (by omega) (by omega) ho ha hab
    refine ⟨s, hs, (by exact_mod_cast hm : (s.card : ℝ) ≤ M) |>.trans ?_⟩
    exact hLM.trans (by nlinarith [mul_nonneg (hK.trans_le hLK).le htt])

end OddEgyptian

