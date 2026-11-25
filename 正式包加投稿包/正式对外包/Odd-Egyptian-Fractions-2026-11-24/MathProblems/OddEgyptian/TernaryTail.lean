module

public import MathProblems.OddEgyptian.Layers
public import MathProblems.OddEgyptian.TernaryDigits

import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Finset
open scoped BigOperators

private def ternaryLabel (L : ℕ) : (Bool × Fin L) ↪ Bool × ℕ where
  toFun t := (t.1, L - t.2.val)
  inj' := by
    rintro ⟨p, i⟩ ⟨q, j⟩ eq
    have hp : p = q := congrArg Prod.fst eq
    have hij : L - i.val = L - j.val := congrArg Prod.snd eq
    have hfin : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    simp [hp, hfin]

/-- For denominators above the digit bound, each base-three digit can be scaled
directly. The finite digit witnesses are already sets; there is no template assumption. -/
private theorem ternaryProperLarge (R : ℕ)
    (digits : ∀ m : ℕ, m < 3 → ∃ S : Finset ℕ, (∑ c ∈ S, (1 : ℚ) / (c : ℚ)) = m ∧
      ∀ c ∈ S, Odd c ∧ ¬ 3 ∣ c ∧ c ≤ R)
    (a b : ℕ) (ho : Odd b) (h3 : ¬ 3 ∣ b) (hR : R < b) (hlt : a < b) :
    ∃ s : Finset ℕ, Represents ((a : ℚ) / b) s := by
  classical
  let L := b
  have hcover : b ≤ 3 ^ L := (Nat.lt_pow_self (by decide : 1 < 3)).le
  obtain ⟨d, e, _, _, hEq⟩ := euclidean_digit_layers (a := a) (b := b) (B := 3)
    (N := 1) (L := L) ho.pos (by decide) (by decide) (by simpa using hlt) hcover
  let m (t : Bool × Fin L) := baseDigit 3 (if t.1 then e else d) t.2.val
  choose cs hsum hcs using fun t : Bool × Fin L => digits (m t) (baseDigit_lt (by decide : 0 < 3) _ _)
  let scale (t : Bool × Fin L) := 3 ^ (L - t.2.val) * (if t.1 then b else 1)
  let parts (t : Bool × Fin L) := (cs t).image fun c => scale t * c
  have factor (t : Bool × Fin L) (c : ℕ) :
      scale t * c = layerDen b 3 (ternaryLabel L t) c := by
    dsimp [scale, layerDen, ternaryLabel]
    exact mul_assoc _ _ _
  have hodd (t : Bool × Fin L) : Odd (scale t) := by
    dsimp [scale]
    apply (show Odd 3 by decide).pow.mul
    split
    · exact ho
    · decide
  have hlarge (t : Bool × Fin L) : 3 ≤ scale t := by
    have ht : 1 ≤ L - t.2.val := by have := t.2.isLt; omega
    have hp : 3 ^ 1 ≤ 3 ^ (L - t.2.val) := Nat.pow_le_pow_right (by decide) ht
    have hv : 1 ≤ (if t.1 then b else 1) := by split <;> first | exact ho.pos | decide
    have hp' := Nat.mul_le_mul_left (3 ^ (L - t.2.val)) hv
    simp only [pow_one, mul_one] at hp hp'
    exact hp.trans hp'
  have disj : (↑(Finset.univ : Finset (Bool × Fin L)) : Set (Bool × Fin L)).PairwiseDisjoint parts := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    obtain ⟨c, hc, hxc⟩ := Finset.mem_image.mp hi
    obtain ⟨f, hf, hxf⟩ := Finset.mem_image.mp hj
    obtain ⟨hoc, h3c, hcR⟩ := hcs i c hc
    obtain ⟨hof, h3f, hfR⟩ := hcs j f hf
    have eq := (factor i c).symm.trans ((hxc.trans hxf.symm).trans (factor j f))
    exact hij ((ternaryLabel L).injective
      (layer_tag_unique (by decide : Nat.Prime 3) h3 h3c h3f hoc.pos hof.pos
        (hcR.trans_lt hR) (hfR.trans_lt hR) eq))
  have partSum (t : Bool × Fin L) :
      (∑ x ∈ parts t, (1 : ℚ) / (x : ℚ)) = (m t : ℚ) / (scale t : ℚ) := by
    change (∑ x ∈ (cs t).image (fun c => scale t * c), (1 : ℚ) / (x : ℚ)) = _
    rw [Finset.sum_image]
    · rw [← hsum t, Finset.sum_div]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, one_mul]
    · intro c _ f _ eq
      exact Nat.eq_of_mul_eq_mul_left (hodd t).pos eq
  refine ⟨Finset.univ.biUnion parts, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, _, hxt⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hxt
    have hoc := (hcs t c hc).1
    have hb : scale t ≤ scale t * c := by simpa using Nat.mul_le_mul_left (scale t) hoc.pos
    exact ⟨by have := hlarge t; omega, (hodd t).mul hoc⟩
  · rw [Finset.sum_biUnion disj]
    simp_rw [partSum]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, hEq]
    simp only [m, scale, ↓reduceIte, Bool.false_eq_true, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one, mul_one, one_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => (baseDigit 3 e i : ℚ) /
      (3 ^ (L - i) * (b : ℚ))) L,
      Fin.sum_univ_eq_sum_range (fun i => (baseDigit 3 d i : ℚ) / (3 ^ (L - i))) L]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]

/-- Every proper odd-denominator rational whose denominator is coprime to three
has a distinct odd expansion. A common odd multiplier removes the temporary height bound. -/
theorem ternary_proper (a b : ℕ) (ho : Odd b) (h3 : ¬ 3 ∣ b) (hlt : a < b) :
    ∃ s : Finset ℕ, Represents ((a : ℚ) / b) s := by
  obtain ⟨R, digits⟩ := ternaryDigitWitness
  let t := 6 * R + 1
  have htOdd : Odd t := ⟨3 * R, by dsimp [t]; omega⟩
  have ht3 : ¬ 3 ∣ t := by dsimp [t]; omega
  have hrr : R < t := by dsimp [t]; omega
  have hR : R < b * t := hrr.trans_le (by simpa using Nat.mul_le_mul_right t ho.pos)
  have hBt : ¬ 3 ∣ b * t := fun H => ((show Nat.Prime 3 by decide).dvd_mul.mp H).elim h3 ht3
  obtain ⟨s, rep⟩ := ternaryProperLarge R digits (a * t) (b * t) (ho.mul htOdd) hBt hR
    (Nat.mul_lt_mul_of_pos_right hlt htOdd.pos)
  have ht : (t : ℚ) ≠ 0 := by exact_mod_cast htOdd.pos.ne'
  refine ⟨s, ?_⟩
  simpa only [Nat.cast_mul, mul_div_mul_right _ _ ht] using rep

end OddEgyptian
