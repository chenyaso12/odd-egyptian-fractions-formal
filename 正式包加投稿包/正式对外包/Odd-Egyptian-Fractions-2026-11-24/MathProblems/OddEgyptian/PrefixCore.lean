module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace OddEgyptian

theorem exists_odd_prefix_step (a b p : ℕ) (ha : 0 < a) :
    ∃ q : ℕ, Odd q ∧ p < q ∧ b ≤ a*q := by
  let q := 2*(b+p+1)+1
  have hq : q ≤ a*q := by simpa using (Nat.mul_le_mul_right q (show 1 ≤ a by omega))
  exact ⟨q, ⟨b+p+1, by simp [q, two_mul]⟩, by dsimp [q]; omega, (by dsimp [q]; omega : b ≤ q) |>.trans hq⟩

/-- Smallest permissible odd denominator after the preceding denominator. -/
noncomputable def prefixDenom (a b p : ℕ) (ha : 0 < a) : ℕ :=
  Nat.find (exists_odd_prefix_step a b p ha)

theorem prefixDenom_spec (a b p : ℕ) (ha : 0 < a) :
    Odd (prefixDenom a b p ha) ∧ p < prefixDenom a b p ha ∧ b ≤ a*(prefixDenom a b p ha) :=
  Nat.find_spec (exists_odd_prefix_step a b p ha)

theorem prefixDenom_le {a b p q : ℕ} (ha : 0 < a)
    (hq : Odd q) (hp : p < q) (hr : b ≤ a*q) : prefixDenom a b p ha ≤ q :=
  Nat.find_min' (exists_odd_prefix_step a b p ha) ⟨hq, hp, hr⟩

theorem prefixDenom_le_den {a b p : ℕ} (ha : 0 < a) (hb : Odd b) (hp : p < b) :
    prefixDenom a b p ha ≤ b :=
  prefixDenom_le ha hb hp (by simpa using Nat.mul_le_mul_right b (show 1 ≤ a by omega))

/-- The integer pair is deliberately left unreduced. -/
theorem prefix_step_identity {a b q : ℕ} (hb : 0 < b) (hq : 0 < q) (hle : b ≤ a*q) :
    (a : ℚ)/b = 1/(q : ℚ) + ((a*q-b : ℕ) : ℚ)/(b*q : ℕ) := by
  rw [Nat.cast_sub hle]
  push_cast
  field_simp
  ring

theorem prefix_den_next_lt {a b p : ℕ} (ha : 0 < a) (hb : Odd b) (hp : p < b)
    {B : ℕ} (hlt : b < B^3) : b * prefixDenom a b p ha < B^6 := by
  have hq := prefixDenom_le_den ha hb hp
  calc b*prefixDenom a b p ha ≤ b*b := Nat.mul_le_mul_left _ hq
       _ < (B^3)*(B^3) := Nat.mul_self_lt_mul_self hlt
       _ = B^6 := by ring

/-- For ordinary steps, the previous odd number was too small. This gives simultaneously
the strict doubling bound on the unreduced numerator and the gap to the new prefix. -/
theorem prefix_ordinary_estimates {a b p : ℕ} (ha : 0 < a)
    (hprev : p+2 < prefixDenom a b p ha) (hq5 : 5 ≤ prefixDenom a b p ha) :
    let q := prefixDenom a b p ha
    a*q-b < 2*a ∧ (a*q-b)*(q-2) < 2*b ∧ (a*q-b)*q < b*q := by
  let q := prefixDenom a b p ha
  have hs : Odd q ∧ p < q ∧ b ≤ a*q := prefixDenom_spec .. 
  have hqp : q-2+2 = q := by change 5 ≤ q at hq5; omega
  have ho : Odd (q-2) := by
    rw [Nat.odd_iff]
    obtain h := Nat.odd_iff.mp hs.1
    omega
  have hn : a*(q-2) < b := by
    by_contra! h
    have := prefixDenom_le (p := p) ha ho (by change p+2<q at hprev; omega) h
    change q ≤ q-2 at this
    omega
  have hsub : a*q-b+b = a*q := Nat.sub_add_cancel hs.2.2
  change 5 ≤ q at hq5
  change a*q-b < 2*a ∧ (a*q-b)*(q-2) < 2*b ∧ (a*q-b)*q < b*q
  have ha' : a*q-b < 2*a := by nlinarith [congrArg (a*·) hqp]
  have hgap : (a*q-b)*(q-2) < 2*b := by
    calc (a*q-b)*(q-2) ≤ (2*a)*(q-2) := Nat.mul_le_mul_right _ ha'.le
         _ < 2*b := by nlinarith
  have hrem : a*q-b < b := by
    have hh : 2*(a*q-b) ≤ (a*q-b)*(q-2) := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (a*q-b) (show 2 ≤ q-2 by omega)
    omega
  exact ⟨ha', hgap, Nat.mul_lt_mul_of_pos_right hrem (by omega)⟩

end OddEgyptian

