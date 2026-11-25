module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace OddEgyptian

/-- The middle denominator in the three-term odd Egyptian fraction split. -/
def splitU (u : ℕ) : ℕ :=
  if u % 4 = 1 then ((u + 1) / 2) * (u + 2) else u * ((u + 3) / 2)

/-- The largest denominator in the three-term odd Egyptian fraction split. -/
def splitV (u : ℕ) : ℕ :=
  if u % 4 = 1 then u * splitU u else (u + 2) * splitU u

def splitTriple (d u : ℕ) : Finset ℕ :=
  {d * (u + 2), d * splitU u, d * splitV u}

private theorem odd_cases {u : ℕ} (hu : Odd u) :
    ∃ t : ℕ, u = 4 * t + 1 ∨ u = 4 * t + 3 := by
  obtain ⟨k, hk⟩ := hu
  exact ⟨u / 4, by omega⟩

@[simp] theorem splitU_one (t : ℕ) :
    splitU (4 * t + 1) = (2 * t + 1) * (4 * t + 3) := by
  have hm : (4 * t + 1) % 4 = 1 := by omega
  have hh : (4 * t + 1 + 1) / 2 = 2 * t + 1 := by omega
  simp [splitU, hm, hh, Nat.add_assoc]

@[simp] theorem splitU_three (t : ℕ) :
    splitU (4 * t + 3) = (4 * t + 3) * (2 * t + 3) := by
  have hh : (4 * t + 3 + 3) / 2 = 2 * t + 3 := by omega
  simp [splitU, hh]

@[simp] theorem splitV_one (t : ℕ) :
    splitV (4 * t + 1) = (4 * t + 1) * ((2 * t + 1) * (4 * t + 3)) := by
  have hm : (4 * t + 1) % 4 = 1 := by omega
  simp [splitV, hm]

@[simp] theorem splitV_three (t : ℕ) :
    splitV (4 * t + 3) = (4 * t + 5) * ((4 * t + 3) * (2 * t + 3)) := by
  simp [splitV, Nat.add_assoc]

theorem split_order {u : ℕ} (hu : Odd u) (hu3 : 3 ≤ u) :
    u < u + 2 ∧ u + 2 < splitU u ∧ splitU u < splitV u := by
  obtain ⟨t, rfl | rfl⟩ := odd_cases hu
  · have ht : 1 ≤ t := by omega
    simp only [splitU_one, splitV_one]
    refine ⟨by omega, ?_, ?_⟩ <;> nlinarith [Nat.zero_le (t * t), Nat.zero_le (t * t * t)]
  · simp only [splitU_three, splitV_three]
    refine ⟨by omega, ?_, ?_⟩ <;> nlinarith [Nat.zero_le (t * t), Nat.zero_le (t * t * t)]

theorem split_scaled_order {d u : ℕ} (hd : 0 < d) (hu : Odd u) (hu3 : 3 ≤ u) :
    d*u < d*(u+2) ∧ d*(u+2) < d*splitU u ∧ d*splitU u < d*splitV u := by
  obtain ⟨h₁, h₂, h₃⟩ := split_order hu hu3
  exact ⟨Nat.mul_lt_mul_of_pos_left h₁ hd, Nat.mul_lt_mul_of_pos_left h₂ hd,
    Nat.mul_lt_mul_of_pos_left h₃ hd⟩

theorem splitTriple_card {d u : ℕ} (hd : 0 < d) (hu : Odd u) (hu3 : 3 ≤ u) :
    (splitTriple d u).card = 3 := by
  obtain ⟨_, h₁, h₂⟩ := split_scaled_order hd hu hu3
  simp [splitTriple, h₁.ne, h₂.ne, (h₁.trans h₂).ne]

theorem splitTriple_first (d u : ℕ) : d*(u+2) ∈ splitTriple d u := by simp [splitTriple]

theorem splitTriple_lower {d u x : ℕ} (hd : 0 < d) (hu : Odd u) (hu3 : 3 ≤ u)
    (hx : x ∈ splitTriple d u) : d*(u+2) ≤ x := by
  obtain ⟨_, h₁, h₂⟩ := split_scaled_order hd hu hu3
  simp only [splitTriple, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> omega

theorem splitTriple_odd {d u : ℕ} (hd : Odd d) (hu : Odd u) {x : ℕ}
    (hx : x ∈ splitTriple d u) : Odd x := by
  obtain ⟨t, rfl | rfl⟩ := odd_cases hu <;>
    simp only [splitTriple, Finset.mem_insert, Finset.mem_singleton, splitU_one, splitV_one,
      splitU_three, splitV_three] at hx <;>
    rcases hx with rfl | rfl | rfl <;> apply hd.mul
  all_goals repeat' apply Odd.mul
  all_goals rw [Nat.odd_iff]; omega

private theorem split_reciprocal {u : ℕ} (hu : Odd u) (hu3 : 3 ≤ u) :
    (1 : ℚ) / (u + 2) + 1 / (splitU u : ℚ) + 1 / (splitV u : ℚ) = 1 / (u : ℚ) := by
  obtain ⟨t, rfl | rfl⟩ := odd_cases hu <;>
    simp only [splitU_one, splitV_one, splitU_three, splitV_three, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat] <;>
    field_simp <;> ring

theorem splitTriple_sum {d u : ℕ} (hd : 0 < d) (hu : Odd u) (hu3 : 3 ≤ u) :
    ∑ x ∈ splitTriple d u, (1 : ℚ) / (x : ℚ) = 1 / ((d * u : ℕ) : ℚ) := by
  obtain ⟨_, h₁, h₂⟩ := split_scaled_order hd hu hu3
  have h := split_reciprocal hu hu3
  simp [splitTriple, h₁.ne, h₂.ne, (h₁.trans h₂).ne, Nat.cast_add, Nat.cast_mul,
    mul_inv_rev, ← add_mul] at *
  left
  simpa [add_assoc] using h

/-- For a fixed parent denominator the new minimum uniquely identifies the divisor. -/
theorem splitTriple_injective {d e u v : ℕ} (hd : 0 < d) (he : 0 < e)
    (hu : Odd u) (hv : Odd v) (hu3 : 3 ≤ u) (hv3 : 3 ≤ v) (hn : d*u = e*v)
    (hs : splitTriple d u = splitTriple e v) : d = e := by
  have ha := splitTriple_lower hd hu hu3 (hs ▸ splitTriple_first e v)
  have hb := splitTriple_lower he hv hv3 (hs ▸ splitTriple_first d u)
  nlinarith

private theorem splitU_bounds {u : ℕ} (hu : Odd u) (hu3 : 3 ≤ u) :
    u*(u+3) ≤ 2*splitU u ∧ 2*splitU u < u*(u+5) := by
  obtain ⟨t, rfl | rfl⟩ := odd_cases hu <;> simp only [splitU_one, splitU_three] <;>
    constructor <;> nlinarith [Nat.zero_le (t*t)]

private theorem splitV_bounds {u : ℕ} (hu : Odd u) :
    u*((u+1)*(u+2)) ≤ 2*splitV u ∧ 2*splitV u ≤ u*((u+2)*(u+3)) := by
  obtain ⟨t, rfl | rfl⟩ := odd_cases hu <;> simp only [splitV_one, splitV_three] <;>
    constructor <;> nlinarith [Nat.zero_le (t*t), Nat.zero_le (t*t*t)]

theorem self_dvd_splitV {u : ℕ} (hu : Odd u) : u ∣ splitV u := by
  obtain ⟨t, rfl | rfl⟩ := odd_cases hu
  · rw [splitV_one]
    exact dvd_mul_right ..
  · rw [splitV_three]
    exact dvd_mul_of_dvd_right (dvd_mul_right ..) _

/-- Increasing the odd parent strictly increases its new maximum. -/
theorem splitV_lt_of_odd {u v : ℕ} (hu : Odd u) (hv : Odd v) (h : u < v) :
    splitV u < splitV v := by
  have hprod : u * ((u+2)*(u+3)) < v * ((v+1)*(v+2)) := calc
    _ < v * ((u+2)*(u+3)) := Nat.mul_lt_mul_of_pos_right h (by positivity)
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have := ((splitV_bounds hu).2.trans_lt hprod).trans_le (splitV_bounds hv).1
  omega

private theorem odd_gap {u v : ℕ} (hu : Odd u) (hv : Odd v) (hlt : u < v) : u+2 ≤ v := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  omega

/-- With a fixed parent, the middle coordinate strictly increases with the odd quotient. -/
theorem split_middle_strict {d e u v : ℕ} (hd : 0 < d)
    (hu : Odd u) (hv : Odd v) (hu3 : 3 ≤ u) (hv3 : 3 ≤ v)
    (hn : d*u = e*v) (hlt : u < v) : d*splitU u < e*splitU v := by
  have hgap := odd_gap hu hv hlt
  have h : 2*(d*splitU u) < 2*(e*splitU v) := calc
    2*(d*splitU u) = d*(2*splitU u) := by ring
    _ < d*(u*(u+5)) := Nat.mul_lt_mul_of_pos_left (splitU_bounds hu hu3).2 hd
    _ = (e*v)*(u+5) := by rw [← hn]; ring
    _ ≤ (e*v)*(v+3) := Nat.mul_le_mul_left _ (by omega)
    _ = e*(v*(v+3)) := by ring
    _ ≤ e*(2*splitU v) := Nat.mul_le_mul_left _ (splitU_bounds hv hv3).1
    _ = 2*(e*splitU v) := by ring
  omega

/-- With a fixed parent, the largest coordinate strictly increases with the odd quotient. -/
theorem split_largest_strict {d e u v : ℕ} (he : 0 < e)
    (hu : Odd u) (hv : Odd v) (hn : d*u = e*v) (hlt : u < v) :
    d*splitV u < e*splitV v := by
  have hgap := odd_gap hu hv hlt
  have hp : (u+2)*(u+3) < (v+1)*(v+2) := calc
    (u+2)*(u+3) < (v+1)*(u+3) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    _ ≤ (v+1)*(v+2) := Nat.mul_le_mul_left _ (by omega)
  have h : 2*(d*splitV u) < 2*(e*splitV v) := calc
    2*(d*splitV u) = d*(2*splitV u) := by ring
    _ ≤ d*(u*((u+2)*(u+3))) := Nat.mul_le_mul_left _ (splitV_bounds hu).2
    _ = (e*v)*((u+2)*(u+3)) := by rw [← hn]; ring
    _ < (e*v)*((v+1)*(v+2)) := Nat.mul_lt_mul_of_pos_left hp (Nat.mul_pos he (by omega))
    _ = e*(v*((v+1)*(v+2))) := by ring
    _ ≤ e*(2*splitV v) := Nat.mul_le_mul_left _ (splitV_bounds hv).1
    _ = 2*(e*splitV v) := by ring
  omega

/-- A collision in the smallest coordinate determines the divisor. -/
theorem split_first_injective {d e u v : ℕ} (hn : d*u = e*v)
    (h : d*(u+2) = e*(v+2)) : d = e := by nlinarith

theorem split_middle_injective {d e u v : ℕ} (hd : 0 < d) (he : 0 < e)
    (hu : Odd u) (hv : Odd v) (hu3 : 3 ≤ u) (hv3 : 3 ≤ v)
    (hn : d*u = e*v) (h : d*splitU u = e*splitU v) : d = e := by
  have hs : u = v := by
    rcases lt_trichotomy u v with hlt | hEq | hgt
    · exact False.elim ((split_middle_strict hd hu hv hu3 hv3 hn hlt).ne h)
    · exact hEq
    · exact False.elim ((split_middle_strict he hv hu hv3 hu3 hn.symm hgt).ne h.symm)
  subst v
  exact Nat.eq_of_mul_eq_mul_right (by omega) hn

theorem split_largest_injective {d e u v : ℕ} (hd : 0 < d) (he : 0 < e)
    (hu : Odd u) (hv : Odd v) (hu3 : 3 ≤ u)
    (hn : d*u = e*v) (h : d*splitV u = e*splitV v) : d = e := by
  have hs : u = v := by
    rcases lt_trichotomy u v with hlt | hEq | hgt
    · exact False.elim ((split_largest_strict he hu hv hn hlt).ne h)
    · exact hEq
    · exact False.elim ((split_largest_strict hd hv hu hn.symm hgt).ne h.symm)
  subst v
  exact Nat.eq_of_mul_eq_mul_right (by omega) hn

/-- The small coordinate and the two large coordinates have disjoint ranges even for
different divisors of the same parent. -/
theorem split_first_lt_middle {d e u v : ℕ} (hd : 0 < d) (hv : Odd v)
    (hu3 : 3 ≤ u) (hv3 : 3 ≤ v) (hn : d*u = e*v) : d*(u+2) < e*splitU v := by
  have hsmall : d*(u+2) < 3*(d*u) := by
    calc d*(u+2) < d*(3*u) := Nat.mul_lt_mul_of_pos_left (by omega) hd
         _ = 3*(d*u) := by ring
  have hlarge : 6*(d*u) ≤ 2*(e*splitU v) := calc
    6*(d*u) = (e*v)*6 := by rw [hn]; ring
    _ ≤ (e*v)*(v+3) := Nat.mul_le_mul_left _ (by omega)
    _ = e*(v*(v+3)) := by ring
    _ ≤ e*(2*splitU v) := Nat.mul_le_mul_left _ (splitU_bounds hv hv3).1
    _ = 2*(e*splitU v) := by ring
  omega

/-- Arithmetic data for using a proper divisor of an odd number as a split parameter. -/
theorem split_divisor_data {n d : ℕ} (hn : Odd n) (hd : d ∈ n.properDivisors) :
    0 < d ∧ Odd d ∧ Odd (n/d) ∧ 3 ≤ n/d ∧ d*(n/d) = n := by
  obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
  have heq := Nat.mul_div_cancel' hdvd
  have ho : Odd (d * (n / d)) := by rw [heq]; exact hn
  obtain ⟨ho₁, ho₂⟩ := Nat.odd_mul.mp ho
  have hquot : 1 < n / d := by
    by_contra! h
    have hle := Nat.mul_le_mul_left d h
    rw [heq, Nat.mul_one] at hle
    omega
  have hmod := Nat.odd_iff.mp ho₂
  exact ⟨Nat.pos_of_mem_properDivisors hd, ho₁, ho₂, by omega, heq⟩

private theorem split_coordinate_ranges {d u : ℕ} (hd : 0 < d) (hu : Odd u) (hu3 : 3 ≤ u) :
    d*(u+2) < 3*(d*u) ∧ 3*(d*u) ≤ d*splitU u := by
  constructor
  · calc d*(u+2) < d*(3*u) := Nat.mul_lt_mul_of_pos_left (by omega) hd
         _ = 3*(d*u) := by ring
  · have h : 6*(d*u) ≤ 2*(d*splitU u) := calc
      6*(d*u) = (d*u)*6 := by ring
      _ ≤ (d*u)*(u+3) := Nat.mul_le_mul_left _ (by omega)
      _ = d*(u*(u+3)) := by ring
      _ ≤ d*(2*splitU u) := Nat.mul_le_mul_left _ (splitU_bounds hu hu3).1
      _ = 2*(d*splitU u) := by ring
    omega

/-- Any fixed old denominator forbids at most two choices of a proper divisor. -/
theorem split_fiber_le_two {n : ℕ} (hn : Odd n) (_hn3 : 3 ≤ n) (x : ℕ) :
    (n.properDivisors.filter fun d => x ∈ splitTriple d (n/d)).card ≤ 2 := by
  let D := n.properDivisors
  let A (d : ℕ) := d*(n/d + 2)
  let B (d : ℕ) := d*splitU (n/d)
  let C (d : ℕ) := d*splitV (n/d)
  have singleton (f : ℕ → ℕ)
      (hf : ∀ d ∈ D, ∀ e ∈ D, f d = f e → d = e) :
      (D.filter fun d => x = f d).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro d e hd he
    obtain ⟨hd, h₁⟩ := Finset.mem_filter.mp hd
    obtain ⟨he, h₂⟩ := Finset.mem_filter.mp he
    exact hf d hd e he (h₁.symm.trans h₂)
  have hA := singleton A (by
    intro d hd e he h
    obtain ⟨_, _, _, _, h₁⟩ := split_divisor_data hn hd
    obtain ⟨_, _, _, _, h₂⟩ := split_divisor_data hn he
    exact split_first_injective (h₁.trans h₂.symm) h)
  have hB := singleton B (by
    intro d hd e he h
    obtain ⟨hd', _, hu, hu3, h₁⟩ := split_divisor_data hn hd
    obtain ⟨he', _, hv, hv3, h₂⟩ := split_divisor_data hn he
    exact split_middle_injective hd' he' hu hv hu3 hv3 (h₁.trans h₂.symm) h)
  have hC := singleton C (by
    intro d hd e he h
    obtain ⟨hd', _, hu, hu3, h₁⟩ := split_divisor_data hn hd
    obtain ⟨he', _, hv, _, h₂⟩ := split_divisor_data hn he
    exact split_largest_injective hd' he' hu hv hu3 (h₁.trans h₂.symm) h)
  have ranges {d : ℕ} (hd : d ∈ D) : A d < 3*n ∧ 3*n ≤ B d ∧ B d < C d := by
    obtain ⟨hd', _, hu, hu3, h₁⟩ := split_divisor_data hn hd
    obtain ⟨ha, hb⟩ := split_coordinate_ranges hd' hu hu3
    rw [h₁] at ha hb
    exact ⟨ha, hb, (split_scaled_order hd' hu hu3).2.2⟩
  have cases {d : ℕ} (hx : x ∈ splitTriple d (n/d)) : x = A d ∨ x = B d ∨ x = C d := by
    simpa only [splitTriple, Finset.mem_insert, Finset.mem_singleton] using hx
  by_cases hsmall : x < 3*n
  · suffices hsub : (D.filter fun d => x ∈ splitTriple d (n/d)) ⊆
        D.filter (fun d => x = A d) from
      (Finset.card_le_card hsub).trans (by omega)
    intro d hd
    obtain ⟨hd, hx⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hd, by
      obtain ⟨_, hb, hc⟩ := ranges hd
      rcases cases hx with h | h | h <;> omega⟩
  · suffices hsub : (D.filter fun d => x ∈ splitTriple d (n/d)) ⊆
        (D.filter fun d => x = B d) ∪ (D.filter fun d => x = C d) by
      have hunion := Finset.card_union_le (D.filter fun d => x = B d) (D.filter fun d => x = C d)
      exact (Finset.card_le_card hsub).trans (by omega)
    intro d hd
    obtain ⟨hd, hx⟩ := Finset.mem_filter.mp hd
    apply Finset.mem_union.mpr
    rcases cases hx with h | h | h
    · have ha := (ranges hd).1
      omega
    · exact Or.inl (Finset.mem_filter.mpr ⟨hd, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hd, h⟩)

end OddEgyptian

