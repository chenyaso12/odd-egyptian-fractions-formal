module

public import MathProblems.OddEgyptian.PrimeMarker
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian.PrefixPair

/-- The two variable odd denominators above the fixed third-last entry. -/
theorem lastPair {n q t : ℕ} (hn : 3 ≤ n) (hno : Odd n) (hto : Odd t)
    (hq : q % 4 = 1) (hq1 : 1 < q) (hA : t*q = n*(n+2)) :
    let h := (q+1)/2
    let x := t*h
    let y := (n*(n+2))*h
    n+2 < x ∧ x < y ∧ Odd x ∧ Odd y ∧ n ∣ y ∧
      (1:ℚ)/x + 1/y = 2/(n*(n+2):ℕ) := by
  let h := (q+1)/2
  let A := n*(n+2)
  change n+2 < t*h ∧ t*h < A*h ∧ Odd (t*h) ∧ Odd (A*h) ∧ n ∣ A*h ∧ _
  have h2 : q+1 = 2*h := by dsimp [h]; omega
  have hodd : Odd h := by rw [Nat.odd_iff]; dsimp [h]; omega
  have hpos : 0 < h := hodd.pos
  have tpos : 0 < t := hto.pos
  have h3A : 3*(n+2) ≤ A := Nat.mul_le_mul_right (n+2) hn
  have htx : 2*(t*h) = A+t := by
    change 2*(t*h) = n*(n+2)+t
    rw [← hA, ← Nat.mul_add_one t q, h2]
    ring
  have hy : A*h = (t*h)*q := by
    dsimp [A]
    rw [← hA]; ring
  have hno' : Odd (n+2) := hno.add_even (by decide : Even (2:ℕ))
  refine ⟨by omega, ?_, hto.mul hodd, (hno.mul hno').mul hodd, ?_, ?_⟩
  · rw [hy]
    simpa using Nat.mul_lt_mul_of_pos_left hq1 (Nat.mul_pos tpos hpos)
  · dsimp [A]
    exact dvd_mul_of_dvd_left (dvd_mul_right ..) h
  · change (1:ℚ)/(t*h : ℕ) + 1/(A*h : ℕ) = 2/(A : ℕ)
    have ha : A = t*q := hA.symm
    have hh : (q:ℚ)+1 = 2*(h:ℚ) := by exact_mod_cast h2
    have tn : (t : ℚ) ≠ 0 := by positivity
    have qn : (q : ℚ) ≠ 0 := by positivity
    have hn' : (h : ℚ) ≠ 0 := by positivity
    rw [ha]
    push_cast
    field_simp
    linarith

def pick (n d : ℕ) : ℕ := if d%4 = 1 then d else n*(n+2)/d

def mate (n d : ℕ) : ℕ := if d%4 = 1 then n*(n+2)/d else d

private theorem divisorData {n d : ℕ} (hn : 3 ≤ n) (hd : d ∣ n) (hd1 : 1 < d) :
    d ≤ n ∧ n+2 ≤ n*(n+2)/d ∧ d*(n*(n+2)/d) = n*(n+2) := by
  have hdN : d ≤ n := Nat.le_of_dvd (by omega) hd
  refine ⟨hdN, (Nat.le_div_iff_mul_le (by omega)).2 ?_,
    Nat.mul_div_cancel' (hd.trans (dvd_mul_right n (n+2)))⟩
  simpa [mul_comm] using Nat.mul_le_mul_right (n+2) hdN

private theorem oddMod {j : ℕ} (ho : Odd j) : j%4 = 1 ∨ j%4 = 3 := by
  obtain ⟨a, ha⟩ := ho
  omega

theorem pick_spec {n d : ℕ} (hn : 3 ≤ n) (ho : Odd n) (hd : d ∣ n) (hd1 : 1 < d) :
    pick n d % 4 = 1 ∧ 1 < pick n d ∧ Odd (mate n d) ∧
      mate n d * pick n d = n*(n+2) := by
  obtain ⟨hlo, hhi, heq⟩ := divisorData hn hd hd1
  have hno' : Odd (n+2) := ho.add_even (by decide : Even (2:ℕ))
  have hp : Odd (d*(n*(n+2)/d)) := by rw [heq]; exact ho.mul hno'
  have hdodd := Nat.odd_mul.mp hp
  have hmod : n*(n+2)%4 = 3 := by
    rcases oddMod ho with h | h <;> rw [Nat.mul_mod, Nat.add_mod, h]
  have hpair : ((d%4)*((n*(n+2)/d)%4))%4 = 3 := by
    rw [← Nat.mul_mod, heq, hmod]
  by_cases h : d%4 = 1
  · simp [pick, mate, h, hd1, hdodd.2, mul_comm _ d, heq]
  · have d3 : d%4 = 3 := (oddMod hdodd.1).resolve_left h
    have q1 : (n*(n+2)/d)%4 = 1 := by
      rcases oddMod hdodd.2 with hq | hq
      · exact hq
      · simp [d3,hq] at hpair
    simpa [pick, mate, h] using And.intro q1
      (And.intro (show 1 < n*(n+2)/d by omega) (And.intro hdodd.1 heq))

theorem pick_injective {n d e : ℕ} (hn : 3 ≤ n) (hd : d ∣ n) (he : e ∣ n)
    (hd1 : 1 < d) (he1 : 1 < e) (hs : pick n d = pick n e) : d = e := by
  obtain ⟨hloD, hhiD, hdA⟩ := divisorData hn hd hd1
  obtain ⟨hloE, hhiE, heA⟩ := divisorData hn he he1
  by_cases hm : d%4 = 1 <;> by_cases hm' : e%4 = 1
  all_goals simp only [pick, hm, hm', ite_true, ite_false] at hs
  · exact hs
  · omega
  · omega
  · rw [hs] at hdA
    exact Nat.eq_of_mul_eq_mul_right (by omega) (hdA.trans heA.symm)

def largest (n d : ℕ) : ℕ := n*(n+2)*((pick n d+1)/2)

theorem largest_injective {n d e : ℕ} (hn : 3 ≤ n) (ho : Odd n) (hd : d ∣ n) (he : e ∣ n)
    (hd1 : 1 < d) (he1 : 1 < e) (hs : largest n d = largest n e) : d = e := by
  have h1 := (pick_spec hn ho hd hd1).1
  have h2 := (pick_spec hn ho he he1).1
  have hh := Nat.eq_of_mul_eq_mul_left (show 0 < n*(n+2) by positivity) hs
  exact pick_injective hn hd he hd1 he1 (by omega)

theorem fixedTerm {n : ℕ} (hn : 3 ≤ n) :
    1/(n+2 : ℕ) + 2/(n*(n+2):ℕ) = (1:ℚ)/n := by
  push_cast
  have hn0 : (n:ℚ) ≠ 0 := by positivity
  field_simp


open Finset

def maxima (Q n : ℕ) := (Q.divisors.erase 1).image (largest n)

theorem maxima_card {Q n : ℕ} (hn : 3 ≤ n) (ho : Odd n) (hQ : Q ∣ n) :
    (maxima Q n).card = Q.divisors.card - 1 := by
  have hQ0 : Q ≠ 0 := by rintro rfl; simp_all
  have args {d} (hd : d ∈ Q.divisors.erase 1) : d ∣ n ∧ 1 < d := by
    obtain ⟨hd1, hd⟩ := Finset.mem_erase.mp hd
    exact ⟨(Nat.dvd_of_mem_divisors hd).trans hQ, by have := Nat.pos_of_mem_divisors hd; omega⟩
  rw [maxima, Finset.card_image_of_injOn, Finset.card_erase_of_mem (Nat.one_mem_divisors.mpr hQ0)]
  intro d hd e he eq
  exact largest_injective hn ho (args hd).1 (args he).1 (args hd).2 (args he).2 eq

theorem firstPrimeMaxima_card {r n : ℕ} (hr : 3 ≤ r) (hn : 3 ≤ n) (ho : Odd n)
    (hQ : FirstOddProduct r ∣ n) :
    (maxima (FirstOddProduct r) n).card = 2^r - 1 := by
  rw [maxima_card hn ho hQ, (firstOddProduct_spec r hr).2.2.2]

end OddEgyptian.PrefixPair
