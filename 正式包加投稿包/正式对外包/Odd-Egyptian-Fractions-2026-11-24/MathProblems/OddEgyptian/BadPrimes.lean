module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic

public section

namespace OddEgyptian

private def collisions (s : Finset ℕ) (p : ℕ) : Finset (ℕ × ℕ) :=
  s.offDiag.filter fun (u,v) => u % p = v % p

private theorem collision_lower (s : Finset ℕ) (p L : ℕ)
    (hs : 2*L ≤ s.card) (hL : (s.image (· % p)).card ≤ L) :
    s.card^2 ≤ 2*L*(collisions s p).card := by
  classical
  let f (u : ℕ) := u % p
  let T := s.image f
  let fiber (r : ℕ) := s.filter fun x => f x = r
  have hparts : s.card = ∑ r ∈ T, (fiber r).card := Finset.card_eq_sum_card_image f s
  have hin : ((collisions s p : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).MapsTo
      (fun z => f z.1) T := fun z hz =>
    Finset.mem_image_of_mem f (Finset.mem_offDiag.mp (Finset.mem_filter.mp hz).1).1
  have hpart' : (collisions s p).card = ∑ r ∈ T, (fiber r).offDiag.card := by
    rw [Finset.card_eq_sum_card_fiberwise hin]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    ext z
    rcases z with ⟨u,v⟩
    simp only [collisions, fiber, Finset.mem_filter, Finset.mem_offDiag, f]
    grind
  have hsq : ∑ r ∈ T, (fiber r).card ^ 2 = (collisions s p).card + s.card := by
    rw [hpart', hparts, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.offDiag_card, sq, Nat.sub_add_cancel]
    exact Nat.le_mul_self _
  have hcs := sq_sum_le_card_mul_sum_sq (s := T) (f := fun r => (fiber r).card)
  rw [← hparts,hsq] at hcs
  have hu := hcs.trans (Nat.mul_le_mul_right _ hL)
  nlinarith [Nat.mul_le_mul_right s.card hs]

private theorem number_of_prime_divisors {v P : ℕ} (hv : 0 < v) (hvP : v ≤ P) :
    v.primeFactors.card ≤ Nat.log 2 P := by
  apply Nat.le_log_of_pow_le (by decide)
  calc
    2 ^ v.primeFactors.card = ∏ _p ∈ v.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ v.primeFactors, p := Finset.prod_le_prod fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ v := Nat.le_of_dvd hv (Nat.prod_primeFactors_dvd _)
    _ ≤ P := hvP

/-- The estimate is uniform in the chosen subset s and in the finite prime set bad.
The integer L bounds the number of occupied residue classes for each such prime. -/
theorem bad_prime_count (s bad : Finset ℕ) (P L : ℕ) (hpos : 0 < s.card)
    (hsize : 2 * L ≤ s.card) (hbound : ∀ x ∈ s, x ≤ P)
    (hprime : ∀ p ∈ bad, p.Prime)
    (hbad : ∀ p ∈ bad, (s.image (· % p)).card ≤ L) :
    bad.card ≤ 2 * L * Nat.log 2 P := by
  classical
  let rel (p : ℕ) (z : ℕ × ℕ) := z.1 % p = z.2 % p
  have hupper (a b : ℕ) (ha : a ≤ P) (hb : b ≤ P) (hab : a < b) :
      (bad.filter fun p => a % p = b % p).card ≤ Nat.log 2 P := by
    apply le_trans (Finset.card_le_card (t := (b-a).primeFactors) ?_)
    · exact number_of_prime_divisors (by omega) (by omega)
    · intro p hp
      obtain ⟨hp, hm⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hprime p hp, (Nat.modEq_iff_dvd' hab.le).mp hm, by omega⟩
  have hdeg (z) (hz : z ∈ s.offDiag) :
      (bad.bipartiteBelow rel z).card ≤ Nat.log 2 P := by
    rcases z with ⟨a,b⟩
    obtain ⟨ha,hb,hab⟩ := Finset.mem_offDiag.mp hz
    rcases lt_or_gt_of_ne hab with h | h
    · exact hupper a b (hbound a ha) (hbound b hb) h
    · simpa only [Finset.bipartiteBelow, rel, eq_comm] using
        hupper b a (hbound b hb) (hbound a ha) h
  have hsum : bad.card * s.card^2 ≤ 2*L*(s.offDiag.card * Nat.log 2 P) := calc
    _ = ∑ _p ∈ bad, s.card^2 := by simp
    _ ≤ ∑ p ∈ bad, 2*L*(s.offDiag.bipartiteAbove rel p).card :=
      Finset.sum_le_sum fun p hp => collision_lower s p L hsize (hbad p hp)
    _ = 2*L * ∑ z ∈ s.offDiag, (bad.bipartiteBelow rel z).card := by
      rw [← Finset.mul_sum, Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ ≤ _ := by
      apply Nat.mul_le_mul_left
      simpa using Finset.sum_le_sum hdeg
  have hdiag : s.offDiag.card ≤ s.card^2 := by rw [Finset.offDiag_card,sq]; omega
  have hh : bad.card * s.card^2 ≤ (2*L*Nat.log 2 P) * s.card^2 := calc
    _ ≤ _ := hsum
    _ ≤ 2*L*(s.card^2 * Nat.log 2 P) := by gcongr
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hh (pow_pos hpos _)

end OddEgyptian
