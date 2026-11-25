module

public import MathProblems.OddEgyptian.Counting
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Finset

private theorem fresh_triple (Q n : ℕ) (hdvd : Q ∣ n) (hn : 3 ≤ n) (ho : Odd n)
    (F : Finset ℕ) (hbudget : 2*F.card+1 < Q.divisors.card) :
    ∃ T : Finset ℕ, Disjoint F T ∧ Represents (1/(n:ℚ)) T ∧ T.card = 3 ∧
      n ≤ T.sup id ∧ Q ∣ T.sup id := by
  have hsub := Finset.card_le_card (Nat.divisors_subset_of_dvd (by omega : n ≠ 0) hdvd)
  have hc : n.divisors.card = n.properDivisors.card+1 := by
    rw [← Nat.insert_self_properDivisors (by omega : n ≠ 0)]
    exact Finset.card_insert_of_notMem Nat.self_notMem_properDivisors
  let f := fun d => splitTriple d (n/d)
  have hchoices := card_admissibleChoices n.properDivisors F f
    (fun x _ => split_fiber_le_two ho hn x)
  obtain ⟨d,hd⟩ := Finset.card_pos.mp (show 0 < (admissibleChoices n.properDivisors F f).card by omega)
  obtain ⟨hd,hdis⟩ := mem_admissibleChoices.mp hd
  obtain ⟨hd0,hdo,huo,hu,heq⟩ := split_divisor_data ho hd
  let u := n/d
  have he : d*u=n := heq
  obtain ⟨h₁,h₂,h₃⟩ := split_scaled_order hd0 huo hu
  have htop : (splitTriple d u).sup id = d*splitV u := by
    obtain ⟨_,ha,hb⟩ := split_order (u:=u) huo hu
    simp [splitTriple, max_eq_right hb.le, max_eq_right (ha.trans hb).le]
  refine ⟨splitTriple d u, hdis, ⟨?_, ?_⟩, splitTriple_card hd0 huo hu, ?_, ?_⟩
  · intro x hx
    have := splitTriple_lower hd0 huo hu hx
    exact ⟨by dsimp [u] at *; omega, splitTriple_odd hdo huo hx⟩
  · simpa only [he] using splitTriple_sum (u:=u) hd0 huo hu
  · rw [htop, ←he]
    exact (h₁.trans (h₂.trans h₃)).le
  · rw [htop]
    apply hdvd.trans
    rw [←he]
    apply Nat.mul_dvd_mul_left
    dsimp [splitV,splitU]
    split <;> simp_all [dvd_mul_right, Nat.dvd_mul_left_of_dvd]

private theorem split_list (Q : ℕ) (E : Finset ℕ) (l : List ℕ)
    (hv : ∀ n∈l, 3≤n ∧ Odd n ∧ Q∣n)
    (hbudget : 2*(E.card+3*l.length)+1 < Q.divisors.card) :
    ∃ T : Finset ℕ, Disjoint E T ∧ Represents ((l.map fun n : ℕ => (1:ℚ)/n).sum) T ∧
      T.card = 3*l.length ∧ (∀ n∈l, n≤T.sup id) ∧ Q ∣ T.sup id := by
  induction l with
  | nil => exact ⟨∅, by simp, by simp [Represents], by simp, by simp, by simp⟩
  | cons n l ih =>
    obtain ⟨T,hdis,hrep,hcard,hbound,hQT⟩ := ih
      (fun m hm => hv m (List.mem_cons_of_mem _ hm)) (by simp at hbudget; omega)
    obtain ⟨hn,hno,hQn⟩ := hv n (by simp)
    have hcap : 2*(E∪T).card+1 < Q.divisors.card := by
      rw [Finset.card_union_of_disjoint hdis,hcard]
      simp at hbudget
      omega
    obtain ⟨S,hd,hS,hcs,hbs,hQS⟩ := fresh_triple Q n hQn hn hno (E∪T) hcap
    obtain ⟨hdE,hdT⟩ := Finset.disjoint_union_left.mp hd
    refine ⟨S∪T, Finset.disjoint_union_right.mpr ⟨hdE,hdis⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hS.1 x hx
      · exact hrep.1 x hx
    · rw [Finset.sum_union hdT.symm, hS.2,hrep.2]
      simp
    · rw [Finset.card_union_of_disjoint hdT.symm, hcs,hcard]
      simp
      omega
    · intro a ha
      rw [Finset.sup_union]
      rcases List.mem_cons.mp ha with rfl | h
      · exact hbs.trans (le_max_left ..)
      · exact (hbound a h).trans (le_max_right ..)
    · rw [Finset.sup_union]
      rcases le_total (S.sup id) (T.sup id) with h | h
      · simpa [sup_eq_right.mpr h] using hQT
      · simpa [sup_eq_left.mpr h] using hQS

/-- A short expansion of the complement of 1/Q, and enough divisors of Q,
give an expansion whose greatest denominator is a multiple of Q. -/
theorem maximum_multiple_of_complement (Q : ℕ) (hQ : 3≤Q) (ho : Odd Q)
    (E : Finset ℕ) (hE : Represents (1-1/(Q:ℚ)) E)
    (hbudget : 8*E.card+7 < Q.divisors.card) :
    ∃ s : Finset ℕ, Represents 1 s ∧ s.card ≤ 4*E.card+3 ∧ Q ∣ s.sup id := by
  classical
  let l := (Q*Q) :: E.toList.map (fun e => Q*e)
  have hlen : l.length = E.card+1 := by simp [l]
  have hv (n) (hn : n∈l) : 3≤n ∧ Odd n ∧ Q∣n := by
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨by nlinarith, ho.mul ho, dvd_mul_right ..⟩
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hn
    have he' := hE.1 e (Finset.mem_toList.mp he)
    exact ⟨by nlinarith [he'.1], ho.mul he'.2, dvd_mul_right ..⟩
  obtain ⟨T, hd, hT, hcard, hmax, _⟩ := split_list Q E l hv (by rw [hlen]; omega)
  have hall : E.sup id ≤ T.sup id := by
    apply Finset.sup_le
    intro n hn
    have h := hmax (Q*n) (List.mem_cons_of_mem _ (List.mem_map.mpr
      ⟨n, Finset.mem_toList.mpr hn, rfl⟩))
    dsimp [id]; nlinarith
  have hsum : (l.map (fun n : ℕ => (1:ℚ)/n)).sum = 1/(Q:ℚ)^2 + (1/(Q:ℚ))*(1-1/Q) := by
    simp only [l, List.map_cons, List.sum_cons, List.map_map, Function.comp_def, Nat.cast_mul,
      Finset.sum_map_toList]
    rw [← hE.2, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro a _
      ring
  refine ⟨E∪T, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with he | ht
    · exact hE.1 x he
    · exact hT.1 x ht
  · rw [Finset.sum_union hd,hE.2,hT.2,hsum]
    field_simp
    ring
  · rw [Finset.card_union_of_disjoint hd,hcard,hlen]; omega
  · rwa [Finset.sup_union,sup_eq_right.mpr hall]

end OddEgyptian
