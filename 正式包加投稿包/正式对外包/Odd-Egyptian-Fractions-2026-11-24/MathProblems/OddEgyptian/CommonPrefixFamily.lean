module

public import MathProblems.OddEgyptian.CommonPrefixPair
public import MathProblems.OddEgyptian.StructuredFamilies
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Finset

/-- Each recorded maximum indexes an actual k-term solution with the stated prefix. -/
theorem IsPrefixFamily.exists_solution {k Q : ℕ} {P Y : Finset ℕ}
    (h : IsPrefixFamily k Q P Y) {y : ℕ} (hy : y ∈ Y) :
    ∃ (x : ℕ) (s : Solutions k), (∀ p ∈ P, p < x) ∧ x < y ∧
      s.val = insert y (insert x P) ∧ s.val.sup id = y ∧ Q ∣ y := by
  obtain ⟨x,hp,hxy,rep,hdvd⟩ := h.2 y hy
  have hxnot : x ∉ P := fun hx => (hp _ hx).false
  have hynot : y ∉ insert x P := by
    intro hy'
    rcases Finset.mem_insert.mp hy' with eq | hp'
    · omega
    · have := hp _ hp'
      omega
  have hsize : (insert y (insert x P)).card = k := by
    rw [Finset.card_insert_of_notMem hynot, Finset.card_insert_of_notMem hxnot]
    exact h.1
  refine ⟨x,⟨_,rep,hsize⟩,hp,hxy,rfl,le_antisymm ?_ ?_,hdvd⟩
  · apply Finset.sup_le
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_rfl
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hxy.le
    · exact (hp _ hz).le.trans hxy.le
  · exact Finset.le_sup (f:=id) (Finset.mem_insert_self ..)

/-- The final denominator is uniquely determined once all preceding terms are fixed. -/
theorem last_denominator_unique {P : Finset ℕ} {y z : ℕ}
    (hy : ∀ p ∈ P, p < y) (hz : ∀ p ∈ P, p < z)
    (ry : Represents 1 (insert y P)) (rz : Represents 1 (insert z P)) : y = z := by
  have hy' : y ∉ P := fun h => (hy _ h).false
  have hz' : z ∉ P := fun h => (hz _ h).false
  have h := ry.2.trans rz.2.symm
  rw [Finset.sum_insert hy', Finset.sum_insert hz'] at h
  have he := add_right_cancel h
  have hcast : (y:ℚ) = (z:ℚ) := by simpa only [one_div,inv_inj] using he
  exact_mod_cast hcast

theorem sup_mem_of_represents_one {s : Finset ℕ} (hs : Represents 1 s) : s.sup id ∈ s := by
  have hne : s.Nonempty := by
    by_contra! h
    obtain ⟨_, he⟩ := hs
    simp [h] at he
  simpa using Finset.sup_mem_of_nonempty (f:=id) hne

/-- Branch only at the last two entries. Each divisor other than one supplies a
different maximum and all the resulting representations have the same prefix. -/
theorem prefixFamily_of_divisible_maximum {s : Finset ℕ} (hs : Represents 1 s) {Q : ℕ}
    (hQ : Q ∣ s.sup id) :
    ∃ P Y : Finset ℕ, IsPrefixFamily (s.card+2) Q P Y ∧ Y.card = Q.divisors.card-1 := by
  let n := s.sup id
  let E := s.erase n
  let P := insert (n+2) E
  have hnmem : n ∈ s := sup_mem_of_represents_one hs
  obtain ⟨hn1,ho⟩ := hs.1 n hnmem
  have hn : 3 ≤ n := by obtain ⟨a,ha⟩ := ho; omega
  have below (z) (hz : z ∈ E) : z ≤ n := Finset.le_sup (f:=id) (Finset.mem_of_mem_erase hz)
  have hnew : n+2 ∉ E := fun h => by have := below _ h; omega
  have hpc : P.card = s.card := by
    have hpos := Finset.card_pos.mpr ⟨n,hnmem⟩
    rw [show P = insert (n+2) E from rfl, Finset.card_insert_of_notMem hnew,
      show E = s.erase n from rfl, Finset.card_erase_of_mem hnmem]
    omega
  have hprefix (p) (hp : p ∈ P) : p ≤ n+2 := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact le_rfl
    · exact (below _ hp).trans (by omega)
  refine ⟨P, PrefixPair.maxima Q n, ⟨by rw [hpc], ?_⟩,
    PrefixPair.maxima_card hn ho hQ⟩
  intro y hy
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hne,hdQ⟩ := Finset.mem_erase.mp hd
  have hd1 : 1 < d := by have := Nat.pos_of_mem_divisors hdQ; omega
  have hdN := (Nat.dvd_of_mem_divisors hdQ).trans hQ
  obtain ⟨hq,hq1,hto,hA⟩ := PrefixPair.pick_spec hn ho hdN hd1
  let x := PrefixPair.mate n d*((PrefixPair.pick n d+1)/2)
  let y := PrefixPair.largest n d
  obtain ⟨hsmall, hxy, hxo, hyo, hdy, hpairsum⟩ := PrefixPair.lastPair hn ho hto hq hq1 hA
  change n+2 < x at hsmall
  change x < y at hxy
  change Odd x at hxo
  change Odd y at hyo
  change n ∣ y at hdy
  change (1:ℚ)/x + 1/y = 2/(n*(n+2):ℕ) at hpairsum
  have hlt (p) (hp : p ∈ P) := (hprefix p hp).trans_lt hsmall
  have hxnot : x ∉ P := fun hx => (hlt _ hx).false
  have hynot : y ∉ insert x P := by
    intro hy
    rcases Finset.mem_insert.mp hy with he | hp
    · omega
    · have := hlt _ hp
      omega
  refine ⟨x,hlt,hxy,⟨?_,?_⟩,hQ.trans hdy⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨by omega,hyo⟩
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨by omega,hxo⟩
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨by omega,ho.add_even (by decide : Even (2:ℕ))⟩
    · exact hs.1 _ (Finset.mem_of_mem_erase hp)
  · change (∑ p ∈ insert y (insert x P), (1:ℚ)/p) = 1
    rw [Finset.sum_insert hynot, Finset.sum_insert hxnot,
      show P = insert (n+2) E from rfl, Finset.sum_insert hnew]
    have hE : (∑ p ∈ E, (1:ℚ)/p) + 1/n = 1 :=
      (Finset.sum_erase_add s (fun p => (1:ℚ)/p) hnmem).trans hs.2
    linarith only [hE,hpairsum,PrefixPair.fixedTerm hn]

end OddEgyptian
