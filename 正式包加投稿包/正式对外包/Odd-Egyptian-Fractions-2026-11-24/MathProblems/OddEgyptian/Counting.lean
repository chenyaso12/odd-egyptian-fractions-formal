module

public import MathProblems.OddEgyptian.CountingFamilies
public import MathProblems.OddEgyptian.Split
public import MathProblems.OddEgyptian.Finiteness

import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Finset
open scoped BigOperators

/-- Replace the maximum denominator by the ordered three-term splitting with divisor one. -/
def padSet (s : Finset ℕ) : Finset ℕ :=
  let n := s.sup id
  s.erase n ∪ splitTriple 1 n

private theorem max_mem_of_represents {s : Finset ℕ} (hs : Represents 1 s) :
    s.sup id ∈ s := by
  have hne : s.Nonempty := by
    by_contra! h
    simp [h] at hs
    obtain ⟨_, hfalse⟩ := hs
    norm_num at hfalse
  simpa using (Finset.sup_mem_of_nonempty (f := id) hne)

private theorem odd_ge_three {n : ℕ} (hn : 1 < n) (ho : Odd n) : 3 ≤ n := by
  obtain ⟨t, ht⟩ := ho
  omega

theorem padSet_solution {k : ℕ} (s : Solutions k) :
    Represents 1 (padSet s.val) ∧ (padSet s.val).card = k + 2 := by
  let n := s.val.sup id
  have hn : n ∈ s.val := max_mem_of_represents s.property.1
  obtain ⟨hn1, hnOdd⟩ := s.property.1.1 n hn
  have hn3 := odd_ge_three hn1 hnOdd
  have hlow {x : ℕ} (hx : x ∈ splitTriple 1 n) : n + 2 ≤ x := by
    simpa using splitTriple_lower (by decide : 0 < 1) hnOdd hn3 hx
  have hd : Disjoint (s.val.erase n) (splitTriple 1 n) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxs hxt
    have hx : x ≤ n := Finset.le_sup (f := id) (mem_of_mem_erase hxs)
    have := hlow hxt
    omega
  change Represents 1 (s.val.erase n ∪ splitTriple 1 n) ∧
    (s.val.erase n ∪ splitTriple 1 n).card = k + 2
  constructor
  · constructor
    · intro x hx
      rcases mem_union.mp hx with hx | hx
      · exact s.property.1.1 x (mem_of_mem_erase hx)
      · exact ⟨by have := hlow hx; omega, splitTriple_odd (by decide : Odd 1) hnOdd hx⟩
    · rw [Finset.sum_union hd, splitTriple_sum (by decide : 0 < 1) hnOdd hn3, one_mul]
      exact (Finset.sum_erase_add s.val (fun x => (1 : ℚ) / (x : ℚ)) hn).trans s.property.1.2
  · rw [card_union_of_disjoint hd, splitTriple_card (by decide : 0 < 1) hnOdd hn3,
      card_erase_of_mem hn, s.property.2]
    have hk : 0 < k := s.property.2 ▸ Finset.card_pos.mpr ⟨n, hn⟩
    omega

def dropMaximum (s : Finset ℕ) : Finset ℕ := s.erase (s.sup id)

/-- Decoding requires only the output: discard the last two denominators, then subtract
two from the remaining maximum. -/
def unpadSet (s : Finset ℕ) : Finset ℕ :=
  let s' := dropMaximum (dropMaximum s)
  insert (s'.sup id - 2) (dropMaximum s')

private theorem sup_insert_above {s : Finset ℕ} {a : ℕ} (h : s.sup id < a) :
    (insert a s).sup id = a := by
  rw [Finset.sup_insert]
  exact max_eq_left h.le

private theorem dropMaximum_insert_above {s : Finset ℕ} {a : ℕ} (h : s.sup id < a) :
    dropMaximum (insert a s) = s := by
  rw [dropMaximum, sup_insert_above h, Finset.erase_insert]
  exact fun ha => (not_lt_of_ge (Finset.le_sup (f := id) ha)) h

private theorem padSet_form (s : Finset ℕ) :
    padSet s = insert (splitV (s.sup id)) (insert (splitU (s.sup id))
      (insert (s.sup id + 2) (s.erase (s.sup id)))) := by
  ext x
  simp only [padSet, splitTriple, one_mul, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

theorem unpadSet_padSet {s : Finset ℕ} (hs : Represents 1 s) : unpadSet (padSet s) = s := by
  let n := s.sup id
  let e := s.erase n
  have hn : n ∈ s := max_mem_of_represents hs
  obtain ⟨hn1, ho⟩ := hs.1 n hn
  obtain ⟨_, hu, hv⟩ := split_order ho (odd_ge_three hn1 ho)
  have h0 : e.sup id ≤ n := Finset.sup_le (fun x hx => Finset.le_sup (f := id)
    (Finset.mem_of_mem_erase hx))
  have ha : e.sup id < n + 2 := by omega
  have hb : (insert (n + 2) e).sup id < splitU n := (sup_insert_above ha).trans_lt hu
  have hc : (insert (splitU n) (insert (n + 2) e)).sup id < splitV n :=
    (sup_insert_above hb).trans_lt hv
  rw [padSet_form]
  change insert ((dropMaximum (dropMaximum (insert (splitV n)
      (insert (splitU n) (insert (n + 2) e))))).sup id - 2)
    (dropMaximum (dropMaximum (dropMaximum (insert (splitV n)
      (insert (splitU n) (insert (n + 2) e)))))) = s
  rw [dropMaximum_insert_above hc, dropMaximum_insert_above hb, sup_insert_above ha,
    dropMaximum_insert_above ha, Nat.add_sub_cancel]
  exact Finset.insert_erase hn

def paddingEmbedding (k : ℕ) : Solutions k ↪ Solutions (k + 2) where
  toFun s := ⟨padSet s.val, padSet_solution s⟩
  inj' := by
    intro s t h
    apply Subtype.ext
    have heq : padSet s.val = padSet t.val := congrArg Subtype.val h
    simpa only [unpadSet_padSet s.property.1, unpadSet_padSet t.property.1] using
      congrArg unpadSet heq

theorem oddCount_mono_odd {k l : ℕ} (hl : l ≤ k) (hol : Odd l) (hok : Odd k)
    : oddCount l ≤ oddCount k :=
  oddCount_le_of_padding paddingEmbedding hl hol hok

/-- From a two-choice bound on each forbidden denominator, the actual odd divisor
splits of a complement give this many distinct representations of equal length. -/
theorem count_splits_of_fiber_bound {n : ℕ} (hn : 3 ≤ n) (ho : Odd n)
    (E : Finset ℕ) (hb : Represents (1 - 1 / (n : ℚ)) E)
    (fibers : ∀ x ∈ E, (n.properDivisors.filter fun d =>
      x ∈ splitTriple d (n / d)).card ≤ 2) :
    n.divisors.card - 1 - 2 * E.card ≤ oddCount (E.card + 3) := by
  have ht {d : ℕ} (hd : d ∈ n.properDivisors) :
      Represents (1 / (n : ℚ)) (splitTriple d (n / d)) := by
    obtain ⟨hd0, hodd, hou, hu3, hn'⟩ := split_divisor_data ho hd
    constructor
    · intro x hx
      have hle := splitTriple_lower hd0 hou hu3 hx
      have hlt := (split_scaled_order hd0 hou hu3).1
      exact ⟨by omega, splitTriple_odd hodd hou hx⟩
    · simpa only [hn'] using splitTriple_sum hd0 hou hu3
  have hc {d : ℕ} (hd : d ∈ n.properDivisors) : (splitTriple d (n / d)).card = 3 := by
    obtain ⟨hd0, _, hou, hu3, _⟩ := split_divisor_data ho hd
    exact splitTriple_card hd0 hou hu3
  have hi : Set.InjOn (fun d => splitTriple d (n / d)) n.properDivisors := by
    intro d hd e he heq
    obtain ⟨hd0, _, hou, hu3, hnd⟩ := split_divisor_data ho hd
    obtain ⟨he0, _, hov, hv3, hne⟩ := split_divisor_data ho he
    exact splitTriple_injective hd0 he0 hou hov hu3 hv3 (hnd.trans hne.symm) heq
  have hcdiv : n.divisors.card = n.properDivisors.card + 1 := by
    rw [← Nat.insert_self_properDivisors (by omega : n ≠ 0)]
    exact Finset.card_insert_of_notMem Nat.self_notMem_properDivisors
  rw [hcdiv, Nat.add_sub_cancel]
  exact count_from_background _ E _ (1 / (n : ℚ)) hb (fun _ => ht)
    (fun _ => hc) hi fibers

/-- Counting directly from a representation of the complement of the marked denominator. -/
theorem count_splits {n : ℕ} (hn : 3 ≤ n) (ho : Odd n)
    (E : Finset ℕ) (hb : Represents (1 - 1 / (n : ℚ)) E) :
    n.divisors.card - 1 - 2 * E.card ≤ oddCount (E.card + 3) :=
  count_splits_of_fiber_bound hn ho E hb (fun x _ => split_fiber_le_two ho hn x)

end OddEgyptian
