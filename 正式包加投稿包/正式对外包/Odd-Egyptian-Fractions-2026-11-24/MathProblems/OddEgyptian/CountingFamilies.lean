module

public import MathProblems.OddEgyptian.Definitions

import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Finset
open scoped BigOperators

/-- Divisor choices for which none of the three new denominators belongs to the background. -/
def admissibleChoices (choices background : Finset ℕ) (triple : ℕ → Finset ℕ) : Finset ℕ :=
  choices \ background.biUnion fun x => choices.filter fun d => x ∈ triple d

theorem mem_admissibleChoices {choices background : Finset ℕ} {triple : ℕ → Finset ℕ} {d : ℕ} :
    d ∈ admissibleChoices choices background triple ↔
      d ∈ choices ∧ Disjoint background (triple d) := by
  simp only [admissibleChoices, mem_sdiff, mem_biUnion, mem_filter, disjoint_left]
  constructor
  · rintro ⟨hd, avoid⟩
    refine ⟨hd, ?_⟩
    intro x hx hd'
    exact avoid ⟨x, hx, hd, hd'⟩
  · rintro ⟨hd, avoid⟩
    exact ⟨hd, fun ⟨x, hx, _, hd'⟩ => avoid hx hd'⟩

/-- If each old denominator rules out at most two choices, the total loss is at most
twice the number of old denominators. -/
theorem card_admissibleChoices (choices background : Finset ℕ) (triple : ℕ → Finset ℕ)
    (fibers : ∀ x ∈ background, (choices.filter fun d => x ∈ triple d).card ≤ 2) :
    choices.card - 2 * background.card ≤ (admissibleChoices choices background triple).card := by
  have h := Finset.card_biUnion_le (s := background)
    (t := fun x => choices.filter fun d => x ∈ triple d)
  have total : (∑ x ∈ background, (choices.filter fun d => x ∈ triple d).card) ≤
      ∑ _x ∈ background, 2 := Finset.sum_le_sum fibers
  simp only [sum_const, smul_eq_mul] at total
  have hsd := Finset.le_card_sdiff
    (background.biUnion fun x => choices.filter fun d => x ∈ triple d) choices
  unfold admissibleChoices
  omega

/-- For disjoint families, deleting the fixed background recovers the entire triple. -/
theorem backgroundUnion_injOn (choices background : Finset ℕ) (triple : ℕ → Finset ℕ)
    (hinj : Set.InjOn triple choices) :
    Set.InjOn (fun d => background ∪ triple d) (admissibleChoices choices background triple) := by
  intro a ha b hb heq
  obtain ⟨hda, ha'⟩ := mem_admissibleChoices.mp ha
  obtain ⟨hdb, hb'⟩ := mem_admissibleChoices.mp hb
  apply hinj hda hdb
  calc
    triple a = (background ∪ triple a) \ background := (Finset.union_sdiff_cancel_left ha').symm
    _ = (background ∪ triple b) \ background := congrArg (fun s => s \ background) heq
    _ = triple b := Finset.union_sdiff_cancel_left hb'

/-- Turn a family of disjoint triples, each representing the same complement, into a
single-length family of representations of one. -/
theorem count_from_background (choices background : Finset ℕ) (triple : ℕ → Finset ℕ)
    (q : ℚ) (hb : Represents (1 - q) background)
    (ht : ∀ d ∈ choices, Represents q (triple d))
    (hcard : ∀ d ∈ choices, (triple d).card = 3)
    (hinj : Set.InjOn triple choices)
    (fibers : ∀ x ∈ background, (choices.filter fun d => x ∈ triple d).card ≤ 2)
    [Finite (Solutions (background.card + 3))] :
    choices.card - 2 * background.card ≤ oddCount (background.card + 3) := by
  let good := admissibleChoices choices background triple
  let family (d : good) : Solutions (background.card + 3) := by
    obtain ⟨hd, hdis⟩ := mem_admissibleChoices.mp d.property
    refine ⟨background ∪ triple d.val, ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      rcases mem_union.mp hx with h | h
      · exact hb.1 x h
      · exact (ht _ hd).1 x h
    · rw [sum_union hdis, hb.2, (ht _ hd).2]
      ring
    · rw [card_union_of_disjoint hdis, hcard _ hd]
  have inj : Function.Injective family := by
    intro a b h
    apply Subtype.ext
    exact backgroundUnion_injOn choices background triple hinj a.property b.property
      (congrArg Subtype.val h)
  have cmp := Nat.card_le_card_of_injective family inj
  calc
    _ ≤ good.card := card_admissibleChoices choices background triple fibers
    _ = Nat.card good := by simp
    _ ≤ oddCount (background.card + 3) := cmp

/-- Iterating any family of two-term padding embeddings preserves distinctness. -/
def iteratePadding (step : ∀ k, Solutions k ↪ Solutions (k + 2)) (k : ℕ) :
    (t : ℕ) → Solutions k ↪ Solutions (k + 2 * t)
  | 0 => by simpa using Function.Embedding.refl (Solutions k)
  | t + 1 => by
    simpa only [Nat.mul_succ, Nat.add_assoc] using
      (iteratePadding step k t).trans (step (k + 2 * t))

theorem oddCount_le_of_padding (step : ∀ k, Solutions k ↪ Solutions (k + 2)) {k l : ℕ}
    (hl : l ≤ k) (hoddL : Odd l) (hoddK : Odd k) [Finite (Solutions k)] :
    oddCount l ≤ oddCount k := by
  obtain ⟨a, ha⟩ := hoddL
  obtain ⟨b, hb⟩ := hoddK
  have hk : k = l + 2 * (b - a) := by omega
  let emb : Solutions l ↪ Solutions k := hk ▸ iteratePadding step l (b - a)
  exact Nat.card_le_card_of_injective _ emb.injective

end OddEgyptian
