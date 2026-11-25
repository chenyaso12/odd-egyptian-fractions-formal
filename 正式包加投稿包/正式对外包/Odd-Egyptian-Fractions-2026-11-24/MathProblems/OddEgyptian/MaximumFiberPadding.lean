module

public import MathProblems.OddEgyptian.StructuredFamilies
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

theorem padSet_sup {s : Finset ℕ} (hs : Represents 1 s) :
    (padSet s).sup id = splitV (s.sup id) := by
  have hne : s.Nonempty := by
    by_contra! h
    have := hs.2
    simp [h] at this
  have hm : s.sup id ∈ s := by simpa using Finset.sup_mem_of_nonempty (f := id) hne
  obtain ⟨hone, ho⟩ := hs.1 _ hm
  have hn : 3 ≤ s.sup id := by
    obtain ⟨z,hz⟩ := ho
    omega
  obtain ⟨ha,hb,hc⟩ := split_order ho hn
  have herase : (s.erase (s.sup id)).sup id ≤ s.sup id :=
    Finset.sup_le fun x hx => Finset.le_sup (f := id) (Finset.mem_of_mem_erase hx)
  rw [padSet, Finset.sup_union]
  simp [splitTriple, max_eq_right hc.le, max_eq_right (hb.trans hc).le,
    max_eq_right (herase.trans (ha.trans (hb.trans hc)).le)]

/-- Padding sends every maximum to a different maximum and is injective within each fiber. -/
theorem maximumFamilies_pad {k Q n : ℕ} (h : HasMaximumFamilies k Q n) :
    HasMaximumFamilies (k+2) Q n := by
  classical
  rcases n with _ | n
  · exact ⟨∅, by simp, by simp⟩
  obtain ⟨M,hM,data⟩ := h
  have oddMax {y : ℕ} (hy : y ∈ M) : Odd y := by
    obtain ⟨_,S,hs,hS⟩ := data y hy
    obtain ⟨s,h⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    obtain ⟨rep,_,rfl⟩ := hS s h
    have hsne : s.Nonempty := by
      by_contra! he
      have := rep.2
      simp [he] at this
    exact (rep.1 _ (by simpa using Finset.sup_mem_of_nonempty (f := id) hsne)).2
  have inj : Set.InjOn splitV (M : Set ℕ) := by
    intro a ha b hb eq
    rcases lt_trichotomy a b with lt | eq' | gt
    · exact False.elim ((splitV_lt_of_odd (oddMax ha) (oddMax hb) lt).ne eq)
    · exact eq'
    · exact False.elim ((splitV_lt_of_odd (oddMax hb) (oddMax ha) gt).ne eq.symm)
  refine ⟨M.image splitV, by rwa [Finset.card_image_of_injOn inj], ?_⟩
  intro z hz
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hyQ,S,hn,hS⟩ := data y hy
  refine ⟨hyQ.trans (self_dvd_splitV (oddMax hy)), S.image padSet, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn]
    · exact hn
    · intro a ha b hb eq
      simpa only [unpadSet_padSet (hS a ha).1, unpadSet_padSet (hS b hb).1] using
        congrArg unpadSet eq
  · intro t ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨rep,card,top⟩ := hS s hs
    obtain ⟨p,pc⟩ := padSet_solution (k := k) ⟨s,rep,card⟩
    exact ⟨p,pc, by rw [padSet_sup rep,top]⟩

end OddEgyptian
