module

public import MathProblems.OddEgyptian.CommonPrefixFamily
public import MathProblems.OddEgyptian.CommonPrefixScale
public import MathProblems.OddEgyptian.MaximumFiberPadding
public import MathProblems.OddEgyptian.Parity

@[expose] public section

namespace OddEgyptian

/-- Pad a single representation to any longer odd length while retaining a divisor of its maximum. -/
theorem pad_divisible_maximum_to_length {s : Finset ℕ} (hs : Represents 1 s) {Q k : ℕ}
    (hQ : Q ∣ s.sup id) (hk : Odd k) (hlen : s.card ≤ k) :
    ∃ t : Finset ℕ, Represents 1 t ∧ t.card = k ∧ Q ∣ t.sup id := by
  have extend (j : ℕ) :
      ∃ t : Finset ℕ, Represents 1 t ∧ t.card = s.card+2*j ∧ Q ∣ t.sup id := by
    induction j with
    | zero => exact ⟨s, hs, by simp, hQ⟩
    | succ j ih =>
      obtain ⟨t,ht,hlen,hQt⟩ := ih
      obtain ⟨hp,hpc⟩ := padSet_solution (k:=t.card) ⟨t,ht,rfl⟩
      change (padSet t).card = t.card+2 at hpc
      have ho := (ht.1 _ (sup_mem_of_represents_one ht)).2
      refine ⟨padSet t,hp,by omega,?_⟩
      rw [padSet_sup ht]
      exact hQt.trans (self_dvd_splitV ho)
  obtain ⟨a,ha⟩ := represents_one_odd_card hs
  obtain ⟨b,hb⟩ := hk
  have heq : s.card+2*((k-s.card)/2) = k := by omega
  simpa only [heq] using extend ((k-s.card)/2)

/-- Theorem 1.3. Fix one representation padded to length k−2 and vary only the two
last terms of the final k-term representations. -/
theorem commonPrefix_of_maximum (hm : MaximumTarget) : CommonPrefixTarget := by
  obtain ⟨A,hA,R,seed⟩ := hm
  obtain ⟨c,hc,K,scale⟩ := commonPrefix_scale A hA R
  refine ⟨c,hc,K,?_⟩
  intro k hk hodd
  obtain ⟨r,hr,hr3,hlen,hrank,hcount⟩ := scale k hk
  obtain ⟨s,hs,hshort,hQ⟩ := seed r hr
  have hsk : s.card+2 ≤ k := by
    exact_mod_cast (show (s.card:ℝ)+2 ≤ (k:ℝ) by linarith)
  have hkodd : Odd (k-2) := by
    obtain ⟨a,ha⟩ := hodd
    exact ⟨a-1,by omega⟩
  obtain ⟨t,ht,hcard,hqt⟩ := pad_divisible_maximum_to_length hs hQ hkodd (by omega : s.card ≤ k-2)
  obtain ⟨P,Y,hfamily,hcardY⟩ := prefixFamily_of_divisible_maximum ht hqt
  have hklen : t.card+2 = k := by omega
  rw [hklen] at hfamily
  refine ⟨P,Y,⟨hfamily.1,?_⟩,?_⟩
  · intro y hy
    obtain ⟨x,hbelow,hxy,hrep,hdvd⟩ := hfamily.2 y hy
    exact ⟨x,hbelow,hxy,hrep,(firstOddProduct_dvd_of_le hrank).trans hdvd⟩
  · rw [hcardY,(firstOddProduct_spec r hr3).2.2.2]
    exact hcount

end OddEgyptian
