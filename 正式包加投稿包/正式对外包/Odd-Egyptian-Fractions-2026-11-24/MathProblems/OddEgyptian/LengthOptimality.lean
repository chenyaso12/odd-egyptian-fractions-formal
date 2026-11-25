module

public import MathProblems.OddEgyptian.LeastLength
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open Finset Real
namespace OddEgyptian

private theorem labelled_bound {ι : Type*} [DecidableEq ι] (D : ι → ℕ) (j K : ℕ)
    (s : Finset ι) (b : ℕ) (a : ℤ) (hb : 0 < b) (hcard : s.card ≤ K) (hj : s.card ≤ j)
    (hp : ∀ t ∈ s, 0 < D t) (hs : ∑ t ∈ s, (1 : ℚ) / D t = (a : ℚ) / b) :
    ∀ x ∈ s, D x ≤ (K*b)^(2^(j-1)) := by
  induction j generalizing s b a with
  | zero =>
    have he : s = ∅ := card_eq_zero.mp (by omega)
    simp [he]
  | succ j ih =>
    intro x hx
    obtain ⟨m,hm,hmin⟩ := s.exists_min_image D ⟨x,hx⟩
    have hpos := hp m hm
    have hab : 0 < (a : ℚ) / b := by
      rw [← hs]
      exact sum_pos (fun y hy => by have := hp y hy; positivity) ⟨x,hx⟩
    have ha : (1 : ℤ) ≤ a := by
      have hh : (0 : ℚ) < a := (div_pos_iff_of_pos_right (by exact_mod_cast hb)).mp hab
      exact Int.add_one_le_iff.mpr (by exact_mod_cast hh)
    have ratio : (a : ℚ)/b ≤ (K : ℚ)/D m := calc
      _ = ∑ t ∈ s, (1 : ℚ)/D t := hs.symm
      _ ≤ ∑ _t ∈ s, (1 : ℚ)/D m := sum_le_sum fun t ht =>
        one_div_le_one_div_of_le (by exact_mod_cast hpos) (by exact_mod_cast hmin t ht)
      _ = (s.card : ℚ)/D m := by simp [div_eq_mul_inv]
      _ ≤ _ := by gcongr
    have hmB : D m ≤ K*b := by
      have cross := (div_le_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hpos)).mp ratio
      have p : (1 : ℚ)*D m ≤ (a : ℚ)*D m := mul_le_mul_of_nonneg_right (by exact_mod_cast ha) (by positivity)
      exact_mod_cast (show (D m : ℚ) ≤ (K : ℚ)*b by linarith)
    simp only [Nat.add_one_sub_one]
    by_cases hxm : x=m
    · rw [hxm]; exact hmB.trans (Nat.le_self_pow (by positivity) _)
    have hx' := mem_erase.mpr (And.intro hxm hx)
    have hlen : (s.erase m).card ≤ j := by rw [card_erase_of_mem hm]; omega
    have hj₁ : 1 ≤ j := (card_pos.mpr ⟨x,hx'⟩).trans_le hlen
    have tail : ∑ y ∈ s.erase m, (1 : ℚ)/D y = ((a*(D m:ℤ)-(b:ℤ) : ℤ):ℚ)/(b*D m:ℕ) := by
      have h := s.sum_erase_add (fun y => (1:ℚ)/D y) hm
      rw [hs] at h
      push_cast
      rw [eq_sub_of_add_eq h]
      field_simp
    have hquad : K*(b*D m) ≤ (K*b)^2 := by
      rw [← Nat.mul_assoc, sq]; exact Nat.mul_le_mul_left _ hmB
    have hexp : 2*(2^(j-1)) = 2^j := by
      calc
        _ = 2^(j-1+1) := by rw [pow_succ]; omega
        _ = _ := by rw [Nat.sub_add_cancel hj₁]
    calc
      D x ≤ (K*(b*D m))^(2^(j-1)) := ih (s.erase m) (b*D m) (a*D m-b) (Nat.mul_pos hb hpos)
        ((card_le_card (erase_subset _ _)).trans hcard) hlen (fun y hy => hp y (mem_of_mem_erase hy)) tail x hx'
      _ ≤ ((K*b)^2)^(2^(j-1)) := Nat.pow_le_pow_left hquad _
      _ = (K*b)^(2^j) := by rw [← pow_mul, hexp]

/-- The two lists of denominators and the additional copy of b keep separate labels. -/
theorem pair_bound {a b : ℕ} (hb : 2 ≤ b) (ha : a < b) {s t : Finset ℕ}
    (hs : Represents ((a:ℚ)/b) s) (ht : Represents (((b-1-a:ℕ):ℚ)/b) t) :
    b ≤ (s.card+t.card+1)^(2^(s.card+t.card)) := by
  let u := (s.disjSum t).disjSum ({b} : Finset ℕ)
  let D : (ℕ ⊕ ℕ) ⊕ ℕ → ℕ := Sum.elim (Sum.elim id id) id
  have hu : u.card = s.card+t.card+1 := by simp [u]
  have hD : ∀ v ∈ u, 0 < D v := by
    rintro ((v|v)|v) hv
    · have h := (hs.1 v (by simpa [u] using hv)).1; exact Nat.zero_lt_of_lt h
    · have h := (ht.1 v (by simpa [u] using hv)).1; exact Nat.zero_lt_of_lt h
    · have h : v=b := by simpa [u] using hv
      simpa [D,h] using (show 0<b by omega)
  have hsum : ∑ v ∈ u, (1:ℚ)/D v = (1:ℚ)/1 := by
    simp only [u,sum_disjSum,sum_singleton,D,Sum.elim_inl,Sum.elim_inr,id_eq]
    rw [hs.2,ht.2]
    have hb₁ : 1 ≤ b := by omega
    have haa : a ≤ b-1 := by omega
    rw [Nat.cast_sub haa, Nat.cast_sub hb₁, Nat.cast_one]
    field_simp; ring
  have h := labelled_bound D u.card u.card u 1 1 (by decide) le_rfl le_rfl hD hsum
    (Sum.inr b) (by simp [u])
  simpa [D,hu] using h

theorem near_one_bound {b : ℕ} (hb : 2 ≤ b) {s : Finset ℕ}
    (hs : Represents (((b-1:ℕ):ℚ)/b) s) : b ≤ (s.card+1)^(2^s.card) := by
  have h := pair_bound (a:=b-1) hb (by omega) hs (t:=∅) (by simp [Represents])
  simpa using h

private theorem double_log {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (h : b ≤ (k+1)^(2^k)) :
    log (log (b:ℝ)) ≤ 2*(k:ℝ) := by
  have hbR : 1 < (b:ℝ) := by exact_mod_cast hb
  have hr : (b:ℝ) ≤ ((k:ℝ)+1)^(2^k : ℕ) := by exact_mod_cast h
  have l : 0 < log ((k:ℝ)+1) := log_pos (by exact_mod_cast (show 1<k+1 by omega))
  have lg := log_le_log (by linarith : (0:ℝ)<b) hr
  rw [log_pow] at lg
  push_cast at lg
  have hh := log_le_log (log_pos hbR) lg
  rw [log_mul (by positivity) (ne_of_gt l), log_pow] at hh
  have h₁ : log (2:ℝ) ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have h₂ := log_le_sub_one_of_pos l
  have h₃ := log_le_sub_one_of_pos (show 0<(k:ℝ)+1 by positivity)
  linarith [mul_le_mul_of_nonneg_left h₁ (show (0:ℝ)≤k by positivity)]

theorem pair_loglog {a b : ℕ} (hb : 2 ≤ b) (ha : a < b) {s t : Finset ℕ}
    (hs : Represents ((a:ℚ)/b) s) (ht : Represents (((b-1-a:ℕ):ℚ)/b) t) :
    log (log (b:ℝ)) ≤ 2*((s.card:ℝ)+(t.card:ℝ)) := by
  have bd := pair_bound hb ha hs ht
  have hnon : 1 ≤ s.card+t.card := by
    by_contra! hh
    have hz : s.card+t.card=0 := by omega
    rw [hz] at bd
    simp at bd
    omega
  simpa using double_log hb hnon bd

theorem near_one_loglog {b : ℕ} (hb : 2 ≤ b) {s : Finset ℕ}
    (hs : Represents (((b-1:ℕ):ℚ)/b) s) : log (log (b:ℝ)) ≤ 2*(s.card:ℝ) := by
  have h := pair_loglog (a:=b-1) hb (by omega) hs (t:=∅) (by simp [Represents])
  simpa using h

def requiresLong (a b : ℕ) : Prop :=
  ∀ s : Finset ℕ, Represents ((a:ℚ)/b) s → log (log (b:ℝ)) ≤ 4*(s.card:ℝ)

noncomputable def hardNumerators (b : ℕ) : Finset ℕ := by
  classical
  exact (range b).filter (fun a => 0<a ∧ requiresLong a b)

/-- Accounting also for the fixed midpoint gives a strict majority at every odd b ≥ 3. -/
theorem hardNumerators_majority {b : ℕ} (hb : 3 ≤ b) (ho : Odd b) :
    (b+1)/2 ≤ (hardNumerators b).card := by
  classical
  have hlog : 0 < log (log (b:ℝ)) := by
    apply log_pos
    apply (lt_log_iff_exp_lt (by positivity)).mpr
    exact exp_one_lt_three.trans_le (by exact_mod_cast hb)
  have nozero : ¬ requiresLong 0 b := by
    intro h
    have hf := h ∅ (by simp [Represents])
    simp at hf
    linarith
  have memHard {a : ℕ} (ha : a<b) : a ∈ hardNumerators b ↔ requiresLong a b := by
    simp only [hardNumerators,mem_filter,mem_range,ha,true_and]
    exact ⟨And.right, fun h => ⟨Nat.pos_of_ne_zero (fun hh => nozero (hh ▸ h)),h⟩⟩
  have sub : hardNumerators b ⊆ range b := filter_subset _ _
  have bound : ((range b) \ hardNumerators b).card ≤ (hardNumerators b).card := by
    apply card_le_card_of_injOn (fun a => b-1-a)
    · intro a h
      obtain ⟨ha, he⟩ := mem_sdiff.mp h
      have hab := mem_range.mp ha
      have failure := (memHard hab).not.mp he
      simp only [requiresLong,not_forall,not_le] at failure
      obtain ⟨s,hs,small⟩ := failure
      apply (memHard (a:=b-1-a) (by omega)).mpr
      intro t ht
      have hpair := pair_loglog (by omega : 2 ≤ b) hab hs ht
      linarith
    · intro a ha c hc eq
      have ha' := mem_range.mp (mem_sdiff.mp ha).1
      have hc' := mem_range.mp (mem_sdiff.mp hc).1
      change b-1-a=b-1-c at eq
      omega
  rw [card_sdiff_of_subset sub, card_range] at bound
  obtain ⟨d,hd⟩ := ho
  omega

/-- Least number of distinct odd denominators representing the indicated fraction. -/
noncomputable def oddMinLength (a b : ℕ) : ℕ :=
  leastDenominatorCard (Represents ((a : ℚ) / b))

/-- Each pointwise minimum is attained, and the same constant works for every pair. -/
def UniformMinLengthTarget : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, 3 ≤ b → Odd b → 1 ≤ a → a < b →
    (∃ s, Represents ((a : ℚ) / b) s ∧ s.card = oddMinLength a b) ∧
      (oddMinLength a b : ℝ) ≤ C*(1 + log (log (b : ℝ)))

theorem uniformMinLength_of_short (short : HTarget) : UniformMinLengthTarget := by
  obtain ⟨C,hC,h⟩ := short
  refine ⟨C,hC,?_⟩
  intro a b hb ho ha hab
  obtain ⟨s, hs, hsize⟩ := h a b hb ho ha hab
  have hh : oddMinLength a b ≤ s.card := leastDenominatorCard_le hs
  exact ⟨leastDenominatorCard_attained ⟨s,hs⟩,
    (show (oddMinLength a b : ℝ) ≤ s.card by exact_mod_cast hh).trans hsize⟩

/-- The maximum includes each numerator from 1 through b−1, without a coprimality filter. -/
noncomputable def maxOddMinLength (b : ℕ) : ℕ :=
  (Ico 1 b).sup (fun a => oddMinLength a b)

noncomputable def meanOddMinLength (b : ℕ) : ℝ :=
  (∑ a ∈ Ico 1 b, (oddMinLength a b : ℝ)) / ((b-1 : ℕ) : ℝ)

theorem meanOddMinLength_le_max {b : ℕ} (hb : 2 ≤ b) :
    meanOddMinLength b ≤ (maxOddMinLength b : ℝ) := by
  have hpos : 0 < ((b-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < b-1 by omega)
  apply (div_le_iff₀ hpos).mpr
  calc
    _ ≤ ∑ _a ∈ Ico 1 b, (maxOddMinLength b : ℝ) := by
      apply sum_le_sum
      intro a ha
      exact_mod_cast (le_sup (f := fun a => oddMinLength a b) ha)
    _ = _ := by simp [Nat.card_Ico, mul_comm]

/-- The paper's maximum and arithmetic mean both have order log log b on all large odd b. -/
def LengthStatisticsTarget : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → Odd b →
    (1/2 : ℝ)*log (log (b:ℝ)) ≤ maxOddMinLength b ∧
    (1/8 : ℝ)*log (log (b:ℝ)) ≤ meanOddMinLength b ∧
    meanOddMinLength b ≤ maxOddMinLength b ∧
    (maxOddMinLength b : ℝ) ≤ C*log (log (b:ℝ))

theorem lengthStatistics_of_short (short : HTarget) : LengthStatisticsTarget := by
  classical
  obtain ⟨C, hC, hshort⟩ := short
  obtain ⟨B, hB⟩ := exists_nat_ge (exp (exp 1))
  refine ⟨2*C, by positivity, max B 3, ?_⟩
  intro b hb ho
  have hb3 : 3 ≤ b := (le_max_right ..).trans hb
  have hb2 : 2 ≤ b := by omega
  have size : exp (exp 1) ≤ (b : ℝ) :=
    hB.trans (by exact_mod_cast (show B ≤ b from (le_max_left ..).trans hb))
  have hlog : 1 ≤ log (log (b:ℝ)) := by
    have h := log_le_log (exp_pos _) size
    rw [log_exp] at h
    simpa using log_le_log (exp_pos 1) h
  have witness (a : ℕ) (ha : a ∈ Ico 1 b) :
      ∃ s, Represents ((a:ℚ)/b) s ∧ s.card = oddMinLength a b := by
    obtain ⟨s,hs,_⟩ := hshort a b hb3 ho (mem_Ico.mp ha).1 (mem_Ico.mp ha).2
    exact leastDenominatorCard_attained ⟨s,hs⟩
  have hnear : b-1 ∈ Ico 1 b := mem_Ico.mpr ⟨by omega,by omega⟩
  have hmax (a : ℕ) (ha : a ∈ Ico 1 b) : oddMinLength a b ≤ maxOddMinLength b :=
    le_sup (f := fun a => oddMinLength a b) ha
  obtain ⟨s, hs, hsc⟩ := witness (b-1) hnear
  have near := near_one_loglog hb2 hs
  rw [hsc] at near
  have maxLower : (1/2 : ℝ)*log (log (b:ℝ)) ≤ maxOddMinLength b := by
    have hm : (oddMinLength (b-1) b : ℝ) ≤ maxOddMinLength b := by exact_mod_cast hmax _ hnear
    linarith
  have hardSub : hardNumerators b ⊆ Ico 1 b := by
    intro a ha
    obtain ⟨haRange,hpos,_⟩ := mem_filter.mp ha
    exact mem_Ico.mpr ⟨hpos,mem_range.mp haRange⟩
  have hardSum : (hardNumerators b).card * (log (log (b:ℝ))/4) ≤
      ∑ a ∈ Ico 1 b, (oddMinLength a b : ℝ) := calc
    _ = ∑ _a ∈ hardNumerators b, (log (log (b:ℝ))/4) := by simp
    _ ≤ ∑ a ∈ hardNumerators b, (oddMinLength a b : ℝ) := by
      apply sum_le_sum
      intro a ha
      obtain ⟨t,ht,htc⟩ := witness a (hardSub ha)
      have hh := (mem_filter.mp ha).2.2 t ht
      rw [htc] at hh
      linarith
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hardSub (fun _ _ _ => by positivity)
  have hcard : b-1 ≤ 2 * (hardNumerators b).card := by
    have maj := hardNumerators_majority hb3 ho
    omega
  have hcardR : ((b-1 : ℕ) : ℝ) ≤ 2 * (hardNumerators b).card := by exact_mod_cast hcard
  have hprod := mul_le_mul_of_nonneg_right hcardR (show 0 ≤ log (log (b:ℝ)) by linarith)
  have aveLower : (1/8 : ℝ)*log (log (b:ℝ)) ≤ meanOddMinLength b := by
    apply (le_div_iff₀ (show 0 < ((b-1 : ℕ) : ℝ) by exact_mod_cast (show 0 < b-1 by omega))).mpr
    nlinarith only [hardSum,hprod]
  refine ⟨maxLower, aveLower, meanOddMinLength_le_max hb2, ?_⟩
  obtain ⟨a,ha,he⟩ := (Ico 1 b).exists_mem_eq_sup ⟨b-1,hnear⟩ (fun a => oddMinLength a b)
  obtain ⟨t,ht,hbound⟩ := hshort a b hb3 ho (mem_Ico.mp ha).1 (mem_Ico.mp ha).2
  have hmin : oddMinLength a b ≤ t.card := leastDenominatorCard_le ht
  have hR : (oddMinLength a b : ℝ) ≤ t.card := by exact_mod_cast hmin
  change (((Ico 1 b).sup (fun a => oddMinLength a b) : ℕ) : ℝ) ≤ _
  rw [he]
  nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hlog)]

end OddEgyptian

