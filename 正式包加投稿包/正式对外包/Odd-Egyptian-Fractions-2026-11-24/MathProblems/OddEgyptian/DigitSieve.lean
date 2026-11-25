module

public import MathProblems.OddEgyptian.DigitInputs
public import MathProblems.OddEgyptian.BadPrimes
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

public section

namespace OddEgyptian

private theorem too_many_triples {m : ℕ} (F bad : Finset ℕ)
    (hbad : ∀ p ≤ m, p.Prime → ¬ NatResidueGood F p → p ∈ bad)
    (hcount : 3*(m+1)*bad.card < (threePrimeReps m).card) : ThreeGood F m := by
  classical
  by_contra hnone
  let pool := bad ×ˢ Finset.range (m+1)
  let left := pool.image (fun (p,q) => (p,q,m-(p+q)))
  let middle := pool.image (fun (p,q) => (q,p,m-(q+p)))
  let right := pool.image (fun (p,q) => (q,m-(p+q),p))
  have sub : threePrimeReps m ⊆ (left ∪ middle) ∪ right := by
    rintro ⟨p,q,t⟩ hx
    obtain ⟨_, hsum, hp, hop, hq, hoq, ht, hot⟩ := Finset.mem_filter.mp hx
    change p+q+t=m at hsum
    have hm (x) (hx : x ≤ m) : x ∈ Finset.range (m+1) := Finset.mem_range.mpr (by omega)
    by_cases bp : NatResidueGood F p
    · by_cases bq : NatResidueGood F q
      · have bt : ¬ NatResidueGood F t := fun bt =>
          hnone ⟨p,q,t,⟨hp,hop,bp⟩,⟨hq,hoq,bq⟩,⟨ht,hot,bt⟩,hsum⟩
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨(t,p),Finset.mem_product.mpr ⟨hbad t (by omega) ht bt,hm p (by omega)⟩,
          by simp; omega⟩
      · apply Finset.mem_union_left; apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨(q,p),Finset.mem_product.mpr ⟨hbad q (by omega) hq bq,hm p (by omega)⟩,
          by simp; omega⟩
    · apply Finset.mem_union_left; apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(p,q),Finset.mem_product.mpr ⟨hbad p (by omega) hp bp,hm q (by omega)⟩,
        by simp; omega⟩
  have h1 : left.card ≤ pool.card := Finset.card_image_le
  have h2 : middle.card ≤ pool.card := Finset.card_image_le
  have h3 : right.card ≤ pool.card := Finset.card_image_le
  have h4 := Finset.card_le_card sub
  have h5 := Finset.card_union_le left middle
  have h6 := Finset.card_union_le (left ∪ middle) right
  have hpool : pool.card = (m+1)*bad.card := by simp [pool, mul_comm]
  rw [show 3*(m+1)*bad.card=3*((m+1)*bad.card) by ring] at hcount
  omega

/-- Removing ordered triples containing a bad prime works for the same fixed F
at every truncation point m. The threshold bound deliberately uses weak constants. -/
theorem goodTriple_of_count (m P : ℕ) (F : Finset ℕ) (v y : ℝ)
    (hm : 7 ≤ m) (hP : 0 < P) (hbound : ∀ x ∈ F, x ≤ P)
    (hlogP : Real.log (P : ℝ) ≤ 2*y)
    (hsize : 2*(m:ℝ)^(3/4:ℝ) ≤ (F.card:ℝ))
    (hcount : v*(m:ℝ)^2 / (Real.log (m:ℝ))^3 ≤ ((threePrimeReps m).card:ℝ))
    (herror : (24 / Real.log 2)*y*(Real.log (m:ℝ))^3 < v*(m:ℝ)^(1/4:ℝ)) :
    ThreeGood F m := by
  classical
  let bad := (Nat.primesLE m).filter fun p => ¬NatResidueGood F p
  let L := ⌊(m:ℝ)^(3/4:ℝ)⌋₊
  have hm1 : (1:ℝ) < m := by exact_mod_cast (show 1<m by omega)
  have hl2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hml := Real.log_pos hm1
  have hL : (L:ℝ) ≤ (m:ℝ)^(3/4:ℝ) := Nat.floor_le (by positivity)
  have hFpos : 0 < F.card := by
    exact_mod_cast (show (0:ℝ)<F.card by linarith [Real.rpow_pos_of_pos (by positivity : (0:ℝ)<m) (3/4:ℝ)])
  have hbad := bad_prime_count F bad P L hFpos (by exact_mod_cast (show 2*(L:ℝ) ≤ F.card by linarith))
    hbound (fun p hp => (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2) (by
      intro p hp
      obtain ⟨hmemp,hpoor⟩ := Finset.mem_filter.mp hp
      apply Nat.le_floor
      have hp' : p ≤ m := (Nat.mem_primesLE.mp hmemp).1
      exact (le_of_not_gt hpoor).trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hp') (by norm_num)))
  have hPl : (Nat.log 2 P : ℝ) ≤ (2*y)/Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    have h := Nat.pow_log_le_self 2 hP.ne'
    have h' : (2:ℝ)^(Nat.log 2 P) ≤ P := by exact_mod_cast h
    have h'' := Real.log_le_log (by positivity) h'
    rw [Real.log_pow] at h''
    exact h''.trans hlogP
  apply too_many_triples F bad (fun p hp hprime hn => Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hp,hprime⟩,hn⟩)
  have hm0 := hm1.le.trans' (by norm_num : (0:ℝ)≤1)
  have hbad' : (bad.card : ℝ) ≤ 2*(m:ℝ)^(3/4:ℝ)*((2*y)/Real.log 2) := calc
    _ ≤ 2*(L:ℝ)*(Nat.log 2 P : ℝ) := by exact_mod_cast hbad
    _ ≤ _ := by gcongr
  have hnonneg : 0 ≤ ((2*y)/Real.log 2) := (Nat.cast_nonneg _).trans hPl
  have hbound' : 3*((m:ℝ)+1)*bad.card ≤
      (m:ℝ)^(7/4:ℝ)*((24/Real.log 2)*y) := calc
    _ ≤ 3*(2*(m:ℝ))*(2*(m:ℝ)^(3/4:ℝ)*((2*y)/Real.log 2)) := by
      apply mul_le_mul _ hbad' (by positivity) (by positivity)
      linarith
    _ = _ := by
      rw [show (7/4:ℝ) = 1 + 3/4 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]; ring
  have hpos : (0:ℝ)<(m:ℝ)^(7/4:ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hex : (m:ℝ)^(7/4:ℝ) * (m:ℝ)^(1/4:ℝ) = (m:ℝ)^2 := by
    rw [← Real.rpow_add (by positivity), show (7/4:ℝ)+1/4 = (2:ℕ) by norm_num, Real.rpow_natCast]
  have hlt : (m:ℝ)^(7/4:ℝ)*((24/Real.log 2)*y) < v*(m:ℝ)^2/(Real.log (m:ℝ))^3 := by
    apply (lt_div_iff₀ (pow_pos hml 3)).mpr
    calc
      _ = (m:ℝ)^(7/4:ℝ)*((24/Real.log 2)*y*(Real.log (m:ℝ))^3) := by ring
      _ < (m:ℝ)^(7/4:ℝ)*(v*(m:ℝ)^(1/4:ℝ)) := mul_lt_mul_of_pos_left herror hpos
      _ = _ := by rw [← hex]; ring
  exact_mod_cast (hbound'.trans_lt (hlt.trans_le hcount))

end OddEgyptian
