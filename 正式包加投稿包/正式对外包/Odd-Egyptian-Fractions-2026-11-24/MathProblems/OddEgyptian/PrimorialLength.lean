module

public import MathProblems.OddEgyptian.MaximumTheorem
public import MathProblems.OddEgyptian.Finiteness
public import MathProblems.OddEgyptian.LeastLength
public import Mathlib.Data.ENat.Basic
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

theorem firstOddProduct_ge_three_pow (r : ℕ) : 3^r ≤ FirstOddProduct r := by
  induction r with
  | zero => simp [FirstOddProduct]
  | succ r ih =>
    rw [show FirstOddProduct (r+1) = FirstOddProduct r * Nat.nth Nat.Prime (r+1)
      from Finset.prod_range_succ .., pow_succ]
    exact Nat.mul_le_mul ih (by have := Nat.add_two_le_nth_prime (r+1); omega)

theorem log_rank_of_height {r k : ℕ} (hr : 1 ≤ r) (hh : 3^r ≤ height k) :
    (1/2 : ℝ)*Real.log (r : ℝ) ≤ k := by
  have hpow : (3 : ℝ)^r ≤ ((k:ℝ)+1)^(2^k : ℕ) := by exact_mod_cast hh
  have hlog := Real.log_le_log (by positivity : 0 < (3:ℝ)^r) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  have log3 : 1 ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num : 0 < (3:ℝ))).2 Real.exp_one_lt_three.le
  have logK : Real.log ((k:ℝ)+1) ≤ k := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < (k:ℝ)+1)]
  have twoK : (2:ℝ)^k ≤ Real.exp (k:ℝ) := calc
    _ ≤ (Real.exp 1)^k := by
      apply pow_le_pow_left₀ (by norm_num)
      linarith [Real.add_one_le_exp (1:ℝ)]
    _ = _ := by rw [← Real.exp_nat_mul]; simp
  have rk : (r:ℝ) ≤ Real.exp ((k:ℝ)+k) := calc
    _ ≤ (r:ℝ)*Real.log 3 := by nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) r) (sub_nonneg.mpr log3)]
    _ ≤ (2:ℝ)^k*Real.log ((k:ℝ)+1) := hlog
    _ ≤ (2:ℝ)^k*(k:ℝ) := mul_le_mul_of_nonneg_left logK (by positivity)
    _ ≤ Real.exp (k:ℝ)*Real.exp (k:ℝ) := by
      apply mul_le_mul twoK _ (by positivity) (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (k:ℝ)]
    _ = _ := (Real.exp_add ..).symm
  have h := Real.log_le_log (by exact_mod_cast (show 0 < r by omega)) rk
  rw [Real.log_exp] at h
  linarith

theorem length_lower_of_primorial {r : ℕ} (hr : 1 ≤ r) {s : Finset ℕ}
    (hs : Represents 1 s) (hd : FirstOddProduct r ∣ s.sup id) :
    (1/2 : ℝ)*Real.log (r:ℝ) ≤ s.card := by
  have hne : s.Nonempty := by
    by_contra! h
    obtain ⟨_, hs'⟩ := hs
    simp [h] at hs'
  have hmem : s.sup id ∈ s := by simpa using Finset.sup_mem_of_nonempty (f:=id) hne
  have hpos : 0 < s.sup id := by have := hs.1 _ hmem; omega
  have hdiv := Nat.le_of_dvd hpos hd
  have hsBound : s ⊆ Finset.range (height s.card+1) :=
    (Finset.mem_powersetCard.mp (solution_mem_universe (k:=s.card) ⟨s,hs,rfl⟩)).1
  have hheight : s.sup id ≤ height s.card := Nat.le_of_lt_succ (Finset.mem_range.mp (hsBound hmem))
  exact log_rank_of_height hr ((firstOddProduct_ge_three_pow r).trans (hdiv.trans hheight))


theorem length_lower_of_primeFactors {r : ℕ} (hr : 1 ≤ r) {s : Finset ℕ}
    (hs : Represents 1 s) (hrank : r ≤ (s.sup id).primeFactors.card) :
    (1/2 : ℝ)*Real.log (r:ℝ) ≤ s.card := by
  let n := s.sup id
  have hne : s.Nonempty := by
    by_contra! h
    obtain ⟨_, hs'⟩ := hs
    simp [h] at hs'
  have hmem : n ∈ s := by simpa [n] using Finset.sup_mem_of_nonempty (f:=id) hne
  obtain ⟨hn,ho⟩ := hs.1 n hmem
  have hmin {p} (hp : p ∈ n.primeFactors) : 3 ≤ p := by
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hd := Nat.dvd_of_mem_primeFactors hp
    have hne2 := ho.not_two_dvd_nat
    by_contra! h
    obtain rfl : p = 2 := by omega
    exact hne2 hd
  have h3 : 3^r ≤ n := calc
    _ ≤ 3^n.primeFactors.card := Nat.pow_le_pow_right (by decide) hrank
    _ = ∏ _p ∈ n.primeFactors, 3 := by simp
    _ ≤ ∏ p ∈ n.primeFactors, p := Finset.prod_le_prod (fun p hp => hmin hp)
    _ ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
  have hsBound : s ⊆ Finset.range (height s.card+1) :=
    (Finset.mem_powersetCard.mp (solution_mem_universe (k:=s.card) ⟨s,hs,rfl⟩)).1
  exact log_rank_of_height hr (h3.trans (Nat.le_of_lt_succ (Finset.mem_range.mp (hsBound hmem))))

/-- Minimum length subject to a restriction on the largest denominator, with value
infinity when there is no representation. -/
noncomputable def minimumLengthAtMaximum (P : ℕ → Prop) : ℕ∞ := by
  classical
  let witness (s : Finset ℕ) := Represents 1 s ∧ P (s.sup id)
  exact if ∃ s, witness s then (leastDenominatorCard witness : ℕ∞) else ⊤

noncomputable def primorialMinLength (r : ℕ) : ℕ∞ :=
  minimumLengthAtMaximum (fun M => FirstOddProduct r ∣ M)

noncomputable def primeFactorMinLength (r : ℕ) : ℕ∞ :=
  minimumLengthAtMaximum (fun M => r ≤ M.primeFactors.card)

theorem minimumLengthAtMaximum_attained {P : ℕ → Prop}
    (h : ∃ s : Finset ℕ, Represents 1 s ∧ P (s.sup id)) :
    ∃ s : Finset ℕ, Represents 1 s ∧ P (s.sup id) ∧
      minimumLengthAtMaximum P = (s.card : ℕ∞) ∧
      ∀ t : Finset ℕ, Represents 1 t → P (t.sup id) → s.card ≤ t.card := by
  classical
  obtain ⟨s, ⟨hs,hP⟩, he⟩ := leastDenominatorCard_attained h
  refine ⟨s,hs,hP,?_,fun t ht hPt => ?_⟩
  · simp [minimumLengthAtMaximum, h, he]
  · rw [he]
    exact leastDenominatorCard_le ⟨ht,hPt⟩

/-- K and its distinct-prime-factor variant are finite for all sufficiently large r,
and their finite values satisfy (log r)/2 ≤ Kω(r) ≤ K(r) ≤ C log r. -/
def PrimorialLengthTarget : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
    ∃ kω k : ℕ, primeFactorMinLength r = (kω : ℕ∞) ∧ primorialMinLength r = (k : ℕ∞) ∧
      (1/2 : ℝ)*Real.log (r:ℝ) ≤ kω ∧ kω ≤ k ∧ (k:ℝ) ≤ C*Real.log (r:ℝ)

theorem primorialLength_of_maximum (maximum : MaximumTarget) : PrimorialLengthTarget := by
  obtain ⟨C,hC,R,chooseMaximum⟩ := maximum
  refine ⟨C,hC,max R 1,?_⟩
  intro r hr
  have hr1 : 1 ≤ r := (le_max_right ..).trans hr
  obtain ⟨s,hs,hsize,hdiv⟩ := chooseMaximum r ((le_max_left ..).trans hr)
  obtain ⟨t,ht,hmarked,hk,hmin⟩ :=
    minimumLengthAtMaximum_attained (P := fun n => FirstOddProduct r ∣ n) ⟨s,hs,hdiv⟩
  have hne : t.Nonempty := by
    by_contra! hh
    have es := ht.2
    simp [hh] at es
  have hmem : t.sup id ∈ t := by simpa using Finset.sup_mem_of_nonempty (f:=id) hne
  have hn : t.sup id ≠ 0 := by have := (ht.1 _ hmem).1; omega
  have hrank : r ≤ (t.sup id).primeFactors.card := by
    rw [← firstOddProduct_primeFactors_card r]
    exact Finset.card_le_card (Nat.primeFactors_mono hmarked hn)
  obtain ⟨u,hu,huRank,hw,hew⟩ :=
    minimumLengthAtMaximum_attained (P := fun n => r ≤ n.primeFactors.card) ⟨t,ht,hrank⟩
  have hks : (t.card : ℝ) ≤ s.card := by exact_mod_cast hmin s hs hdiv
  exact ⟨u.card,t.card,hw,hk,length_lower_of_primeFactors hr1 hu huRank,
    hew t ht hrank,hks.trans hsize⟩

end OddEgyptian


