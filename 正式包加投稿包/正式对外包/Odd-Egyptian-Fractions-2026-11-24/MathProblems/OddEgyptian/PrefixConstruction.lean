module

public import MathProblems.OddEgyptian.Prefix
public import MathProblems.OddEgyptian.PrefixBudget
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Finset
open scoped BigOperators

/-- The ordinary odd greedy phase starts with a strict gap to the next odd integer.
Representations use the original fraction throughout, including when the residual is zero. -/
structure PrefixState (a b : ℕ) where
  num : ℕ
  den : ℕ
  last : ℕ
  terms : Finset ℕ
  den_pos : 0 < den
  den_odd : Odd den
  last_pos : 0 < last
  last_odd : Odd last
  last_lt_den : last < den
  gap : num*(last+2) < den
  bounded : ∀ x ∈ terms, x ≤ last
  repr : Represents ((a : ℚ)/b-(num : ℚ)/den) terms

private theorem prefix_init_balance {a b L : ℕ} (hb : 0 < b) (hl : L*b ≤ 45045*a) :
    (a : ℚ)/b - ((45045*a-L*b : ℕ) : ℚ)/(45045*(b : ℚ)) = L/45045 := by
  rw [Nat.cast_sub hl]
  push_cast
  field_simp
  ring

/-- Use the first strict crossing among 1/3,...,1/15 to initialize the ordinary phase.
Their sum is 46027/45045 > 1, so there are at most six prefix terms. -/
theorem prefix_initialized {a b : ℕ} (hb : 3 ≤ b) (ho : Odd b) (hab : a < b) :
    ∃ S : PrefixState a b, S.den = 45045*b ∧ S.num ≤ 45045*a ∧ S.terms.card ≤ 6 := by
  have make (L last : ℕ) (p : Finset ℕ) (hp : Represents ((L : ℚ)/45045) p)
      (hlast : Odd last) (h₁ : 0 < last) (h₂ : ∀ x ∈ p, x ≤ last)
      (h₃ : last < 45045*b) (hlo : L*b ≤ 45045*a)
      (hgap : (45045*a-L*b)*(last+2) < 45045*b) (hcard : p.card ≤ 6)
      (hnum : 45045*a-L*b ≤ 45045*a) :
      ∃ S : PrefixState a b, S.den = 45045*b ∧ S.num ≤ 45045*a ∧ S.terms.card ≤ 6 := by
    have heq := prefix_init_balance (show 0 < b by omega) hlo
    refine ⟨⟨45045*a-L*b, 45045*b, last, p, by omega,
      (by decide : Odd 45045).mul ho, h₁, hlast, h₃, hgap, h₂, ?_⟩, rfl, hnum, hcard⟩
    simpa only [Nat.cast_mul, Nat.cast_ofNat, heq] using hp
  by_cases h0 : 45045*a < 15015*b
  · exact make 0 1 ∅ (by constructor; decide; norm_num [Finset.sum_insert]) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by omega)
  by_cases h1 : 45045*a < 24024*b
  · exact make 15015 3 {3} (by constructor; decide; norm_num [Finset.sum_insert]) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by omega)
  by_cases h2 : 45045*a < 30459*b
  · exact make 24024 5 {3,5} (by constructor; decide; norm_num [Finset.sum_insert]) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by omega)
  by_cases h3 : 45045*a < 35464*b
  · exact make 30459 7 {3,5,7} (by constructor; decide; norm_num [Finset.sum_insert]) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by omega)
  by_cases h4 : 45045*a < 39559*b
  · exact make 35464 9 {3,5,7,9} (by constructor; decide; norm_num [Finset.sum_insert]) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by omega)
  by_cases h5 : 45045*a < 43024*b
  · exact make 39559 11 {3,5,7,9,11} (by constructor; decide; norm_num [Finset.sum_insert]) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by omega)
  exact make 43024 13 {3,5,7,9,11,13} (by constructor; decide; norm_num [Finset.sum_insert]) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) (by decide) (by omega)

/-- A stable step, with its three quantities needed for the stopping proof. -/
theorem prefix_advance {a b : ℕ} (s : PrefixState a b) (ha : 0 < s.num) :
    ∃ t : PrefixState a b,
      t.terms.card = s.terms.card + 1 ∧ s.den ≤ t.den ∧ t.den ≤ s.den^2 ∧
      t.num ≤ 2*s.num ∧
      2*((t.num : ℝ)/t.den) ≤ (2*((s.num : ℝ)/s.den))^2 := by
  let q := prefixDenom s.num s.den s.last ha
  obtain ⟨ho, hlast, hle⟩ := prefixDenom_spec s.num s.den s.last ha
  change Odd q at ho
  change s.last < q at hlast
  change s.den ≤ s.num*q at hle
  have hgapPre : s.last+2 < q := by
    by_contra! h
    exact s.gap.not_ge (hle.trans (Nat.mul_le_mul_left _ h))
  have hq5 : 5 ≤ q := by
    have hlp := s.last_pos
    have := Nat.odd_iff.mp ho
    omega
  obtain ⟨hnum, hgap, _⟩ := prefix_ordinary_estimates ha hgapPre hq5
  change s.num*q-s.den < 2*s.num at hnum
  change (s.num*q-s.den)*(q-2) < 2*s.den at hgap
  have hqle : q ≤ s.den := prefixDenom_le_den ha s.den_odd s.last_lt_den
  have hqpos : 0 < q := by omega
  have hdb := s.den_pos
  have hd2 : 1 < s.den := lt_of_le_of_lt s.last_pos s.last_lt_den
  have hnextgap : (s.num*q-s.den)*(q+2) < (s.den*q) := by
    have hpoly : 2*(q+2) ≤ q*(q-2) := by
      obtain ⟨k, hk⟩ : ∃ k, q=k+5 := ⟨q-5, by omega⟩
      rw [hk]
      simp only [show ∀ k : ℕ, k+5-2=k+3 by omega]
      nlinarith [Nat.zero_le (k*k)]
    have H : ((s.num*q-s.den)*(q+2))*(q-2) < (s.den*q)*(q-2) := calc
      _ = ((s.num*q-s.den)*(q-2))*(q+2) := by ring
      _ < (2*s.den)*(q+2) := Nat.mul_lt_mul_of_pos_right hgap (by omega)
      _ = s.den*(2*(q+2)) := by ring
      _ ≤ s.den*(q*(q-2)) := Nat.mul_le_mul_left _ hpoly
      _ = _ := by ring
    exact Nat.lt_of_mul_lt_mul_right H
  have hnot : q ∉ s.terms := by
    intro h
    exact hlast.not_ge (s.bounded q h)
  have hrepr : Represents ((a : ℚ)/b-((s.num*q-s.den : ℕ) : ℚ)/(s.den*q : ℕ)) (insert q s.terms) := by
    constructor
    · intro x hx
      rcases mem_insert.mp hx with rfl | h
      · exact ⟨by omega, ho⟩
      · exact s.repr.1 x h
    · rw [sum_insert hnot, s.repr.2]
      linarith [prefix_step_identity s.den_pos hqpos hle]
  have hr : 2*(((s.num*q-s.den : ℕ) : ℝ)/(s.den*q : ℕ)) ≤ (2*((s.num : ℝ)/s.den))^2 := by
    have hsq : (s.num*q-s.den)*s.den ≤ (2*s.num)*(s.num*q) := Nat.mul_le_mul hnum.le hle
    have hr' : ((s.num*q-s.den : ℕ) : ℝ)*(s.den : ℝ) ≤
        (2*(s.num : ℝ))*((s.num : ℝ)*q) := by exact_mod_cast hsq
    have hden : 0 < (s.den : ℝ) := by exact_mod_cast hdb
    have hQ : 0 < (q : ℝ) := by exact_mod_cast hqpos
    rw [Nat.cast_mul]
    field_simp
    nlinarith
  refine ⟨⟨s.num*q-s.den, s.den*q, q, insert q s.terms, Nat.mul_pos hdb hqpos,
    s.den_odd.mul ho, hqpos, ho, ?_, hnextgap, ?_, hrepr⟩, card_insert_of_notMem hnot,
    ?_, ?_, hnum.le, hr⟩
  · simpa using Nat.mul_lt_mul_of_pos_right hd2 hqpos
  · intro x hx
    rcases mem_insert.mp hx with rfl | h
    · rfl
    · exact (s.bounded x h).trans hlast.le
  · simpa using Nat.mul_le_mul_left s.den (show 1 ≤ q by omega)
  · simpa [pow_two] using Nat.mul_le_mul_left s.den hqle

private theorem prefix_walk {a b : ℕ} (hb : 2^128 ≤ b) (ho : Odd b) (hab : a < b) (T : ℕ) :
    ∃ (j : ℕ) (s : PrefixState a b), j ≤ T ∧ s.terms.card ≤ 6+j ∧
      s.num ≤ 2^j*(45045*a) ∧ b ≤ s.den ∧ s.den ≤ b^6 ∧
      2*((s.num : ℝ)/s.den) ≤ (2/3 : ℝ)^(2^j) ∧
      (s.num=0 ∨ b^3 ≤ s.den ∨ j = T) := by
  have hb3 : 3 ≤ b := (by decide : 3 ≤ 2^128).trans hb
  induction T with
  | zero =>
    obtain ⟨s, he, hnum, hc⟩ := prefix_initialized hb3 ho hab
    have hspos := s.den_pos
    have hln := s.last_pos
    have ha3 : 3*s.num ≤ s.den := by
      calc 3*s.num ≤ (s.last+2)*s.num := Nat.mul_le_mul_right _ (by omega)
           _ ≤ s.den := by simpa [Nat.mul_comm] using s.gap.le
    have hden : s.den ≤ b^6 := by
      rw [he]
      have h45 := (by decide : 45045 ≤ 2^128).trans hb
      calc 45045*b ≤ b*b := Nat.mul_le_mul_right _ h45
           _ = b^2 := by ring
           _ ≤ b^6 := Nat.pow_le_pow_right (by omega) (by decide)
    refine ⟨0, s, by omega, by simpa using hc, by simpa using hnum,
      by rw [he]; omega, hden, ?_, Or.inr (Or.inr rfl)⟩
    simp only [pow_zero, pow_one]
    have hpos : (0:ℝ) < s.den := by exact_mod_cast hspos
    field_simp
    nlinarith [show 3*(s.num:ℝ) ≤ s.den by exact_mod_cast ha3]
  | succ T ih =>
    obtain ⟨j, s, hj, hc, hn, hbmin, hbmax, hr, halt⟩ := ih
    by_cases hz : s.num = 0
    · exact ⟨j, s, by omega, hc, hn, hbmin, hbmax, hr, Or.inl hz⟩
    by_cases hcross : b^3 ≤ s.den
    · exact ⟨j, s, by omega, hc, hn, hbmin, hbmax, hr, Or.inr (Or.inl hcross)⟩
    have heq : j=T := by rcases halt with h | h | h <;> omega
    subst j
    obtain ⟨t, hcard, hd, hsq, hnum, hrate⟩ := prefix_advance s (by omega)
    have hx : t.den ≤ b^6 := calc
      t.den ≤ s.den^2 := hsq
      _ ≤ (b^3)^2 := Nat.pow_le_pow_left (by omega) 2
      _ = b^6 := by ring
    refine ⟨T+1, t, le_rfl, by omega, ?_, hbmin.trans hd, hx, ?_, Or.inr (Or.inr rfl)⟩
    · calc t.num ≤ 2*s.num := hnum
           _ ≤ 2*(2^T*(45045*a)) := Nat.mul_le_mul_left _ hn
           _ = 2^(T+1)*(45045*a) := by ring
    · have hnon : 0 ≤ 2*((s.num : ℝ)/s.den) := by positivity
      calc
        2*((t.num : ℝ)/t.den) ≤ (2*((s.num : ℝ)/s.den))^2 := hrate
        _ ≤ ((2/3 : ℝ)^(2^T))^2 := pow_le_pow_left₀ hnon hr 2
        _ = (2/3 : ℝ)^(2^(T+1)) := by rw [← pow_mul, pow_succ]

/-- A fixed crossing among the first seven odd denominators and a bounded run of stable
odd greedy steps supply the complete quantitative prefix required by the bridge to H. -/
theorem quantitativePrefix : QuantitativePrefixTarget := by
  refine ⟨80, by norm_num, fun bS ↦ ⟨max bS (2^128), ?_⟩⟩
  intro a b hb0 hb3 ho ha hab
  have hbig : 2^128 ≤ b := (le_max_right ..).trans hb0
  have hcut : bS ≤ b := (le_max_left ..).trans hb0
  obtain ⟨T, hnum, hdecay, hlen⟩ := prefix_horizon b hbig
  obtain ⟨j, s, hj, hc, hn, hmin, hmax, hrate, halt⟩ := prefix_walk hbig ho hab T
  have hsize : s.terms.card ≤ 6+T := hc.trans (by omega)
  refine ⟨s.terms, s.num, s.den, s.repr,
    (by exact_mod_cast hsize : (s.terms.card : ℝ) ≤ 6+(T : ℝ)) |>.trans hlen, ?_⟩
  by_cases hz : s.num=0
  · exact Or.inl hz
  have hcross : b^3 ≤ s.den := by
    by_contra! h
    have hjT : j=T := by rcases halt with h' | h' | h' <;> omega
    rw [hjT] at hrate
    have hh := (mul_le_mul_of_nonneg_right hrate (by positivity : 0 ≤ (b:ℝ)^3)).trans hdecay
    have hd : (0:ℝ) < s.den := by exact_mod_cast s.den_pos
    have hnum1 : (1:ℝ) ≤ s.num := by exact_mod_cast (show 1 ≤ s.num by omega)
    have hbd : (s.den : ℝ) < (b : ℝ)^3 := by exact_mod_cast h
    field_simp at hh
    nlinarith [mul_nonneg (sub_nonneg.mpr hnum1) (by positivity : 0 ≤ (b:ℝ)^3)]
  have H : s.num ≤ (45045*2^T)*b := calc
    s.num ≤ 2^j*(45045*a) := hn
    _ ≤ 2^T*(45045*b) := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hj)
      (Nat.mul_le_mul_left _ hab.le)
    _ = (45045*2^T)*b := by ring
  have Hsq : s.num^2 ≤ b^3 := calc
    s.num^2 ≤ ((45045*2^T)*b)^2 := Nat.pow_le_pow_left H _
    _ = (45045*2^T)^2 * b^2 := by ring
    _ ≤ b*b^2 := Nat.mul_le_mul_right _ hnum
    _ = b^3 := by ring
  refine Or.inr ⟨by omega, Hsq.trans hcross, hcut.trans hmin, hb3.trans hmin, s.den_odd, hmax, ?_⟩
  intro x hx
  have hxpos : 0 < x := by have := (s.repr.1 x hx).1; omega
  have hpre : s.num*x < s.den := (Nat.mul_le_mul_left _ (show x ≤ s.last+2 by
    have := s.bounded x hx; omega)).trans_lt s.gap
  apply (div_lt_div_iff₀ (by exact_mod_cast s.den_pos) (by exact_mod_cast hxpos)).mpr
  simpa using (show (s.num : ℚ)*x < s.den by exact_mod_cast hpre)

/-- H is reduced entirely to the small-numerator construction and the classical odd tail basis. -/
theorem hTarget_of_small_and_basis (small : SmallNumeratorTarget) (basis : OddTailBasis) : HTarget :=
  hTarget_of_prefix_and_small quantitativePrefix small basis

end OddEgyptian

