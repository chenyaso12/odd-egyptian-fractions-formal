module

public import MathProblems.OddEgyptian.Prefix
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Finset
open scoped BigOperators

/-- The low-to-high digit at position i, with zeros past the leading digit. -/
def baseDigit (B z i : ℕ) : ℕ := z / B ^ i % B

theorem baseDigit_lt {B : ℕ} (hB : 0 < B) (z i : ℕ) : baseDigit B z i < B :=
  Nat.mod_lt _ hB

theorem digits_with_quotient (B z L : ℕ) :
    (∑ i ∈ range L, baseDigit B z i * B ^ i) + (z / B ^ L) * B ^ L = z := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, add_assoc]
    have hd := Nat.mod_add_div (z / B ^ L) B
    change _ + ((z / B ^ L % B) * B ^ L + (z / B ^ (L+1)) * B ^ (L+1)) = z
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    calc
      _ = (∑ i ∈ range L, baseDigit B z i * B ^ i) +
            ((z / B ^ L % B) + B * (z / B ^ L / B)) * B ^ L := by ring
      _ = z := by rw [hd]; exact ih

theorem digits_sum_of_lt {B z L : ℕ} (hz : z < B ^ L) :
    (∑ i ∈ range L, baseDigit B z i * B ^ i) = z := by
  simpa only [Nat.div_eq_of_lt hz, zero_mul, add_zero] using digits_with_quotient B z L

/-- The same expansion after division by W B^L; all occupied layer labels L-i are positive. -/
theorem scaled_digits_sum {B z L W : ℕ} (hB : 0 < B) (hW : 0 < W) (hz : z < B ^ L) :
    (∑ i ∈ range L, (baseDigit B z i : ℚ) / ((W : ℚ) * (B : ℚ) ^ (L - i))) =
    (z : ℚ) / ((W : ℚ) * (B : ℚ) ^ L) := by
  have hBr : (B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have hWr : (W : ℚ) ≠ 0 := by exact_mod_cast hW.ne'
  have repr : (∑ i ∈ range L, (baseDigit B z i : ℚ) * (B : ℚ) ^ i) = (z : ℚ) := by
    exact_mod_cast digits_sum_of_lt hz
  rw [← repr, Finset.sum_div]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  have hpow : (B : ℚ) ^ L = (B : ℚ) ^ i * (B : ℚ) ^ (L - i) := by
    rw [← pow_add, Nat.add_sub_of_le hi'.le]
  rw [hpow]
  field_simp

/-- The Euclidean quotient and remainder both fit in L places and supply the two
families of digits arising from a/b. -/
theorem euclidean_digit_layers {a b B N L : ℕ} (hb : 0 < b) (hB : 0 < B) (hN : 0 < N)
    (hsmall : a * N < b) (hcover : b ≤ B ^ L) :
    ∃ d e : ℕ, d < B ^ L ∧ e < B ^ L ∧
      (a : ℚ) / (b : ℚ) =
        (∑ i ∈ range L, (baseDigit B d i : ℚ) / ((N : ℚ) * (B : ℚ) ^ (L - i))) +
        ∑ i ∈ range L, (baseDigit B e i : ℚ) / (((b * N : ℕ) : ℚ) * (B : ℚ) ^ (L - i)) := by
  let X := a * N * B ^ L
  let d := X / b
  let e := X % b
  have hd : d < B ^ L := (Nat.div_lt_iff_lt_mul hb).mpr (by
    simpa [X, mul_comm b] using Nat.mul_lt_mul_of_pos_right hsmall (pow_pos hB L))
  have he : e < B ^ L := (Nat.mod_lt X hb).trans_le hcover
  refine ⟨d, e, hd, he, ?_⟩
  rw [scaled_digits_sum hB hN hd, scaled_digits_sum hB (Nat.mul_pos hb hN) he]
  have hx : e + b * d = a * N * B ^ L := Nat.mod_add_div X b
  have hxq : (e : ℚ) + b * d = a * N * (B : ℚ) ^ L := by exact_mod_cast hx
  have hbr : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hBr : (B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have hNr : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp
  linear_combination -hxq

/-- Label (false,j) for the first quotient family and (true,j) for the second. -/
def layerDen (b B : ℕ) (tag : Bool × ℕ) (c : ℕ) : ℕ :=
  B ^ tag.2 * ((if tag.1 then b else 1) * c)

theorem layer_factorization {b B c : ℕ} (hB : B.Prime) (hb : ¬ B ∣ b)
    (hc : ¬ B ∣ c) (tag : Bool × ℕ) :
    (layerDen b B tag c).factorization B = tag.2 := by
  have hnf : ¬ B ∣ (if tag.1 then b else 1) * c := by
    apply mt hB.dvd_mul.mp
    have hb1 : ¬ B ∣ 1 := fun h => hB.not_dvd_one h
    cases tag.1 <;> simp [hb, hb1, hc]
  have hpos : (if tag.1 then b else 1) * c ≠ 0 := fun h => hnf (h ▸ dvd_zero B)
  simp only [layerDen, Nat.factorization_mul (pow_ne_zero _ hB.ne_zero) hpos,
    Finsupp.add_apply, Nat.factorization_pow_self hB, Nat.factorization_eq_zero_of_not_dvd hnf,
    add_zero]

/-- The valuation recovers j. Among positive coefficients below b, the size of the
coefficient after removing B^j recovers the Boolean label. -/
theorem layer_tag_unique {b B c d : ℕ} (hB : B.Prime) (hb : ¬ B ∣ b)
    (hc : ¬ B ∣ c) (hd : ¬ B ∣ d) (hcPos : 0 < c) (hdPos : 0 < d)
    (hcSmall : c < b) (hdSmall : d < b) {p q : Bool × ℕ}
    (eq : layerDen b B p c = layerDen b B q d) : p = q := by
  have hlevel : p.2 = q.2 := (layer_factorization hB hb hc p).symm.trans
    ((congrArg (fun n : ℕ => n.factorization B) eq).trans (layer_factorization hB hb hd q))
  obtain ⟨u, j⟩ := p
  obtain ⟨v, k⟩ := q
  change j = k at hlevel
  subst k
  have hcoeff := Nat.eq_of_mul_eq_mul_left (pow_pos hB.pos j) eq
  have hbc : b ≤ b * c := by simpa using Nat.mul_le_mul_left b hcPos
  have hbd : b ≤ b * d := by simpa using Nat.mul_le_mul_left b hdPos
  cases u <;> cases v <;> simp_all
  omega

/-- Fix all templates before choosing b and B. Input blocks may contain repetitions;
different output blocks have disjoint supports, and their cardinalities add. -/
theorem fixedTemplatesAcrossLayers (basis : OddTailBasis) (h : ℕ) :
    ∃ F R : ℕ, ∀ {ι : Type} [Fintype ι] (tag : ι ↪ Bool × ℕ)
      {b B W : ℕ}, B.Prime → ¬ B ∣ b → R < B → W * R < b → ∀ raw : ι → List ℕ,
      (∀ i, (raw i).length ≤ h) → (∀ i x, x ∈ raw i → Odd x) →
      (∀ i x, x ∈ raw i → ∃ c : ℕ, 0 < c ∧ c ≤ W ∧ ¬ B ∣ c ∧ x = layerDen b B (tag i) c) →
      ∃ out : Finset ℕ, Represents (∑ i, listReciprocalSum (raw i)) out ∧
        out.card ≤ Fintype.card ι * F := by
  classical
  obtain ⟨F, R, T⟩ := fixedBlockTemplates basis h
  refine ⟨F, R, ?_⟩
  intro ι inst tag b B W hB hb hR hsep raw hlen hood hraw
  choose blocks represents card origin using fun i => T (raw i) (hlen i) (hood i)
  have refine_coeff {i : ι} {y : ℕ} (hy : y ∈ blocks i) :
      ∃ c : ℕ, 0 < c ∧ c < b ∧ ¬ B ∣ c ∧ y = layerDen b B (tag i) c := by
    obtain ⟨x, hx, s, hs, hsR, _, hyx⟩ := origin i y hy
    obtain ⟨c, hc, hcW, hnc, hxc⟩ := hraw i x hx
    have hs0 : 0 < s := by omega
    have hns : ¬ B ∣ s := fun hd => (not_le_of_gt (hsR.trans_lt hR)) (Nat.le_of_dvd hs0 hd)
    refine ⟨c * s, Nat.mul_pos hc hs0, (Nat.mul_le_mul hcW hsR).trans_lt hsep,
      fun hd => (hB.dvd_mul.mp hd).elim hnc hns, ?_⟩
    rw [hyx, hxc]
    simp [layerDen, mul_assoc]
  have disj : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint blocks := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    obtain ⟨c, hc, hcb, hcB, hxc⟩ := refine_coeff hi
    obtain ⟨d, hd, hdb, hdB, hxd⟩ := refine_coeff hj
    exact hij (tag.injective (layer_tag_unique hB hb hcB hdB hc hd hcb hdb (hxc.symm.trans hxd)))
  refine ⟨Finset.univ.biUnion blocks, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, _, hix⟩ := Finset.mem_biUnion.mp hx
    exact (represents i).1 x hix
  · rw [Finset.sum_biUnion disj]
    exact Finset.sum_congr rfl fun i _ => (represents i).2
  · rw [Finset.card_biUnion disj]
    exact (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => card i)).trans_eq
      (by simp)

/-- Unit-denominator form of a digit after dividing it by the common multiple N.
Repetitions and the empty list are allowed. -/
def NormalizedDigits (B N h : ℕ) : Prop :=
  ∀ m < B, ∃ cs : List ℕ, cs.length ≤ h ∧ listReciprocalSum cs = (m : ℚ) / N ∧
    ∀ c ∈ cs, Odd c ∧ c ≤ N ^ 2 ∧ ¬ B ∣ c

private theorem listReciprocalSum_explicit (xs : List ℕ) :
    listReciprocalSum xs = (xs.map fun x : ℕ => (1 : ℚ) / (x : ℚ)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (1 : ℚ) / (x : ℚ) + listReciprocalSum xs = _ + _
    rw [ih]
    rfl

private theorem scale_block_sum (b B : ℕ) (tag : Bool × ℕ) (cs : List ℕ) :
    listReciprocalSum (cs.map (layerDen b B tag)) =
      listReciprocalSum cs / ((if tag.1 then b else 1 : ℕ) : ℚ) / (B : ℚ) ^ tag.2 := by
  induction cs with
  | nil => simp [listReciprocalSum]
  | cons c cs ih =>
    simp only [listReciprocalSum_explicit, List.map_cons, List.sum_cons] at ih ⊢
    rw [add_div, add_div, ← ih]
    simp only [layerDen, Nat.cast_mul, Nat.cast_pow, div_eq_mul_inv, mul_inv_rev, one_mul]

/-- The whole finite D/T/I-to-S step. The bound is 2*L*F uniform in all digits and in a.
Only the numerical choice of parameters and the existence of the individual digits
are supplied by the caller. -/
theorem finiteSmallNumerator (basis : OddTailBasis) (h : ℕ) :
    ∃ F R : ℕ, ∀ {a b B N L : ℕ}, Odd b → Nat.Prime B → Odd B → ¬ B ∣ b →
      0 < N → a * N < b → b ≤ B ^ L → R < B → N ^ 2 * R < b → NormalizedDigits B N h →
      ∃ out : Finset ℕ, Represents ((a : ℚ) / b) out ∧ out.card ≤ (2 * L) * F := by
  classical
  obtain ⟨F, R, glue⟩ := fixedTemplatesAcrossLayers basis h
  refine ⟨F, R, ?_⟩
  intro a b B N L hob hprime hoB hbb hN hsmall hcover hR hsep digits
  obtain ⟨d, e, _, _, hsum⟩ := euclidean_digit_layers hob.pos hprime.pos hN hsmall hcover
  let label : (Bool × Fin L) ↪ Bool × ℕ :=
    ⟨fun t => (t.1, L - t.2.val), by
      rintro ⟨p, i⟩ ⟨q, j⟩ heq
      have hp : p = q := congrArg Prod.fst heq
      have hij : L - i.val = L - j.val := congrArg Prod.snd heq
      have hfin : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
      simp [hp, hfin]⟩
  let m (t : Bool × Fin L) := baseDigit B (if t.1 then e else d) t.2.val
  choose cs len sums prop using fun t : Bool × Fin L => digits (m t) (baseDigit_lt hprime.pos _ _)
  let raw (t : Bool × Fin L) := (cs t).map (layerDen b B (label t))
  have hlen (t) : (raw t).length ≤ h := by simpa [raw] using len t
  have horig (t) (x : ℕ) (hx : x ∈ raw t) :
      ∃ c : ℕ, 0 < c ∧ c ≤ N ^ 2 ∧ ¬ B ∣ c ∧ x = layerDen b B (label t) c := by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ho, hbound, hn⟩ := prop t c hc
    exact ⟨c, ho.pos, hbound, hn, rfl⟩
  have hodd (t) (x : ℕ) (hx : x ∈ raw t) : Odd x := by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have hc' := (prop t c hc).1
    change Odd (B ^ (label t).2 * ((if (label t).1 then b else 1) * c))
    apply hoB.pow.mul
    split
    · exact hob.mul hc'
    · simpa using hc'
  obtain ⟨out, hout, hc⟩ := glue label hprime hbb hR hsep raw hlen hodd horig
  refine ⟨out, ?_, by simpa using hc⟩
  have hm (t : Bool × Fin L) : listReciprocalSum (raw t) =
      (m t : ℚ) / (((if t.1 then b * N else N : ℕ) : ℚ) * (B : ℚ) ^ (L - t.2.val)) := by
    simp only [raw, scale_block_sum, sums]
    rcases t with ⟨p, i⟩
    cases p
    · change (m (false, i) : ℚ) / N / 1 / (B : ℚ) ^ (L - i.val) = _
      simp only [Bool.false_eq_true, ↓reduceIte,
        div_eq_mul_inv, mul_inv_rev]
      ring
    · change (m (true, i) : ℚ) / N / b / (B : ℚ) ^ (L - i.val) = _
      simp only [↓reduceIte, Nat.cast_mul,
        div_eq_mul_inv, mul_inv_rev]
      ring
  have htotal : (∑ t, listReciprocalSum (raw t)) = (a : ℚ) / b := by
    simp_rw [hm]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, hsum]
    simp only [m, ↓reduceIte, Bool.false_eq_true]
    rw [Fin.sum_univ_eq_sum_range (fun i => (baseDigit B e i : ℚ) /
        (((b * N : ℕ) : ℚ) * (B : ℚ) ^ (L - i))) L,
      Fin.sum_univ_eq_sum_range (fun i => (baseDigit B d i : ℚ) /
        ((N : ℚ) * (B : ℚ) ^ (L - i))) L, add_comm]
  rwa [htotal] at hout

/-- Fractional digit interface: z divides N, w is odd, w ≤ N and B does not divide w.
The full number-theoretic digit lemma additionally constructs the parameters. -/
def FractionDigits (B N h : ℕ) : Prop :=
  ∀ m < B, ∃ terms : List (ℕ × ℕ), terms.length ≤ h ∧
    (terms.map fun t => (t.1 : ℚ) / t.2).sum = (m : ℚ) ∧
    ∀ t ∈ terms, t.1 ∣ N ∧ Odd t.2 ∧ t.2 ≤ N ∧ ¬ B ∣ t.2

/-- Convert each digit fraction z/w into one reciprocal with denominator (N/z)w.
Cardinality is preserved even when different terms have the same denominator. -/
theorem normalizeDigitFractions {B N h : ℕ} (prime : Nat.Prime B) (oddN : Odd N)
    (notDivide : ¬ B ∣ N) (digits : FractionDigits B N h) : NormalizedDigits B N h := by
  intro m hm
  obtain ⟨terms, len, hsum, spec⟩ := digits m hm
  let coeff (t : ℕ × ℕ) := (N / t.1) * t.2
  have hc (t : ℕ × ℕ) (ht : t ∈ terms) :
      Odd (coeff t) ∧ coeff t ≤ N ^ 2 ∧ ¬ B ∣ coeff t := by
    obtain ⟨hz, hw, hwN, hBw⟩ := spec t ht
    have hk := Nat.div_mul_cancel hz
    have ho : Odd (N / t.1 * t.1) := by simpa only [hk] using oddN
    have hBz : ¬ B ∣ N / t.1 := fun h => notDivide (h.trans (Nat.div_dvd_of_dvd hz))
    refine ⟨(Nat.odd_mul.mp ho).1.mul hw, ?_, fun h => (prime.dvd_mul.mp h).elim hBz hBw⟩
    simpa only [coeff, pow_two] using Nat.mul_le_mul (Nat.div_le_self N t.1) hwN
  have hvalue (t : ℕ × ℕ) (ht : t ∈ terms) :
      (1 : ℚ) / (coeff t : ℚ) = ((t.1 : ℚ) / t.2) / N := by
    obtain ⟨hz, hw, _, _⟩ := spec t ht
    let k := N / t.1
    have hkNat : k * t.1 = N := Nat.div_mul_cancel hz
    have ho : Odd (k * t.1) := by simpa only [hkNat] using oddN
    have hz0 : (t.1 : ℚ) ≠ 0 := by exact_mod_cast (Nat.odd_mul.mp ho).2.pos.ne'
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.odd_mul.mp ho).1.pos.ne'
    have hw0 : (t.2 : ℚ) ≠ 0 := by exact_mod_cast hw.pos.ne'
    have hkQ : (k : ℚ) * t.1 = N := by exact_mod_cast hkNat
    change (1 : ℚ) / ((k * t.2 : ℕ) : ℚ) = _
    rw [Nat.cast_mul, ← hkQ]
    field_simp
  refine ⟨terms.map coeff, by simpa using len, ?_, ?_⟩
  · rw [listReciprocalSum_explicit]
    rw [List.map_map]
    have heq : terms.map ((fun n : ℕ => (1 : ℚ) / n) ∘ coeff) =
        terms.map (fun t => ((t.1 : ℚ) / t.2) / N) :=
      List.map_congr_left hvalue
    rw [heq]
    calc
      _ = (terms.map fun t => (t.1 : ℚ) / t.2).sum / N := by
        simpa only [div_eq_mul_inv] using
          (List.sum_map_mul_right terms (fun t : ℕ × ℕ => (t.1 : ℚ) / t.2) ((N : ℚ)⁻¹))
      _ = _ := by rw [hsum]
  · intro c hmem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    exact hc t ht

/-- Numerical and digit content needed from D: the same prime, scale and number of
places work for every digit and every numerator for this denominator. -/
def LayeredDigitTarget : Prop :=
  ∃ h : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ R : ℕ, ∃ b₀ : ℕ, ∀ b : ℕ,
    b₀ ≤ b → 3 ≤ b → Odd b → ∃ B N L : ℕ,
      B.Prime ∧ Odd B ∧ Odd N ∧ ¬ B ∣ b ∧ ¬ B ∣ N ∧
      N ^ 2 < b ∧ b ≤ B ^ L ∧ R < B ∧ N ^ 2 * R < b ∧
      (L : ℝ) ≤ K * Real.log (Real.log b) ∧ FractionDigits B N h

/-- Conditional D/T/I ⇒ S with all input-independent constants and the target
actually used by the prefix module. -/
theorem smallNumerator_of_layeredDigits (basis : OddTailBasis) (supply : LayeredDigitTarget) :
    SmallNumeratorTarget := by
  obtain ⟨h, K, hK, supply⟩ := supply
  obtain ⟨F, R, finite⟩ := finiteSmallNumerator basis h
  obtain ⟨b₀, supply⟩ := supply R
  refine ⟨b₀, 2 * ((F : ℝ) + 1) * K, by positivity, ?_⟩
  intro a b hlarge hb3 hob ha ha2
  obtain ⟨B, N, L, prime, hoB, hoN, hBb, hBN, hN2, cover, hR, sep, layers, frac⟩ :=
    supply b hlarge hb3 hob
  have hsmall : a * N < b := by
    by_contra! hle
    have h₁ := Nat.mul_le_mul hle hle
    have h₂ := Nat.mul_lt_mul_of_pos_left hN2 (pow_pos ha 2)
    have h₃ := Nat.mul_le_mul_right b ha2
    nlinarith
  obtain ⟨out, rep, card⟩ := finite hob prime hoB hBb hoN.pos hsmall cover hR sep
    (normalizeDigitFractions prime hoN hBN frac)
  refine ⟨out, rep, ?_⟩
  have hc : (out.card : ℝ) ≤ 2 * L * F := by exact_mod_cast card
  calc
    _ ≤ 2 * (L : ℝ) * F := hc
    _ ≤ (2 * ((F : ℝ) + 1)) * L := by nlinarith [show (0 : ℝ) ≤ L by positivity]
    _ ≤ (2 * ((F : ℝ) + 1)) * (K * Real.log (Real.log b)) :=
      mul_le_mul_of_nonneg_left layers (by positivity)
    _ = _ := by ring

end OddEgyptian
