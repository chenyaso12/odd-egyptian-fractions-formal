module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

public section

namespace OddEgyptian

private def planeDot {K : Type*} [Field K] (v z : K × K) : K :=
  v.1 * z.1 + v.2 * z.2

private theorem planeLine_card {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (a : K) (v : K × K) (hv : v ≠ 0) :
    (Finset.univ.filter (fun z ↦ planeDot v z = a)).card = Fintype.card K := by
  classical
  rcases v with ⟨b,c⟩
  by_cases hc : c = 0
  · subst c
    have hb : b ≠ 0 := by rintro rfl; exact hv rfl
    have hset : Finset.univ.filter (fun z ↦ planeDot (b,0) z = a) =
        (Finset.univ : Finset K).image (fun y ↦ (a / b, y)) := by
      ext z
      rcases z with ⟨x,y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        planeDot, zero_mul, add_zero, Prod.mk.injEq]
      constructor
      · exact fun h ↦ ⟨y, (div_eq_iff hb).mpr (by simpa [mul_comm] using h.symm), rfl⟩
      · rintro ⟨_, h, rfl⟩
        rw [← h]
        field_simp
    rw [hset, Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.snd h)]
    simp
  · have hset : Finset.univ.filter (fun z ↦ planeDot (b,c) z = a) =
        (Finset.univ : Finset K).image (fun x ↦ (x, (a - b*x) / c)) := by
      ext z
      rcases z with ⟨x,y⟩
      constructor
      · intro hz
        have h := (Finset.mem_filter.mp hz).2
        change b * x + c * y = a at h
        apply Finset.mem_image.mpr
        refine ⟨x, Finset.mem_univ _, Prod.ext rfl ((div_eq_iff hc).mpr ?_)⟩
        linear_combination -h
      · intro hz
        obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hz
        rw [← hw]
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change b * w + c * ((a - b*w) / c) = a
        field_simp
        ring
    rw [hset, Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h)]
    simp

private theorem planeLine_intersection {K : Type*} [Field K] {a : K} (ha : a ≠ 0)
    {v w z z' : K × K} (hvw : v ≠ w)
    (hv : planeDot v z = a) (hw : planeDot w z = a)
    (hv' : planeDot v z' = a) (hw' : planeDot w z' = a) : z = z' := by
  rcases v with ⟨b,c⟩
  rcases w with ⟨d,e⟩
  rcases z with ⟨x,y⟩
  rcases z' with ⟨x',y'⟩
  simp only [planeDot] at hv hw hv' hw'
  have hdet : b*e - c*d ≠ 0 := by
    intro he
    apply hvw
    have h1 : (b-d)*a = 0 := by linear_combination d*hv - b*hw + y*he
    have h2 : (c-e)*a = 0 := by linear_combination e*hv - c*hw - x*he
    exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right ha))
      (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right ha))
  have h1 : (b*e - c*d)*(x-x') = 0 := by linear_combination e*(hv-hv') - c*(hw-hw')
  have h2 : (b*e - c*d)*(y-y') = 0 := by linear_combination b*(hw-hw') - d*(hv-hv')
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hdet))
    (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hdet))

/-- If all lines lie in a set of points and meet pairwise in at most one point,
its cardinality satisfies this second-moment bound. -/
private theorem incidence_bound {I V : Type*} [DecidableEq I] [DecidableEq V]
    (L : Finset I) (T : Finset V) (rel : I → V → Prop) [DecidableRel rel]
    (q : ℕ) (hL : 0 < L.card)
    (hsize : ∀ i ∈ L, (T.bipartiteAbove rel i).card = q)
    (hpair : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → ∀ x ∈ T, ∀ y ∈ T,
      rel i x → rel j x → rel i y → rel j y → x = y) :
    L.card * q^2 ≤ T.card * (q + L.card) := by
  classical
  let fiber (z : V) := L.bipartiteBelow rel z
  let pairRel (ij : I × I) (z : V) := rel ij.1 z ∧ rel ij.2 z
  have first : ∑ z ∈ T, (fiber z).card = L.card * q := by
    dsimp [fiber]
    rw [← Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    simpa using Finset.sum_congr rfl hsize
  have his (ij : I × I) (hij : ij ∈ L.offDiag) :
      (T.bipartiteAbove pairRel ij).card ≤ 1 := by
    obtain ⟨hi, hj, hne⟩ := Finset.mem_offDiag.mp hij
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxT, hix, hjx⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyT, hiy, hjy⟩ := Finset.mem_filter.mp hy
    exact hpair ij.1 hi ij.2 hj hne x hxT y hyT hix hjx hiy hjy
  have hoff (z : V) : (fiber z).offDiag = L.offDiag.bipartiteBelow pairRel z := by
    ext ij
    simp only [fiber, pairRel, Finset.bipartiteBelow, Finset.mem_offDiag, Finset.mem_filter]
    tauto
  have hsum : ∑ z ∈ T, (fiber z).offDiag.card ≤ L.card^2 := calc
    _ = ∑ ij ∈ L.offDiag, (T.bipartiteAbove pairRel ij).card := by
      simp_rw [hoff]
      rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ ≤ ∑ _ij ∈ L.offDiag, 1 := Finset.sum_le_sum his
    _ ≤ L.card^2 := by simp [Finset.offDiag_card, sq]
  have hsecond : ∑ z ∈ T, (fiber z).card^2 ≤ L.card^2 + L.card*q := by
    calc
      _ = ∑ z ∈ T, ((fiber z).offDiag.card + (fiber z).card) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.offDiag_card, sq, Nat.sub_add_cancel (Nat.le_mul_self _)]
      _ ≤ _ := by rw [Finset.sum_add_distrib, first]; omega
  have hcs := sq_sum_le_card_mul_sum_sq (s := T) (f := fun z ↦ (fiber z).card)
  simp only [Nat.cast_id] at hcs
  rw [first] at hcs
  refine Nat.le_of_mul_le_mul_left ?_ hL
  calc
    _ = (L.card*q)^2 := by ring
    _ ≤ _ := hcs.trans (Nat.mul_le_mul_left _ hsecond)
    _ = _ := by ring

/-- The two-product sum covers every nonzero field element once the fourth
power of the cardinality of the input exceeds the cube of the field order. -/
theorem finiteField_twoProducts {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (A : Finset K) (a : K) (ha : a ≠ 0) (hA : Fintype.card K ^ 3 < A.card ^ 4) :
    ∃ b ∈ A, ∃ c ∈ A, ∃ x ∈ A, ∃ y ∈ A, b*x + c*y = a := by
  classical
  let q := Fintype.card K
  let E := A ×ˢ A
  let L := E.erase 0
  let T := Eᶜ
  have hq : 1 ≤ q := Fintype.card_pos
  have hE : q^3 < E.card^2 := by
    have hh : E.card^2 = A.card^4 := by simp [E]; ring
    rwa [hh]
  have hlarge : 1 < E.card := by
    by_contra! he
    have h1 := Nat.pow_le_pow_left he 2
    have h2 := Nat.pow_le_pow_left hq 3
    omega
  have hlen : E.card ≤ L.card + 1 := by
    by_cases h : 0 ∈ E
    · simp only [L, Finset.card_erase_of_mem h]; omega
    · simp [L, Finset.erase_eq_of_notMem h]
  have hL : 0 < L.card := by omega
  by_contra hno
  have hempty (v z : K × K) (hv : v ∈ E) (hz : z ∈ E) : planeDot v z ≠ a :=
    fun he ↦ hno ⟨v.1, (Finset.mem_product.mp hv).1, v.2, (Finset.mem_product.mp hv).2,
      z.1, (Finset.mem_product.mp hz).1, z.2, (Finset.mem_product.mp hz).2, he⟩
  let rel (v z : K × K) := planeDot v z = a
  have hsize (v : K × K) (hv : v ∈ L) : (T.bipartiteAbove rel v).card = q := by
    have hv' := Finset.mem_erase.mp hv
    have hset : T.bipartiteAbove rel v = Finset.univ.filter (fun z ↦ planeDot v z = a) := by
      ext z
      simp only [T, Finset.bipartiteAbove, rel, Finset.mem_filter, Finset.mem_compl,
        Finset.mem_univ, true_and, and_iff_right_iff_imp]
      exact fun h hz ↦ hempty v z hv'.2 hz h
    rw [hset]
    exact planeLine_card a v hv'.1
  have hbound := incidence_bound L T rel q hL hsize (fun _ _ _ _ hij _ _ _ _ hi hj hi' hj' ↦
    planeLine_intersection ha hij hi hj hi' hj')
  have hcomp : T.card + E.card = q^2 := by
    simp [T, q, Fintype.card_prod, pow_two]
  have hprod : E.card * (q + L.card) ≤ q^3 := by
    have h := congrArg (fun n : ℕ ↦ n * (q + L.card)) hcomp
    nlinarith only [h, hbound]
  have he : E.card ≤ q + L.card := by omega
  exact hE.not_ge ((show E.card^2 ≤ E.card * (q + L.card) by
    rw [pow_two]; exact Nat.mul_le_mul_left _ he).trans hprod)

/-- Hart–Iosevich's d = 2 covering assertion in the precise real-exponent
form used by the manuscript, specialized to prime fields. -/
theorem primeField_twoProducts (p : ℕ) [Fact p.Prime] (A : Finset (ZMod p))
    (a : ZMod p) (ha : a ≠ 0) (hA : (p : ℝ) ^ (3 / 4 : ℝ) < (A.card : ℝ)) :
    ∃ b ∈ A, ∃ c ∈ A, ∃ x ∈ A, ∃ y ∈ A, b*x + c*y = a := by
  apply finiteField_twoProducts A a ha
  rw [ZMod.card]
  have h4 : ((p : ℝ) ^ (3 / 4 : ℝ)) ^ 4 < (A.card : ℝ)^4 :=
    pow_lt_pow_left₀ hA (Real.rpow_nonneg (by positivity) _) (by decide)
  have he : ((p : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = (p : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [he] at h4
  exact_mod_cast h4

end OddEgyptian
