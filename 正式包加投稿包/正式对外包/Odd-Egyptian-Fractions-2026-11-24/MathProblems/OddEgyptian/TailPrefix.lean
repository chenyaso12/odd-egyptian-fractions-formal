module

public import MathProblems.OddEgyptian.Prefix
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

private def termDen (t i : ℕ) : ℕ := 6*(t+i)+7
private def prefixSum (t k : ℕ) : ℚ := ∑ i ∈ Finset.range k, (1:ℚ)/termDen t i

private theorem crossing (t h : ℕ) : ∃ k, (h : ℚ) ≤ prefixSum t (k+1) := by
  let c : ℕ := 6*t+7
  have hc : 0 < c := by dsimp [c]; omega
  obtain ⟨k, hk⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_ge_atTop
    ((h:ℝ)*c)).exists
  have hs : (∑ i ∈ Finset.range k, 1 / ((i:ℝ)+1)) ≤
      (c:ℝ) * ∑ i ∈ Finset.range k, 1/(termDen t i : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hd : 0 < termDen t i := by simp [termDen]
    have hbound : termDen t i ≤ c*(i+1) := by dsimp [termDen,c]; nlinarith
    rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast (show 1*termDen t i ≤ c*(i+1) by omega)
  have hsum : (h:ℝ) ≤ ∑ i ∈ Finset.range k, 1/(termDen t i : ℝ) := by
    apply le_of_mul_le_mul_left _ (by exact_mod_cast hc : 0<(c:ℝ))
    exact (mul_comm (c:ℝ) h) ▸ (hk.trans hs)
  refine ⟨k, ?_⟩
  have hrat : (h:ℚ) ≤ prefixSum t k := by
    unfold prefixSum
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hsum
  unfold prefixSum at *
  rw [Finset.sum_range_succ]
  linarith [show 0 ≤ (1:ℚ)/termDen t k by positivity]

/-- A finite prefix from the progression 6n+1 leaves a proper fraction whose
odd denominator is coprime to 3. The last inequality forces its entire representation
to lie past the prefix and the requested cutoff. -/
theorem oddTailBasis_of_ternary
    (proper : ∀ a b : ℕ, Odd b → ¬3 ∣ b → a < b → ∃ s, Represents ((a:ℚ)/b) s) :
    OddTailBasis := by
  classical
  intro h hh t
  let i := Nat.find (crossing t h)
  have hafter : (h:ℚ) ≤ prefixSum t (i+1) := Nat.find_spec (crossing t h)
  have hbefore : prefixSum t i < (h:ℚ) := by
    cases hi : i with
    | zero => simpa [prefixSum] using (show (0:ℚ) < h by exact_mod_cast hh)
    | succ j =>
      exact lt_of_not_ge (Nat.find_min (crossing t h) (show j < i by omega))
  let E := (Finset.range i).image (termDen t)
  have hE : (∑ d ∈ E, (1:ℚ)/d) = prefixSum t i := by
    apply Finset.sum_image
    intro x _ y _ hxy
    unfold termDen at hxy
    omega
  have hd (d) (hd : d ∈ E) : 1<d ∧ Odd d ∧ t<d ∧ d < termDen t i ∧ d%6=1 := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have hj' := Finset.mem_range.mp hj
    simp only [termDen, Nat.odd_iff]
    omega
  let B := E.prod id
  have hBmod : B ≡ 1 [MOD 6] := Nat.ModEq.prod_one fun n hn => (hd n hn).2.2.2.2
  change B % 6 = 1 at hBmod
  have hB : 0 < B := by omega
  have hB3 : ¬3 ∣ B := by omega
  have hBo : Odd B := by rw [Nat.odd_iff]; omega
  let z := ∑ d ∈ E, B / d
  have hz : (z:ℚ) = (B:ℚ)*prefixSum t i := by
    rw [← hE, Finset.mul_sum]
    change ((∑ d ∈ E, B / d : ℕ) : ℚ) = _
    push_cast
    apply Finset.sum_congr rfl
    intro d hd'
    have hdvd : d ∣ B := Finset.dvd_prod_of_mem id hd'
    have := (hd d hd').1
    rw [show (B:ℚ)*(1/d)=B/d by ring, eq_div_iff (by positivity)]
    exact_mod_cast Nat.div_mul_cancel hdvd
  let q : ℚ := h - prefixSum t i
  have hqpos : 0 < q := sub_pos.mpr hbefore
  have hqmax : q ≤ 1/(termDen t i : ℚ) := by
    change (h:ℚ) ≤ (∑ j ∈ Finset.range (i+1), (1:ℚ)/termDen t j) at hafter
    rw [Finset.sum_range_succ] at hafter
    change (h:ℚ) ≤ prefixSum t i + _ at hafter
    dsimp [q]; linarith
  have hdn : 1 < termDen t i := by simp [termDen]
  have hqlt : q < 1 := hqmax.trans_lt (by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast hdn)
  have hzlt : z < h*B := by
    have hzlt' : (z:ℚ) < h*B := by
      rw [hz, mul_comm (h:ℚ)]; exact mul_lt_mul_of_pos_left hbefore (by positivity)
    exact_mod_cast hzlt'
  let a := h*B-z
  have hfrac : (a:ℚ)/B = q := by
    unfold a q
    rw [Nat.cast_sub hzlt.le, Nat.cast_mul, hz]
    field_simp
  have ha : a < B := by
    have : (a:ℚ)/B < 1 := hfrac.trans_lt hqlt
    exact_mod_cast (div_lt_one (by positivity)).mp this
  obtain ⟨S,hS⟩ := proper a B hBo hB3 ha
  rw [hfrac] at hS
  have hprefix : Represents ((h:ℚ)-q) E := by
    refine ⟨fun d hd' => ⟨(hd d hd').1,(hd d hd').2.1⟩, ?_⟩
    rw [hE]; dsimp [q]; ring
  have hgap (x) (hx : x∈E) : q < (1:ℚ)/x :=
    hqmax.trans_lt (one_div_lt_one_div_of_lt
      (by have := (hd x hx).1; positivity) (by exact_mod_cast (hd x hx).2.2.2.1))
  have hp := (prefix_splice hprefix hS hgap).1
  refine ⟨E ∪ S, hp, ?_⟩
  intro d hmem
  rcases Finset.mem_union.mp hmem with hd' | hs'
  · exact (hd d hd').2.2.1
  · have hdpos := (hS.1 d hs').1
    have hunit : (1:ℚ)/d ≤ q := hS.2 ▸
      Finset.single_le_sum (f := fun d : ℕ => (1:ℚ)/d) (fun _ _ => by positivity) hs'
    have hle : termDen t i ≤ d := by
      exact_mod_cast le_of_one_div_le_one_div (by positivity : 0<(d:ℚ)) (hunit.trans hqmax)
    dsimp [termDen] at hle
    omega

end OddEgyptian
