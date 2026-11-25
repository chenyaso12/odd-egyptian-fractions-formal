module

public import MathProblems.OddEgyptian.DigitConclusion
public import MathProblems.OddEgyptian.Reduction
public import MathProblems.OddEgyptian.PrimeMarker

@[expose] public section

namespace OddEgyptian

/-- Proposition M: a short expansion contains the product of the first r odd primes itself. -/
def MarkedExactTarget : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
    ∃ s : Finset ℕ, Represents 1 s ∧ (s.card : ℝ) ≤ A * Real.log (r : ℝ) ∧
      FirstOddProduct r ∈ s

private theorem add_exact_marker {Q : ℕ} (hQ : 3 ≤ Q) (hodd : Odd Q)
    (E : Finset ℕ) (hE : Represents (1 - 1 / (Q : ℚ)) E)
    (hbudget : 1 + 2 * E.card < Q.divisors.card) :
    ∃ s : Finset ℕ, Represents 1 s ∧ s.card ≤ E.card + 3 ∧ Q ∈ s := by
  by_cases hmem : Q ∈ E
  · let triple (d : ℕ) := splitTriple d (Q / d)
    have hcount := card_admissibleChoices Q.properDivisors E triple
      (fun x _ => split_fiber_le_two hodd hQ x)
    have hdiv : Q.divisors.card = Q.properDivisors.card + 1 := by
      rw [← Nat.insert_self_properDivisors (by omega : Q ≠ 0)]
      exact Finset.card_insert_of_notMem Nat.self_notMem_properDivisors
    obtain ⟨d, hd⟩ := Finset.card_pos.mp
      (show 0 < (admissibleChoices Q.properDivisors E triple).card by omega)
    obtain ⟨hd, hdis⟩ := mem_admissibleChoices.mp hd
    obtain ⟨hdpos, hdo, huo, hu, heq⟩ := split_divisor_data hodd hd
    refine ⟨E ∪ triple d, ⟨?_, ?_⟩, ?_, Finset.mem_union_left _ hmem⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hE.1 x hx
      · have hle := splitTriple_lower hdpos huo hu hx
        have hlt := (split_scaled_order hdpos huo hu).1
        exact ⟨by omega, splitTriple_odd hdo huo hx⟩
    · have hsum : ∑ x ∈ triple d, (1 : ℚ) / x = 1 / (Q : ℚ) := by
        simpa only [triple, heq] using splitTriple_sum hdpos huo hu
      rw [Finset.sum_union hdis, hE.2, hsum]
      ring
    · rw [Finset.card_union_of_disjoint hdis, show (triple d).card = 3 from
        splitTriple_card hdpos huo hu]
  · refine ⟨insert Q E, ⟨?_, ?_⟩, ?_, Finset.mem_insert_self ..⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨by omega, hodd⟩
      · exact hE.1 x hx
    · rw [Finset.sum_insert hmem, hE.2]
      ring
    · rw [Finset.card_insert_of_notMem hmem]
      omega

theorem markedExact_of_short (hH : HTarget) : MarkedExactTarget := by
  obtain ⟨C, hC, short⟩ := hH
  obtain ⟨R, hR, budget⟩ := seedCount_budget (3*C) 2
  refine ⟨3*C+3, by positivity, R, ?_⟩
  intro r hr
  have hr3 := hR.trans hr
  obtain ⟨hQ, ho, hsize, hdiv⟩ := firstOddProduct_spec r hr3
  let Q := FirstOddProduct r
  obtain ⟨E, hE, hm⟩ := short (Q-1) Q hQ ho (by omega) (by omega)
  have hQr : (0 : ℚ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hv : ((Q-1 : ℕ) : ℚ) / Q = 1 - 1 / Q := by
    rw [Nat.cast_sub (by omega : 1 ≤ Q)]
    push_cast
    field_simp
  rw [hv] at hE
  have hlog : 1 ≤ Real.log (r : ℝ) :=
    (Real.le_log_iff_exp_le (by positivity)).mpr (Real.exp_one_lt_three.le.trans
      (by exact_mod_cast hr3))
  have hml : (E.card : ℝ) ≤ (3*C) * Real.log (r : ℝ) := calc
    _ ≤ C * (1 + Real.log (Real.log (Q : ℝ))) := hm
    _ ≤ C * (1 + 2 * Real.log (r : ℝ)) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hlog)]
  have hb := budget r hr E.card hml
  have hpow : 0 < (2 : ℕ) ^ (r-1) := by positivity
  have hbudget : 1 + 2 * E.card < Q.divisors.card := by
    rw [show Q.divisors.card = 2^r from hdiv]
    omega
  obtain ⟨s, hs, hcard, hmem⟩ := add_exact_marker hQ ho E hE hbudget
  refine ⟨s, hs, ?_, hmem⟩
  have hreal : (s.card : ℝ) ≤ E.card + 3 := by exact_mod_cast hcard
  nlinarith

theorem markedExact_of_threePrimeInput (vinogradov : ThreePrimeInput) : MarkedExactTarget :=
  markedExact_of_short (short_of_layeredDigits (layeredDigits_of_threePrimeInput vinogradov))

end OddEgyptian
