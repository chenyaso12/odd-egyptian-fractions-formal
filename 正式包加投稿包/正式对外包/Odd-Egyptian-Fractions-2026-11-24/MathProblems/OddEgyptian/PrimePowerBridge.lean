module

public import MathProblems.OddEgyptian.VinogradovBridge
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Finset Filter Real
open scoped ArithmeticFunction.vonMangoldt

/-- The triple sum over the full cube, matching the usual additive von Mangoldt convolution. -/
noncomputable def mangoldtTripleSum (n : ℕ) : ℝ :=
  ∑ a ∈ range (n+1), ∑ b ∈ range (n+1), ∑ c ∈ range (n+1),
    if a+b+c=n then (Λ a : ℝ) * (Λ b : ℝ) * (Λ c : ℝ) else 0

def MangoldtTripleInput : Prop :=
  ∃ v : ℝ, 0 < v ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Odd n →
    v*(n:ℝ)^2 ≤ mangoldtTripleSum n

private def additiveTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (n+1)) ×ˢ ((range (n+1)) ×ˢ range (n+1))).filter fun t => t.1+t.2.1+t.2.2=n

private noncomputable def compositeWeight (a : ℕ) : ℝ :=
  if a.Prime then 0 else Λ a

private theorem compositeWeight_nonneg (a : ℕ) : 0 ≤ compositeWeight a := by
  unfold compositeWeight
  split <;> first | rfl | exact ArithmeticFunction.vonMangoldt_nonneg

private theorem sum_compositeWeight (n : ℕ) :
    ∑ k ∈ range (n+1), compositeWeight k = Chebyshev.psi n - Chebyshev.theta n := by
  have hr : range (n+1) = insert 0 (Ioc 0 n) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [hr, sum_insert (by simp), Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast,
    sum_filter]
  simp [compositeWeight]

private theorem projection_weight_bound (n : ℕ) (pair : ℕ × ℕ × ℕ → ℕ × ℕ)
    (maps : ∀ t ∈ additiveTriples n, pair t ∈ (range (n+1)) ×ˢ range (n+1))
    (inj : Set.InjOn pair (additiveTriples n)) :
    ∑ t ∈ additiveTriples n, compositeWeight (pair t).1 ≤
      ((n:ℝ)+1) * (Chebyshev.psi n - Chebyshev.theta n) := by
  classical
  have sub : (additiveTriples n).image pair ⊆ (range (n+1)) ×ˢ range (n+1) := by
    intro p hp
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hp
    exact maps t ht
  calc
    _ = ∑ p ∈ (additiveTriples n).image pair, compositeWeight p.1 := (sum_image inj).symm
    _ ≤ ∑ p ∈ (range (n+1)) ×ˢ range (n+1), compositeWeight p.1 :=
      sum_le_sum_of_subset_of_nonneg sub (fun p _ _ => compositeWeight_nonneg p.1)
    _ = _ := by
      rw [sum_product]
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      rw [← mul_sum, sum_compositeWeight]

private theorem triple_mem {n a b c : ℕ} (h : (a,b,c) ∈ additiveTriples n) :
    a ≤ n ∧ b ≤ n ∧ c ≤ n ∧ a+b+c=n := by
  have heq := (mem_filter.mp h).2
  change a+b+c=n at heq
  omega

private theorem primePart_sum (n : ℕ) :
    (∑ t ∈ additiveTriples n, if t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime then
      log (t.1:ℝ)*log (t.2.1:ℝ)*log (t.2.2:ℝ) else 0) = primeTripleLogSum n := by
  classical
  have hh : (additiveTriples n).filter (fun t => t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime) =
      allPrimeTriples n := by
    ext ⟨a,b,c⟩
    simp only [additiveTriples, allPrimeTriples, mem_filter]
    tauto
  rw [← sum_filter, hh]
  rfl

/-- The contribution from an offending prime-power coordinate is bounded by its
Mangoldt weight times two logarithms. -/
private theorem pointwise_bound {a b c n : ℕ} (hn : 1 ≤ n)
    (han : a ≤ n) (hbn : b ≤ n) (hcn : c ≤ n) :
    Λ a * Λ b * Λ c ≤
      (if a.Prime ∧ b.Prime ∧ c.Prime then log (a:ℝ)*log (b:ℝ)*log (c:ℝ) else 0) +
      (compositeWeight a + compositeWeight b + compositeWeight c) * (log (n:ℝ))^2 := by
  let M := log (n:ℝ)
  have hM : 0 ≤ M := log_nonneg (by exact_mod_cast hn)
  have hbnd {i : ℕ} (hi : i ≤ n) : Λ i ≤ M := by
    by_cases hiz : i = 0
    · simpa [hiz] using hM
    · exact ArithmeticFunction.vonMangoldt_le_log.trans (log_le_log
        (by exact_mod_cast Nat.pos_of_ne_zero hiz) (by exact_mod_cast hi))
  have hnon (i : ℕ) : 0 ≤ Λ i := ArithmeticFunction.vonMangoldt_nonneg
  have htwo (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) : Λ i * Λ j ≤ M^2 :=
    (mul_le_mul (hbnd hi) (hbnd hj) (hnon _) hM).trans_eq (by ring)
  let S := compositeWeight a + compositeWeight b + compositeWeight c
  have bad (i : ℕ) (hi : ¬i.Prime) (his : compositeWeight i ≤ S) :
      Λ i * M^2 ≤ S * M^2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa [compositeWeight,hi] using his
  have hsa : compositeWeight a ≤ S := by dsimp [S]; linarith [compositeWeight_nonneg b, compositeWeight_nonneg c]
  have hsb : compositeWeight b ≤ S := by dsimp [S]; linarith [compositeWeight_nonneg a, compositeWeight_nonneg c]
  have hsc : compositeWeight c ≤ S := by dsimp [S]; linarith [compositeWeight_nonneg a, compositeWeight_nonneg b]
  by_cases ha : a.Prime
  · by_cases hb : b.Prime
    · by_cases hc : c.Prime
      · simp [ha,hb,hc,compositeWeight,ArithmeticFunction.vonMangoldt_apply_prime]
      · simp only [hc, and_false, ite_false, zero_add]
        exact ((by ring : Λ a*Λ b*Λ c = Λ c*(Λ a*Λ b))).trans_le
          ((mul_le_mul_of_nonneg_left (htwo a b han hbn) (hnon _)).trans (bad c hc hsc))
    · simp only [hb, false_and, and_false, ite_false, zero_add]
      exact ((by ring : Λ a*Λ b*Λ c = Λ b*(Λ a*Λ c))).trans_le
        ((mul_le_mul_of_nonneg_left (htwo a c han hcn) (hnon _)).trans (bad b hb hsb))
  · simp only [ha, false_and, ite_false, zero_add]
    exact (mul_assoc ..).le.trans
      ((mul_le_mul_of_nonneg_left (htwo b c hbn hcn) (hnon _)).trans (bad a ha hsa))

/-- The true additive von Mangoldt convolution loses at most a lower-order term when
all three coordinates are required to be primes. -/
theorem mangoldtTripleSum_error (n : ℕ) (hn : 1 ≤ n) :
    mangoldtTripleSum n ≤ primeTripleLogSum n +
      (3*((n:ℝ)+1)*(Chebyshev.psi n - Chebyshev.theta n)) * (log (n:ℝ))^2 := by
  classical
  have hs : mangoldtTripleSum n =
      ∑ t ∈ additiveTriples n, Λ t.1 * Λ t.2.1 * Λ t.2.2 := by
    simp only [mangoldtTripleSum, additiveTriples, sum_filter, sum_product]
  let total := ((n:ℝ)+1)*(Chebyshev.psi n - Chebyshev.theta n)
  have leftW : (∑ t ∈ additiveTriples n, compositeWeight t.1) ≤ total := by
    refine projection_weight_bound n (fun t => (t.1,t.2.1)) ?_ ?_
    · rintro ⟨a,b,c⟩ h
      obtain ⟨ha,hb,_,_⟩ := triple_mem h
      simp [Nat.lt_succ_of_le ha, Nat.lt_succ_of_le hb]
    · rintro ⟨a,b,c⟩ h ⟨a',b',c'⟩ h' eq
      have eqs : a = a' ∧ b = b' := Prod.mk.inj eq
      have hsum : a+b+c=n := (triple_mem h).2.2.2
      have hsum' : a'+b'+c'=n := (triple_mem h').2.2.2
      simp only [Prod.mk.injEq]
      omega
  have middleW : (∑ t ∈ additiveTriples n, compositeWeight t.2.1) ≤ total := by
    refine projection_weight_bound n (fun t => (t.2.1,t.1)) ?_ ?_
    · rintro ⟨a,b,c⟩ h
      obtain ⟨ha,hb,_,_⟩ := triple_mem h
      simp [Nat.lt_succ_of_le ha, Nat.lt_succ_of_le hb]
    · rintro ⟨a,b,c⟩ h ⟨a',b',c'⟩ h' eq
      have eqs : b = b' ∧ a = a' := Prod.mk.inj eq
      have hsum : a+b+c=n := (triple_mem h).2.2.2
      have hsum' : a'+b'+c'=n := (triple_mem h').2.2.2
      simp only [Prod.mk.injEq]
      omega
  have rightW : (∑ t ∈ additiveTriples n, compositeWeight t.2.2) ≤ total := by
    refine projection_weight_bound n (fun t => (t.2.2,t.1)) ?_ ?_
    · rintro ⟨a,b,c⟩ h
      obtain ⟨ha,_,hc,_⟩ := triple_mem h
      simp [Nat.lt_succ_of_le ha, Nat.lt_succ_of_le hc]
    · rintro ⟨a,b,c⟩ h ⟨a',b',c'⟩ h' eq
      have eqs : c = c' ∧ a = a' := Prod.mk.inj eq
      have hsum : a+b+c=n := (triple_mem h).2.2.2
      have hsum' : a'+b'+c'=n := (triple_mem h').2.2.2
      simp only [Prod.mk.injEq]
      omega
  rw [hs]
  calc
    _ ≤ ∑ t ∈ additiveTriples n, ((if t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime then
        log (t.1:ℝ)*log (t.2.1:ℝ)*log (t.2.2:ℝ) else 0) +
        (compositeWeight t.1 + compositeWeight t.2.1 + compositeWeight t.2.2)*(log (n:ℝ))^2) := by
      apply sum_le_sum
      rintro ⟨a,b,c⟩ h
      obtain ⟨ha,hb,hc,_⟩ := triple_mem h
      exact pointwise_bound hn ha hb hc
    _ ≤ _ := by
      rw [sum_add_distrib, primePart_sum, ← sum_mul, sum_add_distrib, sum_add_distrib]
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      dsimp [total] at leftW middleW rightW
      linarith

theorem logWeighted_of_mangoldt (h : MangoldtTripleInput) : LogWeightedPrimeTripleInput := by
  obtain ⟨v,hv,n₀,input⟩ := h
  have eventual := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (digit_log_power_bound 3 (r := 1/2) (c := v/24) (by norm_num) (by positivity))
  obtain ⟨K,hK⟩ := eventually_atTop.mp eventual
  refine ⟨v/2, by positivity, max n₀ (max K 1), ?_⟩
  intro n hn ho
  have hn₁ : 1 ≤ n := by omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn₁
  have hbig := hK n (show K ≤ n by omega)
  have hlog : (log (n:ℝ))^3 ≤ v/24 * sqrt (n:ℝ) := by
    simpa only [sqrt_eq_rpow] using hbig
  have hpsi := Chebyshev.psi_sub_theta_le hnR
  let l := log (n:ℝ)
  have hl : 0 ≤ l := log_nonneg hnR
  have herr : (3*((n:ℝ)+1)*(Chebyshev.psi n - Chebyshev.theta n)) * l^2 ≤ (v/2)*(n:ℝ)^2 := calc
    _ ≤ (3*(2*(n:ℝ))*(2 * sqrt (n:ℝ) * l)) * l^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul (by linarith) hpsi (sub_nonneg.mpr (Chebyshev.theta_le_psi _)) (by positivity)
    _ = (12*(n:ℝ)*sqrt (n:ℝ)) * l^3 := by ring
    _ ≤ (12*(n:ℝ)*sqrt (n:ℝ)) * (v/24 * sqrt (n:ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (v/2)*(n:ℝ)^2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity),
        congrArg (fun x : ℝ => v*(n:ℝ)*x) (Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity))]
  have hR := input n (by omega) ho
  have hpp := mangoldtTripleSum_error n hn₁
  dsimp [l] at herr
  linarith

theorem threePrimeInput_of_mangoldt (h : MangoldtTripleInput) : ThreePrimeInput :=
  threePrimeInput_of_logWeighted (logWeighted_of_mangoldt h)

end OddEgyptian
