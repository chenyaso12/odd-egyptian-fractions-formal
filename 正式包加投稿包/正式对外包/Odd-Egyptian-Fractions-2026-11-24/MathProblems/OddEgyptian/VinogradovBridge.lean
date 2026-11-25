module

public import MathProblems.OddEgyptian.DigitInputs
public import MathProblems.OddEgyptian.DigitEstimates
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

open Filter Real

/-- Ordered prime triples, allowing repeated primes and the prime two. -/
def allPrimeTriples (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (m+1)) ×ˢ ((Finset.range (m+1)) ×ˢ Finset.range (m+1))).filter
    fun (a,b,c) => a+b+c=m ∧ a.Prime ∧ b.Prime ∧ c.Prime

def AllPrimeTripleInput : Prop :=
  ∃ v : ℝ, 0 < v ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Odd m →
    v*(m:ℝ)^2 / (Real.log (m:ℝ))^3 ≤ ((allPrimeTriples m).card:ℝ)

/-- For an odd total any triple involving 2 has form (2,2,m-4) in one of three orders. -/
theorem allPrimeTriples_card_le {m : ℕ} (hm : Odd m) :
    (allPrimeTriples m).card ≤ (threePrimeReps m).card + 3 := by
  let exceptional : Finset (ℕ × ℕ × ℕ) := {(2,2,m-4), (2,m-4,2), (m-4,2,2)}
  have sub : allPrimeTriples m ⊆ threePrimeReps m ∪ exceptional := by
    rintro ⟨a,b,c⟩ h
    obtain ⟨hbox, eq, hpa, hpb, hpc⟩ := Finset.mem_filter.mp h
    by_cases hodd : Odd a ∧ Odd b ∧ Odd c
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hbox, eq, hpa, hodd.1, hpb, hodd.2.1, hpc, hodd.2.2⟩)
    apply Finset.mem_union_right
    simp only [exceptional, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    obtain ⟨k,hk⟩ := hm
    have primeCases {j : ℕ} (hj : j.Prime) : j = 2 ∨ Odd j :=
      (eq_or_ne j 2).imp id hj.odd_of_ne_two
    rcases primeCases hpa with rfl | ⟨u,hu⟩ <;>
      rcases primeCases hpb with rfl | ⟨v,hv⟩ <;>
      rcases primeCases hpc with rfl | ⟨w,hw⟩
    all_goals first | omega | exact False.elim (hodd ⟨⟨_,hu⟩, ⟨_,hv⟩, ⟨_,hw⟩⟩)
  have hx : exceptional.card ≤ 3 := by
    have h₁ := Finset.card_insert_le (2,2,m-4) ({(2,m-4,2), (m-4,2,2)} : Finset (ℕ × ℕ × ℕ))
    have h₂ := Finset.card_insert_le (2,m-4,2) ({(m-4,2,2)} : Finset (ℕ × ℕ × ℕ))
    simp only [Finset.card_singleton] at h₂
    dsimp [exceptional]
    omega
  exact (Finset.card_le_card sub).trans ((Finset.card_union_le ..).trans (Nat.add_le_add_left hx _))

/-- Discarding the at most three exceptional ordered triples costs arbitrarily little
relative to m²/(log m)³. Here we keep half the lower-bound constant. -/
theorem threePrimeInput_of_allPrimes (h : AllPrimeTripleInput) : ThreePrimeInput := by
  obtain ⟨v, hv, m₀, bound⟩ := h
  have castLim : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have eventuallySmall := castLim.eventually
    (digit_log_power_bound 3 (r := 1) (c := 1) one_pos one_pos)
  obtain ⟨K, hK⟩ := eventually_atTop.mp eventuallySmall
  let cutoff := max 7 (max m₀ (max K ⌈6/v⌉₊))
  refine ⟨v/2, by positivity, cutoff, le_max_left .., ?_⟩
  intro m hm ho
  have h7 : 7 ≤ m := (le_max_left ..).trans hm
  have hm₀ : m₀ ≤ m := by dsimp [cutoff] at hm; omega
  have hK' : K ≤ m := by dsimp [cutoff] at hm; omega
  have hbig : ⌈6/v⌉₊ ≤ m := by dsimp [cutoff] at hm; omega
  have hg : 6/v ≤ (m:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hbig)
  have hVM := (div_le_iff₀ hv).mp hg
  have hlog : (Real.log (m:ℝ))^3 ≤ (m:ℝ) := by simpa using hK m hK'
  have mpos : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have den : 0 < (Real.log (m:ℝ))^3 := pow_pos (Real.log_pos (by exact_mod_cast
    (show 1 < m by omega))) _
  have h6 : 6 ≤ v*(m:ℝ)^2 / (Real.log (m:ℝ))^3 := by
    apply (le_div_iff₀ den).mpr
    calc
      _ ≤ 6*(m:ℝ) := by gcongr
      _ ≤ ((m:ℝ)*v)*m := mul_le_mul_of_nonneg_right hVM mpos.le
      _ = _ := by ring
  have remove : ((allPrimeTriples m).card:ℝ) ≤ ((threePrimeReps m).card:ℝ) + 3 := by
    exact_mod_cast allPrimeTriples_card_le ho
  have ht := bound m hm₀ ho
  have half : (v/2)*(m:ℝ)^2 / (Real.log (m:ℝ))^3 =
      (v*(m:ℝ)^2 / (Real.log (m:ℝ))^3) / 2 := by ring
  rw [half]
  linarith

/-- The log weights are attached to actual primes, and the triples are ordered. -/
noncomputable def primeTripleLogSum (m : ℕ) : ℝ :=
  ∑ t ∈ allPrimeTriples m, log (t.1:ℝ) * log (t.2.1:ℝ) * log (t.2.2:ℝ)

def LogWeightedPrimeTripleInput : Prop :=
  ∃ v : ℝ, 0 < v ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Odd m →
    v*(m:ℝ)^2 ≤ primeTripleLogSum m

theorem primeTripleLogSum_le (m : ℕ) (hm : 1 < m) :
    primeTripleLogSum m ≤ ((allPrimeTriples m).card:ℝ) * (log (m:ℝ))^3 := by
  have one (p : ℕ) (hp : p.Prime) (hpm : p ≤ m) :
      0 ≤ log (p:ℝ) ∧ log (p:ℝ) ≤ log (m:ℝ) :=
    ⟨log_nonneg (by exact_mod_cast hp.one_lt.le),
      log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpm)⟩
  have hmLog := (log_pos (by exact_mod_cast hm : (1:ℝ) < m)).le
  calc
    primeTripleLogSum m ≤ ∑ _t ∈ allPrimeTriples m, (log (m:ℝ))^3 := by
      apply Finset.sum_le_sum
      rintro ⟨a,b,c⟩ h
      obtain ⟨_, eq, hpa, hpb, hpc⟩ := Finset.mem_filter.mp h
      obtain ⟨ha0, ha⟩ := one a hpa (by omega)
      obtain ⟨hb0, hb⟩ := one b hpb (by omega)
      obtain ⟨hc0, hc⟩ := one c hpc (by omega)
      exact (mul_le_mul (mul_le_mul ha hb hb0 hmLog) hc hc0
        (mul_nonneg hmLog hmLog)).trans_eq (by ring)
    _ = _ := by simp

/-- A uniform lower bound for the usual prime-only log-weighted sum already
gives the unweighted project input, including removal of the prime 2. -/
theorem threePrimeInput_of_logWeighted (h : LogWeightedPrimeTripleInput) : ThreePrimeInput := by
  apply threePrimeInput_of_allPrimes
  obtain ⟨v,hv,m₀,bound⟩ := h
  refine ⟨v,hv,max m₀ 2,?_⟩
  intro m hm ho
  have hm' : 1 < m := by omega
  apply (div_le_iff₀ (pow_pos (log_pos (by exact_mod_cast hm' : (1:ℝ)<m)) 3)).mpr
  exact (bound m (by omega) ho).trans (primeTripleLogSum_le m hm')

end OddEgyptian
