module

public import MathProblems.OddEgyptian.ExternalBounds
public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

public section

namespace OddEgyptian

/-- An interval with logarithmic prime mass greater than log b contains a prime
that does not divide b. -/
theorem prime_not_dvd_of_theta_gap (b : ℕ) (hb : 0 < b) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hgap : Real.log (b : ℝ) < Chebyshev.theta v - Chebyshev.theta u) :
    ∃ p : ℕ, p.Prime ∧ u < (p : ℝ) ∧ (p : ℝ) ≤ v ∧ ¬p ∣ b := by
  classical
  let U := Nat.primesLE ⌊u⌋₊
  let V := Nat.primesLE ⌊v⌋₊
  have huv' : U ⊆ V := Nat.primesLE_mono (Nat.floor_mono huv)
  by_contra hn
  have hsub : V \ U ⊆ b.primeFactors := by
    intro p hp
    obtain ⟨hpV, hpU⟩ := Finset.mem_sdiff.mp hp
    have hprime := Nat.prime_of_mem_primesLE hpV
    have hl : u < (p : ℝ) := lt_of_not_ge (fun h ↦ hpU (Nat.mem_primesLE.mpr ⟨Nat.le_floor h, hprime⟩))
    have hcast : (p : ℝ) ≤ (⌊v⌋₊ : ℝ) := by exact_mod_cast Nat.le_of_mem_primesLE hpV
    have hr := hcast.trans (Nat.floor_le (hu.trans huv))
    exact Nat.mem_primeFactors.mpr ⟨hprime, (not_not.mp fun h ↦ hn ⟨p, hprime, hl, hr, h⟩), hb.ne'⟩
  have hsum : ∑ p ∈ V \ U, Real.log (p : ℝ) ≤ ∑ p ∈ b.primeFactors, Real.log (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ ↦
      Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le))
  have hprodpos : 0 < ∏ p ∈ b.primeFactors, (p : ℝ) :=
    Finset.prod_pos (fun p hp ↦ by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
  have hprodle : (∏ p ∈ b.primeFactors, (p : ℝ)) ≤ (b : ℝ) := by
    rw [← Nat.cast_prod (fun p : ℕ ↦ p)]
    exact_mod_cast Nat.le_of_dvd hb (Nat.prod_primeFactors_dvd b)
  have hlog := Real.log_le_log hprodpos hprodle
  rw [Real.log_prod (fun p hp ↦ by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)] at hlog
  rw [Finset.sum_sdiff_eq_sub huv'] at hsum
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE] at hgap
  exact hgap.not_ge (hsum.trans hlog)

/-- The numerical choice of a prime in (X,8X] is uniform in b; the remaining
growth estimates only have to ensure log b < 2X and X beyond the fixed threshold. -/
theorem auxiliary_prime_interval : ∃ t : ℝ, 3 ≤ t ∧ ∀ X : ℝ, t ≤ X → ∀ b : ℕ, 0 < b →
    Real.log (b : ℝ) < 2 * X → ∃ p : ℕ, p.Prime ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ 8*X ∧ ¬p ∣ b := by
  obtain ⟨t, ht, h⟩ := chebyshevInputs.1
  refine ⟨t, ht, ?_⟩
  intro X hX b hb hlog
  have hpos := ht.trans hX
  have hX8 : X ≤ 8*X := by linarith
  apply prime_not_dvd_of_theta_gap b hb (by linarith) hX8
  linarith [(h X hX).2.2, (h (8*X) (hX.trans hX8)).2.1]

private theorem nonroot_of_triple (B : ℕ) (hB : B.Prime) (h3 : 3 < B)
    (d : ℕ) (h : B ∣ 2*d^2 + 1) : ¬ B ∣ 2*(3*d)^2 + 1 := by
  intro h'
  have h9 : B ∣ 9*(2*d^2+1) := dvd_mul_of_dvd_right h _
  have he : 9*(2*d^2+1) = 8 + (2*(3*d)^2 + 1) := by ring
  rw [he] at h9
  have hh : B ∣ 8 := (Nat.dvd_add_left h').mp h9
  have hpow : B ∣ 2^3 := hh
  have h2 := hB.dvd_of_dvd_pow hpow
  have := Nat.le_of_dvd (by decide : 0 < 2) h2
  omega

private theorem common_class_product (n B : ℕ) (hn : 0 < n)
    (h3n : ¬3 ∣ n) (hB : B.Prime) (h3 : 3 < B) (hBn : ¬B ∣ 3*n) :
    ∃ r : ℕ, 0 < r ∧ r < B ∧ ¬ B ∣ 2*r^2+1 ∧
      (3*n).divisors.card ≤ 2*B*((3*n).divisors.filter (fun d ↦ d%B=r)).card := by
  classical
  let chooseD (d : ℕ) := if B ∣ 2*d^2+1 then 3*d else d
  let S := n.divisors.image chooseD
  have h3d (d : ℕ) (hd : d ∈ n.divisors) : ¬3 ∣ d :=
    fun h ↦ h3n (dvd_trans h (Nat.mem_divisors.mp hd).1)
  have hInject : Set.InjOn chooseD n.divisors := by
    intro d hd e he h
    dsimp [chooseD] at h
    split_ifs at h with hx hy hy
    · omega
    · exact False.elim (h3d e he ⟨d, h.symm⟩)
    · exact False.elim (h3d d hd ⟨e, h⟩)
    · exact h
  have hScard : S.card = n.divisors.card := Finset.card_image_of_injOn hInject
  have hval (d : ℕ) (hd : d ∈ S) : d ∈ (3*n).divisors ∧ ¬ B ∣ 2*d^2+1 := by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    have heD := (Nat.mem_divisors.mp he).1
    dsimp [chooseD]
    split_ifs with h
    · exact ⟨Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left 3 heD, by positivity⟩,
        nonroot_of_triple B hB h3 e h⟩
    · exact ⟨Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_right heD _, by positivity⟩, h⟩
  let residues := S.image (fun d ↦ d % B)
  let fiber (r : ℕ) := S.filter (fun d ↦ d % B = r)
  have hSnon : S.Nonempty := (Finset.nonempty_of_ne_empty (by
    have h1 := Nat.one_mem_divisors.mpr hn.ne'
    exact Finset.ne_empty_of_mem (Finset.mem_image_of_mem chooseD h1)))
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image residues (fun t ↦ (fiber t).card) (hSnon.image _)
  have hr' := Finset.mem_image.mp hr
  obtain ⟨e, he, her⟩ := hr'
  have heV := hval e he
  have heB : ¬B ∣ e := fun h ↦ hBn (dvd_trans h (Nat.mem_divisors.mp heV.1).1)
  have erMod : Nat.ModEq B r e := her ▸ Nat.mod_modEq e B
  have hfmod := ((erMod.pow 2).mul_left 2).add_right 1
  have hrB : r < B := her ▸ Nat.mod_lt e hB.pos
  have hrpos : 0 < r := by
    rw [← her, Nat.pos_iff_ne_zero]
    exact fun hh ↦ heB (Nat.dvd_of_mod_eq_zero hh)
  refine ⟨r, hrpos, hrB, fun hd ↦ heV.2 ((hfmod.dvd_iff (dvd_refl B)).mp hd), ?_⟩
  have hbound : S.card ≤ B * (fiber r).card := by
    have hres : residues.card ≤ B := by
      have hh : residues ⊆ Finset.range B := by
        intro v hv
        obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_range.mpr (Nat.mod_lt _ hB.pos)
      simpa using Finset.card_le_card hh
    calc
      S.card = ∑ r ∈ residues, (fiber r).card := Finset.card_eq_sum_card_image _ _
      _ ≤ ∑ _r ∈ residues, (fiber r).card := Finset.sum_le_sum hmax
      _ ≤ _ := by simpa using Nat.mul_le_mul_right (fiber r).card hres
  have hfsub : fiber r ⊆ (3*n).divisors.filter (fun d ↦ d%B=r) := by
    intro d hd
    obtain ⟨hd, hres⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨(hval d hd).1, hres⟩
  have hc : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3n
  rw [hc.card_divisors_mul, show (3 : ℕ).divisors.card = 2 by decide, ← hScard, Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (hbound.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hfsub)))

private theorem prime_not_dvd_product (p : ℕ) (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime) (hpS : p ∉ s) : ¬ p ∣ ∏ q ∈ s, q := by
  intro h
  obtain ⟨q, hq, hd⟩ := (hp.prime.dvd_finsetProd_iff (fun q : ℕ ↦ q)).mp h
  have he := ((Nat.dvd_prime (hs q hq)).mp hd).resolve_left hp.ne_one
  exact hpS (he ▸ hq)

theorem oddPrimeProduct_pos (y : ℝ) : 0 < oddPrimeProduct y :=
  Finset.prod_pos (fun _ hp ↦ (Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hp)).pos)

theorem oddPrimeProduct_odd (y : ℝ) : Odd (oddPrimeProduct y) := by
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  exact prime_not_dvd_product 2 Nat.prime_two _ (fun _ hp ↦
    Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hp)) (by simp)

theorem oddPrimeProduct_dvd_of_le {u v : ℝ} (huv : u ≤ v) :
    oddPrimeProduct u ∣ oddPrimeProduct v :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset_erase 2 (Nat.primesLE_mono (Nat.floor_mono huv)))

theorem prime_not_dvd_oddPrimeProduct {y : ℝ} {B : ℕ} (hB : B.Prime) (hyB : y < (B : ℝ)) :
    ¬ B ∣ oddPrimeProduct y := by
  apply prime_not_dvd_product B hB _ (fun _ hp ↦ Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hp))
  intro hmem
  have hh := Nat.le_of_mem_primesLE (Finset.mem_of_mem_erase hmem)
  have hpos := Nat.pos_of_floor_pos (hB.pos.trans_le hh)
  have hh' : (B : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hh
  exact hyB.not_ge (hh'.trans (Nat.floor_le hpos.le))

/-- A single nonroot residue class contains at least |D|/(2B) divisors of the
odd primorial, uniformly in the later choice of base-B digit. -/
theorem common_nonroot_class (y : ℝ) (B : ℕ) (hy : 3 ≤ y) (hB : B.Prime)
    (hyB : y < (B : ℝ)) :
    ∃ r : ℕ, 0 < r ∧ r < B ∧ ¬ B ∣ 2*r^2+1 ∧
      (oddPrimeProduct y).divisors.card ≤
        2*B*((oddPrimeProduct y).divisors.filter (fun d ↦ d%B=r)).card := by
  classical
  let D := (Nat.primesLE ⌊y⌋₊).erase 2
  let s := D.erase 3
  let n := ∏ q ∈ s, q
  have h3B : 3 < B := by exact_mod_cast hy.trans_lt hyB
  have h3 : 3 ∈ D := Finset.mem_erase.mpr ⟨by decide,
    Nat.mem_primesLE.mpr ⟨Nat.le_floor (by simpa using hy), Nat.prime_three⟩⟩
  have hD (p : ℕ) (hp : p ∈ D) : p.Prime := Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hp)
  have hs (p : ℕ) (hp : p ∈ s) : p.Prime := hD p (Finset.mem_of_mem_erase hp)
  have hprod : 3*n = oddPrimeProduct y := by
    change 3 * ∏ q ∈ D.erase 3, q = ∏ q ∈ D, q
    simpa [Nat.mul_comm] using Finset.prod_erase_mul D (fun q : ℕ ↦ q) h3
  have hbprod : ¬ B ∣ 3*n := by
    rw [hprod]
    exact prime_not_dvd_oddPrimeProduct hB hyB
  simpa only [hprod] using common_class_product n B
    (Finset.prod_pos fun p hp ↦ (hs p hp).pos)
    (prime_not_dvd_product 3 Nat.prime_three s hs (by simp [s])) hB h3B hbprod

end OddEgyptian
