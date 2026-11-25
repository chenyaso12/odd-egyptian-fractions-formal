module

public import MathProblems.OddEgyptian.Layers
public import MathProblems.OddEgyptian.DigitInputs
public import MathProblems.OddEgyptian.FiniteField
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

/-- A positive digit decomposition with smooth numerators and an optional condition on
denominators. The same list may contain duplicate terms. -/
def SmoothExpansion (P limit m : ℕ) (allowed : ℕ → Prop) : Prop :=
  ∃ terms : List (ℕ × ℕ), terms.length ≤ limit ∧
    (terms.map fun t => (t.1 : ℚ) / t.2).sum = (m : ℚ) ∧
    ∀ t ∈ terms, (∃ u : ℕ, u ∣ P ∧ ∃ v : ℕ, v ∣ P ∧ t.1 = u * v) ∧
      Odd t.2 ∧ t.2 ≤ P ^ 2 ∧ allowed t.2

private theorem smooth_mono_length {P l l' m : ℕ} {ok : ℕ → Prop}
    (h : SmoothExpansion P l m ok) (hl : l ≤ l') : SmoothExpansion P l' m ok := by
  obtain ⟨ts, len, total, spec⟩ := h
  exact ⟨ts, len.trans hl, total, spec⟩

private theorem smooth_add {P l k m n : ℕ} {ok : ℕ → Prop}
    (first : SmoothExpansion P l m ok) (second : SmoothExpansion P k n ok) :
    SmoothExpansion P (l+k) (m+n) ok := by
  obtain ⟨s, hs, firstSum, firstSpec⟩ := first
  obtain ⟨t, ht, secondSum, secondSpec⟩ := second
  refine ⟨s++t, by simpa using Nat.add_le_add hs ht, ?_, ?_⟩
  · simp [firstSum, secondSum]
  · intro z hz
    exact (List.mem_append.mp hz).elim (firstSpec z) (secondSpec z)

private theorem smooth_ones (P m : ℕ) (hP : 0 < P) {ok : ℕ → Prop} (h1 : ok 1) :
    SmoothExpansion P m m ok := by
  refine ⟨List.replicate m (1, 1), by simp, ?_, ?_⟩
  · simp
  · intro z hz
    obtain rfl := List.eq_of_mem_replicate hz
    exact ⟨⟨1, one_dvd _, 1, one_dvd _, rfl⟩, by decide, (pow_pos hP 2 : 0 < P ^ 2), h1⟩

private theorem smooth_enlarge {P P' l m : ℕ} {ok ok' : ℕ → Prop} (hdiv : P ∣ P')
    (hP' : 0 < P') (allow : ∀ w, Odd w → w ≤ P ^ 2 → ok w → ok' w)
    (src : SmoothExpansion P l m ok) : SmoothExpansion P' l m ok' := by
  obtain ⟨terms, len, total, spec⟩ := src
  refine ⟨terms, len, total, ?_⟩
  intro t ht
  obtain ⟨⟨u, hu, v, hv, eq⟩, hw, bound, okW⟩ := spec t ht
  exact ⟨⟨u, hu.trans hdiv, v, hv.trans hdiv, eq⟩, hw,
    bound.trans (Nat.pow_le_pow_left (Nat.le_of_dvd hP' hdiv) _), allow _ hw bound okW⟩

/-- Lift the two products in the prime field back to natural-number divisors. -/
theorem goodPrimeLift {F : Finset ℕ} {p : ℕ} (hp : GoodPrime F p) :
    ∃ u ∈ F, ∃ v ∈ F, ∃ x ∈ F, ∃ y ∈ F, p ∣ u * x + v * y + 1 := by
  classical
  have : Fact p.Prime := ⟨hp.1⟩
  let A := F.image (fun k : ℕ => (k : ZMod p))
  have images : A.image ZMod.val = F.image (· % p) := by
    simp [A, Finset.image_image, Function.comp_def, ZMod.val_natCast]
  have card : A.card = (F.image (· % p)).card :=
    (Finset.card_image_of_injective A (ZMod.val_injective p)).symm.trans (congrArg Finset.card images)
  obtain ⟨u, hu, v, hv, x, hx, y, hy, eq⟩ :=
    primeField_twoProducts p A (-1) (neg_ne_zero.mpr one_ne_zero) (by rw [card]; exact hp.2.2)
  change u ∈ F.image (fun k : ℕ => (k : ZMod p)) at hu
  change v ∈ F.image (fun k : ℕ => (k : ZMod p)) at hv
  change x ∈ F.image (fun k : ℕ => (k : ZMod p)) at hx
  change y ∈ F.image (fun k : ℕ => (k : ZMod p)) at hy
  obtain ⟨u', huF, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨v', hvF, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨x', hxF, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y', hyF, rfl⟩ := Finset.mem_image.mp hy
  refine ⟨u', huF, v', hvF, x', hxF, y', hyF, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
  push_cast
  rw [eq, neg_add_cancel]

/-- The quotient produced for a prime is odd and bounded by P². The protection
hypothesis allows both the unrestricted A1 case and the common-residue D case. -/
theorem goodPrimeExpansion {P p : ℕ} {F : Finset ℕ} (hP : Odd P)
    (subset : F ⊆ P.divisors) (hp : GoodPrime F p) {ok : ℕ → Prop}
    (protect : ∀ u ∈ F, ∀ v ∈ F, ∀ x ∈ F, ∀ y ∈ F, ∀ w : ℕ,
      p*w = u*x + v*y + 1 → ok w) :
    SmoothExpansion P 3 p ok := by
  obtain ⟨u, hu, v, hv, x, hx, y, hy, w, hw⟩ := goodPrimeLift hp
  have factor {a : ℕ} (ha : a ∈ F) : a ∣ P ∧ Odd a ∧ a ≤ P := by
    have ha' := Nat.dvd_of_mem_divisors (subset ha)
    have ha'' : Odd (a * (P / a)) := by simpa only [Nat.mul_div_cancel' ha'] using hP
    exact ⟨ha', (Nat.odd_mul.mp ha'').1, Nat.le_of_dvd hP.pos ha'⟩
  obtain ⟨huP, huOdd, huBound⟩ := factor hu
  obtain ⟨hvP, hvOdd, hvBound⟩ := factor hv
  obtain ⟨hxP, hxOdd, hxBound⟩ := factor hx
  obtain ⟨hyP, hyOdd, hyBound⟩ := factor hy
  have hwOdd : Odd w := by
    have hprod : Odd (p*w) := by
      rw [← hw]
      exact ((huOdd.mul hxOdd).add_odd (hvOdd.mul hyOdd)).add_odd (by decide)
    exact (Nat.odd_mul.mp hprod).2
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hp.2.1
    have := hp.1.two_le
    omega
  have hbound : w ≤ P ^ 2 := by
    have := Nat.mul_le_mul_right w hp3
    have := Nat.mul_le_mul huBound hxBound
    have := Nat.mul_le_mul hvBound hyBound
    have hPpos : 0 < P*P := Nat.mul_pos hP.pos hP.pos
    rw [pow_two]
    omega
  have hallowed := protect u hu v hv x hx y hy w hw.symm
  have hw0 : (w : ℚ) ≠ 0 := by exact_mod_cast hwOdd.pos.ne'
  have hwQ : (u : ℚ)*x + v*y + 1 = p*w := by exact_mod_cast hw
  refine ⟨[(u*x,w), (v*y,w), (1,w)], by simp, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Nat.cast_mul, Nat.cast_one]
    field_simp
    linarith
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨⟨u, huP, x, hxP, rfl⟩, hwOdd, hbound, hallowed⟩
    · exact ⟨⟨v, hvP, y, hyP, rfl⟩, hwOdd, hbound, hallowed⟩
    · exact ⟨⟨1, one_dvd _, 1, one_dvd _, rfl⟩, hwOdd, hbound, hallowed⟩

theorem threeGoodExpansion {P m : ℕ} {F : Finset ℕ} (hP : Odd P)
    (subset : F ⊆ P.divisors) (good : ThreeGood F m) {ok : ℕ → Prop}
    (protect : ∀ u ∈ F, ∀ v ∈ F, ∀ x ∈ F, ∀ y ∈ F, ∀ p w : ℕ,
      p*w = u*x + v*y + 1 → ok w) : SmoothExpansion P 9 m ok := by
  obtain ⟨p, q, t, hp, hq, ht, rfl⟩ := good
  have one {j : ℕ} (hj : GoodPrime F j) := goodPrimeExpansion hP subset hj
    (fun u hu v hv x hx y hy w h => protect u hu v hv x hx y hy j w h)
  exact smooth_add (smooth_add (one hp) (one hq)) (one ht)

/-- A common non-root class supplies the extra coprimality constraint for all
quotients, even if the four lifted representatives depend on the prime. -/
theorem commonResidueProtect {F : Finset ℕ} {B r : ℕ} (hr : r < B)
    (fiber : ∀ a ∈ F, a % B = r) (nonroot : ¬ B ∣ 2*r^2+1) :
    ∀ u ∈ F, ∀ v ∈ F, ∀ x ∈ F, ∀ y ∈ F, ∀ p w : ℕ,
      p*w = u*x+v*y+1 → ¬ B ∣ w := by
  intro u hu v hv x hx y hy p w eq hbad
  have rep {a : ℕ} (ha : a ∈ F) : Nat.ModEq B a r := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr] using fiber a ha
  have modEq := (((rep hu).mul (rep hx)).add ((rep hv).mul (rep hy))).add_right 1
  have hh : B ∣ u*x+v*y+1 := eq ▸ (hbad.trans (dvd_mul_left w p))
  have contradiction := (modEq.dvd_iff (dvd_refl B)).mp hh
  apply nonroot
  convert contradiction using 1
  ring

/-- Uniform A1 assembly with a fixed exceptional range. The chosen products need only
increase by divisibility when passing from m-1 to m. -/
theorem boundedSmoothExpansions (P : ℕ → ℕ) (odds : ∀ m, Odd (P m))
    (increasing : ∀ m, P m ∣ P (m+1)) (m₀ : ℕ)
    (good : ∀ m, m₀ ≤ m → Odd m → ThreeGood (P m).divisors m) :
    ∀ m, SmoothExpansion (P m) (max 10 m₀) m (fun _ => True) := by
  intro m
  by_cases small : m ≤ m₀
  · exact smooth_mono_length (smooth_ones (P m) m (odds m).pos trivial) (small.trans (le_max_right ..))
  have oddCase (k) (hk : m₀ ≤ k) (ho : Odd k) :
      SmoothExpansion (P k) 9 k (fun _ => True) :=
    threeGoodExpansion (odds k) (fun _ hs => hs) (good k hk ho) (by intros; trivial)
  rcases Nat.even_or_odd m with even | odd
  · let k := m - 1
    have hk : k+1 = m := by dsimp [k]; omega
    have hodd : Odd k := by obtain ⟨t, ht⟩ := even; refine ⟨k/2, ?_⟩; dsimp [k]; omega
    have hdiv : P k ∣ P m := hk ▸ increasing k
    have prev := smooth_enlarge hdiv (odds m).pos (fun _ _ _ _ => trivial)
      (oddCase k (by dsimp [k]; omega) hodd)
    have append := smooth_add prev (smooth_ones (P m) 1 (odds m).pos trivial)
    rw [hk] at append
    exact smooth_mono_length append (le_max_left ..)
  · exact smooth_mono_length (oddCase m (by omega) odd) (by omega)

/-- A fixed prime and one common class suffice for all digits. The small interval uses
A1 at a smaller divisor-product; the large interval uses three good primes and works
for both possible positions of m-1 at the transition. -/
theorem assembleFractionDigits {P B J T r : ℕ} {F : Finset ℕ} (oddP : Odd P) (hB : 1 < B)
    (subset : F ⊆ P.divisors) (hr : r < B) (fiber : ∀ u ∈ F, u % B = r)
    (nonroot : ¬ B ∣ 2*r^2+1)
    (small : ∀ m, m ≤ T → m < B → ∃ Q : ℕ, Q ∣ P ∧ Q^2 < B ∧
      SmoothExpansion Q J m (fun _ => True))
    (large : ∀ m, T < m → m < B → Odd m → ThreeGood F m) :
    FractionDigits B (P^2) (max (J+1) 10) := by
  let ok (w : ℕ) := ¬ B ∣ w
  have one : ok 1 := fun contra => (not_le_of_gt hB) (Nat.le_of_dvd (by decide) contra)
  have sm {m : ℕ} (hsm : m ≤ T) (hm : m < B) : SmoothExpansion P J m ok := by
    obtain ⟨Q, hQP, hQB, hexp⟩ := small m hsm hm
    exact smooth_enlarge hQP oddP.pos (fun _ wo hw _ hbad =>
      (not_le_of_gt (hw.trans_lt hQB)) (Nat.le_of_dvd wo.pos hbad)) hexp
  have lg {m : ℕ} (hlg : T < m) (hm : m < B) (ho : Odd m) : SmoothExpansion P 9 m ok :=
    threeGoodExpansion oddP subset (large m hlg hm ho) (commonResidueProtect hr fiber nonroot)
  intro m hm
  have expansion : SmoothExpansion P (max (J+1) 10) m ok := by
    by_cases hsm : m ≤ T
    · exact smooth_mono_length (sm hsm hm) (by omega)
    rcases Nat.even_or_odd m with even | odd
    · let k := m-1
      have hk : k+1 = m := by dsimp [k]; omega
      have hodd : Odd k := by obtain ⟨t, ht⟩ := even; refine ⟨k/2, ?_⟩; dsimp [k]; omega
      have hkB : k < B := by omega
      have appendOne {l : ℕ} (e : SmoothExpansion P l k ok) : SmoothExpansion P (l+1) m ok := by
        simpa only [hk] using smooth_add e (smooth_ones P 1 oddP.pos one)
      by_cases hkt : k ≤ T
      · exact smooth_mono_length (appendOne (sm hkt hkB)) (le_max_left ..)
      · exact smooth_mono_length (appendOne (lg (by omega) hkB hodd)) (le_max_right ..)
    · exact smooth_mono_length (lg (by omega) hm odd) (by omega)
  obtain ⟨terms, len, total, spec⟩ := expansion
  refine ⟨terms, len, total, ?_⟩
  intro t ht
  obtain ⟨⟨u, hu, v, hv, eq⟩, odd, bound, avoid⟩ := spec t ht
  exact ⟨by rw [eq, pow_two]; exact mul_dvd_mul hu hv, odd, bound, avoid⟩

end OddEgyptian
