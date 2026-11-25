module

public import MathProblems.OddEgyptian.Definitions
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

@[expose] public section

namespace OddEgyptian

/-- The odd-tail reciprocal-basis input, stated for natural cutoffs. Taking
the natural ceiling of a real cutoff gives the real-cutoff version. -/
def OddTailBasis : Prop :=
  ∀ h : ℕ, 0 < h → ∀ cutoff : ℕ, ∃ s : Finset ℕ,
    Represents (h : ℚ) s ∧ ∀ n ∈ s, cutoff < n

/-- A common finite bound on templates avoiding any forbidden set of bounded size. -/
theorem boundedTemplateAvoidance (basis : OddTailBasis) (f : ℕ) :
    ∃ R : ℕ, ∀ forbidden : Finset ℕ, forbidden.card ≤ f →
      ∃ s : Finset ℕ, Represents 1 s ∧ Disjoint s forbidden ∧ ∀ n ∈ s, n ≤ R := by
  classical
  induction f with
  | zero =>
    obtain ⟨s, hs, _⟩ := basis 1 (by decide) 1
    refine ⟨s.sup id, fun forbidden h ↦ ⟨s, by simpa using hs, ?_, ?_⟩⟩
    · have : forbidden = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [this]
    · exact fun _ hn ↦ Finset.le_sup (f := id) hn
  | succ f ih =>
    obtain ⟨R, hR⟩ := ih
    obtain ⟨s, hs, hlarge⟩ := basis 1 (by decide) R
    refine ⟨max R (s.sup id), ?_⟩
    intro forbidden hf
    by_cases hd : Disjoint s forbidden
    · exact ⟨s, by simpa using hs, hd,
        fun _ hn ↦ (Finset.le_sup (f := id) hn).trans (le_max_right ..)⟩
    obtain ⟨x, hx, hxF⟩ := Finset.not_disjoint_iff.mp hd
    have hcard : (forbidden.erase x).card ≤ f := by
      rw [Finset.card_erase_of_mem hxF]
      omega
    obtain ⟨u, hu, hdis, hub⟩ := hR (forbidden.erase x) hcard
    refine ⟨u, hu, Finset.disjoint_left.mpr ?_, fun n hn ↦ (hub n hn).trans (le_max_left ..)⟩
    intro n hnu hnF
    have hnx : n ≠ x := ((hub n hnu).trans_lt (hlarge x hx)).ne
    exact Finset.disjoint_left.mp hdis hnu (Finset.mem_erase.mpr ⟨hnx, hnF⟩)

/-- The sum of a list of positive unit fractions, retaining repeated inputs. -/
def listReciprocalSum (xs : List ℕ) : ℚ := (xs.map (fun x ↦ (1 : ℚ) / x)).sum

/-- Fixed-size blocks of odd unit fractions can be made distinct. The uniform
constants bound both the output cardinality and every multiplier of an input. -/
theorem fixedBlockTemplates (basis : OddTailBasis) (h : ℕ) :
    ∃ F R : ℕ, ∀ xs : List ℕ, xs.length ≤ h → (∀ x ∈ xs, Odd x) →
      ∃ out : Finset ℕ, Represents (listReciprocalSum xs) out ∧ out.card ≤ F ∧
        ∀ y ∈ out, ∃ x ∈ xs, ∃ s : ℕ, 1 < s ∧ s ≤ R ∧ Odd s ∧ y = x * s := by
  classical
  induction h with
  | zero =>
    refine ⟨0, 0, ?_⟩
    intro xs hlen _
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    exact ⟨∅, by simp [Represents, listReciprocalSum]⟩
  | succ h ih =>
    obtain ⟨F, R, hIH⟩ := ih
    obtain ⟨R', hav⟩ := boundedTemplateAvoidance basis F
    refine ⟨F + (R' + 1), max R R', ?_⟩
    intro xs hlen hodd
    cases xs with
    | nil => exact ⟨∅, by simp [Represents, listReciprocalSum]⟩
    | cons x xs =>
      have hx := hodd x (by simp)
      have hxp : 0 < x := by obtain ⟨z, hz⟩ := hx; omega
      obtain ⟨u, hu, huF, hmul⟩ := hIH xs (by simpa using hlen)
        (fun n hn ↦ hodd n (List.mem_cons_of_mem _ hn))
      let forbidden := u.image (fun y ↦ y / x)
      obtain ⟨s, hs, hsu, hsR⟩ := hav forbidden (Finset.card_image_le.trans huF)
      let v := s.image (fun d ↦ x * d)
      have huv : Disjoint u v := by
        apply Finset.disjoint_left.mpr
        intro y hy hyv
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hyv
        have hforb : (x * d) / x ∈ forbidden := Finset.mem_image_of_mem _ hy
        have hdF : d ∈ forbidden := by simpa [Nat.mul_comm, hxp] using hforb
        exact Finset.disjoint_left.mp hsu hd hdF
      have hvR : v.card ≤ R' + 1 := by
        have hsubset : s ⊆ Finset.range (R' + 1) :=
          fun d hd ↦ Finset.mem_range.mpr (by have := hsR d hd; omega)
        exact Finset.card_image_le.trans (by simpa using Finset.card_le_card hsubset)
      have hvsum : ∑ y ∈ v, (1 : ℚ) / (y : ℚ) = 1 / (x : ℚ) := by
        dsimp [v]
        rw [Finset.sum_image (fun d _ e _ he ↦ Nat.eq_of_mul_eq_mul_left hxp he)]
        simp_rw [Nat.cast_mul, one_div, mul_inv_rev, mul_comm _ (x : ℚ)⁻¹]
        rw [← Finset.mul_sum]
        simpa [one_div] using congrArg ((x : ℚ)⁻¹ * ·) hs.2
      refine ⟨u ∪ v, ⟨?_, ?_⟩, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_union.mp hy with hy | hy
        · exact hu.1 y hy
        · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
          exact ⟨(hs.1 d hd).1.trans_le (Nat.le_mul_of_pos_left d hxp), hx.mul (hs.1 d hd).2⟩
      · rw [Finset.sum_union huv, hu.2, hvsum]
        simp [listReciprocalSum, add_comm]
      · rw [Finset.card_union_of_disjoint huv]
        omega
      · intro y hy
        rcases Finset.mem_union.mp hy with hy | hy
        · obtain ⟨z, hz, d, hd, hdR, hdo, hzd⟩ := hmul y hy
          exact ⟨z, List.mem_cons_of_mem _ hz, d, hd, hdR.trans (le_max_left ..), hdo, hzd⟩
        · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
          exact ⟨x, by simp, d, (hs.1 d hd).1, (hsR d hd).trans (le_max_right ..), (hs.1 d hd).2, rfl⟩

end OddEgyptian
